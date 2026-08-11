import Modelgen.Format
import Modelgen.Naming

/-!
# Universe-level monomorphization

The pass duplicates each declaration once per **ground instantiation** it is
used at, substitutes numerals for its universe parameters, and rewrites every
constant occurrence to name the copy it means. The output's level parameters
are gone: every `Sort` is `Sort n` for a numeral `n`, and every constant is
used at no levels at all — with two exceptions, both named in `MONOMORPH.md`
and both deliberate: mode A keeps the motive's universe — on a recursor, and on
its declaration-local model recursor and iota theorems — and the built-ins are
carried through untouched.

The contract a consumer is written against is `MONOMORPH.md` §1. What is
written here is the implementation of it.

## Why this is a single backward pass and not a fixpoint

An export file is topologically sorted: a declaration can only mention
declarations that appear before it. Walking the file **backwards** therefore
reaches `d` only after every user of `d`, so `d`'s set of demanded
instantiations is complete when it is read, and emitting `d`'s copies pushes
demand only onto declarations that are still ahead in the walk. No revisiting,
no fixpoint, and termination is the length of the file.

Topological sortedness is a property of the exporter and not of the format, so
[`checkOrder`] **asserts** it rather than assuming it; a file that violates it
is refused by name and index rather than silently under-instantiated.

The DAG is over declaration **groups**, not declarations, and a group is one
export **record**: an inductive block, its constructors and its recursors
mention one another cyclically and arrive as a single `inductive` record, so a
group is one node, collects one demand set, and is emitted whole. A mutual
`def` block is *not* a group — see [`buildGroups`].

**One edge is not in the file.** A `modelgen` model is referenced by nothing —
the consumer builds `T._model` off `T` rather than finding it through a use site
— so the sweep would see no demand on it at all and every model group would
take the default: one model, however many copies of `T`. [`modelKeying`]
supplies the edge and [`pushInst`] carries it, and because it runs against the
file's order rather than along it, a cascade onto a group the sweep has already
passed is *counted and named* rather than assumed away. `MONOMORPH.md` §2.3.
-/

open Lean Meta

namespace Modelgen
namespace Mono

/-- One ground instantiation: a natural number per universe parameter, in the
declaration's own parameter order. -/
abbrev Inst := Array Nat

/-- Which recursor treatment, and what an unused declaration defaults to. -/
structure Opts where
  /-- **Mode B.** Substitute a numeral for the eliminating universe too, so the
  output has no level parameter anywhere. The result is not acceptable to a
  kernel that mints recursors itself. -/
  monoRecursors : Bool := false
  /-- The instantiations a declaration nothing demands is emitted at. -/
  defaults : Array Nat := #[0]
  /-- Replay the **output** with the kernel's checking on. Mode A's oracle. -/
  check : Bool := false
  deriving Inhabited

/-! ## The naming scheme

`MONOMORPH.md` §1 is the contract; this is the code it describes. -/

/-- `succ^n zero`. -/
def natLevel : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (natLevel n)

/-- **The marker.** A `Name.str` component `_at` at the *root*, then `|σ|` as a
`Name.num`, then one `Name.num` per level.

The length comes first so that the marker's extent is known without looking at
what follows it: an inverter reads `_at`, reads `k`, takes the next `k`
components as `σ`, and everything after that is the input's name, whatever shape
it has. Nothing here consults the declaration's own name. -/
def atPrefix (σ : Inst) : Name :=
  σ.foldl (fun n k => .num n k) (.num (.str .anonymous "_at") σ.size)

/-- `full` at `σ`: the marker, prepended whole. Empty `σ` is the identity, so a
monomorphic declaration keeps its name exactly.

**Why a prefix and not surgery.** The one thing that *must* survive is the
relationship Lean and `nanoda` both derive rather than read: the recursor of an
inductive named `I` is `I ++ rec`. Prepending a fixed prefix to every name in
the file preserves every such suffix relationship automatically — `I` becomes
`p ++ I` and `I ++ rec` becomes `p ++ I ++ rec` — for *any* names, without the
pass ever asking what a name looks like. The scheme this replaced instead
replaced an *owner* prefix, which is the identity whenever the owner is not a
prefix (Mathlib's private constructors of public inductives), and then every
copy of the block shared one name. -/
def monoName (full : Name) (σ : Inst) : Name :=
  if σ.isEmpty then full else atPrefix σ ++ full

/-- Mode B's suffix for a declaration at eliminating universe `w`. -/
def elimName (n : Name) (w : Nat) : Name := .num (.str n "_elim") w

/-- Whether any component of `n` spells one of the two markers. A file that
already uses one is refused: the scheme would not be invertible on it. -/
def usesMarker : Name → Bool
  | .anonymous => false
  | .num p _ => usesMarker p
  | .str p s => s == "_at" || s == "_elim" || usesMarker p

/-! ## Groups -/

/-- What the pass needs to know about one name the file introduces. -/
structure Info where
  /-- The group that declares it. -/
  group : Nat
  /-- The declaration's own **eliminating universe**, when it has one: the
  motive's, which mode A keeps as a level parameter rather than folding into the
  marker. A recursor has one when its block eliminates largely, and so — for
  exactly the same reason, since it is the same universe — do the corresponding
  declaration-local model recursor and iota theorems. -/
  elim : Option Name := none
  deriving Inhabited

/-- The exact public role of a generated model declaration. -/
inductive ModelRole where
  | typeFormer
  | constructor
  | recursor
  | iota
  | unitlike
  | ruleK
  | projection
  | projectionIota
  deriving BEq, Inhabited

/-- A generated public declaration and the original inductive record that owns
its universe instantiation. `owner` is read from that record, never recovered
by splitting a generated name. -/
structure ModelEntry where
  owner : Name
  ownerDecl : Nat
  ownerLevelParams : List Name
  role : ModelRole
  deriving Inhabited

/-- Exact generated names which Mono can key to their original inductive
record. Ambiguous candidates are deliberately absent. -/
abbrev ModelTable := Std.HashMap Name ModelEntry

private inductive SiteKind where
  | value
  | theorem
  | inductive
  | other
  deriving BEq

private structure Site where
  kind : SiteKind

private def siteKind : EDecl → SiteKind
  | .defn .. => .value
  | .thm .. => .theorem
  | .induct .. => .inductive
  | _ => .other

/-- Build the model relation from exact original roles.

The declaration-local contract is generated from each inductive record:
`T._model`, `C._model`, `R._model`, `R._model.iota_j`, and, exactly when the
export metadata has the corresponding kernel feature, `T._model.unitlike` and
`R._model.ruleK`; a kernel structure-like owner additionally has
`P._model`/`P._model.iota` for each recovered primitive projection. A candidate counts
only when the export contains a declaration of the generated role's kind. That
condition distinguishes an original inductive literally named `Foo._model`
from the definition serving as the carrier model of `Foo`; its own model is, exactly,
`Foo._model._model`. It also makes raw private names ordinary exact keys.

If two source roles demand the same public name, neither owns it here. The
generator's collision census prevents such a model from being emitted, and
guessing would silently attach the declaration to one of two universe sets. -/
def modelTable (x : Export) : ModelTable := Id.run do
  let mut sites : Std.HashMap Name Site := {}
  for i in [0:x.decls.size] do
    let d := x.decls[i]!
    for n in d.names do sites := sites.insert n { kind := siteKind d }
  let mut table : ModelTable := {}
  let mut ambiguous : Std.HashSet Name := {}
  let add := fun (table : ModelTable) (ambiguous : Std.HashSet Name)
      (name : Name) (want : SiteKind) (entry : ModelEntry) =>
    match sites[name]? with
    | some site =>
      if site.kind != want then (table, ambiguous)
      else if ambiguous.contains name then (table, ambiguous)
      else if table.contains name then (table.erase name, ambiguous.insert name)
      else (table.insert name entry, ambiguous)
    | none => (table, ambiguous)
  for oi in [0:x.decls.size] do
    let .induct ts cs rs := x.decls[oi]! | continue
    let some ownerT := ts.head? | continue
    let entry := fun role =>
      { owner := ownerT.name, ownerDecl := oi,
        ownerLevelParams := ownerT.levelParams, role }
    for t in ts do
      (table, ambiguous) := add table ambiguous (Naming.modelName t.name) .value
        (entry .typeFormer)
    for c in cs do
      (table, ambiguous) := add table ambiguous (Naming.modelName c.name) .value
        (entry .constructor)
    for r in rs do
      (table, ambiguous) := add table ambiguous (Naming.modelName r.name) .value
        (entry .recursor)
      for j in [:r.rules.length] do
        (table, ambiguous) := add table ambiguous (Naming.iotaName r.name j) .theorem
          (entry .iota)
      if r.k then
        (table, ambiguous) := add table ambiguous (Naming.ruleKName r.name) .theorem
          (entry .ruleK)
    for t in ts do
      if t.isKernelUnitlike cs then
        (table, ambiguous) := add table ambiguous (Naming.unitlikeName t.name) .theorem
          (entry .unitlike)
      if t.isKernelStructureLike cs then
        for projection in x.projectionsFor t.name do
          (table, ambiguous) := add table ambiguous
            (Naming.projectionName projection.name) .value (entry .projection)
          (table, ambiguous) := add table ambiguous
            (Naming.projectionIotaName projection.name) .theorem (entry .projectionIota)
  return table

/-- One node of the declaration DAG. -/
structure Group where
  /-- The record's index into `Export.decls`. **One record, one group** — see
  [`buildGroups`]. -/
  decl : Nat := 0
  /-- The level parameters the record's declarations share. -/
  levelParams : List Name := []
  /-- The block's elimination universes, one per recursor that has one. -/
  elims : Array Name := #[]
  deriving Inhabited

/-- The names one record introduces, each with its elimination universe if it
has one.

There is no *owner* here any more, and that absence is the point: the renaming
([`monoName`]) is a prefix and needs to know nothing about which member a
constructor or a recursor belongs to. -/
def introOf (d : EDecl) : Array (Name × Option Name) :=
  match d with
  | .ax n .. | .defn n .. | .thm n .. | .opaq n .. | .quot n .. => #[(n, none)]
  | .induct ts cs rs => Id.run do
    let blockLp := match ts with | t :: _ => t.levelParams | [] => []
    let mut out : Array (Name × Option Name) := #[]
    for t in ts do out := out.push (t.name, none)
    for c in cs do out := out.push (c.name, none)
    for r in rs do
      let elim := r.levelParams.filter (fun p => !blockLp.contains p)
      out := out.push (r.name, elim.head?)
    return out

/-- Partition the file into groups and index every name it introduces.

**One record, one group** — and the `all` field is not read.

A group is a node of the DAG the backward sweep walks, so it has to be a set of
declarations that genuinely *cannot* be ordered: emitting it whole puts every
member at the position of its first, and any declaration between them that a
later member uses becomes a forward reference the pass itself created. An
`inductive` record is such a set — its types, constructors and recursors mention
one another cyclically — and it is already a single record, so nothing has to be
merged to keep it together.

A mutual `def` block is not such a set. Its members share an `all` field, but
what they share is *provenance*, not a cycle: `lean4export` writes each member
where its own dependencies are ready, and a file in which one member mentioned a
later one would not be topologically sorted at all — which [`checkOrder`] would
then refuse, as it should.

Mathlib is the measurement (`MONOMORPH.md` §9.3). It has 202 records whose `all`
names more than one declaration, and **97 of those blocks are not contiguous**;
the widest spans 513,481 records. Grouping by `all` relocated the later members
of all 97 to the position of the first, and in five of them that carried a
member in front of a declaration it uses — a forward reference the pass then
reported as an unsorted input. Leaving each record where it stands costs nothing
and removes the whole class, not the five that happened to be caught.

The members of a split block are therefore instantiated independently, each at
the instantiations its own users demand, and the `all` field of a copy names
only that copy ([`emitOne`]). -/
def buildGroups (x : Export) (models : ModelTable) :
    Except String (Array Group × Std.HashMap Name Info) := do
  let mut groups : Array Group := #[]
  let mut info : Std.HashMap Name Info := {}
  for i in [0 : x.decls.size] do
    let d := x.decls[i]!
    let lp := match d with
      | .ax _ lp .. | .defn _ lp .. | .thm _ lp .. | .opaq _ lp .. | .quot _ lp .. => lp
      | .induct ts _ _ => match ts with | t :: _ => t.levelParams | [] => []
    -- The block's level parameters must be shared, or the group cannot be
    -- instantiated as one.
    match d with
    | .induct ts cs rs =>
      for t in ts do
        unless t.levelParams == lp do
          throw s!"{t.name}: an inductive block whose members differ in their level parameters"
      for c in cs do
        unless c.levelParams == lp do
          throw s!"{c.name}: a constructor whose level parameters are not its block's"
      for r in rs do
        let extra := r.levelParams.filter (fun p => !lp.contains p)
        unless extra.length ≤ 1 do
          throw s!"{r.name}: a recursor with more than one elimination universe"
        -- **The eliminating universe is the *first* level parameter, and that
        -- is asserted rather than assumed.** Which parameter it *is* is decided
        -- by the set difference above — semantically, by what it is and not by
        -- where it sits — but [`RwCtx.const`] splits a use site's level
        -- arguments positionally, on the head, because that is the hot path and
        -- a list index is not free there. Lean mints a recursor's parameters
        -- motive-first (`Eq.rec.{u_1, u}`, `List.rec.{u, w}`), so the two agree
        -- on every export there is; if they ever stop agreeing the copy would
        -- come out with the right parameter and its uses at the wrong one, with
        -- nothing downstream to catch it. So the file is refused instead.
        unless extra.isEmpty || extra.head? == r.levelParams.head? do
          throw s!"{r.name}: an eliminating universe that is not the first level parameter"
    | _ => pure ()
    -- **A duplicate universe parameter is a lie monomorphization would erase.**
    -- `vendor/arena-tests/bad/tutorial/016_tut06_bad01.ndjson` declares
    -- `tut06_bad01.{u, u}`; nanoda's `no_dupes_all_params` rejects it, and the
    -- copy at `σ` has no parameters at all and is perfectly well typed. The
    -- pass must not launder that, so it refuses the file.
    unless lp.eraseDups.length == lp.length do
      throw s!"{d.names}: a duplicate universe parameter in {lp}"
    let mut elims : Array Name := #[]
    if let .induct _ _ rs := d then
      for r in rs do
        for p in r.levelParams do
          unless lp.contains p || elims.contains p do elims := elims.push p
    -- A declaration-local model recursor and its iota theorems are recursors
    -- for this purpose. Their exact roles and owner's parameters come from the
    -- original inductive record in `models`; no generated name is parsed.
    let mut lp := lp
    let mut modelElim : Option Name := none
    match d with
    | .induct .. => pure ()
    | _ =>
      if let some mi := models[(d.names[0]!)]? then
        if mi.role == .recursor || mi.role == .iota || mi.role == .ruleK then
          let blockLp := mi.ownerLevelParams
          let extra := lp.filter (fun p => !blockLp.contains p)
          -- One extra parameter, and it is the head — the same two conditions
          -- the recursor branch above asserts, for the same reason. Anything
          -- else is a shape this convention does not describe, and the
          -- declaration is left to monomorphize as it always did.
          if extra.length == 1 && extra.head? == lp.head? then
            modelElim := extra.head?
            elims := extra.toArray
            lp := lp.filter (fun p => !extra.contains p)
    let gi := groups.size
    groups := groups.push
      { decl := i, levelParams := lp, elims }
    for (n, elim) in introOf d do
      info := info.insert n { group := gi, elim := elim.orElse (fun _ => modelElim) }
  return (groups, info)

/-! ## The models

A `modelgen` model is the one thing in the file **nothing references**: a
consumer finds `T._model` by constructing the name off `T`, not through a use site
(`MODELGEN.md` §1). The backward sweep is driven entirely by references, so
left alone it sees no demand on a model at all and every model group takes the
default — one model for however many copies `T` has. That is the defect
`MONOMORPH.md` §1.3 item 1 names, and it is about *demand* and not about
naming: the marker already commutes with the model.

What closes it is an edge the sweep does not get from the file: **a model's
groups are instantiated at exactly the `σ` set of the declaration they model**.
It is not a reference — a model of `T` need not mention `T` — so it is
recovered from the exact role table [`modelTable`], and then propagated as if
it were one. -/

/-- Which group each model group is keyed to, and the reverse index the sweep
cascades along. -/
structure Keying where
  /-- For each group, the group of the declaration its declarations model —
  `none` for a group that is not a model's, which is nearly all of them. -/
  owner : Array (Option Nat) := #[]
  /-- The reverse index: for each group, every model group keyed to it. **This
  is what makes the propagation transitive**, and the second layer of the
  composed naming needs it to be: `T._model._impl.0._model` is keyed to
  `T._model._impl.0`, which is itself part of `T`'s model, so `σ` reaches it only by
  cascading through the first layer. -/
  models : Array (Array Nat) := #[]
  /-- Model groups whose `σ` could not be determined, and why. **Named, not
  defaulted** — a silent default is the defect this pass exists to remove, and
  guessing one level along is the same mistake. -/
  declined : Array String := #[]
  /-- A declaration below a model's implementation namespace whose
  level-parameter arity is not the owner's: a spliced `T._model._impl.funext` is
  genuinely polymorphic in universes that
  are nobody's motive, so `T`'s `σ` says nothing about its own and there is no
  positional mapping to make. It monomorphizes by demand like any other
  declaration, which is *right* — unlike the nine, it is referenced, by the
  model's own declarations. The arity is the discriminator rather than the
  spelling `funext`, so this reads no more of the name than the rest of the
  keying does.

  It is recorded because the reading only holds while such a group **is**
  demanded: one that reaches the default is a model declaration falling to a
  default after all, and the sweep names it. -/
  loose : Array Bool := #[]
  /-- Model groups whose level parameters match their owner's in arity but not
  in name. The mapping is positional either way; this counts how often the
  convention's "carries exactly `ℓ⃗`" is literal. -/
  renamed : Nat := 0
  deriving Inhabited

/-- **Key every model group to the declaration it models.**

A group is a model's when a name it introduces has an exact entry in the model
table built from an original inductive record. A file that merely spells
`_model`, an implementation helper below `_impl`, and an original declaration
whose own name ends in `_model` are therefore untouched. The owner stored in
the entry is looked up in `info`.

**Every name of the record is asked, and they must agree.** A record is one
group and takes one instantiation, so a record whose names model two different
declarations has no single `σ` to take; it declines. Public model declarations
are normally one-name records, while the check also covers any future grouped
emission without assuming that all of its names have the same owner.

**The `σ` mapping is the identity**, which is a claim about `modelgen` and so is
checked: the model's declarations carry exactly `ℓ⃗` (`MODELGEN.md` §1, property
3), and [`buildGroups`] has already lifted the motive's universe out of model
recursors and iota theorems, so what is left is the owner's own parameter list. A group whose
arity does not match its owner's is `Keying.loose` — the tenth family — and is
left to its own demand rather than truncated or padded onto a mapping that does
not exist. -/
def modelKeying (x : Export) (groups : Array Group) (info : Std.HashMap Name Info)
    (models : ModelTable) (refs : Array (Array (Name × List Level)))
    (carried : Std.HashSet Nat) : Keying := Id.run do
  let mut k : Keying :=
    { owner := Array.replicate groups.size none, models := Array.replicate groups.size #[]
      loose := Array.replicate groups.size false }
  for gi in [0 : groups.size] do
    let d := x.decls[groups[gi]!.decl]!
    let mut isModel := false
    let mut owners : Array Nat := #[]
    let mut orphan : Option Name := none
    for (n, _) in introOf d do
      let some mi := models[n]? | continue
      isModel := true
      match info[mi.owner]? with
      | none => orphan := some n
      | some i => unless owners.contains i.group do owners := owners.push i.group
    unless isModel do continue
    let nm := d.names[0]!
    let decline (why : String) : Keying := { k with declined := k.declined.push s!"{nm}: {why}" }
    if let some n := orphan then
      k := decline s!"a model whose owner the file does not declare ({n})"
    else if owners.size != 1 then
      k := decline s!"a model whose names key to {owners.size} different declarations"
    else if owners[0]! == gi then
      k := decline "a model of a declaration its own record introduces"
    else if carried.contains gi then
      -- A carried group is emitted once, at no instantiation at all; there is
      -- nothing for a key to decide. Not a decline — nothing was declined.
      pure ()
    else if carried.contains (owners[0]!) then
      k := decline "a model of a carried declaration, which has no σ to key to"
    else
      let oi := owners[0]!
      let lp := groups[gi]!.levelParams
      let olp := groups[oi]!.levelParams
      if lp.length != olp.length then
        k := { k with loose := k.loose.set! gi true }
      else
        if lp != olp then k := { k with renamed := k.renamed + 1 }
        k := { k with owner := k.owner.set! gi (some oi)
                      models := k.models.set! oi (k.models[oi]!.push gi) }

  -- **The model-of-a-model bridge, structural rather than nominal.** A nested
  -- model's carrier definition directly mentions its private implementation
  -- inductive. That block can itself have a public model, emitted after the
  -- block; without an edge from the root to the block, the backward sweep sees
  -- the second model before demand reaches its owner and reports it as late.
  --
  -- Identify the bridge by three exact facts: this is a type-former model from
  -- `models`, its definition references an inductive group, and that group has
  -- exact public model children of its own. No `_model` or `_impl` component is
  -- inspected. Ordinary dependencies do not qualify unless modelgen actually
  -- emitted a model for them.
  for (modelN, entry) in models.toArray do
    unless entry.role == .typeFormer do continue
    let some mi := info[modelN]? | continue
    let some oi := info[entry.owner]? | continue
    unless k.owner[mi.group]! == some oi.group do continue
    for (dep, _) in refs[mi.group]! do
      let some hi := info[dep]? | continue
      if hi.group == oi.group || k.models[hi.group]!.isEmpty then continue
      unless x.decls[groups[hi.group]!.decl]! matches .induct .. do continue
      if carried.contains hi.group then continue
      match k.owner[hi.group]! with
      | some previous =>
        if previous != oi.group then
          k := { k with declined :=
            (k.declined.push s!"{dep}: a modeled helper belongs to two model families") }
      | none =>
        let lp := groups[hi.group]!.levelParams
        let olp := groups[oi.group]!.levelParams
        if lp.length != olp.length then
          k := { k with declined := (k.declined.push
            s!"{dep}: a modeled helper has different universe arity than its model owner") }
        else
          if lp != olp then k := { k with renamed := k.renamed + 1 }
          k := { k with owner := k.owner.set! hi.group (some oi.group),
                        models := k.models.set! oi.group (k.models[oi.group]!.push hi.group) }
  return k

/-- Add `σ` to a group's demand **and to every model keyed to it**, transitively.

`cutoff` is the group the backward sweep is currently at. A cascade that lands
on a group the sweep has already passed (`> cutoff`) delivers an instantiation
whose *own* references the sweep will never explore, so the output could name a
copy that was never emitted. That is not repaired here — it is collected, so
that it is reported by name instead of being lost.

**Nothing structural rules it out** — a model's groups sit before what they
model in `modelgen`'s output, but the second layer sits *after* the block it
models, so the cascade runs both ways against the file's order. What holds in
practice is that the whole chain is filled in one step, from the first `σ` to
reach the root: `T` is the last of the lot in file order, so `T._model.…` and
`T._model._impl.0._model.…` are both still ahead of the sweep when demand arrives at
`T`, and every later push repeats a `σ` the chain already has and stops at the
first line. **Measured at zero** over `modelgen/tests` (both modes),
`modelgen/monotests`, `vendor/arena-tests` and Mathlib — `MONOMORPH.md` §2.3,
which also has the one thing that was *not* zero and is why `elimD` is not
cascaded. -/
private partial def pushInst (models : Array (Array Nat)) (cutoff : Nat)
    (st : Array (Array Inst) × Array Nat) (gi : Nat) (σ : Inst) :
    Array (Array Inst) × Array Nat :=
  let (demand, late) := st
  if demand[gi]!.contains σ then (demand, late)
  else
    let demand := demand.set! gi (demand[gi]!.push σ)
    let late := if gi > cutoff && !late.contains gi then late.push gi else late
    models[gi]!.foldl (fun s m => pushInst models cutoff s m σ) (demand, late)

/-! ## Levels -/

/-- Substitute the instantiation into a level and simplify. A parameter the
instantiation does not bind — mode A's elimination universe, or any parameter
of a carried declaration — is left standing. -/
partial def substLevel (env : Std.HashMap Name Nat) : Level → Level
  | .zero => .zero
  | .succ a => .succ (substLevel env a)
  | .max a b => mkLevelMax' (substLevel env a) (substLevel env b)
  | .imax a b => mkLevelIMax' (substLevel env a) (substLevel env b)
  | .param n => match env[n]? with | some k => natLevel k | none => .param n
  | l@(.mvar _) => l

/-- The level as a numeral, or `none` if a parameter survived. -/
def evalLevel (env : Std.HashMap Name Nat) (l : Level) : Option Nat :=
  (substLevel env l).normalize.toNat

/-! ## The built-ins, carried through untouched

`MONOMORPH.md` §3 is the list and the argument for it. -/

/-- The seed: names a kernel recognises and cannot be told about a copy of.
`Quot` and its three companions are recognised **structurally**, by the export's
own `quot` record kind, and are not in this list. -/
def builtinSeed : Array Name :=
  #[ -- The equality the round trips and the ι rules are stated with.
     `Eq, `Eq.refl,
     -- The standard axioms.
     `propext, `Classical.choice, `Quot.sound,
     -- Everything a kernel mints when it expands a literal
     -- (`checker/src/util.rs`'s `mk_name_cache`, name for name).
     `eagerReduce, `Nat, `Nat.zero, `Nat.succ, `Nat.add, `Nat.sub, `Nat.mul,
     `Nat.pow, `Nat.mod, `Nat.div, `Nat.beq, `Nat.ble, `Nat.gcd, `Nat.xor,
     `Nat.land, `Nat.lor, `Nat.shiftLeft, `Nat.shiftRight,
     `String, `String.ofList, `Bool, `Bool.true, `Bool.false,
     `Char, `Char.ofNat, `List, `List.nil, `List.cons ]

/-! ## The reference set of a group -/

/-- Every constant an expression mentions, with the level arguments it mentions
it at, and every structure a projection names. -/
partial def collectConsts (e : Expr) :
    StateM (Std.HashSet Expr × Array (Name × List Level) × Bool) Unit := do
  if (← get).1.contains e then return
  modify fun (s, o, p) => (s.insert e, o, p)
  match e with
  | .const n us => modify fun (s, o, p) => (s, o.push (n, us), p)
  | .app f a => collectConsts f; collectConsts a
  | .lam _ t b _ | .forallE _ t b _ => collectConsts t; collectConsts b
  | .letE _ t v b _ => collectConsts t; collectConsts v; collectConsts b
  | .proj _ _ s => modify (fun (s, o, _) => (s, o, true)); collectConsts s
  | .mdata _ b => collectConsts b
  | _ => pure ()

/-- The roots of a record: every expression it carries. -/
def rootsOf : EDecl → Array Expr
  | .ax _ _ t _ => #[t]
  | .defn _ _ t v .. | .thm _ _ t v _ | .opaq _ _ t v .. => #[t, v]
  | .quot _ _ t _ => #[t]
  | .induct ts cs rs => Id.run do
    let mut out : Array Expr := #[]
    for t in ts do out := out.push t.type
    for c in cs do out := out.push c.type
    for r in rs do
      out := out.push r.type
      for rr in r.rules do out := out.push rr.rhs
    return out


/-! ## Instrumentation

Three environment variables, inert unless set, and none of them changes what the
pass emits. `MONOMORPH.md` §9.8 is what they measured.

* `MONO_PHASES=1` — a line on stderr at each phase boundary with the elapsed
  time and `/proc/self/status`'s `VmRSS`/`VmHWM`. The phase deltas are the only
  attribution of the pass's memory there is; every earlier figure was a single
  peak for the whole run.
* `MONO_STATS=1` — [`shareStats`] over the input and the output. **This is the
  measurement that settles whether sharing is preserved**, and it is not an
  estimate: it counts nodes twice, once by pointer and once by structure.
* `MONO_MEMO=<mode>` — which rewrite memo to run, so that §9.8's A/B table is
  one binary and not seven. [`MemoMode`] is the list; the default is the row
  that won.
-/

/-- Resident set and high-water mark, in KB, from `/proc/self/status`. -/
def rssKB : IO (Nat × Nat) := do
  let s ← IO.FS.readFile "/proc/self/status"
  let get (k : String) : Nat := Id.run do
    for line in s.splitOn "\n" do
      if line.startsWith k then
        let digits := (line.drop k.length).toString.foldl
          (fun acc c => if c.isDigit then acc.push c else if acc.isEmpty then acc else acc) ""
        return digits.toNat?.getD 0
    return 0
  return (get "VmRSS:", get "VmHWM:")

initialize monoPhases : Bool ← do return (← IO.getEnv "MONO_PHASES").isSome
initialize monoStats : Bool ← do return (← IO.getEnv "MONO_STATS").isSome
initialize monoT0 : IO.Ref Nat ← IO.mkRef 0

/-- A phase boundary. `n` is a count the phase produced; it is reported, but it
is also there to be **forced** — Lean floats a pure `let` to its first use, so a
marker placed after one measures nothing unless something strict mentions it. -/
def phase (name : String) (n : Option Nat := none) : IO Unit := do
  if monoPhases then
    let (rss, hwm) ← rssKB
    let now ← IO.monoMsNow
    let t0 ← monoT0.get
    if t0 == 0 then monoT0.set now
    IO.eprintln s!"[mono] {name}: t={now - (if t0 == 0 then now else t0)}ms \
      rss={rss}KB hwm={hwm}KB{match n with | some k => s!" n={k}" | none => ""}"
  else if n.isSome then
    -- Forced even when the trace is off, so that the phase's cost does not move
    -- with the flag.
    pure ()

/-- **Distinct nodes by pointer, distinct nodes by structure.**

The first is the size of the DAG actually in memory; the second is the size of
the DAG the re-interning writer puts in the file. Their ratio is the
duplication factor — how many times over each distinct subterm is allocated. -/
unsafe def shareStatsUnsafe (roots : Array Expr) : Nat × Nat := Id.run do
  let mut ptrs : Std.HashSet USize := Std.HashSet.emptyWithCapacity 1024
  let mut strs : Std.HashSet Expr := Std.HashSet.emptyWithCapacity 1024
  let mut stack : Array Expr := roots
  while stack.size > 0 do
    let e := stack[stack.size - 1]!
    stack := stack.pop
    let a := ptrAddrUnsafe e
    if ptrs.contains a then continue
    ptrs := ptrs.insert a
    strs := strs.insert e
    match e with
    | .app f b => stack := (stack.push f).push b
    | .lam _ t b _ | .forallE _ t b _ => stack := (stack.push t).push b
    | .letE _ t v b _ => stack := ((stack.push t).push v).push b
    | .proj _ _ b | .mdata _ b => stack := stack.push b
    | _ => pure ()
  return (ptrs.size, strs.size)

@[implemented_by shareStatsUnsafe]
opaque shareStats (roots : Array Expr) : Nat × Nat

/-- Whether `e` contains a projection: **a lookup in a set the reader built, not
a memo this fills in.**

The answer does not depend on the binder context, which is why the *rewrite* can
be cached below the projection-free subterms and nowhere else — that part is
unchanged. What changed is where the answer comes from. Walking the `Expr` DAG
and memoising as it went needed a table over **every distinct node in the file**,
because a shared subterm would otherwise be walked once per parent; at ten
million lines of Mathlib that table reached 9,264,612 entries and **90,765 of
them (1.0 %) were `true`**. It was the largest single object the `proj` phase
built, and it was 99 % `false`.

[`Export.projNodes`] is the 1 %. The reader computes it in one forward pass over
the arena, where back-references make a visited set unnecessary, and a `.proj`
node is in the set by construction. So: not in the set, no projection. -/
@[inline] def hasProj (s : Std.HashSet Expr) (e : Expr) : Bool :=
  match e with
  | .proj .. => true
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => false
  | _ => s.contains e

/-! ## The memo's key

The rewrite of a subterm depends on the copy through **one thing**: the numerals
the copy binds the level parameters *that subterm mentions* to. Nothing else in
[`RwCtx`] varies in a way a subterm can see — `sigma` and `own` rename
declarations, not expressions, and `recArity` is settled for any target before a
user of it is emitted, because the file is topologically sorted.

So the memo key is `(e, σ restricted to the parameters e mentions)`, and the
restriction is the point rather than a refinement of it: under the *whole* `σ`, a
subterm mentioning only `u` gets a different key for every value of every other
parameter, and `Functor.comp` has six. `Functor.associator` reaches 118 copies
on Mathlib (§9.4); pruned, everything in it that mentions only `u` is one entry.

**The second component has to be canonical across declarations**, because the
`Expr` is: the same node is reached from declarations whose `levelParams` lists
order the same names differently. A position in a declaration's own list is
therefore *not* a key — bit 0 is `u` in one declaration and `v` in the next, and
a memo keyed on it returns the wrong rewrite with no check anywhere that would
catch it. Everything below indexes level parameters **by name, globally and
injectively**, and `monotests/mono_share.ndjson` is the fixture that fails if
that ever stops being true. -/

/-- Every level parameter the file declares, numbered by name — **injectively,
and once for the whole file**, so an index means the same thing in every
declaration. -/
def paramIndex (groups : Array Group) : Std.HashMap Name Nat := Id.run do
  let mut m : Std.HashMap Name Nat := {}
  for g in groups do
    for p in g.levelParams do unless m.contains p do m := m.insert p m.size
    for p in g.elims do unless m.contains p do m := m.insert p m.size
  return m

/-- The bit a parameter occupies in a carrier mask. **Indices past 63 all share
the last bit**, which merges those parameters in the mask and therefore only
ever *over*-approximates a carrier: the key comes out finer than it needed to be
and the memo misses where it could have hit. It never conflates two
substitutions, because [`RwCtx.binding`] is keyed on the injective index and not
on the bit. Mathlib declares 52 distinct level parameters, so this does not
fire there. -/
@[inline] def carrierBit (i : Nat) : UInt64 := (1 : UInt64) <<< (UInt64.ofNat (min i 63))

/-- The parameters a level mentions, as a mask. -/
def levelCarrier (idx : Std.HashMap Name Nat) : Level → UInt64
  | .zero | .mvar _ => 0
  | .succ a => levelCarrier idx a
  | .max a b | .imax a b => levelCarrier idx a ||| levelCarrier idx b
  | .param n => match idx[n]? with | some i => carrierBit i | none => carrierBit 63

/-- The parameters an expression mentions. Memoised on the DAG, exactly as
[`hasProj`] is and for the same reason. **A subterm with no level parameter
costs nothing and gets no entry**: `Expr.hasLevelParam` is a bit in the node
header that Lean maintains for us. -/
partial def carrierOf (idx : Std.HashMap Name Nat) (keep : Option (Std.HashSet Expr))
    (cache : IO.Ref (Std.HashMap Expr UInt64)) (e : Expr) : IO UInt64 := do
  if !e.hasLevelParam then return 0
  match (← cache.get)[e]? with
  | some m => return m
  | none =>
    let m ←
      match e with
      | .sort l => pure (levelCarrier idx l)
      | .const _ us => pure (us.foldl (fun a l => a ||| levelCarrier idx l) 0)
      | .app f a => pure ((← carrierOf idx keep cache f) ||| (← carrierOf idx keep cache a))
      | .lam _ t b _ | .forallE _ t b _ =>
        pure ((← carrierOf idx keep cache t) ||| (← carrierOf idx keep cache b))
      | .letE _ t v b _ =>
        pure ((← carrierOf idx keep cache t) ||| (← carrierOf idx keep cache v)
              ||| (← carrierOf idx keep cache b))
      | .proj _ _ b | .mdata _ b => carrierOf idx keep cache b
      | _ => pure 0
    -- **Only where the answer will be kept.** Under a gating mode the memo only
    -- keys nodes the arena shares, so caching the rest here would build an
    -- 8.4-million-entry table to throw away — and that table, not emission, was
    -- what set the peak (§9.8). Recomputing an unshared node is free in the
    -- aggregate: it has exactly one parent, so it is still computed once.
    if keep.all (·.contains e) then cache.modify (·.insert e m)
    return m

/-- **The nodes the arena shares**: reached from more than one parent, counted
over the whole file. A node with one parent is rebuilt once per rebuild of that
parent, so memoising it buys nothing that memoising the parent does not already
buy — and an entry costs about what the node costs. This is the set that decides
whether a memo pays for itself.

**A node `rwPure` returns unchanged is not recorded.** `.bvar`/`.fvar`/`.mvar`/
`.lit` fall through `rwPure`'s last arm to `e` itself, so a memo entry for one
buys a hash and a probe in place of nothing at all, and costs the `seen` set,
the `shared` set and a `sharedPure` entry. Skipping them is sound because they
have no children: they are never pushed back on the stack, so `seen` never
needed them.

**`.sort` and `.const` are emphatically not in that list, and measuring said
so.** They *look* like atoms and they are not: `rwPure` builds a fresh node for
each — a level rewrite for `.sort`, a name-and-levels rewrite for `.const` —
and a constant used ten thousand times is *one* node in the arena, so dropping
it from the memo rebuilds it ten thousand times. Excluding all six atom
constructors here cut the gate tables 17 % on `init-prelude` and cost **+9.7 %
peak RSS at ten million lines** (2,168,780 → 2,379,508 KB), which is the whole
of §9.8's arithmetic running backwards: the entry is worth it exactly when the
node it saves costs more than the entry. -/
def sharedNodes (roots : Array Expr) : Std.HashSet Expr := Id.run do
  let mut seen : Std.HashSet Expr := Std.HashSet.emptyWithCapacity 1024
  let mut shared : Std.HashSet Expr := Std.HashSet.emptyWithCapacity 1024
  let mut stack : Array Expr := roots
  while stack.size > 0 do
    let e := stack[stack.size - 1]!
    stack := stack.pop
    match e with
    | .bvar .. | .fvar .. | .mvar .. | .lit .. => continue
    | _ => pure ()
    if seen.contains e then
      shared := shared.insert e
      continue
    seen := seen.insert e
    match e with
    | .app f b => stack := (stack.push f).push b
    | .lam _ t b _ | .forallE _ t b _ => stack := (stack.push t).push b
    | .letE _ t v b _ => stack := ((stack.push t).push v).push b
    | .proj _ _ b | .mdata _ b => stack := stack.push b
    | _ => pure ()
  return shared

/-- Which memo the pass runs, so that §9.8's rows are one binary. `MONO_MEMO`:

| | the memo across copies | the key | entries for |
| --- | --- | --- | --- |
| `off` | none | — | — |
| `pure` | level-free subterms only | `e` | every node |
| `full` | all | `(e, σ)` whole | every node |
| `full-gate` | all | `(e, σ)` whole | shared nodes |
| `prune` | all | `(e, σ|carrier e)` | every node |
| `prune-gate` *(default)* | all | `(e, σ|carrier e)` | shared nodes |
| `prune-array` | all | `(e, σ|carrier e)` **uninterned** | shared nodes |
-/
inductive MemoMode where
  | off | pure | full | fullGate | prune | pruneGate | pruneArray
  deriving BEq, Inhabited

def memoModeOf : String → Option MemoMode
  | "off" => some .off | "pure" => some .pure
  | "full" => some .full | "full-gate" => some .fullGate
  | "prune" => some .prune | "prune-gate" => some .pruneGate
  | "prune-array" => some .pruneArray
  | _ => none

initialize memoMode : MemoMode ← do
  match ← IO.getEnv "MONO_MEMO" with
  | none => return .pruneGate
  | some s => match memoModeOf s with
    | some m => return m
    | none => throw (IO.userError s!"MONO_MEMO: unknown mode {s}")

/-! ## The rewrite -/

/-- Everything one copy of one group needs. -/
structure RwCtx where
  info : Std.HashMap Name Info
  carried : Std.HashSet Nat
  opts : Opts
  /-- The level parameters this copy binds, and to what. Mode A leaves a
  recursor's elimination universe out of it, which is what keeps it standing. -/
  env : Std.HashMap Name Nat
  /-- The group's instantiation, for the names the group itself introduces. -/
  sigma : Inst
  /-- **How many level parameters each already-emitted recursor came out with.**

  Monomorphizing moves the elimination universe in *both* directions, and the
  file's references have to follow. `Exists.{u}` is small-eliminating — its
  recursor has no universe of its own — but `Exists._at.0`'s constructor fields
  are propositions, so the kernel mints `Exists._at.0.rec.{u_1}` and a reference
  at no levels is now ill-formed. `PUnit.{u}` moves the other way, into K-like
  reduction. Emission is forward and the file is topologically sorted, so the
  block's own answer is known before anything can mention it. -/
  recArity : Std.HashMap Name Nat := {}
  /-- The carrier of every node the memo may key, by [`carrierOf`]. Under a
  gating mode this holds **only the nodes the arena shares**, so a miss here is
  also the answer to "should this be memoised at all". -/
  carrier : Std.HashMap Expr UInt64 := {}
  /-- The level-free nodes the arena shares. Only consulted under a gating
  mode. -/
  sharedPure : Std.HashSet Expr := {}
  /-- **This copy's substitution, by global parameter index, sorted.** The
  index is [`paramIndex`]'s, so the array means the same thing whichever
  declaration is being emitted — which is the whole soundness argument for
  sharing a memo across declarations. -/
  binding : Array (Nat × Nat) := #[]
  /-- The bits of `binding`'s parameters. -/
  lpMask : UInt64 := 0
  /-- The id of the whole `binding`, for the unpruned modes. -/
  envId : Nat := 0
  mode : MemoMode := .pruneGate

/-- A level under this copy's instantiation, simplified. -/
def RwCtx.level (c : RwCtx) (l : Level) : Level := (substLevel c.env l).normalize

/-- A name the group itself introduces, at this copy. -/
def RwCtx.own (c : RwCtx) (n : Name) : Name :=
  match c.info[n]? with
  | some i => if c.carried.contains i.group then n else monoName n c.sigma
  | none => n

/-- The rewrite state: the memo for projection-free subterms, and the levels
that did not come out ground.

**Half of it lives across the whole emission, not across one copy.** The input
is an arena — one line per node, back-referenced — so a subterm with a hundred
parents is *one* `Expr` in memory, and a memo that starts empty at each
declaration rebuilds it a hundred times and turns the DAG into a tree. -/
structure RwState where
  /-- Subterms whose rewrite does not depend on the copy at all: either they
  mention no level parameter, or none that this copy binds. The key is the
  `Expr` itself, as `lean4export`'s own dedup does it — Lean caches the hash in
  the node header. -/
  pure : Std.HashMap Expr Expr := {}
  /-- Subterms whose rewrite depends on the copy, keyed on the **interned
  pruned substitution** (`sigmaIds`) and the node. -/
  poly : Std.HashMap (Nat × Expr) Expr := {}
  /-- The same, with the pruned substitution carried in the key instead of
  interned — `MONO_MEMO=prune-array`, which exists to measure whether interning
  earns the table it needs. -/
  polyA : Std.HashMap (Array (Nat × Nat) × Expr) Expr := {}
  /-- **The intern table for pruned substitutions.** Global, so the id means the
  same substitution in every declaration. `0` is the empty one and lives in
  `pure`. -/
  sigmaIds : Std.HashMap (Array (Nat × Nat)) Nat := {}
  /-- This copy's carrier-mask → id, so the restriction and the intern lookup
  happen once per distinct mask rather than once per node. Reset at each copy. -/
  maskIds : Std.HashMap UInt64 Nat := {}
  errs : Array String := #[]
  deriving Inhabited

/-- The id of `a`, interning it if new. `0` is reserved for the empty
substitution, which is `RwState.pure`. -/
def sigmaId (a : Array (Nat × Nat)) : StateM RwState Nat := do
  if a.isEmpty then return 0
  match (← get).sigmaIds[a]? with
  | some i => return i
  | none =>
    let i := (← get).sigmaIds.size + 1
    modify fun s => { s with sigmaIds := s.sigmaIds.insert a i }
    return i

/-- `σ` restricted to the parameters a carrier mask names, interned. -/
def RwCtx.maskId (c : RwCtx) (m : UInt64) : StateM RwState Nat := do
  match (← get).maskIds[m]? with
  | some i => return i
  | none =>
    let i ← sigmaId (c.binding.filter (fun (j, _) => m &&& carrierBit j != 0))
    modify fun s => { s with maskIds := s.maskIds.insert m i }
    return i

/-- A constant occurrence, rewritten: which copy it names, and at which levels.

Three outcomes, and they are the whole of §1.2. A **carried** target keeps its
name and takes numerals for its level arguments. An ordinary target becomes the
copy at the instantiation the arguments evaluate to, at no levels. A
target **with an eliminating universe** — a recursor, or its model recursor and
iota theorems — splits its argument list: the head is that universe, which
mode A keeps and mode B folds into the name. The head, and not a stored index,
because this is the hot path; [`buildGroups`] refuses a file in which the
universe is anywhere else, so the two readings cannot disagree here. -/
def RwCtx.const (c : RwCtx) (n : Name) (us : List Level) : Name × List Level × Array String :=
  let us' := us.map c.level
  let ground (what : String) (ls : List Level) : Array Nat × Array String :=
    ls.foldl (fun (a, e) l =>
      match l.toNat with
      | some k => (a.push k, e)
      | none => (a.push 0, e.push s!"{n}: {what} did not evaluate to a numeral")) (#[], #[])
  match c.info[n]? with
  | none => (n, us', #[])
  | some i =>
    if c.carried.contains i.group then (n, us', #[])
    else match i.elim, us' with
      | some _, w :: rest =>
        let (σ, e1) := ground "a level argument" rest
        let base := monoName n σ
        match c.recArity[base]?.getD 1 with
        | 0 =>
          -- The block became small-eliminating at `σ`; the recursor has no
          -- universe left to take one.
          (base, [],
            if w.toNat == some 0 then e1
            else e1.push s!"{n}: eliminates into a nonzero universe, but its copy at this \
              instantiation is small-eliminating")
        | _ => (base, [w], e1)
      | _, _ =>
        let (σ, e1) := ground "a level argument" us'
        let base := monoName n σ
        match i.elim, c.recArity[base]? with
        -- The block became large-eliminating at `σ`. The original recursor
        -- eliminated into `Prop`, so the copy is used at `0`.
        | none, some 1 => (base, [natLevel 0], e1)
        | _, _ => (base, [], e1)

/-- The rewrite, on a subterm with no projection in it. Memoised: the result
does not depend on the binder context. -/
partial def rwPure (c : RwCtx) (e : Expr) : StateM RwState Expr := do
  -- **The slot.** `some 0` is `pure`: the answer does not depend on this copy.
  -- `some k` is `poly` at the interned pruned substitution `k`. `none` is "do
  -- not memoise", which under a gating mode is what a node with one parent
  -- gets. `MONO_MEMO=prune-array` keys on the substitution itself and takes the
  -- `polyA` path instead.
  let gate := c.mode == .fullGate || c.mode == .pruneGate || c.mode == .pruneArray
  let mut arrKey : Array (Nat × Nat) := #[]
  let mut slot : Option Nat := some 0
  if e.hasLevelParam then
    if c.mode == .off || c.mode == .pure then
      slot := some c.envId
    else if c.mode == .full then
      slot := some c.envId
    else
      match c.carrier[e]? with
      | none => slot := none
      | some cm =>
        if c.mode == .fullGate then slot := some c.envId
        else
          let m := cm &&& c.lpMask
          if m == 0 then slot := some 0
          else if c.mode == .pruneArray then
            arrKey := c.binding.filter (fun (j, _) => m &&& carrierBit j != 0)
            slot := some 1
          else slot := some (← c.maskId m)
  else if gate && !c.sharedPure.contains e then
    slot := none
  let hit : Option Expr ←
    match slot with
    | none => pure none
    | some 0 => pure (← get).pure[e]?
    | some k =>
      if c.mode == .pruneArray then pure (← get).polyA[(arrKey, e)]?
      else pure (← get).poly[(k, e)]?
  if let some r := hit then return r
  do
    let r ←
      match e with
      | .const n us =>
        let (n', us', errs) := c.const n us
        unless errs.isEmpty do modify (fun s => { s with errs := s.errs ++ errs })
        pure (.const n' us')
      | .sort l => pure (.sort (c.level l))
      | .app f a => pure (.app (← rwPure c f) (← rwPure c a))
      | .lam n t b bi => pure (.lam n (← rwPure c t) (← rwPure c b) bi)
      | .forallE n t b bi => pure (.forallE n (← rwPure c t) (← rwPure c b) bi)
      | .letE n t v b nd => pure (.letE n (← rwPure c t) (← rwPure c v) (← rwPure c b) nd)
      | .mdata _ b => rwPure c b
      | .proj s i b => pure (.proj s i (← rwPure c b))   -- unreachable; see `rw`
      | _ => pure e
    match slot with
    | none => pure ()
    | some 0 => modify fun s => { s with pure := s.pure.insert e r }
    | some k =>
      if c.mode == .pruneArray then modify fun s => { s with polyA := s.polyA.insert (arrKey, e) r }
      else modify fun s => { s with poly := s.poly.insert (k, e) r }
    return r

/-- **The structure a projection names, read off the projected term's type.**

`Expr.proj` carries the structure's name but not its level arguments, and Lean's
own `inferProjType` rejects a projection whose name is not the head of the
inferred type — so the name has to move to the right copy, and the copy is only
determined by that type. This is the one place the pass needs a typechecker,
and it is why the input is replayed into an environment at all.

`fvars` are the enclosing binders, with their **original** types, so this runs
against the environment the export itself describes. -/
def projHead (fvars : Array Expr) (s : Expr) : MetaM (Option (Name × List Level)) := do
  let ty ← whnf (← inferType (s.instantiateRev fvars))
  match ty.getAppFn with
  | .const n us => return some (n, us)
  | _ => return none

/-- Collect the `(structure, levels)` of every projection in `e`. Descends only
into subterms that have one. -/
partial def projScan (cache : Std.HashSet Expr) (out : IO.Ref (Array (Name × List Level)))
    (fvars : Array Expr) (e : Expr) : MetaM Unit := do
  unless hasProj cache e do return
  match e with
  | .proj _ _ s =>
    if let some r ← projHead fvars s then out.modify (·.push r)
    projScan cache out fvars s
  | .app f a => projScan cache out fvars f; projScan cache out fvars a
  | .lam n t b bi =>
    projScan cache out fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => projScan cache out (fvars.push x) b
  | .forallE n t b bi =>
    projScan cache out fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => projScan cache out (fvars.push x) b
  | .letE n t v b _ =>
    projScan cache out fvars t; projScan cache out fvars v
    withLetDecl n (t.instantiateRev fvars) (v.instantiateRev fvars) fun x =>
      projScan cache out (fvars.push x) b
  | .mdata _ b => projScan cache out fvars b
  | _ => pure ()

/-- The rewrite. Projection-free subterms go through [`rwPure`], which is
memoised; the rest is walked in `MetaM` so that [`projHead`] has a local
context. `e` is the **original** expression throughout, so the fvars carry the
original types and inference sees the environment the export describes. -/
partial def rw (c : RwCtx) (cache : Std.HashSet Expr) (st : IO.Ref RwState)
    (fvars : Array Expr) (e : Expr) : MetaM Expr := do
  unless hasProj cache e do
    -- **`modifyGet`, not `get`-then-`set`.** The memo outlives the declaration
    -- now, so a second reference to it is not free: `get` leaves the ref
    -- holding the map as well, the first `insert` sees a refcount of two and
    -- copies the whole table, and the pass goes quadratic in the memo. Measured
    -- on the 1-million-line prefix, with a memo that lives for the file:
    -- **143.36 s** with `get`/`set` against **3.93 s** with `modifyGet`, which
    -- takes the value out of the ref first.
    return ← st.modifyGet fun s => (rwPure c e).run s
  match e with
  | .proj s i b =>
    let b' ← rw c cache st fvars b
    match ← projHead fvars b with
    | some (n, us) =>
      let (n', _, errs) := c.const n us
      if !errs.isEmpty then st.modify fun s => { s with errs := s.errs ++ errs }
      return .proj n' i b'
    | none =>
      st.modify fun t => { t with errs := t.errs.push s!"a projection of {s} whose type is not an \
        application of a constant" }
      return .proj s i b'
  | .app f a => return .app (← rw c cache st fvars f) (← rw c cache st fvars a)
  | .lam n t b bi =>
    let t' ← rw c cache st fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => do
      return .lam n t' (← rw c cache st (fvars.push x) b) bi
  | .forallE n t b bi =>
    let t' ← rw c cache st fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => do
      return .forallE n t' (← rw c cache st (fvars.push x) b) bi
  | .letE n t v b nd =>
    let t' ← rw c cache st fvars t
    let v' ← rw c cache st fvars v
    withLetDecl n (t.instantiateRev fvars) (v.instantiateRev fvars) fun x => do
      return .letE n t' v' (← rw c cache st (fvars.push x) b) nd
  | .mdata _ b => rw c cache st fvars b
  | _ => return e

/-! ## The sweep -/

private def addInst (a : Array Inst) (i : Inst) : Array Inst :=
  if a.contains i then a else a.push i

private def addNat (a : Array Nat) (i : Nat) : Array Nat :=
  if a.contains i then a else a.push i

/-- What one run did. -/
structure Report where
  groups : Nat := 0
  /-- Declarations in and out — block members, constructors and recursors
  counted one each, which is the figure a checker sees. -/
  declsIn : Nat := 0
  declsOut : Nat := 0
  recordsIn : Nat := 0
  recordsOut : Nat := 0
  /-- Groups left alone, by their first name. -/
  carried : Array Name := #[]
  /-- Groups nothing in the file demanded, which took the default. **A model
  group is never one of them** ([`modelKeying`]). -/
  defaulted : Nat := 0
  /-- Groups keyed to the declaration they model rather than to a use site. -/
  modelGroups : Nat := 0
  /-- Model groups whose `σ` the keying declined to decide. Their reasons are in
  `errors`, by name. -/
  modelDeclined : Nat := 0
  /-- The tenth family: model groups with no positional `σ` mapping to their
  owner, left to their own demand ([`Keying.loose`]). -/
  modelLoose : Nat := 0
  /-- Copies per group, as a histogram. -/
  hist : Array (Nat × Nat) := #[]
  errors : Array String := #[]
  /-- Recursors the kernel minted differently from the substitution — the
  `Prop`-at-`σ` effect, counted rather than argued. -/
  recRegen : Nat := 0
  /-- Monomorphized declarations the replay would not take. -/
  rejected : Nat := 0
  /-- The pass refused the file whole; the output is the input. -/
  refused : Option String := none
  deriving Inhabited

/-- How many declarations a record carries. -/
def declCount : EDecl → Nat
  | .induct ts cs rs => ts.length + cs.length + rs.length
  | _ => 1

/-! ## The driver -/

/-! The replay's `EDecl → Declaration` is
[`Modelgen.toDeclaration`], in `Modelgen.Format`. This module used to carry a
trimmed copy of it because the original lived in `Modelgen.Driver`, which it
deliberately does not import; the function has since moved down to the shared
floor and the copy is gone. -/

/-- One record, at one instantiation. Always **mode A**: mode B is a pure
post-pass over this ([`foldElim`]), which is what makes "B is A with the
eliminating universe folded into the name" true by construction rather than by
two parallel implementations.

`keepParams` is the carried case: a built-in keeps its name and its level
parameters, and only its *references* move to the copies they mean.

**A copy's `all` field names the copy and nothing else.** `all` is the mutual
block a record was elaborated with, and [`buildGroups`] does not group by it:
two members of one block are instantiated independently, so `mono(m₁, σ)` may
exist where `mono(m₂, σ)` does not, and mapping the whole list through
[`RwCtx.own`] would write a name no record declares. What survives
monomorphization is one record per copy, which is what a singleton `all` says —
the same thing `lean4export` writes for a definition that was never mutual. An
`inductive` record's `all` lists are *within* the record and are mapped, because
there the copy at `σ` really is the whole block. -/
def emitOne (c : RwCtx) (cache : Std.HashSet Expr) (st : IO.Ref RwState)
    (keepParams : Bool) (blockLp : List Name) (d : EDecl) : MetaM EDecl := do
  let E (e : Expr) : MetaM Expr := rw c cache st #[] e
  -- **What survives is what `σ` does not bind**, which is the eliminating
  -- universe and nothing else: `blockLp` is the group's own parameters, so for
  -- an ordinary declaration this is the empty list, for a recursor it is the
  -- motive's universe, and for a model recursor or iota theorem it is the same
  -- universe by its exact role in [`modelTable`].
  let lp (orig : List Name) : List Name :=
    if keepParams then orig else orig.filter (fun p => !blockLp.contains p)
  match d with
  | .ax n l t u => return .ax (c.own n) (lp l) (← E t) u
  | .defn n l t v h sf _ =>
    return .defn (c.own n) (lp l) (← E t) (← E v) h sf [c.own n]
  | .thm n l t v _ => return .thm (c.own n) (lp l) (← E t) (← E v) [c.own n]
  | .opaq n l t v u _ => return .opaq (c.own n) (lp l) (← E t) (← E v) u [c.own n]
  -- The four `quot` records are carried verbatim: they mention nothing but
  -- `Quot`, `Sort` and themselves, and `Declaration.quotDecl` is a unit.
  | .quot n l t k => return .quot n l t k
  | .induct ts cs rs => do
    let ts' ← ts.mapM fun t => do
      return { t with name := c.own t.name, levelParams := lp t.levelParams
                      type := ← E t.type, all := t.all.map c.own, ctors := t.ctors.map c.own }
    let cs' ← cs.mapM fun x => do
      return { x with name := c.own x.name, levelParams := lp x.levelParams
                      type := ← E x.type, induct := c.own x.induct }
    let rs' ← rs.mapM fun r => do
      return { r with name := c.own r.name
                      levelParams := lp r.levelParams
                      type := ← E r.type, all := r.all.map c.own
                      rules := ← r.rules.mapM fun rr => do
                        return { rr with ctor := c.own rr.ctor, rhs := ← E rr.rhs } }
    return .induct ts' cs' rs'

/-- **The recursors the kernel mints for the monomorphized block**, in place of
the ones the substitution produced.

This is not a nicety. Substituting `σ` into an inductive changes properties the
kernel *derives* from the block rather than reads off it: `PUnit.{u}` at `u = 0`
is a `Prop` with one argument-free constructor, which is **K-like**, and the
export's `k : false` becomes a lie. Large elimination can move the same way. So
the block is replayed and its recursors are read back, which makes mode A's
output kernel-consistent by construction and turns the whole question into a
measurement: [`Report.recRegen`] counts the recursors that came back different. -/
def kernelRecs (env : Environment) (rs : List ERec) : List ERec × Nat := Id.run do
  let mut out : Array ERec := #[]
  let mut diff := 0
  for r in rs do
    match env.constants.find? r.name with
    | some (.recInfo rv) =>
      let k : ERec :=
        { name := rv.name, levelParams := rv.levelParams, type := rv.type, all := rv.all
          numParams := rv.numParams, numIndices := rv.numIndices, numMotives := rv.numMotives
          numMinors := rv.numMinors, k := rv.k, isUnsafe := rv.isUnsafe
          rules := rv.rules.map fun x => { ctor := x.ctor, nfields := x.nfields, rhs := x.rhs } }
      -- The elimination universe's *name* is Lean's to choose, so compare the
      -- statement with the export's name put back.
      let renamed :=
        match r.levelParams, rv.levelParams with
        | [a], [b] => k.type.instantiateLevelParams [b] [.param a]
        | _, _ => k.type
      unless renamed == r.type && k.k == r.k && k.numMotives == r.numMotives
          && k.numMinors == r.numMinors && k.numIndices == r.numIndices do
        diff := diff + 1
      out := out.push k
    | _ => out := out.push r
  return (out.toList, diff)

/-! ## Mode B

The eliminating universe, folded into the name. A pure pass over mode A's own
output: the only level parameter mode A leaves standing is an eliminating
universe — a recursor's, or its model recursor and iota theorems' — every use
of it in the file is at a numeral, and
this replaces each such declaration by one copy per numeral used.

**Which names those are is not re-derived here.** Mode A knows: it decided, per
group, which parameter it was keeping, and it hands the *output* names over
(`elimDefs`). Re-deriving them from the output file would mean guessing from
"a `def` with exactly one level parameter", and the carried built-ins are
exactly that — `Classical.choice.{u}` is an axiom with one parameter and folding
it would rename a constant a kernel recognises by name. -/

/-- Rewrite every reference `r.{k}` to a recursor in `elimOf` into `r._elim.k`. -/
partial def foldRefs (elimOf : Std.HashSet Name) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  match (← get)[e]? with
  | some r => return r
  | none => pure ()
  let r ←
    match e with
    | .const n [l] => pure <| if elimOf.contains n then .const (elimName n (l.toNat.getD 0)) [] else e
    | .app f a => pure (.app (← foldRefs elimOf f) (← foldRefs elimOf a))
    | .lam n t b bi => pure (.lam n (← foldRefs elimOf t) (← foldRefs elimOf b) bi)
    | .forallE n t b bi => pure (.forallE n (← foldRefs elimOf t) (← foldRefs elimOf b) bi)
    | .letE n t v b nd =>
      pure (.letE n (← foldRefs elimOf t) (← foldRefs elimOf v) (← foldRefs elimOf b) nd)
    | .proj s i b => pure (.proj s i (← foldRefs elimOf b))
    | .mdata _ b => foldRefs elimOf b
    | _ => pure e
  modify (·.insert e r)
  return r

/-- Every declaration with an eliminating universe of its own, and the numerals
the file uses it at. `elimDefs` is mode A's own answer for the non-recursors —
the declaration-local model recursors and iota theorems. -/
def elimUses (x : Export) (defaults : Array Nat) (elimDefs : Std.HashSet Name) :
    Std.HashMap Name (Array Nat) := Id.run do
  let mut ws : Std.HashMap Name (Array Nat) := {}
  for d in x.decls do
    if let .induct _ _ rs := d then
      for r in rs do
        if r.levelParams.length == 1 then ws := ws.insert r.name #[]
  for n in elimDefs do ws := ws.insert n #[]
  let mut seen : Std.HashSet Expr := {}
  for d in x.decls do
    for root in rootsOf d do
      let mut stack : Array Expr := #[root]
      while stack.size > 0 do
        let e := stack[stack.size - 1]!
        stack := stack.pop
        if seen.contains e then continue
        seen := seen.insert e
        match e with
        | .const n [l] =>
          if let some a := ws[n]? then
            if let some k := l.toNat then ws := ws.insert n (addNat a k)
        | .app f a => stack := (stack.push f).push a
        | .lam _ t b _ | .forallE _ t b _ => stack := (stack.push t).push b
        | .letE _ t v b _ => stack := ((stack.push t).push v).push b
        | .proj _ _ b | .mdata _ b => stack := stack.push b
        | _ => pure ()
  for (n, a) in ws.toArray do if a.isEmpty then ws := ws.insert n defaults
  return ws

/-- **Mode B.** -/
def foldElim (x : Export) (defaults : Array Nat) (elimDefs : Std.HashSet Name) :
    Export := Id.run do
  let ws := elimUses x defaults elimDefs
  let names : Std.HashSet Name := ws.toArray.foldl (fun s (n, _) => s.insert n) {}
  let fold (e : Expr) : Expr := (foldRefs names e).run' {}
  -- A model recursor or iota theorem splits exactly as a recursor does: one copy per
  -- numeral the file uses it at, the universe substituted and folded into the
  -- name. `all` names the copy, as everywhere else in this pass. A declaration
  -- that does not split is rebuilt unchanged, `all` included.
  let split (n : Name) (l : List Name) (a : List Name)
      (mk : Name → List Name → List Name → (Expr → Expr) → EDecl) : List EDecl :=
    match l, ws[n]? with
    | [u], some vals => vals.toList.map fun w =>
      let n' := elimName n w
      mk n' [] [n'] (fun e => fold (e.instantiateLevelParams [u] [natLevel w]))
    | _, _ => [mk n l a fold]
  let mut out : Array EDecl := #[]
  for d in x.decls do
    out := out.appendList <|
      match d with
      | .ax n l t u => split n l [] fun n' l' _ s => .ax n' l' (s t) u
      | .defn n l t v h sf a => split n l a fun n' l' a' s => .defn n' l' (s t) (s v) h sf a'
      | .thm n l t v a => split n l a fun n' l' a' s => .thm n' l' (s t) (s v) a'
      | .opaq n l t v u a => split n l a fun n' l' a' s => .opaq n' l' (s t) (s v) u a'
      | .quot n l t k => [.quot n l t k]
      | .induct ts cs rs =>
        let rs' := rs.flatMap fun r =>
          match r.levelParams, ws[r.name]? with
          | [u], some vals => vals.toList.map fun w =>
            let sub (e : Expr) : Expr := fold (e.instantiateLevelParams [u] [natLevel w])
            { r with name := elimName r.name w, levelParams := [], type := sub r.type
                     rules := r.rules.map fun rr => { rr with rhs := sub rr.rhs } }
          | _, _ => [{ r with type := fold r.type
                              rules := r.rules.map fun rr => { rr with rhs := fold rr.rhs } }]
        [.induct (ts.map fun t => { t with type := fold t.type })
          (cs.map fun c => { c with type := fold c.type }) rs']
  return { x with decls := out }

/-- **Topological sortedness, asserted rather than assumed** — the reason the
sweep can be one backward pass and not a fixpoint.

The property is a claim about `lean4export`, not about the format, so it is
checked: no group may mention a name a later group declares. The failure it
catches is silent otherwise — a group read before its user is instantiated at
too few `σ`, and the output is a well-formed file missing copies — so this is a
refusal and not a warning.

It is stated over *groups* because groups are what the sweep visits, which is
what made [`buildGroups`]' old `all`-based grouping visible here: five Mathlib
blocks were reported as forward references that the grouping had itself created
(`MONOMORPH.md` §9.3). The check was right and the grouping was wrong — and the
check is what said so, which is the argument for keeping it. -/
def checkOrder (n : Nat) (refs : Array (Array (Name × List Level)))
    (info : Std.HashMap Name Info) : Option String := Id.run do
  for gi in [0 : n] do
    for (nm, _) in refs[gi]! do
      if let some i := info[nm]? then
        if i.group > gi then
          return some s!"the file is not topologically sorted: group {gi} \
            mentions {nm}, which group {i.group} declares"
  return none

/-- **The pass.** -/
def monomorphize (x : Export) (opts : Opts) : MetaM (Export × Report) := do
  let mut rep : Report :=
    { recordsIn := x.decls.size, declsIn := x.decls.foldl (fun a d => a + declCount d) 0 }
  -- The markers must not already be in use, or the scheme is not invertible.
  for d in x.decls do
    for n in d.names do
      if usesMarker n then
        return (x, { rep with refused := some s!"the file already declares {n}, which spells a marker" })
  phase "entry"
  let base ← getEnv
  let models := modelTable x
  let (groups, info) ←
    match buildGroups x models with
    | .error e => return (x, { rep with refused := some e })
    | .ok r => pure r
  rep := { rep with groups := groups.size }

  -- ── The reference set of each group: every constant it mentions, at the
  -- level arguments it mentions it at.
  let mut refs : Array (Array (Name × List Level)) := Array.replicate groups.size #[]
  let mut anyProj := false
  for gi in [0 : groups.size] do
    let mut seen : Std.HashSet Expr := {}
    let mut out : Array (Name × List Level) := #[]
    let mut p := false
    for r in rootsOf x.decls[groups[gi]!.decl]! do
      let ((), (s, o, q)) := (collectConsts r).run (seen, out, p)
      seen := s; out := o; p := q
    refs := refs.set! gi out
    if p then anyProj := true
  phase "refs"

  -- ── The projections. `Expr.proj` does not carry the structure's level
  -- arguments, so they are inferred — which needs the input replayed. A file
  -- with no projection never pays for this, and a file the kernel will not
  -- replay at all is refused whole rather than half done.
  -- **Refused rather than trusted.** [`Export.projNodes`] is empty both when
  -- the file has no projection and when the reader was not asked to compute it,
  -- and the second reading would make [`hasProj`] answer `false` everywhere:
  -- every projection would take the memoised path, keep its input structure
  -- name, and the file would come out wrong with no error. `anyProj` is
  -- computed here, from the input, by [`collectConsts`] — so the two disagree
  -- exactly when the reader was not asked, and that is caught.
  let projCache := x.projNodes
  if anyProj && projCache.isEmpty then
    return (x, { rep with refused := some "the file has projections but was read \
      without `analyse`, so `Export.projNodes` is empty" })
  let mut projGroups := 0
  let mut projSites := 0
  if anyProj then
    for gi in [0 : groups.size] do
      let d := x.decls[groups[gi]!.decl]!
      if let some dcl := toDeclaration (← getEnv) d then
        match (← getEnv).addDeclCore 0 dcl none false with
        | .ok e => setEnv e
        | .error ex =>
          let msg ← (ex.toMessageData {}).toString
          return (x, { rep with refused := some s!"{d.names} did not replay: {msg}" })
      let out ← IO.mkRef (#[] : Array (Name × List Level))
      for r in rootsOf d do projScan projCache out #[] r
      let got ← out.get
      unless got.isEmpty do projGroups := projGroups + 1; projSites := projSites + got.size
      refs := refs.set! gi (refs[gi]! ++ got)

  phase "proj"
  if monoStats && anyProj then
    -- **How much of the replay a projection actually reaches.** The loop above
    -- replays every group because a later `projHead` may infer a type that
    -- mentions any earlier constant; the closure below is the *sound
    -- over-approximation* of what it could reach — the groups a
    -- projection-bearing group depends on, transitively. If that is most of
    -- the file the replay cannot be narrowed by dependency, and this is the
    -- measurement that says so rather than an argument about it.
    let mut need : Array Bool := Array.replicate groups.size false
    let mut hasP : Array Bool := Array.replicate groups.size false
    for gi in [0 : groups.size] do
      for r in rootsOf x.decls[groups[gi]!.decl]! do
        if hasProj projCache r then hasP := hasP.set! gi true
    -- Backward: a group is needed if it bears a projection or a needed group
    -- mentions it. One pass suffices — the file is topologically sorted.
    for k in [0 : groups.size] do
      let gi := groups.size - 1 - k
      if hasP[gi]! then need := need.set! gi true
      if need[gi]! then
        for (nm, _) in refs[gi]! do
          if let some i := info[nm]? then need := need.set! i.group true
    let needed := need.foldl (fun a b => if b then a + 1 else a) 0
    let bearing := hasP.foldl (fun a b => if b then a + 1 else a) 0
    let ms ← getThe Meta.State
    let pn {α β} [BEq α] [Hashable α] (m : Lean.PersistentHashMap α β) : Nat :=
      m.foldl (fun a _ _ => a + 1) 0
    IO.eprintln s!"[mono] proj: groups={groups.size} bearing={bearing} \
      needClosure={needed} sitesFound={projSites} inGroups={projGroups} \
      projNodes={projCache.size} \
      metaCache=infer:{pn ms.cache.inferType} whnf:{pn ms.cache.whnf} \
      defEqP:{pn ms.cache.defEqPerm} defEqT:{pn ms.cache.defEqTrans} \
      funInfo:{pn ms.cache.funInfo} \
      envConsts={(← getEnv).constants.fold (fun a _ _ => a + 1) 0}"
  -- **Two things that look droppable here and are not, both measured.**
  --
  -- *The replay environment.* Emission threads `monoEnv`, which is `base`, so
  -- nothing after this line reads `getEnv` by name — but [`rw`] calls
  -- [`projHead`] again at every projection it rewrites, and `projHead` is
  -- `inferType` in the ambient environment. Drop it and every
  -- projection-bearing declaration fails with an unknown constant. The replay
  -- is live until the last copy is emitted.
  --
  -- *`MetaM`'s `inferType`/`whnf`/`defEq` caches.* Clearing them is always safe
  -- — they are pure memos — and it buys **nothing**, because they are empty:
  -- `0` entries in all five after 117,138 `projHead` calls on the ten-million
  -- line prefix, and `0` after 211 on `init-prelude`. Lean does not populate
  -- them for a query made under a `withLocalDecl` context. The clear was
  -- written, measured at zero, and removed rather than left in looking useful.
  if let some why := checkOrder groups.size refs info then
    return (x, { rep with refused := some why })

  -- ── The carried set: the built-ins, closed under "mentioned at a level a
  -- copy could not be chosen for".
  let seed : Std.HashSet Name := builtinSeed.foldl (·.insert ·) {}
  let mut carried : Std.HashSet Nat := {}
  for gi in [0 : groups.size] do
    let d := x.decls[groups[gi]!.decl]!
    match d with
    | .quot .. => carried := carried.insert gi
    | _ => if (introOf d).any (fun (n, _) => seed.contains n) then carried := carried.insert gi
  let mut changed := true
  while changed do
    changed := false
    for gi in [0 : groups.size] do
      if carried.contains gi then
        for (n, us) in refs[gi]! do
          if let some i := info[n]? then
            unless carried.contains i.group do
              if us.any (fun l => (l.toNat).isNone) then
                carried := carried.insert i.group
                changed := true

  phase "carried"
  -- ── The models, keyed to what they model. The keying needs the carried set
  -- (a carried group has no `σ` to key to) and the sweep needs the keying, so
  -- it goes exactly here.
  let keying := modelKeying x groups info models refs carried
  let modelGroups := keying.owner.foldl (fun a o => if o.isSome then a + 1 else a) 0
  let modelLoose := keying.loose.foldl (fun a b => if b then a + 1 else a) 0
  if monoStats then
    IO.eprintln s!"[mono] models: keyed={modelGroups} loose={modelLoose} \
      declined={keying.declined.size} renamed={keying.renamed}"
  phase "keying"
  -- ── The backward sweep.
  let mut demand : Array (Array Inst) := Array.replicate groups.size #[]
  let mut elimD : Array (Array Nat) := Array.replicate groups.size #[]
  let mut errors : Array String := #[]
  let mut late : Array Nat := #[]
  let mut defaulted := 0
  for k in [0 : groups.size] do
    let gi := groups.size - 1 - k
    let g := groups[gi]!
    let isCarried := carried.contains gi
    let isModel := keying.owner[gi]!.isSome
    -- **A model does not default.** Its `σ` set is the one the declaration it
    -- models takes, and the cascade below delivers it — from the owner's own
    -- demand, or from the owner's default at the owner's visit. Falling back to
    -- `--default` here is exactly `MONOMORPH.md` §1.3 item 1: one model for
    -- however many copies of `T` the file wants.
    if !isCarried && !isModel && demand[gi]!.isEmpty then
      defaulted := defaulted + 1
      -- The tenth family's reading is that it is demanded like anything else
      -- ([`Keying.loose`]). One that is not is a model declaration taking a
      -- default, which is the thing this pass must not do quietly.
      if keying.loose[gi]! then
        errors := errors.push
          s!"{x.decls[g.decl]!.names[0]!}: a model declaration nothing demands, at the default"
      for l in opts.defaults do
        let (d, lt) := pushInst keying.models gi (demand, late) gi
          (Array.replicate g.levelParams.length l)
        demand := d; late := lt
    let sigmas := if isCarried then #[(#[] : Inst)] else demand[gi]!
    let ws := if g.elims.isEmpty then #[0] else
      (if elimD[gi]!.isEmpty then opts.defaults else elimD[gi]!)
    if !g.elims.isEmpty && elimD[gi]!.isEmpty then
      elimD := elimD.set! gi opts.defaults
    for σ in sigmas do
      for w in ws do
        let mut env : Std.HashMap Name Nat := {}
        unless isCarried do
          for (p, v) in g.levelParams.zip σ.toList do env := env.insert p v
          for p in g.elims do env := env.insert p w
        for (n, us) in refs[gi]! do
          let some i := info[n]? | continue
          if carried.contains i.group then continue
          let us' := us.map (fun l => (substLevel env l).normalize)
          let (wv, rest) := match i.elim, us' with
            | some _, a :: r => (a.toNat, r)
            | _, r => (none, r)
          if rest.any (fun l => l.toNat.isNone) then
            errors := errors.push s!"{n}: a level argument did not evaluate to a numeral"
            continue
          let σt : Inst := (rest.map (fun l => l.toNat.getD 0)).toArray
          if i.group == gi then
            unless demand[gi]!.contains σt do
              errors := errors.push s!"{n}: the group demands itself at a new instantiation"
          else
            let (d, lt) := pushInst keying.models gi (demand, late) i.group σt
            demand := d; late := lt
          if let some wk := wv then
            if i.group == gi then
              unless elimD[gi]!.contains wk do
                errors := errors.push s!"{n}: the group demands itself at a new eliminating universe"
            else elimD := elimD.set! i.group (addNat elimD[i.group]! wk)
  -- **What the keying could not decide, named.** A model group the cascade
  -- never reached has no `σ` of its own and is emitted at none: the pass says
  -- which, rather than inventing one and leaving the file quietly wrong.
  for gi in [0 : groups.size] do
    if keying.owner[gi]!.isSome && !carried.contains gi && demand[gi]!.isEmpty then
      errors := errors.push
        s!"{x.decls[groups[gi]!.decl]!.names[0]!}: a model the sweep never keyed"
  for gi in late do
    errors := errors.push
      s!"{x.decls[groups[gi]!.decl]!.names[0]!}: a model reached after the sweep passed it"
  errors := errors ++ keying.declined
  rep := { rep with defaulted, modelGroups, modelLoose, modelDeclined := keying.declined.size }
  -- The sweep is the last reader of `refs` — the carriers and emission below
  -- ask `info` and `demand`, never this — and releasing it here explicitly was
  -- tried and **measured at nothing**: 1,797,792 KB against 1,796,272 KB on the
  -- 10 M prefix. The compiler already drops it at its last use, and the pages
  -- go to the carriers either way.
  phase "sweep"

  -- ── Emission, forward, so the output keeps the input's order, and so that
  -- each monomorphized block can be replayed into `monoEnv` before the next
  -- one needs its constants.
  let errRef ← IO.mkRef errors
  let mut monoEnv := base
  let mut recRegen := 0
  let mut addFailed : Array String := #[]
  let mut out : Array EDecl := #[]
  let mut hist : Std.HashMap Nat Nat := {}
  let mut recArity : Std.HashMap Name Nat := {}
  let mut elimDefs : Std.HashSet Name := {}
  -- **The memo outlives the copy.** See [`RwState`]: the input's sharing is
  -- across declarations, so a memo that is per-declaration preserves none of
  -- it, and `MONOMORPH.md` §9.8 counts what that costs — 2.26× the nodes at ten
  -- million lines.
  let st ← IO.mkRef ({} : RwState)
  let pidx := paramIndex groups
  -- The carrier of every node, and — under a gating mode — which nodes the
  -- arena shares. Both are computed once, before the first copy, and the
  -- working sets they need are dropped before emission allocates anything.
  let mut carrier : Std.HashMap Expr UInt64 := {}
  let mut sharedPure : Std.HashSet Expr := {}
  let gating := memoMode == .fullGate || memoMode == .pruneGate || memoMode == .pruneArray
  if memoMode != .off && memoMode != .pure then
    let roots := x.decls.flatMap rootsOf
    let mut keep : Option (Std.HashSet Expr) := none
    if gating then
      -- The `seen` set this needs is over every node, and it is dropped here —
      -- before the carriers, so the two working sets never coexist.
      -- **The size is passed to `phase` because that is what forces it.**
      -- `sharedNodes` is pure, so `let shared := …` alone is floated to its
      -- first use and the marker below landed *before* the work it claims to
      -- bound — a 232 ms "shared" phase on the full file, measuring nothing.
      -- Lean is call-by-value, so an argument mentioning `shared` is not.
      let shared := sharedNodes roots
      phase "shared" (n := shared.size)
      for e in shared do unless e.hasLevelParam do sharedPure := sharedPure.insert e
      keep := some shared
    let cc ← IO.mkRef ({} : Std.HashMap Expr UInt64)
    for r in roots do discard <| carrierOf pidx keep cc r
    carrier := ← cc.get
    if monoStats then
      IO.eprintln s!"[mono] params={pidx.size} carrierEntries={carrier.size} sharedPure={sharedPure.size}"
    phase "carriers"
  for gi in [0 : groups.size] do
    let g := groups[gi]!
    let isCarried := carried.contains gi
    let sigmas := if isCarried then #[(#[] : Inst)] else demand[gi]!
    hist := hist.insert sigmas.size ((hist[sigmas.size]?.getD 0) + 1)
    for σ in sigmas do
      let mut env : Std.HashMap Name Nat := {}
      unless isCarried do
        for (p, v) in g.levelParams.zip σ.toList do env := env.insert p v
      -- This copy's substitution, by **global** parameter index and sorted, so
      -- that it means the same thing in every declaration that reaches the same
      -- node. §"The memo's key" is why that is the property that matters.
      let binding : Array (Nat × Nat) :=
        (env.toArray.filterMap (fun (n, v) => (pidx[n]?).map (·, v))).qsort (·.1 < ·.1)
      let lpMask := binding.foldl (fun m (j, _) => m ||| carrierBit j) 0
      let envId ← st.modifyGet fun t => (sigmaId binding).run t
      let c : RwCtx :=
        { info, carried, opts, env, sigma := σ, recArity
          carrier, sharedPure, binding, lpMask, envId, mode := memoMode }
      -- The mask table is this copy's. Under `off` so is everything.
      st.modify fun t =>
        { t with maskIds := {}
                 pure := if memoMode == .off then {} else t.pure
                 poly := if memoMode == .off || memoMode == .pure then {} else t.poly }
      let mut e ← emitOne c projCache st isCarried g.levelParams x.decls[g.decl]!
      -- The non-recursor copies that came out with an eliminating universe
      -- still standing — model recursors and iota theorems. Mode B needs the
      -- list and must not guess it back off the output file.
      unless isCarried || g.elims.isEmpty do
        match e with
        | .induct .. => pure ()
        | _ => elimDefs := elimDefs.insert e.names[0]!
      -- Replay, so that a block's recursors are the kernel's own and so that
      -- the next block can be elaborated against this one.
      if let some dcl := toDeclaration monoEnv e then
        match monoEnv.addDeclCore 0 dcl none opts.check with
        | .ok m =>
          monoEnv := m
          if let .induct ts cs rs := e then
            let (rs', d) := kernelRecs monoEnv rs
            recRegen := recRegen + d
            e := .induct ts cs rs'
        | .error ex =>
          addFailed := addFailed.push s!"{e.names}: {← (ex.toMessageData {}).toString}"
      if let .induct _ _ rs := e then
        for r in rs do recArity := recArity.insert r.name r.levelParams.length
      out := out.push e
      -- Drained, not copied: the memo is shared across groups now, so the error
      -- array in it is too.
      let es ← st.modifyGet fun t => (t.errs, { t with errs := #[] })
      unless es.isEmpty do errRef.modify (· ++ es)
  phase "emit"
  if monoStats then
    let inRoots := x.decls.flatMap rootsOf
    let (ip, is) := shareStats inRoots
    IO.eprintln s!"[mono] input  nodes: ptr={ip} struct={is} dup={(1000*ip)/(max is 1)}/1000"
    phase "stats-in"
    let outRoots := out.flatMap rootsOf
    let (op, os) := shareStats outRoots
    IO.eprintln s!"[mono] output nodes: ptr={op} struct={os} dup={(1000*op)/(max os 1)}/1000"
    let t ← st.get
    IO.eprintln s!"[mono] memo entries: pure={t.pure.size} poly={t.poly.size + t.polyA.size} \
      distinct pruned σ={t.sigmaIds.size}"
    phase "stats-out"
  let mut carriedNames : Array Name := #[]
  for gi in [0 : groups.size] do
    if carried.contains gi then
      carriedNames := carriedNames.push (x.decls[groups[gi]!.decl]!.names[0]!)
  -- Every output name is a distinct one. The marker guard is what makes the
  -- scheme *invertible*; this is what makes it collision-free, and it is a
  -- check rather than an argument.
  let mut seenNames : Std.HashSet Name := {}
  for d in out do
    for n in d.names do
      if seenNames.contains n then
        return (x, { rep with refused := some s!"two output declarations are both named {n}" })
      seenNames := seenNames.insert n
  let y : Export := { x with decls := out }
  let y := if opts.monoRecursors then foldElim y opts.defaults elimDefs else y
  rep := { rep with
    errors := (← errRef.get) ++ addFailed, carried := carriedNames
    recRegen, rejected := addFailed.size
    recordsOut := y.decls.size, declsOut := y.decls.foldl (fun a d => a + declCount d) 0
    hist := hist.toArray.qsort (fun a b => a.1 < b.1) }
  return (y, rep)
