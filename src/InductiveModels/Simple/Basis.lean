import InductiveModels.Mutual
import InductiveModels.Naming
import InductiveModels.Projection

/-!
# The trusted basis, its owners' exact declarations, and their splices

The five basis names, the canonical declaration of each ordinary inductive
owner, the exact-record validation an exempt owner must pass, and the
`ensure*` splices that install a missing one.
-/

open Lean Meta

namespace InductiveModels

/-- The complete trusted basis, by principal name.

`Quot` denotes Lean's kernel-special quotient bundle (`Quot`, `Quot.mk`,
`Quot.lift`, and `Quot.ind`), not an ordinary inductive declaration. It is
nevertheless part of the advertised basis: generated proofs may use it to
derive `funext` from `Quot.sound`. -/
def basis : List Name := [`Eq, `PSigma', `Nat, `PUnit, `Quot]

/-- The ordinary inductive subset of [`InductiveModels.basis`]. Declarations in this
set are not modelled — the exemption that makes the construction
well-founded. `Quot` is handled by the kernel's quotient declaration path
instead, so it does not participate in this owner-exemption test.

**`Acc` was the fifth and is not here any more.** Its one grant — the
subsingleton-recursive large eliminator — is derived by
[`InductiveModels.graphArm`], so `Acc` is an ordinary declaration and models like
one. `Nonempty` never joins this list either, though the graph arm names it:
`Classical.choice`'s domain is not an exemption, and it self-models.

`False` is **not** among them: it is derived (Church `∀ p : Prop, p`, with
its `Sort w` eliminator from `0 = 1` plus a `Nat.rec`-built family to
transport along — [`InductiveModels.cfalseElim`]), so `False` models like any other
declaration. The tight pair and `PUnit` together take its place. -/
def inductiveBasis : List Name := [`Eq, `PSigma', `Nat, `PUnit]

/-- **Lean's `PUnit`**, exactly as `Init/Prelude.lean` declares it:
`inductive PUnit.{u} : Sort u | unit : PUnit`.

Like the tight pair below, this crosses Lean's bootstrap resulting-universe
boundary: at `u = 0` the result is a proposition, while at positive levels it
is a type.  The kernel accepts the declaration and gives its ordinary
universe-polymorphic eliminator.  Paired with `PSigma'`, it supplies the
inhabited exact-sort fibre used by the internally derived propositional lift. -/
def punitDecl : Declaration :=
  let lu := Level.param `u
  .inductDecl [`u] 0
    [{ name := `PUnit, type := .sort lu,
       ctors := [{ name := `PUnit.unit, type := .const `PUnit [lu] }] }] false

/-- **Lean's `Nat`**, as `Init/Prelude.lean` declares it. The models build
tags as `succ` chains, so nothing here depends on literals. -/
def natDecl : Declaration :=
  let nat : Expr := .const `Nat []
  .inductDecl [] 0
    [{ name := `Nat, type := .sort (.succ .zero)
       ctors := [{ name := `Nat.zero, type := nat },
                 { name := `Nat.succ, type := .forallE `n nat nat .default }] }] false

/-! ## The tight dependent-pair primitive

`PSigma'` differs from Lean's `PSigma` only in its resulting universe:
`Sort (max u v)`, with no built-in `1`.  The declaration crosses the same
bootstrap boundary: the result may specialize to `Prop`, so Lean's
surface inductive checker refuses it while the kernel accepts the declaration.

Only the inductive and its constructor are primitive.  The named projections
and the universe-polymorphic eliminator below are ordinary definitions over
primitive `.proj` expressions.  In particular, `PSigma'.rec'` does not add a
second kernel exception: structure eta makes `mk t.1 t.2` convertible to `t`,
so `fun h t => h t.1 t.2` has an arbitrary `Sort w` motive and its constructor
rule is reflexivity. -/

def psigmaPrimeDecl : Declaration :=
  let lu := Level.param `u
  let lv := Level.param `v
  let ty : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default)
      (.sort (mkLevelMax' lu lv)) .default) .implicit
  let mkTy : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default)
      (.forallE `fst (.bvar 1)
        (.forallE `snd (.app (.bvar 1) (.bvar 0))
          (mkAppN (.const `PSigma' [lu, lv]) #[.bvar 3, .bvar 2]) .default)
        .default) .implicit) .implicit
  .inductDecl [`u, `v] 2
    [{ name := `PSigma', type := ty,
       ctors := [{ name := `PSigma'.mk, type := mkTy }] }] false

/-! ## Exact basis-owner validation

A declaration is exempt because a consumer is expected to implement its
*particular kernel interface*, not merely because it owns one of four reserved
names. Validate that interface even when no generated model happens to use the
declaration later in the stream.

The expected record is minted by this same kernel from the canonical
declaration under a disposable fresh alias. Renaming it back gives every piece
of metadata the export carries: the inductive, constructor and recursor types,
their order and counts, recursor rules, flags, and safety bits. -/

private def basisCanonicalDecl? : Name → Option Declaration
  | `Eq => some eqDecl
  | `Nat => some natDecl
  | `PUnit => some punitDecl
  | `PSigma' => some psigmaPrimeDecl
  | _ => none

private def basisRecordFromEnv (env : Environment) (root : Name) : Except String EDecl := do
  let some (.inductInfo type) := env.constants.find? root
    | throw s!"{root} is not an inductive type"
  let mut constructors : Array ECtor := #[]
  for constructorName in type.ctors do
    let some (.ctorInfo constructor) := env.constants.find? constructorName
      | throw s!"{constructorName} is not a constructor"
    constructors := constructors.push
      { name := constructor.name, levelParams := constructor.levelParams,
        type := constructor.type, cidx := constructor.cidx,
        numParams := constructor.numParams, numFields := constructor.numFields,
        induct := constructor.induct, isUnsafe := constructor.isUnsafe }
  let recursorName := Name.str root "rec"
  let some (.recInfo recursor) := env.constants.find? recursorName
    | throw s!"{recursorName} is not a recursor"
  let exportedRecursor : ERec :=
    { name := recursor.name, levelParams := recursor.levelParams, type := recursor.type,
      all := recursor.all, numParams := recursor.numParams,
      numIndices := recursor.numIndices, numMotives := recursor.numMotives,
      numMinors := recursor.numMinors,
      rules := recursor.rules.map fun rule =>
        { ctor := rule.ctor, nfields := rule.nfields, rhs := rule.rhs },
      k := recursor.k, isUnsafe := recursor.isUnsafe }
  let exportedType : EIndType :=
    { name := type.name, levelParams := type.levelParams, type := type.type,
      all := type.all, ctors := type.ctors, numParams := type.numParams,
      numIndices := type.numIndices, numNested := type.numNested,
      isRec := type.isRec, isReflexive := type.isReflexive,
      isUnsafe := type.isUnsafe }
  return .induct [exportedType] constructors.toList [exportedRecursor]

private def basisAliasNames (root alias : Name) : Name → Option Name := fun name =>
  if root.isPrefixOf name then some (name.replacePrefix root alias) else none

private def aliasBasisDeclaration (root alias : Name) : Declaration → Declaration
  | .inductDecl levelParams numParams types isUnsafe =>
    let rename := fun name => (basisAliasNames root alias name).getD name
    let rewrite := mapConstsE (basisAliasNames root alias)
    .inductDecl levelParams numParams (types.map fun type =>
      { name := rename type.name, type := rewrite type.type,
        ctors := type.ctors.map fun constructor =>
          { name := rename constructor.name, type := rewrite constructor.type } }) isUnsafe
  | declaration => declaration

private partial def freshBasisAlias (env : Environment) (root : Name)
    (canonical : Declaration) (attempt : Nat := 0) : Name :=
  let stem := (`_inductive_models_basis_validation).mkNum attempt
  let alias := stem ++ root
  let declarationNames := canonical.getNames.map fun name =>
    if root.isPrefixOf name then name.replacePrefix root alias else name
  let names := Name.str alias "rec" :: declarationNames
  if names.any env.constants.contains then
    freshBasisAlias env root canonical (attempt + 1)
  else alias

def alignBasisLevelParams (declaration : Declaration) (actual : List Name) : Declaration :=
  match declaration with
  | .inductDecl expected numParams types isUnsafe =>
    if expected.length != actual.length then declaration else
      let levels := actual.map Level.param
      .inductDecl actual numParams (types.map fun type =>
        { type with
          type := type.type.instantiateLevelParams expected levels,
          ctors := type.ctors.map fun constructor =>
            { constructor with
              type := constructor.type.instantiateLevelParams expected levels } }) isUnsafe
  | _ => declaration

/-- **The export record a canonical inductive declaration produces**, at the
level-parameter names `levelParams`, minted by this same kernel under a
disposable fresh alias and renamed back. Comparing an input record against it
is a byte comparison over every piece of metadata the export carries. -/
private def canonicalInductiveRecord (root : Name) (canonical : Declaration)
    (levelParams : List Name) : MetaM (Except String EDecl) := do
  let env ← getEnv
  let canonical := alignBasisLevelParams canonical levelParams
  let alias := freshBasisAlias env root canonical
  let canonical := aliasBasisDeclaration root alias canonical
  let expectedEnv ← match env.addDeclCore 0 canonical none true with
    | .ok next => pure next
    | .error exception =>
      return .error s!"cannot mint the canonical {root} interface: \
        {← (exception.toMessageData {}).toString}"
  let expectedAlias ← match basisRecordFromEnv expectedEnv alias with
    | .ok record => pure record
    | .error message =>
      return .error s!"cannot read the canonical {root} interface: {message}"
  return .ok <| EDecl.mapNames
    (fun name => if alias.isPrefixOf name then name.replacePrefix alias root else name)
    (mapConstsE fun name =>
      if alias.isPrefixOf name then some (name.replacePrefix alias root) else none)
    expectedAlias

/-- Require an encountered basis owner to be the exact canonical declaration
family before it may be reported as an exemption. A noncanonical declaration
is never a successful exemption. -/
def validateBasisOwner (root : Name) (owner : EDecl) : GenM Unit := do
  let .induct (type :: _) _ _ := owner
    | badShape "the basis owner is not a nonempty inductive record"
  let some canonical := basisCanonicalDecl? root
    | badShape s!"{root} is not a basis owner"
  let expected ← match ← canonicalInductiveRecord root canonical type.levelParams with
    | .ok expected => pure expected
    | .error message => badShape message
  unless owner == expected do
    declineWith (.notLeans root
      "its complete inductive, constructor, and recursor metadata is not canonical")

/-- **Whether an input record is the canonical basis declaration itself.**

The same comparison [`InductiveModels.validateBasisOwner`] makes, asked before the
record is reached rather than at it. A record that passes carries no
information the canonical declaration does not: writing that declaration and
replaying this record are the same act. -/
def isCanonicalInductiveRecord (root : Name) (canonical : Declaration)
    (record : EDecl) : MetaM Bool := do
  let .induct (type :: _) _ _ := record | return false
  unless type.name == root do return false
  match ← canonicalInductiveRecord root canonical type.levelParams with
  | .ok expected => return record == expected
  | .error _ => return false

def psigmaPrimeT (u v : Level) (α β : Expr) : Expr :=
  mkAppN (.const `PSigma' [u, v]) #[α, β]

def psigmaPrimeMk (u v : Level) (α β fst snd : Expr) : Expr :=
  mkAppN (.const `PSigma'.mk [u, v]) #[α, β, fst, snd]

def psigmaPrimeFst (u v : Level) (α β self : Expr) : Expr :=
  mkAppN (.const `PSigma'.fst [u, v]) #[α, β, self]

def psigmaPrimeSnd (u v : Level) (α β self : Expr) : Expr :=
  mkAppN (.const `PSigma'.snd [u, v]) #[α, β, self]

def psigmaPrimeRec (u v w : Level) (α β motive minor self : Expr) : Expr :=
  mkAppN (.const `PSigma'.rec' [u, v, w]) #[α, β, motive, minor, self]

/-- One primitive, checked or spliced. `check` runs on a present declaration
and says what is wrong with it; a missing one is spliced at Lean's shape and
re-checked. The pattern is [`InductiveModels.ensureEq`]'s.

**There is no reserved-name guard here, and that is the point.** A canonical
basis name is one this tool writes itself, at a declaration it holds. Where
the input declares one *later* in the stream, waiting for it would emit an
island against a constant the output does not declare until afterwards; so the
canonical declaration is written here, at the first point it is needed, and the
input's own later record is dropped against it
([`InductiveModels.canonicalBasisRecordMatches`]). -/
def ensurePrim (n : Name) (d : Declaration)
    (check : Environment → Except String Unit) :
    GenM (Array Declaration) := do
  if (← getEnv).constants.contains n then
    match check (← getEnv) with
    | .ok () => return #[]
    | .error why => declineWith (.notLeans n why)
  addChecked d
  match check (← getEnv) with
  | .ok () => return #[d]
  | .error why => badShape s!"the spliced {n} is not Lean's ({why})"

/-- Validate the exact standard polymorphic unit, including its arbitrary-sort
eliminator.  A merely similarly named singleton is not accepted as basis
support. -/
def checkPUnit (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `PUnit
    | throw "it is not an inductive type"
  unless iv.numParams == 0 && iv.numIndices == 0 && iv.ctors == [`PUnit.unit]
      && iv.levelParams.length == 1 do
    throw "it is not a nullary, one-constructor polymorphic unit"
  let [u] := iv.levelParams | throw "it does not have one universe parameter"
  unless iv.type == .sort (.param u) do throw "it does not land in exactly `Sort u`"
  let some (.ctorInfo constructor) := env.constants.find? `PUnit.unit
    | throw "PUnit.unit is not its constructor"
  unless constructor.type == .const `PUnit [.param u] && constructor.numFields == 0 do
    throw "PUnit.unit is not the fieldless canonical constructor"
  let some (.recInfo recursor) := env.constants.find? `PUnit.rec
    | throw "PUnit.rec is not a recursor"
  let [v, u] := recursor.levelParams
    | throw "PUnit.rec is not universe-polymorphic in its motive"
  unless recursor.numParams == 0 && recursor.numMotives == 1 &&
      recursor.numMinors == 1 && recursor.numIndices == 0 &&
      recursor.rules.length == 1 && recursor.rules[0]!.ctor == `PUnit.unit do
    throw "PUnit.rec does not have the standard fieldless-singleton recursor metadata"
  let punit := Expr.const `PUnit [.param u]
  let unit := Expr.const `PUnit.unit [.param u]
  let motiveType := Expr.forallE `self punit (.sort (.param v)) .default
  let expectedRecursor := Expr.forallE `motive motiveType
    (.forallE `unitCase (.app (.bvar 0) unit)
      (.forallE `t punit (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit
  unless recursor.type == expectedRecursor do
    throw "PUnit.rec does not have the exact standard arbitrary-sort statement"

/-- `Nat` at Lean's shape, **including the large elimination the whole Type
route rests on**: `Nat.rec` must carry a motive universe. This property is
checked rather than assumed — on the input's own `Nat` as much as on a
spliced one. -/
def checkNat (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `Nat | throw "it is not an inductive type"
  unless iv.numParams == 0 && iv.numIndices == 0 && iv.ctors == [`Nat.zero, `Nat.succ] do
    throw "it is not zero/succ with 0 parameters and 0 indices"
  unless iv.type == Expr.sort (.succ .zero) do throw "it does not land in Type"
  let some (.recInfo rv) := env.constants.find? `Nat.rec | throw "Nat.rec is not a recursor"
  unless rv.levelParams.length == 1 do
    throw "Nat.rec is not large-eliminating (no motive universe)"

/-- Validate the only trusted part of the tight pair bundle: the kernel
inductive and constructor.  The named projections and `rec'` are checked as
ordinary derived declarations by [`InductiveModels.ensurePSigmaPrime`]. -/
def checkPSigmaPrimeCore (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `PSigma'
    | throw "it is not an inductive type"
  unless iv.numParams == 2 && iv.numIndices == 0 && iv.ctors == [`PSigma'.mk]
      && iv.levelParams.length == 2 do
    throw "it is not a two-parameter, one-constructor tight Sort-polymorphic pair"
  let [u, v] := iv.levelParams | throw "it does not have two universe parameters"
  let expectedType := match psigmaPrimeDecl with
    | .inductDecl _ _ [value] _ =>
      value.type.instantiateLevelParams [`u, `v] [.param u, .param v]
    | _ => unreachable!
  unless iv.type == expectedType do
    throw "its type is not `{α : Sort u} → (α → Sort v) → Sort (max u v)`"
  let some (.ctorInfo constructor) := env.constants.find? `PSigma'.mk
    | throw "PSigma'.mk is not its constructor"
  let expectedConstructor := match psigmaPrimeDecl with
    | .inductDecl _ _ [value] _ =>
      value.ctors[0]!.type.instantiateLevelParams [`u, `v] [.param u, .param v]
    | _ => unreachable!
  unless constructor.type == expectedConstructor && constructor.numFields == 2 do
    throw "PSigma'.mk does not retain exactly its dependent first and second components"

/-- **Lean's `Nonempty`**, as `Init/Prelude.lean` declares it:
`inductive Nonempty (α : Sort u) : Prop | intro (val : α) : Nonempty α`.

**It is not a basis primitive** and it is not on [`InductiveModels.basis`]'s list.
It is here for one reason: `Classical.choice`'s *own domain* is `Nonempty`, so
the graph arm ([`InductiveModels.graphArm`]) cannot state totality without naming it.
Unlike the five it does not need an exemption to keep the construction
well-founded — it is a non-recursive, small-eliminating `Prop`, so where the
input declares one the Church route models it like anything else, and the
model is emitted beside it as usual. What a *spliced* `Nonempty` costs is one
unmodelled inductive in that run's output, which is why the splice is reported
like every other. -/
def nonemptyDecl : Declaration :=
  let lu := Level.param `u
  let ty : Expr := .forallE `α (.sort lu) (.sort .zero) .default
  let introTy : Expr := .forallE `α (.sort lu)
    (.forallE `val (.bvar 0) (.app (.const `Nonempty [lu]) (.bvar 1)) .default) .implicit
  .inductDecl [`u] 1
    [{ name := `Nonempty, type := ty,
       ctors := [{ name := `Nonempty.intro, type := introTy }] }] false

def checkNonempty (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `Nonempty | throw "it is not an inductive type"
  unless iv.numParams == 1 && iv.numIndices == 0 && iv.ctors == [`Nonempty.intro]
      && iv.levelParams.length == 1 do
    throw "it is not a one-parameter, one-constructor lift with a single level parameter"
  match iv.type with
  | .forallE _ (.sort (.param _)) (.sort .zero) _ => pure ()
  | _ => throw "it is not `Sort u → Prop`"

/-- `Classical.choice`'s statement: `{α : Sort u} → Nonempty α → α`. One
builder for both uses — the input's own is compared against it with `isDefEq`
and a spliced one is declared at it, exactly as [`InductiveModels.funextType`] serves
`funext`. -/
def choiceType (lu : Level) : Expr :=
  .forallE `α (.sort lu)
    (.forallE `h (.app (.const `Nonempty [lu]) (.bvar 0)) (.bvar 1) .default) .implicit

def choiceDecl : Declaration :=
  .axiomDecl { name := `Classical.choice, levelParams := [`u]
               type := choiceType (.param `u), isUnsafe := false }

/-- **The binder Lean gives the argument of a non-dependent function type.**

`a✝`, whose macro scopes serialize as `a._@._internal._hyg.0`. It is not a
choice this tool gets to make: `Iff.intro`'s two fields *are* function types,
so a canonical `Iff` which named those binders anything else would not be the
declaration Lean's own export carries, and the comparison below is a byte
comparison. `basisvalidationtest` pins the canonical record against the
fragment the W arm actually splices, so a Lean release that spelled this
differently fails there rather than silently declining every W target. -/
def anonymousArrowBinder : Name :=
  .num (.str (.str (.str (.str .anonymous "a") "_@") "_internal") "_hyg") 0

/-- **Lean's `Iff`**, as `Init/Core.lean` declares it:
`structure Iff (a b : Prop) : Prop where intro :: mp : a → b; mpr : b → a`.

**It is not a basis primitive** and, like `Nonempty`, it does not need to be:
it is a non-recursive, small-eliminating `Prop`, so an input that declares one
is modelled like anything else. It is here because it is the only inductive in
the exact logical interface the W fragment shares with the input
([`InductiveModels.wCoreShared`]): `propext`'s statement names it, and standard-axiom
recognition keys on `propext`'s exact name, so the fragment cannot rename
either of them. -/
def iffDecl : Declaration :=
  let prop : Expr := .sort .zero
  let arrow := fun (domain codomain : Expr) =>
    Expr.forallE anonymousArrowBinder domain codomain .default
  let iff := fun (a b : Expr) => mkAppN (.const `Iff []) #[a, b]
  .inductDecl [] 2
    [{ name := `Iff, type := .forallE `a prop (.forallE `b prop prop .default) .default,
       ctors := [{ name := `Iff.intro,
                   type := .forallE `a prop
                     (.forallE `b prop
                       (.forallE `mp (arrow (.bvar 1) (.bvar 1))
                         (.forallE `mpr (arrow (.bvar 1) (.bvar 3))
                           (iff (.bvar 3) (.bvar 2)) .default)
                         .default)
                       .implicit)
                     .implicit }] }] false

/-- `propext`'s statement, as `Init/Core.lean` declares it:
`{a b : Prop} → Iff a b → Eq a b`. Stated at the `Eq` the caller names, the
way [`InductiveModels.quotSoundType`] and [`InductiveModels.funextType`] are, and
compared against the input's own with `isDefEq`. -/
def propextType (eqN : Name) : MetaM Expr := do
  let prop : Expr := .sort .zero
  withLocalDecl `a .implicit prop fun a =>
    withLocalDecl `b .implicit prop fun b =>
      withLocalDeclD `h (mkAppN (.const `Iff []) #[a, b]) fun h =>
        mkForallFVars #[a, b, h] (mkAppN (.const eqN [.succ .zero]) #[prop, a, b])

/-- **The inductive declarations this tool writes at a fixed canonical shape.**

Exactly the roots for which generation holds a `Declaration` of its own and
splices it when the input declares none: the four of
[`InductiveModels.inductiveBasis`]; `Nonempty`, which is not a basis primitive
but is `Classical.choice`'s own domain and is spliced by the graph arm on the
same terms; and `Iff`, which is `propext`'s own domain and which the W
fragment splices on those same terms. A name outside this list belongs to the
input alone — there is no declaration of this tool's own to write under it.

The declaration and the root travel together because the list is read for both:
the names each declaration introduces are what
[`InductiveModels.canonicalBasisNames`] is built from, and the declaration
itself is the shape written under that root. `Iff`'s copy here is the W
fragment's own, which `basisvalidationtest` pins. -/
def canonicalSpliceInductives : List (Name × Declaration) :=
  [(`Eq, eqDecl), (`Nat, natDecl), (`PUnit, punitDecl),
   (`PSigma', psigmaPrimeDecl), (`Nonempty, nonemptyDecl), (`Iff, iffDecl)]

/-- **Every name generation writes at a fixed canonical declaration of its
own** — the six inductives above with their constructors and kernel recursors,
the tight pair's six derived declarations, the kernel quotient's four records,
and the three axioms.

This is the complete hardcoded basis group and nothing else: it is a fixed
list, not a shape, count, or corpus test. Two rules are stated in terms of it
and no third: generation writes these declarations at the first point one is
needed, whatever the input reserves ([`InductiveModels.ensurePrim`]), and the
input's own later record at one of these names is dropped against the
declaration that was written ([`InductiveModels.canonicalBasisRecordMatches`]). -/
def canonicalBasisNames : Std.HashSet Name :=
  Std.HashSet.ofList <|
    (canonicalSpliceInductives.flatMap fun (_, declaration) => declaration.getNames) ++
      Declaration.quotDecl.getNames ++
      [`PSigma'.fst, `PSigma'.snd, `PSigma'.rec',
       `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec'_mk,
       `Quot.sound, `Classical.choice, `propext]

def ensurePUnit : GenM (Array Declaration) :=
  ensurePrim `PUnit punitDecl checkPUnit
def ensureNonempty : GenM (Array Declaration) :=
  ensurePrim `Nonempty nonemptyDecl checkNonempty

/-- **`Classical.choice`, the one axiom the graph arm asserts.** The input's
own where it declares one at Lean's statement; Lean's, spliced in, where it
does not. `funext` is *derived* from `Quot.sound` rather than asserted and
this one cannot be — it is an axiom in Lean too — so the asymmetry is the
subject matter's and not a shortcut. Axiom-freedom is not a goal of this
construction and the standard axioms may be used. -/
def ensureChoice : GenM (Array Declaration) := do
  match (← getEnv).constants.find? `Classical.choice with
  | some ci =>
    let [su] := ci.levelParams
      | declineWith (.notLeans `Classical.choice
          s!"it has {ci.levelParams.length} level parameters, where Lean's has 1")
    unless ← isDefEq ci.type (choiceType (.param su)) do
      declineWith (.notLeans `Classical.choice "its statement is not Lean's")
    return #[]
  | none =>
    addChecked choiceDecl
    return #[choiceDecl]
def ensureNat : GenM (Array Declaration) :=
  ensurePrim `Nat natDecl checkNat
/-- The ordinary declarations derived from the tight pair's two primitive
projections. None of these declarations crosses the bootstrap inductive
boundary. -/
def psigmaPrimeDerivedDecls : GenM (Array Declaration) := do
  let u := Level.param `u
  let v := Level.param `v
  let w := Level.param `w
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok value => pure value
    | .error message => badShape s!"PSigma' support needs Lean's Eq ({message})"

  let fstDecl ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `self (psigmaPrimeT u v α β) fun self => do
      let type ← mkForallFVars #[α, β, self] α
      let value ← mkLambdaFVars #[α, β, self] (.proj `PSigma' 0 self)
      return .defnDecl
        { name := `PSigma'.fst, levelParams := [`u, `v], type, value,
          hints := ← hintsFor value, safety := .safe }

  let sndDecl ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `self (psigmaPrimeT u v α β) fun self => do
      let fst := psigmaPrimeFst u v α β self
      let type ← mkForallFVars #[α, β, self] (mkApp β fst)
      let value ← mkLambdaFVars #[α, β, self] (.proj `PSigma' 1 self)
      return .defnDecl
        { name := `PSigma'.snd, levelParams := [`u, `v], type, value,
          hints := ← hintsFor value, safety := .safe }

  let recDecl ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β => do
    let pair := psigmaPrimeT u v α β
    withLocalDecl `motive .implicit (.forallE `self pair (.sort w) .default) fun motive => do
      let minorType ← withLocalDeclD `fst α fun fst =>
        withLocalDeclD `snd (mkApp β fst) fun snd =>
          mkForallFVars #[fst, snd] (mkApp motive (psigmaPrimeMk u v α β fst snd))
      withLocalDeclD `minor minorType fun minor =>
        withLocalDeclD `self pair fun self => do
          let type ← mkForallFVars #[α, β, motive, minor, self] (mkApp motive self)
          let body := mkAppN minor
            #[psigmaPrimeFst u v α β self, psigmaPrimeSnd u v α β self]
          let value ← mkLambdaFVars #[α, β, motive, minor, self] body
          return .defnDecl
            { name := `PSigma'.rec', levelParams := [`u, `v, `w], type, value,
              hints := ← hintsFor value, safety := .safe }

  let fstRule ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `fst α fun fst =>
      withLocalDeclD `snd (mkApp β fst) fun snd => do
        let pair := psigmaPrimeMk u v α β fst snd
        let lhs := psigmaPrimeFst u v α β pair
        let type ← mkForallFVars #[α, β, fst, snd] (eqi.mk' u α lhs fst)
        let value ← mkLambdaFVars #[α, β, fst, snd] (eqi.refl' u α fst)
        return .thmDecl
          { name := `PSigma'.fst_mk, levelParams := [`u, `v], type, value }

  let sndRule ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `fst α fun fst =>
      withLocalDeclD `snd (mkApp β fst) fun snd => do
        let pair := psigmaPrimeMk u v α β fst snd
        let lhs := psigmaPrimeSnd u v α β pair
        let fieldType := mkApp β fst
        let type ← mkForallFVars #[α, β, fst, snd] (eqi.mk' v fieldType lhs snd)
        let value ← mkLambdaFVars #[α, β, fst, snd] (eqi.refl' v fieldType snd)
        return .thmDecl
          { name := `PSigma'.snd_mk, levelParams := [`u, `v], type, value }

  let recRule ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β => do
    let pairType := psigmaPrimeT u v α β
    withLocalDecl `motive .implicit (.forallE `self pairType (.sort w) .default) fun motive => do
      let minorType ← withLocalDeclD `fst α fun fst =>
        withLocalDeclD `snd (mkApp β fst) fun snd =>
          mkForallFVars #[fst, snd] (mkApp motive (psigmaPrimeMk u v α β fst snd))
      withLocalDeclD `minor minorType fun minor =>
        withLocalDeclD `fst α fun fst =>
          withLocalDeclD `snd (mkApp β fst) fun snd => do
            let pair := psigmaPrimeMk u v α β fst snd
            let lhs := psigmaPrimeRec u v w α β motive minor pair
            let rhs := mkAppN minor #[fst, snd]
            let resultType := mkApp motive pair
            let type ← mkForallFVars #[α, β, motive, minor, fst, snd]
              (eqi.mk' w resultType lhs rhs)
            let value ← mkLambdaFVars #[α, β, motive, minor, fst, snd]
              (eqi.refl' w resultType rhs)
            return .thmDecl
              { name := `PSigma'.rec'_mk, levelParams := [`u, `v, `w], type, value }

  return #[fstDecl, sndDecl, recDecl, fstRule, sndRule, recRule]

private def checkPSigmaPrimeDerived (expected : Array Declaration) : GenM Unit := do
  for declaration in expected do
    let [name] := declaration.getNames
      | badShape "one PSigma' support declaration has several names"
    let some actual := (← getEnv).constants.find? name
      | declineWith (.notLeans name "it is missing from the tight pair support bundle")
    let (expectedLevels, expectedType, expectedValue, expectedTheorem) ← match declaration with
      | .defnDecl value => pure (value.levelParams, value.type, value.value, false)
      | .thmDecl value => pure (value.levelParams, value.type, value.value, true)
      | _ => badShape s!"{name} is not a derived tight-pair declaration"
    let (actualLevels, actualType, actualValue) ← match actual, expectedTheorem with
      | .defnInfo value, false => pure (value.levelParams, value.type, value.value)
      | .thmInfo value, true => pure (value.levelParams, value.type, value.value)
      | _, _ => declineWith (.notLeans name "it has the wrong declaration kind")
    unless actualLevels.length == expectedLevels.length do
      declineWith (.notLeans name
        s!"it has {actualLevels.length} universe parameters, expected {expectedLevels.length}")
    let levels := actualLevels.map Level.param
    let expectedType := expectedType.instantiateLevelParams expectedLevels levels
    let expectedValue := expectedValue.instantiateLevelParams expectedLevels levels
    unless ← isDefEq actualType expectedType do
      declineWith (.notLeans name "its type is not the projection-derived interface type")
    unless ← isDefEq actualValue expectedValue do
      declineWith (.notLeans name "its value is not the projection-derived implementation")

/-- Ensure the exact tight-pair bundle. The inductive is the one new basis
primitive; all named projections, reduction rules, and the large `rec'` are
ordinary checked declarations derived from primitive projections. -/
def ensurePSigmaPrime : GenM (Array Declaration) := do
  let mut out ← ensurePrim `PSigma' psigmaPrimeDecl checkPSigmaPrimeCore
  let expected ← psigmaPrimeDerivedDecls
  for declaration in expected do
    let [name] := declaration.getNames
      | badShape "one PSigma' support declaration has several names"
    if (← getEnv).constants.contains name then continue
    addChecked declaration
    out := out.push declaration
  checkPSigmaPrimeDerived expected
  return out

/-- Ensure the complete shared support for the internally derived exact-sort
propositional lift.  The construction itself is inlined into generated
expressions; only the exact standard `PUnit` and tight-pair bundle persist. -/
def ensureExactSortLift : GenM (Array Declaration) := do
  let pairs ← ensurePSigmaPrime
  let units ← ensurePUnit
  return pairs ++ units

end InductiveModels
