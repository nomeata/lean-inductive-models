import Lean
import Modelgen.Naming
/-!
# The Lean 4 export format, read and written

`lean4export` 3.1.0's `.ndjson`: one JSON object per line, each either a
*record* interning a name (`in`), a level (`il`) or an expression (`ie`), or a
**declaration** naming earlier records by index.

The parser here is the whole of the tool's trust boundary and it does **no
checking**: an export is read into `Lean.Name` / `Lean.Level` / `Lean.Expr`
verbatim, because the owner's instruction is to trust the input and that is
where the speed comes from. Nothing below runs a typechecker.

Two properties the rest of the tool depends on:

* **Back-references must be continuous.** `nanoda`'s parser — which `mini`
  uses — rejects a record whose index is not the current count
  (`vendor/nanoda_lib-upstream/src/parser.rs`'s `assert_ie`). So a model
  cannot be *spliced* into an existing file with fresh high indices; the whole
  output has to be re-interned from scratch. [`Writer`] does that.
* **Key order is alphabetical and there is no whitespace.** Matching it is
  what makes a no-op run byte-identical to its input, which is
  `Modelgen.Tests`'s cheapest oracle.
-/
open Lean

namespace Modelgen

/-- One constructor, as the export declares it. -/
structure ECtor where
  name : Name
  levelParams : List Name
  type : Expr
  cidx : Nat
  numParams : Nat
  numFields : Nat
  induct : Name
  isUnsafe : Bool
  deriving Inhabited, BEq

/-- One ι rule of an exported recursor. -/
structure ERecRule where
  ctor : Name
  nfields : Nat
  rhs : Expr
  deriving Inhabited, BEq

/-- One recursor, as the export declares it. A nested declaration carries more
than one: `Tree.rec` and `Tree.rec_1`. -/
structure ERec where
  name : Name
  levelParams : List Name
  type : Expr
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List ERecRule
  k : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq

/-- One member of an inductive block. `numNested > 0` is the whole reason this
tool exists. -/
structure EIndType where
  name : Name
  levelParams : List Name
  type : Expr
  all : List Name
  ctors : List Name
  numParams : Nat
  numIndices : Nat
  numNested : Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq

/-- A definition's reducibility hint, kept verbatim so a round trip is exact. -/
inductive EHints where
  | abbrev
  | «opaque»
  | regular (h : Nat)
  deriving Inhabited, BEq

/-- One declaration record. -/
inductive EDecl where
  | ax (name : Name) (levelParams : List Name) (type : Expr) (isUnsafe : Bool)
  | defn (name : Name) (levelParams : List Name) (type value : Expr)
      (hints : EHints) (safety : String) (all : List Name)
  | thm (name : Name) (levelParams : List Name) (type value : Expr) (all : List Name)
  | opaq (name : Name) (levelParams : List Name) (type value : Expr)
      (isUnsafe : Bool) (all : List Name)
  | quot (name : Name) (levelParams : List Name) (type : Expr) (kind : String)
  | induct (types : List EIndType) (ctors : List ECtor) (recs : List ERec)
  deriving Inhabited, BEq

namespace EDecl

/-- Every top-level name a declaration introduces — used to key the model's
insertion point and to detect a name the model would collide with. -/
def names : EDecl → List Name
  | .ax n .. | .defn n .. | .thm n .. | .opaq n .. | .quot n .. => [n]
  | .induct ts cs rs => ts.map (·.name) ++ cs.map (·.name) ++ rs.map (·.name)

end EDecl

/-! ## A record as a kernel declaration

The one function that turns a parsed record into something the kernel takes,
and the two hint/safety translations it needs. **It lives here rather than
beside its callers because it has three of them at three different heights of
the import graph**: the input replay in `Modelgen.Driver`, the replay in
`Modelgen.Mono` — which deliberately does not import `Driver` — and the
fragment splice in `Modelgen.Simple`, which sits *below* `Driver`. `Format` is
the shared floor, and the function is pure in its argument, so nothing but the
name resolution moves. -/

def hintsOf : ReducibilityHints → EHints
  | .abbrev => .abbrev
  | .opaque => .opaque
  | .regular h => .regular h.toNat

def hintsTo : EHints → ReducibilityHints
  | .abbrev => .abbrev
  | .opaque => .opaque
  | .regular h => .regular h.toUInt32

def safetyOf : String → DefinitionSafety
  | "unsafe" => .unsafe
  | "partial" => .partial
  | _ => .safe

/-- An export record as a kernel declaration. `none` for the three `quot`
records that `Declaration.quotDecl` already covers. -/
def toDeclaration (env : Environment) : EDecl → Option Declaration
  | .ax n lp t u => some <| .axiomDecl { name := n, levelParams := lp, type := t, isUnsafe := u }
  | .defn n lp t v h sf _ => some <| .defnDecl
      { name := n, levelParams := lp, type := t, value := v
        hints := hintsTo h, safety := safetyOf sf }
  | .thm n lp t v _ => some <| .thmDecl { name := n, levelParams := lp, type := t, value := v }
  | .opaq n lp t v u _ => some <| .opaqueDecl
      { name := n, levelParams := lp, type := t, value := v, isUnsafe := u }
  | .quot .. => if env.constants.contains `Quot then none else some .quotDecl
  | .induct ts cs _ =>
    let its := ts.map fun t =>
      ({ name := t.name, type := t.type
         ctors := (cs.filter (·.induct == t.name)).map fun c =>
           ({ name := c.name, type := c.type } : Constructor) } : InductiveType)
    match ts with
    | [] => none
    | t :: _ => some <| .inductDecl t.levelParams t.numParams its t.isUnsafe

/-! ## Renaming generated declarations by exact aliases -/

/-- **Every constant an expression names, rewritten** — and there are two kinds
of node that name one, not one.

`Expr.const` is the obvious kind. The other is `Expr.proj`, whose `typeName`
field is the structure the projection is *of*: a `proj` left pointing at the
old name after its structure has been renamed is `(kernel) invalid projection`,
which is exactly how this was found, splicing a fragment whose `Sigma.fst` is a
`proj` at `Sigma`. Binder names are not constants and are deliberately not
touched.

`f` returns `none` to mean "not mine", which both keeps the walk allocation-free
on the common subterm and, at a `proj`, lets `Expr.replace` recurse into the
structure the ordinary way. -/
partial def mapConstsE (f : Name → Option Name) (e : Expr) : Expr :=
  e.replace fun sub => match sub with
    | .const n us => (f n).map (Expr.const · us)
    | .proj n i s => (f n).map (fun n' => Expr.proj n' i (mapConstsE f s))
    | _ => none

/-- One export record with **every name it carries** rewritten — every name it
introduces, every name it refers to, and every constant inside its expressions.
`f` is applied to declaration names and `g` to expressions, and they are two
arguments so declaration fields and expression constants share one exhaustive
record walk.

**Every field that can hold a `Name` is listed**, because one missed field is a
record that refers to a constant the output does not contain, and no oracle here
would see it: the statement check reads the environment, which keeps the alias.
This is the single place that enumerates them, so a field added to a record is
caught once. -/
def EDecl.mapNames (f : Name → Name) (g : Expr → Expr) : EDecl → EDecl
  | .ax n lp t u => .ax (f n) lp (g t) u
  | .defn n lp t v h sf all => .defn (f n) lp (g t) (g v) h sf (all.map f)
  | .thm n lp t v all => .thm (f n) lp (g t) (g v) (all.map f)
  | .opaq n lp t v u all => .opaq (f n) lp (g t) (g v) u (all.map f)
  | .quot n lp t k => .quot (f n) lp (g t) k
  | .induct ts cs rs =>
    .induct
      (ts.map fun t => { t with
        name := f t.name, type := g t.type, all := t.all.map f, ctors := t.ctors.map f })
      (cs.map fun c => { c with name := f c.name, type := g c.type, induct := f c.induct })
      (rs.map fun r => { r with
        name := f r.name, type := g r.type, all := r.all.map f,
        rules := r.rules.map fun u => { u with ctor := f u.ctor, rhs := g u.rhs } })

/-- Rewrite one export record by an explicit whole-name alias table.  There is
no namespace fallback: a name absent from the table is left byte-for-byte
alone. -/
def EDecl.renameAliases (aliases : Naming.AliasMap) : EDecl → EDecl :=
  EDecl.mapNames aliases.exact
    (mapConstsE fun n => aliases.exact? n)

/-- A whole export: the `meta` line verbatim, then the declarations in order. -/
structure Export where
  metaLine : Json
  decls : Array EDecl
  /-- **The nodes with an `Expr.proj` somewhere in their subtree**, when the
  reader was asked for them (`analyse`), and empty when it was not.

  This is here rather than in the consumer because it is **an arena property and
  the arena is only in scope during the read**. Computed afterwards, over
  `Expr`s, it needs a visited set spanning every distinct node in the file so
  that a shared subterm is not walked once per parent — and that set is enormous
  and almost entirely `false`: at ten million lines of Mathlib, 9,264,612
  entries of which **90,765 (1.0 %) are `true`**. Computed here it needs no
  visited set at all, because the format guarantees a child's record precedes
  its parent's, so one forward pass over the arena in index order sees every
  child's answer already settled. What is kept is the 1 %.

  A consumer reads it as a **set membership and not a memo**: `e ∈ projNodes`
  is the whole query, there is nothing to fill in, and a node that is not in it
  is not in it. -/
  projNodes : Std.HashSet Expr := {}
  deriving Inhabited

/-! ## Reading -/

private def jField (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k

private def jNat (j : Json) (k : String) : Except String Nat := do
  (← jField j k).getNat?

private def jStr (j : Json) (k : String) : Except String String := do
  (← jField j k).getStr?

private def jBool (j : Json) (k : String) : Except String Bool := do
  (← jField j k).getBool?

private def jArr (j : Json) (k : String) : Except String (Array Json) := do
  (← jField j k).getArr?

/-- The interning tables, grown line by line. -/
structure RCtx where
  names : Array Name := #[.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  deriving Inhabited

namespace RCtx

def name! (c : RCtx) (i : Nat) : Except String Name :=
  if h : i < c.names.size then .ok c.names[i] else .error s!"name index {i} out of range"

def level! (c : RCtx) (i : Nat) : Except String Level :=
  if h : i < c.levels.size then .ok c.levels[i] else .error s!"level index {i} out of range"

def expr! (c : RCtx) (i : Nat) : Except String Expr :=
  if h : i < c.exprs.size then .ok c.exprs[i] else .error s!"expr index {i} out of range"

def nameF (c : RCtx) (j : Json) (k : String) : Except String Name := do c.name! (← jNat j k)
def exprF (c : RCtx) (j : Json) (k : String) : Except String Expr := do c.expr! (← jNat j k)

def nameL (c : RCtx) (j : Json) (k : String) : Except String (List Name) := do
  ((← jArr j k).toList.mapM fun x => do c.name! (← x.getNat?))

def levelL (c : RCtx) (j : Json) (k : String) : Except String (List Level) := do
  ((← jArr j k).toList.mapM fun x => do c.level! (← x.getNat?))

end RCtx

private def binderInfo : String → Except String BinderInfo
  | "default" => .ok .default
  | "implicit" => .ok .implicit
  | "strictImplicit" => .ok .strictImplicit
  | "instImplicit" => .ok .instImplicit
  | s => .error s!"unknown binderInfo {s}"

private def readCtor (c : RCtx) (j : Json) : Except String ECtor := do
  return {
    name := ← c.nameF j "name", levelParams := ← c.nameL j "levelParams"
    type := ← c.exprF j "type", cidx := ← jNat j "cidx"
    numParams := ← jNat j "numParams", numFields := ← jNat j "numFields"
    induct := ← c.nameF j "induct", isUnsafe := ← jBool j "isUnsafe" }

private def readRule (c : RCtx) (j : Json) : Except String ERecRule := do
  return { ctor := ← c.nameF j "ctor", nfields := ← jNat j "nfields", rhs := ← c.exprF j "rhs" }

private def readRec (c : RCtx) (j : Json) : Except String ERec := do
  return {
    name := ← c.nameF j "name", levelParams := ← c.nameL j "levelParams"
    type := ← c.exprF j "type", all := ← c.nameL j "all"
    numParams := ← jNat j "numParams", numIndices := ← jNat j "numIndices"
    numMotives := ← jNat j "numMotives", numMinors := ← jNat j "numMinors"
    rules := ← (← jArr j "rules").toList.mapM (readRule c)
    k := ← jBool j "k", isUnsafe := ← jBool j "isUnsafe" }

private def readIndType (c : RCtx) (j : Json) : Except String EIndType := do
  return {
    name := ← c.nameF j "name", levelParams := ← c.nameL j "levelParams"
    type := ← c.exprF j "type", all := ← c.nameL j "all"
    ctors := ← c.nameL j "ctors"
    numParams := ← jNat j "numParams", numIndices := ← jNat j "numIndices"
    numNested := ← jNat j "numNested", isRec := ← jBool j "isRec"
    isReflexive := ← jBool j "isReflexive", isUnsafe := ← jBool j "isUnsafe" }

private def readHints (j : Json) : Except String EHints :=
  match j with
  | .str "abbrev" => .ok .abbrev
  | .str "opaque" => .ok .opaque
  | o => do return .regular (← jNat o "regular")

/-- Store `v` at index `i`, growing with `pad`. The exporter usually emits
back-references densely and in order, but it is not required to:
`vendor/arena-tests/good/sparse-name-index.ndjson` and
`level-index-out-of-order.ndjson` are the fixtures that say so. The **writer**
is continuous regardless, because `nanoda` requires that. -/
def setAt (a : Array α) (i : Nat) (v pad : α) : Array α :=
  let a := if i < a.size then a else a ++ Array.replicate (i + 1 - a.size) pad
  a.set! i v

/-- Read one line into the context, returning a declaration if the line was one. -/
def readLine (c : RCtx) (j : Json) : Except String (RCtx × Option EDecl) := do
  -- Name records.
  if let .ok i := jNat j "in" then
    let n ←
      if let .ok o := jField j "str" then
        pure <| Name.str (← c.nameF o "pre") (← jStr o "str")
      else if let .ok o := jField j "num" then
        pure <| Name.num (← c.nameF o "pre") (← jNat o "i")
      else .error "name record with neither str nor num"
    return ({ c with names := setAt c.names i n .anonymous }, none)
  -- Level records.
  if let .ok i := jNat j "il" then
    let l ←
      if let .ok k := jNat j "succ" then pure <| Level.succ (← c.level! k)
      else if let .ok k := jNat j "param" then pure <| Level.param (← c.name! k)
      else if let .ok a := jArr j "max" then
        pure <| Level.max (← c.level! (← a[0]!.getNat?)) (← c.level! (← a[1]!.getNat?))
      else if let .ok a := jArr j "imax" then
        pure <| Level.imax (← c.level! (← a[0]!.getNat?)) (← c.level! (← a[1]!.getNat?))
      else .error "unknown level record"
    return ({ c with levels := setAt c.levels i l .zero }, none)
  -- Expression records.
  if let .ok i := jNat j "ie" then
    let e ←
      if let .ok k := jNat j "bvar" then pure <| Expr.bvar k
      else if let .ok k := jNat j "sort" then pure <| Expr.sort (← c.level! k)
      else if let .ok o := jField j "const" then
        pure <| Expr.const (← c.nameF o "name")
          (← (← (← o.getObjVal? "us").getArr?).toList.mapM fun x => do c.level! (← x.getNat?))
      else if let .ok o := jField j "app" then
        pure <| Expr.app (← c.exprF o "fn") (← c.exprF o "arg")
      else if let .ok o := jField j "lam" then
        pure <| Expr.lam (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
          (← binderInfo (← jStr o "binderInfo"))
      else if let .ok o := jField j "forallE" then
        pure <| Expr.forallE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
          (← binderInfo (← jStr o "binderInfo"))
      else if let .ok o := jField j "letE" then
        pure <| Expr.letE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "value")
          (← c.exprF o "body") (← jBool o "nondep")
      else if let .ok o := jField j "proj" then
        pure <| Expr.proj (← c.nameF o "typeName") (← jNat o "idx") (← c.exprF o "struct")
      else if let .ok s := jStr j "natVal" then
        pure <| Expr.lit (.natVal s.toNat!)
      else if let .ok s := jStr j "strVal" then
        pure <| Expr.lit (.strVal s)
      else .error "unknown expr record"
    return ({ c with exprs := setAt c.exprs i e (.bvar 0) }, none)
  -- Declaration records.
  if let .ok o := jField j "axiom" then
    return (c, some <| .ax (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← jBool o "isUnsafe"))
  if let .ok o := jField j "def" then
    return (c, some <| .defn (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← readHints (← jField o "hints"))
      (← jStr o "safety") (← c.nameL o "all"))
  if let .ok o := jField j "thm" then
    return (c, some <| .thm (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← c.nameL o "all"))
  if let .ok o := jField j "opaque" then
    return (c, some <| .opaq (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← jBool o "isUnsafe") (← c.nameL o "all"))
  if let .ok o := jField j "quot" then
    return (c, some <| .quot (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← jStr o "kind"))
  if let .ok o := jField j "inductive" then
    return (c, some <| .induct
      (← (← jArr o "types").toList.mapM (readIndType c))
      (← (← jArr o "ctors").toList.mapM (readCtor c))
      (← (← jArr o "recs").toList.mapM (readRec c)))
  .error s!"unrecognised record: {j.compress}"

/-- [`Export.projNodes`], in one forward pass over the arena.

Sound because the format admits **back-references only** — `RCtx.expr!` refuses
an index it has not filled yet — so every child of the node at index `i` sits at
an index below `i` and its answer is already in `s`. Nothing is ever revisited
and nothing false is stored. -/
def projNodesOf (exprs : Array Expr) : Std.HashSet Expr := Id.run do
  let mut s : Std.HashSet Expr := {}
  for e in exprs do
    let t :=
      match e with
      | .proj .. => true
      | .app f a => s.contains f || s.contains a
      | .lam _ t b _ | .forallE _ t b _ => s.contains t || s.contains b
      | .letE _ t v b _ => s.contains t || s.contains v || s.contains b
      | .mdata _ b => s.contains b
      | _ => false
    if t then s := s.insert e
  return s

/-- Parse a whole export.

`analyse` fills [`Export.projNodes`] and **defaults to on**, because an empty
`projNodes` reads as "no declaration contains a projection" and a consumer that
believed it would emit wrong output silently. A caller that does not look at the
field can turn it off; `monomorphize` refuses a file whose projections it can
see but whose `projNodes` is empty, so the two cannot disagree unnoticed. -/
def parse (text : String) (analyse : Bool := true) : Except String Export := do
  let mut c : RCtx := {}
  let mut decls : Array EDecl := #[]
  let mut metaLine : Json := .null
  let mut first := true
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let j ← Json.parse line
    if first then
      first := false
      if (jField j "meta").toOption.isSome then
        metaLine := j
        continue
    let (c', d?) ← readLine c j
    c := c'
    if let some d := d? then decls := decls.push d
  return { metaLine, decls, projNodes := if analyse then projNodesOf c.exprs else {} }

/-- **The same parse, off a handle, a chunk at a time.**

[`parse`] takes the file as one `String`, and on a large export that costs more
than everything it builds. Measured on a 512 MiB prefix of the Mathlib export
(`MONOMORPH.md` §9.9): `IO.FS.readFile` peaks at **2× the file** — the
`ByteArray` and the `String` `String.fromUTF8?` copies out of it are live
together, and the `ByteArray` is one large block the small-object allocator
cannot reuse afterwards — and `text.splitOn "\n"` then materialises **every line
of the file** as a live list, 124 bytes a line, before the first one is read.
Those two reach the parse's whole high-water mark **before a single JSON object
is parsed**; adding the JSON costs 0 and building the whole `Export` costs
0.13 % more, because both fit inside what the reader had already taken.

This reads 4 MiB at a time and holds one chunk's lines, and it is not a
different parser: the line handling is [`readLine`]'s, untouched, and the output
is byte-identical on `init-prelude` and on 20 MB, 1 M and 10 M of Mathlib. On
the 10-million-line prefix it takes the parse's peak from 2,381,888 KB to
**618,580 KB** and the whole pass's from 3,083,532 KB to **2,170,272 KB**, for
**1.3 % fewer instructions**. `Handle.getLine` is not the route: it did not
finish a 1-million-line prefix in ten minutes.
-/
def parseHandle (h : IO.FS.Handle) (analyse : Bool := true) : IO (Except String Export) := do
  -- **One ref per growing array, and `modifyGet`.** `RCtx` holds three arrays
  -- that grow by `push`, and a `push` is in-place only while the array is
  -- uniquely referenced. Two shapes lose that and both were measured on a 20 MB
  -- input, against **0.49 s** for the whole pass:
  --   * threading `RCtx` as a `mut` through a `for` nested in a `while` — the
  --     outer loop's state keeps a second reference: **78.8 s**;
  --   * holding it in a record and writing `{ st with c := c' }` — the
  --     projection reads the field while the record still holds it: **79.5 s**.
  -- `modifyGet` takes the value out of the ref, so what `readLine` is handed is
  -- the only reference to it.
  let cRef ← IO.mkRef ({} : RCtx)
  let declsRef ← IO.mkRef (#[] : Array EDecl)
  let mut metaLine : Json := .null
  let mut first := true
  let mut err : Option String := none
  -- The tail of the last chunk, past its final newline: an incomplete line, and
  -- the only thing carried between chunks.
  let mut carry : ByteArray := .empty
  let mut eof := false
  while !eof && err.isNone do
    let chunk ← h.read 4194304
    if chunk.size == 0 then eof := true
    let block := if carry.isEmpty then chunk else carry ++ chunk
    -- Cut at the last newline: only there is the byte boundary guaranteed not
    -- to fall inside a character, so only there can the prefix be decoded.
    let mut cut := block.size
    if !eof then
      cut := 0
      let mut i := block.size
      while i > 0 && cut == 0 do
        i := i - 1
        if block[i]! == 10 then cut := i + 1
      if cut == 0 then
        -- No newline in a whole chunk: keep reading rather than guess.
        carry := block
        continue
    carry := block.extract cut block.size
    match String.fromUTF8? (block.extract 0 cut) with
    | none => err := some "the input is not valid UTF-8"
    | some text =>
      for line in text.splitOn "\n" do
        if line.isEmpty then continue
        match Json.parse line with
        | .error e => err := some e; break
        | .ok j =>
          if first then
            first := false
            if (jField j "meta").toOption.isSome then
              metaLine := j
              continue
          match ← cRef.modifyGet fun c =>
              match readLine c j with
              -- **`{}`, not `c`.** Putting `c` back in the failure arm keeps it
              -- alive across `readLine`, so the arrays it pushes to are at
              -- refcount two and every push reallocates. The parse is over when
              -- this arm fires, so the context is dead either way.
              | .error e => (Except.error e, ({} : RCtx))
              | .ok (c', d?) => (Except.ok d?, c') with
          | .error e => err := some e; break
          | .ok d? => if let some d := d? then declsRef.modify (·.push d)
  match err with
  | some e => return .error e
  | none =>
    -- The arena is taken out of the ref rather than read out of it, so that the
    -- pass below sees the only reference to it and it is released as soon as it
    -- has been walked.
    let exprs ← if analyse then cRef.modifyGet fun c => (c.exprs, {}) else pure #[]
    return .ok { metaLine, decls := ← declsRef.get,
                 projNodes := if analyse then projNodesOf exprs else {} }

/-! ## Writing

Fresh interning, in dependency order, with the same key order and spacing the
exporter uses — so a file the tool does not change comes back byte-identical.

**The writer streams.** [`Writer.out`] holds the lines of **one record** and is
drained after each; it is never the whole file. That is not a micro-optimisation
but the difference between finishing and not: on Mathlib the pass emits ~110
million lines, and an `Array String` of them intercalated into one ~6 GB
`String` is what `MONOMORPH.md` §9.5 measured dying at 44.9 GB *after* the whole
computation had succeeded.

[`Export.stream`] is the one fold; [`Export.render`] and [`Export.writeTo`] are
its two consumers, which is what keeps them byte-identical rather than merely
intended to be.
-/

structure Writer where
  /-- The lines of the record being written. Drained by [`Export.stream`] after
  each record — do not accumulate a file here. -/
  out : Array String := #[]
  names : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity 1024 |>.insert .anonymous 0
  levels : Std.HashMap Level Nat := Std.HashMap.emptyWithCapacity 64 |>.insert .zero 0
  exprs : Std.HashMap Expr Nat := Std.HashMap.emptyWithCapacity 4096
  deriving Inhabited

namespace Writer

private def esc (s : String) : String := (Json.str s).compress

private def push (w : Writer) (line : String) : Writer := { w with out := w.out.push line }

partial def name (w : Writer) (n : Name) : Writer × Nat :=
  match w.names[n]? with
  | some i => (w, i)
  | none =>
    match n with
    | .anonymous => (w, 0)
    | .str p s =>
      let (w, pi) := w.name p
      let i := w.names.size
      let w := (w.push s!"\{\"in\":{i},\"str\":\{\"pre\":{pi},\"str\":{esc s}}}")
      ({ w with names := w.names.insert n i }, i)
    | .num p k =>
      let (w, pi) := w.name p
      let i := w.names.size
      let w := (w.push s!"\{\"in\":{i},\"num\":\{\"i\":{k},\"pre\":{pi}}}")
      ({ w with names := w.names.insert n i }, i)

partial def level (w : Writer) (l : Level) : Writer × Nat :=
  match w.levels[l]? with
  | some i => (w, i)
  | none =>
    let (w, body) :=
      match l with
      | .zero => (w, "")  -- unreachable: seeded at 0
      | .succ a => let (w, ai) := w.level a; (w, s!"\"succ\":{ai}")
      | .param p => let (w, pi) := w.name p; (w, s!"\"param\":{pi}")
      | .max a b =>
        let (w, ai) := w.level a
        let (w, bi) := w.level b
        (w, s!"\"max\":[{ai},{bi}]")
      | .imax a b =>
        let (w, ai) := w.level a
        let (w, bi) := w.level b
        (w, s!"\"imax\":[{ai},{bi}]")
      | .mvar _ => (w, "\"param\":0")  -- cannot occur in an export
    let i := w.levels.size
    let w := w.push s!"\{\"il\":{i},{body}}"
    ({ w with levels := w.levels.insert l i }, i)

private def levelsJ (w : Writer) (ls : List Level) : Writer × String :=
  let (w, idxs) := ls.foldl (fun (w, acc) l => let (w, i) := w.level l; (w, acc.push i)) (w, #[])
  (w, "[" ++ String.intercalate "," (idxs.toList.map toString) ++ "]")

private def namesJ (w : Writer) (ns : List Name) : Writer × String :=
  let (w, idxs) := ns.foldl (fun (w, acc) n => let (w, i) := w.name n; (w, acc.push i)) (w, #[])
  (w, "[" ++ String.intercalate "," (idxs.toList.map toString) ++ "]")

private def binderStr : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def expr (w : Writer) (e : Expr) : Writer × Nat :=
  match w.exprs[e]? with
  | some i => (w, i)
  | none =>
    if let .mdata _ b := e then w.expr b else
    let (w, body) :=
      match e with
      | .bvar k => (w, s!"\"bvar\":{k}")
      | .sort l => let (w, li) := w.level l; (w, s!"\"sort\":{li}")
      | .const n us =>
        let (w, ni) := w.name n
        let (w, uj) := w.levelsJ us
        (w, s!"\"const\":\{\"name\":{ni},\"us\":{uj}}")
      | .app f a =>
        let (w, fi) := w.expr f
        let (w, ai) := w.expr a
        (w, s!"\"app\":\{\"arg\":{ai},\"fn\":{fi}}")
      | .lam n t b bi =>
        let (w, ni) := w.name n
        let (w, ti) := w.expr t
        let (w, bd) := w.expr b
        (w, s!"\"lam\":\{\"binderInfo\":\"{binderStr bi}\",\"body\":{bd},\"name\":{ni},\"type\":{ti}}")
      | .forallE n t b bi =>
        let (w, ni) := w.name n
        let (w, ti) := w.expr t
        let (w, bd) := w.expr b
        (w, s!"\"forallE\":\{\"binderInfo\":\"{binderStr bi}\",\"body\":{bd},\"name\":{ni},\"type\":{ti}}")
      | .letE n t v b nd =>
        let (w, ni) := w.name n
        let (w, ti) := w.expr t
        let (w, vi) := w.expr v
        let (w, bd) := w.expr b
        (w, s!"\"letE\":\{\"body\":{bd},\"name\":{ni},\"nondep\":{nd},\"type\":{ti},\"value\":{vi}}")
      | .proj tn k s =>
        let (w, ti) := w.name tn
        let (w, si) := w.expr s
        (w, s!"\"proj\":\{\"idx\":{k},\"struct\":{si},\"typeName\":{ti}}")
      | .lit (.natVal k) => (w, s!"\"natVal\":\"{k}\"")
      | .lit (.strVal s) => (w, s!"\"strVal\":{esc s}")
      | _ => (w, "\"bvar\":0")  -- mdata/fvar/mvar cannot occur in an export
    let i := w.exprs.size
    let w := w.push s!"\{\"ie\":{i},{body}}"
    ({ w with exprs := w.exprs.insert e i }, i)

private def hintsJ : EHints → String
  | .abbrev => "\"abbrev\""
  | .opaque => "\"opaque\""
  | .regular h => s!"\{\"regular\":{h}}"

private def ctorJ (w : Writer) (c : ECtor) : Writer × String :=
  let (w, ni) := w.name c.name
  let (w, lp) := w.namesJ c.levelParams
  let (w, ti) := w.expr c.type
  let (w, ii) := w.name c.induct
  (w, s!"\{\"cidx\":{c.cidx},\"induct\":{ii},\"isUnsafe\":{c.isUnsafe},\"levelParams\":{lp},\
       \"name\":{ni},\"numFields\":{c.numFields},\"numParams\":{c.numParams},\"type\":{ti}}")

private def ruleJ (w : Writer) (r : ERecRule) : Writer × String :=
  let (w, ci) := w.name r.ctor
  let (w, ri) := w.expr r.rhs
  (w, s!"\{\"ctor\":{ci},\"nfields\":{r.nfields},\"rhs\":{ri}}")

private def recJ (w : Writer) (r : ERec) : Writer × String :=
  let (w, al) := w.namesJ r.all
  let (w, lp) := w.namesJ r.levelParams
  let (w, ni) := w.name r.name
  let (w, rules) :=
    r.rules.foldl (fun (w, acc) x => let (w, s) := w.ruleJ x; (w, acc.push s)) (w, #[])
  let (w, ti) := w.expr r.type
  (w, s!"\{\"all\":{al},\"isUnsafe\":{r.isUnsafe},\"k\":{r.k},\"levelParams\":{lp},\
       \"name\":{ni},\"numIndices\":{r.numIndices},\"numMinors\":{r.numMinors},\
       \"numMotives\":{r.numMotives},\"numParams\":{r.numParams},\
       \"rules\":[{String.intercalate "," rules.toList}],\"type\":{ti}}")

private def indTypeJ (w : Writer) (t : EIndType) : Writer × String :=
  let (w, al) := w.namesJ t.all
  let (w, cs) := w.namesJ t.ctors
  let (w, lp) := w.namesJ t.levelParams
  let (w, ni) := w.name t.name
  let (w, ti) := w.expr t.type
  (w, s!"\{\"all\":{al},\"ctors\":{cs},\"isRec\":{t.isRec},\"isReflexive\":{t.isReflexive},\
       \"isUnsafe\":{t.isUnsafe},\"levelParams\":{lp},\"name\":{ni},\"numIndices\":{t.numIndices},\
       \"numNested\":{t.numNested},\"numParams\":{t.numParams},\"type\":{ti}}")

/-- Emit one declaration, interning everything it names first. -/
def decl (w : Writer) (d : EDecl) : Writer :=
  match d with
  | .ax n lp t u =>
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    w.push s!"\{\"axiom\":\{\"isUnsafe\":{u},\"levelParams\":{lpj},\"name\":{ni},\"type\":{ti}}}"
  | .defn n lp t v h sf all =>
    let (w, aj) := w.namesJ all
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    let (w, vi) := w.expr v
    w.push s!"\{\"def\":\{\"all\":{aj},\"hints\":{hintsJ h},\"levelParams\":{lpj},\
      \"name\":{ni},\"safety\":\"{sf}\",\"type\":{ti},\"value\":{vi}}}"
  | .thm n lp t v all =>
    let (w, aj) := w.namesJ all
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    let (w, vi) := w.expr v
    w.push s!"\{\"thm\":\{\"all\":{aj},\"levelParams\":{lpj},\"name\":{ni},\
      \"type\":{ti},\"value\":{vi}}}"
  | .opaq n lp t v u all =>
    let (w, aj) := w.namesJ all
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    let (w, vi) := w.expr v
    w.push s!"\{\"opaque\":\{\"all\":{aj},\"isUnsafe\":{u},\"levelParams\":{lpj},\"name\":{ni},\
      \"type\":{ti},\"value\":{vi}}}"
  | .quot n lp t k =>
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    w.push s!"\{\"quot\":\{\"kind\":\"{k}\",\"levelParams\":{lpj},\"name\":{ni},\"type\":{ti}}}"
  | .induct ts cs rs =>
    let (w, csj) := cs.foldl (fun (w, a) c => let (w, s) := w.ctorJ c; (w, a.push s)) (w, #[])
    let (w, rsj) := rs.foldl (fun (w, a) r => let (w, s) := w.recJ r; (w, a.push s)) (w, #[])
    let (w, tsj) := ts.foldl (fun (w, a) t => let (w, s) := w.indTypeJ t; (w, a.push s)) (w, #[])
    w.push s!"\{\"inductive\":\{\"ctors\":[{String.intercalate "," csj.toList}],\
      \"recs\":[{String.intercalate "," rsj.toList}],\
      \"types\":[{String.intercalate "," tsj.toList}]}}"

end Writer

/-- **Serialise a whole export, one record at a time.**

`emit` is handed the lines of each record — the interned names, levels and
expressions it introduced, then the record itself — in file order, each without
its terminating newline. The interning tables live across the whole fold, which
is what the format requires; the *lines* do not.

Every consumer of the writer goes through here, so there is one definition of
what the file looks like. -/
@[specialize] def Export.stream {m : Type → Type} [Monad m] (x : Export)
    (emit : Array String → m Unit) : m Unit := do
  unless x.metaLine.isNull do emit #[x.metaLine.compress]
  let mut w : Writer := {}
  for d in x.decls do
    w := w.decl d
    emit w.out
    w := { w with out := #[] }

/-- Serialise a whole export into a `String`. Fine for a fixture; on a real
export use [`Export.writeTo`], which does not hold the file in memory. -/
def Export.render (x : Export) : String :=
  let go : StateM String Unit :=
    x.stream fun ls => modify fun s => ls.foldl (fun s l => s ++ l ++ "\n") s
  go.run "" |>.2

/-- Serialise a whole export to a stream, in bounded memory.

A `Stream` rather than a `Handle` because `-o -` is stdout, which `modelgen`
takes first class rather than through `/dev/stdout`.

Lines are gathered into a buffer of at least [`writeChunk`] bytes before each
write, so the cost is one `putStr` per few thousand lines rather than one per
line; nothing larger than that buffer plus the interning tables is ever
live. -/
def Export.writeTo (x : Export) (h : IO.FS.Stream) : IO Unit := do
  let buf ← IO.mkRef ""
  let n ← IO.mkRef 0
  x.stream fun ls => do
    let mut b ← buf.get
    let mut k ← n.get
    -- Take the buffer out of the ref first, so the append below sees a
    -- uniquely-referenced string and extends it in place.
    buf.set ""
    for l in ls do
      b := b ++ l ++ "\n"
      k := k + l.utf8ByteSize + 1
    if k ≥ writeChunk then
      h.putStr b
      b := ""
      k := 0
    buf.set b
    n.set k
  h.putStr (← buf.get)
where
  /-- 4 MiB: large enough that the per-write overhead vanishes, small enough
  that the buffer is not the thing that runs the machine out of memory. -/
  writeChunk : Nat := 4 * 1024 * 1024

end Modelgen
