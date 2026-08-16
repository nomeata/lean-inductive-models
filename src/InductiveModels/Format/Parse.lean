import InductiveModels.Format.Export
/-!
# Reading an export

The interning arena, the record reader, the whole-string and streaming parser
entry points, and the raw source-capture side channel with its certificate.
-/
open Lean

namespace InductiveModels

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

/-- Whether a top-level record has exactly these keys.  The Kernel Arena
parser dispatches on the complete top-level key set: extra keys and records
which combine two tags are malformed rather than partially recognized. -/
private def hasExactKeys (j : Json) (keys : List String) : Bool :=
  match j with
  | .obj fields =>
      let actual := fields.toList.map (·.1)
      actual.length == keys.length && keys.all actual.contains
  | _ => false

/-- A compact arena table with an exact sparse fallback.

The dense prefix is the common exporter case.  An out-of-order entry beyond
that prefix lives in `sparse`; when the missing boundary arrives, consecutive
sparse entries are absorbed into the prefix.  Thus an arbitrarily large
malicious ID allocates one hash entry rather than padding an array up to that
ID, while lookup still distinguishes an absent hole from an explicitly written
default-looking value. -/
structure ArenaTable (α : Type) where
  dense : Array α := #[]
  sparse : Std.HashMap Nat α := {}
  deriving Inhabited

namespace ArenaTable

def seed (value : α) : ArenaTable α :=
  { dense := #[value] }

def get? (table : ArenaTable α) (index : Nat) : Option α :=
  if h : index < table.dense.size then some table.dense[index]
  else table.sparse[index]?

private def absorb (dense : Array α) (sparse : Std.HashMap Nat α) : ArenaTable α := Id.run do
  let mut dense := dense
  let mut sparse := sparse
  let mut done := false
  while !done do
    match sparse[dense.size]? with
    | none => done := true
    | some value =>
      sparse := sparse.erase dense.size
      dense := dense.push value
  return { dense, sparse }

/-- Write one explicit arena ID. Repeated IDs overwrite, matching the export
parser used by the Lean Kernel Arena. -/
def set (table : ArenaTable α) (index : Nat) (value : α) : ArenaTable α :=
  if h : index < table.dense.size then
    { table with dense := table.dense.set index value }
  else if index == table.dense.size then
    absorb (table.dense.push value) (table.sparse.erase index)
  else
    { table with sparse := table.sparse.insert index value }

end ArenaTable

/-- The interning tables, grown line by line. -/
structure RCtx where
  names : ArenaTable Name := .seed .anonymous
  levels : ArenaTable Level := .seed .zero
  exprs : ArenaTable Expr := {}
  deriving Inhabited

namespace RCtx

def name! (c : RCtx) (i : Nat) : Except String Name :=
  match c.names.get? i with
  | some name => .ok name
  | none => .error s!"name index {i} is not defined"

def level! (c : RCtx) (i : Nat) : Except String Level :=
  match c.levels.get? i with
  | some level => .ok level
  | none => .error s!"level index {i} is not defined"

def expr! (c : RCtx) (i : Nat) : Except String Expr :=
  match c.exprs.get? i with
  | some expression => .ok expression
  | none => .error s!"expr index {i} is not defined"

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

/-- Exact expression-arena roots named directly by one declaration record.
Expression nodes already contain their children, so random declaration replay
needs only these roots rather than the complete parser lookup table. -/
private def declarationExprRootIds (j : Json) : Except String (Array Nat) := do
  let mut roots := #[]
  if hasExactKeys j ["axiom"] || hasExactKeys j ["quot"] then
    roots := roots.push (← jNat (← jField j (if hasExactKeys j ["axiom"] then "axiom" else "quot")) "type")
  else if hasExactKeys j ["def"] || hasExactKeys j ["thm"] ||
      hasExactKeys j ["opaque"] then
    let key := if hasExactKeys j ["def"] then "def" else if hasExactKeys j ["thm"] then "thm" else "opaque"
    let declaration ← jField j key
    roots := (roots.push (← jNat declaration "type")).push (← jNat declaration "value")
  else if hasExactKeys j ["inductive"] then
    let declaration ← jField j "inductive"
    for type in ← jArr declaration "types" do
      roots := roots.push (← jNat type "type")
    for ctor in ← jArr declaration "ctors" do
      roots := roots.push (← jNat ctor "type")
    for recursor in ← jArr declaration "recs" do
      roots := roots.push (← jNat recursor "type")
      for rule in ← jArr recursor "rules" do
        roots := roots.push (← jNat rule "rhs")
  else
    throw "cannot collect expression roots from a non-declaration record"
  return roots

private def readHints (j : Json) : Except String EHints :=
  match j with
  | .str "abbrev" => .ok .abbrev
  | .str "opaque" => .ok .opaque
  | o => do return .regular (← jNat o "regular")

/-- Read one line into the context, returning a declaration if the line was one. -/
def readLine (c : RCtx) (j : Json) : Except String (RCtx × Option EDecl) := do
  -- Name records.
  if hasExactKeys j ["in", "str"] then
    let i ← jNat j "in"
    let o ← jField j "str"
    let n := Name.str (← c.nameF o "pre") (← jStr o "str")
    return ({ c with names := c.names.set i n }, none)
  if hasExactKeys j ["in", "num"] then
    let i ← jNat j "in"
    let o ← jField j "num"
    let n := Name.num (← c.nameF o "pre") (← jNat o "i")
    return ({ c with names := c.names.set i n }, none)
  -- Level records.
  if hasExactKeys j ["il", "succ"] then
    let i ← jNat j "il"
    let l := Level.succ (← c.level! (← jNat j "succ"))
    return ({ c with levels := c.levels.set i l }, none)
  if hasExactKeys j ["il", "param"] then
    let i ← jNat j "il"
    let l := Level.param (← c.name! (← jNat j "param"))
    return ({ c with levels := c.levels.set i l }, none)
  if hasExactKeys j ["il", "max"] then
    let i ← jNat j "il"
    let #[left, right] ← jArr j "max" | .error "Level.max invalid"
    let l := Level.max (← c.level! (← left.getNat?)) (← c.level! (← right.getNat?))
    return ({ c with levels := c.levels.set i l }, none)
  if hasExactKeys j ["il", "imax"] then
    let i ← jNat j "il"
    let #[left, right] ← jArr j "imax" | .error "Level.imax invalid"
    let l := Level.imax (← c.level! (← left.getNat?)) (← c.level! (← right.getNat?))
    return ({ c with levels := c.levels.set i l }, none)
  -- Expression records.
  let expression? ←
    if hasExactKeys j ["ie", "bvar"] then
      pure <| some (Expr.bvar (← jNat j "bvar"))
    else if hasExactKeys j ["ie", "sort"] then
      pure <| some (Expr.sort (← c.level! (← jNat j "sort")))
    else if hasExactKeys j ["ie", "const"] then
      let o ← jField j "const"
      pure <| some <| Expr.const (← c.nameF o "name")
        (← (← (← o.getObjVal? "us").getArr?).toList.mapM fun x => do c.level! (← x.getNat?))
    else if hasExactKeys j ["ie", "app"] then
      let o ← jField j "app"
      pure <| some <| Expr.app (← c.exprF o "fn") (← c.exprF o "arg")
    else if hasExactKeys j ["ie", "lam"] then
      let o ← jField j "lam"
      pure <| some <| Expr.lam (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
        (← binderInfo (← jStr o "binderInfo"))
    else if hasExactKeys j ["ie", "forallE"] then
      let o ← jField j "forallE"
      pure <| some <| Expr.forallE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
        (← binderInfo (← jStr o "binderInfo"))
    else if hasExactKeys j ["ie", "letE"] then
      let o ← jField j "letE"
      pure <| some <| Expr.letE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "value")
        (← c.exprF o "body") (← jBool o "nondep")
    else if hasExactKeys j ["ie", "proj"] then
      let o ← jField j "proj"
      pure <| some <| Expr.proj (← c.nameF o "typeName") (← jNat o "idx") (← c.exprF o "struct")
    else if hasExactKeys j ["ie", "natVal"] then
      let value ← match (← jStr j "natVal").toNat? with
        | some value => pure value
        | none => .error "Expr.lit natVal invalid"
      pure <| some <| Expr.lit (.natVal value)
    else if hasExactKeys j ["ie", "strVal"] then
      pure <| some <| Expr.lit (.strVal (← jStr j "strVal"))
    else if hasExactKeys j ["ie", "mdata"] then
      let o ← jField j "mdata"
      match ← jField o "data" with
      | .obj _ => pure <| some <| Expr.mdata {} (← c.exprF o "expr")
      | _ => .error "Expr.mdata invalid"
    else pure none
  if let some e := expression? then
    let i ← jNat j "ie"
    return ({ c with exprs := c.exprs.set i e }, none)
  -- Declaration records.
  if hasExactKeys j ["axiom"] then
    let o ← jField j "axiom"
    return (c, some <| .ax (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← jBool o "isUnsafe"))
  if hasExactKeys j ["def"] then
    let o ← jField j "def"
    let safety ← jStr o "safety"
    unless (safetyOf? safety).isSome do
      throw s!"unknown definition safety {safety}"
    return (c, some <| .defn (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← readHints (← jField o "hints"))
      safety (← c.nameL o "all"))
  if hasExactKeys j ["thm"] then
    let o ← jField j "thm"
    return (c, some <| .thm (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← c.nameL o "all"))
  if hasExactKeys j ["opaque"] then
    let o ← jField j "opaque"
    let isUnsafe ← match (jField o "isUnsafe").toOption with
      | none => pure false
      | some value => value.getBool?
    return (c, some <| .opaq (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") isUnsafe (← c.nameL o "all"))
  if hasExactKeys j ["quot"] then
    let o ← jField j "quot"
    let kind ← jStr o "kind"
    unless (quotKindOf? kind).isSome do throw s!"unknown quotient kind {kind}"
    return (c, some <| .quot (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") kind)
  if hasExactKeys j ["inductive"] then
    let o ← jField j "inductive"
    return (c, some <| .induct
      (← (← jArr o "types").toList.mapM (readIndType c))
      (← (← jArr o "ctors").toList.mapM (readCtor c))
      (← (← jArr o "recs").toList.mapM (readRec c)))
  .error s!"unrecognised record: {j.compress}"

/-- Complete name/level tables and expression roots sufficient to decode
declaration records in any order. The parser-backed form retains only roots
named directly by declarations; every root already owns its expression DAG.
The context is opaque so callers cannot mutate parser implementation tables. -/
structure DeclarationArena where private context : RCtx
  deriving Inhabited

/-- Decode one exact declaration-spool record against a completed arena.  A
span must contain exactly one UTF-8 JSON declaration and its terminating LF;
arena or metadata records fail closed. -/
def DeclarationArena.decode (arena : DeclarationArena)
    (bytes : ByteArray) : Except String EDecl := do
  unless !bytes.isEmpty && bytes[bytes.size - 1]! == 10 do
    throw "declaration span is not LF-terminated"
  let some line := String.fromUTF8? (bytes.extract 0 (bytes.size - 1))
    | throw "declaration span is not valid UTF-8"
  if line.isEmpty || line.contains '\n' || line.contains '\r' then
    throw "declaration span does not contain exactly one canonical line"
  let json ← Json.parse line
  let (_, declaration?) ← readLine arena.context json
  let some declaration := declaration?
    | throw "declaration span decoded as an arena record"
  return declaration

/-- Number of expression roots retained by a completed random-decode arena.
This observer exposes storage cardinality, never expression values. -/
def DeclarationArena.retainedExprRoots (arena : DeclarationArena) : Nat :=
  arena.context.exprs.dense.size + arena.context.exprs.sparse.size

/-- Build the random-decode arena from an arena-only stream using the same
bounded chunk/UTF-8 boundary discipline as the full streaming parser. This
fallback has no declaration records from which to derive the compact root set,
so it retains the completed interning tables but no declaration value. -/
def DeclarationArena.ofStream (stream : IO.FS.Stream) : IO (Except String DeclarationArena) := do
  let context ← IO.mkRef ({} : RCtx)
  let mut carry : ByteArray := .empty
  let mut eof := false
  let mut err : Option String := none
  while !eof && err.isNone do
    let chunk ← stream.read 4194304
    if chunk.size == 0 then eof := true
    let block := if carry.isEmpty then chunk else carry ++ chunk
    let mut cut := block.size
    if !eof then
      cut := 0
      let mut i := block.size
      while i > 0 && cut == 0 do
        i := i - 1
        if block[i]! == 10 then cut := i + 1
      if cut == 0 then
        carry := block
        continue
    carry := block.extract cut block.size
    match String.fromUTF8? (block.extract 0 cut) with
    | none => err := some "the declaration arena is not valid UTF-8"
    | some text =>
      let lines := (text.splitOn "\n").toArray
      for lineIndex in [:lines.size] do
        let line := lines[lineIndex]!
        if line.isEmpty then continue
        match Json.parse line with
        | .error error => err := some error; break
        | .ok json =>
          match ← context.modifyGet fun current =>
              match readLine current json with
              | .error error => (Except.error error, ({} : RCtx))
              | .ok (_, some _) =>
                  (Except.error "declaration record found in arena spool", ({} : RCtx))
              | .ok (next, none) => (Except.ok (), next) with
          | .error error => err := some error; break
          | .ok () => pure ()
  match err with
  | some error => return .error error
  | none =>
    let completed ← context.modifyGet fun current => (current, {})
    return .ok { context := completed }

/-- Handle-specialized completed-arena loader. -/
def DeclarationArena.ofHandle (handle : IO.FS.Handle) : IO (Except String DeclarationArena) :=
  DeclarationArena.ofStream (IO.FS.Stream.ofHandle handle)

/-- Parse a whole export. -/
def parse (text : String) : Except String Export := do
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
  let resultExport : Export := { metaLine, decls }
  resultExport.validateUniqueDeclarationNames
  return resultExport

/-! ## Optional raw source capture during streaming parse

The parser may hand each exact UTF-8 record to a transient sink while it is
already in scope.  This is deliberately an optional side channel: ordinary
parsing retains its old result and does no spool allocation. Planned input
replay may use the certified source spool without reopening a mutable path.
-/

/-- Which logical spool consumes one exact input record.  `ignored` covers
blank lines; accepting them remains parser-compatible, but they disqualify the
strict raw-arena fast path. -/
inductive RawRecordKind where
  | metadata | arena | declaration | ignored
  deriving Inhabited, Repr, BEq

/-- A transient exact line, including its original LF when present.  Sinks
must consume `bytes` during the call rather than retaining the parser chunk. -/
structure RawRecord where
  kind : RawRecordKind
  bytes : ByteArray

/-- Optional parse-time consumer for exact raw records. -/
structure RawSink where
  emit : RawRecord → IO Unit

/-- A declaration callback sharing the parser's exact `readLine` result.  The
callback must consume the value during `emit`: discard-mode parsing does not
retain declaration records after the call returns. -/
structure DeclarationSink where
  emit : EDecl → IO Unit

/-- The whole-input facts which survive declaration-discarding parsing. The
arena holds complete name/level tables plus only exact declaration expression
roots; `PlannedSourceReader` receives this value without reparsing. -/
structure ParsedEnvelope where
  metaLine : Json := .null
  declarationCount : Nat := 0
  /-- The exact compacted parser arena. Planned replay decodes declaration
  spans against this value instead of retaining the dense expression-ID table
  or reparsing a second expression graph. -/
  private declarationArena : DeclarationArena := { context := {} }
  /-- Observable retention contract for regression tests. -/
  retainedDeclarations : Nat := 0
  deriving Inhabited

def ParsedEnvelope.template (envelope : ParsedEnvelope) : Export :=
  { metaLine := envelope.metaLine, decls := #[] }

/-- Share the completed parser arena with one planned declaration reader. -/
def ParsedEnvelope.arena (envelope : ParsedEnvelope) : DeclarationArena :=
  envelope.declarationArena

/-- A compact byte span in the declaration-only spool. Both coordinates are
fixed-width and every conversion/addition is checked before publication. -/
structure RawSpan where
  offset : UInt64
  bytes : UInt64
  deriving Inhabited, Repr, BEq

def RawSpan.end? (span : RawSpan) : Option UInt64 :=
  if span.offset.toNat + span.bytes.toNat < UInt64.size then
    some (span.offset + span.bytes)
  else none

/-- Exclusive upper bounds of a strictly progressive input arena. -/
structure RawArenaCursor where
  nextName : Nat := 1
  nextLevel : Nat := 1
  nextExpr : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Certification and compact offsets produced beside a raw spool.

`canonical` is intentionally stronger than parser acceptance: every nonempty
record has canonical compressed JSON spelling and a terminating LF, and name,
level, and expression IDs progress exactly `1,2,…`, `1,2,…`, and `0,1,…`.
Sparse, repeated, or out-of-order arenas therefore fall back to full
re-interning instead of changing the snapshot seen by an earlier declaration.

This is evidence about the input byte stream, not an output backend. Planned
source replay additionally validates every span against the finished spool
size before reading declarations by index.
-/
structure RawCertificate where
  canonical : Bool := true
  /-- Arena IDs are strictly progressive, so the completed parser arena is
  also the exact arena seen by every earlier declaration. Whitespace and
  metadata spelling do not affect this declaration-replay property. -/
  replayable : Bool := true
  cursor : RawArenaCursor := {}
  metadataBytes : UInt64 := 0
  arenaBytes : UInt64 := 0
  declarationBytes : UInt64 := 0
  declarations : Array RawSpan := #[]
  deriving Inhabited, Repr, BEq

/-- Actual sizes of the three completed logical spool files. -/
structure RawSpoolSizes where
  metadata : UInt64
  arena : UInt64
  declarations : UInt64
  deriving Inhabited, Repr, BEq

/-- Validate completed spool totals and the exact declaration partition.  This
is sufficient for random declaration decoding even when a parser-compatible
sparse/repeated arena is ineligible for raw output composition. -/
def RawCertificate.validateDeclarationSpans (certificate : RawCertificate)
    (sizes : RawSpoolSizes) (declarationCount : Nat) : Except String Unit := do
  let expectedSizes : RawSpoolSizes :=
    { metadata := certificate.metadataBytes
      arena := certificate.arenaBytes
      declarations := certificate.declarationBytes }
  unless sizes == expectedSizes do
    throw "raw spool sizes do not match the parser certificate"
  unless certificate.declarations.size == declarationCount do
    throw "raw declaration span count does not match the parsed declarations"
  let mut endpoint : UInt64 := 0
  for span in certificate.declarations do
    unless span.offset == endpoint do
      throw "raw declaration spans are not contiguous"
    let some next := span.end?
      | throw "raw declaration span endpoint overflows UInt64"
    endpoint := next
  unless endpoint == sizes.declarations do
    throw "raw declaration spans do not cover the completed spool"

/-- Validate all persistent offsets and canonical arena evidence before any
raw composition may consume them. -/
def RawCertificate.validate (certificate : RawCertificate) (sizes : RawSpoolSizes)
    (declarationCount : Nat) : Except String RawArenaCursor := do
  unless certificate.canonical do throw "raw input is not canonical"
  certificate.validateDeclarationSpans sizes declarationCount
  return certificate.cursor

/-- Validate declaration-only storage against the completed parser arena.
Unlike canonical raw composition, declaration replay is insensitive to JSON
spacing but must reject arena holes, reordering, and overwrites. -/
def RawCertificate.validateReplay (certificate : RawCertificate)
    (declarationBytes : UInt64) (declarationCount : Nat) : Except String Unit := do
  unless certificate.replayable do throw "raw input arena is not declaration-replayable"
  certificate.validateDeclarationSpans
    { metadata := certificate.metadataBytes, arena := certificate.arenaBytes,
      declarations := declarationBytes }
    declarationCount

private structure RawCertState where
  certificate : RawCertificate := {}

private def addUInt64Bytes (current : UInt64) (bytes : Nat) : UInt64 × Bool :=
  if bytes < UInt64.size && current.toNat ≤ UInt64.size - 1 - bytes then
    (current + bytes.toUInt64, true)
  else
    (current, false)

private def exactRawBytes (line : String) (terminated : Bool) : ByteArray :=
  if terminated then line.toUTF8.push 10 else line.toUTF8

/-- Recognize the whitespace-free JSON spelling emitted by lean4export and
`Writer` without depending on `Json.compress`'s hash-map iteration order.
Object key order is semantically irrelevant and may change when unrelated
imports perturb compiled hash-map layout; whitespace outside strings is the
only spelling freedom which would make the raw line non-compressed.  The line
has already parsed as JSON, so quote/escape well-formedness is not rechecked
here. -/
private def compressedJsonSpelling (line : String) : Bool :=
  let rec loop (chars : List Char) (inString escaped : Bool) : Bool :=
    match chars with
    | [] => !inString && !escaped
    | char :: rest =>
      if inString then
        if escaped then loop rest true false
        else if char == '\\' then loop rest true true
        else if char == '"' then loop rest false false
        else loop rest true false
      else if char == '"' then loop rest true false
      else if char == ' ' || char == '\t' || char == '\r' || char == '\n' then false
      else loop rest false false
  loop line.toList false false

private inductive RawArenaAxis where
  | name | level | expression

private def rawArenaId? (j : Json) : Option (RawArenaAxis × Nat) :=
  if let some id := (jField j "in").toOption.bind fun value => value.getNat?.toOption then
    some (.name, id)
  else if let some id := (jField j "il").toOption.bind fun value => value.getNat?.toOption then
    some (.level, id)
  else if let some id := (jField j "ie").toOption.bind fun value => value.getNat?.toOption then
    some (.expression, id)
  else none

private def RawCertState.addBytes (state : RawCertState) (kind : RawRecordKind)
    (bytes : Nat) : RawCertState :=
  match kind with
  | .metadata =>
      let (total, valid) := addUInt64Bytes state.certificate.metadataBytes bytes
      { state with certificate := { state.certificate with
          canonical := state.certificate.canonical && valid, metadataBytes := total } }
  | .arena =>
      let (total, valid) := addUInt64Bytes state.certificate.arenaBytes bytes
      { state with certificate := { state.certificate with
          canonical := state.certificate.canonical && valid, arenaBytes := total } }
  | .declaration =>
      let (total, validTotal) := addUInt64Bytes state.certificate.declarationBytes bytes
      let validLength := bytes < UInt64.size
      { certificate := { state.certificate with
          canonical := state.certificate.canonical && validTotal && validLength
          declarationBytes := total
          declarations := state.certificate.declarations.push
            { offset := state.certificate.declarationBytes,
              bytes := if validLength then bytes.toUInt64 else 0 } } }
  | .ignored => state

private def RawCertState.observeArena (state : RawCertState) (j : Json) : RawCertState :=
  match rawArenaId? j with
  | some (.name, id) =>
      { state with certificate := { state.certificate with
          replayable := state.certificate.replayable &&
            id == state.certificate.cursor.nextName
          canonical := state.certificate.canonical && id == state.certificate.cursor.nextName
          cursor.nextName := state.certificate.cursor.nextName + 1 } }
  | some (.level, id) =>
      { state with certificate := { state.certificate with
          replayable := state.certificate.replayable &&
            id == state.certificate.cursor.nextLevel
          canonical := state.certificate.canonical && id == state.certificate.cursor.nextLevel
          cursor.nextLevel := state.certificate.cursor.nextLevel + 1 } }
  | some (.expression, id) =>
      { state with certificate := { state.certificate with
          replayable := state.certificate.replayable &&
            id == state.certificate.cursor.nextExpr
          -- The ordinary writer erases expression metadata, so a raw source
          -- containing `mdata` is not yet eligible for mixed raw/generated
          -- composition even when its IDs are dense.
          canonical := state.certificate.canonical &&
            (jField j "mdata").toOption.isNone &&
            id == state.certificate.cursor.nextExpr
          cursor.nextExpr := state.certificate.cursor.nextExpr + 1 } }
  | _ => { state with certificate := { state.certificate with
      canonical := false, replayable := false } }

private def emitRaw (sink : RawSink) (state : IO.Ref RawCertState)
    (kind : RawRecordKind) (line : String) (terminated : Bool)
    (json? : Option Json := none) : IO Unit := do
  let bytes := exactRawBytes line terminated
  sink.emit { kind, bytes }
  state.modify fun current =>
    let current := current.addBytes kind bytes.size
    let spelling := terminated && json?.isSome && compressedJsonSpelling line
    let current := { current with certificate := { current.certificate with
      canonical := current.certificate.canonical && spelling
      -- `DeclarationArena.decode` consumes one complete NDJSON declaration
      -- record. An otherwise valid declaration at EOF without LF is accepted
      -- by the whole parser, but its declaration-only span must select the
      -- exact raw-snapshot fallback rather than fail during planned replay.
      replayable := current.certificate.replayable &&
        (kind != .declaration || terminated) } }
    if kind == .arena then json?.elim current current.observeArena else current

/-- Options shared by the streaming/handle parser entry points. A structure is
used deliberately: adding or removing an option cannot silently reinterpret a
positional `Bool` at public call sites. -/
structure ParseOptions where
  allowDuplicateNames : Bool := false
  deriving Inhabited, Repr, BEq

/-- **The same parse, off a handle, a chunk at a time.**

[`parse`] takes the file as one `String`, and on a large export that costs more
than everything it builds. Measured on a 512 MiB prefix of the Mathlib export,
`IO.FS.readFile` peaks at **2× the file** — the
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
private def parseStreamCore (h : IO.FS.Stream)
    (sink? : Option RawSink) (declarationSink? : Option DeclarationSink)
    (retainDeclarations allowDuplicateNames : Bool) :
    IO (Except String (Export × RawCertificate × Nat × DeclarationArena)) := do
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
  let declarationCountRef ← IO.mkRef 0
  let declarationNamesRef ← IO.mkRef ({} : Std.HashSet Name)
  let duplicateRef ← IO.mkRef (none : Option Name)
  -- A declaration refers directly to very few expression roots. Preserve
  -- exactly those roots for later random replay instead of retaining the
  -- parser's complete dense expression-ID table.
  let declarationExprRootsRef ← IO.mkRef ({} : Std.HashMap Nat Expr)
  let rawRef ← IO.mkRef ({} : RawCertState)
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
      let lines := (text.splitOn "\n").toArray
      for hline : lineIndex in [:lines.size] do
        let line := lines[lineIndex]
        let terminated := lineIndex + 1 < lines.size
        -- `splitOn` leaves one empty sentinel after a final LF.  Other empty
        -- lines remain accepted by the historical parser but disqualify raw
        -- canonical source capture and are handed to the sink exactly.
        if line.isEmpty then
          if terminated then
            if let some sink := sink? then
              emitRaw sink rawRef .ignored line true
          continue
        match Json.parse line with
        | .error e => err := some e; break
        | .ok j =>
          if first then
            first := false
            if (jField j "meta").toOption.isSome then
              metaLine := j
              if let some sink := sink? then
                emitRaw sink rawRef .metadata line terminated (some j)
              continue
          match ← cRef.modifyGet fun c =>
              match readLine c j with
              -- **`{}`, not `c`.** Putting `c` back in the failure arm keeps it
              -- alive across `readLine`, so the arrays it pushes to are at
              -- refcount two and every push reallocates. The parse is over when
              -- this arm fires, so the context is dead either way.
              | .error e => (Except.error e, ({} : RCtx))
              | .ok (c', d?) =>
                  let result : Except String (Option EDecl × Array (Nat × Expr)) := do
                    let ids ← if d?.isSome then declarationExprRootIds j else pure #[]
                    let roots ← ids.mapM fun id => return (id, ← c'.expr! id)
                    return (d?, roots)
                  (result, c') with
          | .error e => err := some e; break
          | .ok (d?, expressionRoots) =>
            unless retainDeclarations do
              declarationExprRootsRef.modify fun roots =>
                expressionRoots.foldl (fun roots (id, expression) =>
                  roots.insert id expression) roots
            if let some sink := sink? then
              emitRaw sink rawRef (if d?.isSome then .declaration else .arena)
                line terminated (some j)
            if let some d := d? then
              declarationCountRef.modify (· + 1)
              -- Match `Export.validateUniqueDeclarationNames`: remember the
              -- first collision, but report it only after the complete parse
              -- so a later syntax/arena error retains historical precedence.
              unless retainDeclarations do
                for name in d.names do
                  let already ← declarationNamesRef.modifyGet fun names =>
                    (names.contains name, names.insert name)
                  if already then
                    duplicateRef.modify fun duplicate => duplicate.orElse (fun _ => some name)
              if let some declarationSink := declarationSink? then
                declarationSink.emit d
              if retainDeclarations then declsRef.modify (·.push d)
  match err with
  | some e => return .error e
  | none =>
    let decls ← declsRef.get
    -- Take the completed arena out of the ref. Whole-export callers release
    -- the table wrapper after returning, while declaration-discarding callers
    -- transfer this exact graph to `PlannedSourceReader`.
    let completed ← cRef.modifyGet fun c => (c, {})
    let declarationExprRoots ← declarationExprRootsRef.modifyGet fun roots => (roots, {})
    let replayArena : DeclarationArena := if retainDeclarations then default else
      { context := { completed with exprs := { sparse := declarationExprRoots } } }
    let rawState ← rawRef.get
    let declarationCount ← declarationCountRef.get
    let certificate := if sink?.isSome then rawState.certificate else {}
    let resultExport := { metaLine, decls }
    unless allowDuplicateNames do
      if retainDeclarations then
        if let .error message := resultExport.validateUniqueDeclarationNames then
          return .error message
      else if let some name ← duplicateRef.get then
          return .error s!"duplicate declaration {name}"
    return .ok (resultExport, certificate, declarationCount, replayArena)

/-- Parse while sending exact input records to `sink`. The compact returned
certificate is necessary but not sufficient for a later raw-hoist fast path;
a false certificate unconditionally requires the ordinary writer. -/
def parseStreamWithSink (h : IO.FS.Stream) (sink : RawSink)
    (options : ParseOptions := {}) :
    IO (Except String (Export × RawCertificate)) := do
  return (← parseStreamCore h (some sink) none true options.allowDuplicateNames).map
    fun (parsed, certificate, _, _) => (parsed, certificate)

/-- Parse and certify the exact stream while delivering each decoded
declaration to one callback instead of retaining a whole `Export.decls`.
The callback and raw sink observe the same successful `readLine` transition;
there is no second JSON or arena pass. -/
def parseStreamDiscardingDeclarations (h : IO.FS.Stream) (rawSink : RawSink)
    (declarationSink : DeclarationSink)
    (options : ParseOptions := {}) :
    IO (Except String (ParsedEnvelope × RawCertificate)) := do
  return (← parseStreamCore h (some rawSink) (some declarationSink)
    false options.allowDuplicateNames).map fun (parsed, certificate, declarationCount, arena) =>
      ({ metaLine := parsed.metaLine, declarationCount, declarationArena := arena,
         retainedDeclarations := parsed.decls.size }, certificate)

def parseStream (h : IO.FS.Stream) (options : ParseOptions := {}) :
    IO (Except String Export) := do
  return (← parseStreamCore h none none true options.allowDuplicateNames).map (·.1)

/-- Handle-specialized wrapper around [`parseStream`]. -/
def parseHandle (h : IO.FS.Handle) (options : ParseOptions := {}) :
    IO (Except String Export) :=
  parseStream (IO.FS.Stream.ofHandle h) options

/-- Handle-specialized raw-source-capture parser. -/
def parseHandleWithSink (h : IO.FS.Handle) (sink : RawSink)
    (options : ParseOptions := {}) :
    IO (Except String (Export × RawCertificate)) :=
  parseStreamWithSink (IO.FS.Stream.ofHandle h) sink options

/-- Handle-specialized declaration-discarding parser. -/
def parseHandleDiscardingDeclarations (h : IO.FS.Handle) (rawSink : RawSink)
    (declarationSink : DeclarationSink)
    (options : ParseOptions := {}) :
    IO (Except String (ParsedEnvelope × RawCertificate)) :=
  parseStreamDiscardingDeclarations (IO.FS.Stream.ofHandle h) rawSink declarationSink
    options

/-- Lowercase hexadecimal encoding used for random spool leaf names. Exposed
so the secure workspace tests can pin the entropy-preserving representation. -/
def rawSpoolSuffixOfBytes (bytes : ByteArray) : String :=
  bytes.foldl (fun suffix byte =>
    let value := byte.toNat
    suffix ++ hexDigitRepr (value / 16) ++ hexDigitRepr (value % 16)) ""

end InductiveModels
