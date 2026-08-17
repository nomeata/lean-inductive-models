import InductiveModels.Format.Export
/-!
# Reading an export

The interning arena, the record reader, and the whole-string and streaming
parser entry points.
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

/-- Which expression a `ie` record builds. -/
private inductive ExprTag where
  | bvar | sort | const | app | lam | forallE | letE | proj | natVal | strVal | mdata
  deriving Inhabited

/-- Which record a top-level line is. -/
private inductive RecordTag where
  | nameStr | nameNum
  | levelSucc | levelParam | levelMax | levelImax
  | expr (tag : ExprTag)
  | ax | defn | thm | opaq | quot | induct
  deriving Inhabited

/-- The tag of a single-key declaration record. -/
private def declTag? (fields : Std.TreeMap.Raw String Json) : Option RecordTag :=
  if fields.contains "axiom" then some .ax
  else if fields.contains "def" then some .defn
  else if fields.contains "thm" then some .thm
  else if fields.contains "opaque" then some .opaq
  else if fields.contains "quot" then some .quot
  else if fields.contains "inductive" then some .induct
  else none

/-- The tag of a two-key arena record: an arena slot and the thing it holds. -/
private def arenaTag? (fields : Std.TreeMap.Raw String Json) : Option RecordTag :=
  if fields.contains "in" then
    if fields.contains "str" then some .nameStr
    else if fields.contains "num" then some .nameNum
    else none
  else if fields.contains "il" then
    if fields.contains "succ" then some .levelSucc
    else if fields.contains "param" then some .levelParam
    else if fields.contains "max" then some .levelMax
    else if fields.contains "imax" then some .levelImax
    else none
  else if fields.contains "ie" then
    if fields.contains "bvar" then some (.expr .bvar)
    else if fields.contains "sort" then some (.expr .sort)
    else if fields.contains "const" then some (.expr .const)
    else if fields.contains "app" then some (.expr .app)
    else if fields.contains "lam" then some (.expr .lam)
    else if fields.contains "forallE" then some (.expr .forallE)
    else if fields.contains "letE" then some (.expr .letE)
    else if fields.contains "proj" then some (.expr .proj)
    else if fields.contains "natVal" then some (.expr .natVal)
    else if fields.contains "strVal" then some (.expr .strVal)
    else if fields.contains "mdata" then some (.expr .mdata)
    else none
  else none

/-- Which record this is, decided from its complete top-level key set.  The
Kernel Arena parser dispatches on the complete key set: extra keys and records
which combine two tags are malformed rather than partially recognized.

Every recognized record carries either one declaration key or an arena slot key
(`in`, `il`, `ie`) beside one tag key, so the key set is settled by the map's
size -- which a `Std.TreeMap` stores -- and then by membership tests, which are
lookups into the record's own two-entry map.  The dispatch this replaced
re-materialised the whole key list per candidate and walked it twice, ten times
down an if-chain for an expression record; retiring it took a quarter of the
parse away. -/
private def recordTag? (j : Json) : Option RecordTag :=
  match j with
  | .obj fields =>
      match fields.size with
      | 1 => declTag? fields
      | 2 => arenaTag? fields
      | _ => none
  | _ => none

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

/-- Build the expression an `ie` record holds.  The arena index is read by the
caller afterwards, as it was when this was an if-chain: a record whose payload
and whose index are both malformed still reports the payload. -/
private def readExprRecord (c : RCtx) (j : Json) : ExprTag → Except String Expr
  | .bvar => do return Expr.bvar (← jNat j "bvar")
  | .sort => do return Expr.sort (← c.level! (← jNat j "sort"))
  | .const => do
    let o ← jField j "const"
    return Expr.const (← c.nameF o "name")
      (← (← (← o.getObjVal? "us").getArr?).toList.mapM fun x => do c.level! (← x.getNat?))
  | .app => do
    let o ← jField j "app"
    return Expr.app (← c.exprF o "fn") (← c.exprF o "arg")
  | .lam => do
    let o ← jField j "lam"
    return Expr.lam (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
      (← binderInfo (← jStr o "binderInfo"))
  | .forallE => do
    let o ← jField j "forallE"
    return Expr.forallE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
      (← binderInfo (← jStr o "binderInfo"))
  | .letE => do
    let o ← jField j "letE"
    return Expr.letE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "value")
      (← c.exprF o "body") (← jBool o "nondep")
  | .proj => do
    let o ← jField j "proj"
    return Expr.proj (← c.nameF o "typeName") (← jNat o "idx") (← c.exprF o "struct")
  | .natVal => do
    let value ← match (← jStr j "natVal").toNat? with
      | some value => pure value
      | none => .error "Expr.lit natVal invalid"
    return Expr.lit (.natVal value)
  | .strVal => do return Expr.lit (.strVal (← jStr j "strVal"))
  | .mdata => do
    let o ← jField j "mdata"
    match ← jField o "data" with
    | .obj _ => return Expr.mdata {} (← c.exprF o "expr")
    | _ => .error "Expr.mdata invalid"

/-- Read one line into the context, returning a declaration if the line was one. -/
def readLine (c : RCtx) (j : Json) : Except String (RCtx × Option EDecl) := do
  match recordTag? j with
  | none => .error s!"unrecognised record: {j.compress}"
  -- Name records.
  | some .nameStr =>
    let i ← jNat j "in"
    let o ← jField j "str"
    let n := Name.str (← c.nameF o "pre") (← jStr o "str")
    return ({ c with names := c.names.set i n }, none)
  | some .nameNum =>
    let i ← jNat j "in"
    let o ← jField j "num"
    let n := Name.num (← c.nameF o "pre") (← jNat o "i")
    return ({ c with names := c.names.set i n }, none)
  -- Level records.
  | some .levelSucc =>
    let i ← jNat j "il"
    let l := Level.succ (← c.level! (← jNat j "succ"))
    return ({ c with levels := c.levels.set i l }, none)
  | some .levelParam =>
    let i ← jNat j "il"
    let l := Level.param (← c.name! (← jNat j "param"))
    return ({ c with levels := c.levels.set i l }, none)
  | some .levelMax =>
    let i ← jNat j "il"
    let #[left, right] ← jArr j "max" | .error "Level.max invalid"
    let l := Level.max (← c.level! (← left.getNat?)) (← c.level! (← right.getNat?))
    return ({ c with levels := c.levels.set i l }, none)
  | some .levelImax =>
    let i ← jNat j "il"
    let #[left, right] ← jArr j "imax" | .error "Level.imax invalid"
    let l := Level.imax (← c.level! (← left.getNat?)) (← c.level! (← right.getNat?))
    return ({ c with levels := c.levels.set i l }, none)
  -- Expression records.
  | some (.expr tag) =>
    let e ← readExprRecord c j tag
    let i ← jNat j "ie"
    return ({ c with exprs := c.exprs.set i e }, none)
  -- Declaration records.
  | some .ax =>
    let o ← jField j "axiom"
    return (c, some <| .ax (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← jBool o "isUnsafe"))
  | some .defn =>
    let o ← jField j "def"
    let safety ← jStr o "safety"
    unless (safetyOf? safety).isSome do
      throw s!"unknown definition safety {safety}"
    return (c, some <| .defn (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← readHints (← jField o "hints"))
      safety (← c.nameL o "all"))
  | some .thm =>
    let o ← jField j "thm"
    return (c, some <| .thm (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← c.nameL o "all"))
  | some .opaq =>
    let o ← jField j "opaque"
    let isUnsafe ← match (jField o "isUnsafe").toOption with
      | none => pure false
      | some value => value.getBool?
    return (c, some <| .opaq (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") isUnsafe (← c.nameL o "all"))
  | some .quot =>
    let o ← jField j "quot"
    let kind ← jStr o "kind"
    unless (quotKindOf? kind).isSome do throw s!"unknown quotient kind {kind}"
    return (c, some <| .quot (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") kind)
  | some .induct =>
    let o ← jField j "inductive"
    return (c, some <| .induct
      (← (← jArr o "types").toList.mapM (readIndType c))
      (← (← jArr o "ctors").toList.mapM (readCtor c))
      (← (← jArr o "recs").toList.mapM (readRec c)))

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

/-- The index of the first `0x0A` in `bytes` at or after `start`, or `limit` if
there is none before it.

Deliberately a pure function and not a `while` in the reader's `do` block: a
`while` over mutable state compiles to a monadic loop whose state is allocated
once per iteration, which is affordable once per line and ruinous once per byte
-- measured at 2.6× the whole parse when the byte scan was written that way. -/
private def nextNewline (bytes : ByteArray) (limit : Nat) (start : Nat) : Nat :=
  if start < limit then
    if bytes[start]! == 10 then start else nextNewline bytes limit (start + 1)
  else limit
termination_by limit - start

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
private def parseStreamCore (h : IO.FS.Stream) (allowDuplicateNames : Bool) :
    IO (Except String Export) := do
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
      -- **The line breaks are found in the bytes, not in the string.**
      -- `text.splitOn "\n"` decoded the whole chunk as UTF-8 a character at a
      -- time to look for one ASCII byte, and built every line of the chunk as a
      -- live list before the first of them was read; together that was an
      -- eighth of the parse. `0x0A` cannot occur inside a multi-byte UTF-8
      -- character, so a byte scan finds exactly the same breaks and every one
      -- of them is a character boundary, which is what a `String.Pos` counts.
      -- The lines are therefore the same lines, now cut one at a time.
      --
      -- The chunk is still decoded and validated *whole*, before any line of it
      -- is parsed: validating line by line would let a syntax error earlier in
      -- the chunk preempt invalid UTF-8 later in it, which is a different
      -- verdict on the same input.
      let mut lineStart := 0
      let mut stop := false
      while !stop && lineStart <= cut do
        -- The segment runs to the next LF, or to the cut if there is none: as
        -- `splitOn` does, a chunk ending in LF yields one empty sentinel there,
        -- and one not ending in LF -- only possible at EOF -- yields its last
        -- real line.
        let lineEnd := nextNewline block cut lineStart
        let line := String.Pos.Raw.extract text ⟨lineStart⟩ ⟨lineEnd⟩
        lineStart := lineEnd + 1
        -- Empty lines, sentinel or not, remain accepted by the historical
        -- parser.
        if !line.isEmpty then
          match Json.parse line with
          | .error e => err := some e; stop := true
          | .ok j =>
            let mut isMeta := false
            if first then
              first := false
              if (jField j "meta").toOption.isSome then
                metaLine := j
                isMeta := true
            if !isMeta then
              match ← cRef.modifyGet fun c =>
                  match readLine c j with
                  -- **`{}`, not `c`.** Putting `c` back in the failure arm
                  -- keeps it alive across `readLine`, so the arrays it pushes
                  -- to are at refcount two and every push reallocates. The
                  -- parse is over when this arm fires, so the context is dead
                  -- either way.
                  | .error e => (Except.error e, ({} : RCtx))
                  | .ok (c', d?) => (Except.ok d?, c') with
              | .error e => err := some e; stop := true
              | .ok d? => if let some d := d? then declsRef.modify (·.push d)
  match err with
  | some e => return .error e
  | none =>
    let decls ← declsRef.get
    -- Release the completed interning tables. Everything a declaration
    -- reaches is already held by the declaration itself.
    cRef.set {}
    let resultExport := { metaLine, decls }
    unless allowDuplicateNames do
      -- Report a repeated name only after the complete parse, so a later
      -- syntax or arena error retains historical precedence.
      if let .error message := resultExport.validateUniqueDeclarationNames then
        return .error message
    return .ok resultExport

def parseStream (h : IO.FS.Stream) (options : ParseOptions := {}) :
    IO (Except String Export) :=
  parseStreamCore h options.allowDuplicateNames

/-- Handle-specialized wrapper around [`parseStream`]. -/
def parseHandle (h : IO.FS.Handle) (options : ParseOptions := {}) :
    IO (Except String Export) :=
  parseStream (IO.FS.Stream.ofHandle h) options

end InductiveModels
