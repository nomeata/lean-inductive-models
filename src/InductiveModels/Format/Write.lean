import InductiveModels.Format.Parse
/-!
# Writing an export

Fresh dense interning in dependency order with the exporter's key order and
spacing. `Writer.Cursor.ofRaw` consumes the parser's certified
`RawArenaCursor`, which is the one reason this module sits above the reader.
-/
open Lean

namespace InductiveModels

/-! ## Writing

Fresh dense interning, in dependency order, with the same key order and spacing
the exporter uses. A canonical exporter file which the tool does not change is
therefore byte-identical; other valid arena layouts and JSON formatting are
normalized.

**The writer streams.** [`Writer.out`] holds the lines of **one record** and is
drained after each; it is never the whole file. That is not a micro-optimisation
but the difference between finishing and not: on Mathlib the pass emits ~110
million lines, and an `Array String` of them intercalated into one ~6 GB
`String` was measured dying at 44.9 GB *after* the whole
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
  /-- The next arena IDs.  They are counters rather than table sizes so a
  fresh island-local writer can continue after an earlier island while
  deliberately forgetting its structural interning tables. -/
  nextName : Nat := 1
  nextLevel : Nat := 1
  nextExpr : Nat := 0
  deriving Inhabited

namespace Writer

/-- The exclusive upper bounds of the three independent export arenas. -/
structure Cursor where
  nextName : Nat := 1
  nextLevel : Nat := 1
  nextExpr : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Exact handoff from a validated raw input arena to a generated writer. No
table size or inferred count is substituted for the certified next IDs. -/
def Cursor.ofRaw (cursor : RawArenaCursor) : Cursor :=
  { nextName := cursor.nextName, nextLevel := cursor.nextLevel,
    nextExpr := cursor.nextExpr }

/-- Start a structurally fresh writer at explicit, non-overlapping arena IDs.
Only the format's distinguished anonymous name and zero level remain shared
at index zero.  Equal nontrivial nodes written by another island are therefore
allowed to receive fresh IDs. -/
def fromCursor (cursor : Cursor) : Writer :=
  { nextName := cursor.nextName, nextLevel := cursor.nextLevel,
    nextExpr := cursor.nextExpr }

def cursor (w : Writer) : Cursor :=
  { nextName := w.nextName, nextLevel := w.nextLevel, nextExpr := w.nextExpr }

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
      let i := w.nextName
      let w := (w.push s!"\{\"in\":{i},\"str\":\{\"pre\":{pi},\"str\":{esc s}}}")
      ({ w with names := w.names.insert n i, nextName := i + 1 }, i)
    | .num p k =>
      let (w, pi) := w.name p
      let i := w.nextName
      let w := (w.push s!"\{\"in\":{i},\"num\":\{\"i\":{k},\"pre\":{pi}}}")
      ({ w with names := w.names.insert n i, nextName := i + 1 }, i)

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
    let i := w.nextLevel
    let w := w.push s!"\{\"il\":{i},{body}}"
    ({ w with levels := w.levels.insert l i, nextLevel := i + 1 }, i)

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
    let i := w.nextExpr
    let w := w.push s!"\{\"ie\":{i},{body}}"
    ({ w with exprs := w.exprs.insert e i, nextExpr := i + 1 }, i)

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

/-- One declaration split into the arena definitions which must precede every
declaration spool, and its single reorderable declaration line. -/
structure DeclSplit where
  before : Cursor
  arena : Array String
  declaration : String
  after : Cursor
  deriving Inhabited, Repr, BEq

/-- Fail closed when a spool segment was produced for a different arena
cursor.  The reader accepts sparse arenas for compatibility, so composition
must enforce the writer's stronger continuous-ID contract itself. -/
def DeclSplit.validateStart (split : DeclSplit) (expected : Cursor) : Except String Unit :=
  if split.before == expected then .ok ()
  else .error s!"arena segment starts at {repr split.before}, expected {repr expected}"

/-- Serialize one declaration while keeping arena and declaration records
separate.  The returned writer retains only this island's interning maps, but
its line buffer is empty and ready for the next declaration in the island. -/
def splitDecl (w : Writer) (d : EDecl) : Writer × DeclSplit :=
  match w with
  | { names, levels, exprs, nextName, nextLevel, nextExpr, .. } =>
    let before := { nextName, nextLevel, nextExpr : Cursor }
    let completed :=
      ({ out := #[], names, levels, exprs, nextName, nextLevel, nextExpr } : Writer).decl d
    match completed with
    | { out, names, levels, exprs, nextName, nextLevel, nextExpr } =>
      let declaration := out.back!
      let arena := out.pop
      let after := { nextName, nextLevel, nextExpr : Cursor }
      ({ out := #[], names, levels, exprs, nextName, nextLevel, nextExpr },
        { before, arena, declaration, after })

end Writer

/-- Standard persistent export writer for declarations which become available
one at a time. Arena lines are flushed in bounded physical chunks, while the
ordinary name, level, and expression interning maps remain global for exactly
the lifetime of the output transaction. Complete `EDecl` arrays are never
retained by this state. -/
structure DeclarationStreamWriter where
  writer : Writer := {}
  buffer : String := ""
  bufferedBytes : Nat := 0
  declarationsWritten : Nat := 0
  maxRecordLines : Nat := 0
  deriving Inhabited

namespace DeclarationStreamWriter

private def writeChunk : Nat := 4 * 1024 * 1024

private def emitLines (state : DeclarationStreamWriter) (h : IO.FS.Stream)
    (lines : Array String) : IO DeclarationStreamWriter := do
  -- Consume the buffer from the input state before extending it, preserving
  -- unique string ownership across the callback boundary.
  let { writer, buffer, bufferedBytes, declarationsWritten, maxRecordLines } := state
  let mut buffer := buffer
  let mut bufferedBytes := bufferedBytes
  for line in lines do
    buffer := buffer ++ line ++ "\n"
    bufferedBytes := bufferedBytes + line.utf8ByteSize + 1
  if bufferedBytes >= writeChunk then
    h.putStr buffer
    buffer := ""
    bufferedBytes := 0
  return { writer, buffer, bufferedBytes, declarationsWritten, maxRecordLines }

/-- Begin a declaration stream and emit its optional metadata record. -/
def start (metaLine : Json) (h : IO.FS.Stream) : IO DeclarationStreamWriter := do
  let state : DeclarationStreamWriter := {}
  if metaLine.isNull then return state
  state.emitLines h #[metaLine.compress]

/-- Feed one exact declaration into the persistent standard writer. The lines
it adds are moved into the bounded buffer immediately; the returned state keeps
only the standard global interning maps, not the declaration or line array. -/
def writeDeclaration (state : DeclarationStreamWriter) (h : IO.FS.Stream)
    (declaration : EDecl) : IO DeclarationStreamWriter := do
  -- Consume the outer state before extending the writer. Keeping `state`
  -- alive across `Writer.decl` would retain a sibling reference to its maps
  -- and could force every declaration insertion down a copy-on-write path.
  let { writer, buffer, bufferedBytes, declarationsWritten, maxRecordLines } := state
  let { out := lines, names, levels, exprs, nextName, nextLevel, nextExpr } :=
    writer.decl declaration
  let state : DeclarationStreamWriter := {
    writer := { out := #[], names, levels, exprs, nextName, nextLevel, nextExpr }
    buffer, bufferedBytes, declarationsWritten, maxRecordLines }
  let nextState ← state.emitLines h lines
  let nextState := { nextState with
    declarationsWritten := declarationsWritten + 1 }
  return { nextState with maxRecordLines := max maxRecordLines lines.size }

def cursor (state : DeclarationStreamWriter) : Writer.Cursor := state.writer.cursor

/-- Flush the final bounded buffer. The enclosing output transaction owns the
stream flush and commit decision. -/
def finish (state : DeclarationStreamWriter) (h : IO.FS.Stream) : IO Unit :=
  unless state.buffer.isEmpty do h.putStr state.buffer

end DeclarationStreamWriter

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

A `Stream` rather than a `Handle` because `-o -` is stdout, which `lean-inductive-models`
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

end InductiveModels
