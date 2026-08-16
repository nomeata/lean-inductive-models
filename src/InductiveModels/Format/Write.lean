import InductiveModels.Format.Parse
/-!
# Writing an export

Fresh dense interning in dependency order with the exporter's key order and
spacing.
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

/-! ## Interning

The writer holds one table entry per emitted arena node for the whole length of
the export — nothing may be forgotten, because any later record may
back-reference any earlier ID — so the *per-entry* cost of these tables is the
writer's entire memory profile.  On Mathlib that is ~10^8 entries, and the
difference between a cheap entry and an expensive one is gigabytes.

A `Std.HashMap` spends a three-word `AssocList.cons` cell (32 bytes with its
header) on every entry, plus a machine word per bucket at a 3/4 load factor:
about 40 bytes to record that a pointer we are already holding was given a
small integer.  Measured on a 10M-line Mathlib prefix, that is 40.5 bytes per
interned node.

[`Interner`] stores the same fact in two much smaller pieces:

* the key, once, in a **dense array in insertion order** — and insertion order
  *is* arena-ID order, because the writer interns a node exactly when it hands
  out the next ID, so the node at index `i` has ID `base + i` and no side table
  of values is needed at all; and
* an **open-addressed probe table** of indices into that array, packed two
  31-bit slots to a machine word, so a probe slot costs four bytes rather than
  the eight an `Array Nat` would spend or the 32 + 8 the hash map does.

The key array is a plain `Array`, whose `push` doubles capacity and so sits on
up to twice the bytes it uses.  Holding the keys in fixed-size chunks instead
removes that slack on paper — 274 MB of it at Mathlib's 99.9M expressions — but
was measured *raising* the whole-export peak from 11.37 GiB to 11.52 GiB, so
the peak is not where the slack is.  The simpler array stays.

Replacing the map is sound only because `Expr`, `Level` and `Name` all hash
consistently with their `BEq`: equal keys always have equal hashes (`Expr.eqv`
ignores binder names and annotations, and `Expr.hash` excludes both).  A table
built by lookup-then-insert therefore never holds two equal keys, and linear
probing from a key's home slot — which passes over no empty slot before
reaching an entry inserted from the same home slot — finds exactly the entry
bucketing would have found.  The IDs handed out, and so the emitted bytes, are
unchanged.
-/

/-- The width of one packed probe slot.  Two fit in a machine word with the
tag bit to spare, so `Nat` slots stay unboxed scalars. -/
@[inline] private def probeBits : Nat := 31

/-- One past the largest index a probe slot can hold.  A table storing this
many nodes would be an export of some 10^11 lines. -/
@[inline] private def probeLimit : Nat := 1 <<< probeBits

/-- The low slot of a packed word. -/
@[inline] private def probeMask : Nat := probeLimit - 1

/-- A dense arena interning table: keys in ID order, plus an open-addressed
index into them.  See the section comment for why this is not a `Std.HashMap`. -/
structure Interner (α : Type) where
  /-- The arena ID of `keys[0]`.  The node at index `i` has ID `base + i`. -/
  base : Nat := 0
  /-- The interned nodes, in insertion order, which is arena-ID order. -/
  keys : Array α := #[]
  /-- An open-addressed index into [`keys`], two 31-bit slots per element: slot
  `k` is the low field of `probe[k / 2]` when `k` is even and the high field
  when it is odd.  A slot is `0` when empty and `i + 1` for `keys[i]`
  otherwise.  The slot count is a power of two and always exceeds `keys.size`,
  so a probe always meets an empty slot. -/
  probe : Array Nat := Array.replicate 8 0

instance : Inhabited (Interner α) := ⟨{}⟩

namespace Interner

/-- An empty table whose first node will be given arena ID `base`, sized to
hold `capacity` nodes without rehashing. -/
def empty (base capacity : Nat) : Interner α :=
  { base, probe := Array.replicate (max 16 (capacity * 4 / 3).nextPowerOfTwo / 2) 0 }

/-- The arena ID the next interned node will receive.  The three counters the
writer used to carry alongside its maps are this, and cannot drift from it. -/
@[inline] def next (t : Interner α) : Nat := t.base + t.keys.size

@[inline] private def slotAt (probe : Array Nat) (k : Nat) : Nat :=
  let w := probe[k >>> 1]!
  if k &&& 1 == 0 then w &&& probeMask else w >>> probeBits

@[inline] private def setSlotAt (probe : Array Nat) (k v : Nat) : Array Nat :=
  let j := k >>> 1
  let w := probe[j]!
  probe.set! j <| if k &&& 1 == 0 then ((w >>> probeBits) <<< probeBits) ||| v
    else (w &&& probeMask) ||| (v <<< probeBits)

/-- Write `v` into the first empty slot at or after `k`.  `fuel` is the slot
count, which strictly exceeds the number of occupied slots, so the scan always
finds one and never runs out. -/
private def place (probe : Array Nat) (k mask v : Nat) : Nat → Array Nat
  | 0 => probe
  | fuel + 1 =>
    if slotAt probe k == 0 then setSlotAt probe k v
    else place probe ((k + 1) &&& mask) mask v fuel

/-- The arena ID `a` was interned under, if it was. -/
@[specialize] def find? [BEq α] [Hashable α] [Inhabited α] (t : Interner α) (a : α) :
    Option Nat :=
  let slots := t.probe.size * 2
  go ((hash a).toUInt32.toNat &&& (slots - 1)) (slots - 1) slots
where
  go (k mask : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      let s := slotAt t.probe k
      if s == 0 then none
      else if t.keys[s - 1]! == a then some (t.base + (s - 1))
      else go ((k + 1) &&& mask) mask fuel

/-- Rebuild the probe table at twice the slot count once it passes the standard
3/4 load factor.  The table is derived from [`keys`], so it is rebuilt rather
than copied and the old one is released first: the two are never live at once,
which is what keeps the rehash from being the run's peak. -/
@[specialize] private def grow [Hashable α] [Inhabited α] (t : Interner α) : Interner α :=
  if (t.keys.size + 1) * 4 ≤ t.probe.size * 2 * 3 then t else
  match t with
  | { base, keys, probe } =>
    let slots := probe.size * 4
    let words := probe.size * 2
    let fresh := Array.replicate words 0
    let mask := slots - 1
    let probe := Id.run do
      let mut probe := fresh
      for i in [0 : keys.size] do
        probe := place probe ((hash keys[i]!).toUInt32.toNat &&& mask) mask (i + 1) slots
      return probe
    { base, keys, probe }

/-- Intern `a` under the next arena ID and return that ID.  `a` must be absent:
the writer only ever calls this after [`find?`] has missed. -/
@[specialize] def insert [BEq α] [Hashable α] [Inhabited α] (t : Interner α) (a : α) :
    Interner α × Nat :=
  match t.grow with
  | { base, keys, probe } =>
    let id := base + keys.size
    if keys.size + 1 ≥ probeLimit then
      panic! "arena interning table exhausted: more than 2^31 - 1 nodes"
    else
      let slots := probe.size * 2
      let mask := slots - 1
      let probe := place probe ((hash a).toUInt32.toNat &&& mask) mask (keys.size + 1) slots
      ({ base, keys := keys.push a, probe }, id)

end Interner

structure Writer where
  /-- The lines of the record being written. Drained by [`Export.stream`] after
  each record — do not accumulate a file here. -/
  out : Array String := #[]
  /-- Interned names.  The format's distinguished anonymous name is *not* in
  here: [`Writer.name`] answers `0` for it directly, which is what keeps the
  table's IDs contiguous from [`Interner.base`]. -/
  names : Interner Name := Interner.empty 1 1024
  /-- Interned levels.  As with [`names`], the distinguished zero level is
  answered directly rather than interned. -/
  levels : Interner Level := Interner.empty 1 64
  exprs : Interner Expr := Interner.empty 0 4096
  deriving Inhabited

namespace Writer

/-- The exclusive upper bounds of the three independent export arenas. -/
structure Cursor where
  nextName : Nat := 1
  nextLevel : Nat := 1
  nextExpr : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Start a structurally fresh writer at explicit, non-overlapping arena IDs.
Only the format's distinguished anonymous name and zero level remain shared
at index zero.  Equal nontrivial nodes written by another island are therefore
allowed to receive fresh IDs. -/
def fromCursor (cursor : Cursor) : Writer :=
  { names := Interner.empty cursor.nextName 1024,
    levels := Interner.empty cursor.nextLevel 64,
    exprs := Interner.empty cursor.nextExpr 4096 }

/-- The next arena IDs.  They are the interning tables' own dense extents,
so a fresh island-local writer continues after an earlier island simply by
starting its tables at the cursor. -/
def cursor (w : Writer) : Cursor :=
  { nextName := w.names.next, nextLevel := w.levels.next, nextExpr := w.exprs.next }

private def esc (s : String) : String := (Json.str s).compress

/-! The four writer updates below all rebuild the record from its destructured
fields rather than using `{ w with … }`.  That is deliberate and load-bearing:
`{ w with f := g w.f }` leaves `w` holding a sibling reference to the field
while `g` runs, which sends every array push and every table insertion down a
copy-on-write path. -/

private def push (w : Writer) (line : String) : Writer :=
  match w with
  | { out, names, levels, exprs } => { out := out.push line, names, levels, exprs }

@[inline] private def internName (w : Writer) (n : Name) : Writer × Nat :=
  match w with
  | { out, names, levels, exprs } =>
    let (names, i) := names.insert n
    ({ out, names, levels, exprs }, i)

@[inline] private def internLevel (w : Writer) (l : Level) : Writer × Nat :=
  match w with
  | { out, names, levels, exprs } =>
    let (levels, i) := levels.insert l
    ({ out, names, levels, exprs }, i)

@[inline] private def internExpr (w : Writer) (e : Expr) : Writer × Nat :=
  match w with
  | { out, names, levels, exprs } =>
    let (exprs, i) := exprs.insert e
    ({ out, names, levels, exprs }, i)

partial def name (w : Writer) (n : Name) : Writer × Nat :=
  match w.names.find? n with
  | some i => (w, i)
  | none =>
    match n with
    | .anonymous => (w, 0)  -- distinguished, never interned
    | .str p s =>
      let (w, pi) := w.name p
      let (w, i) := w.internName n
      (w.push s!"\{\"in\":{i},\"str\":\{\"pre\":{pi},\"str\":{esc s}}}", i)
    | .num p k =>
      let (w, pi) := w.name p
      let (w, i) := w.internName n
      (w.push s!"\{\"in\":{i},\"num\":\{\"i\":{k},\"pre\":{pi}}}", i)

partial def level (w : Writer) (l : Level) : Writer × Nat :=
  if l matches .zero then (w, 0) else  -- distinguished, never interned
  match w.levels.find? l with
  | some i => (w, i)
  | none =>
    let (w, body) :=
      match l with
      | .zero => (w, "")  -- unreachable: answered above
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
    let (w, i) := w.internLevel l
    (w.push s!"\{\"il\":{i},{body}}", i)

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
  match w.exprs.find? e with
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
    let (w, i) := w.internExpr e
    (w.push s!"\{\"ie\":{i},{body}}", i)

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

/-- One declaration split into the arena definitions which must precede it,
and its single reorderable declaration line. -/
structure DeclSplit where
  before : Cursor
  arena : Array String
  declaration : String
  after : Cursor
  deriving Inhabited, Repr, BEq

/-- Fail closed when a segment was produced for a different arena cursor. The
reader accepts sparse arenas for compatibility, so composition must enforce
the writer's stronger continuous-ID contract itself. -/
def DeclSplit.validateStart (split : DeclSplit) (expected : Cursor) : Except String Unit :=
  if split.before == expected then .ok ()
  else .error s!"arena segment starts at {repr split.before}, expected {repr expected}"

/-- Serialize one declaration while keeping arena and declaration records
separate.  The returned writer retains only this island's interning maps, but
its line buffer is empty and ready for the next declaration in the island. -/
def splitDecl (w : Writer) (d : EDecl) : Writer × DeclSplit :=
  match w with
  | { names, levels, exprs, .. } =>
    let before :=
      { nextName := names.next, nextLevel := levels.next, nextExpr := exprs.next : Cursor }
    let completed := ({ out := #[], names, levels, exprs } : Writer).decl d
    match completed with
    | { out, names, levels, exprs } =>
      let declaration := out.back!
      let arena := out.pop
      let after :=
        { nextName := names.next, nextLevel := levels.next, nextExpr := exprs.next : Cursor }
      ({ out := #[], names, levels, exprs }, { before, arena, declaration, after })

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
  let { out := lines, names, levels, exprs } := writer.decl declaration
  let state : DeclarationStreamWriter := {
    writer := { out := #[], names, levels, exprs }
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
