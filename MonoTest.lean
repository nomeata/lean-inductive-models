import Modelgen.Mono

/-!
# `monomorph`'s own oracles, as a test

Run from the repository root: `lake exe monotest [ROOT]`.

Five axes, and each one has an occupant the other four would pass.

1. **The kernel.** Mode A's output is replayed into a `Lean.Environment` with
   `addDeclCore`'s checking **on**. A file that comes back with
   `rejected = 0` is Lean's answer about the monomorphized declarations, not
   this tool's. It is also the only reason the recursors are right: the pass
   asks the kernel to mint them rather than substituting the export's, because
   substituting is wrong (`mono_prop`).
2. **The counts**, pinned below, in *both* modes. A pass that renamed instead of
   duplicating measures nothing on a file where every declaration is used once,
   and the two mode columns are what separate mode A from mode B — they are
   equal on every fixture where no recursor is used at more than one motive
   universe, which is why `mono_elim` exists.
3. **The derived flags.** `mono_prop` pins `recRegen`: the recursors the kernel
   minted *differently* from what substituting `σ` would have produced. Zero
   there would mean the K-like and the large-elimination move had gone unnoticed.
4. **The round trip.** `parse (render y) = y`, structurally, and a file with no
   universe parameter at all comes back byte for byte.
5. **`nanoda`**, outside this process: `MONOMORPH.md` §5 records the corpus
   run and its numbers. It is not run from here.
-/

open Lean Meta Modelgen Modelgen.Mono

/-- `(fixture, declarations in, mode A out, mode B out, recursors the kernel
minted differently, refusal)`. -/
structure Row where
  file : String
  declsIn : Nat := 0
  outA : Nat := 0
  outB : Nat := 0
  regen : Nat := 0
  refused : Option String := none

def expected : List Row :=
  [ { file := "mono_poly",  declsIn := 20, outA := 32, outB := 32, regen := 0 }
  -- **The memo's key, and the one shape that makes it wrong.** `fwd` and `rev`
  -- share one type expression and order their `levelParams` oppositely, and are
  -- used at instantiations that agree *positionally*. A rewrite memo keyed on a
  -- parameter's position in the declaring declaration's own list gives them one
  -- key and two different right answers; measured, that is `rejected = 2` here
  -- and `0` with the global key. The counts alone do not move, so it is axis 1
  -- — the kernel — that catches it and nothing else would.
  , { file := "mono_share", declsIn := 12, outA := 13, outB := 13, regen := 0 }
  , { file := "mono_elim",  declsIn := 10, outA := 10, outB := 12, regen := 0 }
  , { file := "mono_proj",  declsIn := 12, outA := 19, outB := 19, regen := 0 }
  , { file := "mono_prop",  declsIn := 17, outA := 23, outB := 23, regen := 2 }
  , { file := "mono_mutual",declsIn := 14, outA := 21, outB := 21, regen := 0 }
  -- **The `all` field is not a group.** The two members of this mutual
  -- `partial def` block are 73 records apart with a user of the first and an
  -- inductive the *second* needs in between, so a grouping that emitted the
  -- block at its first member would carry the second in front of `Box` and
  -- refuse the file for a forward reference it had just created. It is also
  -- the count: the members are demanded at `[0]` and at `[1]`, one copy each,
  -- and a shared instantiation set would make it two each — 24 out, not 22.
  , { file := "mono_split", declsIn := 18, outA := 22, outB := 22, regen := 0 }
  , { file := "mono_offname", declsIn := 13, outA := 19, outB := 19, regen := 0 }
  , { file := "marker_taken"
      refused := some "the file already declares foo._at.bar, which spells a marker" } ]

def readExport (p : String) : IO (Option (String × Export)) := do
  if !(← System.FilePath.pathExists p) then return none
  let t ← IO.FS.readFile p
  match Modelgen.parse t with
  | .error e => throw (IO.userError s!"{p}: {e}")
  | .ok x => return some (t, x)

/-- What `monomorph -o` would put in the file: [`Export.writeTo`] through a
temporary, read back. -/
def streamed (y : Export) : IO String := do
  let (h, p) ← IO.FS.createTempFile
  try
    y.writeTo (IO.FS.Stream.ofHandle h)
    h.flush
    IO.FS.readFile p
  finally
    IO.FS.removeFile p

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  initSearchPath (← findSysroot)
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<monotest>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let mut fails : Array String := #[]
  let mut ran := 0

  -- ── The fixtures.
  for r in expected do
    let p := s!"{root}/monotests/{r.file}.ndjson"
    let some (text, x) ← readExport p | fails := fails.push s!"{r.file}: missing"; continue
    ran := ran + 1
    for (modeB, want) in [(false, r.outA), (true, r.outB)] do
      let opts : Mono.Opts := { monoRecursors := modeB, check := !modeB }
      let ((y, rep), _) ←
        Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (monomorphize x opts)) ctx { env }
      let tag := if modeB then "B" else "A"
      match r.refused with
      | some why =>
        unless rep.refused == some why do
          fails := fails.push s!"{r.file}[{tag}]: expected refusal {why}, got {rep.refused}"
        unless y.render == text || rep.refused.isSome do
          fails := fails.push s!"{r.file}[{tag}]: a refused file must come back unchanged"
      | none =>
        if let some why := rep.refused then
          fails := fails.push s!"{r.file}[{tag}]: unexpected refusal {why}"
          continue
        unless rep.declsIn == r.declsIn do
          fails := fails.push s!"{r.file}[{tag}]: {rep.declsIn} declarations in, expected {r.declsIn}"
        unless rep.declsOut == want do
          fails := fails.push s!"{r.file}[{tag}]: {rep.declsOut} out, expected {want}"
        unless rep.recRegen == r.regen do
          fails := fails.push s!"{r.file}[{tag}]: recRegen {rep.recRegen}, expected {r.regen}"
        unless rep.errors.isEmpty do
          fails := fails.push s!"{r.file}[{tag}]: {rep.errors.size} problems: {rep.errors[0]!}"
        unless rep.rejected == 0 do
          fails := fails.push s!"{r.file}[{tag}]: the kernel rejected {rep.rejected} of the output"
        -- The round trip.
        match Modelgen.parse y.render with
        | .error e => fails := fails.push s!"{r.file}[{tag}]: output does not re-parse: {e}"
        | .ok z =>
          unless z.decls == y.decls do
            fails := fails.push s!"{r.file}[{tag}]: render/parse is not the identity"
        -- **The two consumers of the writer agree.** `render` is what the
        -- checks above read and `writeTo` is what the binary actually emits;
        -- they share one fold, and this is what says so.
        unless (← streamed y) == y.render do
          fails := fails.push s!"{r.file}[{tag}]: writeTo and render disagree"

  -- ── A file with no universe parameter anywhere is the identity, byte for
  -- byte. Without this, "one copy per instantiation" could be one copy per
  -- declaration and every count above would still hold.
  let idp := s!"{root}/vendor/arena-tests/good/tutorial/001_basicDef.ndjson"
  if let some (text, x) ← readExport idp then
    ran := ran + 1
    let ((y, _), _) ←
      Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (monomorphize x {})) ctx { env }
    unless y.render == text do fails := fails.push "001_basicDef: not byte-identical"
    unless (← streamed y) == text do
      fails := fails.push "001_basicDef: not byte-identical through writeTo"

  -- ── The corpus, when it is present: no `good/` file may report a problem,
  -- and none of its output may be rejected by the kernel.
  let corpus := s!"{root}/vendor/arena-tests/good"
  if ← System.FilePath.isDir corpus then
    let mut din := 0
    let mut dout := 0
    let mut files := 0
    for e in ← System.FilePath.walkDir corpus do
      unless e.toString.endsWith ".ndjson" do continue
      if (e.toString.splitOn "/perf/").length != 1 then continue
      let some (_, x) ← readExport e.toString | continue
      files := files + 1
      let ((_, rep), _) ←
        Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (monomorphize x { check := true })) ctx { env }
      if rep.refused.isSome then continue
      din := din + rep.declsIn; dout := dout + rep.declsOut
      unless rep.errors.isEmpty && rep.rejected == 0 do
        fails := fails.push s!"{e}: {rep.errors.size} problems, {rep.rejected} rejected"
    ran := ran + files
    IO.println s!"corpus: {files} files, {din} declarations in, {dout} out"

  if fails.isEmpty then
    IO.println s!"monotest: {ran} checks, all pass"
    return 0
  else
    for f in fails do IO.eprintln s!"  ! {f}"
    IO.eprintln s!"monotest: {fails.size} failures"
    return 1
