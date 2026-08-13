import InductiveModels.Driver

/-!
`envprobe IN.ndjson [P|A|B|C]` — **what a replayed export is visible as, and
whether Lean's kernel takes it.**

This program measures three facts about Lean's environment that nothing else in
this repository can quantify. It is not a test: the test suite's `runEnvProbe`
pins the same two properties on a fixture so a toolchain bump cannot change
them silently. What this adds is *scale*: the Mathlib counts take substantial
time and memory to obtain.

* **`P`** — parse and stop. Says how much of the pass's peak is the parsed
  export rather than the environment built from it.
* **`A`** — parse, then replay through `Environment.addDeclCore`, which is
  what `InductiveModels.runFilter` does. Counts and prints the names that are in the
  **kernel** constant map and invisible to `Environment.find?`: the
  `AsyncConsts.add` panic's victims, and the auxiliary `T.rec_k` of every
  nested inductive, which `Declaration.getNames` documents itself as omitting.
* **`B`** — parse, then replay through
  `Kernel.Environment.addDeclWithoutChecking` and hand the result to
  `Environment.ofKernelEnv`. Counts how many names survive into
  `Environment.find?`, which is the lookup `MetaM` uses.

* **`C`** — parse, then replay through `Environment.addDeclCore` **with
  checking on**, and report how many declarations the kernel *rejected*, with
  the first few reasons. This is the whole-output oracle: `lean-inductive-models` checks
  each declaration it generates as it generates it, against the environment it
  has built so far, and `C` asks the independent question — does the emitted
  file, read back from bytes and replayed from nothing, typecheck end to end.
  `A` deliberately swallows rejections (it is asking about visibility, not
  validity); `C` is the mode that counts them.

No argument: `A` then `B`. Both replays in one process needs twice the memory of
one, so on anything Mathlib-sized pass a mode.
-/

open Lean Meta InductiveModels

def probeA (x : Export) (names : Array Name) (env0 : Environment) : IO Unit := do
  let mut env := env0
  for d in x.decls do
    if let some dcl := toDeclaration env d then
      match env.addDeclCore 0 dcl none false with
      | .ok e => env := e
      | .error _ => pure ()
  let kenv := env.toKernelEnv
  let mut lost : Array Name := #[]
  for n in names do
    if (kenv.find? n).isSome && (env.find? n).isNone then lost := lost.push n
  IO.println s!"A addDeclCore: {names.size} names, {lost.size} in the kernel map and \
    invisible to Environment.find?"
  for n in lost do IO.println s!"  lost {n}"

/-- Replay with the kernel switched on, and count what it refuses. -/
def probeC (x : Export) (env0 : Environment) : IO Unit := do
  let mut env := env0
  let mut ok := 0
  let mut bad : Array String := #[]
  for d in x.decls do
    if let some dcl := toDeclaration env d then
      match env.addDeclCore 0 dcl none true with
      | .ok e => env := e; ok := ok + 1
      | .error ex =>
        bad := bad.push s!"{dcl.getTopLevelNames}: {← (ex.toMessageData {}).toString}"
  IO.println s!"C checked replay: {ok} accepted, {bad.size} rejected"
  for m in bad[0:10] do IO.println s!"  rejected {m}"

/-- **The W core, spliced onto a replayed input.** Replays `IN` the way the tool
does — trusted, checking off — and then runs [`InductiveModels.ensureWCore`], which is
the checked side. Reports how many of the fragment's records were added, how
many the input already had, and what the kernel said. This is the splice's
oracle at scale: `w_core.ndjson` alone goes in from nothing (that is
`envprobe test/fixtures/inductive-models/w_core.ndjson C`), and this asks the different question of
whether it goes in *on top of* a real export's own `Eq`, `Iff`, `Quot` and
`propext`. -/
def probeW (x : Export) (env0 : Environment) : IO Unit := do
  let mut env := env0
  for d in x.decls do
    if let some dcl := toDeclaration env d then
      match env.addDeclCore 0 dcl none false with
      | .ok e => env := e
      | .error _ => pure ()
  let reserved : Std.HashSet Name :=
    x.decls.foldl (fun s d => d.names.foldl (·.insert ·) s) {}
  let act : MetaM Unit := do
    match ← InductiveModels.ensureWCore reserved with
    | .ok ds =>
      -- The total is read off the compiled-in fragment rather than written
      -- down, so that re-exporting `w_core.ndjson` does not leave a literal
      -- here saying what it used to hold.
      let nFrag := match InductiveModels.parse InductiveModels.wCoreText (analyse := false) with
        | .ok x => x.decls.size
        | .error _ => 0
      IO.println s!"W splice: {ds.size} records added, {nFrag - ds.size} the input \
        already had or the parse folded (the four quotient records are one Declaration)"
      let mut n := 0
      for d in ds do n := n + d.getNames.length
      IO.println s!"W splice: {n} constants, all through addChecked"
      for k in [InductiveModels.wCoreSelf, InductiveModels.wCoreSup, InductiveModels.wCoreRec, InductiveModels.wCoreIota,
                InductiveModels.wCoreDecEqNat, InductiveModels.wCoreDecEqAll] do
        IO.println s!"  {k}: {if ((← getEnv).find? k).isSome then "present" else "MISSING"}"
    | .error e => IO.println s!"W splice DECLINED: {e.label}"
  discard <| Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' act)
    { fileName := "<envprobe>", fileMap := default } { env }

def probeB (x : Export) (names : Array Name) (env0 : Environment) : IO Unit := do
  let mut kenv := env0.toKernelEnv
  for d in x.decls do
    if let some dcl := toDeclaration (Environment.ofKernelEnv kenv) d then
      match kenv.addDeclWithoutChecking dcl with
      | .ok e => kenv := e
      | .error _ => pure ()
  let envB := Environment.ofKernelEnv kenv
  let mut visB := 0
  let mut visK := 0
  for n in names do
    if (envB.find? n).isSome then visB := visB + 1
    if (kenv.find? n).isSome then visK := visK + 1
  IO.println s!"B kernel replay: {visK} of {names.size} in Kernel.Environment.find?, \
    {visB} visible to Environment.find? after ofKernelEnv"

def main (args : List String) : IO UInt32 := do
  let path :: rest := args | do IO.eprintln "usage: envprobe IN.ndjson [P|A|B]"; return 1
  let text ← IO.FS.readFile path
  let .ok x := InductiveModels.parse text (analyse := false) | do IO.eprintln s!"{path}: parse error"; return 2
  initSearchPath (← findSysroot)
  let env0 ← importModules #[] {}
  let mut names : Array Name := #[]
  for d in x.decls do names := names ++ d.names.toArray
  if rest == ["P"] then
    IO.println s!"P parse only: {x.decls.size} records, {names.size} names"
    return 0
  if rest == ["C"] then probeC x env0; return 0
  if rest == ["W"] then probeW x env0; return 0
  unless rest == ["B"] do probeA x names env0
  unless rest == ["A"] do probeB x names env0
  return 0
