import Lean

/-!
# Command-line configuration

This module contains only the command-line data model and parser. Keeping it
independent of `Main` and the generator makes option semantics testable without
reading an export or constructing a Lean environment.

Options are applied from left to right. The plural options are bundles:
`--inductives` (or `--no-inductives`) changes all four model-generation
branches, and `--check` (or `--no-check`) changes both checks. A later
individual option may therefore override part of an earlier bundle, and a
later bundle may override earlier individual options.
-/

namespace Modelgen.Cli

/-- The command line after parsing, before any input is read. -/
structure Config where
  input : Option String := none
  nested : Bool := true
  mutualModels : Bool := true
  /-- Ordinary non-mutual inductives, excluding [`basicInputNames`]. -/
  simple : Bool := true
  /-- Bootstrap inductives and generated support needed to reduce to the basis. -/
  basic : Bool := true
  checkInput : Bool := true
  checkOutput : Bool := true
  monoLevels : Bool := false
  /-- Whether an export is written. -/
  output : Bool := true
  /-- `"-"` means stdout. The target is retained while output is disabled. -/
  outputTarget : String := "-"
  quiet : Bool := false
  deriving Repr, BEq

/-- The input declarations assigned to the bootstrap branch rather than the
ordinary-simple branch. Generated support inductives form a dynamic closure;
that closure belongs in the generator, not in this command-line module. -/
def basicInputNames : List Lean.Name := [`Acc, `Nonempty]

def isBasicInputName (name : Lean.Name) : Bool :=
  basicInputNames.contains name

/-- Select the CLI branch for a non-mutual, non-nested input inductive. Shape
classification and generated-support closure are intentionally left to the
driver. -/
def Config.modelsSimpleInput (config : Config) (name : Lean.Name) : Bool :=
  if isBasicInputName name then config.basic else config.simple

def usage : String := String.intercalate "\n" [
  "usage: modelgen [OPTIONS] IN.ndjson",
  "  -o PATH              write the export to PATH (`-` means stdout)",
  "  --[no-]output        enable or disable output",
  "  --[no-]nested        model nested inductives",
  "  --[no-]mutual        model mutual inductives",
  "  --[no-]simple        model ordinary non-mutual inductives",
  "  --[no-]basic         model bootstrap and generated support inductives",
  "  --[no-]inductives    set all four inductive-model options",
  "  --[no-]check-input   check models already present in the input",
  "  --[no-]check-output  check generated models",
  "  --[no-]check         set both check options",
  "  --[no-]mono-levels   monomorphize universe levels",
  "  --[no-]quiet         enable or disable diagnostics"]

/-- Parse command-line arguments without performing IO. -/
def parseArgs (args : List String) : Except String Config :=
  go args {}
where
  go : List String → Config → Except String Config
    | [], config =>
      if config.input.isSome then .ok config else .error "no input file"
    | "-o" :: [], _ => .error "missing operand after -o"
    | "-o" :: path :: rest, config =>
      go rest { config with output := true, outputTarget := path }
    | "--nested" :: rest, config => go rest { config with nested := true }
    | "--no-nested" :: rest, config => go rest { config with nested := false }
    | "--mutual" :: rest, config => go rest { config with mutualModels := true }
    | "--no-mutual" :: rest, config => go rest { config with mutualModels := false }
    | "--simple" :: rest, config => go rest { config with simple := true }
    | "--no-simple" :: rest, config => go rest { config with simple := false }
    | "--basic" :: rest, config => go rest { config with basic := true }
    | "--no-basic" :: rest, config => go rest { config with basic := false }
    | "--inductives" :: rest, config =>
      go rest {
        config with nested := true, mutualModels := true, simple := true, basic := true }
    | "--no-inductives" :: rest, config =>
      go rest {
        config with nested := false, mutualModels := false, simple := false, basic := false }
    | "--check-input" :: rest, config => go rest { config with checkInput := true }
    | "--no-check-input" :: rest, config => go rest { config with checkInput := false }
    | "--check-output" :: rest, config => go rest { config with checkOutput := true }
    | "--no-check-output" :: rest, config => go rest { config with checkOutput := false }
    | "--check" :: rest, config =>
      go rest { config with checkInput := true, checkOutput := true }
    | "--no-check" :: rest, config =>
      go rest { config with checkInput := false, checkOutput := false }
    | "--mono-levels" :: rest, config => go rest { config with monoLevels := true }
    | "--no-mono-levels" :: rest, config => go rest { config with monoLevels := false }
    | "--output" :: rest, config => go rest { config with output := true }
    | "--no-output" :: rest, config => go rest { config with output := false }
    | "--quiet" :: rest, config => go rest { config with quiet := true }
    | "--no-quiet" :: rest, config => go rest { config with quiet := false }
    | arg :: rest, config =>
      if arg.startsWith "-" then
        .error s!"unknown option {arg}"
      else if let some previous := config.input then
        .error s!"multiple input files: {previous} and {arg}"
      else
        go rest { config with input := some arg }

end Modelgen.Cli
