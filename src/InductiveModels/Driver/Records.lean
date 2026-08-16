import InductiveModels.Model

/-!
# Lean declarations as export records

The conversion in the direction the driver needs it: an installed inductive
block, a `Declaration`, or an installed quotient primitive read back as the
export records that name it.  Pure record plumbing — nothing here generates a
model, so both the island machinery and the source census may depend on it.
-/

open Lean Meta

namespace InductiveModels

/-- Read one inductive block back out of the environment, including the
recursors the **kernel** generated for it. -/
def indEDecl (names : Array Name) : MetaM EDecl := do
  let env ← getEnv
  let mut ts : Array EIndType := #[]
  let mut cs : Array ECtor := #[]
  let mut rs : Array ERec := #[]
  for n in names do
    let some (.inductInfo iv) := env.constants.find? n | throwError "{n} is not an inductive"
    ts := ts.push
      { name := iv.name, levelParams := iv.levelParams, type := iv.type, all := iv.all
        ctors := iv.ctors, numParams := iv.numParams, numIndices := iv.numIndices
        numNested := iv.numNested, isRec := iv.isRec, isReflexive := iv.isReflexive
        isUnsafe := iv.isUnsafe }
    for cn in iv.ctors do
      let some (.ctorInfo cv) := env.constants.find? cn | throwError "{cn} is not a constructor"
      cs := cs.push
        { name := cv.name, levelParams := cv.levelParams, type := cv.type, cidx := cv.cidx
          numParams := cv.numParams, numFields := cv.numFields, induct := cv.induct
          isUnsafe := cv.isUnsafe }
  for n in names do
    if let some (.recInfo rv) := env.constants.find? (Name.str n "rec") then
      rs := rs.push
        { name := rv.name, levelParams := rv.levelParams, type := rv.type, all := rv.all
          numParams := rv.numParams, numIndices := rv.numIndices, numMotives := rv.numMotives
          numMinors := rv.numMinors, k := rv.k, isUnsafe := rv.isUnsafe
          rules := rv.rules.map fun r =>
            { ctor := r.ctor, nfields := r.nfields, rhs := r.rhs } }
  return .induct ts.toList cs.toList rs.toList


/-- Read the exact recursor records of a block generated inside this pass. -/
def recursorsOfNames (names : Array Name) : MetaM (Array ERec) := do
  let .induct _ _ recursors ← indEDecl names
    | throwError "{names} did not read back as an inductive block"
  return recursors.toArray

/-- A generated declaration as an export record. -/
def toEDecl : Declaration → MetaM EDecl
  | .defnDecl v =>
      return .defn v.name v.levelParams v.type v.value (hintsOf v.hints)
        (safetyTo v.safety) [v.name]
  | .thmDecl v => return .thm v.name v.levelParams v.type v.value [v.name]
  | .axiomDecl v => return .ax v.name v.levelParams v.type v.isUnsafe
  | .opaqueDecl v => return .opaq v.name v.levelParams v.type v.value v.isUnsafe [v.name]
  | .inductDecl _ _ ts _ => indEDecl (ts.toArray.map (·.name))
  | d => throwError "cannot serialise {d.getTopLevelNames}"

/-- The export's word for each of the four quotient records. Read off the
`QuotKind` the kernel stamped on the constant, so the record is recognised
**structurally** on the way back out. -/
def quotKindStr : QuotKind → String
  | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"

/-- Whether a quotient export record is exactly the part of the single kernel
`quotDecl` already installed in `env`.  This distinguishes the three covered
records of a valid four-record bundle from malformed or unrelated records. -/
def installedQuotRecord (env : Environment) : EDecl → Bool
  | .quot name levelParams type kind =>
    match env.constants.find? name with
    | some (.quotInfo info) => info.levelParams == levelParams && info.type == type &&
        quotKindStr info.kind == kind
    | _ => false
  | _ => false

/-- The exact four-record export spelling of the kernel quotient already
installed in `env`.  A quotient declaration is atomic to the kernel even
though lean4export represents it by four consecutive records. -/
def installedQuotRecords? (env : Environment) : Option (Array EDecl) := do
  let record (name : Name) : Option EDecl :=
    match env.constants.find? name with
    | some (.quotInfo info) =>
      some (.quot info.name info.levelParams info.type (quotKindStr info.kind))
    | _ => none
  let quot ← record `Quot
  let mk ← record `Quot.mk
  let lift ← record `Quot.lift
  let ind ← record `Quot.ind
  return #[quot, mk, lift, ind]

/-- A generated declaration as export records — **plural**, because
`Declaration.quotDecl` is one kernel declaration and four records. Everything
else is one record and goes through [`InductiveModels.toEDecl`]. -/
def toEDecls (d : Declaration) : MetaM (Array EDecl) := do
  match d with
  | .quotDecl =>
    let env ← getEnv
    let some records := installedQuotRecords? env
      | throwError "the quotient declaration did not install its four constants"
    return records
  | _ => return #[← toEDecl d]
