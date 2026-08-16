import InductiveModels.OneLayer

/-! A handwritten oracle for the equality bookkeeping used by the generated
one-layer public recursor.  The private recursive result stays fixed while the
public endpoint is eliminated. -/

universe u v

namespace OneLayerRecursorProof

theorem compatibility
    {M : Type u} {P : Type u}
    (roll : P → M) (unroll : M → P)
    (unrollRoll : ∀ p, unroll (roll p) = p)
    (privateCtor : M → M) (publicCtor : P → P)
    (rollCtor : ∀ p, roll (publicCtor p) = privateCtor (roll p))
    (constructorAgreement : ∀ q, publicCtor (unroll q) = unroll (privateCtor q))
    (C : P → Sort v) (minor : ∀ p, C p → C (publicCtor p))
    (core : ∀ q, C (unroll q))
    (coreIota : ∀ q, core (privateCtor q) =
      Eq.mp (congrArg C (constructorAgreement q)) (minor (unroll q) (core q))) :
    let publicRec : ∀ p, C p := fun p =>
      Eq.mp (congrArg C (unrollRoll p)) (core (roll p))
    ∀ p, publicRec (publicCtor p) = minor p (publicRec p) := by
  have cancel {a b : P} (h : a = b) (value : C a) :
      Eq.mp (congrArg C h.symm) (Eq.mp (congrArg C h) value) = value := by
    exact Eq.rec (motive := fun b h =>
      Eq.mp (congrArg C h.symm) (Eq.mp (congrArg C h) value) = value) rfl h
  intro publicRec p
  unfold publicRec
  -- Eliminate only the public endpoint while `q` and its private recursive
  -- result `ih` remain fixed.
  have compat (q r : M) (p : P) (hp : unroll q = p)
      (hc : r = privateCtor q) (hout : unroll r = publicCtor p) :
      Eq.mp (congrArg C hout) (core r) =
        minor p (Eq.mp (congrArg C hp) (core q)) := by
    cases hc
    cases hp
    rw [coreIota]
    have paths : hout = (constructorAgreement q).symm := by rfl
    rw [paths]
    exact cancel (constructorAgreement q) _
  exact compat (roll p) (roll (publicCtor p)) p (unrollRoll p)
    (rollCtor p) (unrollRoll (publicCtor p))

end OneLayerRecursorProof

namespace OneLayerRecursorApplication

axiom M : Type
axiom P : Type
axiom Q : Type
axiom R : Type
axiom C : P → Sort 1
axiom H : R → Sort 1
axiom roll : P → M
axiom unroll : M → P
axiom unrollRoll : ∀ p, unroll (roll p) = p
axiom rollField : R → Q
axiom unrollField : Q → R
axiom unrollRollField : ∀ p, unrollField (rollField p) = p
axiom privateCtor : Q → M
axiom publicCtor : R → P
axiom rollCtor : ∀ p, roll (publicCtor p) = privateCtor (rollField p)
axiom privateIH : ∀ q, H (unrollField q)
axiom publicIH : ∀ p, H p
axiom ihAgreement : ∀ q, publicIH (unrollField q) = privateIH q
axiom minor : ∀ p, H p → C (publicCtor p)
axiom core : ∀ q, C (unroll q)
axiom constructorAgreement : ∀ q,
  publicCtor (unrollField q) = unroll (privateCtor q)
axiom coreIota : ∀ q, core (privateCtor q) =
  Eq.mp (congrArg C (constructorAgreement q))
    (minor (unrollField q) (privateIH q))

-- Lean 4.33.0's `linter.defProp` wants a `theorem` here, but `theorem` demands
-- the statement be written out and the point of this declaration is that the
-- statement is whatever `oneLayerRecursorCompatibility` says it is -- the
-- `run_meta` below reads it back with `inferType`.
set_option linter.defProp false in
def expected := InductiveModels.oneLayerRecursorCompatibility roll unroll unrollRoll
  rollField unrollField unrollRollField privateCtor publicCtor rollCtor
  privateIH publicIH ihAgreement minor core constructorAgreement coreIota

end OneLayerRecursorApplication

open Lean Meta InductiveModels

run_meta
  let arguments ← #[``OneLayerRecursorApplication.M,
    ``OneLayerRecursorApplication.P,
    ``OneLayerRecursorApplication.Q,
    ``OneLayerRecursorApplication.R,
    ``OneLayerRecursorApplication.C,
    ``OneLayerRecursorApplication.H,
    ``OneLayerRecursorApplication.roll,
    ``OneLayerRecursorApplication.unroll,
    ``OneLayerRecursorApplication.unrollRoll,
    ``OneLayerRecursorApplication.rollField,
    ``OneLayerRecursorApplication.unrollField,
    ``OneLayerRecursorApplication.unrollRollField,
    ``OneLayerRecursorApplication.privateCtor,
    ``OneLayerRecursorApplication.publicCtor,
    ``OneLayerRecursorApplication.rollCtor,
    ``OneLayerRecursorApplication.privateIH,
    ``OneLayerRecursorApplication.publicIH,
    ``OneLayerRecursorApplication.ihAgreement,
    ``OneLayerRecursorApplication.minor,
    ``OneLayerRecursorApplication.core,
    ``OneLayerRecursorApplication.constructorAgreement,
    ``OneLayerRecursorApplication.coreIota].mapM mkConstWithFreshMVarLevels
  let expected ← inferType (← mkConstWithFreshMVarLevels
    ``OneLayerRecursorApplication.expected)
  let result ← applyOneLayerCompatibility [.zero, .zero, .succ .zero, .succ .zero]
    arguments expected
  let proof ← match result with
    | .ok proof => pure proof
    | .error message => throwError "the embedded compatibility proof did not apply: {message}"
  check proof
