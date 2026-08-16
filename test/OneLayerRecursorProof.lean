import InductiveModels.OneLayer

/-! A handwritten oracle for the equality bookkeeping used by the generated
one-layer public recursor.

The generator never applies a lemma stated at the owner's arity — there is no
such lemma to state, because `n` recursive fields need `n` independent field
universes.  It builds the ι proof out of [`InductiveModels.oneLayerFieldStep`]
and [`InductiveModels.oneLayerTransportCancel`], one step per field over one
cancellation.  This file is the compile-time witness that the assembly is
sound at an arity no fixed-arity lemma reaches: `three` is the statement the
old two-field oracle could not carry, proved here by exactly the chain the
generator builds, and the `run_meta` block below applies the same two embedded
proofs the generator instantiates. -/

universe u v w

namespace OneLayerRecursorProof

open InductiveModels

/-- The three-recursive-field ι rule, from the two fixed-arity lemmas alone.
`roll (publicCtor p⃗) ≡ privateCtor (rollField⃗ p⃗)` is definitional for the
generated declarations, so it is discharged here by taking the private major
as given. -/
theorem three
    {M P : Type u} {Q₁ R₁ Q₂ R₂ Q₃ R₃ : Type w} {C : P → Sort v}
    {H₁ : R₁ → Sort v} {H₂ : R₂ → Sort v} {H₃ : R₃ → Sort v}
    (unroll : M → P)
    (rollField₁ : R₁ → Q₁) (unrollField₁ : Q₁ → R₁)
    (unrollRollField₁ : ∀ p, unrollField₁ (rollField₁ p) = p)
    (rollField₂ : R₂ → Q₂) (unrollField₂ : Q₂ → R₂)
    (unrollRollField₂ : ∀ p, unrollField₂ (rollField₂ p) = p)
    (rollField₃ : R₃ → Q₃) (unrollField₃ : Q₃ → R₃)
    (unrollRollField₃ : ∀ p, unrollField₃ (rollField₃ p) = p)
    (privateCtor : Q₁ → Q₂ → Q₃ → M) (publicCtor : R₁ → R₂ → R₃ → P)
    (privateIH₁ : ∀ q, H₁ (unrollField₁ q)) (publicIH₁ : ∀ p, H₁ p)
    (ihAgreement₁ : ∀ q, publicIH₁ (unrollField₁ q) = privateIH₁ q)
    (privateIH₂ : ∀ q, H₂ (unrollField₂ q)) (publicIH₂ : ∀ p, H₂ p)
    (ihAgreement₂ : ∀ q, publicIH₂ (unrollField₂ q) = privateIH₂ q)
    (privateIH₃ : ∀ q, H₃ (unrollField₃ q)) (publicIH₃ : ∀ p, H₃ p)
    (ihAgreement₃ : ∀ q, publicIH₃ (unrollField₃ q) = privateIH₃ q)
    (minor : ∀ p₁ p₂ p₃, H₁ p₁ → H₂ p₂ → H₃ p₃ → C (publicCtor p₁ p₂ p₃))
    (core : ∀ q, C (unroll q))
    (constructorAgreement : ∀ q₁ q₂ q₃,
      publicCtor (unrollField₁ q₁) (unrollField₂ q₂) (unrollField₃ q₃) =
        unroll (privateCtor q₁ q₂ q₃))
    (coreIota : ∀ q₁ q₂ q₃, core (privateCtor q₁ q₂ q₃) =
      Eq.mp (congrArg C (constructorAgreement q₁ q₂ q₃))
        (minor (unrollField₁ q₁) (unrollField₂ q₂) (unrollField₃ q₃)
          (privateIH₁ q₁) (privateIH₂ q₂) (privateIH₃ q₃)))
    (p₁ : R₁) (p₂ : R₂) (p₃ : R₃)
    (roundTripMajor :
      unroll (privateCtor (rollField₁ p₁) (rollField₂ p₂) (rollField₃ p₃)) =
        publicCtor p₁ p₂ p₃) :
    Eq.mp (congrArg C roundTripMajor)
        (core (privateCtor (rollField₁ p₁) (rollField₂ p₂) (rollField₃ p₃))) =
      minor p₁ p₂ p₃ (publicIH₁ p₁) (publicIH₂ p₂) (publicIH₃ p₃) := by
  let q₁ := rollField₁ p₁
  let q₂ := rollField₂ p₂
  let q₃ := rollField₃ p₃
  let m₁ := unrollField₁ q₁
  let m₂ := unrollField₂ q₂
  let m₃ := unrollField₃ q₃
  let result : ∀ x₁ x₂ x₃, C (publicCtor x₁ x₂ x₃) :=
    fun x₁ x₂ x₃ => minor x₁ x₂ x₃ (publicIH₁ x₁) (publicIH₂ x₂) (publicIH₃ x₃)
  let agreement := constructorAgreement q₁ q₂ q₃
  let source := unroll (privateCtor q₁ q₂ q₃)
  let value : C source := Eq.mp (congrArg C agreement) (result m₁ m₂ m₃)
  -- The chain: one cancellation, then one step per recursive field.
  let chain₀ := oneLayerTransportCancel _ _ agreement (result m₁ m₂ m₃)
  let chain₁ := oneLayerFieldStep source value
    (fun x => publicCtor x m₂ m₃) (fun x => result x m₂ m₃) _ _
    (unrollRollField₁ p₁) chain₀
  let chain₂ := oneLayerFieldStep source value
    (fun x => publicCtor p₁ x m₃) (fun x => result p₁ x m₃) _ _
    (unrollRollField₂ p₂) chain₁
  let chain₃ := oneLayerFieldStep source value
    (fun x => publicCtor p₁ p₂ x) (fun x => result p₁ p₂ x) _ _
    (unrollRollField₃ p₃) chain₂
  -- The bridge: the private ι rule, then one congruence per hypothesis.
  have bridge : core (privateCtor q₁ q₂ q₃) = value := by
    refine Eq.trans (coreIota q₁ q₂ q₃) ?_
    refine congrArg (Eq.mp (congrArg C agreement)) ?_
    show minor m₁ m₂ m₃ (privateIH₁ q₁) (privateIH₂ q₂) (privateIH₃ q₃) =
      minor m₁ m₂ m₃ (publicIH₁ m₁) (publicIH₂ m₂) (publicIH₃ m₃)
    rw [ihAgreement₁ q₁, ihAgreement₂ q₂, ihAgreement₃ q₃]
  rw [bridge]
  exact chain₃ roundTripMajor

end OneLayerRecursorProof

namespace OneLayerRecursorApplication

axiom P : Type
axiom A : Type
axiom C : P → Sort 1
axiom source : P
axiom target : P
axiom equality : source = target
axiom value : C source
axiom layer : A → P
axiom result : (x : A) → C (layer x)
axiom before : A
axiom after : A
axiom roundTrip : before = after
axiom previous : ∀ path : source = layer before,
  Eq.mp (congrArg C path) value = result before

-- Lean 4.33.0's `linter.defProp` wants a `theorem` here, but `theorem` demands
-- the statement be written out and the point of these two declarations is that
-- the statement is whatever the lemma says it is -- the `run_meta` below reads
-- both back with `inferType`.
set_option linter.defProp false in
def expectedCancel := InductiveModels.oneLayerTransportCancel source target equality value

set_option linter.defProp false in
def expectedStep := InductiveModels.oneLayerFieldStep source value layer result
  before after roundTrip previous

end OneLayerRecursorApplication

open Lean Meta InductiveModels

/- The generator instantiates the *embedded* copies of both lemmas by level
   name and applies them by position.  Check that the copies really are the
   theorems above, at the argument order and universe order the generator
   uses. -/
run_meta do
  let constant := fun (name : Name) => mkConstWithFreshMVarLevels name
  let cancelArguments ← #[``OneLayerRecursorApplication.P,
    ``OneLayerRecursorApplication.C,
    ``OneLayerRecursorApplication.source,
    ``OneLayerRecursorApplication.target,
    ``OneLayerRecursorApplication.equality,
    ``OneLayerRecursorApplication.value].mapM constant
  let cancel := mkAppN (oneLayerTransportCancelAt (.succ .zero) (.succ .zero))
    cancelArguments
  let expectedCancel ← inferType (← constant ``OneLayerRecursorApplication.expectedCancel)
  match ← checkOneLayerCompatibility "embedded cancel" cancel expectedCancel with
  | .ok _ => pure ()
  | .error message => throwError "the embedded cancellation did not apply: {message}"
  let stepArguments ← #[``OneLayerRecursorApplication.P,
    ``OneLayerRecursorApplication.C,
    ``OneLayerRecursorApplication.A,
    ``OneLayerRecursorApplication.source,
    ``OneLayerRecursorApplication.value,
    ``OneLayerRecursorApplication.layer,
    ``OneLayerRecursorApplication.result,
    ``OneLayerRecursorApplication.before,
    ``OneLayerRecursorApplication.after,
    ``OneLayerRecursorApplication.roundTrip,
    ``OneLayerRecursorApplication.previous].mapM constant
  let step := mkAppN
    (oneLayerFieldStepAt (.succ .zero) (.succ .zero) (.succ .zero)) stepArguments
  let expectedStep ← inferType (← constant ``OneLayerRecursorApplication.expectedStep)
  match ← checkOneLayerCompatibility "embedded step" step expectedStep with
  | .ok _ => pure ()
  | .error message => throwError "the embedded field step did not apply: {message}"
