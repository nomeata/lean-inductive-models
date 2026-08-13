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
