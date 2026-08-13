import Lean

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
  intro publicRec p
  unfold publicRec
  -- Eliminate only the public endpoint while `q` and its private recursive
  -- result `ih` remain fixed.
  have compat (q r : M) (p : P) (hp : unroll q = p)
      (hc : r = privateCtor q) (hout : unroll r = publicCtor p) :
      Eq.mp (congrArg C hout) (core r) =
        minor p (Eq.mp (congrArg C hp) (core q)) := by
    subst r
    subst p
    simp [coreIota]
  exact compat (roll p) (roll (publicCtor p)) p (unrollRoll p)
    (rollCtor p) (unrollRoll (publicCtor p))

end OneLayerRecursorProof
