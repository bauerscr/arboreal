-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.SupDist
public import ArborealDecay.Provider.SuperpolyFinite

/-!
# Frozen declaration `ArborealDecay.superpoly_finite`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- **Proposition `prop:superpoly`, finite subgraphs** (note L924–933). -/
theorem superpoly_finite (β : ℝ) (hβ : 0 ≤ β) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (W : EdgeWeights Λ),
        (∀ x y : Λ, W.w x y ≠ 0 → IsNN x y) →
        (∀ x y : Λ, W.w x y ≤ β) →
        ∀ x z : Λ, twoPoint W x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + supDist x z) ^ 2)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.superpoly_finite β hβ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
