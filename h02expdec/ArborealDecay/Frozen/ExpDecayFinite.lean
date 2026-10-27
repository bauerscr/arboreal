-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.SupDist
public import ArborealDecay.Provider.ExpDecayFinite

/-!
# Frozen declaration `ArborealDecay.expDecay_finite`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- **Theorem `thm:main`, finite subgraphs of `ℤ²`** (note L81–87). -/
theorem expDecay_finite (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (W : EdgeWeights Λ),
        (∀ x y : Λ, W.w x y ≠ 0 → IsNN x y) →
        (∀ x y : Λ, W.w x y ≤ β) →
        ∀ x y : Λ, twoPoint W x y ≤ 2 * Real.exp (-c * supDist x y) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.expDecay_finite β hβ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
