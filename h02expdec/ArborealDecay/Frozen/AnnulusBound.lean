-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.EdgeWeightsMap
public import ArborealDecay.Frozen.SupNorm
public import ArborealDecay.Frozen.AnnulusCollapse
public import ArborealDecay.Provider.AnnulusBound

/-!
# Frozen declaration `ArborealDecay.annulus_bound`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- **Proposition `prop:annulus`** (note L833–841): uniform over all nearest-neighbour
subgraphs of the annulus with weights at most `β`. -/
theorem annulus_bound (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
        (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * r) →
        ∀ W : EdgeWeights Λ,
          (∀ x y : Λ, W.w x y ≠ 0 → IsNN x y) →
          (∀ x y : Λ, W.w x y ≤ β) →
          twoPoint (W.map (annulusCollapse r Λ)) (Sum.inl false) (Sum.inl true) ≤
            C * (r : ℝ) ^ (-κ) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.annulus_bound β hβ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
