-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsTorusNN
public import ArborealDecay.Frozen.TorusSupDist
public import ArborealDecay.Provider.SuperpolyTorus

/-!
# Frozen declaration `ArborealDecay.superpoly_torus`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- **Proposition `prop:superpoly`, torus** (note L934). -/
theorem superpoly_torus (β : ℝ) (hβ : 0 ≤ β) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (L : ℕ) [NeZero L] (W : EdgeWeights (ZMod L × ZMod L)),
        (∀ x y, W.w x y ≠ 0 → IsTorusNN L x y) →
        (∀ x y, W.w x y ≤ β) →
        ∀ x z, twoPoint W x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + torusSupDist L x z) ^ 2)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.superpoly_torus β hβ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
