-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsTorusNN
public import ArborealDecay.Frozen.TorusSupDist
public import ArborealDecay.Provider.ExpDecayTorus

/-!
# Frozen declaration `ArborealDecay.expDecay_torus`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- **Theorem `thm:main`, torus** (note L88–89). -/
theorem expDecay_torus (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (W : EdgeWeights (ZMod L × ZMod L)),
        (∀ x y, W.w x y ≠ 0 → IsTorusNN L x y) →
        (∀ x y, W.w x y ≤ β) →
        ∀ x y, twoPoint W x y ≤ 2 * Real.exp (-c * torusSupDist L x y) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.expDecay_torus β hβ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
