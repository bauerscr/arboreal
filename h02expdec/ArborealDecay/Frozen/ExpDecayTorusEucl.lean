-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.TorusUniform
public import ArborealDecay.Frozen.TorusEuclNorm
public import ArborealDecay.Provider.ExpDecayTorusEucl

/-!
# Frozen declaration `ArborealDecay.expDecay_torus_eucl`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- **Theorem `thm:main`, Euclidean consequence** (note L89–93): uniform in `L`. -/
theorem expDecay_torus_eucl (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (x : ZMod L × ZMod L),
        twoPoint (torusUniform L β hβ) 0 x ≤ C * Real.exp (-c * torusEuclNorm L x) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.expDecay_torus_eucl β hβ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
