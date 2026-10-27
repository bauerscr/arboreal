module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.IsRealStable`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- Real stability: `p(z) ≠ 0` whenever `Im z_j > 0` for all `j`. -/
def IsRealStable {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ z : σ → ℂ, (∀ j, 0 < (z j).im) → MvPolynomial.aeval z p ≠ 0

end ArborealDecay

end
