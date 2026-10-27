module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.torusEuclNorm`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- The toroidal Euclidean distance from `0`. -/
noncomputable def torusEuclNorm (L : ℕ) (x : ZMod L × ZMod L) : ℝ :=
  Real.sqrt ((x.1.valMinAbs : ℝ) ^ 2 + (x.2.valMinAbs : ℝ) ^ 2)

end ArborealDecay

end
