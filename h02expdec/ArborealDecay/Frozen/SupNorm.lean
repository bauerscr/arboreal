module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.supNorm`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- `‖z‖_∞` on `ℤ²`. -/
def supNorm (z : ℤ × ℤ) : ℤ := max |z.1| |z.2|

end ArborealDecay

end
