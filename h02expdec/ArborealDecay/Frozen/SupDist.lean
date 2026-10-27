module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.supDist`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- The `ℓ^∞` distance on `ℤ²`. -/
def supDist (x y : ℤ × ℤ) : ℤ := max |x.1 - y.1| |x.2 - y.2|

end ArborealDecay

end
