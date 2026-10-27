module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.IsNN`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- Nearest neighbours in `ℤ²`. -/
def IsNN (x y : ℤ × ℤ) : Prop := |x.1 - y.1| + |x.2 - y.2| = 1

end ArborealDecay

end
