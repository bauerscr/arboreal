module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.IsTorusNN`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- Nearest neighbours in the torus `(ℤ/Lℤ)²`. -/
def IsTorusNN (L : ℕ) (x y : ZMod L × ZMod L) : Prop :=
  (x.1 = y.1 ∧ (x.2 - y.2 = 1 ∨ y.2 - x.2 = 1)) ∨ (x.2 = y.2 ∧ (x.1 - y.1 = 1 ∨ y.1 - x.1 = 1))

end ArborealDecay

end
