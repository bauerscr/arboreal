module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.torusSupDist`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- The toroidal `ℓ^∞` distance. -/
def torusSupDist (L : ℕ) (x y : ZMod L × ZMod L) : ℕ :=
  max (x.1 - y.1).valMinAbs.natAbs (x.2 - y.2).valMinAbs.natAbs

end ArborealDecay

end
