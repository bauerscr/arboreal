module

public import Mathlib
public import ArborealDecay.Frozen.SupNorm

/-!
# Frozen declaration `ArborealDecay.annulusCollapse`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- Wiring of the annulus `𝒜_r = {r ≤ ‖z‖_∞ ≤ 2r}`: the inner boundary becomes the terminal
`a = inl false`, the outer boundary the terminal `b = inl true` (note L824–831). -/
def annulusCollapse (r : ℤ) (Λ : Finset (ℤ × ℤ)) (z : Λ) : Bool ⊕ Λ :=
  if supNorm z = r then Sum.inl false else if supNorm z = 2 * r then Sum.inl true else Sum.inr z

end ArborealDecay

end
