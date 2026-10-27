module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.sMonomial`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- The exponent of the monomial `s_1 ⋯ s_m` in the variables `Fin 2 ⊕ ι`. -/
noncomputable def sMonomial (ι : Type*) [Fintype ι] : Fin 2 ⊕ ι →₀ ℕ :=
  ∑ k, Finsupp.single (Sum.inr k) 1

end ArborealDecay

end
