module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.IsTorusNN

/-!
# Frozen declaration `ArborealDecay.torusUniform`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

open Classical in
/-- The torus with constant weight `β` on every nearest-neighbour edge: `ℙ_{Λ_L,β}`. -/
noncomputable def torusUniform (L : ℕ) (β : ℝ) (hβ : 0 ≤ β) : EdgeWeights (ZMod L × ZMod L) where
  w x y := if IsTorusNN L x y then β else 0
  symm x y := by
    have h : IsTorusNN L x y ↔ IsTorusNN L y x := by
      unfold IsTorusNN
      constructor <;> rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩) <;> simp_all
    simp only [h]
  nonneg x y := by split_ifs <;> simp [hβ]

end ArborealDecay

end
