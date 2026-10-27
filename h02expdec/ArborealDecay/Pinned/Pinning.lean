module

public import ArborealDecay.H02

/-!
# Pinning for general forms (supplement `lem:pinning`, ghost form)

For the graph `Λ ∪ {g}` (`Option Λ`, `g = none`) with weights `ghostW w h` (`w` on `Λ`, `h_i` on
`ig`) and **every** form `G ∈ Ω(Λ)` (embedded by `H02.emb`),
`[(1 - z_g) G]^{Λ∪g}_{ghostW w h, 0} = [ξ_g η_g G]^{Λ∪g}_{ghostW w h, 0} = [G]^Λ_{w,h}`.

No hypothesis on `G` (in particular no `T`-invariance, unlike `H02.expect_ghost`), and real
symmetric weights and real field.  The proof is the core of `H02.expect_ghost`:
`ξ_g η_g e^{-H^{Λ∪g}} = ξ_g η_g emb(e^{-H^Λ})` (`H02.ξη_mul_exp_ghost`) and
`[ξ_g η_g emb X]_0 = [X]_0` (`H02.int0_ξη_emb`).
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- **Pinning for general forms** (supplement `lem:pinning`, ghost form):
`[ξ_g η_g G]^{Λ∪g}_{ghostW w h, 0} = [G]^Λ_{w,h}` for every `G ∈ Ω(Λ)`. -/
theorem expect_ghost_pin {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ)
    (G : Grassmann Λ) :
    expect (ghostW w h) 0 (ξ (none : Option Λ) * η none * emb G) = expect w h G := by
  have hPc : ∀ X : Grassmann (Option Λ), ξ (none : Option Λ) * η none * X =
      X * (ξ none * η none) := fun X => mul_comm_of_even (inv'_ξη _ _) X
  have key : ξ (none : Option Λ) * η none * emb G *
        IsNilpotent.exp (-action (ghostW w h) (fun _ => 0)) =
      ξ none * η none * emb (G * IsNilpotent.exp (-action w h)) := by
    calc ξ (none : Option Λ) * η none * emb G *
          IsNilpotent.exp (-action (ghostW w h) (fun _ => 0))
        = emb G * (ξ none * η none * IsNilpotent.exp (-action (ghostW w h) (fun _ => 0))) := by
          rw [hPc (emb G), mul_assoc]
      _ = emb G * (ξ none * η none * emb (IsNilpotent.exp (-action w h))) := by
          rw [ξη_mul_exp_ghost hw h]
      _ = _ := by rw [← mul_assoc, ← hPc (emb G), mul_assoc, map_mul]
  show int0 (ξ (none : Option Λ) * η none * emb G *
    IsNilpotent.exp (-action (ghostW w h) (fun _ => 0))) = int0 _
  rw [key, int0_ξη_emb]

/-- `1 - z_g = ξ_g η_g`. -/
theorem one_sub_z {V : Type*} [DecidableEq V] (r : V) : 1 - z r = ξ r * η r := by
  simp [z]

/-- **Pinning for general forms**, the `(1 - z_g)` form. -/
theorem expect_ghost_pin_one_sub_z {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ)
    (G : Grassmann Λ) :
    expect (ghostW w h) 0 ((1 - z (none : Option Λ)) * emb G) = expect w h G := by
  rw [one_sub_z, expect_ghost_pin hw h]

end

end ArborealDecay.Pinned

end
