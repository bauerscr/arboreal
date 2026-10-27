import Mathlib

/-!
# Shooting on a perturbed coordinate

`exists_eq_of_perturb`: let `g` be strictly increasing on an order-connected set `U` with
`g(U) = (0, ε)`, and let `f` be continuous on `U` with `|f - g| ≤ C g²` on `U`, `C ε ≤ 1/4`. Then
every `y ∈ (0, ε/2]` is a value of `f` on `U` (intermediate value theorem between the points
where `g = y/2` and `g = 3y/2`). Every solution `f(b) = y` has `|g(b) - y| ≤ 2 C y²`
(`g_near_of_eq`).

This is the abstract part of the shooting on the final coupling `ǧ_N` (`Step2/Flow/FlowComplete.lean`):
`g = ǧ_{N-2}` along the admissible flow, `f = ǧ_N`.
-/

open Set

namespace Flow2

/-- **Existence for the shooting on a perturbation `f` of a strictly increasing `g`.** -/
theorem exists_eq_of_perturb {U : Set ℝ} {g f : ℝ → ℝ} {ε C : ℝ} (hU : U.OrdConnected)
    (hmono : StrictMonoOn g U) (himg : g '' U = Ioo 0 ε) (hf : ContinuousOn f U)
    (hfg : ∀ b ∈ U, |f b - g b| ≤ C * g b ^ 2) (hC : 0 ≤ C) (hCε : C * ε ≤ 1 / 4) :
    ∀ y, 0 < y → y ≤ ε / 2 → ∃ b ∈ U, f b = y := by
  intro y hy hyε
  have hε : 0 < ε := by linarith
  have h1 : y / 2 ∈ g '' U := by rw [himg]; constructor <;> linarith
  have h2 : 3 * y / 2 ∈ g '' U := by rw [himg]; constructor <;> linarith
  obtain ⟨b₁, hb₁, hg₁⟩ := h1
  obtain ⟨b₂, hb₂, hg₂⟩ := h2
  have hlt : b₁ < b₂ := by
    by_contra hn
    push_neg at hn
    have := hmono.monotoneOn hb₂ hb₁ hn
    rw [hg₁, hg₂] at this
    linarith
  -- `f(b₁) < y < f(b₂)`
  have hf₁ : f b₁ ≤ y := by
    have := (abs_le.1 (hfg b₁ hb₁)).2
    rw [hg₁] at this
    have hc : C * (y / 2) ≤ 1 / 16 := by
      have := mul_le_mul_of_nonneg_left (show y / 2 ≤ ε / 4 by linarith) hC
      linarith
    have : C * (y / 2) ^ 2 ≤ 1 / 16 * (y / 2) := by
      rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (by linarith)
    linarith
  have hf₂ : y ≤ f b₂ := by
    have := (abs_le.1 (hfg b₂ hb₂)).1
    rw [hg₂] at this
    have hc : C * (3 * y / 2) ≤ 3 / 16 := by
      have := mul_le_mul_of_nonneg_left (show 3 * y / 2 ≤ 3 * ε / 4 by linarith) hC
      linarith
    have : C * (3 * y / 2) ^ 2 ≤ 3 / 16 * (3 * y / 2) := by
      rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (by linarith)
    linarith
  have hsub : Icc b₁ b₂ ⊆ U := hU.out hb₁ hb₂
  obtain ⟨b, hb, hfb⟩ := intermediate_value_Icc hlt.le (hf.mono hsub) ⟨hf₁, hf₂⟩
  exact ⟨b, hsub hb, hfb⟩

/-- **Solutions of the perturbed shooting are close to the unperturbed one**: if `f(b) = y`,
`|f - g| ≤ C g²` at `b`, `0 ≤ g(b)` and `C g(b) ≤ 1/4`, then `|g(b) - y| ≤ 2 C y²`. -/
theorem g_near_of_eq {gb y C : ℝ} (hC : 0 ≤ C) (hg0 : 0 ≤ gb) (hCg : C * gb ≤ 1 / 4)
    (h : |y - gb| ≤ C * gb ^ 2) : |gb - y| ≤ 2 * C * y ^ 2 := by
  rw [abs_sub_comm]
  have h1 := (abs_le.1 h).1
  have hq : C * gb ^ 2 ≤ gb / 4 := by
    have := mul_le_mul_of_nonneg_right hCg hg0
    nlinarith
  have hgb : gb ≤ 4 / 3 * y := by linarith
  refine h.trans ?_
  have hy : 0 ≤ y := by linarith
  have : gb ^ 2 ≤ (4 / 3 * y) ^ 2 := pow_le_pow_left₀ hg0 hgb 2
  nlinarith

end Flow2
