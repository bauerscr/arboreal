module

public import Mathlib

/-!
# Inverses of positive definite `Z`-matrices are entrywise nonnegative

If `A` is real positive definite with `A i j ≤ 0` for `i ≠ j`, then `A⁻¹ i j ≥ 0`.

Proof: let `y = A⁻¹ e_j` and `x = min(y, 0)`, `p = max(y, 0)`. Then `x ⬝ A p ≥ 0` (sign pattern),
so `x ⬝ A x = x ⬝ A y - x ⬝ A p ≤ x_j ≤ 0`, and positive definiteness forces `x = 0`.
-/

open Matrix

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem inv_apply_nonneg_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (i j : n) : 0 ≤ A⁻¹ i j := by
  set y : n → ℝ := A⁻¹ *ᵥ Pi.single j 1 with hy
  have hu : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA.isUnit
  have hAy : A *ᵥ y = Pi.single j 1 := by
    rw [hy, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  set x : n → ℝ := fun k => min (y k) 0
  set p : n → ℝ := fun k => max (y k) 0
  have hyxp : y = x + p := by
    funext k; simp only [Pi.add_apply, x, p]; rw [min_add_max, add_zero]
  have hxp : 0 ≤ x ⬝ᵥ (A *ᵥ p) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => ?_
    by_cases hkl : k = l
    · subst hkl
      have : x k * p k = 0 := by
        simp only [x, p]
        rcases le_total (y k) 0 with h | h
        · rw [max_eq_right h]; ring
        · rw [min_eq_right h]; ring
      calc (0 : ℝ) = A k k * (x k * p k) := by rw [this, mul_zero]
        _ = x k * (A k k * p k) := by ring
        _ ≤ x k * (A k k * p k) := le_rfl
    · have hx : x k ≤ 0 := min_le_right _ _
      have hp : 0 ≤ p l := le_max_right _ _
      have hA' := hoff k l hkl
      have : 0 ≤ x k * A k l := mul_nonneg_of_nonpos_of_nonpos hx hA'
      calc (0 : ℝ) ≤ x k * A k l * p l := mul_nonneg this hp
        _ = x k * (A k l * p l) := by ring
  have hxy : x ⬝ᵥ (A *ᵥ y) = x j := by
    rw [hAy, dotProduct_single, mul_one]
  have hxx : x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
    have e : x ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ (A *ᵥ x) + x ⬝ᵥ (A *ᵥ p) := by
      rw [hyxp, mulVec_add, dotProduct_add]
    have hxj : x j ≤ 0 := min_le_right _ _
    linarith
  have hx0 : x = 0 := by
    by_contra hne
    have := hA.dotProduct_mulVec_pos hne
    rw [star_trivial] at this
    linarith
  have hyi : 0 ≤ y i := by
    have := congr_fun hx0 i
    simp only [x, Pi.zero_apply] at this
    by_contra h
    push Not at h
    rw [min_eq_left h.le] at this
    linarith
  have : y i = A⁻¹ i j := by
    simp [hy]
  rw [← this]; exact hyi

end ArborealDecay.Annulus
