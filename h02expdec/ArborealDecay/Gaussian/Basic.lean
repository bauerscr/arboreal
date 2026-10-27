module

public import Mathlib
public import ArborealDecay.Gaussian.Standard
public import ArborealDecay.Gaussian.Linear

/-!
# Gaussian integrals for a positive definite quadratic form

For `M` a positive definite real matrix, `q(s) = s ⬝ᵥ M *ᵥ s`: integrability, normalization
and the covariance formula for `exp (-q/2)` on `ι → ℝ`. We factor `M = Bᵀ B` with `B`
invertible (`B` the matrix square root), change variables `u = B s` and reduce to the
standard Gaussian.
-/

open MeasureTheory Matrix MatrixOrder Real

set_option linter.unusedSectionVars false

namespace ArborealDecay.Gaussian

public section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive definite real matrix factors as `Bᵀ B` with `B` invertible. -/
theorem exists_transpose_mul_self (M : Matrix ι ι ℝ) (hM : M.PosDef) :
    ∃ B : Matrix ι ι ℝ, M = Bᵀ * B ∧ B.det ≠ 0 := by
  have h0 : (0 : Matrix ι ι ℝ) ≤ M := hM.posSemidef.nonneg
  have hB : M = (CFC.sqrt M)ᵀ * CFC.sqrt M := by
    have h1 : (CFC.sqrt M)ᴴ = CFC.sqrt M := (CFC.sqrt_nonneg M).posSemidef.isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    rw [h1]
    exact (CFC.sqrt_mul_sqrt_self M h0).symm
  refine ⟨CFC.sqrt M, hB, fun h => ?_⟩
  have := hM.det_pos
  rw [hB, det_mul, det_transpose, h] at this
  simp at this

section Factored

variable {M B : Matrix ι ι ℝ} (hMB : M = Bᵀ * B) (hdet : B.det ≠ 0)
include hMB hdet

private theorem mulVec_inv_mulVec (u : ι → ℝ) : B *ᵥ (B⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]

private theorem inv_mulVec_mulVec (u : ι → ℝ) : B⁻¹ *ᵥ (B *ᵥ u) = u := by
  rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]

private theorem quad_eq (s : ι → ℝ) : s ⬝ᵥ M *ᵥ s = ∑ i, (B *ᵥ s) i ^ 2 := by
  rw [hMB, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp [dotProduct, pow_two]

private theorem weight_inv (u : ι → ℝ) :
    Real.exp (-(1 / 2) * ((B⁻¹ *ᵥ u) ⬝ᵥ M *ᵥ (B⁻¹ *ᵥ u))) = stdWeight u := by
  rw [quad_eq hMB hdet, mulVec_inv_mulVec hMB hdet]; rfl

private theorem integral_transfer (F : (ι → ℝ) → ℝ) :
    ∫ s, F s = |B.det|⁻¹ * ∫ u, F (B⁻¹ *ᵥ u) := by
  have := integral_comp_mulVec B hdet (fun u => F (B⁻¹ *ᵥ u))
  simpa only [inv_mulVec_mulVec hMB hdet] using this

private theorem integrable_transfer (F : (ι → ℝ) → ℝ) :
    Integrable F ↔ Integrable (fun u => F (B⁻¹ *ᵥ u)) := by
  have := integrable_comp_mulVec_iff B hdet (fun u => F (B⁻¹ *ᵥ u))
  simpa only [inv_mulVec_mulVec hMB hdet] using this

private theorem coord_expand (i j : ι) (u : ι → ℝ) :
    (B⁻¹ *ᵥ u) i * (B⁻¹ *ᵥ u) j * stdWeight u
      = ∑ k, ∑ l, B⁻¹ i k * B⁻¹ j l * (u k * u l * stdWeight u) := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

private theorem coord_expand1 (i : ι) (u : ι → ℝ) :
    (B⁻¹ *ᵥ u) i * stdWeight u = ∑ k, B⁻¹ i k * (u k * stdWeight u) := by
  simp only [mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem integrable_exp_neg_half_quad_of_factor :
    Integrable fun s : ι → ℝ => Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  rw [integrable_transfer hMB hdet]
  simp only [weight_inv hMB hdet]
  exact integrable_stdWeight

theorem integrable_coord_of_factor (i : ι) :
    Integrable fun s : ι → ℝ => s i * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  rw [integrable_transfer hMB hdet]
  simp only [weight_inv hMB hdet, coord_expand1 hMB hdet]
  exact integrable_finsetSum _ fun k _ =>
    (integrable_coord_mul_stdWeight k).const_mul _

theorem integrable_coord_mul_coord_of_factor (i j : ι) :
    Integrable fun s : ι → ℝ => s i * s j * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  rw [integrable_transfer hMB hdet]
  simp only [weight_inv hMB hdet, coord_expand hMB hdet]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrable_coord_mul_coord_mul_stdWeight k l).const_mul _

theorem integral_exp_neg_half_quad_of_factor :
    ∫ s : ι → ℝ, Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s))
      = |B.det|⁻¹ * Real.sqrt (2 * π) ^ Fintype.card ι := by
  rw [integral_transfer hMB hdet]
  simp only [weight_inv hMB hdet]
  rw [integral_stdWeight]

theorem integral_coord_mul_coord_of_factor (i j : ι) :
    ∫ s : ι → ℝ, s i * s j * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s))
      = M⁻¹ i j * ∫ s : ι → ℝ, Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  rw [integral_transfer hMB hdet, integral_exp_neg_half_quad_of_factor hMB hdet]
  simp only [weight_inv hMB hdet, coord_expand hMB hdet]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrable_coord_mul_coord_mul_stdWeight k l).const_mul _]
  have h1 : ∀ k, ∫ u : ι → ℝ, ∑ l, B⁻¹ i k * B⁻¹ j l * (u k * u l * stdWeight u)
      = ∑ l, B⁻¹ i k * B⁻¹ j l *
        (if k = l then Real.sqrt (2 * π) ^ Fintype.card ι else 0) := by
    intro k
    rw [integral_finsetSum _ fun l _ => (integrable_coord_mul_coord_mul_stdWeight k l).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_coord_mul_coord_mul_stdWeight]
  simp only [h1]
  have hinv : M⁻¹ = B⁻¹ * (B⁻¹)ᵀ := by
    rw [hMB, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  rw [hinv]
  simp only [mul_apply, transpose_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [← Finset.sum_mul]
  ring

end Factored

variable {M : Matrix ι ι ℝ}

theorem det_sqrt_eq_abs {B : Matrix ι ι ℝ} (hMB : M = Bᵀ * B) :
    Real.sqrt M.det = |B.det| := by
  rw [hMB, det_mul, det_transpose, ← sq, Real.sqrt_sq_eq_abs]

/-- Integrability of the Gaussian weight. -/
theorem integrable_exp_neg_half_quad (hM : M.PosDef) :
    Integrable fun s : ι → ℝ => Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  obtain ⟨B, hMB, hdet⟩ := exists_transpose_mul_self M hM
  exact integrable_exp_neg_half_quad_of_factor hMB hdet

theorem integrable_coord_mul_exp_neg_half_quad (hM : M.PosDef) (i : ι) :
    Integrable fun s : ι → ℝ => s i * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  obtain ⟨B, hMB, hdet⟩ := exists_transpose_mul_self M hM
  exact integrable_coord_of_factor hMB hdet i

theorem integrable_coord_mul_coord_mul_exp_neg_half_quad (hM : M.PosDef) (i j : ι) :
    Integrable fun s : ι → ℝ => s i * s j * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  obtain ⟨B, hMB, hdet⟩ := exists_transpose_mul_self M hM
  exact integrable_coord_mul_coord_of_factor hMB hdet i j

/-- `∫ exp (-q/2) = (2π)^{|ι|/2} (det M)^{-1/2}`. -/
theorem integral_exp_neg_half_quad (hM : M.PosDef) :
    ∫ s : ι → ℝ, Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s))
      = Real.sqrt (2 * π) ^ Fintype.card ι / Real.sqrt M.det := by
  obtain ⟨B, hMB, hdet⟩ := exists_transpose_mul_self M hM
  rw [integral_exp_neg_half_quad_of_factor hMB hdet, det_sqrt_eq_abs hMB]
  ring

/-- Covariance: `∫ s_i s_j exp (-q/2) = (M⁻¹)_{ij} ∫ exp (-q/2)`. -/
theorem integral_coord_mul_coord_mul_exp_neg_half_quad (hM : M.PosDef) (i j : ι) :
    ∫ s : ι → ℝ, s i * s j * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s))
      = M⁻¹ i j * ∫ s : ι → ℝ, Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s)) := by
  obtain ⟨B, hMB, hdet⟩ := exists_transpose_mul_self M hM
  exact integral_coord_mul_coord_of_factor hMB hdet i j

end

end ArborealDecay.Gaussian
