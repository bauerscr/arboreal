module

public import Mathlib
public import ArborealDecay.Gaussian.Basic

/-!
# Gaussian integrals with a linear term

Completing the square: `exp (-q(s)/2 + b ⬝ᵥ s) = exp (b ⬝ᵥ M⁻¹ b / 2) · exp (-q(s - M⁻¹ b)/2)`.
-/

open MeasureTheory Matrix Real

set_option linter.unusedSectionVars false

namespace ArborealDecay.Gaussian

public section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}

/-- Completing the square. -/
theorem exp_neg_half_quad_add_dotProduct (hM : M.PosDef) (b s : ι → ℝ) :
    Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s)
      = Real.exp ((1 / 2) * (b ⬝ᵥ M⁻¹ *ᵥ b)) *
        Real.exp (-(1 / 2) * ((s - M⁻¹ *ᵥ b) ⬝ᵥ M *ᵥ (s - M⁻¹ *ᵥ b))) := by
  have hsym : Mᵀ = M := by
    have := hM.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  set m : ι → ℝ := M⁻¹ *ᵥ b with hm
  have hMm : M *ᵥ m = b := by
    rw [hm, mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, one_mulVec]
  have h2 : m ⬝ᵥ M *ᵥ s = b ⬝ᵥ s := by
    have : m ᵥ* M = M *ᵥ m := by
      conv_lhs => rw [← hsym]
      exact vecMul_transpose M m
    rw [dotProduct_mulVec, this, hMm]
  have h3 : s ⬝ᵥ M *ᵥ m = b ⬝ᵥ s := by
    rw [hMm, dotProduct_comm]
  have h4 : m ⬝ᵥ M *ᵥ m = b ⬝ᵥ m := by
    rw [hMm, dotProduct_comm]
  rw [← Real.exp_add]
  congr 1
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct, h2, h3, h4]
  ring

private theorem shift_eq (hM : M.PosDef) (b : ι → ℝ) :
    (fun s : ι → ℝ => Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s))
      = fun s => Real.exp ((1 / 2) * (b ⬝ᵥ M⁻¹ *ᵥ b)) *
        (fun t : ι → ℝ => Real.exp (-(1 / 2) * (t ⬝ᵥ M *ᵥ t))) (s - M⁻¹ *ᵥ b) :=
  funext fun s => exp_neg_half_quad_add_dotProduct hM b s

/-- Integrability of the Gaussian weight with a linear term. -/
theorem integrable_exp_neg_half_quad_add_dotProduct (hM : M.PosDef) (b : ι → ℝ) :
    Integrable fun s : ι → ℝ => Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s) := by
  rw [shift_eq hM b]
  exact ((integrable_exp_neg_half_quad hM).comp_sub_right _).const_mul _

/-- `∫ exp (-q/2 + b ⬝ s) = (2π)^{|ι|/2} (det M)^{-1/2} exp (b ⬝ M⁻¹ b / 2)`. -/
theorem integral_exp_neg_half_quad_add_dotProduct (hM : M.PosDef) (b : ι → ℝ) :
    ∫ s : ι → ℝ, Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s)
      = Real.sqrt (2 * π) ^ Fintype.card ι / Real.sqrt M.det
        * Real.exp ((1 / 2) * (b ⬝ᵥ M⁻¹ *ᵥ b)) := by
  rw [shift_eq hM b, integral_const_mul,
    integral_sub_right_eq_self (fun t : ι → ℝ => Real.exp (-(1 / 2) * (t ⬝ᵥ M *ᵥ t))),
    integral_exp_neg_half_quad hM]
  ring

/-- `s_i · exp (-q/2 + b ⬝ s)` is integrable. -/
theorem integrable_coord_mul_exp_neg_half_quad_add_dotProduct (hM : M.PosDef)
    (b : ι → ℝ) (i : ι) :
    Integrable fun s : ι → ℝ => s i * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s) := by
  have h := ((integrable_coord_mul_exp_neg_half_quad hM i).add
    ((integrable_exp_neg_half_quad hM).const_mul ((M⁻¹ *ᵥ b) i))).comp_sub_right (M⁻¹ *ᵥ b)
  have h2 := h.const_mul (Real.exp ((1 / 2) * (b ⬝ᵥ M⁻¹ *ᵥ b)))
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [exp_neg_half_quad_add_dotProduct hM b s]
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- `s_i s_j · exp (-q/2 + b ⬝ s)` is integrable. -/
theorem integrable_coord_mul_coord_mul_exp_neg_half_quad_add_dotProduct (hM : M.PosDef)
    (b : ι → ℝ) (i j : ι) :
    Integrable fun s : ι → ℝ =>
      s i * s j * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s) := by
  set m := M⁻¹ *ᵥ b
  have h := (((integrable_coord_mul_coord_mul_exp_neg_half_quad hM i j).add
    ((integrable_coord_mul_exp_neg_half_quad hM i).const_mul (m j))).add
    ((integrable_coord_mul_exp_neg_half_quad hM j).const_mul (m i))).add
    ((integrable_exp_neg_half_quad hM).const_mul (m i * m j))
  have h2 := (h.comp_sub_right m).const_mul (Real.exp ((1 / 2) * (b ⬝ᵥ M⁻¹ *ᵥ b)))
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [exp_neg_half_quad_add_dotProduct hM b s]
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

private theorem dot_mul_eq (c s : ι → ℝ) (e : ℝ) :
    (c ⬝ᵥ s) * e = ∑ i, c i * (s i * e) := by
  simp only [dotProduct, Finset.sum_mul, mul_assoc]

private theorem quad_mul_eq (d : Matrix ι ι ℝ) (s : ι → ℝ) (e : ℝ) :
    (s ⬝ᵥ d *ᵥ s) * e = ∑ i, ∑ j, d i j * (s i * s j * e) := by
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Polynomials of degree at most two times the Gaussian weight with linear term are integrable. -/
theorem integrable_quadPoly_mul_exp_neg_half_quad_add_dotProduct (hM : M.PosDef)
    (b : ι → ℝ) (a : ℝ) (c : ι → ℝ) (d : Matrix ι ι ℝ) :
    Integrable fun s : ι → ℝ =>
      (a + c ⬝ᵥ s + s ⬝ᵥ d *ᵥ s) * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s) := by
  have h0 := integrable_exp_neg_half_quad_add_dotProduct hM b
  have h1 : Integrable fun s : ι → ℝ =>
      (c ⬝ᵥ s) * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s) := by
    simp only [dot_mul_eq]
    exact integrable_finsetSum _ fun i _ =>
      (integrable_coord_mul_exp_neg_half_quad_add_dotProduct hM b i).const_mul (c i)
  have h2 : Integrable fun s : ι → ℝ =>
      (s ⬝ᵥ d *ᵥ s) * Real.exp (-(1 / 2) * (s ⬝ᵥ M *ᵥ s) + b ⬝ᵥ s) := by
    simp only [quad_mul_eq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_coord_mul_coord_mul_exp_neg_half_quad_add_dotProduct hM b i j).const_mul (d i j)
  have := ((h0.const_mul a).add h1).add h2
  refine this.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply]
  ring

end

end ArborealDecay.Gaussian
