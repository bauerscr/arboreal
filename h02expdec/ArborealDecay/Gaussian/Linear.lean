module

public import Mathlib

/-!
# Linear change of variables on `ι → ℝ`
-/

open MeasureTheory Matrix

namespace ArborealDecay.Gaussian

public section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `mulVec` by an invertible real matrix as a measurable equivalence. -/
@[expose] noncomputable def mulVecEquiv (B : Matrix ι ι ℝ) (hB : B.det ≠ 0) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  ((Matrix.toLinearEquiv' B this).toContinuousLinearEquiv).toHomeomorph.toMeasurableEquiv

theorem mulVecEquiv_apply (B : Matrix ι ι ℝ) (hB : B.det ≠ 0) (s : ι → ℝ) :
    mulVecEquiv B hB s = B *ᵥ s := rfl

theorem map_mulVecEquiv (B : Matrix ι ι ℝ) (hB : B.det ≠ 0) :
    Measure.map (mulVecEquiv B hB) (volume : Measure (ι → ℝ))
      = ENNReal.ofReal (abs B.det⁻¹) • volume :=
  Real.map_matrix_volume_pi_eq_smul_volume_pi hB

theorem integral_comp_mulVec (B : Matrix ι ι ℝ) (hB : B.det ≠ 0) (f : (ι → ℝ) → ℝ) :
    ∫ s, f (B *ᵥ s) = |B.det|⁻¹ * ∫ u, f u := by
  have h := integral_map_equiv (μ := (volume : Measure (ι → ℝ))) (mulVecEquiv B hB) f
  simp only [mulVecEquiv_apply] at h
  rw [← h, map_mulVecEquiv, integral_smul_measure]
  simp [abs_inv, ENNReal.toReal_ofReal, abs_nonneg]

theorem integrable_comp_mulVec_iff (B : Matrix ι ι ℝ) (hB : B.det ≠ 0) (f : (ι → ℝ) → ℝ) :
    Integrable (fun s => f (B *ᵥ s)) ↔ Integrable f := by
  have h := integrable_map_equiv (μ := (volume : Measure (ι → ℝ))) (mulVecEquiv B hB) f
  have h0 : B.det⁻¹ ≠ 0 := inv_ne_zero hB
  rw [map_mulVecEquiv] at h
  have h1 : Integrable f (ENNReal.ofReal (abs B.det⁻¹) • (volume : Measure (ι → ℝ))) ↔
      Integrable f volume :=
    integrable_smul_measure (by simpa using h0) ENNReal.ofReal_ne_top
  rw [h1] at h
  exact h.symm

end

end ArborealDecay.Gaussian
