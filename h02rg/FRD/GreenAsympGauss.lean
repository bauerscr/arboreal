import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The continuum heat kernel and the constant `c_d` (for eq:LapZd)

* `cd d = Γ(d/2 - 1) / (4 π^{d/2})`;
* `pbar d R t = (4πt)^{-d/2} e^{-R/(4t)}` (with `R = |x|²`);
* `integral_pbar`: `∫_0^∞ pbar d R t dt = cd d * R^{1 - d/2}` for `R > 0`, `d ≥ 3`.
-/

namespace FRD.GreenAsymp

noncomputable section

open MeasureTheory Set

/-- The continuum constant `c_d = Γ(d/2 - 1) / (4 π^{d/2})`. -/
def cd (d : ℕ) : ℝ := Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2))

theorem cd_pos {d : ℕ} (hd : 3 ≤ d) : 0 < cd d := by
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold cd
  have := Real.pi_pos
  exact div_pos (Real.Gamma_pos_of_pos (by linarith)) (by positivity)

/-- The continuum heat kernel `(4πt)^{-d/2} e^{-R/(4t)}`. -/
def pbar (d : ℕ) (R t : ℝ) : ℝ := Real.exp (-R / (4 * t)) / Real.sqrt (4 * Real.pi * t) ^ d

theorem pbar_nonneg (d : ℕ) (R t : ℝ) : 0 ≤ pbar d R t :=
  div_nonneg (Real.exp_pos _).le (pow_nonneg (Real.sqrt_nonneg _) _)

theorem sqrt_pow_eq_rpow {y : ℝ} (hy : 0 ≤ y) (d : ℕ) : Real.sqrt y ^ d = y ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hy]; congr 1; ring

theorem pbar_comp_inv (d : ℕ) (R : ℝ) {x : ℝ} (hx : 0 < x) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • pbar d R (x ^ (-1 : ℝ)) =
      (4 * Real.pi) ^ (-((d : ℝ) / 2)) *
        (x ^ (((d : ℝ) / 2 - 1) - 1) * Real.exp (-(R / 4 * x))) := by
  have hpi := Real.pi_pos
  rw [Real.rpow_neg_one, smul_eq_mul, abs_neg, abs_one, one_mul, pbar,
    sqrt_pow_eq_rpow (by positivity), Real.mul_rpow (by positivity) (by positivity),
    Real.inv_rpow hx.le]
  have e1 : -R / (4 * x⁻¹) = -(R / 4 * x) := by field_simp
  rw [e1]
  have e2 : x ^ ((d : ℝ) / 2 - 1 - 1) = x ^ ((-1 : ℝ) - 1) * x ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [e2, Real.rpow_neg (by positivity)]
  have : 0 < x ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have : 0 < (4 * Real.pi) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  field_simp

theorem integral_Gamma_kernel {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) ∧
      ∫ x in Ioi 0, x ^ (a - 1) * Real.exp (-(r * x)) = (1 / r) ^ a * Real.Gamma a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  refine ⟨?_, h⟩
  by_contra hc
  rw [integral_undef hc] at h
  have : 0 < (1 / r) ^ a * Real.Gamma a :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos ha)
  linarith

/-- `∫_0^∞ (4πt)^{-d/2} e^{-R/(4t)} dt = c_d R^{1-d/2}`. -/
theorem integral_pbar {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (pbar d R) (Ioi 0) ∧ ∫ t in Ioi 0, pbar d R t = cd d * R ^ (1 - (d : ℝ) / 2) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have ha : 0 < (d : ℝ) / 2 - 1 := by linarith
  have hr : 0 < R / 4 := by positivity
  obtain ⟨hint, hval⟩ := integral_Gamma_kernel ha hr
  have hcongr : EqOn (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • pbar d R (x ^ (-1 : ℝ)))
      (fun x => (4 * Real.pi) ^ (-((d : ℝ) / 2)) *
        (x ^ (((d : ℝ) / 2 - 1) - 1) * Real.exp (-(R / 4 * x)))) (Ioi 0) :=
    fun x hx => pbar_comp_inv d R hx
  have hI : IntegrableOn (pbar d R) (Ioi 0) := by
    rw [← integrableOn_Ioi_comp_rpow_iff (pbar d R) (p := -1) (by norm_num)]
    exact IntegrableOn.congr_fun (Integrable.const_mul hint _) hcongr.symm measurableSet_Ioi
  refine ⟨hI, ?_⟩
  rw [← integral_comp_rpow_Ioi (pbar d R) (p := -1) (by norm_num),
    setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, hval]
  -- algebra
  unfold cd
  have h4 : (4 : ℝ) ^ ((d : ℝ) / 2 - 1) = (4 : ℝ) ^ ((d : ℝ) / 2) / 4 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have hR' : R ^ (1 - (d : ℝ) / 2) = (R ^ ((d : ℝ) / 2 - 1))⁻¹ := by
    rw [← Real.rpow_neg hR.le]; congr 1; ring
  rw [Real.rpow_neg (by positivity), Real.mul_rpow (by norm_num) hpi.le,
    Real.div_rpow (by norm_num) hr.le, Real.one_rpow, Real.div_rpow hR.le (by norm_num), h4, hR']
  have : 0 < (4 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hpi _
  have : 0 < R ^ ((d : ℝ) / 2 - 1) := Real.rpow_pos_of_pos hR _
  field_simp

end

end FRD.GreenAsymp
