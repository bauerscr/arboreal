import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# One-dimensional heat kernel of `ℤ` (for eq:LapZd)

`Q t n = (2π)^{-1} ∫_{-π}^{π} e^{ikn} e^{-t(2-2cos k)} dk` is the continuous-time
simple random walk kernel on `ℤ`. We prove:

* `norm_Q_le_one`: `‖Q t n‖ ≤ 1`;
* `norm_Q_le_chernoff`: `‖Q t n‖ ≤ exp(-a|n| + 2 t a²)` for `a ∈ [0,1]` (contour shift);
* `norm_Q_le_sqrt`: `‖Q t n‖ ≤ C / √t`;
* `norm_Q_sub_gauss_le`: `‖Q t n - g t n‖ ≤ C / (t √t)` (local CLT), where
  `g t n = (4πt)^{-1/2} e^{-n²/(4t)}`.
-/

namespace FRD.GreenAsymp

noncomputable section

open MeasureTheory Set Complex

/-- `λ₁(k) = 2 - 2 cos k`. -/
def lam1 (k : ℝ) : ℝ := 2 - 2 * Real.cos k

/-- The integrand, extended to `ℂ`. -/
def fC (t : ℝ) (n : ℤ) (z : ℂ) : ℂ := cexp (I * z * n - t * (2 - 2 * Complex.cos z))

/-- The 1D heat kernel of `ℤ`. -/
def Q (t : ℝ) (n : ℤ) : ℂ := (2 * Real.pi : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi, fC t n k

theorem fC_add_two_pi (t : ℝ) (n : ℤ) (z : ℂ) : fC t n (z + 2 * Real.pi) = fC t n z := by
  unfold fC
  rw [Complex.cos_add_two_pi]
  have : I * (z + 2 * Real.pi) * n - t * (2 - 2 * Complex.cos z) =
      (I * z * n - t * (2 - 2 * Complex.cos z)) + n * (2 * Real.pi * I) := by ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem fC_differentiable (t : ℝ) (n : ℤ) : Differentiable ℂ (fC t n) := by
  unfold fC; fun_prop

/-- Contour shift: the integral over `[-π, π]` equals that over `[-π, π] + iα`. -/
theorem integral_fC_shift (t : ℝ) (n : ℤ) (α : ℝ) :
    ∫ k in (-Real.pi)..Real.pi, fC t n k = ∫ k in (-Real.pi)..Real.pi, fC t n (k + α * I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fC t n)
    (-Real.pi : ℂ) (Real.pi + α * I) (fC_differentiable t n).differentiableOn
  have hper : ∀ y : ℝ, fC t n ((Real.pi : ℂ) + y * I) = fC t n ((-Real.pi : ℂ) + y * I) := by
    intro y
    rw [← fC_add_two_pi t n ((-Real.pi : ℂ) + y * I)]
    congr 1; ring
  simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, mul_re, I_re, mul_zero,
    I_im, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add, ofReal_zero, zero_mul] at h
  simp only [ofReal_neg, hper] at h
  have h2 := sub_eq_zero.1 (by simpa using h)
  simpa using h2

theorem re_cos_add_mul_I (k α : ℝ) :
    (Complex.cos ((k : ℂ) + α * I)).re = Real.cos k * Real.cosh α := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  simp [mul_re, Complex.cos_ofReal_re]

theorem norm_fC_shift_le {t : ℝ} (ht : 0 ≤ t) (n : ℤ) (k α : ℝ) :
    ‖fC t n ((k : ℂ) + α * I)‖ ≤ Real.exp (-α * n + 2 * t * (Real.cosh α - 1)) := by
  unfold fC
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hre : (I * ((k : ℂ) + α * I) * n - t * (2 - 2 * Complex.cos ((k : ℂ) + α * I))).re =
      -α * n - 2 * t + 2 * t * (Real.cos k * Real.cosh α) := by
    have := re_cos_add_mul_I k α
    simp [mul_re, sub_re, this]
    ring
  rw [hre]
  have h1 : Real.cos k * Real.cosh α ≤ Real.cosh α := by
    have := Real.cosh_pos α
    nlinarith [Real.cos_le_one k]
  nlinarith

/-- Chernoff-type bound via contour shift, for any real `α`. -/
theorem norm_Q_le_exp {t : ℝ} (ht : 0 ≤ t) (n : ℤ) (α : ℝ) :
    ‖Q t n‖ ≤ Real.exp (-α * n + 2 * t * (Real.cosh α - 1)) := by
  unfold Q
  rw [integral_fC_shift t n α, norm_mul]
  have hpi := Real.pi_pos
  have hn : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]; congr 1
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi)
    (C := Real.exp (-α * n + 2 * t * (Real.cosh α - 1)))
    (f := fun k : ℝ => fC t n ((k : ℂ) + α * I)) (fun k _ => norm_fC_shift_le ht n k α)
  rw [show |Real.pi - -Real.pi| = 2 * Real.pi by rw [abs_of_pos (by linarith)]; ring] at hb
  calc (2 * Real.pi)⁻¹ * ‖∫ k in (-Real.pi)..Real.pi, fC t n ((k : ℂ) + α * I)‖
      ≤ (2 * Real.pi)⁻¹ * (Real.exp (-α * n + 2 * t * (Real.cosh α - 1)) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

theorem norm_Q_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℤ) : ‖Q t n‖ ≤ 1 := by
  simpa using norm_Q_le_exp ht n 0

theorem cosh_sub_one_le_sq {a : ℝ} (ha : |a| ≤ 1) : Real.cosh a - 1 ≤ a ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq a
  have hy : |a ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have : a ^ 2 ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
    linarith
  have h2 := Real.abs_exp_sub_one_le hy
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2 / 2)] at h2
  have h3 := (abs_le.1 h2).2
  linarith

/-- `‖Q t n‖ ≤ exp(-a|n| + 2ta²)` for `0 ≤ a ≤ 1`. -/
theorem norm_Q_le_chernoff {t : ℝ} (ht : 0 ≤ t) (n : ℤ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖Q t n‖ ≤ Real.exp (-a * |(n : ℝ)| + 2 * t * a ^ 2) := by
  rcases le_total 0 (n : ℝ) with hn | hn
  · refine (norm_Q_le_exp ht n a).trans (Real.exp_le_exp.2 ?_)
    rw [abs_of_nonneg hn]
    have := cosh_sub_one_le_sq (a := a) (by rw [abs_of_nonneg ha0]; exact ha1)
    nlinarith
  · refine (norm_Q_le_exp ht n (-a)).trans (Real.exp_le_exp.2 ?_)
    rw [abs_of_nonpos hn, Real.cosh_neg]
    have := cosh_sub_one_le_sq (a := a) (by rw [abs_of_nonneg ha0]; exact ha1)
    nlinarith

/-! ### Bounds on the real line -/

theorem fC_ofReal (t : ℝ) (n : ℤ) (k : ℝ) :
    fC t n k = cexp (((k * n : ℝ) : ℂ) * I) * ((Real.exp (-t * lam1 k) : ℝ) : ℂ) := by
  unfold fC lam1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem norm_fC_ofReal (t : ℝ) (n : ℤ) (k : ℝ) : ‖fC t n k‖ = Real.exp (-t * lam1 k) := by
  rw [fC_ofReal, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem continuous_fC_ofReal (t : ℝ) (n : ℤ) : Continuous fun k : ℝ => fC t n k :=
  (fC_differentiable t n).continuous.comp Complex.continuous_ofReal

theorem lam1_nonneg (k : ℝ) : 0 ≤ lam1 k := by
  unfold lam1; linarith [Real.cos_le_one k]

theorem lam1_ge {k : ℝ} (hk : |k| ≤ Real.pi) : 4 / Real.pi ^ 2 * k ^ 2 ≤ lam1 k := by
  unfold lam1
  have := Real.cos_le_one_sub_mul_cos_sq hk
  have h2 : 4 / Real.pi ^ 2 * k ^ 2 = 2 * (2 / Real.pi ^ 2 * k ^ 2) := by ring
  linarith

theorem lam1_le (k : ℝ) : lam1 k ≤ k ^ 2 := by
  unfold lam1
  have := Real.one_sub_sq_div_two_le_cos (x := k)
  linarith

theorem sq_sub_lam1_le (k : ℝ) : k ^ 2 - lam1 k ≤ k ^ 4 := by
  unfold lam1
  rcases le_or_gt |k| 1 with hk | hk
  · have h := Real.cos_bound hk
    have h2 := (abs_le.1 h).2
    have : |k| ^ 4 = k ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
    rw [this] at h2
    nlinarith [sq_nonneg (k ^ 2)]
  · have h1 : 1 < k ^ 2 := by
      have := sq_abs k
      nlinarith [abs_nonneg k]
    have : k ^ 2 ≤ k ^ 4 := by nlinarith
    linarith [Real.cos_le_one k]

/-- `‖Q t n‖ ≤ √π / (4 √t)`. -/
theorem norm_Q_le_sqrt {t : ℝ} (ht : 0 < t) (n : ℤ) :
    ‖Q t n‖ ≤ Real.sqrt Real.pi / (4 * Real.sqrt t) := by
  have hpi := Real.pi_pos
  set b := 4 * t / Real.pi ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have h1 : ‖∫ k in (-Real.pi)..Real.pi, fC t n k‖ ≤
      ∫ k in (-Real.pi)..Real.pi, Real.exp (-b * k ^ 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuous_fC_ofReal t n).norm.intervalIntegrable _ _)
      (by exact (by fun_prop : Continuous fun k : ℝ => Real.exp (-b * k ^ 2)).intervalIntegrable _ _)
      fun k hk => ?_
    rw [norm_fC_ofReal]
    refine Real.exp_le_exp.2 ?_
    have := lam1_ge (k := k) (abs_le.2 hk)
    rw [hb]
    have : 4 * t / Real.pi ^ 2 * k ^ 2 = t * (4 / Real.pi ^ 2 * k ^ 2) := by ring
    nlinarith
  have h2 : ∫ k in (-Real.pi)..Real.pi, Real.exp (-b * k ^ 2) ≤ Real.sqrt (Real.pi / b) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_gaussian b]
    exact setIntegral_le_integral (integrable_exp_neg_mul_sq hb0)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have h3 : Real.sqrt (Real.pi / b) = Real.pi * Real.sqrt Real.pi / (2 * Real.sqrt t) := by
    rw [hb, show Real.pi / (4 * t / Real.pi ^ 2) = (Real.pi / 2) ^ 2 * (Real.pi / t) by
      field_simp; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      Real.sqrt_div hpi.le]
    field_simp
  have hn : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]; congr 1
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold Q
  rw [norm_mul, hn]
  have hst := Real.sqrt_pos.2 ht
  calc (2 * Real.pi)⁻¹ * ‖∫ k in (-Real.pi)..Real.pi, fC t n k‖
      ≤ (2 * Real.pi)⁻¹ * (Real.pi * Real.sqrt Real.pi / (2 * Real.sqrt t)) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = Real.sqrt Real.pi / (4 * Real.sqrt t) := by field_simp; ring

/-! ### Local CLT -/

/-- The continuum heat kernel `g t n = (4πt)^{-1/2} e^{-n²/(4t)}`. -/
def g (t : ℝ) (n : ℤ) : ℝ := Real.exp (-(n : ℝ) ^ 2 / (4 * t)) / Real.sqrt (4 * Real.pi * t)

theorem g_nonneg (t : ℝ) (n : ℤ) : 0 ≤ g t n :=
  div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

theorem g_le_sqrt {t : ℝ} (ht : 0 < t) (n : ℤ) : g t n ≤ Real.sqrt Real.pi / (4 * Real.sqrt t) := by
  unfold g
  have hpi := Real.pi_pos
  have h1 : Real.exp (-(n : ℝ) ^ 2 / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (n : ℝ)]) (by positivity)
  have hs : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs]
  have hsp := Real.sqrt_pos.2 hpi
  have hst := Real.sqrt_pos.2 ht
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpi4 : 1 ≤ Real.sqrt Real.pi * Real.sqrt Real.pi / 2 := by
    rw [Real.mul_self_sqrt hpi.le]; linarith [Real.two_le_pi]
  nlinarith [mul_pos hsp hst]

/-- The real-line integrand of the continuum kernel. -/
def hG (t : ℝ) (n : ℤ) (k : ℝ) : ℂ := cexp (((k * n : ℝ) : ℂ) * I) * ((Real.exp (-t * k ^ 2) : ℝ) : ℂ)

theorem norm_hG (t : ℝ) (n : ℤ) (k : ℝ) : ‖hG t n k‖ = Real.exp (-t * k ^ 2) := by
  rw [hG, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem integrable_hG {t : ℝ} (ht : 0 < t) (n : ℤ) : Integrable (hG t n) := by
  refine (integrable_exp_neg_mul_sq ht).mono' (by unfold hG; fun_prop) ?_
  exact Filter.Eventually.of_forall fun k => (norm_hG t n k).le

theorem integral_hG {t : ℝ} (ht : 0 < t) (n : ℤ) :
    ∫ k, hG t n k = ((2 * Real.pi * g t n : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have h := fourierIntegral_gaussian (b := (t : ℂ)) (by simpa using ht) (n : ℂ)
  have heq : (fun k : ℝ => hG t n k) =
      fun k : ℝ => cexp (I * (n : ℂ) * k) * cexp (-(t : ℂ) * k ^ 2) := by
    funext k; unfold hG
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [heq, h]
  have hc : ((Real.pi : ℂ) / t) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  have he : cexp (-(n : ℂ) ^ 2 / (4 * t)) = ((Real.exp (-(n : ℝ) ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  rw [hc, he, ← Complex.ofReal_mul]
  congr 1
  unfold g
  have hs2 : Real.sqrt (Real.pi / t) * Real.sqrt (4 * Real.pi * t) = 2 * Real.pi := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / t * (4 * Real.pi * t) = (2 * Real.pi) ^ 2 by
      field_simp; ring, Real.sqrt_sq (by positivity)]
  have hpos : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.2 (by positivity)
  rw [← hs2]
  field_simp

theorem exp_sub_exp_le {a b : ℝ} (hab : a ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ (b - a) * Real.exp (-a) := by
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith)]
  have h2 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by linarith [Real.add_one_le_exp (-(b - a))]
  have h3 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  nlinarith [Real.exp_pos (-a)]

theorem lclt_pointwise {t : ℝ} (ht : 0 < t) {k : ℝ} (hk : |k| ≤ Real.pi) :
    |Real.exp (-t * lam1 k) - Real.exp (-t * k ^ 2)| ≤
      Real.pi ^ 4 / (2 * t) * Real.exp (-(2 * t / Real.pi ^ 2) * k ^ 2) := by
  have hpi := Real.pi_pos
  have hl0 := lam1_nonneg k
  have hl1 := lam1_le k
  have hl2 := sq_sub_lam1_le k
  have hl3 := lam1_ge hk
  have h := exp_sub_exp_le (a := t * lam1 k) (b := t * k ^ 2)
    (mul_le_mul_of_nonneg_left hl1 ht.le)
  rw [show -(t * lam1 k) = -t * lam1 k by ring, show -(t * k ^ 2) = -t * k ^ 2 by ring] at h
  refine h.trans ?_
  set y := t * k ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  -- `y² ≤ (π⁴/2) e^{2y/π²}`
  have hfac := Real.pow_div_factorial_le_exp (x := 2 * y / Real.pi ^ 2) (by positivity) 2
  simp only [Nat.factorial_two, Nat.cast_ofNat] at hfac
  have hy2 : y ^ 2 ≤ Real.pi ^ 4 / 2 * Real.exp (2 * y / Real.pi ^ 2) := by
    have : y ^ 2 = Real.pi ^ 4 / 2 * ((2 * y / Real.pi ^ 2) ^ 2 / 2) := by field_simp
    rw [this]; gcongr
  have hA : (t * k ^ 2 - t * lam1 k) ≤ y ^ 2 / t := by
    rw [hy]; field_simp; nlinarith
  have hB : Real.exp (-t * lam1 k) ≤ Real.exp (-(4 / Real.pi ^ 2) * y) := by
    refine Real.exp_le_exp.2 ?_
    rw [hy]; nlinarith
  have hC : Real.exp (2 * y / Real.pi ^ 2) * Real.exp (-(4 / Real.pi ^ 2) * y) =
      Real.exp (-(2 * t / Real.pi ^ 2) * k ^ 2) := by
    rw [← Real.exp_add]; congr 1; rw [hy]; ring
  calc (t * k ^ 2 - t * lam1 k) * Real.exp (-t * lam1 k)
      ≤ y ^ 2 / t * Real.exp (-(4 / Real.pi ^ 2) * y) :=
        mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    _ ≤ (Real.pi ^ 4 / 2 * Real.exp (2 * y / Real.pi ^ 2)) / t *
          Real.exp (-(4 / Real.pi ^ 2) * y) := by gcongr
    _ = Real.pi ^ 4 / (2 * t) * Real.exp (-(2 * t / Real.pi ^ 2) * k ^ 2) := by
        rw [← hC]; field_simp

theorem tail_pointwise {t : ℝ} (ht : 0 < t) {k : ℝ} (hk : Real.pi ≤ |k|) :
    Real.exp (-t * k ^ 2) ≤ 2 / (Real.pi ^ 2 * t) * Real.exp (-(t / 2) * k ^ 2) := by
  have hpi := Real.pi_pos
  have hk2 : Real.pi ^ 2 ≤ k ^ 2 := by
    rw [← sq_abs k]; exact pow_le_pow_left₀ hpi.le hk 2
  have h1 : Real.exp (-t * k ^ 2) = Real.exp (-(t / 2) * k ^ 2) * Real.exp (-(t / 2) * k ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(t / 2) * k ^ 2) ≤ Real.exp (-(t * Real.pi ^ 2 / 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h3 : Real.exp (-(t * Real.pi ^ 2 / 2)) ≤ 2 / (Real.pi ^ 2 * t) := by
    have := Real.add_one_le_exp (t * Real.pi ^ 2 / 2)
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (t * Real.pi ^ 2 / 2)]
  rw [h1, mul_comm]
  exact mul_le_mul_of_nonneg_right (h2.trans h3) (Real.exp_pos _).le

/-- The explicit LCLT constant. -/
def Clclt : ℝ := (2 * Real.pi)⁻¹ *
  (Real.pi ^ 4 / 2 * Real.sqrt (Real.pi / (2 / Real.pi ^ 2)) +
    2 / Real.pi ^ 2 * Real.sqrt (Real.pi / (1 / 2)))

theorem Clclt_nonneg : 0 ≤ Clclt := by unfold Clclt; have := Real.pi_pos; positivity

/-- Local CLT: `‖Q t n - g t n‖ ≤ C / (t √t)`. -/
theorem norm_Q_sub_g_le {t : ℝ} (ht : 0 < t) (n : ℤ) :
    ‖Q t n - (g t n : ℂ)‖ ≤ Clclt / (t * Real.sqrt t) := by
  have hpi := Real.pi_pos
  set S := Ioc (-Real.pi) Real.pi
  set B : ℝ → ℝ := fun k => Real.pi ^ 4 / (2 * t) * Real.exp (-(2 * t / Real.pi ^ 2) * k ^ 2) +
    2 / (Real.pi ^ 2 * t) * Real.exp (-(t / 2) * k ^ 2) with hB
  have hBi : Integrable B :=
    ((integrable_exp_neg_mul_sq (by positivity)).const_mul _).add
      ((integrable_exp_neg_mul_sq (by positivity)).const_mul _)
  have hBint : ∫ k, B k = Real.pi ^ 4 / (2 * t) * Real.sqrt (Real.pi / (2 * t / Real.pi ^ 2)) +
      2 / (Real.pi ^ 2 * t) * Real.sqrt (Real.pi / (t / 2)) := by
    rw [hB, integral_add ((integrable_exp_neg_mul_sq (by positivity)).const_mul _)
      ((integrable_exp_neg_mul_sq (by positivity)).const_mul _), integral_const_mul,
      integral_const_mul, integral_gaussian, integral_gaussian]
  have hfi : Integrable (S.indicator fun k : ℝ => fC t n k) :=
    ((continuous_fC_ofReal t n).integrableOn_Icc (a := -Real.pi) (b := Real.pi)).mono_set
      Ioc_subset_Icc_self |>.integrable_indicator measurableSet_Ioc
  have h2pi : (2 * Real.pi : ℂ) * (Q t n - (g t n : ℂ)) =
      ∫ k, (S.indicator (fun k : ℝ => fC t n k) k - hG t n k) := by
    rw [integral_sub hfi (integrable_hG ht n), integral_indicator measurableSet_Ioc,
      integral_hG ht n, ← intervalIntegral.integral_of_le (by linarith), Q]
    have : (2 * Real.pi : ℂ) ≠ 0 := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ this, one_mul]
    push_cast; ring
  have hpt : ∀ k, ‖S.indicator (fun k : ℝ => fC t n k) k - hG t n k‖ ≤ B k := by
    intro k
    have hB1 : 0 ≤ Real.pi ^ 4 / (2 * t) * Real.exp (-(2 * t / Real.pi ^ 2) * k ^ 2) := by
      positivity
    have hB2 : 0 ≤ 2 / (Real.pi ^ 2 * t) * Real.exp (-(t / 2) * k ^ 2) := by positivity
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem hk, fC_ofReal, hG, ← mul_sub, norm_mul,
        Complex.norm_exp_ofReal_mul_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      have hk' : |k| ≤ Real.pi := abs_le.2 ⟨hk.1.le, hk.2⟩
      exact (lclt_pointwise ht hk').trans (le_add_of_nonneg_right hB2)
    · rw [Set.indicator_of_notMem hk, zero_sub, norm_neg, norm_hG]
      have hk' : Real.pi ≤ |k| := by
        simp only [S, Set.mem_Ioc, not_and_or, not_lt, not_le] at hk
        rcases hk with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact (tail_pointwise ht hk').trans (le_add_of_nonneg_left hB1)
  have hnorm := norm_integral_le_of_norm_le hBi (Filter.Eventually.of_forall hpt)
  rw [← h2pi, hBint, norm_mul] at hnorm
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn] at hnorm
  have hst := Real.sqrt_pos.2 ht
  have e1 : Real.sqrt (Real.pi / (2 * t / Real.pi ^ 2)) =
      Real.sqrt (Real.pi / (2 / Real.pi ^ 2)) / Real.sqrt t := by
    rw [← Real.sqrt_div (by positivity)]; congr 1; field_simp
  have e2 : Real.sqrt (Real.pi / (t / 2)) = Real.sqrt (Real.pi / (1 / 2)) / Real.sqrt t := by
    rw [← Real.sqrt_div (by positivity)]; congr 1; field_simp
  rw [e1, e2] at hnorm
  have : ‖Q t n - (g t n : ℂ)‖ ≤ (2 * Real.pi)⁻¹ *
      (Real.pi ^ 4 / (2 * t) * (Real.sqrt (Real.pi / (2 / Real.pi ^ 2)) / Real.sqrt t) +
        2 / (Real.pi ^ 2 * t) * (Real.sqrt (Real.pi / (1 / 2)) / Real.sqrt t)) := by
    rw [le_inv_mul_iff₀ (by positivity)]; exact hnorm
  refine this.trans (le_of_eq ?_)
  unfold Clclt
  field_simp

end

end FRD.GreenAsymp
