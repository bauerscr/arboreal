import Step2.Flow.ZetaSharp0

/-!
# One step of `log |Z_j|` from the sharp gradient coupling (numbers)

If `‖ζ + ǧ_r X‖ ≤ c_E g²` (`zeta_sharp_hist`), `|ǧ_r - g| ≤ c_n g²` (`stGr_sub_le`),
`|ǧ_r| ≤ (8/7) g`, `|X| ≤ K_z` (`Zcov_hist`) and `|X - log L/2π| ≤ ε_X` (`Cprime_values`), then
(`logZ_step_num`)

  `|log‖1 + ζ‖ + (log L/2π) g| ≤ (7(c_E + (8/7)K_z)² + c_E + c_n K_z) g² + g ε_X`,

and without the value of `X` (`logZ_step_crude`, used at `j = 0`)

  `|log‖1 + ζ‖ + ℓ₀ g| ≤ (7(c_E + (8/7)K_z)² + c_E + (8/7) K_z + |ℓ₀|) g`.
-/

namespace Step2

theorem zeta_norm_le {ζ gr X : ℂ} {g cE Kz : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1) (hcE : 0 ≤ cE)
    (hs : ‖ζ + gr * X‖ ≤ cE * g ^ 2) (hgr' : ‖gr‖ ≤ 8 / 7 * g) (hX : ‖X‖ ≤ Kz) :
    ‖ζ‖ ≤ (cE + 8 / 7 * Kz) * g := by
  have h1 : ‖gr * X‖ ≤ 8 / 7 * g * Kz := by
    have hK : 0 ≤ Kz := (norm_nonneg _).trans hX
    rw [norm_mul]; exact mul_le_mul hgr' hX (norm_nonneg _) (by positivity)
  have e : ζ = (ζ + gr * X) - gr * X := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hg2 : g ^ 2 ≤ g := by rw [sq]; exact mul_le_of_le_one_right hg hg1
  have h2 : cE * g ^ 2 ≤ cE * g := mul_le_mul_of_nonneg_left hg2 hcE
  have e2 : (cE + 8 / 7 * Kz) * g = cE * g + 8 / 7 * g * Kz := by ring
  linarith only [hs, h1, h2, e2]

theorem logZ_step_num {ζ gr X : ℂ} {g ℓ0 cE Kz cn εX : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hζ4 : ‖ζ‖ ≤ 1 / 4) (hs : ‖ζ + gr * X‖ ≤ cE * g ^ 2) (hgr : ‖gr - g‖ ≤ cn * g ^ 2)
    (hgr' : ‖gr‖ ≤ 8 / 7 * g) (hX : ‖X‖ ≤ Kz) (hXl : ‖X - ℓ0‖ ≤ εX) (hcE : 0 ≤ cE)
    (hKz : 0 ≤ Kz) :
    |Real.log ‖1 + ζ‖ + ℓ0 * g| ≤ (7 * (cE + 8 / 7 * Kz) ^ 2 + cE + cn * Kz) * g ^ 2 + g * εX := by
  have hζ := zeta_norm_le hg hg1 hcE hs hgr' hX
  have hl := log_norm_one_add hζ4
  have hζ2 : ‖ζ‖ ^ 2 ≤ ((cE + 8 / 7 * Kz) * g) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  -- `Re ζ + ℓ₀ g = Re(ζ + ǧ_r X) - Re((ǧ_r - g) X) - g Re(X - ℓ₀)`
  have e : ζ.re + ℓ0 * g = (ζ + gr * X).re - ((gr - g) * X).re - g * (X - ℓ0).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have h1 : |(ζ + gr * X).re| ≤ cE * g ^ 2 := (Complex.abs_re_le_norm _).trans hs
  have h2 : |((gr - g) * X).re| ≤ cn * g ^ 2 * Kz := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]; exact mul_le_mul hgr hX (norm_nonneg _) ((norm_nonneg _).trans hgr)
  have h3 : |g * (X - ℓ0).re| ≤ g * εX := by
    rw [abs_mul, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hXl) hg
  have e2 : Real.log ‖1 + ζ‖ + ℓ0 * g = (Real.log ‖1 + ζ‖ - ζ.re) + (ζ.re + ℓ0 * g) := by ring
  rw [e2, e]
  have t := abs_add_le (Real.log ‖1 + ζ‖ - ζ.re)
    ((ζ + gr * X).re - ((gr - g) * X).re - g * (X - ℓ0).re)
  have t2 := abs_sub ((ζ + gr * X).re - ((gr - g) * X).re) (g * (X - ℓ0).re)
  have t3 := abs_sub ((ζ + gr * X).re) (((gr - g) * X).re)
  have e3 : ((cE + 8 / 7 * Kz) * g) ^ 2 = (cE + 8 / 7 * Kz) ^ 2 * g ^ 2 := by ring
  have e4 : (7 * (cE + 8 / 7 * Kz) ^ 2 + cE + cn * Kz) * g ^ 2 + g * εX =
      7 * ((cE + 8 / 7 * Kz) ^ 2 * g ^ 2) + cE * g ^ 2 + cn * g ^ 2 * Kz + g * εX := by ring
  rw [e3] at hζ2
  have h7 : 7 * ‖ζ‖ ^ 2 ≤ 7 * ((cE + 8 / 7 * Kz) ^ 2 * g ^ 2) := by linarith only [hζ2]
  linarith only [t, t2, t3, hl, h1, h2, h3, h7, e4]

theorem logZ_step_crude {ζ gr X : ℂ} {g ℓ0 cE Kz : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hζ4 : ‖ζ‖ ≤ 1 / 4) (hs : ‖ζ + gr * X‖ ≤ cE * g ^ 2) (hgr' : ‖gr‖ ≤ 8 / 7 * g)
    (hX : ‖X‖ ≤ Kz) (hcE : 0 ≤ cE) (hKz : 0 ≤ Kz) :
    |Real.log ‖1 + ζ‖ + ℓ0 * g| ≤ (7 * (cE + 8 / 7 * Kz) ^ 2 + cE + 8 / 7 * Kz + |ℓ0|) * g := by
  have hζ := zeta_norm_le hg hg1 hcE hs hgr' hX
  have hl := log_norm_one_add hζ4
  have hζ2 : ‖ζ‖ ^ 2 ≤ ((cE + 8 / 7 * Kz) * g) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hre : |ζ.re| ≤ (cE + 8 / 7 * Kz) * g := (Complex.abs_re_le_norm _).trans hζ
  have hg2 : g ^ 2 ≤ g := by rw [sq]; exact mul_le_of_le_one_right hg hg1
  have hc0 : 0 ≤ (cE + 8 / 7 * Kz) ^ 2 := sq_nonneg _
  have h5 : ((cE + 8 / 7 * Kz) * g) ^ 2 ≤ (cE + 8 / 7 * Kz) ^ 2 * g := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hg2 hc0
  have e2 : Real.log ‖1 + ζ‖ + ℓ0 * g = (Real.log ‖1 + ζ‖ - ζ.re) + ζ.re + ℓ0 * g := by ring
  rw [e2]
  have t1 := abs_add_le (Real.log ‖1 + ζ‖ - ζ.re + ζ.re) (ℓ0 * g)
  have t2 := abs_add_le (Real.log ‖1 + ζ‖ - ζ.re) ζ.re
  have t3 : |ℓ0 * g| = |ℓ0| * g := by rw [abs_mul, abs_of_nonneg hg]
  have e4 : (7 * (cE + 8 / 7 * Kz) ^ 2 + cE + 8 / 7 * Kz + |ℓ0|) * g =
      7 * ((cE + 8 / 7 * Kz) ^ 2 * g) + (cE + 8 / 7 * Kz) * g + |ℓ0| * g := by ring
  linarith only [t1, t2, t3, hl, hζ2, h5, hre, e4]

end Step2
