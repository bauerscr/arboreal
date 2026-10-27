import Mathlib

/-!
# The algebra of the (F1) band

`F1_alg`: if `P = g + p₂ g² + r_P` and `w = -c g + r_w` with `|r_P| ≤ e g² + c₃ g³`,
`|r_w| ≤ c_w g²`, `|w| ≤ 1/8`, `|c| ≤ c₁`, then
`|Re(P/(1+w)²) - g - Re(p₂ + 2c) g²| ≤ e' g² + C g³` with explicit constants.
-/

namespace Step2

noncomputable section

/-- `|(1+w)^{-2} - 1 + 2w| ≤ 4|w|²` for `|w| ≤ 1/8`. -/
theorem inv_sq_expand {w : ℂ} (hw : ‖w‖ ≤ 1 / 8) :
    ‖((1 + w) ^ 2)⁻¹ - 1 + 2 * w‖ ≤ 5 * ‖w‖ ^ 2 := by
  have h1 : 7 / 8 ≤ ‖1 + w‖ := by
    have := norm_sub_le (1 + w) w
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have h0 : (1 + w) ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; norm_num at h1
  have e : ((1 + w) ^ 2)⁻¹ - 1 + 2 * w = w ^ 2 * (3 + 2 * w) / (1 + w) ^ 2 := by
    field_simp; ring
  rw [e, norm_div, norm_mul, norm_pow, norm_pow]
  have h3 : ‖3 + 2 * w‖ ≤ 13 / 4 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]; simp only [Complex.norm_ofNat]; linarith
  have h2 : (49 / 64 : ℝ) ≤ ‖1 + w‖ ^ 2 := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  have hw2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h3 hw2, mul_le_mul_of_nonneg_left h2 hw2]

/-- **The algebra of (F1).** -/
theorem F1_alg {g e c₃ c₁ cw : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1) (he : 0 ≤ e) (hc₃ : 0 ≤ c₃)
    (hc₁ : 0 ≤ c₁) (hcw : 0 ≤ cw) {P p₂ w c rP rw : ℂ} (hP : P = g + p₂ * g ^ 2 + rP)
    (hrP : ‖rP‖ ≤ e * g ^ 2 + c₃ * g ^ 3) (hw : w = -(c * g) + rw) (hrw : ‖rw‖ ≤ cw * g ^ 2)
    (hw8 : ‖w‖ ≤ 1 / 8) (hc : ‖c‖ ≤ c₁) (hp₂ : ‖p₂‖ ≤ c₁) :
    |(P / (1 + w) ^ 2).re - g - (p₂ + 2 * c).re * g ^ 2| ≤
      e * g ^ 2 + (c₃ + 2 * cw + 5 * (c₁ + cw) ^ 2 + 3 * (c₁ + e + c₃) * (c₁ + cw)) * g ^ 3 := by
  set u := ((1 + w) ^ 2)⁻¹ - 1 + 2 * w with hu
  have hu' := inv_sq_expand hw8
  have hwn : ‖w‖ ≤ (c₁ + cw) * g := by
    rw [hw]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
    have : cw * g ^ 2 ≤ cw * g := by
      have : g ^ 2 ≤ g := by nlinarith
      exact mul_le_mul_of_nonneg_left this hcw
    nlinarith [mul_le_mul_of_nonneg_right hc hg]
  -- P / (1+w)² = P (1 - 2w + u)
  have e1 : P / (1 + w) ^ 2 = P * (1 - 2 * w + u) := by
    rw [hu, div_eq_mul_inv]; ring
  -- expansion
  set Q := P - g with hQ
  have hQe : Q = p₂ * g ^ 2 + rP := by rw [hQ, hP]; ring
  have hQn : ‖Q‖ ≤ (c₁ + e + c₃) * g ^ 2 := by
    rw [hQe]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
    have : c₃ * g ^ 3 ≤ c₃ * g ^ 2 := by
      have : g ^ 3 ≤ g ^ 2 := by nlinarith [sq_nonneg g]
      exact mul_le_mul_of_nonneg_left this hc₃
    nlinarith [mul_le_mul_of_nonneg_right hp₂ (sq_nonneg g)]
  have hun : ‖u‖ ≤ 5 * (c₁ + cw) ^ 2 * g ^ 2 := by
    refine hu'.trans ?_
    have := pow_le_pow_left₀ (norm_nonneg w) hwn 2
    nlinarith
  have key : P / (1 + w) ^ 2 - g - (p₂ + 2 * c) * g ^ 2 =
      rP - g * (2 * rw) + g * u + Q * (-2 * w + u) := by
    have hPQ : P = g + Q := by rw [hQ]; ring
    rw [e1, hPQ, hQe, hw]; ring
  have hre : (P / (1 + w) ^ 2).re - g - (p₂ + 2 * c).re * g ^ 2 =
      (P / (1 + w) ^ 2 - g - (p₂ + 2 * c) * g ^ 2).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re]
    have : ((g : ℂ) ^ 2).re = g ^ 2 := by rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
    have h2 : ((g : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
    rw [this, h2]; ring
  rw [hre, key]
  refine (Complex.abs_re_le_norm _).trans ?_
  have t1 : ‖g * (2 * rw)‖ ≤ 2 * cw * g ^ 3 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
    simp only [Complex.norm_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hrw hg]
  have t2 : ‖g * u‖ ≤ 5 * (c₁ + cw) ^ 2 * g ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
    nlinarith [mul_le_mul_of_nonneg_left hun hg]
  have t3 : ‖-2 * w + u‖ ≤ 3 * ((c₁ + cw) * g) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_neg]; simp only [Complex.norm_ofNat]
    have hu2 : ‖u‖ ≤ 5 / 8 * ‖w‖ := by
      refine hu'.trans ?_
      have := norm_nonneg w
      nlinarith
    nlinarith [norm_nonneg w]
  have t4 : ‖Q * (-2 * w + u)‖ ≤ 3 * (c₁ + e + c₃) * (c₁ + cw) * g ^ 3 := by
    rw [norm_mul]
    have h0 : 0 ≤ (c₁ + e + c₃) * g ^ 2 := by positivity
    calc ‖Q‖ * ‖-2 * w + u‖ ≤ (c₁ + e + c₃) * g ^ 2 * (3 * ((c₁ + cw) * g)) :=
          mul_le_mul hQn t3 (norm_nonneg _) h0
      _ = _ := by ring
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add hrP t1)) t2)) t4)
  refine hsum.trans (le_of_eq ?_)
  ring

/-- **The exact expansion of `P = κ'_g (1 + n')/Z²`.** -/
theorem P_identity {z gr n n' K2 K3 nu a msq w1 C1 δ κQg κQnu κLnu κDg S q SB ES G : ℂ}
    (hz : z ≠ 0) (e1 : G = gr * (1 + n)) (e2 : n = 4 * nu * w1) (e3 : n' = 4 * K2 * (w1 + C1))
    (e4 : K2 = nu - a * msq + 4 * (gr * z ^ 2) * δ - (κQnu + 4 * κQg * δ) - κLnu)
    (e5 : K3 = gr * z ^ 2 - κQg - (S + (gr * z ^ 2) ^ 2 * q +
      4 * C1 * (gr * z ^ 2) * (nu - a * msq + 4 * (gr * z ^ 2) * δ)) - κDg)
    (e6 : S = z ^ 2 * (G ^ 2 * SB + ES)) :
    K3 / z ^ 2 * (1 + n') - G + (z ^ 2 * q + SB) * G ^ 2 =
      gr * (4 * (-(a * msq) + 4 * (gr * z ^ 2) * δ) * w1 -
          4 * (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) -
          4 * C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ) * n') -
        (ES + (gr ^ 2 - G ^ 2) * z ^ 2 * q) * (1 + n') - G ^ 2 * (z ^ 2 * q + SB) * n' -
        (κQg + κDg) / z ^ 2 * (1 + n') := by
  subst e1 e2 e3 e4 e5 e6
  field_simp
  ring

/-- **The bound on the remainder of `P`.** -/
theorem rP_bound {z gr n' a msq w1 C1 δ κQg κQnu κLnu κDg q SB ES G nu : ℂ}
    {g eA eB ℓ L2 Cq cRQ cRL cCnu cn cn' cES KB CqD cRD : ℝ} (hg : 0 ≤ g)
    (hG : ‖G‖ = g) (hgr : ‖gr‖ ≤ 8 / 7 * g)
    (hT1 : ‖a * msq * w1‖ ≤ eA * g)
    (hT2 : ‖z ^ 2 * δ * w1‖ ≤ eB)
    (hT3 : ‖(κQnu + 4 * κQg * δ + κLnu) * (w1 + C1)‖ ≤ (2 * L2 * Cq * cRQ + Cq * cRL) * g ^ 2)
    (hT4 : ‖C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ)‖ ≤ cCnu * g)
    (hn' : ‖n'‖ ≤ cn' * g) (h1n' : ‖1 + n'‖ ≤ 9 / 8)
    (hES : ‖ES‖ ≤ cES * g ^ 3) (hgg : ‖gr ^ 2 - G ^ 2‖ ≤ 3 * cn * g ^ 3)
    (hq : ‖z ^ 2 * q‖ ≤ KB) (hSB : ‖SB‖ ≤ KB)
    (hQD : ‖(κQg + κDg) / z ^ 2‖ ≤ (64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4 * g ^ 3) :
    ‖gr * (4 * (-(a * msq) + 4 * (gr * z ^ 2) * δ) * w1 -
          4 * (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) -
          4 * C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ) * n') -
        (ES + (gr ^ 2 - G ^ 2) * z ^ 2 * q) * (1 + n') - G ^ 2 * (z ^ 2 * q + SB) * n' -
        (κQg + κDg) / z ^ 2 * (1 + n')‖ ≤
      (32 / 7 * eA + 1024 / 49 * eB) * g ^ 2 +
        (32 / 7 * (2 * L2 * Cq * cRQ + Cq * cRL) + 32 / 7 * cCnu * cn' +
          9 / 8 * (cES + 3 * cn * KB) + 2 * KB * cn' +
          9 / 8 * ((64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4)) * g ^ 3 := by
  have hgr0 := norm_nonneg gr
  have hKB : 0 ≤ KB := (norm_nonneg _).trans hSB
  -- the four pieces
  have e1 : gr * (4 * (-(a * msq) + 4 * (gr * z ^ 2) * δ) * w1 -
      4 * (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) -
      4 * C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ) * n') =
      -(4 * gr * (a * msq * w1)) + 16 * gr ^ 2 * (z ^ 2 * δ * w1) -
        4 * gr * ((κQnu + 4 * κQg * δ + κLnu) * (w1 + C1)) -
        4 * gr * (C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ)) * n' := by ring
  rw [e1]
  have t1 : ‖4 * gr * (a * msq * w1)‖ ≤ 32 / 7 * eA * g ^ 2 := by
    rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    calc 4 * ‖gr‖ * ‖a * msq * w1‖ ≤ 4 * (8 / 7 * g) * (eA * g) := by gcongr
      _ = _ := by ring
  have t2 : ‖16 * gr ^ 2 * (z ^ 2 * δ * w1)‖ ≤ 1024 / 49 * eB * g ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow]; simp only [Complex.norm_ofNat]
    have hg2 : ‖gr‖ ^ 2 ≤ (8 / 7 * g) ^ 2 := pow_le_pow_left₀ hgr0 hgr 2
    calc 16 * ‖gr‖ ^ 2 * ‖z ^ 2 * δ * w1‖ ≤ 16 * (8 / 7 * g) ^ 2 * eB := by gcongr
      _ = _ := by ring
  have t3 : ‖4 * gr * ((κQnu + 4 * κQg * δ + κLnu) * (w1 + C1))‖ ≤
      32 / 7 * (2 * L2 * Cq * cRQ + Cq * cRL) * g ^ 3 := by
    rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    calc 4 * ‖gr‖ * ‖(κQnu + 4 * κQg * δ + κLnu) * (w1 + C1)‖ ≤
        4 * (8 / 7 * g) * ((2 * L2 * Cq * cRQ + Cq * cRL) * g ^ 2) := by gcongr
      _ = _ := by ring
  have t4 : ‖4 * gr * (C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ)) * n'‖ ≤
      32 / 7 * cCnu * cn' * g ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    have hc : 0 ≤ cCnu * g := (norm_nonneg _).trans hT4
    calc 4 * ‖gr‖ * ‖C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ)‖ * ‖n'‖ ≤
        4 * (8 / 7 * g) * (cCnu * g) * (cn' * g) := by gcongr
      _ = _ := by ring
  have t5 : ‖(ES + (gr ^ 2 - G ^ 2) * z ^ 2 * q) * (1 + n')‖ ≤
      9 / 8 * (cES + 3 * cn * KB) * g ^ 3 := by
    rw [norm_mul]
    have h : ‖ES + (gr ^ 2 - G ^ 2) * z ^ 2 * q‖ ≤ (cES + 3 * cn * KB) * g ^ 3 := by
      refine (norm_add_le _ _).trans ?_
      rw [mul_assoc, norm_mul]
      have := mul_le_mul hgg hq (norm_nonneg _) ((norm_nonneg _).trans hgg)
      nlinarith
    have h0 : 0 ≤ (cES + 3 * cn * KB) * g ^ 3 := (norm_nonneg _).trans h
    calc ‖ES + (gr ^ 2 - G ^ 2) * z ^ 2 * q‖ * ‖1 + n'‖ ≤ (cES + 3 * cn * KB) * g ^ 3 * (9 / 8) :=
          mul_le_mul h h1n' (norm_nonneg _) h0
      _ = _ := by ring
  have t6 : ‖G ^ 2 * (z ^ 2 * q + SB) * n'‖ ≤ 2 * KB * cn' * g ^ 3 := by
    rw [norm_mul, norm_mul, norm_pow, hG]
    have h : ‖z ^ 2 * q + SB‖ ≤ 2 * KB := (norm_add_le _ _).trans (by linarith)
    have hcn : 0 ≤ cn' * g := (norm_nonneg _).trans hn'
    calc g ^ 2 * ‖z ^ 2 * q + SB‖ * ‖n'‖ ≤ g ^ 2 * (2 * KB) * (cn' * g) := by gcongr
      _ = _ := by ring
  have t7 : ‖(κQg + κDg) / z ^ 2 * (1 + n')‖ ≤
      9 / 8 * ((64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4) * g ^ 3 := by
    rw [norm_mul]
    have h0 : 0 ≤ (64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4 * g ^ 3 := (norm_nonneg _).trans hQD
    calc ‖(κQg + κDg) / z ^ 2‖ * ‖1 + n'‖ ≤
        (64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4 * g ^ 3 * (9 / 8) :=
          mul_le_mul hQD h1n' (norm_nonneg _) h0
      _ = _ := by ring
  have hsum := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_neg _).le.trans t1) t2)) t3)) t4)) t5)) t6)) t7)
  refine hsum.trans (le_of_eq ?_)
  ring

end

end Step2
