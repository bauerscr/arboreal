import Step2.Flow.FlowF1c

/-!
# The sharp (F1) expansion: the tadpole in the one-loop coefficient

In `P_identity` the remainder contains `gr · 16 gr Z² δ w⁽¹⁾`, i.e.
`16 G² Z² δ w⁽¹⁾ + 16 (gr² - G²) Z² δ w⁽¹⁾`; the second piece is cubic. Moving the first piece
into the `g²` coefficient (`P_identity2`) leaves the mass term `-4 gr a m² w⁽¹⁾` as the only
`g²` remainder (`rP_bound2`). With `Z = Z_{j+1}`, `δ = C_j(e₁, 0) - C_j(0, 0)` and the accumulated
zero mode `w⁽¹⁾`, the new term `16 Z² δ w⁽¹⁾` is the dressed tadpole `T̃_j` of `Step2.HV_sharp`.

* `P_identity2`, `rP_bound2`, `F1_alg2`;
* `F1_core2`: `|Re(...) - g - Re(2c - (Z²q + S_B) + 16 Z² δ w⁽¹⁾) g²| ≤ (32/7) e_A g² + c₃ g³`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

/-- **The exact expansion of `P`, with the tadpole moved into the `g²` coefficient.** -/
theorem P_identity2 {z gr n n' K2 K3 nu a msq w1 C1 δ κQg κQnu κLnu κDg S q SB ES G : ℂ}
    (hz : z ≠ 0) (e1 : G = gr * (1 + n)) (e2 : n = 4 * nu * w1) (e3 : n' = 4 * K2 * (w1 + C1))
    (e4 : K2 = nu - a * msq + 4 * (gr * z ^ 2) * δ - (κQnu + 4 * κQg * δ) - κLnu)
    (e5 : K3 = gr * z ^ 2 - κQg - (S + (gr * z ^ 2) ^ 2 * q +
      4 * C1 * (gr * z ^ 2) * (nu - a * msq + 4 * (gr * z ^ 2) * δ)) - κDg)
    (e6 : S = z ^ 2 * (G ^ 2 * SB + ES)) :
    K3 / z ^ 2 * (1 + n') - G + (z ^ 2 * q + SB - 16 * (z ^ 2 * δ * w1)) * G ^ 2 =
      gr * (-(4 * (a * msq * w1)) - 4 * (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) -
          4 * C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ) * n') +
        16 * (gr ^ 2 - G ^ 2) * (z ^ 2 * δ * w1) -
        (ES + (gr ^ 2 - G ^ 2) * z ^ 2 * q) * (1 + n') - G ^ 2 * (z ^ 2 * q + SB) * n' -
        (κQg + κDg) / z ^ 2 * (1 + n') := by
  have h := P_identity hz e1 e2 e3 e4 e5 e6
  linear_combination h

/-- **The bound on the remainder of `P` in the sharp form**: only the mass term is quadratic. -/
theorem rP_bound2 {z gr n' a msq w1 C1 δ κQg κQnu κLnu κDg q SB ES G nu : ℂ}
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
    ‖gr * (-(4 * (a * msq * w1)) - 4 * (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) -
          4 * C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ) * n') +
        16 * (gr ^ 2 - G ^ 2) * (z ^ 2 * δ * w1) -
        (ES + (gr ^ 2 - G ^ 2) * z ^ 2 * q) * (1 + n') - G ^ 2 * (z ^ 2 * q + SB) * n' -
        (κQg + κDg) / z ^ 2 * (1 + n')‖ ≤
      32 / 7 * eA * g ^ 2 +
        (32 / 7 * (2 * L2 * Cq * cRQ + Cq * cRL) + 32 / 7 * cCnu * cn' +
          9 / 8 * (cES + 3 * cn * KB) + 2 * KB * cn' +
          9 / 8 * ((64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4) + 48 * cn * eB) * g ^ 3 := by
  have hgr0 := norm_nonneg gr
  have hKB : 0 ≤ KB := (norm_nonneg _).trans hSB
  have e1 : gr * (-(4 * (a * msq * w1)) - 4 * (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) -
      4 * C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ) * n') =
      -(4 * gr * (a * msq * w1)) -
        4 * gr * ((κQnu + 4 * κQg * δ + κLnu) * (w1 + C1)) -
        4 * gr * (C1 * (nu - a * msq + 4 * (gr * z ^ 2) * δ)) * n' := by ring
  rw [e1]
  have t1 : ‖4 * gr * (a * msq * w1)‖ ≤ 32 / 7 * eA * g ^ 2 := by
    rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    calc 4 * ‖gr‖ * ‖a * msq * w1‖ ≤ 4 * (8 / 7 * g) * (eA * g) := by gcongr
      _ = _ := by ring
  have t2 : ‖16 * (gr ^ 2 - G ^ 2) * (z ^ 2 * δ * w1)‖ ≤ 48 * cn * eB * g ^ 3 := by
    rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    have h0 : 0 ≤ 3 * cn * g ^ 3 := (norm_nonneg _).trans hgg
    calc 16 * ‖gr ^ 2 - G ^ 2‖ * ‖z ^ 2 * δ * w1‖ ≤ 16 * (3 * cn * g ^ 3) * eB := by gcongr
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
    ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
        ((norm_neg _).le.trans t1) t3)) t4)) t2)) t5)) t6)) t7)
  refine hsum.trans (le_of_eq ?_)
  ring

/-- **The algebra of (F1), with a separate bound `e ≤ e_m` in the cubic constant.** -/
theorem F1_alg2 {g e em c₃ c₁ cw : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1) (he : 0 ≤ e) (hem : e ≤ em)
    (hc₃ : 0 ≤ c₃) (hc₁ : 0 ≤ c₁) (hcw : 0 ≤ cw) {P p₂ w c rP rw : ℂ} (hP : P = g + p₂ * g ^ 2 + rP)
    (hrP : ‖rP‖ ≤ e * g ^ 2 + c₃ * g ^ 3) (hw : w = -(c * g) + rw) (hrw : ‖rw‖ ≤ cw * g ^ 2)
    (hw8 : ‖w‖ ≤ 1 / 8) (hc : ‖c‖ ≤ c₁) (hp₂ : ‖p₂‖ ≤ c₁) :
    |(P / (1 + w) ^ 2).re - g - (p₂ + 2 * c).re * g ^ 2| ≤
      e * g ^ 2 + (c₃ + 2 * cw + 5 * (c₁ + cw) ^ 2 + 3 * (c₁ + em + c₃) * (c₁ + cw)) * g ^ 3 := by
  refine (F1_alg hg hg1 he hc₃ hc₁ hcw hP hrP hw hrw hw8 hc hp₂).trans ?_
  have h1 : 3 * (c₁ + e + c₃) * (c₁ + cw) ≤ 3 * (c₁ + em + c₃) * (c₁ + cw) := by
    have : 0 ≤ c₁ + cw := by positivity
    nlinarith
  have h3 : 0 ≤ g ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_right h1 h3
  nlinarith

/-! ### The constants of the sharp one-step expansion -/

/-- `|Z² δ w⁽¹⁾| ≤ ℓ⁴/32`. -/
def f1eBs (ℓ : ℝ) : ℝ := ℓ ^ 4 / 32
/-- The cubic remainder of `P` in the sharp form. -/
def f1cPs (L : ℕ) (ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES : ℝ) : ℝ :=
  32 / 7 * (2 * (L : ℝ) ^ 2 * Cq * cRQ + Cq * cRL) +
    32 / 7 * f1cCnu L ℓ cZ cmu * f1cn' L ℓ cZ cmu Cq cRQ cRL +
    9 / 8 * (cES + 3 * f1cn ℓ cmu * KB) + 2 * KB * f1cn' L ℓ cZ cmu Cq cRQ cRL +
    9 / 8 * ((64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4) + 48 * f1cn ℓ cmu * f1eBs ℓ
/-- The cubic constant of the sharp (F1); `e_m` bounds the mass coefficient `(32/7) e_A`. -/
def f1c3s (L : ℕ) (ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES em : ℝ) : ℝ :=
  let c₁ := ℓ ^ 2 / 8 + 2 * KB + ℓ ^ 4 / 2
  let cw := f1cw ℓ cmu Cq cRQ cRL
  let cP := f1cPs L ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES
  cP + 2 * cw + 5 * (c₁ + cw) ^ 2 + 3 * (c₁ + em + cP) * (c₁ + cw)

set_option maxHeartbeats 4000000 in
/-- **The sharp core of the one-step (F1) estimate**, in plain numbers: the `g²`-coefficient
includes the tadpole `16 Z² δ w⁽¹⁾`, and the only `g²`-remainder is the mass term. -/
theorem F1_core2 {L : ℕ} {g ℓ Lj aZ cZ cmu Cq RQ RL CqD RD cRQ cRL cRD cES KB ρ msqR : ℝ}
    {z c₀ δ gr nuS A w1 C1 κQz κQy κQnu κQg κLz κLy κLnu κDg S q SB ES : ℂ}
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hℓ : 0 < ℓ) (hL4 : (4 : ℝ) ≤ (L : ℝ) ^ 2) (hLj1 : 1 ≤ Lj)
    (hap : 0 < ‖z‖) (haZp : 0 < aZ) (hr : aZ ≤ 8 / 7 * ‖z‖)
    (hcZ : 0 ≤ cZ) (hcmu : 0 ≤ cmu) (hCq : 0 ≤ Cq) (hCqD : 0 ≤ CqD) (hcRQ : 0 ≤ cRQ)
    (hcRL : 0 ≤ cRL) (hcRD : 0 ≤ cRD) (hKB : 0 ≤ KB) (hcES : 0 ≤ cES) (hρ0 : 0 ≤ ρ)
    (hρ8 : ρ ≤ 1 / 8)
    (hG : (g : ℂ) = gr * (1 + nCor nuS w1))
    (hnuS : ‖nuS / z‖ * ((L : ℝ) ^ 2 * Lj) ≤ (L : ℝ) ^ 2 * (cmu * g))
    (hA : ‖A / z‖ ≤ 16 / 7 * (cZ * g)) (hmsq : |msqR| * Lj ≤ 1) {eA em : ℝ} (heA : 0 ≤ eA)
    (heAm : 32 / 7 * eA ≤ em) (hT1 : ‖A * (msqR : ℂ) * w1‖ ≤ eA * g)
    (hzw1 : ‖z * w1‖ ≤ ℓ ^ 2 * Lj) (hzC1 : ‖z * C1‖ ≤ 9 / 16 * ℓ ^ 2 * ((L : ℝ) ^ 2 * Lj))
    (hzc0 : ‖z * c₀‖ ≤ ℓ ^ 2 / 16) (hzδ : ‖z * δ‖ * ((L : ℝ) ^ 2 * Lj) ≤ ℓ ^ 2 / 32)
    (q1 : ‖κQz‖ ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ) (q2 : ‖κQy‖ ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ)
    (q3 : ‖κQnu‖ ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / Lj) (q4 : ‖κQg‖ ≤ Cq * ((ℓ ^ 2 / aZ) ^ 2)⁻¹ * RQ)
    (l1 : ‖κLz‖ ≤ Cq * (ℓ ^ 2 / ‖z‖)⁻¹ * RL) (l2 : ‖κLy‖ ≤ Cq * (ℓ ^ 2 / ‖z‖)⁻¹ * RL)
    (l3 : ‖κLnu‖ ≤ Cq * (ℓ ^ 2 / ‖z‖)⁻¹ * RL / ((L : ℝ) ^ 2 * Lj))
    (hDg : ‖κDg‖ ≤ CqD * ((ℓ ^ 2 / ‖z‖) ^ 2)⁻¹ * RD)
    (hRQ0 : 0 ≤ RQ) (hRL0 : 0 ≤ RL) (hRD0 : 0 ≤ RD)
    (hRQ : RQ ≤ cRQ * g ^ 3) (hRL : RL ≤ cRL * g ^ 2) (hRD : RD ≤ cRD * g ^ 3)
    (hS : S = z ^ 2 * ((g : ℂ) ^ 2 * SB + ES)) (hES : ‖ES‖ ≤ cES * g ^ 3)
    (hq : ‖z ^ 2 * q‖ ≤ KB) (hSB : ‖SB‖ ≤ KB)
    (hn8 : f1cn ℓ cmu * g ≤ 1 / 8) (hn'8 : f1cn' L ℓ cZ cmu Cq cRQ cRL * g ≤ 1 / 8)
    (hζ8 : (ℓ ^ 2 / 7 + f1cw ℓ cmu Cq cRQ cRL) * g ≤ ρ) :
    let K0 := -(gr * z ^ 2) * c₀ - (κQz - κQg * c₀) - κLz
    let K1 := -(gr * z ^ 2) * δ - (κQy - κQg * δ) - κLy
    let K2 := nuS - A * (msqR : ℂ) + 4 * (gr * z ^ 2) * δ - (κQnu + 4 * κQg * δ) - κLnu
    let K3 := gr * z ^ 2 - κQg - (S + (gr * z ^ 2) ^ 2 * q +
      4 * C1 * (gr * z ^ 2) * (nuS - A * msqR + 4 * (gr * z ^ 2) * δ)) - κDg
    |(K3 / (z * (1 + clampDisk ρ ((K0 + K1) / z))) ^ 2 * (1 + nCor K2 (w1 + C1))).re - g -
        (2 * (z * (c₀ + δ)) - (z ^ 2 * q + SB) + 16 * (z ^ 2 * δ * w1)).re * g ^ 2| ≤
      32 / 7 * eA * g ^ 2 + f1c3s L ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES em * g ^ 3 := by
  intro K0 K1 K2 K3
  have hLj : 0 < Lj := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hap
  set a := ‖z‖ with ha
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hg3 : g ^ 3 ≤ g ^ 2 := by nlinarith [sq_nonneg g]
  have hLLj : 0 < (L : ℝ) ^ 2 * Lj := by positivity
  -- `n`
  have hnw : ‖4 * nuS * w1‖ ≤ f1cn ℓ cmu * g := by
    have e : 4 * nuS * w1 = 4 * (nuS / z) * (z * w1) := by field_simp
    rw [e, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    have h1 : ‖nuS / z‖ ≤ cmu * g / Lj := by
      rw [le_div_iff₀ hLj]
      have := hnuS
      rw [show ‖nuS / z‖ * ((L : ℝ) ^ 2 * Lj) = (L : ℝ) ^ 2 * (‖nuS / z‖ * Lj) by ring] at this
      exact le_of_mul_le_mul_left this (by linarith)
    calc 4 * ‖nuS / z‖ * ‖z * w1‖ ≤ 4 * (cmu * g / Lj) * (ℓ ^ 2 * Lj) := by gcongr
      _ = f1cn ℓ cmu * g := by unfold f1cn; field_simp
  set n := nCor nuS w1 with hndef
  have hn : n = 4 * nuS * w1 := by rw [hndef, nCor, clampDisk_of_le (hnw.trans hn8)]
  have hnb : ‖n‖ ≤ f1cn ℓ cmu * g := by rw [hn]; exact hnw
  have h1n : 7 / 8 ≤ ‖1 + n‖ := norm_one_add_nCor _ _
  have h1n0 : 1 + n ≠ 0 := one_add_nCor_ne _ _
  have hgr : gr = (g : ℂ) / (1 + n) := by rw [hG]; field_simp
  have hgrb : ‖gr‖ ≤ 8 / 7 * g := by
    rw [hgr, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0,
      div_le_iff₀ (by linarith)]
    nlinarith
  -- `κ'_ν/z`
  set P := (L : ℝ) ^ 2 * Lj with hPdef
  have hQ1 := hb_inv1 hCq hRQ0 hℓ2 hap haZp hr
  have hQ2 := hb_inv2 hCq hRQ0 hℓ2 hap haZp hr
  have hL0 := hb_inv0 (Cq := Cq) (R := RL) hℓ2 hap
  have hD0 := hb_inv0' (Cq := CqD) (R := RD) hℓ2 hap
  have hRQg : RQ ≤ cRQ * g := hRQ.trans (by nlinarith [sq_nonneg g])
  have hRLg : RL ≤ cRL * g := hRL.trans (by nlinarith)
  have b1 : ‖A * (msqR : ℂ) / z‖ * P ≤ (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) := by
    rw [mul_div_right_comm, norm_mul, Complex.norm_real, Real.norm_eq_abs, hPdef]
    have h0 : 0 ≤ 16 / 7 * (cZ * g) := by positivity
    calc ‖A / z‖ * |msqR| * ((L : ℝ) ^ 2 * Lj) = (L : ℝ) ^ 2 * (‖A / z‖ * (|msqR| * Lj)) := by ring
      _ ≤ (L : ℝ) ^ 2 * (16 / 7 * (cZ * g) * 1) := by gcongr
      _ = _ := by ring
  have b2 : ‖4 * (gr * z ^ 2) * δ / z‖ * P ≤ ℓ ^ 2 / 7 * g := by
    have e : 4 * (gr * z ^ 2) * δ / z = 4 * gr * (z * δ) := by field_simp
    rw [e, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    calc 4 * ‖gr‖ * ‖z * δ‖ * P = 4 * ‖gr‖ * (‖z * δ‖ * P) := by ring
      _ ≤ 4 * (8 / 7 * g) * (ℓ ^ 2 / 32) := by gcongr
      _ = _ := by ring
  have b3 : ‖κQnu / z‖ * P ≤ (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) := by
    rw [norm_div, ← ha, hPdef]
    have h1 : ‖κQnu‖ / a ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / Lj / a := div_le_div_of_nonneg_right q3 hap.le
    calc ‖κQnu‖ / a * ((L : ℝ) ^ 2 * Lj) ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / Lj / a * ((L : ℝ) ^ 2 * Lj) :=
          mul_le_mul_of_nonneg_right h1 hLLj.le
      _ = (L : ℝ) ^ 2 * (Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / a) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ1 (by positivity)
  have b4 : ‖4 * κQg * δ / z‖ * P ≤ 8 / 49 * (Cq * RQ / ℓ ^ 2) := by
    have e : 4 * κQg * δ / z = 4 * κQg * (z * δ) / z ^ 2 := by field_simp
    rw [e, norm_div, norm_mul, norm_mul, norm_pow, ← ha]; simp only [Complex.norm_ofNat]
    have h1 : ‖κQg‖ / a ^ 2 ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) :=
      (div_le_div_of_nonneg_right q4 (by positivity)).trans hQ2
    calc 4 * ‖κQg‖ * ‖z * δ‖ / a ^ 2 * P = 4 * (‖κQg‖ / a ^ 2) * (‖z * δ‖ * P) := by ring
      _ ≤ 4 * (64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2)) * (ℓ ^ 2 / 32) := by gcongr
      _ = _ := by field_simp; ring
  have b5 : ‖κLnu / z‖ * P ≤ Cq * RL / ℓ ^ 2 := by
    rw [norm_div, ← ha, ← hL0]
    have h1 : ‖κLnu‖ / a ≤ Cq * (ℓ ^ 2 / a)⁻¹ * RL / P / a := div_le_div_of_nonneg_right l3 hap.le
    calc ‖κLnu‖ / a * P ≤ Cq * (ℓ ^ 2 / a)⁻¹ * RL / P / a * P := mul_le_mul_of_nonneg_right h1 hLLj.le
      _ = _ := by field_simp
  have hK2b : ‖K2 / z‖ * P ≤ f1cK L ℓ cZ cmu Cq cRQ cRL * g := by
    have e : K2 / z = nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z -
        (κQnu / z + 4 * κQg * δ / z) - κLnu / z := by simp only [K2]; ring
    rw [e]
    have hsum : ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z -
        (κQnu / z + 4 * κQg * δ / z) - κLnu / z‖ ≤
        ‖nuS / z‖ + ‖A * (msqR : ℂ) / z‖ + ‖4 * (gr * z ^ 2) * δ / z‖ +
          (‖κQnu / z‖ + ‖4 * κQg * δ / z‖) + ‖κLnu / z‖ :=
      (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) (norm_add_le _ _))) le_rfl)
    have hP := mul_le_mul_of_nonneg_right hsum hLLj.le
    have h1 : Cq * RQ / ℓ ^ 2 ≤ Cq * cRQ / ℓ ^ 2 * g := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr
    have h2 : Cq * RL / ℓ ^ 2 ≤ Cq * cRL / ℓ ^ 2 * g := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr
    have hcq : 0 ≤ Cq * RQ / ℓ ^ 2 := by positivity
    unfold f1cK
    have e3 : ((L : ℝ) ^ 2 * (cmu + 3 * cZ) + ℓ ^ 2 / 7 +
        (2 * (L : ℝ) ^ 2 * Cq * cRQ + Cq * cRL) / ℓ ^ 2) * g =
        (L : ℝ) ^ 2 * (cmu * g) + (L : ℝ) ^ 2 * (3 * (cZ * g)) + ℓ ^ 2 / 7 * g +
          2 * (L : ℝ) ^ 2 * (Cq * cRQ / ℓ ^ 2 * g) + Cq * cRL / ℓ ^ 2 * g := by ring
    rw [e3]
    have hcz : 0 ≤ cZ * g := by positivity
    have hL2 : 0 ≤ (L : ℝ) ^ 2 := by positivity
    have k1 : (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) ≤ (L : ℝ) ^ 2 * (3 * (cZ * g)) :=
      mul_le_mul_of_nonneg_left (by linarith) hL2
    have k2 : (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) ≤
        2 * (L : ℝ) ^ 2 * (Cq * cRQ / ℓ ^ 2 * g) := by
      have : (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) ≤
          2 * (L : ℝ) ^ 2 * (Cq * RQ / ℓ ^ 2) := by nlinarith
      exact this.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    linarith [hP, hnuS, b1, b2, b3, b4, b5, k1, k2, h2]
  -- `n'`
  have hzW : ‖z * (w1 + C1)‖ ≤ ℓ ^ 2 * P := by
    rw [mul_add]; refine (norm_add_le _ _).trans ?_
    have h1 : ℓ ^ 2 * Lj ≤ ℓ ^ 2 * P / 4 := by
      rw [hPdef]; have := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ ℓ ^ 2 * Lj)
      linarith
    have h2 : 9 / 16 * ℓ ^ 2 * ((L : ℝ) ^ 2 * Lj) = 9 / 16 * (ℓ ^ 2 * P) := by rw [hPdef]; ring
    have h3 : 0 ≤ ℓ ^ 2 * P := by positivity
    linarith [hzw1, hzC1]
  have hn'w : ‖4 * K2 * (w1 + C1)‖ ≤ f1cn' L ℓ cZ cmu Cq cRQ cRL * g := by
    have e : 4 * K2 * (w1 + C1) = 4 * (K2 / z) * (z * (w1 + C1)) := by field_simp
    rw [e, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    unfold f1cn'
    calc 4 * ‖K2 / z‖ * ‖z * (w1 + C1)‖ ≤ 4 * ‖K2 / z‖ * (ℓ ^ 2 * P) := by gcongr
      _ = 4 * (‖K2 / z‖ * P) * ℓ ^ 2 := by ring
      _ ≤ 4 * (f1cK L ℓ cZ cmu Cq cRQ cRL * g) * ℓ ^ 2 := by gcongr
      _ = _ := by ring
  set n' := nCor K2 (w1 + C1) with hn'def
  have hn' : n' = 4 * K2 * (w1 + C1) := by rw [hn'def, nCor, clampDisk_of_le (hn'w.trans hn'8)]
  have hn'b : ‖n'‖ ≤ f1cn' L ℓ cZ cmu Cq cRQ cRL * g := by rw [hn']; exact hn'w
  have h1n' : ‖1 + n'‖ ≤ 9 / 8 := by
    refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith [hn'b.trans hn'8]
  -- the field strength `ζ_{j+1}`
  have hP1 : 1 ≤ P := by
    rw [hPdef]; nlinarith [hL4, hLj1]
  have hzδ1 : ‖z * δ‖ ≤ ℓ ^ 2 / 32 := by
    have h0 := norm_nonneg (z * δ)
    have : ‖z * δ‖ * 1 ≤ ‖z * δ‖ * P := mul_le_mul_of_nonneg_left hP1 h0
    linarith
  set c := z * (c₀ + δ) with hcdef
  have hcb : ‖c‖ ≤ ℓ ^ 2 / 8 := by
    rw [hcdef, mul_add]; refine (norm_add_le _ _).trans ?_; linarith
  set rw0 := (-(κQz + κQy) + κQg * (c₀ + δ) - (κLz + κLy)) / z with hrw0
  have hrw0b : ‖rw0‖ ≤ (3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 * g ^ 2 := by
    have e : rw0 = -(κQz / z) - κQy / z + κQg * c / z ^ 2 - κLz / z - κLy / z := by
      rw [hrw0, hcdef]; field_simp; ring
    rw [e]
    have a1 : ‖κQz / z‖ ≤ 8 / 7 * (Cq * RQ / ℓ ^ 2) := by
      rw [norm_div, ← ha]; exact (div_le_div_of_nonneg_right q1 hap.le).trans hQ1
    have a2 : ‖κQy / z‖ ≤ 8 / 7 * (Cq * RQ / ℓ ^ 2) := by
      rw [norm_div, ← ha]; exact (div_le_div_of_nonneg_right q2 hap.le).trans hQ1
    have a3 : ‖κQg * c / z ^ 2‖ ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) * (ℓ ^ 2 / 8) := by
      rw [norm_div, norm_mul, norm_pow, ← ha, mul_div_right_comm]
      have h1 : ‖κQg‖ / a ^ 2 ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) :=
        (div_le_div_of_nonneg_right q4 (by positivity)).trans hQ2
      exact mul_le_mul h1 hcb (norm_nonneg _) (by positivity)
    have a4 : ‖κLz / z‖ ≤ Cq * RL / ℓ ^ 2 := by
      rw [norm_div, ← ha, ← hL0]; exact div_le_div_of_nonneg_right l1 hap.le
    have a5 : ‖κLy / z‖ ≤ Cq * RL / ℓ ^ 2 := by
      rw [norm_div, ← ha, ← hL0]; exact div_le_div_of_nonneg_right l2 hap.le
    have hsum : ‖-(κQz / z) - κQy / z + κQg * c / z ^ 2 - κLz / z - κLy / z‖ ≤
        ‖κQz / z‖ + ‖κQy / z‖ + ‖κQg * c / z ^ 2‖ + ‖κLz / z‖ + ‖κLy / z‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
          (norm_neg _).le le_rfl)) le_rfl)) le_rfl)) le_rfl)
    have e3 : 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) * (ℓ ^ 2 / 8) = 8 / 49 * (Cq * RQ / ℓ ^ 2) := by
      field_simp; ring
    have h1 : Cq * RQ / ℓ ^ 2 ≤ Cq * cRQ / ℓ ^ 2 * g ^ 2 := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr; exact hRQ.trans (mul_le_mul_of_nonneg_left hg3 hcRQ)
    have h2 : Cq * RL / ℓ ^ 2 ≤ Cq * cRL / ℓ ^ 2 * g ^ 2 := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr
    have e4 : (3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 * g ^ 2 =
        3 * (Cq * cRQ / ℓ ^ 2 * g ^ 2) + 2 * (Cq * cRL / ℓ ^ 2 * g ^ 2) := by ring
    rw [e4]
    have hq0 : 0 ≤ Cq * RQ / ℓ ^ 2 := by positivity
    linarith [hsum, a1, a2, a3, a4, a5, e3, h1, h2]
  have hK01 : (K0 + K1) / z = -(gr * c) + rw0 := by
    simp only [K0, K1]; rw [hrw0, hcdef]; field_simp; ring
  have hgrn : (g : ℂ) - gr = gr * n := by rw [hG]; ring
  set rw := rw0 + c * (gr * n) with hrwdef
  have hw_eq : (K0 + K1) / z = -(c * g) + rw := by
    rw [hK01, hrwdef, ← hgrn]; ring
  have hcw : ‖rw‖ ≤ f1cw ℓ cmu Cq cRQ cRL * g ^ 2 := by
    rw [hrwdef]; refine (norm_add_le _ _).trans ?_
    have h1 : ‖c * (gr * n)‖ ≤ ℓ ^ 2 / 8 * (8 / 7 * g) * (f1cn ℓ cmu * g) := by
      rw [norm_mul c, norm_mul gr n, ← mul_assoc]
      exact mul_le_mul (mul_le_mul hcb hgrb (norm_nonneg _) (by positivity)) hnb (norm_nonneg _)
        (by positivity)
    unfold f1cw
    have e : ℓ ^ 2 / 8 * (8 / 7 * g) * (f1cn ℓ cmu * g) = ℓ ^ 2 * f1cn ℓ cmu / 7 * g ^ 2 := by ring
    rw [e] at h1
    have e2 : ((3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 + ℓ ^ 2 * f1cn ℓ cmu / 7) * g ^ 2 =
        (3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 * g ^ 2 + ℓ ^ 2 * f1cn ℓ cmu / 7 * g ^ 2 := by ring
    rw [e2]; linarith
  have hwin : ‖(K0 + K1) / z‖ ≤ ρ := by
    rw [hw_eq]; refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]
    have h1 : ‖c‖ * g ≤ ℓ ^ 2 / 7 * g := mul_le_mul_of_nonneg_right (by linarith) hg0
    have hcw0 : 0 ≤ f1cw ℓ cmu Cq cRQ cRL := by unfold f1cw f1cn; positivity
    have h2 : f1cw ℓ cmu Cq cRQ cRL * g ^ 2 ≤ f1cw ℓ cmu Cq cRQ cRL * g :=
      mul_le_mul_of_nonneg_left hg2 hcw0
    have e : (ℓ ^ 2 / 7 + f1cw ℓ cmu Cq cRQ cRL) * g = ℓ ^ 2 / 7 * g + f1cw ℓ cmu Cq cRQ cRL * g := by
      ring
    linarith
  have hw : clampDisk ρ ((K0 + K1) / z) = (K0 + K1) / z := clampDisk_of_le hwin
  rw [hw]
  -- the expansion of `P`
  have hid := P_identity2 (z := z) (gr := gr) (n := n) (n' := n') (K2 := K2) (K3 := K3) (nu := nuS)
    (a := A) (msq := (msqR : ℂ)) (w1 := w1) (C1 := C1) (δ := δ) (κQg := κQg) (κQnu := κQnu)
    (κLnu := κLnu) (κDg := κDg) (S := S) (q := q) (SB := SB) (ES := ES) (G := (g : ℂ)) hz0 hG hn
    hn' rfl rfl hS
  -- the tadpole is `O(1)`
  have hT2 : ‖z ^ 2 * δ * w1‖ ≤ f1eBs ℓ := by
    have e : z ^ 2 * δ * w1 = (z * δ) * (z * w1) := by ring
    rw [e, norm_mul]
    have h1 : ℓ ^ 2 * Lj ≤ ℓ ^ 2 * P := by
      have : Lj ≤ P := by rw [hPdef]; exact le_mul_of_one_le_left hLj.le (by linarith only [hL4])
      exact mul_le_mul_of_nonneg_left this hℓ2.le
    have h0 := norm_nonneg (z * δ)
    calc ‖z * δ‖ * ‖z * w1‖ ≤ ‖z * δ‖ * (ℓ ^ 2 * P) :=
          mul_le_mul_of_nonneg_left (hzw1.trans h1) h0
      _ = (‖z * δ‖ * P) * ℓ ^ 2 := by ring
      _ ≤ ℓ ^ 2 / 32 * ℓ ^ 2 := mul_le_mul_of_nonneg_right hzδ hℓ2.le
      _ = f1eBs ℓ := by unfold f1eBs; ring
  -- the remainder bounds
  have hgg : ‖gr ^ 2 - (g : ℂ) ^ 2‖ ≤ 3 * f1cn ℓ cmu * g ^ 3 := by
    have e : gr ^ 2 - (g : ℂ) ^ 2 = -((g : ℂ) ^ 2 * (n * (2 + n)) / (1 + n) ^ 2) := by
      rw [hgr]; field_simp; ring
    rw [e, norm_neg, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hg0]
    have h2 : ‖2 + n‖ ≤ 17 / 8 := by
      refine (norm_add_le _ _).trans ?_; simp only [Complex.norm_ofNat]; linarith [hnb.trans hn8]
    have h3 : (49 / 64 : ℝ) ≤ ‖1 + n‖ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 8) h1n 2
      linarith only [this, show ((7 : ℝ) / 8) ^ 2 = 49 / 64 by norm_num]
    rw [div_le_iff₀ (by linarith only [h3])]
    have hcn0 : 0 ≤ f1cn ℓ cmu * g := (norm_nonneg _).trans hnb
    have h4 : ‖n‖ * ‖2 + n‖ ≤ f1cn ℓ cmu * g * (17 / 8) := mul_le_mul hnb h2 (norm_nonneg _) hcn0
    have hA' : g ^ 2 * (‖n‖ * ‖2 + n‖) ≤ g ^ 2 * (f1cn ℓ cmu * g * (17 / 8)) :=
      mul_le_mul_of_nonneg_left h4 (sq_nonneg g)
    have hB : 3 * f1cn ℓ cmu * g ^ 3 * (49 / 64) ≤ 3 * f1cn ℓ cmu * g ^ 3 * ‖1 + n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by unfold f1cn; positivity)
    have h5 : 0 ≤ f1cn ℓ cmu * g ^ 3 := by unfold f1cn; positivity
    linarith only [hA', hB, h5]
  have hT3 : ‖(κQnu + 4 * κQg * δ + κLnu) * (w1 + C1)‖ ≤
      (2 * (L : ℝ) ^ 2 * Cq * cRQ + Cq * cRL) * g ^ 2 := by
    have e : (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) =
        (κQnu / z + 4 * κQg * δ / z + κLnu / z) * (z * (w1 + C1)) := by field_simp
    rw [e, norm_mul]
    have hs : ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * P ≤
        (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) + Cq * RL / ℓ ^ 2 := by
      have h0 : ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ ≤
          ‖κQnu / z‖ + ‖4 * κQg * δ / z‖ + ‖κLnu / z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      have := mul_le_mul_of_nonneg_right h0 hLLj.le
      linarith only [this, b3, b4, b5]
    have h0 : 0 ≤ ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ := norm_nonneg _
    calc ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * ‖z * (w1 + C1)‖ ≤
        ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * (ℓ ^ 2 * P) := by gcongr
      _ = (‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * P) * ℓ ^ 2 := by ring
      _ ≤ ((L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) +
          Cq * RL / ℓ ^ 2) * ℓ ^ 2 := by gcongr
      _ = ((L : ℝ) ^ 2 * (8 / 7) + 8 / 49) * (Cq * RQ) + Cq * RL := by field_simp
      _ ≤ 2 * (L : ℝ) ^ 2 * (Cq * (cRQ * g ^ 2)) + Cq * (cRL * g ^ 2) := by
          have hRQ2 : RQ ≤ cRQ * g ^ 2 := hRQ.trans (mul_le_mul_of_nonneg_left hg3 hcRQ)
          have h1 : Cq * RQ ≤ Cq * (cRQ * g ^ 2) := mul_le_mul_of_nonneg_left hRQ2 hCq
          have h2 : Cq * RL ≤ Cq * (cRL * g ^ 2) := mul_le_mul_of_nonneg_left hRL hCq
          have h3 : ((L : ℝ) ^ 2 * (8 / 7) + 8 / 49) * (Cq * RQ) ≤ 2 * (L : ℝ) ^ 2 * (Cq * RQ) := by
            have h0 : 0 ≤ Cq * RQ := by positivity
            have := mul_le_mul_of_nonneg_right hL4 h0
            linarith only [this, h0]
          have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) ^ 2)
          linarith only [h2, h3, h4]
      _ = _ := by ring
  have hT4 : ‖C1 * (nuS - A * msqR + 4 * (gr * z ^ 2) * δ)‖ ≤ f1cCnu L ℓ cZ cmu * g := by
    have e : C1 * (nuS - A * msqR + 4 * (gr * z ^ 2) * δ) =
        (z * C1) * (nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z) := by field_simp
    rw [e, norm_mul]
    have hs : ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ * P ≤
        (L : ℝ) ^ 2 * (cmu * g) + (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) + ℓ ^ 2 / 7 * g := by
      have h0 : ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ ≤
          ‖nuS / z‖ + ‖A * (msqR : ℂ) / z‖ + ‖4 * (gr * z ^ 2) * δ / z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      have := mul_le_mul_of_nonneg_right h0 hLLj.le
      linarith only [this, hnuS, b1, b2]
    have h0 : 0 ≤ ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ := norm_nonneg _
    unfold f1cCnu
    calc ‖z * C1‖ * ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ ≤
        9 / 16 * ℓ ^ 2 * P * ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ := by
          rw [hPdef]; gcongr
      _ = 9 / 16 * ℓ ^ 2 * (‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ * P) := by ring
      _ ≤ 9 / 16 * ℓ ^ 2 * ((L : ℝ) ^ 2 * (cmu * g) + (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) +
          ℓ ^ 2 / 7 * g) := by gcongr
      _ ≤ _ := by
          have hcz : 0 ≤ cZ * g := by positivity
          have : (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) ≤ (L : ℝ) ^ 2 * (3 * (cZ * g)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h9 : (0 : ℝ) ≤ 9 / 16 * ℓ ^ 2 := by positivity
          linarith only [mul_le_mul_of_nonneg_left this h9]
  have hQD : ‖(κQg + κDg) / z ^ 2‖ ≤ (64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4 * g ^ 3 := by
    rw [add_div]; refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_pow, ← ha]
    have h1 : ‖κQg‖ / a ^ 2 ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) :=
      (div_le_div_of_nonneg_right q4 (by positivity)).trans hQ2
    have h2 : ‖κDg‖ / a ^ 2 ≤ CqD * RD / (ℓ ^ 2) ^ 2 := by
      rw [← hD0]; exact div_le_div_of_nonneg_right hDg (by positivity)
    have e : (64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4 * g ^ 3 =
        64 / 49 * (Cq * (cRQ * g ^ 3) / (ℓ ^ 2) ^ 2) + CqD * (cRD * g ^ 3) / (ℓ ^ 2) ^ 2 := by
      field_simp
    rw [e]
    have h3 : 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) ≤ 64 / 49 * (Cq * (cRQ * g ^ 3) / (ℓ ^ 2) ^ 2) := by
      gcongr
    have h4 : CqD * RD / (ℓ ^ 2) ^ 2 ≤ CqD * (cRD * g ^ 3) / (ℓ ^ 2) ^ 2 := by gcongr
    linarith only [h1, h2, h3, h4]
  have hrP := rP_bound2 (L2 := (L : ℝ) ^ 2) hg0
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]) hgrb hT1 hT2 hT3 hT4 hn'b h1n'
    hES hgg hq hSB hQD
  -- the algebra of (F1)
  set Pv := K3 / z ^ 2 * (1 + n') with hPv
  set p₂ := -(z ^ 2 * q + SB) + 16 * (z ^ 2 * δ * w1) with hp₂
  have hPe : Pv = (g : ℂ) + p₂ * (g : ℂ) ^ 2 + (Pv - g - p₂ * (g : ℂ) ^ 2) := by ring
  have hrP' : ‖Pv - g - p₂ * (g : ℂ) ^ 2‖ ≤ 32 / 7 * eA * g ^ 2 +
      f1cPs L ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES * g ^ 3 := by
    have e : Pv - g - p₂ * (g : ℂ) ^ 2 =
        K3 / z ^ 2 * (1 + n') - g + (z ^ 2 * q + SB - 16 * (z ^ 2 * δ * w1)) * (g : ℂ) ^ 2 := by
      rw [hPv, hp₂]; ring
    rw [e, hid]
    refine hrP.trans (le_of_eq ?_)
    unfold f1cPs f1eBs; ring
  have hp₂b : ‖p₂‖ ≤ ℓ ^ 2 / 8 + 2 * KB + ℓ ^ 4 / 2 := by
    rw [hp₂]; refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul]; simp only [Complex.norm_ofNat]
    have h1 : ‖z ^ 2 * q + SB‖ ≤ 2 * KB := (norm_add_le _ _).trans (by linarith only [hq, hSB])
    have h2 : 16 * ‖z ^ 2 * δ * w1‖ ≤ ℓ ^ 4 / 2 := by
      have := hT2; unfold f1eBs at this; linarith only [this]
    have : 0 ≤ ℓ ^ 2 / 8 := by positivity
    linarith only [h1, h2, this]
  have hw8 : ‖(K0 + K1) / z‖ ≤ 1 / 8 := hwin.trans hρ8
  have hℓ4 : 0 ≤ ℓ ^ 4 / 2 := by positivity
  have hfin := F1_alg2 hg0 hg1 (by positivity) heAm
    (by unfold f1cPs f1eBs f1cCnu f1cn' f1cK f1cn; positivity) (by positivity)
    (by unfold f1cw f1cn; positivity) hPe hrP' hw_eq hcw hw8
    (hcb.trans (by linarith)) hp₂b
  have e1 : K3 / (z * (1 + (K0 + K1) / z)) ^ 2 * (1 + n') = Pv / (1 + (K0 + K1) / z) ^ 2 := by
    have h1 : 1 + (K0 + K1) / z ≠ 0 := by
      intro h; have := norm_nonneg ((K0 + K1) / z)
      have h2 : (K0 + K1) / z = -1 := by linear_combination h
      rw [h2, norm_neg, norm_one] at hw8; norm_num at hw8
    rw [hPv]; field_simp
  rw [e1]
  have e2 : (2 * c - (z ^ 2 * q + SB) + 16 * (z ^ 2 * δ * w1)).re = (p₂ + 2 * c).re := by
    rw [hp₂]; ring_nf
  rw [e2]
  refine hfin.trans (le_of_eq ?_)
  unfold f1c3s; ring

end

end Step2
