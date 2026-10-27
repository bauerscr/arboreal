import Step2.Last.FlowLastLip3

/-!
# The Lipschitz layer at the step `j = N - 2`, part 4 (namespace `Step2.LL`)

Copies of the final-step estimates of `Step2/Lip/FlowFadeHist` and `FlowZetaHist` (`LGd_hist_w`,
`pieces_hist_w`, `dζ_hist_w`, `Lm_hist_z`, …) for the weakened `Run` of `Step2.LL`.
-/
-- from Step2/Lip/FlowFadeHist.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

/-- `Θ_j` at the final step, from the error bounds. -/
theorem Run.theta_j_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W₁ Z : ℝ} (hM : 0 ≤ M)
    (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M))
    (heW : eWH R j t t' ≤ (e + ε) * W₁ * M) (hew : ewH R j t t' ≤ Z * M) :
    thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') ≤
      (1 + Real.exp 1) * ‖(t' j).2.2 - (t j).2.2‖ + (e + ε) * kTh R.ℓ (cmu Λ cm)
        (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z *
          (|(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) := by
  have HC := H.cmp j le_rfl
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have hcTh : 0 ≤ cTh R.ℓ cw (cx κ cT) := by
    have := HC.hcw; have := HC.hcx
    unfold cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hdn := H.dn_le (le_refl j)
  exact theta_final HC.hℓ HC.hcmu hcTh (by have := H.hKc; positivity) HC.he.le H.he1 H.hε0.le
    HC.hε1 hM hV hZ hW₁ (abs_nonneg _) (abs_nonneg _) hev hew heW
    (eζ_le_ev HC.H HC.H') (evH_nonneg j) (ewH_nonneg j) (norm_nonneg _) (norm_nonneg _) hdn
    hΔ (thetaH_le HC)


/-- **The common pieces at the final step.** -/
theorem pieces_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W₁ Z K : ℝ} (hM : 0 ≤ M)
    (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M))
    (heW : eWH R j t t' ≤ (e + ε) * W₁ * M) (hew : ewH R j t t' ≤ Z * M)
    (hK1 : 1 + Real.exp 1 ≤ K)
    (hK2 : kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z ≤ K)
    (hK3 : 2 * cmu Λ cm * R.ℓ ^ 2 ≤ K) (hK4 : 2 * R.ℓ ^ 2 ≤ K)
    (hK5 : 4 * cmu Λ cm * R.ℓ ^ 2 * V + 3 * cmu Λ cm * Z ≤ K) :
    Pieces K (e + ε) ε ‖(t' j).2.2 - (t j).2.2‖ |(t' j).1 - (t j).1| |(t' j).2.1 - (t j).2.1| M
      ‖ghat (sdH R j t') - ghat (sdH R j t)‖ (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t')) := by
  have HC := H.cmp j le_rfl
  have he := HC.he
  have hε := H.hε0
  have hε1 := HC.hε1
  have hcmu := HC.hcmu
  have hE := (Real.exp_pos 1).le
  have hK0 : 1 ≤ K := by linarith
  set dx := ‖(t' j).2.2 - (t j).2.2‖
  set dg := |(t' j).1 - (t j).1|
  set dμ := |(t' j).2.1 - (t j).2.1|
  have hdx : 0 ≤ dx := norm_nonneg _
  have hdg : 0 ≤ dg := abs_nonneg _
  have hdμ : 0 ≤ dμ := abs_nonneg _
  have hQ : 0 ≤ dx + dg + dμ + M := by linarith
  have hσ : 0 ≤ e + ε := by linarith
  refine ⟨hK0, hσ, by linarith [H.he1], by linarith, hε.le, hdx, hdg, hdμ, hM, ?_, ?_,
    thetaH_nonneg HC, norm_nonneg _⟩
  · have h1 := dĝ_hist H hM hV hZ hev hew
    have h2 : 8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤ 4 * K * (dx + dg + dμ + M) := by
      have b1 : 8 * cmu Λ cm * R.ℓ ^ 2 * dg ≤ 4 * K * dg :=
        mul_le_mul_of_nonneg_right (by linarith) hdg
      have b2 : 8 * R.ℓ ^ 2 * dμ ≤ 4 * K * dμ := mul_le_mul_of_nonneg_right (by linarith) hdμ
      have b3 : (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤ 4 * K * M :=
        mul_le_mul_of_nonneg_right (by have := mul_nonneg hcmu hZ; linarith) hM
      have b4 : 0 ≤ 4 * K * dx := by positivity
      have e1 : 4 * K * (dx + dg + dμ + M) = 4 * K * dx + 4 * K * dg + 4 * K * dμ + 4 * K * M := by ring
      linarith only [b1, b2, b3, b4, e1]
    have h3 : ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) ≤ (e + ε) * (4 * K * (dx + dg + dμ + M)) :=
      mul_le_mul (by linarith) h2 (by positivity) hσ
    have e1 : (e + ε) * (4 * K) * (dx + dg + dμ + M) = (e + ε) * (4 * K * (dx + dg + dμ + M)) := by ring
    linarith only [h1, h3, e1]
  · have h1 := H.theta_j_w hM hV hW₁ hZ hev hΔ heW hew
    have b1 : (1 + Real.exp 1) * dx ≤ K * dx := mul_le_mul_of_nonneg_right hK1 hdx
    have b2 : kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z * (dg + dμ + M) ≤
        K * (dx + dg + dμ + M) :=
      mul_le_mul hK2 (by linarith) (by positivity) (by linarith)
    have b3 := mul_le_mul_of_nonneg_left b2 hσ
    have e1 : (e + ε) * kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z *
        (dg + dμ + M) = (e + ε) * (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8)
          V W₁ Z * (dg + dμ + M)) := by ring
    have e2 : (e + ε) * K * (dx + dg + dμ + M) = (e + ε) * (K * (dx + dg + dμ + M)) := by ring
    linarith only [h1, b1, b3, e1, e2]


/-- The common bound on `δζ₁`. -/
theorem dζ_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (F : FinOne R j t ε b₁ cz cmuv)
    (F' : FinOne R j t' ε b₁ cz cmuv) {M V β K : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4))
    (hK8 : 8 * β ≤ K) (hK9 : 3 * R.ℓ ^ 2 / 16 ≤ K) (hK10 : 4 * (2 * Kc * (L : ℝ) ^ 8) * V ≤ K) :
    ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ ≤ K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
      K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + (e + ε) * K * M := by
  have HC := H.cmp j le_rfl
  have h1 := (dζ_eq_le F F').trans (ev_succ_le HC hkap)
  rw [← hβd] at h1
  have hΘ := thetaH_nonneg HC
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have hg : |(sdH R j t).g| ≤ ε := by
      show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
    linarith
  have hε := H.hε0
  have he := HC.he
  have a1 : 8 * β * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') ≤
      K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := mul_le_mul_of_nonneg_right hK8 hΘ
  have a2 : 3 * (R.ℓ / 4) ^ 2 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤
      K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ :=
    mul_le_mul_of_nonneg_right (by linarith [show 3 * (R.ℓ / 4) ^ 2 = 3 * R.ℓ ^ 2 / 16 by ring])
      (norm_nonneg _)
  have a3 : 3 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ (e + ε) * K * M := by
    have b1 := mul_le_mul (mul_le_mul_of_nonneg_left hĝ (by norm_num : (0 : ℝ) ≤ 3)) hΔ
      (sq_nonneg _) (by positivity)
    have hKc := H.hKc
    have b2 : 3 * (8 / 7 * ε) * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) ≤ ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V * M) := by
      have : 0 ≤ ε * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) := by positivity
      nlinarith
    have b3 : ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V * M) ≤ (e + ε) * K * M := by
      have := mul_le_mul (show ε ≤ e + ε by linarith) hK10 (by positivity) (by linarith)
      have := mul_le_mul_of_nonneg_right this hM
      linarith only [this, show ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V * M) =
        ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V) * M by ring]
    linarith only [b1, b2, b3]
  linarith only [h1, a1, a2, a3]


/-- The common bound on `δ(ν̃ - L²μ)`. -/
theorem dY_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4)) :
    ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) - (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ ≤
      (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) * M +
        (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ +
        (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
  have HC := H.cmp j le_rfl
  have h1 := dY_le HC (kap_rem_scaled HC hkap)
  rw [← hβd] at h1
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have hg : |(sdH R j t).g| ≤ ε := by
      show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
    linarith
  have hm0 : 0 ≤ |R.msq| * ((L : ℝ) ^ j) ^ 2 := by positivity
  have a1 : 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' ≤
      2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V * M := by
    have := mul_le_mul_of_nonneg_left (hζIH0) (by positivity : (0 : ℝ) ≤ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2))
    linarith only [this, show 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * (V * M) =
      2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V * M by ring]
  have a2 : 2 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ 16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hĝ (by norm_num : (0 : ℝ) ≤ 2)) hΔ
      (sq_nonneg _) (by have := H.hε0; positivity)
    linarith only [this, show 2 * (8 / 7 * ε) * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) =
      16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M by ring]
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  set X := 4 * β * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t')
  set Y := R.ℓ ^ 2 / 8 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖
  have hsum : X + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' + Y +
      2 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ X + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V * M + Y +
        16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M := by linarith only [a1, a2]
  have := mul_le_mul_of_nonneg_left hsum hL2
  refine h1.trans (this.trans (le_of_eq ?_))
  simp only [X, Y]
  ring


/-- The bound on `δŵ_{j+1}`. -/
theorem dw_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) (hew : ewH R j t t' ≤ Z * M) :
    ‖whH R (j + 1) t' - whH R (j + 1) t‖ ≤
      (2 * R.ℓ ^ 2 * V + 2 * Z + 9 * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
  have HC := H.cmp j le_rfl
  have h1 : ewH R (j + 1) t t' ≤ _ := ew_succ_le HC
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have h2 := nW1H_sub_le HC.H HC.H' (H.whH_le le_rfl)
  have h3 : ‖nW1H R j t' - nW1H R j t‖ ≤ (2 * R.ℓ ^ 2 * V + 2 * Z) * M := by
    have b1 := mul_le_mul_of_nonneg_left (hζIH0) (by positivity : (0 : ℝ) ≤ 2 * R.ℓ ^ 2)
    have b2 := mul_le_mul_of_nonneg_left hew (by norm_num : (0 : ℝ) ≤ 9 / 8)
    have b3 : 9 / 8 * (Z * M) ≤ 2 * Z * M := by nlinarith [mul_nonneg hZ hM]
    linarith only [h2, b1, b2, b3, show (2 * R.ℓ ^ 2 * V + 2 * Z) * M =
      2 * R.ℓ ^ 2 * (V * M) + 2 * Z * M by ring]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have h4 : ‖nW1H R j t' - nW1H R j t‖ / (L : ℝ) ^ 2 ≤ (2 * R.ℓ ^ 2 * V + 2 * Z) * M :=
    (div_le_self (norm_nonneg _) hL1).trans h3
  show ewH R (j + 1) t t' ≤ _
  linarith only [h1, h4, hΔ, show (2 * R.ℓ ^ 2 * V + 2 * Z + 9 * (2 * Kc * (L : ℝ) ^ 8) * V) * M =
    (2 * R.ℓ ^ 2 * V + 2 * Z) * M + 9 * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) by ring]


/-- **`|δĝ - δg|`.** -/
theorem dĝd_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M) (hew : ewH R j t t' ≤ Z * M) :
    ‖(ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)‖ ≤
      ε * (8 * cmu Λ cm * R.ℓ ^ 2 * |(t' j).1 - (t j).1| + 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by
  have HC := H.cmp j le_rfl
  have hτ := ghat_nCor_le H
  have h1 := ghat_sub_sub_le (sdH R j t) (sdH R j t') (le_refl _)
    ((norm_nCor_le _ _).trans (by norm_num))
  have hg : |(sdH R j t).g| ≤ ε := by
    show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
  have hdn := H.dn_le (le_refl j)
  have hζ := (eζ_le_ev HC.H HC.H').trans hev
  have hε := H.hε0
  have hε1 := HC.hε1
  have hcmu := HC.hcmu
  have hℓ := HC.hℓ
  set dg := |(t' j).1 - (t j).1|
  set dμ := |(t' j).2.1 - (t j).2.1|
  set dn := ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t') - nCor ((t j).2.1 : ℂ) (nW1H R j t)‖
  have hdg : 0 ≤ dg := abs_nonneg _
  have hdn0 : 0 ≤ dn := norm_nonneg _
  have a1 : 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ * dg ≤ ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg) := by
    have := mul_le_mul_of_nonneg_right hτ hdg
    nlinarith
  have a2 : 2 * |(sdH R j t).g| * dn ≤ 2 * ε * dn := by
    have := mul_le_mul_of_nonneg_right hg hdn0
    linarith
  have a3 : dn ≤ 4 * R.ℓ ^ 2 * dμ + (8 * cmu Λ cm * R.ℓ ^ 2 * V + 9 / 2 * cmu Λ cm * Z) * M := by
    have b1 : cmu Λ cm * ε * (2 * R.ℓ ^ 2 * eζH R j t t' + 9 / 8 * ewH R j t t') ≤
        cmu Λ cm * 1 * (2 * R.ℓ ^ 2 * (V * M) + 9 / 8 * (Z * M)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hε1 hcmu)
        (add_le_add (mul_le_mul_of_nonneg_left hζ (by positivity))
          (mul_le_mul_of_nonneg_left hew (by norm_num)))
        (by have := norm_nonneg (zetaH R j t' - zetaH R j t); have := ewH_nonneg (R := R)
                (t := t) (t' := t') j; unfold eζH; positivity) (by positivity)
    have e1 : 4 * (R.ℓ ^ 2 * dμ + cmu Λ cm * 1 * (2 * R.ℓ ^ 2 * (V * M) + 9 / 8 * (Z * M))) =
        4 * R.ℓ ^ 2 * dμ + (8 * cmu Λ cm * R.ℓ ^ 2 * V + 9 / 2 * cmu Λ cm * Z) * M := by ring
    linarith only [hdn, b1, e1]
  have a4 : 2 * ε * dn ≤ ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by
    have := mul_le_mul_of_nonneg_left a3 (by positivity : (0 : ℝ) ≤ 2 * ε)
    have e1 : 2 * ε * (4 * R.ℓ ^ 2 * dμ + (8 * cmu Λ cm * R.ℓ ^ 2 * V + 9 / 2 * cmu Λ cm * Z) * M) =
        ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by ring
    linarith only [this, e1]
  have e3 : ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
      (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) = ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg) +
      ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by ring
  have h1' : ‖(ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)‖ ≤
      2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ * dg + 2 * |(sdH R j t).g| * dn := h1
  linarith only [h1', a1, a2, a4, e3]

set_option maxHeartbeats 1000000 in
/-- **(LG), difference form, along two histories.** -/
theorem LGd_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {b₁ : ℝ}
    (F : FinOne R j t ε b₁ cz (cmu Λ cm)) (F' : FinOne R j t' ε b₁ cz (cmu Λ cm))
    {M V W₁ Z β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hβ : 0 ≤ β)
    (hb : 0 ≤ b₁) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) (heW : eWH R j t t' ≤ (e + ε) * W₁ * M)
    (hew : ewH R j t t' ≤ Z * M) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4))
    (hs16 : ε * (cSz b₁ R.ℓ + cSn L b₁ cz R.ℓ (cmu Λ cm)) ≤ 1 / 16) :
    let K := cKa L β b₁ R.ℓ (cmu Λ cm) cz V Z (2 * Kc * (L : ℝ) ^ 8)
      (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z)
    |(rgData R).G j t - (rgData R).G j t' - ((t j).1 - (t' j).1)| ≤
      (e + ε) * (200 * K ^ 4) * |(t' j).1 - (t j).1| +
      (e + ε) * (200 * K ^ 4) * |(t' j).2.1 - (t j).2.1| + 500 * K ^ 4 * ‖(t' j).2.2 - (t j).2.2‖ +
      (e + ε) * (200 * K ^ 4) * M := by
  intro K
  have HC := H.cmp j le_rfl
  have hε := H.hε0
  have hε1 := HC.hε1
  have he := HC.he
  have hcmu := HC.hcmu
  have hcz := HC.H.hcz
  have hKc := H.hKc
  have hkTh : 0 ≤ kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z := by
    have := HC.hcw; have := HC.hcx
    unfold kTh cTh; have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, -, -, -, -, -, k20⟩ :=
    cKa_ge (β := β) (b₁ := b₁) (ℓ := R.ℓ) (cmu := cmu Λ cm) (cz := cz) (V := V) (Z := Z)
      (Λ0 := 2 * Kc * (L : ℝ) ^ 8) (kThv := kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT))
        (2 * Kc * (L : ℝ) ^ 8) V W₁ Z) L hβ hb hcmu hcz hV hZ (by positivity) hkTh
  have P := pieces_hist_w H hM hV hW₁ hZ hev hΔ heW hew k1 k2 k3 k4 k5
  set σ := e + ε
  set s := ε * (cSz b₁ R.ℓ + cSn L b₁ cz R.ℓ (cmu Λ cm))
  have hp1 : 0 ≤ cSz b₁ R.ℓ := by unfold cSz; positivity
  have hp4 : 0 ≤ cSn L b₁ cz R.ℓ (cmu Λ cm) := by
    unfold cSn cSν cSY; positivity
  have hs0 : 0 ≤ s := by positivity
  have hsz : ∀ {x : ℝ}, x ≤ ε * cSz b₁ R.ℓ → x ≤ s := fun h => h.trans (by
    have := mul_nonneg hε.le hp4
    linarith only [this, show s = ε * cSz b₁ R.ℓ + ε * cSn L b₁ cz R.ℓ (cmu Λ cm) by ring])
  have hsn : ∀ {x : ℝ}, x ≤ ε * cSn L b₁ cz R.ℓ (cmu Λ cm) → x ≤ s := fun h => h.trans (by
    have := mul_nonneg hε.le hp1
    linarith only [this, show s = ε * cSz b₁ R.ℓ + ε * cSn L b₁ cz R.ℓ (cmu Λ cm) by ring])
  have hG := G_core_d F.hO F'.hO hs16 (hsz F.ζ_le) (hsz F'.ζ_le) (hsn F.n_le) (hsn F'.n_le)
  have h3 := d3_le HC (kap_rem_scaled HC hkap)
  rw [← hβd] at h3
  have hζ := dζ_hist_w H F F' hM hV hev hΔ hβd hkap k8 k9 k10
  have hY := dY_hist_w H hM hV hev hΔ hβd hkap
  have hw := dw_hist_w H hM hV hZ hev hΔ hew
  -- `dν`
  have hν : ‖nuT R j t' - nuT R j t‖ ≤ K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
      |(t' j).2.1 - (t j).2.1| + ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + M) := by
    have e1 : nuT R j t' - nuT R j t = ((nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))) + (L : ℂ) ^ 2 * (((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) := by
      push_cast; ring
    have h1 := norm_add_le ((nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))) ((L : ℂ) ^ 2 * (((t' j).2.1 - (t j).2.1 : ℝ) : ℂ))
    rw [← e1] at h1
    have hLμ : ‖(L : ℂ) ^ 2 * (((t' j).2.1 - (t j).2.1 : ℝ) : ℂ)‖ = (L : ℝ) ^ 2 * |(t' j).2.1 - (t j).2.1| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [hLμ] at h1
    have hm1 := HC.hm
    have hΘ := thetaH_nonneg HC
    have hdĝ := norm_nonneg (ghat (sdH R j t') - ghat (sdH R j t))
    have hdμ := abs_nonneg ((t' j).2.1 - (t j).2.1)
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have c1 : (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) * M ≤ (L : ℝ) ^ 2 * (2 * V) * M := by
      have a := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 2 * V)
      have b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a hL2) hM
      have e1 : (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) * M =
          (L : ℝ) ^ 2 * (2 * V * (|R.msq| * ((L : ℝ) ^ j) ^ 2)) * M := by ring
      have e2 : (L : ℝ) ^ 2 * (2 * V) * M = (L : ℝ) ^ 2 * (2 * V * 1) * M := by ring
      linarith only [b, e1, e2]
    have c2 : (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) * M ≤
        (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
      have : 16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V ≤ 3 * (2 * Kc * (L : ℝ) ^ 8) * V := by
        have h0 : 0 ≤ (2 * Kc * (L : ℝ) ^ 8) * V := by positivity
        have := mul_le_mul_of_nonneg_right hε1 h0
        linarith only [this, h0, show 16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V =
          16 / 7 * (ε * ((2 * Kc * (L : ℝ) ^ 8) * V)) by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hL2) hM
    have e2 : K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') + |(t' j).2.1 - (t j).2.1| +
        ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + M) = K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        K * |(t' j).2.1 - (t j).2.1| + K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + K * M := by ring
    have d1 : (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') ≤
        K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := by
      refine mul_le_mul_of_nonneg_right ?_ hΘ
      have : 0 ≤ (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (4 * β) +
        (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d2 : (L : ℝ) ^ 2 * |(t' j).2.1 - (t j).2.1| ≤ K * |(t' j).2.1 - (t j).2.1| := by
      refine mul_le_mul_of_nonneg_right ?_ hdμ
      have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 +
        (L : ℝ) ^ 2 * (4 * β + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d3 : (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤
        K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
      refine mul_le_mul_of_nonneg_right ?_ hdĝ
      have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) +
        (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d4 : (L : ℝ) ^ 2 * (2 * V) * M + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) * M ≤ K * M := by
      have h0 : (L : ℝ) ^ 2 * (2 * V) + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) ≤ K := by
        have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8) := by positivity
        linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
          3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8) +
          ((L : ℝ) ^ 2 * (2 * V) + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V)) by ring]
      have := mul_le_mul_of_nonneg_right h0 hM
      linarith only [this, show ((L : ℝ) ^ 2 * (2 * V) + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V)) * M
        = (L : ℝ) ^ 2 * (2 * V) * M + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) * M by ring]
    linarith only [h1, hY, c1, c2, e2, d1, d2, d3, d4]
  -- `dn₁`
  have hn : ‖nCor (nuT R j t') (whH R (j + 1) t') - nCor (nuT R j t) (whH R (j + 1) t)‖ ≤
      K * (‖nuT R j t' - nuT R j t‖ + ‖whH R (j + 1) t' - whH R (j + 1) t‖) := by
    have h1 := nCor_sub_le' F'.ν F.w F.nd F'.nd
    have hp3 : 0 ≤ cSν L b₁ cz R.ℓ (cmu Λ cm) := by unfold cSν cSY; positivity
    have b1 : 4 * (R.ℓ ^ 2 * ‖nuT R j t' - nuT R j t‖) ≤ K * ‖nuT R j t' - nuT R j t‖ := by
      have := mul_le_mul_of_nonneg_right k13 (norm_nonneg (nuT R j t' - nuT R j t))
      linarith only [this, show 4 * (R.ℓ ^ 2 * ‖nuT R j t' - nuT R j t‖) =
        4 * R.ℓ ^ 2 * ‖nuT R j t' - nuT R j t‖ by ring]
    have b2 : 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm) * ‖whH R (j + 1) t' - whH R (j + 1) t‖) ≤
        K * ‖whH R (j + 1) t' - whH R (j + 1) t‖ := by
      have h0 : 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) ≤ K := by
        have := mul_le_mul_of_nonneg_right hε1 hp3
        linarith only [k14, this, show 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) =
          4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) by ring]
      have := mul_le_mul_of_nonneg_right h0 (norm_nonneg (whH R (j + 1) t' - whH R (j + 1) t))
      linarith only [this, show 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm) *
        ‖whH R (j + 1) t' - whH R (j + 1) t‖) = 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) *
        ‖whH R (j + 1) t' - whH R (j + 1) t‖ by ring]
    linarith only [h1, b1, b2]
  have hB3 : ‖kapH R j t 3‖ ≤ σ * K := F.κ3.trans (by
    have h0 : 0 ≤ cS3 b₁ := by unfold cS3; positivity
    exact mul_le_mul (by linarith) k7 h0 (by linarith))
  have hsK : s ≤ σ * K := mul_le_mul (by linarith) k6 (by positivity) (by linarith)
  have hwK : ‖whH R (j + 1) t' - whH R (j + 1) t‖ ≤ K * M :=
    hw.trans (mul_le_mul_of_nonneg_right k12 hM)
  have h3K : ‖kapH R j t' 3 - kapH R j t 3‖ ≤ K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
      ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
    have : 4 * β ≤ K := by linarith
    have := mul_le_mul_of_nonneg_right this (thetaH_nonneg HC)
    linarith
  -- the difference parts
  have hκĝ : ‖(kapH R j t' 3 - kapH R j t 3) - (ghat (sdH R j t') - ghat (sdH R j t))‖ ≤
      K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := by
    have hk3 := kap_rem_scaled HC hkap 3
    rw [show cwt L j 3 = 1 from rfl, one_mul,
      shv3_sub R j (sdH R j t) (sdH R j t') HC.sOK.hzy HC.sOK.hy HC.sOK'.hzy HC.sOK'.hy,
      ← hβd] at hk3
    have : 4 * β ≤ K := by linarith
    exact hk3.trans (mul_le_mul_of_nonneg_right this (thetaH_nonneg HC))
  have hĝg := dĝd_hist H hM hV hZ hev hew
  have hĝg' : ‖(ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)‖ ≤
      σ * (4 * K) * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) := by
    have hdx := norm_nonneg ((t' j).2.2 - (t j).2.2)
    have hdg := abs_nonneg ((t' j).1 - (t j).1)
    have hdμ := abs_nonneg ((t' j).2.1 - (t j).2.1)
    have b1 : 8 * cmu Λ cm * R.ℓ ^ 2 * |(t' j).1 - (t j).1| ≤ 4 * K * |(t' j).1 - (t j).1| :=
      mul_le_mul_of_nonneg_right (by linarith) hdg
    have b2 : 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| ≤ 4 * K * |(t' j).2.1 - (t j).2.1| :=
      mul_le_mul_of_nonneg_right (by linarith) hdμ
    have b3 : (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤ 4 * K * M :=
      mul_le_mul_of_nonneg_right (by have := mul_nonneg hcmu hZ; linarith) hM
    have b4 : 0 ≤ 4 * K * ‖(t' j).2.2 - (t j).2.2‖ := by positivity
    have h2 : 8 * cmu Λ cm * R.ℓ ^ 2 * |(t' j).1 - (t j).1| + 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤
        4 * K * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) := by
      linarith only [b1, b2, b3, b4, show 4 * K * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| +
        |(t' j).2.1 - (t j).2.1| + M) = 4 * K * ‖(t' j).2.2 - (t j).2.2‖ +
        4 * K * |(t' j).1 - (t j).1| + 4 * K * |(t' j).2.1 - (t j).2.1| + 4 * K * M by ring]
    have h3 := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) h2 (by positivity)
      (by simp only [σ]; linarith)
    linarith only [hĝg, h3, show σ * (4 * K) * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| +
      |(t' j).2.1 - (t j).2.1| + M) = σ * (4 * K * (‖(t' j).2.2 - (t j).2.2‖ +
      |(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M)) by ring]
  exact G_assemble_d P hsK hs0 hB3 (norm_nonneg _) h3K hζ hν hwK hn (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hκĝ hĝg' hG


end Hist

end

end Step2.LL


-- from Step2/Lip/FlowZetaHist.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

/-- The bound on `δ(ν̃ - L²μ)` with the mass term kept as `2 m² L^{2j} |δζ_j|`. -/
theorem dY_hist_z (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4)) :
    ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) - (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ ≤
      (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t') +
        (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ +
        (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
  have HC := H.cmp j le_rfl
  have h1 := dY_le HC (kap_rem_scaled HC hkap)
  rw [← hβd] at h1
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have hg : |(sdH R j t).g| ≤ ε := by
      show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
    linarith
  have hm0 : 0 ≤ |R.msq| * ((L : ℝ) ^ j) ^ 2 := by positivity
  have a2 : 2 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ 16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hĝ (by norm_num : (0 : ℝ) ≤ 2)) hΔ
      (sq_nonneg _) (by have := H.hε0; positivity)
    linarith only [this, show 2 * (8 / 7 * ε) * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) =
      16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M by ring]
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  set X := 4 * β * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t')
  set Y := R.ℓ ^ 2 / 8 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖
  have hsum : X + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' + Y +
      2 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ X + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' + Y +
        16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M := by linarith only [a2]
  have := mul_le_mul_of_nonneg_left hsum hL2
  refine h1.trans (this.trans (le_of_eq ?_))
  simp only [X, Y]
  ring


set_option maxHeartbeats 1000000 in
/-- **(Lm) along two histories, with the hidden coupling kept.** The past enters the mass term
only through `|δζ_j|`, with coefficient `4` (if `|m²| L^{2(j+1)} ≤ 1`). -/
theorem Lm_hist_z (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {b₁ : ℝ}
    (F : FinOne R j t ε b₁ cz (cmu Λ cm)) (F' : FinOne R j t' ε b₁ cz (cmu Λ cm))
    {M V W₁ Z β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hβ : 0 ≤ β)
    (hb : 0 ≤ b₁) (hmj1 : |R.msq| * ((L : ℝ) ^ (j + 1)) ^ 2 ≤ 1)
    (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) (heW : eWH R j t t' ≤ (e + ε) * W₁ * M)
    (hew : ewH R j t t' ≤ Z * M) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4))
    (hs8 : ε * cSz b₁ R.ℓ ≤ 1 / 8) :
    let K := cKa L β b₁ R.ℓ (cmu Λ cm) cz V Z (2 * Kc * (L : ℝ) ^ 8)
      (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z)
    |(rgData R).m j t - (rgData R).m j t'| ≤ 300 * K ^ 4 * (|(t' j).1 - (t j).1| +
      ‖(t' j).2.2 - (t j).2.2‖) + (e + ε) * (300 * K ^ 4) * |(t' j).2.1 - (t j).2.1| +
      (e + ε) * (300 * K ^ 4) * M + 4 * eζH R j t t' := by
  intro K
  have HC := H.cmp j le_rfl
  have hε := H.hε0
  have hε1 := HC.hε1
  have he := HC.he
  have hcmu := HC.hcmu
  have hcz := HC.H.hcz
  have hKc := H.hKc
  have hkTh : 0 ≤ kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z := by
    have := HC.hcw; have := HC.hcx
    unfold kTh cTh; have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8, k9, k10, k11, -, -, -, k15, k16, k17, k18, k19, -⟩ :=
    cKa_ge (β := β) (b₁ := b₁) (ℓ := R.ℓ) (cmu := cmu Λ cm) (cz := cz) (V := V) (Z := Z)
      (Λ0 := 2 * Kc * (L : ℝ) ^ 8) (kThv := kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT))
        (2 * Kc * (L : ℝ) ^ 8) V W₁ Z) L hβ hb hcmu hcz hV hZ (by positivity) hkTh
  have P := pieces_hist_w H hM hV hW₁ hZ hev hΔ heW hew k1 k2 k3 k4 k5
  set σ := e + ε
  have hζ := dζ_hist_w H F F' hM hV hev hΔ hβd hkap k8 k9 k10
  have hY := dY_hist_z H hM hV hev hΔ hβd hkap
  have hp1 : 0 ≤ cSz b₁ R.ℓ := by unfold cSz; positivity
  have hζ1 : ‖zetaH R (j + 1) t‖ ≤ 1 / 8 := F.ζ_le.trans hs8
  have hζ1' : ‖zetaH R (j + 1) t'‖ ≤ 1 / 8 := F'.ζ_le.trans hs8
  have hm := m_core F.hO F'.hO hζ1 hζ1'
  have hΘ := thetaH_nonneg HC
  have hdĝ := norm_nonneg (ghat (sdH R j t') - ghat (sdH R j t))
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  -- `dY ≤ K(Θ + dĝ) + ϑ K M + σ K M`
  have hY' : ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) - (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ ≤
      K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') + ‖ghat (sdH R j t') - ghat (sdH R j t)‖) +
        (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t') + σ * K * M := by
    have d1 : (L : ℝ) ^ 2 * (4 * β) ≤ K := by
      have : 0 ≤ (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (4 * β) +
        (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d2 : (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) ≤ K := by
      have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) +
        (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have a1 := mul_le_mul_of_nonneg_right d1 hΘ
    have a2 := mul_le_mul_of_nonneg_right d2 hdĝ
    -- the mass term
    have a4 : (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) * M ≤ σ * K * M := by
      have b1 : (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) ≤
          σ * (3 * (L : ℝ) ^ 2 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        have h0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Kc * (L : ℝ) ^ 8) * V := by positivity
        have := mul_le_mul_of_nonneg_right (show ε ≤ σ by simp only [σ]; linarith) h0
        nlinarith
      have b2 : σ * (3 * (L : ℝ) ^ 2 * (2 * Kc * (L : ℝ) ^ 8) * V) ≤ σ * K :=
        mul_le_mul_of_nonneg_left k17 (by simp only [σ]; linarith)
      exact mul_le_mul_of_nonneg_right (b1.trans b2) hM
    have e2 : K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        ‖ghat (sdH R j t') - ghat (sdH R j t)‖) = K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by ring
    have e3 : (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') =
        (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := rfl
    linarith only [hY, a1, a2, a4, e2]
  -- `dP`
  set Pt := nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ) * (1 + zetaH R (j + 1) t)
  set Pt' := nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ) * (1 + zetaH R (j + 1) t')
  have hdζ0 := norm_nonneg (zetaH R (j + 1) t' - zetaH R (j + 1) t)
  have hP : ‖Pt' - Pt‖ ≤ ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
      (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ + σ * K * |(t' j).2.1 - (t j).2.1| +
      σ * K * ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ := by
    have e1 : Pt' - Pt = ((nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))) -
        ((L : ℂ) ^ 2 * ((((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) * zetaH R (j + 1) t') +
          (L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * (zetaH R (j + 1) t' - zetaH R (j + 1) t))) := by
      simp only [Pt, Pt']; push_cast; ring
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have b1 := norm_add_le ((L : ℂ) ^ 2 * ((((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) * zetaH R (j + 1) t'))
      ((L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * (zetaH R (j + 1) t' - zetaH R (j + 1) t)))
    have hn1 : ‖(L : ℂ) ^ 2 * ((((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) * zetaH R (j + 1) t')‖ =
        (L : ℝ) ^ 2 * ‖zetaH R (j + 1) t'‖ * |(t' j).2.1 - (t j).2.1| := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]; ring
    have hn2 : ‖(L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * (zetaH R (j + 1) t' - zetaH R (j + 1) t))‖ =
        (L : ℝ) ^ 2 * |(t j).2.1| * ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]; ring
    have c1 : (L : ℝ) ^ 2 * ‖zetaH R (j + 1) t'‖ ≤ σ * K := by
      have := mul_le_mul_of_nonneg_left F'.ζ_le hL2
      have h2 : (L : ℝ) ^ 2 * (ε * cSz b₁ R.ℓ) ≤ σ * K := by
        have := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) k18 (by positivity)
          (by simp only [σ]; linarith)
        linarith only [this, show (L : ℝ) ^ 2 * (ε * cSz b₁ R.ℓ) = ε * ((L : ℝ) ^ 2 * cSz b₁ R.ℓ) by ring]
      linarith only [this, h2]
    have c2 : (L : ℝ) ^ 2 * |(t j).2.1| ≤ σ * K := by
      have := mul_le_mul_of_nonneg_left F.μ hL2
      have h2 : (L : ℝ) ^ 2 * (cmu Λ cm * ε) ≤ σ * K := by
        have := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) k19 (by positivity)
          (by simp only [σ]; linarith)
        linarith only [this, show (L : ℝ) ^ 2 * (cmu Λ cm * ε) = ε * ((L : ℝ) ^ 2 * cmu Λ cm) by ring]
      linarith only [this, h2]
    have d1 := mul_le_mul_of_nonneg_right c1 (abs_nonneg ((t' j).2.1 - (t j).2.1))
    have d2 := mul_le_mul_of_nonneg_right c2 hdζ0
    linarith only [b1, hn1, hn2, d1, d2]
  -- `|P|`
  have hPn : ‖Pt‖ ≤ σ * K := by
    have e1 : Pt = (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)) -
        (L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * zetaH R (j + 1) t) := by simp only [Pt]; ring
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    have a1 := F.Y
    have a2 : (L : ℝ) ^ 2 * (|(t j).2.1| * ‖zetaH R (j + 1) t‖) ≤
        ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) := by
      have := mul_le_mul F.μ F.ζ_le (norm_nonneg _) (by positivity)
      have := mul_le_mul_of_nonneg_left this hL2
      have h3 : (L : ℝ) ^ 2 * (cmu Λ cm * ε * (ε * cSz b₁ R.ℓ)) ≤ ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) := by
        have h0 : 0 ≤ ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) := by positivity
        have := mul_le_mul_of_nonneg_right hε1 h0
        nlinarith
      linarith only [this, h3]
    have h4 : ε * cSY L b₁ cz R.ℓ + ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) ≤ σ * K := by
      have := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) k15
        (by unfold cSY; positivity) (by simp only [σ]; linarith)
      linarith only [this, show ε * (cSY L b₁ cz R.ℓ + (L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) =
        ε * cSY L b₁ cz R.ℓ + ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) by ring]
    linarith only [a1, a2, h4]
  set X := (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t') with hXd
  have hX4 : 2 * X ≤ 4 * eζH R j t t' := by
    have h0 : 0 ≤ eζH R j t t' := norm_nonneg _
    have hmj : (L : ℝ) ^ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 1 := by
      have e1 : |R.msq| * ((L : ℝ) ^ (j + 1)) ^ 2 =
          (L : ℝ) ^ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by ring
      linarith only [hmj1, e1]
    have := mul_le_mul_of_nonneg_right hmj h0
    rw [hXd]
    linarith only [this, show 2 * ((L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t')) =
      4 * ((L : ℝ) ^ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t') by ring]
  have := m_assemble (ϑ := 0) P le_rfl hPn (norm_nonneg _) hζ hdζ0
    (dY := ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
      (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ - X) (by linarith only [hY'])
    (dP := ‖Pt' - Pt‖ - X) (by linarith only [hP])
    (dm := |(rgData R).m j t - (rgData R).m j t'| - 2 * X) (by linarith only [hm])
  linarith only [this, hX4]


end Hist

end

end Step2.LL

