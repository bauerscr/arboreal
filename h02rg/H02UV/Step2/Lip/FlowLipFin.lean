import Step2.Lip.FlowLipRun

/-!
# The final step: the irrelevant map (Lipschitz bounds, part 24)

With the error bounds of `run_errors` at step `j`, `Θ_j ≤ (1 + e) ‖δx_j‖ + (e + ε) K_Θ (|δg| + |δμ| + M)`
(`theta_final`), and the comparison bounds for `K̂_{j+1}`, `D̂_{j+1}` give (LT).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- The constant of the final `Θ` bound. -/
def kTh (ℓ cmu cThv Λ0 V W₁ Z : ℝ) : ℝ :=
  W₁ + kX ℓ + 8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) + 2 * (cM : ℝ) * ℓ ^ 2 * V +
    cThv * V + 16 * Λ0 * V / ℓ ^ 2

theorem theta_final {Θ dx dg dμ dn eW ev ew eζ M V W₁ Z ℓ cmu cThv Λ0 ℓΔ2 e ε E1 : ℝ}
    (hℓ : 0 < ℓ) (hcmu : 0 ≤ cmu) (hcTh : 0 ≤ cThv) (hΛ0 : 0 ≤ Λ0) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M) (hV : 0 ≤ V) (hZ : 0 ≤ Z) (hW₁ : 0 ≤ W₁)
    (hdg0 : 0 ≤ dg) (hdμ0 : 0 ≤ dμ)
    (hev : ev ≤ V * M) (hew : ew ≤ Z * M) (heW : eW ≤ (e + ε) * W₁ * M) (hζ : eζ ≤ ev)
    (hev0 : 0 ≤ ev) (hew0 : 0 ≤ ew) (hζ0 : 0 ≤ eζ) (hdn0 : 0 ≤ dn)
    (hdn : dn ≤ 4 * (ℓ ^ 2 * dμ + cmu * ε * (2 * ℓ ^ 2 * eζ + 9 / 8 * ew)))
    (hΔ : ℓΔ2 ≤ Λ0 * (V * M))
    (hΘ : Θ ≤ (1 + E1) * dx + eW + e * ((cM : ℝ) * ℓ ^ 2 * dμ + 5 * ℓ ^ 4 * dg +
      8 * ℓ ^ 4 * dn + 2 * cM * ℓ ^ 2 * ev) + ε ^ 2 * cThv * ev + 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2) :
    Θ ≤ (1 + E1) * dx + (e + ε) * kTh ℓ cmu cThv Λ0 V W₁ Z * (dg + dμ + M) := by
  have hM' : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hS : e ≤ e + ε := by linarith
  have hS0 : 0 ≤ e + ε := by linarith
  have hdn' : dn ≤ 4 * ℓ ^ 2 * dμ + (8 * cmu * ℓ ^ 2 * V + 9 / 2 * cmu * Z) * M := by
    have h1 : ℓ ^ 2 * dμ ≤ ℓ ^ 2 * dμ := le_rfl
    have h2 : 2 * ℓ ^ 2 * eζ + 9 / 8 * ew ≤ (2 * ℓ ^ 2 * V + 9 / 8 * Z) * M := by
      have := mul_le_mul_of_nonneg_left (hζ.trans hev) (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ 2)
      have := mul_le_mul_of_nonneg_left hew (by norm_num : (0 : ℝ) ≤ 9 / 8)
      nlinarith
    have h3 : cmu * ε * (2 * ℓ ^ 2 * eζ + 9 / 8 * ew) ≤ cmu * 1 * ((2 * ℓ ^ 2 * V + 9 / 8 * Z) * M) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hε1 hcmu) h2 (by positivity) (by positivity)
    have e1 : 4 * (ℓ ^ 2 * dμ + cmu * 1 * ((2 * ℓ ^ 2 * V + 9 / 8 * Z) * M)) =
        4 * ℓ ^ 2 * dμ + (8 * cmu * ℓ ^ 2 * V + 9 / 2 * cmu * Z) * M := by ring
    linarith only [hdn, h1, h3, e1]
  set K₀ := kX ℓ + 8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) + 2 * (cM : ℝ) * ℓ ^ 2 * V with hK₀
  have hK1 : (cM : ℝ) * ℓ ^ 2 + 32 * ℓ ^ 6 ≤ K₀ := by
    rw [hK₀]; unfold kX; have : 0 ≤ 8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) := by positivity
    have : 0 ≤ 2 * (cM : ℝ) * ℓ ^ 2 * V := by positivity
    have : 0 ≤ 5 * ℓ ^ 4 := by positivity
    linarith
  have hK2 : 5 * ℓ ^ 4 ≤ K₀ := by
    rw [hK₀]; unfold kX; have : 0 ≤ 8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) := by positivity
    have : 0 ≤ 2 * (cM : ℝ) * ℓ ^ 2 * V := by positivity
    have : 0 ≤ (cM : ℝ) * ℓ ^ 2 + 32 * ℓ ^ 6 := by positivity
    linarith
  have hK3 : 8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) + 2 * (cM : ℝ) * ℓ ^ 2 * V ≤ K₀ := by
    rw [hK₀]; have := kX_nonneg ℓ; linarith
  have hX : (cM : ℝ) * ℓ ^ 2 * dμ + 5 * ℓ ^ 4 * dg + 8 * ℓ ^ 4 * dn + 2 * cM * ℓ ^ 2 * ev ≤
      K₀ * (dg + dμ + M) := by
    have a3 := mul_le_mul_of_nonneg_left hdn' (by positivity : (0 : ℝ) ≤ 8 * ℓ ^ 4)
    have a4 := mul_le_mul_of_nonneg_left hev (by positivity : (0 : ℝ) ≤ 2 * cM * ℓ ^ 2)
    have b1 := mul_le_mul_of_nonneg_right hK1 hdμ0
    have b2 := mul_le_mul_of_nonneg_right hK2 hdg0
    have b3 := mul_le_mul_of_nonneg_right hK3 hM
    have e1 : 8 * ℓ ^ 4 * (4 * ℓ ^ 2 * dμ + (8 * cmu * ℓ ^ 2 * V + 9 / 2 * cmu * Z) * M) =
        32 * ℓ ^ 6 * dμ + 8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) * M := by ring
    have e2 : K₀ * (dg + dμ + M) = K₀ * dg + K₀ * dμ + K₀ * M := by ring
    have e3 : (8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) + 2 * (cM : ℝ) * ℓ ^ 2 * V) * M =
        8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) * M + 2 * cM * ℓ ^ 2 * (V * M) := by ring
    have e4 : ((cM : ℝ) * ℓ ^ 2 + 32 * ℓ ^ 6) * dμ = cM * ℓ ^ 2 * dμ + 32 * ℓ ^ 6 * dμ := by ring
    linarith only [a3, a4, b1, b2, b3, e1, e2, e3, e4]
  have t1 : (0 : ℝ) ≤ 1 := zero_le_one
  have hDM : 0 ≤ dg + dμ := by positivity
  have t2 : ε ^ 2 * cThv * ev ≤ (e + ε) * (cThv * V * M) := by
    have hε2 : ε ^ 2 ≤ e + ε := by
      have : ε ^ 2 ≤ ε := pow_le_of_le_one hε hε1 (by norm_num)
      linarith
    have h1 := mul_le_mul hε2 (mul_le_mul_of_nonneg_left hev hcTh) (by positivity) hS0
    have e1 : ε ^ 2 * cThv * ev = ε ^ 2 * (cThv * ev) := by ring
    have e2 : (e + ε) * (cThv * V * M) = (e + ε) * (cThv * (V * M)) := by ring
    linarith only [h1, e1, e2]
  have t3 : 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2 ≤ (e + ε) * (16 * Λ0 * V / ℓ ^ 2 * M) := by
    have he2 : e ^ 2 ≤ e + ε := by
      have : e ^ 2 ≤ e := pow_le_of_le_one he he1 (by norm_num)
      linarith
    have hℓ2 : 0 < ℓ ^ 2 := by positivity
    have h0 : 0 ≤ ℓΔ2 ∨ ℓΔ2 < 0 := le_or_gt 0 ℓΔ2
    rcases h0 with h0 | h0
    · have h1 : 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2 = e ^ 2 * (16 * ℓΔ2 / ℓ ^ 2) := by ring
      have h2 : 16 * ℓΔ2 / ℓ ^ 2 ≤ 16 * Λ0 * V / ℓ ^ 2 * M := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hℓ2]
        have := mul_le_mul_of_nonneg_left hΔ (by norm_num : (0 : ℝ) ≤ 16)
        linarith only [this, show 16 * (Λ0 * (V * M)) = 16 * Λ0 * V * M by ring]
      rw [h1]; exact mul_le_mul he2 h2 (by positivity) hS0
    · have h1 : 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2 ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hℓ2.le
        have : 0 ≤ 16 * e ^ 2 := by positivity
        exact mul_nonpos_of_nonneg_of_nonpos this h0.le
      have h2 : 0 ≤ (e + ε) * (16 * Λ0 * V / ℓ ^ 2 * M) := by positivity
      linarith only [h1, h2]
  have t2' : (e + ε) * (cThv * V * M) ≤ (e + ε) * (cThv * V * (dg + dμ + M)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hS0
  have t3' : (e + ε) * (16 * Λ0 * V / ℓ ^ 2 * M) ≤ (e + ε) * (16 * Λ0 * V / ℓ ^ 2 * (dg + dμ + M)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hS0
  have t4 : (e + ε) * W₁ * M ≤ (e + ε) * W₁ * (dg + dμ + M) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t1' : e * ((cM : ℝ) * ℓ ^ 2 * dμ + 5 * ℓ ^ 4 * dg + 8 * ℓ ^ 4 * dn + 2 * cM * ℓ ^ 2 * ev) ≤
      (e + ε) * (K₀ * (dg + dμ + M)) :=
    (mul_le_mul_of_nonneg_left hX he).trans
      (mul_le_mul_of_nonneg_right hS (by have := kX_nonneg ℓ; positivity))
  unfold kTh
  have e1 : (e + ε) * (W₁ + kX ℓ + 8 * ℓ ^ 4 * cmu * (8 * ℓ ^ 2 * V + 9 / 2 * Z) +
      2 * (cM : ℝ) * ℓ ^ 2 * V + cThv * V + 16 * Λ0 * V / ℓ ^ 2) * (dg + dμ + M) =
      (e + ε) * W₁ * (dg + dμ + M) + (e + ε) * (K₀ * (dg + dμ + M)) +
        (e + ε) * (cThv * V * (dg + dμ + M)) + (e + ε) * (16 * Λ0 * V / ℓ ^ 2 * (dg + dμ + M)) := by
    rw [hK₀]; ring
  linarith only [hΘ, heW, t1', t2, t3, t2', t3', t4, e1]


section LT

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

/-- `Θ_j` at the final step, from the error bounds. -/
theorem Run.theta_j (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W₁ Z : ℝ} (hM : 0 ≤ M)
    (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hev : ∀ i ≤ j, evH R i t t' ≤ V * M)
    (heW : eWH R j t t' ≤ (e + ε) * W₁ * M) (hew : ewH R j t t' ≤ Z * M) :
    thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') ≤
      (1 + Real.exp 1) * ‖(t' j).2.2 - (t j).2.2‖ + (e + ε) * kTh R.ℓ (cmu Λ cm)
        (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z *
          (|(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) := by
  have HC := H.cmp j le_rfl
  have hζIH : ∀ i ≤ j, eζH R i t t' ≤ V * M := fun i hi =>
    (eζ_le_ev (H.cmp i hi).H (H.cmp i hi).H').trans (hev i hi)
  have hcTh : 0 ≤ cTh R.ℓ cw (cx κ cT) := by
    have := HC.hcw; have := HC.hcx
    unfold cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hdn := H.dn_le (le_refl j)
  exact theta_final HC.hℓ HC.hcmu hcTh (by have := H.hKc; positivity) HC.he.le H.he1 H.hε0.le
    HC.hε1 hM hV hZ hW₁ (abs_nonneg _) (abs_nonneg _) (hev j le_rfl) hew heW
    (eζ_le_ev HC.H HC.H') (evH_nonneg j) (ewH_nonneg j) (norm_nonneg _) (norm_nonneg _) hdn
    (lD_sq_le H.hKc j t t' hζIH) (thetaH_le HC)

theorem Tmap_sub_snd {j : ℕ} (h : ∀ i ≤ j, ValidAt R i) (t t' : Hist.Seq (Xs R))
    (H : HistOK R j t) (H' : HistOK R j t') :
    ‖(Tmap R j t').2 - (Tmap R j t).2‖ =
      (Knorm (j + 1) R.ℓ R.A (nKH R j t' - nKH R j t)).toReal := by
  rw [ASp.norm_def, map_sub, (Tmap_norm h t' H').2, (Tmap_norm h t H).2]

theorem Tmap_sub_fst {j : ℕ} (h : ∀ i ≤ j, ValidAt R i) (t t' : Hist.Seq (Xs R))
    (H : HistOK R j t) (H' : HistOK R j t') :
    ‖(Tmap R j t').1 - (Tmap R j t).1‖ =
      (Fnorm (j + 1) R.ℓ (nDH R j t' - nDH R j t)).toReal := by
  rw [BSp.norm_def, map_sub, (Tmap_norm h t' H').1, (Tmap_norm h t H).1]

/-- **(LT), the activity.** -/
theorem LT_K (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (hval : ∀ i ≤ j, ValidAt R i)
    {κK C₁ : ℝ} (hκK : 0 ≤ κK) (hC₁ : 0 ≤ C₁)
    (hK : Knorm (j + 1) R.ℓ R.A (nKH R j t' - nKH R j t) ≤
      ENNReal.ofReal (4 * (2 * κK * e ^ 2 + 16 * C₁ * e ^ 3) * relDist e (aIn R j t t')
        (bWIn R cw j t t' + bDIn R (cx κ cT) j t t') (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1
          (R.ℓ / 4))) :
    ‖(Tmap R j t').2 - (Tmap R j t).2‖ ≤
      4 * (2 * κK + 16 * C₁ * e) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := by
  have HC := H.cmp j le_rfl
  rw [Tmap_sub_snd hval t t' HC.H.histOK HC.H'.histOK]
  have hr : 0 ≤ relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
      (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4) :=
    relDist_nonneg HC.he HC.aIn_nonneg (add_nonneg HC.bWIn_nonneg HC.bDIn_nonneg) HC.cIn_nonneg
  have he := HC.he
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hK).trans (le_of_eq ?_)
  rw [← thetaH_eq HC]; ring

/-- **(LT), the remainder `D`.** -/
theorem LT_D (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (hval : ∀ i ≤ j, ValidAt R i)
    {κD C₃ : ℝ} (hκD : 0 ≤ κD) (hC₃ : 0 ≤ C₃)
    (hD : Fnorm (j + 1) R.ℓ (nDH R j t' - nDH R j t) ≤
      ENNReal.ofReal (4 * (2 * κD * e ^ 2 + 64 * C₃ * e ^ 4) * relDist e (aIn R j t t')
        (bWIn R cw j t t' + bDIn R (cx κ cT) j t t') (bDIn R (cx κ cT) j t t') (lD R Kc j t t') 1
          (R.ℓ / 4))) :
    ‖(Tmap R j t').1 - (Tmap R j t).1‖ ≤
      4 * (2 * κD + 64 * C₃ * e ^ 2) * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        bDIn R (cx κ cT) j t t') := by
  have HC := H.cmp j le_rfl
  rw [Tmap_sub_fst hval t t' HC.H.histOK HC.H'.histOK]
  have hr : 0 ≤ relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
      (bDIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4) :=
    relDist_nonneg HC.he HC.aIn_nonneg (add_nonneg HC.bWIn_nonneg HC.bDIn_nonneg) HC.bDIn_nonneg
  have he := HC.he
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hD).trans ?_
  have e1 : 4 * (2 * κD * e ^ 2 + 64 * C₃ * e ^ 4) * relDist e (aIn R j t t')
      (bWIn R cw j t t' + bDIn R (cx κ cT) j t t') (bDIn R (cx κ cT) j t t') (lD R Kc j t t') 1
        (R.ℓ / 4) = 4 * (2 * κD + 64 * C₃ * e ^ 2) * (e ^ 2 * relDist e (aIn R j t t')
      (bWIn R cw j t t' + bDIn R (cx κ cT) j t t') (bDIn R (cx κ cT) j t t') (lD R Kc j t t') 1
        (R.ℓ / 4)) := by ring
  rw [e1, relDist_mul HC.he HC.hℓ]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold thetaH thetaIn
  have := HC.cIn_nonneg
  linarith

end LT

end

end Step2
