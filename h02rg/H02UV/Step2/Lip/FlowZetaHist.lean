import Step2.Lip.FlowFadeHist

/-!
# The hidden coupling `ζ` as a separate channel in the Lipschitz chain

In `Lm_hist_w` the mass term `L² · 2 m² L^{2j} · |δζ_j|` of `δm_j` is bounded through
`|δζ_j| ≤ V M` (the past distance), which gives the `M`-coefficient `2Kϑ` with the large
Lipschitz constant `K`. Here it is kept as `|δζ_j|`:
* `dY_hist_z`, `Lm_hist_z`: `|δm_j| ≤ 300K⁴(|δg| + ‖δx‖) + σ300K⁴(|δμ| + M) + 4|δζ_j|`
  (if `|m²| L^{2(j+1)} ≤ 1`);
* `zeta_assemble`: `|δζ_{j+1}| ≤ 11K²(|δg| + ‖δx‖) + σ 6K²(|δμ| + M)` from `dζ_hist_w`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- `|δζ_{j+1}|` from the pieces. -/
theorem zeta_assemble {K σ ε dx dg dμ M dĝ Θ dζ : ℝ} (H : Pieces K σ ε dx dg dμ M dĝ Θ)
    (hζ : dζ ≤ K * Θ + K * dĝ + σ * K * M) :
    dζ ≤ 11 * K ^ 2 * (dg + dx) + σ * (6 * K ^ 2) * (dμ + M) := by
  have hK := H.hK
  have hK0 : 0 ≤ K := by linarith
  have hσ := H.hσ
  have hσ2 := H.hσ2
  have hdx := H.hdx; have hdg := H.hdg; have hdμ := H.hdμ; have hM := H.hM
  have hKK : K ≤ K ^ 2 := by nlinarith
  have a1 := mul_le_mul_of_nonneg_left H.hΘ hK0
  have a2 := mul_le_mul_of_nonneg_left H.hĝ hK0
  have a3 : σ * K * M ≤ σ * K ^ 2 * M := by
    have := mul_le_mul_of_nonneg_left hKK hσ
    exact mul_le_mul_of_nonneg_right this hM
  have a4 : K * dg ≤ K ^ 2 * dg := mul_le_mul_of_nonneg_right hKK hdg
  have hσK : 0 ≤ σ * K ^ 2 := by positivity
  have a5 : 5 * (σ * K ^ 2) * (dx + dg) ≤ 10 * K ^ 2 * (dx + dg) := by
    have : σ * K ^ 2 ≤ 2 * K ^ 2 := by nlinarith
    nlinarith
  have e1 : K * (K * dx + σ * K * (dx + dg + dμ + M)) = K ^ 2 * dx + σ * K ^ 2 * (dx + dg + dμ + M) := by
    ring
  have e2 : K * (dg + σ * (4 * K) * (dx + dg + dμ + M)) =
      K * dg + 4 * (σ * K ^ 2) * (dx + dg + dμ + M) := by ring
  have e3 : σ * (6 * K ^ 2) * (dμ + M) = 6 * (σ * K ^ 2) * (dμ + M) := by ring
  have e4 : σ * K ^ 2 * (dx + dg + dμ + M) = σ * K ^ 2 * (dx + dg) + σ * K ^ 2 * (dμ + M) := by ring
  have e5 : σ * K ^ 2 * M ≤ σ * K ^ 2 * (dμ + M) :=
    mul_le_mul_of_nonneg_left (by linarith) hσK
  nlinarith

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

end Step2
