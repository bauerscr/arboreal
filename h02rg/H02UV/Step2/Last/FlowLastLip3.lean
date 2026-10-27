import Step2.Last.FlowLastLip2
import Step2.Last.FlowLastBand2

/-!
# The Lipschitz layer at the step `j = N - 2`, part 3 (namespace `Step2.LL`)

Copies of the declarations of `Step2/Lip/FlowLipFinal`, `FlowLipRunH`, `FlowFadeRun` that depend on
the validity. `nW1H_le`, `domH_of`, `run_of` take `ValidAt` below `j` and `ValidAtL` at `j`
(`nW1H_le` from `Zw1_hist`).
-/
-- from Step2/Lip/FlowLipFinal.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section KC

variable {β b₁ ℓ cmu cz V Z Λ0 kThv : ℝ}

end KC

section Hist

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

theorem ghat_nCor_le (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) :
    ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ ≤ 4 * cmu Λ cm * ε * R.ℓ ^ 2 := by
  have HC := H.cmp j le_rfl
  rw [nCor_dom (H.nd j le_rfl).2, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show ‖(4 : ℂ)‖ = 4 by norm_num]
  have hμ : |(t' j).2.1| ≤ cmu Λ cm * ε :=
    HC.H'.hD.2.2.1.trans (mul_le_mul_of_nonneg_left HC.H'.g_le HC.hcmu)
  have := mul_le_mul hμ (H.nW j le_rfl).2 (norm_nonneg _) (by have := HC.hcmu; have := H.hε0; positivity)
  nlinarith

/-- **`|δĝ|`.** -/
theorem dĝ_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M) (hew : ewH R j t t' ≤ Z * M) :
    ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤ |(t' j).1 - (t j).1| + ε * (8 * cmu Λ cm * R.ℓ ^ 2 *
      |(t' j).1 - (t j).1| + 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by
  have HC := H.cmp j le_rfl
  have hτ := ghat_nCor_le H
  have h1 := ghat_sub_le' (sdH R j t) (sdH R j t') (le_refl _)
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
  have e2 : (1 + 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖) * dg =
      dg + 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ * dg := by ring
  have e3 : ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
      (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) = ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg) +
      ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by ring
  have h1' : ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤
      (1 + 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖) * dg + 2 * |(sdH R j t).g| * dn := h1
  linarith only [h1', e2, a1, a2, a4, e3]

/-- **The final-step facts from the sizes.** -/
theorem finOne_of (HD : DomH j t Λ κ cm cT ε cz cw) {Cq Cl cS : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hε1 : ε ≤ 1)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (hL2 : 2 ≤ L) (hnW : ‖nW1H R j t‖ ≤ R.ℓ ^ 2)
    (hrem : ∀ i : Fin 4, cwt L j i * ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t j).1 ^ 3)))
    (hsmall : ε * cSz (bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) R.ℓ ≤ R.ρ)
    (hsmall2 : ε * cSn L (bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) cz
      R.ℓ (cmu Λ cm) ≤ 1 / 8) :
    FinOne R j t ε (bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) cz
      (cmu Λ cm) := by
  obtain ⟨s01, s3, sY, -⟩ := HD.sizes hCq hCl hcS hcw hcx hcmu hε1 hm hrem
  set b₁ := bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)
  have HO := HD.histOK
  have hε : 0 ≤ ε := HD.g_pos.le.trans HD.g_le
  have hz : ‖kapH R j t 0 + kapH R j t 1‖ ≤ ε * cSz b₁ R.ℓ :=
    (norm_add_le _ _).trans (by unfold cSz; exact s01)
  have hζ := zeta1_eq HO (hz.trans hsmall)
  have hμ : |(t j).2.1| ≤ cmu Λ cm * ε :=
    HD.hD.2.2.1.trans (mul_le_mul_of_nonneg_left HD.g_le hcmu)
  have hν : ‖nuT R j t‖ ≤ ε * cSν L b₁ cz R.ℓ (cmu Λ cm) := by
    have h1 := norm_add_le (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)) ((L : ℂ) ^ 2 * ((t j).2.1 : ℂ))
    rw [sub_add_cancel] at h1
    have hLμ : ‖(L : ℂ) ^ 2 * ((t j).2.1 : ℂ)‖ = (L : ℝ) ^ 2 * |(t j).2.1| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [hLμ] at h1
    have h2 := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    unfold cSν
    have e1 : ε * (cSY L b₁ cz R.ℓ + (L : ℝ) ^ 2 * cmu Λ cm) =
        ε * cSY L b₁ cz R.ℓ + (L : ℝ) ^ 2 * (cmu Λ cm * ε) := by ring
    unfold cSY at e1 ⊢
    linarith only [h1, sY, h2, e1]
  have hw := HD.whH_succ_le hL2 hnW
  have hn4 : ‖4 * nuT R j t * whH R (j + 1) t‖ ≤ ε * cSn L b₁ cz R.ℓ (cmu Λ cm) := by
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have := mul_le_mul hν hw (norm_nonneg _) ((norm_nonneg _).trans hν)
    unfold cSn
    linarith only [this, show 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm) * R.ℓ ^ 2) =
      ε * (4 * cSν L b₁ cz R.ℓ (cmu Λ cm) * R.ℓ ^ 2) by ring]
  refine ⟨HO, hζ, by rw [hζ]; exact hz, ?_, by unfold cSY; exact sY, hν, hw,
    hn4.trans hsmall2, ?_, hμ⟩
  · unfold cS3; exact s3
  · rw [nCor_dom (hn4.trans hsmall2)]; exact hn4

end Hist

end

end Step2.LL


-- from Step2/Lip/FlowLipRunH.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Run

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ β δ κ cg cm cT ε cz cw Kc : ℝ}

theorem nW1H_le (hV : ∀ i < j, ValidAt R i) (hVj : ValidAtL R j) (t : Hist.Seq (Xs R)) {k : ℕ}
    (hk : k ≤ j) : ‖nW1H R k t‖ ≤ R.ℓ ^ 2 := by
  have hρ := hVj.2.2.2.2.1
  have h := Zw1_hist R hρ k (fun i hi => hV i (by omega)) t
  have hL : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have e : nW1H R k t = stZ' R (rawHist R k t) * (rawHist R k t).w1 / (L : ℂ) ^ (2 * k) := rfl
  have e2 : (L : ℝ) ^ (2 * k) = ((L : ℝ) ^ k) ^ 2 := by ring
  rw [e, norm_div, norm_pow, Complex.norm_natCast, e2, div_le_iff₀ hL]
  exact h

/-- The domain at step `k` from `InDh` and the a priori bounds. -/
theorem domH_of (hV : ∀ i < j, ValidAt R i) (hVj : ValidAtL R j) (ht : Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hA : ∀ k ≤ j, APB R cz cw (t k).1 (rawHist R k t) k) (hcz : 0 ≤ cz)
    (hρ : 2 * cz * ε ≤ R.ρ) (h16 : 2 * cz * ε ≤ 1 / 16) {k : ℕ} (hk : k ≤ j) :
    DomH k t Λ κ cm cT ε cz cw :=
  ⟨fun i hi => hV i (by omega), by
    rcases lt_or_eq_of_le hk with h | h
    · exact (hV k h).toValidAtL hVj.1
    · exact h ▸ hVj, ht.1 k hk, hA k hk, hcz, hρ, h16⟩

/-- **The comparison hypotheses hold along two histories in the domain.** -/
theorem run_of (hV : ∀ i < j, ValidAt R i) (hVj : ValidAtL R j) (ht : Hist.InDh Λ β δ κ cg cm cT ε j t)
    (ht' : Hist.InDh Λ β δ κ cg cm cT ε j t')
    (hA : ∀ k ≤ j, APB R cz cw (t k).1 (rawHist R k t) k)
    (hA' : ∀ k ≤ j, APB R cz cw (t' k).1 (rawHist R k t') k)
    (hm : ∀ k ≤ j, |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hC : ∀ k ≤ j, GoodCov2 k (lD R Kc k t t') (CvH R k t' - CvH R k t))
    (hcz : 0 ≤ cz) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hKc : 0 ≤ Kc)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 2 * cz * ε ≤ R.ρ) (h16 : 2 * cz * ε ≤ 1 / 16)
    (hΔ : cDl (7 / 8 * R.ℓ) cz * ε ≤ 1 / 4)
    (hE1 : cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * ε ≤ 1)
    (hnd : 4 * cmu Λ cm * ε * R.ℓ ^ 2 ≤ 1 / 8) :
    Run R j t t' Λ κ cm cT ε cz cw (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * ε) Kc := by
  set cE := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) with hcE
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE1 : 1 ≤ cE := by rw [hcE]; unfold cEr; linarith
  have hcE2 : cw + 3 * cx κ cT ≤ cE := by rw [hcE]; unfold cEr; linarith
  have hcEV : cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) ≤ cE := by rw [hcE]; unfold cEr; linarith
  have hE3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hε2 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have hcEE : cE ≤ cE ^ 2 := by nlinarith
  have nd1 : ∀ (tt : Hist.Seq (Xs R)), Hist.InDh Λ β δ κ cg cm cT ε j tt → ∀ k ≤ j,
      ‖4 * ((tt k).2.1 : ℂ) * nW1H R k tt‖ ≤ 1 / 8 := fun tt htt k hk => by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(4 : ℂ)‖ = 4 by norm_num]
    obtain ⟨hg, hgε, hμ, -⟩ := htt.1 k hk
    have hμ' : |(tt k).2.1| ≤ cmu Λ cm * ε := hμ.trans (mul_le_mul_of_nonneg_left hgε hcmu)
    have := mul_le_mul hμ' (nW1H_le hV hVj tt hk) (norm_nonneg _) (by positivity)
    nlinarith
  refine ⟨fun k hk => ?_, fun k hk => ⟨nW1H_le hV hVj t hk, nW1H_le hV hVj t' hk⟩,
    fun k hk => ⟨nd1 t ht k hk, nd1 t' ht' k hk⟩, hKc, hE1, hε0⟩
  refine ⟨domH_of hV hVj ht hA hcz hρ h16 hk, domH_of hV hVj ht' hA' hcz hρ h16 hk, hm k hk, hcw, hcx,
    hcmu, hε1, hΔ, by positivity, ?_, ?_, ?_, lD_nonneg _ _ _ _, hC k hk⟩
  · exact (mul_le_mul_of_nonneg_right hcEV hε0.le)
  · have h1 : cw * ε ^ 2 + cx κ cT * ε ^ 3 ≤ (cw + cx κ cT) * ε ^ 2 := by nlinarith
    have h2 : (cw + cx κ cT) * ε ^ 2 ≤ cE ^ 2 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    nlinarith
  · have h1 : Real.exp 1 * (cx κ cT * ε ^ 3) ≤ 3 * cx κ cT * ε ^ 2 := by
      have := mul_le_mul hE3 (mul_le_mul_of_nonneg_left hε2 hcx) (by positivity) (by norm_num)
      nlinarith
    have h2 : 3 * cx κ cT * ε ^ 2 ≤ cE ^ 2 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    nlinarith

end Run

end

end Step2.LL


-- from Step2/Lip/FlowFadeRun.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Def

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

end Def

section Step

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

set_option maxHeartbeats 1000000 in
/-- **One step of the error recursion.** -/
theorem run_step_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {k : ℕ} (hk : k < j) {M V : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hd : Hist.dist3 (t k) (t' k) ≤ M)
    (hΔ : lD R Kc k t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) {Cq Cl cS C₀ C₂ : ℝ} (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
    (hβ : 0 ≤ bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') (lD R Kc k t t') 1 (R.ℓ / 4))
    (hW : Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 (lD R Kc k t t') 1
          (R.ℓ / 4) + 4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + lD R Kc k t t' ^ 2 / (1 * (R.ℓ / 4)) ^ 2))) :
    let β := bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2
    let Λ0 := 2 * Kc * (L : ℝ) ^ 8
    let κW := C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)
    evH R (k + 1) t t' ≤ ka0 R.ℓ β * M + 8 * β * eWH R k t t' + (e + ε) *
        (kEv R.ℓ β (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) * evH R k t t' +
          kEw R.ℓ β (cmu Λ cm) * ewH R k t t' + kEV R.ℓ β Λ0 * (V * M)) ∧
      eWH R (k + 1) t t' ≤ 8 * κW * eWH R k t t' + (e + ε) * (kWM R.ℓ C₂ * M +
        kWv R.ℓ C₂ κW cw (cmu Λ cm) * evH R k t t' + kWw R.ℓ C₂ (cmu Λ cm) * ewH R k t t' +
        kWV R.ℓ C₂ κW cw Λ0 * (V * M)) ∧
      ewH R (k + 1) t t' ≤ 9 / (8 * (L : ℝ) ^ 2) * ewH R k t t' +
        (2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * Λ0) * (evH R k t t' + V * M) := by
  intro β Λ0 κW
  have HC := H.cmp k hk.le
  have hℓ := HC.hℓ
  have he := HC.he
  have hε := H.hε0
  have hε1 := HC.hε1
  have hcmu := HC.hcmu
  have hcw := HC.hcw
  have hcx := HC.hcx
  obtain ⟨hdx, hdg, hdμ⟩ := dist3_parts hd
  have hζ := eζ_le_ev HC.H HC.H'
  have hev := evH_nonneg (R := R) (t := t) (t' := t') k
  have hew := ewH_nonneg (R := R) (t := t) (t' := t') k
  have hdn := H.dn_le hk.le
  have hΔ0 : 0 ≤ lD R Kc k t t' ^ 2 := sq_nonneg _
  have hΘ := thetaH_le HC
  have hcTh : 0 ≤ cTh R.ℓ cw (cx κ cT) := by
    unfold cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hΛ0 : 0 ≤ Λ0 := by have := H.hKc; positivity
  refine ⟨?_, ?_, ?_⟩
  · -- couplings
    have h1 := ev_succ_le HC hkap
    have hG := ghat_sub_le (sdH R k t) (sdH R k t')
      (show |(t' k).1| ≤ 1 by rw [abs_of_pos HC.H'.g_pos]; exact HC.H'.g_le.trans hε1)
    have hγ : ‖ghat (sdH R k t)‖ ≤ 2 * ε := by
      have := norm_ghat_le (sdH R k t)
      have hg : |(sdH R k t).g| ≤ ε := by
        show |(t k).1| ≤ ε
        rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
      linarith
    exact ev_rec hℓ hβ hcmu hcTh hΛ0 he.le H.he1 hε.le hε1 hM hV hev hew hdx hdg hdμ hζ hdn
      hΔ hΔ0 hΘ hG hγ (norm_nonneg _) h1
  · -- `𝒲^lin`
    have h1 := eW_succ_le HC hε hC₀ hC₂ hW
    have ha : aIn R k t t' ≤ (cM : ℝ) * R.ℓ ^ 2 * |(t' k).2.1 - (t k).2.1| +
        5 * R.ℓ ^ 4 * |(t' k).1 - (t k).1| + 8 * R.ℓ ^ 4 *
        ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖ +
        2 * cM * R.ℓ ^ 2 * evH R k t t' := by
      unfold aIn aVf
      have hM' : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
      have hℓ2 : (7 / 8 * R.ℓ) ^ 2 ≤ R.ℓ ^ 2 := by nlinarith
      have hℓ4 : (7 / 8 * R.ℓ) ^ 4 ≤ R.ℓ ^ 4 := by
        have : (7 / 8 * R.ℓ) ^ 4 = (7 / 8) ^ 4 * R.ℓ ^ 4 := by ring
        rw [this]; nlinarith [pow_pos hℓ 4]
      have hdn0 := norm_nonneg (nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ)
        (nW1H R k t))
      have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ2 hM')
        (by positivity : (0 : ℝ) ≤ |(t' k).2.1 - (t k).2.1| + 2 * evH R k t t')
      have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ4 (by norm_num : (0 : ℝ) ≤ 4))
        (by positivity : (0 : ℝ) ≤ 8 / 7 * |(t' k).1 - (t k).1| + 2 *
          ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖)
      have h3 : 4 * R.ℓ ^ 4 * (8 / 7 * |(t' k).1 - (t k).1|) ≤ 5 * R.ℓ ^ 4 * |(t' k).1 - (t k).1| := by
        nlinarith [pow_pos hℓ 4, abs_nonneg ((t' k).1 - (t k).1)]
      nlinarith
    have hbW : bWIn R cw k t t' ≤ eWH R k t t' + 28 * cw * ε ^ 2 * evH R k t t' := by
      unfold bWIn
      have hg2 : (t k).1 ^ 2 ≤ ε ^ 2 := by have := HC.H.g_pos; have := HC.H.g_le; gcongr
      have := mul_le_mul hζ (mul_le_mul_of_nonneg_left hg2 hcw) (by positivity) hev
      nlinarith
    have hκW : 0 ≤ κW := by positivity
    exact eW_rec hℓ hC₂ hκW hcw hcmu hΛ0 he.le H.he1 hε.le hε1 hM hV hev hew hdg hdμ hζ hdn hΔ
      hΔ0 ha hbW h1
  · -- the zero mode
    have h1 := ew_succ_le HC
    have h2 := nW1H_sub_le HC.H HC.H' (H.whH_le hk.le)
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    exact ew_rec hL hΛ0 hev hew hM hV hζ h2 hΔ h1

end Step

section Ind

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

set_option maxHeartbeats 2000000 in
/-- **The errors along two histories with fading memory.** If the past distances satisfy
`dist3(t_i, t'_i) ≤ M (4/3)^{j-1-i}` for `i < j`, the errors at `k ≤ j` are bounded by
`m_k = M (4/3)^{j-k}` times the constants. -/
theorem run_errors_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W Z : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i < j, Hist.dist3 (t i) (t' i) ≤ mW M j (i + 1)) {Cq Cl cS C₀ C₂ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC₂ : 0 ≤ C₂)
    (hβ : 0 ≤ bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ k < j, ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') (lD R Kc k t t') 1 (R.ℓ / 4))
    (hW : ∀ k < j, Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 (lD R Kc k t t') 1
          (R.ℓ / 4) + 4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + lD R Kc k t t' ^ 2 / (1 * (R.ℓ / 4)) ^ 2)))
    (hV : 0 ≤ V) (hW0 : 0 ≤ W) (hZ : 0 ≤ Z)
    (c1 : ka0 R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) +
      4 / 3 * (8 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 * W +
      (e + ε) * kAll R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
        (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂
        (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) cw * (5 / 2 * V + Z)) ≤ V)
    (c2 : 4 / 3 * (8 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2)) * W +
      (e + ε) * kAll R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
        (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂
        (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) cw * (1 + 4 / 3 * (5 / 2 * V + Z)) ≤ W)
    (c3 : 4 / 3 * ((8 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2)) * Z +
      (2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * (2 * Kc * (L : ℝ) ^ 8)) * (5 / 2 * V)) ≤ Z) :
    ∀ k ≤ j, (∀ i ≤ k, evH R i t t' ≤ V * mW M j i) ∧ eWH R k t t' ≤ W * mW M j k ∧
      ewH R k t t' ≤ Z * mW M j k := by
  set β := bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 with hβd
  set Λ0 := 2 * Kc * (L : ℝ) ^ 8 with hΛd
  set κW := C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) with hκd
  set cThv := cTh R.ℓ cw (cx κ cT) with hcd
  set ka := kAll R.ℓ β (cmu Λ cm) cThv Λ0 C₂ κW cw
  have hℓ : 0 < R.ℓ := Fact.out
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hκW : 0 ≤ κW := by positivity
  have hΛ0 : 0 ≤ Λ0 := by have := H.hKc; positivity
  have hcmu : 0 ≤ cmu Λ cm := ((H.cmp 0 (Nat.zero_le _))).hcmu
  have hcw : 0 ≤ cw := ((H.cmp 0 (Nat.zero_le _))).hcw
  have hcx : 0 ≤ cx κ cT := ((H.cmp 0 (Nat.zero_le _))).hcx
  have hcTh : 0 ≤ cThv := by
    unfold cThv cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := kAll_parts hℓ hβ hcmu hcTh hΛ0 hC₂ hκW hcw
  have hS : 0 ≤ e + ε := by linarith [(H.cmp 0 (Nat.zero_le _)).he, H.hε0]
  have hη : 0 ≤ (e + ε) * ka := by unfold ka kAll; positivity
  have ha0 : 0 ≤ ka0 R.ℓ β := by
    unfold ka0; have := kX_nonneg R.ℓ; have := (Real.exp_pos 1).le; positivity
  refine err_rec_w (a₀ := ka0 R.ℓ β) (a₁ := 8 * β) (η := (e + ε) * ka)
    (q := 8 * κW + 9 / (8 * (L : ℝ) ^ 2)) (b := 2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * Λ0) ha0
    (by positivity) hη (by positivity) (by positivity) hV hW0 hZ
    (by linarith only [c1, show 4 / 3 * (8 * β * W + (e + ε) * ka * (5 / 2 * V + Z)) =
      4 / 3 * (8 * β * W + (e + ε) * ka * (5 / 2 * V + Z)) by ring])
    (by linarith only [c2, show (e + ε) * ka * (1 + 4 / 3 * (5 / 2 * V + Z)) =
      (e + ε) * ka * (1 + 4 / 3 * (5 / 2 * V + Z)) by ring]) c3
    (mW M j) (mW_nonneg hM j) (fun k hk => le_of_eq (mW_succ hk))
    (fun k => evH R k t t') (fun k => eWH R k t t') (fun k => ewH R k t t') errs_zero ?_
  intro k hk hIH
  have hm' := mW_nonneg hM j (k + 1)
  have hVm : 0 ≤ 2 * V * mW M j (k + 1) := by positivity
  -- the covariance difference
  have hζIH : ∀ i ≤ k, eζH R i t t' ≤ V * (mW M j k * (4 / 3) ^ (k - i)) := fun i hi => by
    rw [← mW_le hi hk.le]
    exact (eζ_le_ev (H.cmp i (by omega)).H (H.cmp i (by omega)).H').trans (hIH i hi)
  have hΔ0 := lD_sq_le_w H.hKc hV (mW_nonneg hM j k) k t t' hζIH
  have hΔ : lD R Kc k t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * ((2 * V) * mW M j (k + 1)) := by
    rw [mW_succ hk] at hΔ0
    linarith only [hΔ0, show 3 * Kc * (L : ℝ) ^ 8 * (V * (4 / 3 * mW M j (k + 1))) =
      2 * Kc * (L : ℝ) ^ 8 * ((2 * V) * mW M j (k + 1)) by ring]
  have hdk : Hist.dist3 (t k) (t' k) ≤ mW M j (k + 1) := hd k hk
  obtain ⟨s1, s2, s3⟩ := run_step_w H hk hm' (by positivity : (0 : ℝ) ≤ 2 * V) hdk hΔ hC₀ hC₂ hβ
    (hkap k hk) (hW k hk)
  simp only [← hβd, ← hΛd, ← hκd, ← hcd] at s1 s2 s3
  have hev := evH_nonneg (R := R) (t := t) (t' := t') k
  have hew := ewH_nonneg (R := R) (t := t) (t' := t') k
  have heW : 0 ≤ eWH R k t t' := eWH_nonneg R k t t'
  have eVM : 2 * V * mW M j (k + 1) = (2 * V) * mW M j (k + 1) := by ring
  rw [← eVM] at s1 s2 s3
  refine ⟨s1.trans ?_, s2.trans ?_, s3.trans ?_⟩
  · have : kEv R.ℓ β (cmu Λ cm) cThv * evH R k t t' + kEw R.ℓ β (cmu Λ cm) * ewH R k t t' +
        kEV R.ℓ β Λ0 * (2 * V * mW M j (k + 1)) ≤
        ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1)) := by
      have a1 : kEv R.ℓ β (cmu Λ cm) cThv ≤ ka := by unfold ka kAll; linarith
      have a2 : kEw R.ℓ β (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a3 : kEV R.ℓ β Λ0 ≤ ka := by unfold ka kAll; linarith
      nlinarith [mul_le_mul_of_nonneg_right a1 hev, mul_le_mul_of_nonneg_right a2 hew,
        mul_le_mul_of_nonneg_right a3 hVm]
    have h1 := mul_le_mul_of_nonneg_left this hS
    have e1 : (e + ε) * ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1)) =
        (e + ε) * (ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1))) := by ring
    show _ ≤ ka0 R.ℓ β * mW M j (k + 1) + 8 * β * eWH R k t t' +
      (e + ε) * ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1))
    linarith only [h1, e1]
  · have : kWM R.ℓ C₂ * mW M j (k + 1) + kWv R.ℓ C₂ κW cw (cmu Λ cm) * evH R k t t' +
        kWw R.ℓ C₂ (cmu Λ cm) * ewH R k t t' + kWV R.ℓ C₂ κW cw Λ0 * (2 * V * mW M j (k + 1)) ≤
        ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1)) := by
      have a1 : kWM R.ℓ C₂ ≤ ka := by unfold ka kAll; linarith
      have a2 : kWv R.ℓ C₂ κW cw (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a3 : kWw R.ℓ C₂ (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a4 : kWV R.ℓ C₂ κW cw Λ0 ≤ ka := by unfold ka kAll; linarith
      nlinarith [mul_le_mul_of_nonneg_right a1 hm', mul_le_mul_of_nonneg_right a2 hev,
        mul_le_mul_of_nonneg_right a3 hew, mul_le_mul_of_nonneg_right a4 hVm]
    have h1 := mul_le_mul_of_nonneg_left this hS
    have h2 : 8 * κW * eWH R k t t' ≤ (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * eWH R k t t' :=
      mul_le_mul_of_nonneg_right (by have : 0 ≤ 9 / (8 * (L : ℝ) ^ 2) := by positivity
                                     linarith) heW
    have e1 : (e + ε) * ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' +
        2 * V * mW M j (k + 1)) = (e + ε) * (ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' +
        2 * V * mW M j (k + 1))) := by ring
    show _ ≤ (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * eWH R k t t' +
      (e + ε) * ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1))
    linarith only [h1, h2, e1]
  · have h2 : 9 / (8 * (L : ℝ) ^ 2) * ewH R k t t' ≤
        (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * ewH R k t t' :=
      mul_le_mul_of_nonneg_right (by linarith) hew
    linarith

end Ind

end

end Step2.LL

