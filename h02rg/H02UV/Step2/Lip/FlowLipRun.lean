import Step2.Lip.FlowLipRec

/-!
# The induction along two histories (Lipschitz bounds, part 23)

`lD R Kc k t t'` is the field scale of the difference of the normalised covariances of step `k`
(`prop_C5_lip` with ratio `1/2`), `lD² = K_c L⁸ ∑_{i≤k} 2^{-(k-i)} |δζ_i|`.

`Run` collects the hypotheses for comparing two histories at all steps `k ≤ j`. Under `Run`, the
errors of the normalised states satisfy the recursion of `err_rec` (`run_step`), hence
(`run_errors`) `ev_k ≤ V M`, `eW_k ≤ W M`, `ew_k ≤ Z M` for `k ≤ j`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

theorem geom_half_sum (k : ℕ) : ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) ≤ 2 := by
  have e : ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) = ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ i :=
    sum_range_reflect (fun i => (1 / 2 : ℝ) ^ i) (k + 1)
  rw [e]
  have := sum_geometric_two_le (k + 1)
  simpa [one_div] using this

section Def

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The field scale of the difference of the covariances. -/
def lD (Kc : ℝ) (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ :=
  ellLip 2 L (Kc * ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * eζH R i t t') k

variable {R}

theorem lD_nonneg (Kc : ℝ) (k : ℕ) (t t' : Hist.Seq (Xs R)) : 0 ≤ lD R Kc k t t' :=
  ellLip_two_nonneg _ _ _

/-- `lD² ≤ Λ₀ V M` with `Λ₀ = 2 K_c L⁸` if `|δζ_i| ≤ V M` for `i ≤ k`. -/
theorem lD_sq_le {Kc V M : ℝ} (hKc : 0 ≤ Kc) (k : ℕ) (t t' : Hist.Seq (Xs R))
    (h : ∀ i ≤ k, eζH R i t t' ≤ V * M) :
    lD R Kc k t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M) := by
  have hS0 : 0 ≤ ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * eζH R i t t' :=
    sum_nonneg fun i _ => mul_nonneg (by positivity) (norm_nonneg _)
  rw [lD, ellLip_two_sq L (mul_nonneg hKc hS0)]
  have hS : ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * eζH R i t t' ≤ 2 * (V * M) := by
    have hVM : 0 ≤ V * M := (norm_nonneg _).trans (h 0 (Nat.zero_le _))
    calc ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * eζH R i t t'
        ≤ ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * (V * M) :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
            (h i (by have := mem_range.1 hi; omega)) (by positivity)
      _ = (∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i)) * (V * M) := by rw [sum_mul]
      _ ≤ 2 * (V * M) := mul_le_mul_of_nonneg_right (geom_half_sum k) hVM
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ (2 * pPhi 2) := by positivity
  have e8 : (L : ℝ) ^ (2 * pPhi 2) = (L : ℝ) ^ 8 := by simp [pPhi]
  rw [e8] at hL ⊢
  have := mul_le_mul_of_nonneg_left hS hKc
  nlinarith

end Def

/-- **The hypotheses for comparing two histories up to step `j`.** -/
structure Run (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (j : ℕ)
    (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e Kc : ℝ) : Prop where
  cmp : ∀ k ≤ j, Cmp R k t t' Λ κ cm cT ε cz cw e (lD R Kc k t t')
  nW : ∀ k ≤ j, ‖nW1H R k t‖ ≤ R.ℓ ^ 2 ∧ ‖nW1H R k t'‖ ≤ R.ℓ ^ 2
  nd : ∀ k ≤ j, ‖4 * ((t k).2.1 : ℂ) * nW1H R k t‖ ≤ 1 / 8 ∧
    ‖4 * ((t' k).2.1 : ℂ) * nW1H R k t'‖ ≤ 1 / 8
  hKc : 0 ≤ Kc
  he1 : e ≤ 1
  hε0 : 0 < ε

namespace Run

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ} (H : Run R j t t' Λ κ cm cT ε cz cw e Kc)
include H

theorem whH_le {k : ℕ} (hk : k ≤ j) : ‖whH R k t'‖ ≤ 2 * R.ℓ ^ 2 := by
  have hD := (H.cmp k hk).H'
  have h1 := (H.nW k hk).2
  have hζ := hD.zetaH_16
  have hne : (1 + zetaH R k t') ≠ 0 := one_add_ne_zero (by linarith)
  have e : whH R k t' = nW1H R k t' / (1 + zetaH R k t') := by
    rw [nW1H_eq, mul_div_cancel_left₀ _ hne]
  rw [e, norm_div]
  have h2 : 15 / 16 ≤ ‖1 + zetaH R k t'‖ := by linarith [norm_one_add_ge (ζ := zetaH R k t')]
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  nlinarith

/-- `dn ≤ 4(ℓ² dμ + c_μ ε (2ℓ² δζ + 9/8 δŵ))`. -/
theorem dn_le {k : ℕ} (hk : k ≤ j) :
    ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖ ≤
      4 * (R.ℓ ^ 2 * |(t' k).2.1 - (t k).2.1| + cmu Λ cm * ε *
        (2 * R.ℓ ^ 2 * eζH R k t t' + 9 / 8 * ewH R k t t')) := by
  have HC := H.cmp k hk
  have hμ : |(t' k).2.1| ≤ cmu Λ cm * ε :=
    HC.H'.hD.2.2.1.trans (mul_le_mul_of_nonneg_left HC.H'.g_le HC.hcmu)
  have h1 := nCor_sub_le hμ (H.nW k hk).1 (H.nd k hk).1 (H.nd k hk).2
  have h2 := nW1H_sub_le HC.H HC.H' (H.whH_le hk)
  have h3 : cmu Λ cm * ε * ‖nW1H R k t' - nW1H R k t‖ ≤
      cmu Λ cm * ε * (2 * R.ℓ ^ 2 * eζH R k t t' + 9 / 8 * ewH R k t t') :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg HC.hcmu H.hε0.le)
  linarith

end Run

section Step

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

/-- The input differences at step `k` are bounded by `M`. -/
theorem dist3_parts {k : ℕ} {M : ℝ} (h : Hist.dist3 (t k) (t' k) ≤ M) :
    ‖(t' k).2.2 - (t k).2.2‖ ≤ M ∧ |(t' k).1 - (t k).1| ≤ M ∧ |(t' k).2.1 - (t k).2.1| ≤ M := by
  unfold Hist.dist3 at h
  rw [norm_sub_rev, abs_sub_comm, abs_sub_comm (t' k).2.1]
  have := norm_nonneg ((t k).2.2 - (t' k).2.2)
  have := abs_nonneg ((t k).1 - (t' k).1)
  have := abs_nonneg ((t k).2.1 - (t' k).2.1)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem evH_nonneg (k : ℕ) : 0 ≤ evH R k t t' := by unfold evH; positivity
theorem ewH_nonneg (k : ℕ) : 0 ≤ ewH R k t t' := norm_nonneg _

set_option maxHeartbeats 1000000 in
/-- **One step of the error recursion.** -/
theorem run_step (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {k : ℕ} (hk : k < j) {M V : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hd : Hist.dist3 (t k) (t' k) ≤ M)
    (hIH : ∀ i ≤ k, evH R i t t' ≤ V * M) {Cq Cl cS C₀ C₂ : ℝ} (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
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
  have hζIH : ∀ i ≤ k, eζH R i t t' ≤ V * M := fun i hi =>
    (eζ_le_ev (H.cmp i (by omega)).H (H.cmp i (by omega)).H').trans (hIH i hi)
  have hΔ := lD_sq_le H.hKc k t t' hζIH
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

/-- The total constant of the small terms. -/
def kAll (ℓ β cmu cThv Λ0 C₂ κW cw : ℝ) : ℝ :=
  kEv ℓ β cmu cThv + kEw ℓ β cmu + kEV ℓ β Λ0 + kWM ℓ C₂ + kWv ℓ C₂ κW cw cmu + kWw ℓ C₂ cmu +
    kWV ℓ C₂ κW cw Λ0

theorem kAll_parts {ℓ β cmu cThv Λ0 C₂ κW cw : ℝ} (hℓ : 0 < ℓ) (hβ : 0 ≤ β) (hcmu : 0 ≤ cmu)
    (hc : 0 ≤ cThv) (hΛ0 : 0 ≤ Λ0) (hC₂ : 0 ≤ C₂) (hκW : 0 ≤ κW) (hcw : 0 ≤ cw) :
    0 ≤ kEv ℓ β cmu cThv ∧ 0 ≤ kEw ℓ β cmu ∧ 0 ≤ kEV ℓ β Λ0 ∧ 0 ≤ kWM ℓ C₂ ∧
      0 ≤ kWv ℓ C₂ κW cw cmu ∧ 0 ≤ kWw ℓ C₂ cmu ∧ 0 ≤ kWV ℓ C₂ κW cw Λ0 := by
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have h1 : 0 ≤ kc1 ℓ cmu := by unfold kc1; positivity
  have h2 : 0 ≤ kc2 ℓ cmu := by unfold kc2; positivity
  have h3 := kX_nonneg ℓ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (unfold kEv; positivity) | (unfold kEw; positivity) | (unfold kEV; positivity)
    | (unfold kWM; positivity) | (unfold kWv; positivity) | (unfold kWw; positivity)
    | (unfold kWV; positivity)

section Ind

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

theorem errs_zero : evH R 0 t t' = 0 ∧ eWH R 0 t t' = 0 ∧ ewH R 0 t t' = 0 := by
  have e : rawHist R 0 t' = rawHist R 0 t := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [evH, zhH, yhH, e]
  · simp [eWH, WhH, uH, e, Fnorm, Step.Tj_zero]
  · simp [ewH, whH, e]

set_option maxHeartbeats 1000000 in
/-- **The errors along two histories.** -/
theorem run_errors (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W Z : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i < j, Hist.dist3 (t i) (t' i) ≤ M) {Cq Cl cS C₀ C₂ : ℝ} (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
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
      8 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 * W +
      (e + ε) * kAll R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
        (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂
        (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) cw * (2 * V + Z) ≤ V)
    (c2 : (8 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2)) * W +
      (e + ε) * kAll R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
        (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂
        (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) cw * (1 + 2 * V + Z) ≤ W)
    (c3 : (8 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2)) * Z +
      (2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * (2 * Kc * (L : ℝ) ^ 8)) * (2 * V) ≤ Z) :
    ∀ k ≤ j, (∀ i ≤ k, evH R i t t' ≤ V * M) ∧ eWH R k t t' ≤ W * M ∧ ewH R k t t' ≤ Z * M := by
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
  refine err_rec (a₀ := ka0 R.ℓ β) (a₁ := 8 * β) (η := (e + ε) * ka)
    (q := 8 * κW + 9 / (8 * (L : ℝ) ^ 2)) (b := 2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * Λ0) hM
    (by positivity) hη (by positivity) (by positivity) hV hW0 hZ c1 c2 c3
    (fun k => evH R k t t') (fun k => eWH R k t t') (fun k => ewH R k t t') errs_zero ?_
  intro k hk hIH
  obtain ⟨s1, s2, s3⟩ := run_step H hk hM hV (hd k hk) hIH hC₀ hC₂ hβ (hkap k hk) (hW k hk)
  simp only [← hβd, ← hΛd, ← hκd, ← hcd] at s1 s2 s3
  have hev := evH_nonneg (R := R) (t := t) (t' := t') k
  have hew := ewH_nonneg (R := R) (t := t) (t' := t') k
  have heW : 0 ≤ eWH R k t t' := eWH_nonneg R k t t'
  have hVM : 0 ≤ V * M := by positivity
  refine ⟨s1.trans ?_, s2.trans ?_, s3.trans ?_⟩
  · have : kEv R.ℓ β (cmu Λ cm) cThv * evH R k t t' + kEw R.ℓ β (cmu Λ cm) * ewH R k t t' +
        kEV R.ℓ β Λ0 * (V * M) ≤ ka * (evH R k t t' + ewH R k t t' + V * M) := by
      have a1 : kEv R.ℓ β (cmu Λ cm) cThv ≤ ka := by unfold ka kAll; linarith
      have a2 : kEw R.ℓ β (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a3 : kEV R.ℓ β Λ0 ≤ ka := by unfold ka kAll; linarith
      nlinarith [mul_le_mul_of_nonneg_right a1 hev, mul_le_mul_of_nonneg_right a2 hew,
        mul_le_mul_of_nonneg_right a3 hVM]
    have h1 := mul_le_mul_of_nonneg_left this hS
    have e1 : (e + ε) * ka * (evH R k t t' + ewH R k t t' + V * M) =
        (e + ε) * (ka * (evH R k t t' + ewH R k t t' + V * M)) := by ring
    show _ ≤ ka0 R.ℓ β * M + 8 * β * eWH R k t t' +
      (e + ε) * ka * (evH R k t t' + ewH R k t t' + V * M)
    linarith only [h1, e1]
  · have : kWM R.ℓ C₂ * M + kWv R.ℓ C₂ κW cw (cmu Λ cm) * evH R k t t' +
        kWw R.ℓ C₂ (cmu Λ cm) * ewH R k t t' + kWV R.ℓ C₂ κW cw Λ0 * (V * M) ≤
        ka * (M + evH R k t t' + ewH R k t t' + V * M) := by
      have a1 : kWM R.ℓ C₂ ≤ ka := by unfold ka kAll; linarith
      have a2 : kWv R.ℓ C₂ κW cw (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a3 : kWw R.ℓ C₂ (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a4 : kWV R.ℓ C₂ κW cw Λ0 ≤ ka := by unfold ka kAll; linarith
      nlinarith [mul_le_mul_of_nonneg_right a1 hM, mul_le_mul_of_nonneg_right a2 hev,
        mul_le_mul_of_nonneg_right a3 hew, mul_le_mul_of_nonneg_right a4 hVM]
    have h1 := mul_le_mul_of_nonneg_left this hS
    have h2 : 8 * κW * eWH R k t t' ≤ (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * eWH R k t t' :=
      mul_le_mul_of_nonneg_right (by have : 0 ≤ 9 / (8 * (L : ℝ) ^ 2) := by positivity
                                     linarith) heW
    have e1 : (e + ε) * ka * (M + evH R k t t' + ewH R k t t' + V * M) =
        (e + ε) * (ka * (M + evH R k t t' + ewH R k t t' + V * M)) := by ring
    show _ ≤ (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * eWH R k t t' +
      (e + ε) * ka * (M + evH R k t t' + ewH R k t t' + V * M)
    linarith only [h1, h2, e1]
  · have h2 : 9 / (8 * (L : ℝ) ^ 2) * ewH R k t t' ≤ (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * ewH R k t t' :=
      mul_le_mul_of_nonneg_right (by linarith) hew
    linarith

end Ind

end

end Step2
