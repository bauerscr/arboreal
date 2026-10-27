import Step2.Last.FlowLastLip1

/-!
# The Lipschitz layer at the step `j = N - 2`, part 2 (namespace `Step2.LL`)

Copies (with the weakened `SD.OK`, `DomH`, `Cmp` of `Step2.Last.FlowLastLip1`) of the declarations of
`Step2/Lip/FlowLipSize`, `FlowLipInd`, `FlowLipRun`, `FlowLipGH`, `FlowLipGH2`, `FlowLipGH3` that depend
on the validity. `Run` shadows the original inside `Step2.LL`.
-/
-- from Step2/Lip/FlowLipSize.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Dom

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

/-- The input bounds at the radius `r = c_E g`. -/
theorem DomH.r_bounds (H : DomH k t Λ κ cm cT ε cz cw) (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hg1 : (t k).1 ≤ 1)
    (hΔ : cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4) :
    let r := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1
    Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t)) ≤ ENNReal.ofReal r ∧
      Fnorm k (7 / 8 * R.ℓ) ((sdH R k t).W + (sdH R k t).D) ≤ ENNReal.ofReal (r ^ 2) ∧
      Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t)) ≤
        ENNReal.ofReal (Real.exp 1 * (cx κ cT * (t k).1 ^ 3)) := by
  intro r
  have hℓ : 0 < R.ℓ := Fact.out
  have hA : 0 < R.A := Fact.out
  have hg := H.g_pos
  have hs := H.sdH_OK
  have hsm : cz * (t k).1 ≤ 1 / 16 := by have := H.czg; have := H.h16; linarith
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have := H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE := cEr_ge (R := R) hcw hcx hcV
  refine ⟨?_, ?_, ?_⟩
  · refine (hs.V_le (by positivity) H.hcz hsm hm).trans (ENNReal.ofReal_le_ofReal ?_)
    show cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) * (t k).1 ≤ cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1
    unfold cEr; nlinarith
  · refine (Fnorm_add_le _ _ (by positivity) (by positivity) hs.hWn hs.hDn).trans
      (ENNReal.ofReal_le_ofReal ?_)
    show cw * (t k).1 ^ 2 + cx κ cT * (t k).1 ^ 3 ≤ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2
    have h3 : (t k).1 ^ 3 ≤ (t k).1 ^ 2 := by nlinarith [sq_nonneg (t k).1]
    have hc2 : cw + cx κ cT ≤ cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) ^ 2 := by
      unfold cEr at hcE ⊢; nlinarith
    have := mul_le_mul_of_nonneg_left h3 hcx
    nlinarith [sq_nonneg (t k).1]
  · have h1 : R.A / 2 ≤ R.A * Real.exp (-(1 / 4)) := by
      have := Real.add_one_le_exp (-(1 / 4)); nlinarith
    exact (Knorm_mono_wt (by positivity) h1 _).trans
      (hs.Kf_le (by positivity) hA.le H.hcz hsm hm hΔ)

end Dom

set_option maxHeartbeats 1000000 in
/-- **The size of the coupling remainder of step `k`.** -/
theorem size_rem : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], 2 ≤ R.A →
    ∀ (k : ℕ) (t : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw : ℝ),
      DomH k t Λ κ cm cT ε cz cw →
      |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 → 0 ≤ cw → 0 ≤ cx κ cT → 0 ≤ cmu Λ cm → (t k).1 ≤ 1 →
      cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 →
      cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 ≤ 1 →
      Real.exp 1 * (cx κ cT * (t k).1 ^ 3) ≤ 1 →
      ∀ i : Fin 4, cwt L k i * ‖kapH R k t i - SD.shv R k (sdH R k t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t k).1 ^ 3)) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := coupRem_bound
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R _ _ hA2 k t Λ κ cm cT ε cz cw H hm hcw hcx hcmu hg1 hΔ hr hk i
  have hℓ : 0 < R.ℓ := Fact.out
  have hs := H.sdH_OK
  have hg := H.g_pos
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have := H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE := cEr_ge (R := R) hcw hcx hcV
  obtain ⟨hV, hWD, hKf⟩ := H.r_bounds hm hcw hcx hcmu hg1 hΔ
  have hr0 : 0 ≤ cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 := by positivity
  have hr2 : (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2 ≤ 1 := by nlinarith
  have e1 : kapH R k t i - SD.shv R k (sdH R k t) i =
      coupRem k R.i₀ (sdH R k t).C (nVec R k (sdH R k t).zh (sdH R k t).yh (sdH R k t).g
        (sdH R k t).μ (sdH R k t).w) ((sdH R k t).W + (sdH R k t).D) (SD.Kf R k (sdH R k t)) i := by
    have := SD.kap_eq R k (sdH R k t)
    rw [show kapH R k t = SD.kap R k (sdH R k t) from rfl, this, Pi.add_apply, add_sub_cancel_right]
  rw [e1]
  exact h L hL8 hLp N k hs.hk hs.hLg R.i₀ (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (by positivity) hℓ (by positivity)
    (by linarith) _ hs.hC hs.hCs hs.hCsym _ _ _ (add_mem hs.hW hs.hD) (hs.Kf_mem hL8) (R.A / 2)
    (by linarith) _ _ _ hr0 (sq_nonneg _) (by positivity) hr hr2 hk hV hWD hKf i

end

end Step2.LL


-- from Step2/Lip/FlowLipInd.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Err

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e ℓΔ : ℝ}

theorem eζ_le_ev (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw) :
    eζH R k t t' ≤ evH R k t t' := by
  unfold eζH evH
  rw [H.zetaH_eq, H'.zetaH_eq]
  have e : zhH R k t' + yhH R k t' - (zhH R k t + yhH R k t) =
      (zhH R k t' - zhH R k t) + (yhH R k t' - yhH R k t) := by ring
  rw [e]; exact norm_add_le _ _

/-- The zero mode `ŵ' = (1+ζ) ŵ` entering step `k`. -/
theorem nW1H_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw)
    {Bw : ℝ} (hw' : ‖whH R k t'‖ ≤ Bw) :
    ‖nW1H R k t' - nW1H R k t‖ ≤ Bw * eζH R k t t' + 9 / 8 * ewH R k t t' := by
  rw [nW1H_eq, nW1H_eq]
  have e : (1 + zetaH R k t') * whH R k t' - (1 + zetaH R k t) * whH R k t =
      (zetaH R k t' - zetaH R k t) * whH R k t' + (1 + zetaH R k t) * (whH R k t' - whH R k t) := by
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖1 + zetaH R k t‖ ≤ 9 / 8 :=
    (norm_add_le _ _).trans (by rw [norm_one]; linarith [H.zetaH_16])
  unfold eζH ewH
  have := mul_le_mul_of_nonneg_left hw' (norm_nonneg (zetaH R k t' - zetaH R k t))
  have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (whH R k t' - whH R k t))
  linarith

end Err

section Step

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e ℓΔ : ℝ}

theorem thetaH_eq (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ) :
    e ^ 2 * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
      (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4) = thetaH R k t t' cw (cx κ cT) e ℓΔ := by
  rw [relDist_mul H.he H.hℓ, thetaH, thetaIn]; ring

theorem thetaH_nonneg (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ) :
    0 ≤ thetaH R k t t' cw (cx κ cT) e ℓΔ := by
  have := H.aIn_nonneg; have := H.bWIn_nonneg; have := H.bDIn_nonneg; have := H.cIn_nonneg
  have := H.he; have := H.hℓ
  unfold thetaH thetaIn; positivity

/-- **The coupling errors after step `k`.** -/
theorem ev_succ_le (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ) {Cq Cl cS : ℝ}
    (hkap : ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)) :
    evH R (k + 1) t t' ≤ 8 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
      thetaH R k t t' cw (cx κ cT) e ℓΔ +
        (3 * (R.ℓ / 4) ^ 2 * ‖ghat (sdH R k t') - ghat (sdH R k t)‖ +
          3 * ‖ghat (sdH R k t)‖ * ℓΔ ^ 2) := by
  have HO := H.H.histOK
  have HO' := H.H'.histOK
  have hrem : ∀ i : Fin 4, i = 0 ∨ i = 1 → ‖(kapH R k t' i - kapH R k t i) -
      (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
          thetaH R k t t' cw (cx κ cT) e ℓΔ := by
    intro i hi
    have h := hkap i
    have hw : cwt L k i = 1 := by rcases hi with rfl | rfl <;> rfl
    rw [hw, one_mul, bRem_scale] at h
    have e2 : 4 * (e ^ 2 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) *
        relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
          (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4) =
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
          (e ^ 2 * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)) := by ring
    rw [e2, thetaH_eq H] at h
    exact h
  have hs := shv01_sub_le R k (sdH R k t) (sdH R k t') H.sOK.hzy H.sOK.hy H.sOK'.hzy H.sOK'.hy
    H.sOK'.hC H.hC
  have e0 : evH R (k + 1) t t' = ‖kapH R k t' 0 - kapH R k t 0‖ + ‖kapH R k t' 1 - kapH R k t 1‖ := by
    rw [evH, zhH_succ HO, zhH_succ HO', yhH_succ HO, yhH_succ HO']
  rw [e0]
  have a0 := hrem 0 (Or.inl rfl)
  have a1 := hrem 1 (Or.inr rfl)
  have b0 := norm_sub_le_norm_sub_add_norm_sub (kapH R k t' 0 - kapH R k t 0)
    (SD.shv R k (sdH R k t') 0 - SD.shv R k (sdH R k t) 0) 0
  have b1 := norm_sub_le_norm_sub_add_norm_sub (kapH R k t' 1 - kapH R k t 1)
    (SD.shv R k (sdH R k t') 1 - SD.shv R k (sdH R k t) 1) 0
  simp only [sub_zero] at b0 b1
  linarith

/-- **The `𝒲^lin` error after step `k`.** -/
theorem eW_succ_le (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ) {C₀ C₂ : ℝ} (hε : 0 < ε)
    (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
    (hW : Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 ℓΔ 1 (R.ℓ / 4) +
          4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + ℓΔ ^ 2 / (1 * (R.ℓ / 4)) ^ 2))) :
    eWH R (k + 1) t t' ≤ 16 * C₂ * (e * aIn R k t t' + 16 * e ^ 2 * ℓΔ ^ 2 / R.ℓ ^ 2) +
      8 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) *
        (bWIn R cw k t t' + 16 * ((cw + 1) * ε ^ 2) * ℓΔ ^ 2 / R.ℓ ^ 2) := by
  have HO := H.H.histOK
  have HO' := H.H'.histOK
  have he := H.he
  have hℓ := H.hℓ
  have hcw := H.hcw
  have hc : 0 < (cw + 1) * ε ^ 2 := by positivity
  rw [eWH, WhH_succ HO, WhH_succ HO']
  have hr : 0 ≤ 4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 ℓΔ 1 (R.ℓ / 4) +
      4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
        (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + ℓΔ ^ 2 / (1 * (R.ℓ / 4)) ^ 2) :=
    by
      have := relDist_nonneg (ℓΔ := ℓΔ) (τ := 1) (ℓC := R.ℓ / 4) he H.aIn_nonneg le_rfl le_rfl
      have := H.bWIn_nonneg
      positivity
  refine (ENNReal.toReal_le_of_le_ofReal hr hW).trans (le_of_eq ?_)
  unfold relDist
  field_simp
  ring

/-- **The zero-mode error after step `k`.** -/
theorem ew_succ_le (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ) :
    ewH R (k + 1) t t' ≤ ‖nW1H R k t' - nW1H R k t‖ / (L : ℝ) ^ 2 + 9 * ℓΔ ^ 2 := by
  have HO := H.H.histOK
  have HO' := H.H'.histOK
  have hk1 : k + 1 < N := by have := H.sOK.hk; omega
  have hz := zero_mode_le hk1 H.hC
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [ewH, whH_succ HO, whH_succ HO']
  have e1 : (nW1H R k t' * (L : ℂ) ^ (2 * k) + ∑ x, CvH R k t' x 0) / (L : ℂ) ^ (2 * (k + 1)) -
      (nW1H R k t * (L : ℂ) ^ (2 * k) + ∑ x, CvH R k t x 0) / (L : ℂ) ^ (2 * (k + 1)) =
      (nW1H R k t' - nW1H R k t) / (L : ℂ) ^ 2 +
        (∑ x, (CvH R k t' - CvH R k t) x 0) / (L : ℂ) ^ (2 * (k + 1)) := by
    simp only [Matrix.sub_apply, sum_sub_distrib]
    have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
    field_simp
    ring
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · rw [norm_div, norm_pow, Complex.norm_natCast]
  · rw [norm_div, norm_pow, Complex.norm_natCast, div_le_iff₀ (by positivity)]
    have e2 : ((L : ℝ) ^ (2 * (k + 1))) = ((L : ℝ) ^ (k + 1)) ^ 2 := by ring
    rw [e2]; linarith

/-- **The bound on `Θ_k`** by the differences of the coordinates and of the normalised states. -/
theorem thetaH_le (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ) :
    thetaH R k t t' cw (cx κ cT) e ℓΔ ≤ (1 + Real.exp 1) * ‖(t' k).2.2 - (t k).2.2‖ +
      eWH R k t t' + e * (cM * R.ℓ ^ 2 * |(t' k).2.1 - (t k).2.1| + 5 * R.ℓ ^ 4 * |(t' k).1 - (t k).1| +
        8 * R.ℓ ^ 4 * ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖ +
        2 * cM * R.ℓ ^ 2 * evH R k t t') +
      ε ^ 2 * cTh R.ℓ cw (cx κ cT) * evH R k t t' + 16 * e ^ 2 * ℓΔ ^ 2 / R.ℓ ^ 2 := by
  have hℓ := H.hℓ
  have he := H.he
  have hcw := H.hcw
  have hcx := H.hcx
  have hg := H.H.g_pos
  have hgε := H.H.g_le
  have hε1 := H.hε1
  have hζ := eζ_le_ev H.H H.H'
  have hζ0 : 0 ≤ eζH R k t t' := norm_nonneg _
  have hev0 : 0 ≤ evH R k t t' := by unfold evH; positivity
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  set dn := ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖
  set dg := |(t' k).1 - (t k).1|
  set dμ := |(t' k).2.1 - (t k).2.1|
  set ev := evH R k t t'
  have hdn : 0 ≤ dn := norm_nonneg _
  have hdg : 0 ≤ dg := abs_nonneg _
  have hdμ : 0 ≤ dμ := abs_nonneg _
  have hℓ2 : (7 / 8 * R.ℓ) ^ 2 ≤ R.ℓ ^ 2 := by nlinarith
  have hℓ4 : (7 / 8 * R.ℓ) ^ 4 ≤ R.ℓ ^ 4 := by
    have : (7 / 8 * R.ℓ) ^ 4 = (7 / 8) ^ 4 * R.ℓ ^ 4 := by ring
    rw [this]; nlinarith [pow_pos hℓ 4]
  have hg2 : (t k).1 ^ 2 ≤ ε ^ 2 := by gcongr
  have hg3 : (t k).1 ^ 3 ≤ ε ^ 2 := by
    have : (t k).1 ^ 3 ≤ ε ^ 3 := by gcongr
    have : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one (by linarith) hε1 (by norm_num)
    linarith
  -- aIn
  have ha : aIn R k t t' ≤ cM * R.ℓ ^ 2 * dμ + 5 * R.ℓ ^ 4 * dg + 8 * R.ℓ ^ 4 * dn +
      2 * cM * R.ℓ ^ 2 * ev := by
    unfold aIn aVf
    have h1 : cM * (7 / 8 * R.ℓ) ^ 2 * (dμ + 2 * ev) ≤ cM * R.ℓ ^ 2 * (dμ + 2 * ev) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ2 hM) (by positivity)
    have h2 : 4 * (7 / 8 * R.ℓ) ^ 4 * (8 / 7 * dg + 2 * dn) ≤ 4 * R.ℓ ^ 4 * (8 / 7 * dg + 2 * dn) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : 4 * R.ℓ ^ 4 * (8 / 7 * dg) ≤ 5 * R.ℓ ^ 4 * dg := by nlinarith [pow_pos hℓ 4]
    nlinarith
  -- bWIn
  have hbW : bWIn R cw k t t' ≤ eWH R k t t' + 28 * cw * ε ^ 2 * ev := by
    unfold bWIn
    have := mul_le_mul hζ (mul_le_mul_of_nonneg_left hg2 hcw) (by positivity) hev0
    nlinarith
  -- bDIn
  have hbD : bDIn R (cx κ cT) k t t' ≤ ‖(t' k).2.2 - (t k).2.2‖ + 28 * cx κ cT * ε ^ 2 * ev := by
    unfold bDIn
    have := mul_le_mul hζ (mul_le_mul_of_nonneg_left hg3 hcx) (by positivity) hev0
    nlinarith
  -- cIn
  have hcI : cIn R (cx κ cT) k t t' ≤ Real.exp 1 * (‖(t' k).2.2 - (t k).2.2‖ +
      28 * cx κ cT * ε ^ 2 * ev) + 128 * Real.exp 2 * cx κ cT * cM * R.ℓ ^ 2 * ε ^ 2 * ev := by
    unfold cIn
    have h1 := mul_le_mul_of_nonneg_left hbD (Real.exp_pos 1).le
    have h2 : 4 * (Real.exp 2 * (cx κ cT * (t k).1 ^ 3)) *
        (cM * (7 / 8 * R.ℓ) ^ 2 * (8 * ev) / (1 / 4)) =
        128 * Real.exp 2 * cx κ cT * cM * ((t k).1 ^ 3 * ((7 / 8 * R.ℓ) ^ 2 * ev)) := by ring
    have h3 : (t k).1 ^ 3 * ((7 / 8 * R.ℓ) ^ 2 * ev) ≤ ε ^ 2 * (R.ℓ ^ 2 * ev) :=
      mul_le_mul hg3 (mul_le_mul_of_nonneg_right hℓ2 hev0) (by positivity) (by positivity)
    have h4 : 0 ≤ 128 * Real.exp 2 * cx κ cT * cM := by positivity
    have := mul_le_mul_of_nonneg_left h3 h4
    rw [h2]
    nlinarith
  unfold thetaH thetaIn cTh
  have := mul_le_mul_of_nonneg_left ha he.le
  nlinarith [Real.exp_pos 1, Real.exp_pos 2]

end Step

end

end Step2.LL


-- from Step2/Lip/FlowLipRun.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Def

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

variable {R}

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

end Step

section Ind

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

end Ind

end

end Step2.LL


-- from Step2/Lip/FlowLipGH.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Sizes

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

/-- `L^{2(j+1)} |δ| ≤ ℓ²/32` for the covariance of the step. -/
theorem DomH.dl_le (H : DomH j t Λ κ cm cT ε cz cw) :
    ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC (sdH R j t).C‖ ≤ R.ℓ ^ 2 / 32 := by
  have hs := H.sdH_OK
  have := dlC_le' hs.hC hs.hCs hs.hCsym
  have e : (R.ℓ / 4) ^ 2 / 2 = R.ℓ ^ 2 / 32 := by ring
  linarith

/-- **The sizes at the final step.** -/
theorem DomH.sizes (H : DomH j t Λ κ cm cT ε cz cw) {Cq Cl cS : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hε1 : ε ≤ 1)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hrem : ∀ i : Fin 4, cwt L j i * ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t j).1 ^ 3))) :
    let b₁ := bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)
    ‖kapH R j t 0‖ + ‖kapH R j t 1‖ ≤ ε * (2 * b₁ + R.ℓ ^ 2 / 4) ∧
      ‖kapH R j t 3‖ ≤ ε * (b₁ + 2) ∧
      ‖(L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)‖ ≤
        ε * ((L : ℝ) ^ 2 * (b₁ + 3 * cz + R.ℓ ^ 2 / 7)) ∧
      ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
  intro b₁
  have hℓ : 0 < R.ℓ := Fact.out
  have hs := H.sdH_OK
  have hg := H.g_pos
  have hgε := H.g_le
  have hε0 : 0 ≤ ε := hg.le.trans hgε
  set cE := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) with hcE
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have := H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE0 : 0 ≤ cE := by rw [hcE]; unfold cEr; positivity
  -- the remainder
  have hB : bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cE * (t j).1) ((cE * (t j).1) ^ 2)
      (Real.exp 1 * (cx κ cT * (t j).1 ^ 3)) ≤ ε * b₁ := by
    have h1 : bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cE * (t j).1) ((cE * (t j).1) ^ 2)
        (Real.exp 1 * (cx κ cT * (t j).1 ^ 3)) ≤ bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4)
          (ε * cE) (ε ^ 2 * cE ^ 2) (ε * (Real.exp 1 * cx κ cT)) := by
      refine bRem_mono hCq hCl hcS (by positivity) (by nlinarith) (by
        have : ((t j).1) ^ 2 ≤ ε ^ 2 := by gcongr
        nlinarith [sq_nonneg cE]) ?_
      have h3 : (t j).1 ^ 3 ≤ ε := by
        have : (t j).1 ^ 3 ≤ ε ^ 3 := by gcongr
        have : ε ^ 3 ≤ ε := by
          have := pow_le_pow_of_le_one hε0 hε1 (show 1 ≤ 3 by norm_num); simpa using this
        linarith
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg (Real.exp_pos 1).le hcx)
      nlinarith [Real.exp_pos 1]
    refine h1.trans (bRem_scale_le hCq hCl hcS (sq_nonneg _) (by positivity) hε0 hε1)
  have hr : ∀ i : Fin 4, cwt L j i * ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ ≤ ε * b₁ :=
    fun i => (hrem i).trans hB
  have hsh := shv_le R j (sdH R j t) hs.hzy hs.hy hs.hC
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have h2 : |(sdH R j t).g| ≤ ε := by show |(t j).1| ≤ ε; rw [abs_of_pos hg]; exact hgε
    linarith
  have hc01 : cwt L j 0 = 1 ∧ cwt L j 1 = 1 ∧ cwt L j 3 = 1 ∧ cwt L j 2 = (L : ℝ) ^ (2 * j) :=
    ⟨rfl, rfl, rfl, rfl⟩
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have r3 := hr 3
  rw [hc01.1, one_mul] at r0
  rw [hc01.2.1, one_mul] at r1
  rw [hc01.2.2.1, one_mul] at r3
  rw [hc01.2.2.2] at r2
  have tri : ∀ i : Fin 4, ‖kapH R j t i‖ ≤ ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ +
      ‖SD.shv R j (sdH R j t) i‖ := fun i => by
    have := norm_add_le (kapH R j t i - SD.shv R j (sdH R j t) i) (SD.shv R j (sdH R j t) i)
    simpa using this
  refine ⟨?_, ?_, ?_, hĝ⟩
  · have t0 := tri 0
    have t1 := tri 1
    have h1 : 3 * (R.ℓ / 4) ^ 2 * ‖ghat (sdH R j t)‖ ≤ 3 * (R.ℓ / 4) ^ 2 * (8 / 7 * ε) :=
      mul_le_mul_of_nonneg_left hĝ (by positivity)
    have e1 : 3 * (R.ℓ / 4) ^ 2 * (8 / 7 * ε) = ε * (3 * R.ℓ ^ 2 / 14) := by ring
    have h2 : ε * (3 * R.ℓ ^ 2 / 14) ≤ ε * (R.ℓ ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg R.ℓ]) hε0
    have e2 : ε * (2 * b₁ + R.ℓ ^ 2 / 4) = ε * b₁ + ε * b₁ + ε * (R.ℓ ^ 2 / 4) := by ring
    linarith only [t0, t1, r0, r1, hsh.1, h1, e1, h2, e2]
  · have t3 := tri 3
    rw [hsh.2] at t3
    have e2 : ε * (b₁ + 2) = ε * b₁ + 2 * ε := by ring
    linarith only [t3, r3, hĝ, e2, hε0]
  · -- the relevant coupling
    have hsh2 := shv_dom R j (sdH R j t) hs.hzy hs.hy
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hLc : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
    have e2 : SD.shv R j (sdH R j t) 2 = ((t j).2.1 : ℂ) / (L : ℂ) ^ (2 * j) -
        (zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq +
        4 * ghat (sdH R j t) * dlC (sdH R j t).C := by
      rw [hsh2]; rfl
    have e3 : (L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ) =
        (L : ℂ) ^ 2 * ((L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2) -
          (L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq) +
          4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t).C) * ghat (sdH R j t)) := by
      rw [e2]; field_simp; ring
    rw [e3, norm_mul, norm_pow, Complex.norm_natCast]
    have hLj : ‖(L : ℂ) ^ (2 * j)‖ = (L : ℝ) ^ (2 * j) := by
      rw [norm_pow, Complex.norm_natCast]
    have a1 : ‖(L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2)‖ ≤ ε * b₁ := by
      rw [norm_mul, hLj]; exact r2
    have hζ8 : ‖zhH R j t + yhH R j t‖ ≤ 2 * cz * ε := H.zy_le.trans H.czg
    have hζ16 : ‖zhH R j t + yhH R j t‖ ≤ 1 / 8 := hζ8.trans (by linarith [H.h16])
    have a2 : ‖(L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ *
        R.msq)‖ ≤ 3 * cz * ε := by
      rw [norm_mul, norm_mul, norm_mul, hLj, Complex.norm_real, Real.norm_eq_abs]
      have b1 := norm_inv_one_add_le hζ16
      have e4 : (L : ℝ) ^ (2 * j) * (‖zhH R j t + yhH R j t‖ * ‖(1 + (zhH R j t + yhH R j t))⁻¹‖ *
          |R.msq|) = ‖zhH R j t + yhH R j t‖ * ‖(1 + (zhH R j t + yhH R j t))⁻¹‖ *
          (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by ring
      rw [e4]
      have b2 : ‖zhH R j t + yhH R j t‖ * ‖(1 + (zhH R j t + yhH R j t))⁻¹‖ ≤ 2 * cz * ε * (8 / 7) :=
        mul_le_mul hζ8 b1 (norm_nonneg _) (by have := H.hcz; positivity)
      have b3 := mul_le_mul b2 hm (by positivity) (by have := H.hcz; positivity)
      have hce : 0 ≤ cz * ε := mul_nonneg H.hcz hε0
      linarith only [b3, hce]
    have a3 : ‖4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t).C) * ghat (sdH R j t)‖ ≤
        ε * (R.ℓ ^ 2 / 7) := by
      rw [norm_mul, norm_mul, norm_mul, hLj, show ‖(4 : ℂ)‖ = 4 by norm_num]
      have hdl := H.dl_le
      have hLL : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
      have b1 : (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖ ≤ R.ℓ ^ 2 / 32 := by
        have e5 : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC (sdH R j t).C‖ =
            (L : ℝ) ^ 2 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖) := by ring
        rw [e5] at hdl
        have h0 : 0 ≤ (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖ := by positivity
        have := le_mul_of_one_le_left h0 hLL
        linarith only [this, hdl]
      have := mul_le_mul b1 hĝ (norm_nonneg _) (by positivity)
      have e7 : 4 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖) * ‖ghat (sdH R j t)‖ =
          4 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖ * ‖ghat (sdH R j t)‖) := by ring
      rw [e7]
      linarith only [this]
    have hsum := norm_add_le ((L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2) -
      (L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq))
      (4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t).C) * ghat (sdH R j t))
    have hsub := norm_sub_le ((L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2))
      ((L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq))
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left (hsum.trans (add_le_add (hsub.trans (add_le_add a1 a2)) a3))
      hL2
    have e6 : (L : ℝ) ^ 2 * (ε * b₁ + 3 * cz * ε + ε * (R.ℓ ^ 2 / 7)) =
        ε * ((L : ℝ) ^ 2 * (b₁ + 3 * cz + R.ℓ ^ 2 / 7)) := by ring
    linarith only [this, e6]

end Sizes

end

end Step2.LL


-- from Step2/Lip/FlowLipGH2.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Diff

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e ℓΔ : ℝ}

theorem kap_rem_scaled (H : Cmp R j t t' Λ κ cm cT ε cz cw e ℓΔ) {Cq Cl cS : ℝ}
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') ℓΔ 1 (R.ℓ / 4)) (i : Fin 4) :
    cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
        (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ := by
  have h := hkap i
  rw [bRem_scale] at h
  have e2 : 4 * (e ^ 2 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) *
      relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
        (cIn R (cx κ cT) j t t') ℓΔ 1 (R.ℓ / 4) =
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        (e ^ 2 * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
          (cIn R (cx κ cT) j t t') ℓΔ 1 (R.ℓ / 4)) := by ring
  rwa [e2, thetaH_eq H] at h

/-- **The quartic coupling.** -/
theorem d3_le (H : Cmp R j t t' Λ κ cm cT ε cz cw e ℓΔ) {Cq Cl cS : ℝ}
    (hk : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
        (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ) :
    ‖kapH R j t' 3 - kapH R j t 3‖ ≤ 4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4))
      2 2 2 * thetaH R j t t' cw (cx κ cT) e ℓΔ + ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
  have h := hk 3
  rw [show cwt L j 3 = 1 from rfl, one_mul] at h
  have h3 := shv3_sub R j (sdH R j t) (sdH R j t') H.sOK.hzy H.sOK.hy H.sOK'.hzy H.sOK'.hy
  have := norm_add_le ((kapH R j t' 3 - kapH R j t 3) -
    (SD.shv R j (sdH R j t') 3 - SD.shv R j (sdH R j t) 3))
    (SD.shv R j (sdH R j t') 3 - SD.shv R j (sdH R j t) 3)
  rw [sub_add_cancel, h3] at this
  rw [h3] at h
  linarith

/-- **The relevant coupling minus its leading part.** -/
theorem dY_le (H : Cmp R j t t' Λ κ cm cT ε cz cw e ℓΔ) {Cq Cl cS : ℝ}
    (hk : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
        (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ) :
    ‖((L : ℂ) ^ (2 * (j + 1)) * kapH R j t' 2 - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        ((L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ ≤
      (L : ℝ) ^ 2 * (4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' +
        R.ℓ ^ 2 / 8 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ +
        2 * ‖ghat (sdH R j t)‖ * ℓΔ ^ 2) := by
  have h := hk 2
  rw [show cwt L j 2 = (L : ℝ) ^ (2 * j) from rfl] at h
  have hs := H.sOK
  have hs' := H.sOK'
  have e2 : ∀ (tt : Hist.Seq (Xs R)), DomH j tt Λ κ cm cT ε cz cw →
      SD.shv R j (sdH R j tt) 2 = ((tt j).2.1 : ℂ) / (L : ℂ) ^ (2 * j) -
        (zhH R j tt + yhH R j tt) * (1 + (zhH R j tt + yhH R j tt))⁻¹ * R.msq +
        4 * ghat (sdH R j tt) * dlC (sdH R j tt).C := fun tt Ht => by
    rw [shv_dom R j (sdH R j tt) Ht.sdH_OK.hzy Ht.sdH_OK.hy]; rfl
  have hLc : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  set f : ℂ → ℂ := fun z => z * (1 + z)⁻¹
  have e3 : ((L : ℂ) ^ (2 * (j + 1)) * kapH R j t' 2 - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
      ((L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)) =
      (L : ℂ) ^ 2 * ((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)) -
        (L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)) +
        4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t)) +
        4 * ghat (sdH R j t) * ((L : ℂ) ^ (2 * j) * dlC ((sdH R j t').C - (sdH R j t).C))) := by
    rw [e2 t' H.H', e2 t H.H, ← dlC_sub]
    simp only [f]
    field_simp
    ring
  rw [e3, norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hLj : ‖(L : ℂ) ^ (2 * j)‖ = (L : ℝ) ^ (2 * j) := by rw [norm_pow, Complex.norm_natCast]
  have hLL : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  -- the pieces
  have a1 : ‖(L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
      (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2))‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ := by rw [norm_mul, hLj]; exact h
  have a2 : ‖(L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t))‖ ≤
      2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' := by
    rw [norm_mul, norm_mul, hLj, Complex.norm_real, Real.norm_eq_abs]
    have hζ := norm_div_one_add_sub_le (H.H'.zy_le.trans (H.H'.czg.trans (by linarith [H.H'.h16])))
      (H.H.zy_le.trans (H.H.czg.trans (by linarith [H.H.h16])))
    rw [← H.H.zetaH_eq, ← H.H'.zetaH_eq] at hζ
    have e4 : (L : ℝ) ^ (2 * j) * |R.msq| = |R.msq| * ((L : ℝ) ^ j) ^ 2 := by ring
    rw [e4]
    have := mul_le_mul_of_nonneg_left hζ (by positivity : (0 : ℝ) ≤ |R.msq| * ((L : ℝ) ^ j) ^ 2)
    simp only [f, H.H.zetaH_eq, H.H'.zetaH_eq] at this ⊢
    unfold eζH; rw [H.H.zetaH_eq, H.H'.zetaH_eq]
    linarith only [this]
  have a3 : ‖4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t))‖ ≤
      R.ℓ ^ 2 / 8 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
    rw [norm_mul, norm_mul, norm_mul, hLj, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hdl := H.H'.dl_le
    have b1 : (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t').C‖ ≤ R.ℓ ^ 2 / 32 := by
      have e5 : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC (sdH R j t').C‖ =
          (L : ℝ) ^ 2 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t').C‖) := by ring
      rw [e5] at hdl
      have h0 : 0 ≤ (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t').C‖ := by positivity
      have := le_mul_of_one_le_left h0 hLL
      linarith only [this, hdl]
    have := mul_le_mul_of_nonneg_right b1 (norm_nonneg (ghat (sdH R j t') - ghat (sdH R j t)))
    linarith only [this]
  have a4 : ‖4 * ghat (sdH R j t) * ((L : ℂ) ^ (2 * j) * dlC ((sdH R j t').C - (sdH R j t).C))‖ ≤
      2 * ‖ghat (sdH R j t)‖ * ℓΔ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hLj, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hsym : ∀ x y, ((sdH R j t').C - (sdH R j t).C) x y = ((sdH R j t').C - (sdH R j t).C) y x :=
      fun x y => by simp [Matrix.sub_apply, hs.hCsym x y, hs'.hCsym x y]
    have hCs : CSym ((sdH R j t').C - (sdH R j t).C) := fun T hT x y => by
      simp [Matrix.sub_apply, hs.hCs T hT x y, hs'.hCs T hT x y]
    have hdl : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ ≤ ℓΔ ^ 2 / 2 :=
      dlC_le' H.hC hCs hsym
    have b1 : (L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ ≤ ℓΔ ^ 2 / 2 := by
      have e5 : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ =
          (L : ℝ) ^ 2 * ((L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖) := by ring
      rw [e5] at hdl
      have h0 : 0 ≤ (L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ := by positivity
      have := le_mul_of_one_le_left h0 hLL
      linarith only [this, hdl]
    have := mul_le_mul_of_nonneg_left b1 (norm_nonneg (ghat (sdH R j t)))
    have e6 : 4 * ‖ghat (sdH R j t)‖ * ((L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖) =
        4 * (‖ghat (sdH R j t)‖ * ((L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖)) := by ring
    rw [e6]
    linarith only [this]
  have s1 := norm_add_le (((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)) -
        (L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)) +
        4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t))))
      (4 * ghat (sdH R j t) * ((L : ℂ) ^ (2 * j) * dlC ((sdH R j t').C - (sdH R j t).C)))
  have s2 := norm_add_le ((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)) -
        (L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)))
      (4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t)))
  have s3 := norm_sub_le ((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)))
      ((L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)))
  linarith only [s1, s2, s3, a1, a2, a3, a4]

end Diff

end

end Step2.LL


-- from Step2/Lip/FlowLipGH3.lean
namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Core

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

/-- `|ŵ_{j+1}| ≤ ℓ²`. -/
theorem DomH.whH_succ_le (H : DomH j t Λ κ cm cT ε cz cw) (hL2 : 2 ≤ L)
    (hnW : ‖nW1H R j t‖ ≤ R.ℓ ^ 2) : ‖whH R (j + 1) t‖ ≤ R.ℓ ^ 2 := by
  have HO := H.histOK
  have hs := H.sdH_OK
  have hk1 : j + 1 < N := by have := hs.hk; omega
  have hz : ‖∑ x, CvH R j t x 0‖ ≤ 9 * ((L : ℝ) ^ (j + 1)) ^ 2 * (R.ℓ / 4) ^ 2 :=
    zero_mode_le hk1 hs.hC
  have hL : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  rw [whH_succ HO]
  have hLp : (0 : ℝ) < (L : ℝ) ^ (2 * (j + 1)) := by positivity
  rw [norm_div, norm_pow, Complex.norm_natCast, div_le_iff₀ hLp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have e1 : (L : ℝ) ^ (2 * (j + 1)) = (L : ℝ) ^ 2 * (L : ℝ) ^ (2 * j) := by ring
  have e2 : ((L : ℝ) ^ (j + 1)) ^ 2 = (L : ℝ) ^ (2 * (j + 1)) := by ring
  rw [e2] at hz
  have h1 : ‖nW1H R j t‖ * (L : ℝ) ^ (2 * j) ≤ R.ℓ ^ 2 * (L : ℝ) ^ (2 * j) :=
    mul_le_mul_of_nonneg_right hnW (by positivity)
  have hLj : (0 : ℝ) ≤ (L : ℝ) ^ (2 * j) := by positivity
  have h2 : R.ℓ ^ 2 * (L : ℝ) ^ (2 * j) ≤ R.ℓ ^ 2 / 4 * (L : ℝ) ^ (2 * (j + 1)) := by
    rw [e1]
    have : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have hℓ := sq_nonneg R.ℓ
    nlinarith [mul_nonneg hℓ hLj]
  have h3 : 9 * (L : ℝ) ^ (2 * (j + 1)) * (R.ℓ / 4) ^ 2 = 9 / 16 * R.ℓ ^ 2 * (L : ℝ) ^ (2 * (j + 1)) := by
    ring
  have h4 := mul_nonneg (sq_nonneg R.ℓ) hLp.le
  linarith only [h1, h2, h3, hz, h4]

end Core

end

end Step2.LL

