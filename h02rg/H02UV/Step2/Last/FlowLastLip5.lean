import Step2.Last.FlowLastLip4

/-!
# The Lipschitz bounds at the step `j = N - 2` (namespace `Step2.LL`)

`lip_pair_top`: the bounds (LGd), (Lmz), (LZ) of `lip_pair_z` for one step `j` with `ValidAt`
below `j` and only `ValidAtL` at `j` (so `j = N - 2` is allowed), with the same Lipschitz
constant `C_L`; the bound (LT) is dropped (the outputs `D, K` of the step `N - 2` are not flow
coordinates), and the comparison hypothesis for `𝒲^lin` is only needed below `j`. In addition:
the zero mode entering the last step, `‖δ(Z_{j+2} w^{(1)}_{j+1}/L^{2(j+1)})‖ ≤ 2ℓ²|δζ_{j+1}| +
c_{NW} M` (`nW1H_top`).
-/


namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- The history constant of the zero mode after the step `j`. -/
def cNW (L : ℕ) (ℓ β Kc : ℝ) : ℝ :=
  9 / 8 * ((2 * ℓ ^ 2 * (2 * (2 * ka0 ℓ β + 1)) + 9 / 8 * (10 * cbb L ℓ Kc * (2 * ka0 ℓ β + 1))) /
    (L : ℝ) ^ 2 + 9 * (2 * Kc * (L : ℝ) ^ 8 * (2 * (2 * ka0 ℓ β + 1))))

section NW

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `‖Z_{j+2} w^{(1)}_{j+1}‖ ≤ ℓ² L^{2(j+1)}` after the step `j` (`ValidAtL` at `j`). -/
theorem nW1H_succ_le {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVj : ValidAtL R j)
    (t : Hist.Seq (Xs R)) : ‖nW1H R (j + 1) t‖ ≤ R.ℓ ^ 2 := by
  have hρ := hVj.2.2.2.2.1
  have h := Zw1_step hVj.2 (rawInv_hist R hρ j hV t) (Zw1_hist R hρ j hV t) (t j).1 (t j).2.1
    (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2)
  have hL : (0 : ℝ) < ((L : ℝ) ^ (j + 1)) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have e : nW1H R (j + 1) t = stZ' R (rawHist R (j + 1) t) * (rawHist R (j + 1) t).w1 /
      (L : ℂ) ^ (2 * (j + 1)) := rfl
  have e2 : (L : ℝ) ^ (2 * (j + 1)) = ((L : ℝ) ^ (j + 1)) ^ 2 := by ring
  rw [e, norm_div, norm_pow, Complex.norm_natCast, e2, div_le_iff₀ hL]
  exact h

/-- The zero mode after the step `j`: `‖δ nW1H_{j+1}‖ ≤ 2ℓ² |δζ_{j+1}| + (9/8) δŵ_{j+1}`. -/
theorem nW1H_succ_sub_le {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVj : ValidAtL R j)
    (t t' : Hist.Seq (Xs R)) :
    ‖nW1H R (j + 1) t' - nW1H R (j + 1) t‖ ≤
      2 * R.ℓ ^ 2 * eζH R (j + 1) t t' + 9 / 8 * ewH R (j + 1) t t' := by
  have hρ := hVj.2.2.2.2.1
  have hρ8 := hVj.2.2.2.2.2.1
  have hζ : ∀ tt : Hist.Seq (Xs R), ‖zetaH R (j + 1) tt‖ ≤ 1 / 8 := fun tt =>
    (absorb_le R hρ _ _).trans hρ8
  have hw' : ‖whH R (j + 1) t'‖ ≤ 2 * R.ℓ ^ 2 := by
    have h1 := nW1H_succ_le hV hVj t'
    have h2 : 7 / 8 ≤ ‖1 + zetaH R (j + 1) t'‖ := by
      linarith [norm_one_add_ge (ζ := zetaH R (j + 1) t'), hζ t']
    rw [nW1H_eq, norm_mul] at h1
    have h3 : 7 / 8 * ‖whH R (j + 1) t'‖ ≤ R.ℓ ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h1
    nlinarith [sq_nonneg R.ℓ, norm_nonneg (whH R (j + 1) t')]
  rw [nW1H_eq, nW1H_eq]
  have e : (1 + zetaH R (j + 1) t') * whH R (j + 1) t' - (1 + zetaH R (j + 1) t) * whH R (j + 1) t =
      (zetaH R (j + 1) t' - zetaH R (j + 1) t) * whH R (j + 1) t' +
        (1 + zetaH R (j + 1) t) * (whH R (j + 1) t' - whH R (j + 1) t) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖1 + zetaH R (j + 1) t‖ ≤ 9 / 8 :=
    (norm_add_le _ _).trans (by rw [norm_one]; linarith [hζ t])
  unfold eζH ewH
  have := mul_le_mul_of_nonneg_left hw' (norm_nonneg (zetaH R (j + 1) t' - zetaH R (j + 1) t))
  have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (whH R (j + 1) t' - whH R (j + 1) t))
  linarith

set_option maxHeartbeats 1000000 in
/-- **The zero mode entering the last step**, along two histories. -/
theorem nW1H_top {j : ℕ} {t t' : Hist.Seq (Xs R)} {Λ κ cm cT ε cz cw e Kc : ℝ}
    (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (hV : ∀ i < j, ValidAt R i) (hVj : ValidAtL R j)
    {M V Z β : ℝ} (hVd : V = 2 * ka0 R.ℓ β + 1) (hZd : Z = 10 * cbb L R.ℓ Kc * V)
    (hM : 0 ≤ M) (hV0 : 0 ≤ 2 * V) (hev : evH R j t t' ≤ (2 * V) * M)
    (hΔj : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * ((2 * V) * M))
    (hew : ewH R j t t' ≤ Z * M) :
    ‖nW1H R (j + 1) t - nW1H R (j + 1) t'‖ ≤
      2 * R.ℓ ^ 2 * ‖zetaH R (j + 1) t - zetaH R (j + 1) t'‖ + cNW L R.ℓ β Kc * M := by
  have hc : cNW L R.ℓ β Kc = 9 / 8 * ((2 * R.ℓ ^ 2 * (2 * V) + 9 / 8 * Z) / (L : ℝ) ^ 2 +
      9 * (2 * Kc * (L : ℝ) ^ 8 * (2 * V))) := by
    rw [hZd, hVd]; unfold cNW; ring
  rw [hc]
  have HC := H.cmp j le_rfl
  have h1 := nW1H_succ_sub_le hV hVj t t'
  have h2 := ew_succ_le HC
  have h3 := nW1H_sub_le HC.H HC.H' (H.whH_le le_rfl)
  have h4 := (eζ_le_ev HC.H HC.H').trans hev
  have hL : (0 : ℝ) < (L : ℝ) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hℓ2 : 0 ≤ 2 * R.ℓ ^ 2 := by positivity
  have h5 : ‖nW1H R j t' - nW1H R j t‖ ≤ 2 * R.ℓ ^ 2 * (2 * V) * M + 9 / 8 * Z * M := by
    have a := mul_le_mul_of_nonneg_left h4 hℓ2
    have b := mul_le_mul_of_nonneg_left hew (by norm_num : (0 : ℝ) ≤ 9 / 8)
    linarith only [h3, a, b]
  have h6 : ewH R (j + 1) t t' ≤ (2 * R.ℓ ^ 2 * (2 * V) + 9 / 8 * Z) / (L : ℝ) ^ 2 * M +
      9 * (2 * Kc * (L : ℝ) ^ 8 * (2 * V)) * M := by
    have a : ‖nW1H R j t' - nW1H R j t‖ / (L : ℝ) ^ 2 ≤
        (2 * R.ℓ ^ 2 * (2 * V) + 9 / 8 * Z) / (L : ℝ) ^ 2 * M := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL]
      linarith only [h5]
    have b : 9 * lD R Kc j t t' ^ 2 ≤ 9 * (2 * Kc * (L : ℝ) ^ 8 * (2 * V)) * M := by
      linarith only [hΔj]
    linarith only [h2, a, b]
  have h7 : eζH R (j + 1) t t' = ‖zetaH R (j + 1) t - zetaH R (j + 1) t'‖ := norm_sub_rev _ _
  rw [norm_sub_rev, ← h7]
  have := mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 9 / 8)
  linarith only [h1, this]

end NW

end

end Step2.LL

namespace Step2.LL


open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Pair

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 4000000 in
/-- **The Lipschitz bounds for a pair of histories, with the hidden coupling `ζ` kept separate.** -/
theorem lip_pair_top {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVj : ValidAtL R j)
    (hmj1 : |R.msq| * ((L : ℝ) ^ (j + 1)) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε cz cw Kc : ℝ}
    (hAP : ∀ k ≤ j, ∀ t : Hist.Seq (Xs R), Hist.InDh Λ β δ κ cg cm cT ε k t →
      APB R cz cw (t k).1 (rawHist R k t) k)
    (hCov : ∀ k ≤ j, ∀ t t' : Hist.Seq (Xs R),
      GoodCov2 k (lD R Kc k t t') (CvH R k t' - CvH R k t))
    {κK κD C₁ C₃ C₂ C₀W Cq Cl cS Cq' Cl' cS' : ℝ}
    (hcW : ∀ k < j, ∀ (t t' : Hist.Seq (Xs R)) (e ℓΔ : ℝ), Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ →
      e ≤ 1 / 2 → Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 ℓΔ 1 (R.ℓ / 4) +
          4 * (2 * (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + ℓΔ ^ 2 / (1 * (R.ℓ / 4)) ^ 2)))
    (hck : ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (e ℓΔ : ℝ), Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ →
      e ≤ 1 / 2 → ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4))
    (hsz : ∀ (k : ℕ) (t : Hist.Seq (Xs R)), DomH k t Λ κ cm cT ε cz cw →
      |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 → (t k).1 ≤ 1 → cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 →
      cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 ≤ 1 →
      Real.exp 1 * (cx κ cT * (t k).1 ^ 3) ≤ 1 →
      ∀ i : Fin 4, cwt L k i * ‖kapH R k t i - SD.shv R k (sdH R k t) i‖ ≤
        bRem L Cq' Cl' cS' (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t k).1 ^ 3)))
    (hcz : 0 ≤ cz) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hKc : 0 ≤ Kc)
    (hκK : 0 ≤ κK) (hκD : 0 ≤ κD) (hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃) (hC₂ : 0 ≤ C₂) (hC₀W : 0 ≤ C₀W)
    (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl) (hcS : 0 ≤ cS) (hCq' : 0 ≤ Cq') (hCl' : 0 ≤ Cl') (hcS' : 0 ≤ cS')
    (hL2 : 2 ≤ L) (hq : 8 * (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2) ≤ 1 / 2)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 2 * cz * ε ≤ R.ρ) (h16 : 2 * cz * ε ≤ 1 / 16)
    (hΔ : cDl (7 / 8 * R.ℓ) cz * ε ≤ 1 / 4)
    (hE1 : cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * ε ≤ 1 / 4)
    (hnd : 4 * cmu Λ cm * ε * R.ℓ ^ 2 ≤ 1 / 8)
    (hclo : (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) + 1) * ε *
      cCloW L R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) (cmu Λ cm)
        (cx κ cT) cw Kc C₂ (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) ≤ 1 / 2)
    (hsz1 : ε * cSz (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) R.ℓ ≤ R.ρ)
    (hsz2 : ε * (cSz (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) R.ℓ +
      cSn L (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) cz R.ℓ
        (cmu Λ cm)) ≤ 1 / 16) :
    let CL := cLipW L R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
      (bR1 L Cq' Cl' cS' R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) (cmu Λ cm) cz
      (cx κ cT) cw Kc C₂ (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) κK κD C₁ C₃
      (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm))
    ∀ t t' : Hist.Seq (Xs R), Hist.InDh Λ β δ κ cg cm cT ε j t →
      Hist.InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * Hist.dist3 (t i) (t' i) ≤ M) →
      |(rgData R).G j t - (rgData R).G j t' - ((t j).1 - (t' j).1)| ≤
        CL * ε * |(t j).1 - (t' j).1| +
        CL * ε * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ + CL * ε * M ∧
      |(rgData R).m j t - (rgData R).m j t'| ≤ CL * |(t j).1 - (t' j).1| +
        CL * ε * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ +
        CL * ε * M + 4 * ‖zetaH R j t - zetaH R j t'‖ ∧
      ‖zetaH R (j + 1) t - zetaH R (j + 1) t'‖ ≤
        CL * (|(t j).1 - (t' j).1| + ‖(t j).2.2 - (t' j).2.2‖) +
        CL * ε * (|(t j).2.1 - (t' j).2.1| + M) ∧
      ‖nW1H R (j + 1) t - nW1H R (j + 1) t'‖ ≤
        2 * R.ℓ ^ 2 * ‖zetaH R (j + 1) t - zetaH R (j + 1) t'‖ +
        cNW L R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) Kc * M := by
  intro CL t t' ht ht' M hM hd
  have hℓ : 0 < R.ℓ := Fact.out
  have hA : ∀ k ≤ j, APB R cz cw (t k).1 (rawHist R k t) k := fun k hk =>
    hAP k (by omega) t (InDh_le ht hk)
  have hA' : ∀ k ≤ j, APB R cz cw (t' k).1 (rawHist R k t') k := fun k hk =>
    hAP k (by omega) t' (InDh_le ht' hk)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hm : ∀ k ≤ j, |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 := fun k hk => by
    have h1 := hmj1
    have h2 : ((L : ℝ) ^ k) ^ 2 ≤ ((L : ℝ) ^ (j + 1)) ^ 2 := by
      have : (L : ℝ) ^ k ≤ (L : ℝ) ^ (j + 1) := pow_le_pow_right₀ hL1 (by omega)
      gcongr
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg R.msq)
    linarith
  have hC : ∀ k ≤ j, GoodCov2 k (lD R Kc k t t') (CvH R k t' - CvH R k t) := fun k hk =>
    hCov k hk t t'
  set cE := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) with hcEd
  have H := run_of hV hVj ht ht' hA hA' hm hC hcz hcw hcx hcmu hKc hε0 hε1 hρ h16 hΔ
    (hE1.trans (by norm_num)) hnd
  set e := cE * ε with hed
  have he := (H.cmp 0 (Nat.zero_le _)).he
  have hcE0 : 0 ≤ cE := by
    have := he.le; rw [hed] at this
    exact nonneg_of_mul_nonneg_left (by linarith) hε0
  -- the error recursion
  set β₀ := bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 with hβd
  have hβ0 : 0 ≤ β₀ := by
    rw [hβd]; unfold bRem
    have := BHsig_nonneg (L := L) (v := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
    have : 0 ≤ ((7 / 8 * R.ℓ) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have : 0 ≤ ((7 / 8 * R.ℓ) ^ 4)⁻¹ := inv_nonneg.2 (by positivity)
    have : 0 ≤ (R.ℓ ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have : 0 ≤ (R.ℓ ^ 4)⁻¹ := inv_nonneg.2 (by positivity)
    positivity
  set κW := C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) with hκWd
  have hκW : 0 ≤ κW := by positivity
  set kA := cA0 L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW with hkAd
  have hcTh : 0 ≤ cTh R.ℓ cw (cx κ cT) := by
    unfold cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hkA : 0 ≤ kA := by
    have hΛ : 0 ≤ cLam0 L Kc := by unfold cLam0; positivity
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := kAll_parts hℓ hβ0 hcmu hcTh hΛ hC₂ hκW hcw
    rw [hkAd]; unfold cA0 kAll; linarith
  have ha₀ : 0 ≤ ka0 R.ℓ β₀ := by
    unfold ka0; have := kX_nonneg R.ℓ; have := (Real.exp_pos 1).le; positivity
  have hbb : 0 ≤ cbb L R.ℓ Kc := by unfold cbb cLam0; positivity
  have hσ : 0 ≤ e + ε := by linarith
  have hsmall : ((e + ε) * kA) * (4 * (8 * β₀) * (1 + 4 * (2 * ka0 R.ℓ β₀ + 1) +
      2 * (10 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1))) + (4 * (2 * ka0 R.ℓ β₀ + 1) +
      2 * (10 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1)))) ≤ 1 / 2 := by
    have e1 : ((e + ε) * kA) * (4 * (8 * β₀) * (1 + 4 * (2 * ka0 R.ℓ β₀ + 1) +
      2 * (10 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1))) + (4 * (2 * ka0 R.ℓ β₀ + 1) +
      2 * (10 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1)))) = (cE + 1) * ε *
        cCloW L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW := by
      rw [hed, hkAd]; unfold cCloW cZ0w cV0; ring
    rw [e1]; exact hclo
  obtain ⟨c1, c2, c3⟩ := err_consts_w ha₀ (by positivity : (0 : ℝ) ≤ 8 * β₀) (by positivity)
    (by positivity : (0 : ℝ) ≤ 8 * κW + 9 / (8 * (L : ℝ) ^ 2)) hq hbb hsmall
  have hV0 : 0 ≤ 2 * ka0 R.ℓ β₀ + 1 := by positivity
  have hZ0 : 0 ≤ 10 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1) := by positivity
  have hW0 : 0 ≤ 3 * ((e + ε) * kA) * (1 + 4 * (2 * ka0 R.ℓ β₀ + 1) +
      2 * (10 * cbb L R.ℓ Kc * (2 * ka0 R.ℓ β₀ + 1))) := by positivity
  have hkAe : kA = kAll R.ℓ β₀ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂ κW cw := by
    rw [hkAd]; rfl
  have hbbe : cbb L R.ℓ Kc = 2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * (2 * Kc * (L : ℝ) ^ 8) := rfl
  rw [hkAe] at c1 c2
  rw [hbbe] at c3
  have hd' : ∀ i < j, Hist.dist3 (t i) (t' i) ≤ mW M j (i + 1) := fun i hi => by
    have h0 := hd i hi
    have hp : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ (j - 1 - i) := by positivity
    have h1 := mul_le_mul_of_nonneg_left h0 hp
    have e2 : (4 / 3 : ℝ) ^ (j - 1 - i) * ((3 / 4 : ℝ) ^ (j - 1 - i) * Hist.dist3 (t i) (t' i)) =
        Hist.dist3 (t i) (t' i) := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    unfold mW
    rw [show j - (i + 1) = j - 1 - i by omega]
    linarith only [h1, e2, show M * (4 / 3 : ℝ) ^ (j - 1 - i) = (4 / 3 : ℝ) ^ (j - 1 - i) * M by ring]
  have herr := run_errors_w H hM hd' hC₀W hC₂ hβ0
    (fun k hk => hck k t t' e (lD R Kc k t t') (H.cmp k hk.le) (hE1.trans (by norm_num)))
    (fun k hk => hcW k hk t t' e (lD R Kc k t t') (H.cmp k hk.le) (hE1.trans (by norm_num)))
    hV0 hW0 hZ0 c1 c2 c3
  obtain ⟨hevall, heW, hew⟩ := herr j le_rfl
  rw [mW_self] at heW hew
  set V := 2 * ka0 R.ℓ β₀ + 1
  set Z := 10 * cbb L R.ℓ Kc * V
  have hev : evH R j t t' ≤ (2 * V) * M := by
    have := hevall j le_rfl
    rw [mW_self] at this
    nlinarith
  have hΔj : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * ((2 * V) * M) := by
    have h := lD_sq_le_w (R := R) hKc hV0 hM j t t' (fun i hi =>
      (eζ_le_ev (H.cmp i hi).H (H.cmp i hi).H').trans (hevall i hi))
    have : 0 ≤ Kc * (L : ℝ) ^ 8 * (V * M) := by positivity
    linarith only [h, this, show 2 * Kc * (L : ℝ) ^ 8 * ((2 * V) * M) =
      4 * (Kc * (L : ℝ) ^ 8 * (V * M)) by ring, show 3 * Kc * (L : ℝ) ^ 8 * (V * M) =
      3 * (Kc * (L : ℝ) ^ 8 * (V * M)) by ring]
  have hV0' : 0 ≤ 2 * V := by positivity
  set W₁ := cW0w L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW with hW₁d
  have hW₁0 : 0 ≤ W₁ := by rw [hW₁d]; unfold cW0w; have := hV0; positivity
  have heW' : eWH R j t t' ≤ (e + ε) * W₁ * M := by
    refine heW.trans (le_of_eq ?_)
    rw [hW₁d]; unfold cW0w cZ0w cV0; rw [← hkAd]; ring
  have hZ0' : 0 ≤ Z := hZ0
  -- (LT)
  have HC := H.cmp j le_rfl
  -- the final-step facts
  set b₁ := bR1 L Cq' Cl' cS' R.ℓ cE (cx κ cT) with hb₁d
  have hb₁ : 0 ≤ b₁ := bR1_nonneg hCq' hCl' hcS' hcx
  have hsn : ε * cSn L b₁ cz R.ℓ (cmu Λ cm) ≤ 1 / 8 := by
    have : 0 ≤ ε * cSz b₁ R.ℓ := by unfold cSz; positivity
    linarith
  have hfin : ∀ tt : Hist.Seq (Xs R), Hist.InDh Λ β δ κ cg cm cT ε j tt →
      (∀ k ≤ j, APB R cz cw (tt k).1 (rawHist R k tt) k) →
      FinOne R j tt ε b₁ cz (cmu Λ cm) := fun tt htt hAt => by
    have HD := domH_of hV hVj htt hAt hcz hρ h16 (le_refl j)
    have hg := HD.g_pos
    have hgε := HD.g_le
    have hcDl : 0 ≤ cDl (7 / 8 * R.ℓ) cz := by
      unfold cDl; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
    have hd1 : cDl (7 / 8 * R.ℓ) cz * (tt j).1 ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left hgε hcDl).trans hΔ
    have hd2 : cE * (tt j).1 ≤ 1 := (mul_le_mul_of_nonneg_left hgε hcE0).trans (hE1.trans (by norm_num))
    have h1 : (tt j).1 ^ 3 ≤ ε := by
      have : (tt j).1 ^ 3 ≤ ε ^ 3 := by gcongr
      have : ε ^ 3 ≤ ε := by
        have := pow_le_pow_of_le_one hε0.le hε1 (show 1 ≤ 3 by norm_num); simpa using this
      linarith
    have h2 : 3 * cx κ cT ≤ cE := by
      rw [hcEd]; unfold cEr
      have : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
        unfold cVf; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
      linarith
    have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hd3 : Real.exp 1 * (cx κ cT * (tt j).1 ^ 3) ≤ 1 := by
      have a := mul_le_mul h3 (mul_le_mul_of_nonneg_left h1 hcx) (by positivity) (by norm_num)
      have b : 3 * (cx κ cT * ε) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right h2 hε0.le
        linarith
      linarith
    exact finOne_of HD hCq' hCl' hcS' hcw hcx hcmu hε1 (hm j le_rfl) hL2 (nW1H_le hV hVj tt le_rfl)
      (hsz j tt HD (hm j le_rfl) (hgε.trans hε1) hd1 hd2 hd3) hsz1 hsn
  have F := hfin t ht hA
  have F' := hfin t' ht' hA'
  have hkapj := hck j t t' e (lD R Kc j t t') HC (hE1.trans (by norm_num))
  have hLG := LGd_hist_w H F F' hM hV0' hW₁0 hZ0' hβ0 hb₁ hev hΔj heW' hew hβd hkapj hsz2
  have hLm := Lm_hist_z H F F' hM hV0' hW₁0 hZ0' hβ0 hb₁ hmj1 hev hΔj heW' hew hβd hkapj
    (by have : 0 ≤ ε * cSn L b₁ cz R.ℓ (cmu Λ cm) := by unfold cSn cSν cSY; positivity
        linarith)
  -- the constants
  set K₀ := cK0w L R.ℓ β₀ b₁ (cmu Λ cm) cz (cx κ cT) cw Kc C₂ κW with hK₀d
  set CT₀ := cTT κK κD C₁ C₃ (cKT0w L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW) (cx κ cT)
    (2 * cV0 R.ℓ β₀) with hCT₀d
  have hKeq : cKa L β₀ b₁ R.ℓ (cmu Λ cm) cz (2 * V) Z (2 * Kc * (L : ℝ) ^ 8)
      (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) (2 * V) W₁ Z) = K₀ := rfl
  have hCTeq : cTT κK κD C₁ C₃ (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8)
      (2 * V) W₁ Z) (cx κ cT) (2 * V) = CT₀ := rfl
  -- `δζ_{j+1}`
  have hkT : 0 ≤ kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) (2 * V) W₁ Z := by
    unfold kTh; have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8, k9, k10, -⟩ :=
    cKa_ge (β := β₀) (b₁ := b₁) (ℓ := R.ℓ) (cmu := cmu Λ cm) (cz := cz) (V := 2 * V) (Z := Z)
      (Λ0 := 2 * Kc * (L : ℝ) ^ 8) (kThv := kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT))
        (2 * Kc * (L : ℝ) ^ 8) (2 * V) W₁ Z) L hβ0 hb₁ hcmu hcz hV0' hZ0' (by positivity) hkT
  rw [hKeq] at k1 k2 k3 k4 k5 k8 k9 k10
  have Pz := pieces_hist_w H hM hV0' hW₁0 hZ0' hev hΔj heW' hew k1 k2 k3 k4 k5
  have hζd := dζ_hist_w H F F' hM hV0' hev hΔj hβd hkapj k8 k9 k10
  have hLZ := zeta_assemble Pz hζd
  rw [hKeq] at hLG hLm
  have hCLd : CL = (cE + 1) * (300 * K₀ ^ 4 + CT₀) + 500 * K₀ ^ 4 + 2 * K₀ := rfl
  have hK1 : 1 ≤ K₀ := by have := (Real.exp_pos 1).le; linarith
  have hK0 : 0 ≤ K₀ := by linarith
  have hCT0 : 0 ≤ CT₀ := by
    rw [hCT₀d]; unfold cTT cKT0w
    have hkT : 0 ≤ kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (cLam0 L Kc) (2 * cV0 R.ℓ β₀)
        (cW0w L R.ℓ β₀ (cmu Λ cm) (cx κ cT) cw Kc C₂ κW) (cZ0w L R.ℓ Kc β₀) := by
      unfold kTh cLam0 cV0 cW0w cZ0w cbb cLam0
      have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
      positivity
    have : 0 ≤ cV0 R.ℓ β₀ := hV0
    positivity
  have hK4 : 0 ≤ K₀ ^ 4 := by positivity
  have hK2 : K₀ ^ 2 ≤ K₀ ^ 4 := by
    have h1 : 1 ≤ K₀ ^ 2 := one_le_pow₀ hK1
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ K₀ ^ 2)
    linarith only [this, show K₀ ^ 2 * K₀ ^ 2 = K₀ ^ 4 by ring, show K₀ ^ 2 * 1 = K₀ ^ 2 by ring]
  have hεσ : e + ε = (cE + 1) * ε := by rw [hed]; ring
  set dx := ‖(t j).2.2 - (t' j).2.2‖
  set dg := |(t j).1 - (t' j).1|
  set dμ := |(t j).2.1 - (t' j).2.1|
  have hdx : ‖(t' j).2.2 - (t j).2.2‖ = dx := norm_sub_rev _ _
  have hdg : |(t' j).1 - (t j).1| = dg := abs_sub_comm _ _
  have hdμ : |(t' j).2.1 - (t j).2.1| = dμ := abs_sub_comm _ _
  rw [hdx, hdg, hdμ] at hLG hLm hLZ
  have hdx0 : 0 ≤ dx := norm_nonneg _
  have hdg0 : 0 ≤ dg := abs_nonneg _
  have hdμ0 : 0 ≤ dμ := abs_nonneg _
  have hQ : 0 ≤ dx + dg + dμ + M := by positivity
  have hCL1 : (cE + 1) * CT₀ ≤ CL := by
    rw [hCLd]; have h1 : 0 ≤ (cE + 1) * (300 * K₀ ^ 4) := by positivity
    have h2 : 0 ≤ 500 * K₀ ^ 4 + 2 * K₀ := by positivity
    linarith only [h1, h2, show (cE + 1) * (300 * K₀ ^ 4 + CT₀) = (cE + 1) * (300 * K₀ ^ 4) +
      (cE + 1) * CT₀ by ring]
  have hCL2 : (cE + 1) * (300 * K₀ ^ 4) ≤ CL := by
    rw [hCLd]; have h1 : 0 ≤ (cE + 1) * CT₀ := by positivity
    have h2 : 0 ≤ 500 * K₀ ^ 4 + 2 * K₀ := by positivity
    linarith only [h1, h2, show (cE + 1) * (300 * K₀ ^ 4 + CT₀) = (cE + 1) * (300 * K₀ ^ 4) +
      (cE + 1) * CT₀ by ring]
  have hCL3 : 500 * K₀ ^ 4 ≤ CL := by
    rw [hCLd]; have h1 : 0 ≤ (cE + 1) * (300 * K₀ ^ 4 + CT₀) := by positivity
    have h2 : 0 ≤ 2 * K₀ := by positivity
    linarith only [h1, h2]
  have hCL0 : 0 ≤ CL := le_trans (by positivity) hCL3
  have hTT : (e + ε) * CT₀ * (dx + dg + dμ + M) ≤ CL * ε * (dx + dg + dμ + M) := by
    rw [hεσ]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL1 hε0.le) hQ
    linarith only [this, show (cE + 1) * ε * CT₀ * (dx + dg + dμ + M) =
      (cE + 1) * CT₀ * ε * (dx + dg + dμ + M) by ring]
  have h300 : (e + ε) * (300 * K₀ ^ 4) ≤ CL * ε := by
    rw [hεσ]
    have a := mul_le_mul_of_nonneg_right hCL2 hε0.le
    linarith only [a, show (cE + 1) * ε * (300 * K₀ ^ 4) = (cE + 1) * (300 * K₀ ^ 4) * ε by ring]
  have h200 : (e + ε) * (200 * K₀ ^ 4) ≤ CL * ε := by
    have h0 : 0 ≤ (e + ε) * K₀ ^ 4 := by positivity
    linarith only [h300, h0, show (e + ε) * (200 * K₀ ^ 4) = 200 * ((e + ε) * K₀ ^ 4) by ring,
      show (e + ε) * (300 * K₀ ^ 4) = 300 * ((e + ε) * K₀ ^ 4) by ring]
  have h6 : (e + ε) * (6 * K₀ ^ 2) ≤ CL * ε := by
    have h0 : 0 ≤ e + ε := by rw [hεσ]; positivity
    have := mul_le_mul_of_nonneg_left hK2 h0
    linarith only [h300, this, show (e + ε) * (6 * K₀ ^ 2) = 6 * ((e + ε) * K₀ ^ 2) by ring,
      show (e + ε) * (300 * K₀ ^ 4) = 300 * ((e + ε) * K₀ ^ 4) by ring,
      mul_nonneg h0 hK4]
  have h11 : 11 * K₀ ^ 2 ≤ CL := by linarith only [hCL3, hK2, hK4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have a1 := mul_le_mul_of_nonneg_right h200 hdg0
    have a2 := mul_le_mul_of_nonneg_right h200 hdμ0
    have a3 := mul_le_mul_of_nonneg_right hCL3 hdx0
    have a4 := mul_le_mul_of_nonneg_right h200 hM
    linarith only [hLG, a1, a2, a3, a4]
  · have b1 : 300 * K₀ ^ 4 ≤ CL := by linarith only [hCL3, hK4]
    have a1 := mul_le_mul_of_nonneg_right b1 (add_nonneg hdg0 hdx0)
    have a2 := mul_le_mul_of_nonneg_right h300 hdμ0
    have a3 := mul_le_mul_of_nonneg_right h300 hM
    have e1 : eζH R j t t' = ‖zetaH R j t - zetaH R j t'‖ := norm_sub_rev _ _
    rw [e1] at hLm
    linarith only [hLm, a1, a2, a3, show CL * (dg + dx) = CL * dg + CL * dx by ring]
  · rw [norm_sub_rev]
    have a1 := mul_le_mul_of_nonneg_right h11 (add_nonneg hdg0 hdx0)
    have a2 := mul_le_mul_of_nonneg_right h6 (add_nonneg hdμ0 hM)
    have e2 : (e + ε) * (6 * K₀ ^ 2) * (dμ + M) = (e + ε) * (6 * K₀ ^ 2) * (dμ + M) := rfl
    linarith only [hLZ, a1, a2]
  · exact nW1H_top H hV hVj (β := β₀) rfl rfl hM hV0' hev hΔj hew

end Pair

end

end Step2.LL

