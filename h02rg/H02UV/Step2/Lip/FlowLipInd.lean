import Step2.Lip.FlowLipSize
import Step2.Lip.FlowLipErr
import Step2.Flow.FlowF1

/-!
# The errors of one step along two histories (Lipschitz bounds, part 21)

For two histories compared at step `k` (`Cmp`), with
`Θ_k = e·aIn + bWIn + bDIn + cIn + 16 e² ℓ_Δ²/ℓ²` (`thetaIn`), the errors of the normalised
state at `k + 1` are bounded in terms of `Θ_k` and the input differences:
* `ev_succ_le`: `ev_{k+1} ≤ 8 β_R Θ_k + 3(ℓ/4)² |δĝ| + 3|ĝ| ℓ_Δ²`;
* `eW_succ_le`: `eW_{k+1} ≤ 16 C₂ (e aIn + 16 e²ℓ_Δ²/ℓ²) + 8κ_W (bWIn + 16(c_w+1)ε²ℓ_Δ²/ℓ²)`;
* `ew_succ_le`: `ew_{k+1} ≤ L^{-2} |δŵ'| + 9 ℓ_Δ²`;
and `thetaIn_le` bounds `Θ_k` by the differences of the coordinates and the states.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-! ### Algebra -/

theorem relDist_mul {e a b c ℓΔ ℓ : ℝ} (he : 0 < e) (hℓ : 0 < ℓ) :
    e ^ 2 * relDist e a b c ℓΔ 1 (ℓ / 4) = e * a + b + c + 16 * e ^ 2 * ℓΔ ^ 2 / ℓ ^ 2 := by
  unfold relDist
  field_simp
  ring

theorem bRem_scale (L : ℕ) (Cq Cl cS ℓi ℓ ℓC e : ℝ) :
    bRem L Cq Cl cS ℓi ℓ ℓC (2 * e) (2 * e ^ 2) (2 * e ^ 2) =
      e ^ 2 * bRem L Cq Cl cS ℓi ℓ ℓC 2 2 2 := by
  unfold bRem BH.sig
  ring

/-- `Θ = e·aIn + bWIn + bDIn + cIn + 16 e² ℓ_Δ²/ℓ²`. -/
def thetaIn (e a b c d ℓΔ ℓ : ℝ) : ℝ := e * a + b + c + d + 16 * e ^ 2 * ℓΔ ^ 2 / ℓ ^ 2

theorem nCor_dom {μ w : ℂ} (h : ‖4 * μ * w‖ ≤ 1 / 8) : nCor μ w = 4 * μ * w :=
  clampDisk_of_le h

/-! ### The errors along two histories -/

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

/-- **The difference of the coordinate change `n`** on the domain. -/
theorem nCor_sub_le {μ μ' : ℝ} {w w' : ℂ} {Bμ Bw : ℝ} (hμ' : |μ'| ≤ Bμ) (hw : ‖w‖ ≤ Bw)
    (hd : ‖4 * (μ : ℂ) * w‖ ≤ 1 / 8) (hd' : ‖4 * (μ' : ℂ) * w'‖ ≤ 1 / 8) :
    ‖nCor (μ' : ℂ) w' - nCor (μ : ℂ) w‖ ≤ 4 * (Bw * |μ' - μ| + Bμ * ‖w' - w‖) := by
  rw [nCor_dom hd, nCor_dom hd']
  have e : 4 * (μ' : ℂ) * w' - 4 * (μ : ℂ) * w = 4 * (((μ' - μ : ℝ) : ℂ) * w + (μ' : ℂ) * (w' - w)) := by
    push_cast; ring
  rw [e, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by norm_num)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left hw (abs_nonneg (μ' - μ))
  have := mul_le_mul_of_nonneg_right hμ' (norm_nonneg (w' - w))
  linarith

end Err

section Step

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e ℓΔ : ℝ}

/-- The quantity `Θ_k` for two histories. -/
def thetaH (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (k : ℕ) (t t' : Hist.Seq (Xs R))
    (cw cxx e ℓΔ : ℝ) : ℝ :=
  thetaIn e (aIn R k t t') (bWIn R cw k t t') (bDIn R cxx k t t') (cIn R cxx k t t') ℓΔ R.ℓ

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

/-- The constant of the `ev` part of `Θ`. -/
def cTh (ℓ cw cxx : ℝ) : ℝ := 28 * cw + 28 * (1 + Real.exp 1) * cxx + 128 * Real.exp 2 * cxx * cM * ℓ ^ 2

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

end Step2
