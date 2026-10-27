import Spin2.Cont.ContEqC1
import PtCorr2.Cont.ContFx1

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`), step 1: the `b`-weight ratio is bounded uniformly

The reference `b`-weight ratio of `cw2_pMS_ratio` is the crude per-step product
`Θ_b(j) = e^{c}(81/56)^{N_h−j}`. Using the two-sided bounds `|log|Z_{n+1}| + (1/3)log(ǧ_n/b)| ≤ K_Zǧ_n`
(`spinD`) and (H_λ) (`hLam_pairD`), together with the monotonicity of `θ_k = (ǧ_k/b)^{1/3}`
(`eqc_thJ_mono`), the ratio is bounded by a constant of the master construction:

* **`MasterFacts.fx_pMS_ratioU`**: `2s_j²|β^S_j| ≤ Θ*·pM(ptsS y)_{N_h}` for `1 ≤ j ≤ N_h`, where
  `Θ* = (16/7)e^{2K_Z}e^{c}(1 + 3K_p)` (`fxTh`), provided `K_p(ǧ_{N_h−1} + a_{N_h−1}) ≤ 1/2`.

The smallness condition involves `ǧ_{N_h−1} ≤ 4/β_R` and `a_{N_h−1} = L^{−2(N_h−1)} + mL^{2N_h}`
only, so it is independent of `N_h − j` (no `r`-dependence).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- The uniform `b`-weight ratio `Θ* = (16/7)e^{2K_Z}e^{c}(1 + 3K_p)`. -/
def fxTh : ℝ :=
  16 / 7 * Real.exp (2 * M.core.KZ) * Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) *
    (1 + 3 * M.Kp)

theorem one_le_fxTh (hε : 0 ≤ M.core.ε) : 1 ≤ M.fxTh := by
  unfold fxTh
  have h1 : 1 ≤ Real.exp (2 * M.core.KZ) := Real.one_le_exp (by have := M.KZ_nonneg; linarith)
  have hc : 0 ≤ 2 * (M.core.cRel * (4 / betaL L) * M.core.ε) := by
    obtain ⟨hcR, -⟩ := M.core.consts_nonneg
    have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
    have : 0 ≤ 4 / betaL L := div_nonneg (by norm_num) (by linarith)
    positivity
  have h2 : 1 ≤ Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) := Real.one_le_exp hc
  have h3 : 1 ≤ 1 + 3 * M.Kp := by have := M.Kp_nonneg; linarith
  have h12 : 1 ≤ Real.exp (2 * M.core.KZ) * Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) :=
    one_le_mul_of_one_le_of_one_le h1 h2
  have h123 := one_le_mul_of_one_le_of_one_le h12 h3
  nlinarith

/-- `s_k² = ℓ²/|Z_k|`. -/
theorem fx_histS_sq {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R)) (k : ℕ) :
    PtCorr2.histS R k t ^ 2 = R.ℓ ^ 2 * (zH R t k)⁻¹ := by
  unfold PtCorr2.histS; rw [mul_pow, Step2.fscale_sq]; ring

set_option maxHeartbeats 4000000 in
/-- **The `b`-weight ratio, uniformly in `N_h − j`**: `2s_j²|β^S_j| ≤ Θ*·pM(ptsS y)_{N_h}`. -/
theorem fx_pMS_ratioU {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (y : Lam 2 L N) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ Nh)
    (hsm : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 + zA L m (Nh - 1)) ≤ 1 / 2) :
    2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsS y) (zV0 b) m b μ₀ j‖ ≤
      M.fxTh * pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hε : 0 ≤ M.core.ε := ((hD 0 (Nat.zero_le _)).1.le).trans (hD 0 (Nat.zero_le _)).2.1
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hpM : pM (R.withMsq m) (ptsS y) (zV0 b) t Nh =
      2 * histS (R.withMsq m) Nh t ^ 2 * ‖bt2 R (ptsS y) (zV0 b) m b μ₀ Nh‖ := rfl
  have hpM0 : 0 ≤ pM (R.withMsq m) (ptsS y) (zV0 b) t Nh := by rw [hpM]; positivity
  rcases eq_or_lt_of_le hj with hjN | hjN
  · rw [hjN]
    exact le_mul_of_one_le_left hpM0 (M.one_le_fxTh hε)
  -- `1 ≤ j < N_h`
  set n := Nh - 1 with hnd
  have hn1 : 1 ≤ n := by omega
  have hnN : n + 1 = Nh := by omega
  have hKp := M.Kp_nonneg
  set θ := thJ R m b μ₀ n with hθd
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg (div_pos (hD n (by omega)).1 hb).le _
  set c := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε) with hcd
  set KZ := M.core.KZ with hKZd
  have hKZ : 0 ≤ KZ := M.KZ_nonneg
  -- upper bound at `j`
  have hzj : (zH (R.withMsq m) t j)⁻¹ ≤ Real.exp KZ * θ := by
    have h := M.eqc_zinv_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (n := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    exact M.eqc_thJ_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (by omega) (by omega)
  have hβj : ‖bt2 R (ptsS y) (zV0 b) m b μ₀ j‖ ≤ (1 + 3 * M.Kp) * b * θ := by
    refine (M.eqc_bt_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsS y) hj1 hjN).trans ?_
    exact mul_le_mul_of_nonneg_left
      (M.eqc_thJ_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (by omega) (by omega)) (by positivity)
  -- lower bound of `1/|Z_{N_h}|`
  have hzN : Real.exp (-KZ) * θ ≤ (zH (R.withMsq m) t Nh)⁻¹ := by
    obtain ⟨hZ0, hZl⟩ :=
      (M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ₀ hD n (by omega)
    have hg := (hD n (by omega)).1
    have hg1 : (t n).1 ≤ 1 := (hD n (by omega)).2.1.trans M.eps_le
    have hZp : 0 < ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ := norm_pos_iff.2 hZ0
    have h2 : Real.log ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ + 1 / 3 * Real.log ((t n).1 / b) ≤
        KZ * (t n).1 := (abs_le.1 hZl).2
    have e1 : zH (R.withMsq m) t Nh = ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ := by
      rw [hnN]
    rw [e1]
    have hθe : θ = Real.exp (1 / 3 * Real.log ((t n).1 / b)) := by
      rw [hθd]; unfold thJ
      rw [Real.rpow_def_of_pos (div_pos hg hb), mul_comm]
    have hZe : ‖(rawHist (R.withMsq m) (n + 1) t).Z‖⁻¹ =
        Real.exp (-Real.log ‖(rawHist (R.withMsq m) (n + 1) t).Z‖) := by
      rw [Real.exp_neg, Real.exp_log hZp]
    rw [hθe, hZe, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : KZ * (t n).1 ≤ KZ := by nlinarith
    linarith
  -- lower bound of `|β_{N_h−1}|`
  have hβn : 1 / 2 * (b * θ) ≤ ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n‖ := by
    have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsS y) n (by omega)
    have hlh : lamHat2 R (ptsS y) (zV b) m b μ₀ n = bt2 R (ptsS y) (zV b) m b μ₀ n / b := by
      unfold lamHat2; rw [bt2_zV_zero]
    rw [hlh, cdd_bt2_zV0 R (ptsS y) m b μ₀ hn1] at hl
    have hl0 : ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n / b - ((θ : ℝ) : ℂ)‖ ≤
        M.Kp * θ * ((t n).1 + zA L m n) := hl
    have h2 := norm_sub_norm_le ((θ : ℝ) : ℂ) (bt2 R (ptsS y) (zV0 b) m b μ₀ n / b)
    rw [norm_sub_rev] at h2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0] at h2
    have hl' : ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n / b - ((θ : ℝ) : ℂ)‖ ≤ θ / 2 := by
      refine hl0.trans ?_
      have : M.Kp * θ * ((t n).1 + zA L m n) = θ * (M.Kp * ((t n).1 + zA L m n)) := by ring
      rw [this]
      nlinarith
    have hdiv : ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n / b‖ = ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n‖ / b := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    have h3 : θ / 2 ≤ ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n‖ / b := by rw [← hdiv]; linarith
    rw [le_div_iff₀ hb] at h3
    linarith
  -- one step `N_h − 1 → N_h`
  have hβN : Real.exp (-c) * (7 / 8) * ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n‖ ≤
      ‖bt2 R (ptsS y) (zV0 b) m b μ₀ Nh‖ := by
    have hmu := zV0_mua_ne hb
    have hr := M.cw2_ratioD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS y) (zV0 b) hmu
      (k := n) (j := 1) (by omega)
    rw [hnN, Finset.prod_range_one, add_zero] at hr
    obtain ⟨-, -, hl⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS y) (zV0 b)
    obtain ⟨q, -, -, hl⟩ := hl
    have h1 := (hl n (by omega)).1
    have h2 := norm_sub_norm_le (1 : ℂ) (nn2 R (ptsS y) (zV0 b) m b μ₀ n)
    rw [norm_one] at h2
    have h78 : 7 / 8 ≤ ‖1 - nn2 R (ptsS y) (zV0 b) m b μ₀ n‖ := by linarith
    have hβ0 := norm_nonneg (bt2 R (ptsS y) (zV0 b) m b μ₀ n)
    have := mul_le_mul_of_nonneg_left h78
      (mul_nonneg (Real.exp_pos (-c)).le hβ0)
    nlinarith
  -- assemble
  have hsj := fx_histS_sq (R.withMsq m) t j
  have hsN := fx_histS_sq (R.withMsq m) t Nh
  have eℓ : (R.withMsq m).ℓ ^ 2 = M.core.ℓ ^ 2 := by
    rw [show (R.withMsq m).ℓ = R.ℓ from rfl, hRℓ]
  rw [eℓ] at hsj hsN
  set ℓ2 := M.core.ℓ ^ 2 with hℓ2d
  have hℓ2 : 0 ≤ ℓ2 := by positivity
  set βj := ‖bt2 R (ptsS y) (zV0 b) m b μ₀ j‖
  set βn := ‖bt2 R (ptsS y) (zV0 b) m b μ₀ n‖
  set βN := ‖bt2 R (ptsS y) (zV0 b) m b μ₀ Nh‖
  set zj := (zH (R.withMsq m) t j)⁻¹
  set zN := (zH (R.withMsq m) t Nh)⁻¹
  have hzj0 : 0 ≤ zj := inv_nonneg.2 (norm_nonneg _)
  have hβj0 : 0 ≤ βj := norm_nonneg _
  have heK : Real.exp KZ * Real.exp (-KZ) = 1 := by rw [← Real.exp_add]; simp
  have hec : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  have heKK : Real.exp (2 * KZ) = Real.exp KZ * Real.exp KZ := by rw [← Real.exp_add]; ring_nf
  -- `zj·βj ≤ e^{K_Z}(1+3K_p)bθ²` and `zN·βN ≥ e^{-K_Z}e^{-c}(7/16)bθ²`
  have hup : zj * βj ≤ Real.exp KZ * θ * ((1 + 3 * M.Kp) * b * θ) :=
    mul_le_mul hzj hβj hβj0 (by positivity)
  have hlo : Real.exp (-KZ) * θ * (Real.exp (-c) * (7 / 8) * (1 / 2 * (b * θ))) ≤ zN * βN := by
    have h1 : Real.exp (-c) * (7 / 8) * (1 / 2 * (b * θ)) ≤ βN :=
      le_trans (mul_le_mul_of_nonneg_left hβn (by positivity)) hβN
    exact mul_le_mul hzN h1 (by positivity) (inv_nonneg.2 (norm_nonneg _))
  have key : zj * βj ≤ M.fxTh * (zN * βN) := by
    refine hup.trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hlo
      (by have := M.one_le_fxTh hε; linarith)))
    unfold fxTh
    rw [← hcd, ← hKZd, heKK]
    have e1 : Real.exp KZ * Real.exp KZ * Real.exp c *
        (Real.exp (-KZ) * θ * (Real.exp (-c) * (7 / 8) * (1 / 2 * (b * θ)))) =
        (Real.exp KZ * Real.exp (-KZ)) * (Real.exp c * Real.exp (-c)) * Real.exp KZ *
          (7 / 16 * (b * θ * θ)) := by ring
    calc Real.exp KZ * θ * ((1 + 3 * M.Kp) * b * θ)
        = 16 / 7 * (1 + 3 * M.Kp) * (Real.exp KZ * (7 / 16 * (b * θ * θ))) := by ring
      _ = _ := by
        rw [Real.exp_neg, Real.exp_neg]
        field_simp
        ring
  have e1 : 2 * histS (R.withMsq m) j t ^ 2 * βj = 2 * (ℓ2 * zj) * βj := by rw [hsj]
  have e2 : pM (R.withMsq m) (ptsS y) (zV0 b) t Nh = 2 * (ℓ2 * zN) * βN := by rw [hpM, hsN]
  show 2 * histS (R.withMsq m) j t ^ 2 * βj ≤ M.fxTh * pM (R.withMsq m) (ptsS y) (zV0 b) t Nh
  rw [e1, e2]
  calc 2 * (ℓ2 * zj) * βj = 2 * ℓ2 * (zj * βj) := by ring
    _ ≤ 2 * ℓ2 * (M.fxTh * (zN * βN)) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = M.fxTh * (2 * (ℓ2 * zN) * βN) := by ring

end MasterFacts

end

end Spin2
