import Spin2.Cont.ContWire3
import Spin2.Pair.PairInitSizes
import PtCorr2.Restart.RestartPairB
import Spin2.Cont.ContDiff4c

set_option autoImplicit false

/-!
# B3, T6 (a) wiring: the `b`-sector sizes of a restarted history with the reference `b`-part

For a datum `δ` at scale `m_r` whose `σ_b` projection is the reference one
(`prjSt false δ = prjSt false (obsHist R' (ptsX x) (obsInit .two (zV0 b) (ptsX x)) m_r t)`), every
`σ_b` component of the restarted history at `m_r ≤ j ≤ N_h` is the reference one (`rpb_b_eq`),
i.e. the `σ_a` component of the mirrored one-point history at `ptsS x` (`mirror_b_eq`).

**`MasterFacts.cw2_bSizes`** (along `D_ε`): with `β^S_j = bt2 R (ptsS x) (zV0 b) m b μ₀ j`,
`T(V_j(q)_b) ≤ 2s_j²|β^S_j|`, `T(𝒲_j(q)_b) ≤ c_W(cǧ_j)·2s_j²|β^S_j|`,
`A^{(|𝓑(X)|−4)_+}T(K_j(X)_b) ≤ 16c_WB(cǧ_j)²s_j²|β^S_j|` (`MasterFacts.cw2_relBaseD`).

**`MasterFacts.cw2_ratioD`**: `cd4_ratio` along `D_ε` (`relGD`, `gincD`).
**`MasterFacts.cw2_pMS_ratio`**: `2s_j²|β^S_j| ≤ e^{2c_δ(4/β_L)ε}(81/56)^{N_h−j}·pM(ptsS x)_{N_h}`
(`|1 − 𝔫| ≥ 7/8` from `loopD`, `s_j ≤ (15/14)^n s_{j+n}`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 1000000 in
/-- **The `b`-sector sizes of the restarted history** (reference `b`-part). -/
theorem cw2_bSizes (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc)
    (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ)
    (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) {mr : ℕ} (δ : ObsSt .two L N)
    (hb : prjSt false δ = prjSt false (obsHist (R.withMsq m) (ptsX x)
      (obsInit .two (zV0 b) (ptsX x)) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    {j : ℕ} (hmj : mr ≤ j) (hjN : j ≤ Nh) :
    (∀ q ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (((obsHistFrom (R.withMsq m) (ptsX x) mr δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖)) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (((obsHistFrom (R.withMsq m) (ptsX x) mr δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) *
          (2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖))) ∧
    (∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (((obsHistFrom (R.withMsq m) (ptsX x) mr δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (16 * M.core.cWo * M.core.Bk *
          (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ 2 *
          (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖))) := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  obtain ⟨hV1, hW1, hK1, -⟩ := rpb_b_eq (R.withMsq m) (ptsX x) (obsInit .two (zV0 b) (ptsX x)) δ
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hb hmj
  obtain ⟨hV2, hW2, hK2⟩ := prjSt_eq_cmp (mirror_b_eq (R.withMsq m)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) b x j)
  have hNh0 : 0 < Nh := by omega
  have hN : 2 ≤ N := by omega
  obtain ⟨-, hA, hW, hK⟩ := M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD (ptsS x)
    (zV0 b) rfl hmu hNh0 j hjN
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hs := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun X hX => ?_⟩
  · rw [hV1 q, hV2 q, obsHist2_pure (R.withMsq m) (ptsS x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (zV0 b) rfl j q]
    refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : ‖LocObs.mass2 (((obsHist (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x)) j
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).a‖ ≤
        Obs2.shA2 (Obs2.histVO2 (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) j := by
      rw [← histVO2_a (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j q]
      exact Finset.single_le_sum (f := fun c => ‖LocObs.mass2
        (Obs2.histVO2 (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j c : SA .two (Lam 2 L N)).a‖)
        (fun _ _ => norm_nonneg _) hq
    have := mul_le_mul_of_nonneg_right (h1.trans hA)
      (sq_nonneg (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    have e : 2 * ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ *
        histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 =
        2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ := by ring
    linarith
  · rw [hW1 q, hW2 q]
    have h := hW q hq
    rw [Obs2.oTo_wA] at h
    exact h
  · rw [hK1 X, hK2 X]
    have h := hK X hX
    rw [Obs2.oTo_wA] at h
    exact h

/-- `s_j ≤ (15/14)s_{j+1}` (inline in `obs_hist_restartT`). -/
theorem cw2_histS_le_succ {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Hist.Seq (Xs R)) (j : ℕ) :
    histS R j t ≤ 15 / 14 * histS R (j + 1) t := by
  have e : histS R (j + 1) t = histS R j t * fscale (1 + zetaH R j t) := by
    unfold histS
    rw [rawHist_succ_Z, fscale_mul]; ring
  have hz : ‖zetaH R j t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
  have h1 := fscale_one_add_ge hz
  have h2 := histS_pos' R hρ0 hρ t j
  rw [e]; nlinarith

theorem cw2_histS_le_pow {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Hist.Seq (Xs R)) (j : ℕ) :
    ∀ n, histS R j t ≤ (15 / 14) ^ n * histS R (j + n) t
  | 0 => by simp
  | n + 1 => by
    have h := cw2_histS_le_pow R hρ0 hρ t j n
    have h' := cw2_histS_le_succ R hρ0 hρ t (j + n)
    rw [pow_succ, ← add_assoc]
    nlinarith [pow_pos (show (0 : ℝ) < 15 / 14 by norm_num) n]

set_option maxHeartbeats 4000000 in
/-- `MasterFacts.cd4_ratio` along `D_ε` (`M.relGD`, `M.gincD`). -/
theorem cw2_ratioD (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P' : ObsPts 2 L N) (V : OCoup .two) (hmu : OCoup2.mua V ≠ 0) {k j : ℕ} (hkj : k + j ≤ Nh) :
    Real.exp (-(2 * (M.core.cRel * (4 / betaL L) * M.core.ε))) * ‖bt2 R P' V m b μ₀ k‖ *
        ∏ i ∈ range j, ‖1 - nn2 R P' V m b μ₀ (k + i)‖ ≤ ‖bt2 R P' V m b μ₀ (k + j)‖ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hrel := M.relGD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P' V hmu
  have hginc := M.gincD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD
  obtain ⟨hcR, -⟩ := M.core.consts_nonneg
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hβp : 0 < betaL L := by linarith
  have hlow := r3_beta_lower (fun i => bt2 R P' V m b μ₀ i) (fun i => nn2 R P' V m b μ₀ i)
    (fun i => err2 R P' V m b μ₀ i) (fun i => M.core.cRel * (t i).1 ^ 2) k Nh
    (fun i hi => bt2_flow R P' V (show Nh < N by omega) m b μ₀ hi)
    (fun i hi => (hrel i hi).1) (fun i _ => mul_nonneg hcR (sq_nonneg _))
    (fun i hi => by have := (hrel i hi).2; linarith) j hkj
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 ?_) (norm_nonneg _)) (prod_nonneg fun _ _ => norm_nonneg _)) hlow
  have hs := r3_gsq_sum (fun i => (t i).1) (β := betaL L) k (n := Nh) hginc j hkj
  have hgk : 0 < (t k).1 := (hD k (by omega)).1
  have hgε : (t (k + j)).1 ≤ M.core.ε := (hD (k + j) hkj).2.1
  rw [← mul_sum]
  have hS : ∑ i ∈ range j, (t (k + i)).1 ^ 2 ≤ 4 / betaL L * M.core.ε := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hβp]
    have : betaL L / 4 * ∑ i ∈ range j, (t (k + i)).1 ^ 2 ≤ M.core.ε := by
      linarith
    linarith
  have := mul_le_mul_of_nonneg_left hS hcR
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The reference `b`-weight at scale `j` against the one at `N_h`**:
`2s_j²|β^S_j| ≤ e^{2c_δ(4/β_L)ε}(81/56)^{N_h−j}·pM(ptsS x)_{N_h}`. -/
theorem cw2_pMS_ratio (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) {j : ℕ} (hj : j ≤ Nh) :
    2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ ≤
      Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) * (81 / 56) ^ (Nh - j) *
        pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  set n := Nh - j with hnd
  have hjn : j + n = Nh := by omega
  have hr := M.cw2_ratioD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD (ptsS x) (zV0 b) hmu
    (k := j) (j := n) (by omega)
  rw [hjn] at hr
  obtain ⟨-, -, hl⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD (ptsS x) (zV0 b)
  obtain ⟨q, -, -, hl⟩ := hl
  have hprod : (7 / 8 : ℝ) ^ n ≤ ∏ i ∈ range n, ‖1 - nn2 R (ptsS x) (zV0 b) m b μ₀ (j + i)‖ := by
    have e : (7 / 8 : ℝ) ^ n = ∏ _i ∈ range n, (7 / 8 : ℝ) := by rw [prod_const, card_range]
    rw [e]
    refine prod_le_prod (fun _ _ => by norm_num) fun i hi => ?_
    have h1 := (hl (j + i) (by have := mem_range.1 hi; omega)).1
    have h2 := norm_sub_norm_le (1 : ℂ) (nn2 R (ptsS x) (zV0 b) m b μ₀ (j + i))
    rw [norm_one] at h2
    linarith
  set c := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε) with hcd
  set βj := ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ with hβjd
  set βN := ‖bt2 R (ptsS x) (zV0 b) m b μ₀ Nh‖ with hβNd
  have hβj0 : 0 ≤ βj := norm_nonneg _
  have hP0 : 0 ≤ ∏ i ∈ range n, ‖1 - nn2 R (ptsS x) (zV0 b) m b μ₀ (j + i)‖ :=
    prod_nonneg fun _ _ => norm_nonneg _
  have hβ : βj ≤ Real.exp c * (8 / 7) ^ n * βN := by
    have h1 : Real.exp (-c) * βj * (7 / 8) ^ n ≤ βN :=
      le_trans (mul_le_mul_of_nonneg_left hprod (by positivity)) hr
    have h2 : βj = Real.exp c * (8 / 7) ^ n * (Real.exp (-c) * βj * (7 / 8) ^ n) := by
      have e1 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
      have e2 : ((8 : ℝ) / 7) ^ n * (7 / 8) ^ n = 1 := by rw [← mul_pow]; norm_num
      calc βj = (Real.exp c * Real.exp (-c)) * (((8 : ℝ) / 7) ^ n * (7 / 8) ^ n) * βj := by
            rw [e1, e2]; ring
        _ = _ := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hs := cw2_histS_le_pow (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j n
  rw [hjn] at hs
  have hsj := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j
  have hsq : histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 ≤
      ((15 / 14 : ℝ) ^ n) ^ 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hsj.le hs 2
  have hpM : pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh =
      2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * βN := rfl
  rw [hpM]
  have hθ : ((15 / 14 : ℝ) ^ n) ^ 2 * (8 / 7) ^ n ≤ (81 / 56) ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hβN0 : 0 ≤ βN := norm_nonneg _
  have hSN : 0 ≤ histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 := sq_nonneg _
  calc 2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * βj
      ≤ 2 * (((15 / 14 : ℝ) ^ n) ^ 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2) *
          (Real.exp c * (8 / 7) ^ n * βN) := by
        apply mul_le_mul (by linarith) hβ hβj0 (by positivity)
    _ = Real.exp c * (((15 / 14 : ℝ) ^ n) ^ 2 * (8 / 7) ^ n) *
          (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * βN) := by ring
    _ ≤ Real.exp c * (81 / 56) ^ n * (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * βN) := by
        gcongr

end MasterFacts

end

end Spin2
