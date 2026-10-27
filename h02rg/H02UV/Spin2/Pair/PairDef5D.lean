import Spin2.Pair.PairDef5c
import Spin2.Pair.PairDef5d
import Spin2.Pair.PairLoop6D

/-!
# The windowed (`D_ε`) forms of the `PairDefSizesR3P` discharge

Copies (suffix `D`) of `MasterCore.vhistSL`, `pairKSWSizes_MFat`, `pairDefSeed_MF`,
`pairDefSizesR3P_of_NS_at`, `pairDefSizesR3P_of_NS_MFC` and `pairVB_top_MF` with `Admissible … b μ₀`
replaced by the domain condition `∀ j ≤ N_h, InD3 … (t_j)` (`inDh_rg_of_D`, the `D` forms of
`MasterFacts`, `MasterCore.AbwHistPD6`/`abwHistCD6` and the `D6` copies of `Spin2/Pair/PairLoop6D`).
Same bodies otherwise.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

set_option maxHeartbeats 4000000 in
/-- **The `S` sizes along the history up to `N_h`.** -/
theorem MasterCore.vhistSLD {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
    (P : Obs2.ObsPts 2 L N) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀) (i : ℕ) (hji : j₀ ≤ i) (hi : i ≤ Nh)
    (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
      oTo (wM Ma Mb) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤
        ENNReal.ofReal mV)
    (hWo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
      oTo (wM Ma Mb) i (histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) P j₀ o₀ i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
        ENNReal.ofReal mW) :
    let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    ∀ b' ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
          (SXO i (histCovO (R.withMsq m) t i) (hVR (R.withMsq m) P j₀ o₀ t i)
            (hWR (R.withMsq m) P j₀ o₀ t i) (Step2.Bp (L := L) (N := N) i b') :
            SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * ((L : ℝ) ^ 2 * sO 2 L (D.c * (t i).1) mV mW)) ∧
      (¬ (Step2.Bp (L := L) (N := N) i b' ∩ P.pts).Nonempty →
        (SXO i (histCovO (R.withMsq m) t i) (hVR (R.withMsq m) P j₀ o₀ t i)
          (hWR (R.withMsq m) P j₀ o₀ t i) (Step2.Bp (L := L) (N := N) i b') :
          SA .two (Lam 2 L N)).ab = 0) := by
  rcases Nat.lt_or_ge i Nh with hlt | hge
  · exact D.vhistSD6 N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P hMa hMb o₀ h0 hl0 hs0 ha0 i
      hji hlt mV mW hmV hmW hVo hWo
  obtain rfl : i = Nh := by omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN i hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN i hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hcR : cR R' ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have ht := inDh_rg_of_D R' F1 hadm i le_rfl
  have hmsq : R'.msq ∈ mRange L N := hm
  have hmN : |R'.msq| * ((L : ℝ) ^ i) ^ 2 ≤ 1 := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by have := D.hL49; omega)
    have h1 : R'.msq * ((L : ℝ) ^ (i + 1)) ^ 2 ≤ 1 := by
      have := msq_horizon (L := (L : ℝ)) hL1 hmsq.2 (Nh := i) (k := 0) (by omega)
      simpa using this
    have hm0 : 0 ≤ R'.msq := hmsq.1.le
    rw [abs_of_nonneg hm0]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm0) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) 2
  have H' := sxo_hist_ab_leL R' D.hSX hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hVL hmN
    P hMa hMb o₀ h0 hl0 hs0 ha0 _ hji ht mV mW hmV hmW hVo hWo
  simp only [hcR] at H'
  exact H'


set_option maxHeartbeats 4000000 in
/-- **The history `K`, `S` (up to `N_h`) and `𝒲` sizes of the reduced states under `PairVB`**
(copy of `pairKSSizes_MFat`, at the constants of `hAH : AbwHistP C₁k C₁w`). -/
theorem pairKSWSizes_MFatD {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w : ℝ} (hC₁k : 0 ≤ C₁k)
    (hC₁w : 0 ≤ C₁w) (hAH : M.core.AbwHistPD6 C₁k C₁w) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (cu mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ n, n ≤ Nh + 1 → PairVB R m b μ₀ lam x mbar n →
    ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < n → i ≤ Nh →
      let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
      let C := histCovO (R.withMsq m) t
      let V := hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      let W := hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      let K := hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ dxStd x) t
      (∀ Y, IsSmall i Y → Tj 2 (L : ℝ) i (histS (R.withMsq m) i t) (K i Y : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i)) ∧
      (∀ b' ∈ blockIdx (L := L) (N := N) i,
        Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
            (SXO i (C i) (V i) (W i) (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (kszS R M C₁w mbar m b μ₀ lam x i) ∧
        (¬ (Step2.Bp (L := L) (N := N) i b' ∩ (ptsX x).pts).Nonempty →
          (SXO i (C i) (V i) (W i) (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab = 0)) ∧
      (∀ B, Tj 2 (L : ℝ) i (histS (R.withMsq m) i t) (W i B : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (kszW R M C₁w mbar m b μ₀ lam x i)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj
    n hn hVB i hi1 hin hiN
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hb : 0 < b := by
    have := (hadm 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := by
    obtain ⟨q, -, -, hl⟩ :=
      (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
    intro k hk
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1)
      (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1 k hk
    exact ⟨a1, a2⟩
  have hρ0 : 0 ≤ (R.withMsq m).ρ := (hV 0 (by omega) |>.toValidCore).2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := ((hRI 0 (by omega)).1).2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := fun k =>
    histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  have hvwA : ∀ k ≤ Nh + 1, vwA R m b μ₀ x k = 2 * histS (R.withMsq m) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ‖hBeta R m b μ₀ x k‖ := by
    intro k hk
    have hne : hBeta R m b μ₀ x k ≠ 0 := by
      rcases Nat.lt_or_ge k (Nh + 1) with h | h
      · exact (hβne k (by omega)).1
      · rw [show k = Nh + 1 by omega]
        exact (hβne Nh le_rfl).2
    unfold vwA; rw [if_neg hne]
  have hMa : ∀ k, 0 < vwA R m b μ₀ x k := fun k => by
    unfold vwA
    split_ifs with h
    · norm_num
    · have := hs k; have := norm_pos_iff.2 h; positivity
  -- the seed
  obtain ⟨hpa, hpb, hK⟩ := pairSeed_hK0D M.pairInitWD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hadm x h1 hj
  have hU' := hU x hx h1 hj
  have hg0 : 0 ≤ ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 := (hadm j hj).1.le
  have hwB0 : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) hg0
  have hwB : 0 < vwB R m b μ₀ lam x := by
    rcases hwB0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hU'; linarith
  have hcu : 0 < cu := by
    by_contra hc
    push Not at hc
    have : cu * vwB R m b μ₀ lam x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hwB0
    linarith
  have hpaE : pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j =
      vwA R m b μ₀ x j := by
    rw [hvwA j (by omega), hBeta_eq_zV0 R m b μ₀ x h1]; rfl
  set k₀ := cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) with hk₀d
  have hιA : 0 ≤ (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) := by
    have := M.ιW_ge; have := M.core.hA2; positivity
  have hk₀ : 0 ≤ k₀ := mul_nonneg hcu.le hιA
  have hK0 : ∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      oTo (wM (vwA R m b μ₀ x j) (vwB R m b μ₀ lam x)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X) ≤ ENNReal.ofReal k₀ := by
    intro X hX
    have hab : (oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X ∈
        (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
      (PtCorr2.obsAbInv_redSt _ _ _ _ _ _ _ _ _ _).K X hX
    rw [oTo_wM_rescale (hMa j) hwB hpa hpb j _ hab, hpaE, mul_left_comm]
    have hr : vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) ≤ cu := by
      rw [mul_div_mul_left _ _ (hMa j).ne', div_le_iff₀ hwB]; linarith
    calc ENNReal.ofReal (vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
          (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) *
          (ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
            oTo (wM (vwA R m b μ₀ x j) (pM (R.withMsq m) (ptsS x) (zV0 b)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)) j
              (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X))
        ≤ ENNReal.ofReal cu * ENNReal.ofReal ((2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) := by
          gcongr
          rw [← hpaE]; exact hK X hX
      _ = ENNReal.ofReal k₀ := by rw [← ENNReal.ofReal_mul hcu.le]
  -- the initial state
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j fun i hi => (hRI i (by omega)))
  -- the doubling of the weights
  have hdbl : ∀ k, j ≤ k → k < n → vwA R m b μ₀ x k ≤ 2 * vwA R m b μ₀ x (k + 1) := by
    intro k hk hkn
    rw [hvwA k (by omega), hvwA (k + 1) (by omega)]
    have h1' := histS_sq_ratio (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
    have h2' := hβr k (by omega)
    have h3 := sq_nonneg (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    have h4 := norm_nonneg (hBeta R m b μ₀ x (k + 1))
    have h5 : histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖hBeta R m b μ₀ x k‖ ≤
        (6 / 5 * histS (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2) *
          (64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖) :=
      mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg (histS (R.withMsq m) (k + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) h4]
  -- the `𝒲` chain up to `i`
  obtain ⟨hcR, hAH'⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hm' : ∀ k, j ≤ k → k < i → vwA R m b μ₀ x k * (fun _ : ℕ => vwB R m b μ₀ lam x) k /
      (vwA R m b μ₀ x j * (fun _ : ℕ => vwB R m b μ₀ lam x) j) * (fun _ : ℕ => mbar) k ≤
      2 * (vwA R m b μ₀ x (k + 1) * (fun _ : ℕ => vwB R m b μ₀ lam x) (k + 1) /
        (vwA R m b μ₀ x j * (fun _ : ℕ => vwB R m b μ₀ lam x) j) * (fun _ : ℕ => mbar) (k + 1)) := by
    intro k hk hki
    have h := hdbl k hk (by omega)
    have hpos : 0 ≤ vwB R m b μ₀ lam x * mbar / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) := by
      have := hMa j; positivity
    have e1 : vwA R m b μ₀ x k * vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar =
        vwA R m b μ₀ x k * (vwB R m b μ₀ lam x * mbar / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) := by
      ring
    have e2 : 2 * (vwA R m b μ₀ x (k + 1) * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar) =
        2 * vwA R m b μ₀ x (k + 1) * (vwB R m b μ₀ lam x * mbar /
          (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) := by ring
    show vwA R m b μ₀ x k * vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar ≤
      2 * (vwA R m b μ₀ x (k + 1) * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar)
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h hpos
  have hVo : ∀ k, j ≤ k → k < i → ∀ b' ∈ blockIdx (L := L) (N := N) k,
      oTo (wM (vwA R m b μ₀ x k) ((fun _ : ℕ => vwB R m b μ₀ lam x) k)) k
        (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) k
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤ ENNReal.ofReal ((fun _ : ℕ => mbar) k) :=
    fun k hk hki b' hb' => hVB k hk (by omega) b' hb'
  have hW0 : ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (vwA R m b μ₀ x j) ((fun _ : ℕ => vwB R m b μ₀ lam x) j)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oRed R m b μ₀ dxStd x).W b') ≤
      ENNReal.ofReal ((4 * C₁w + 1) * (cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) * (fun _ : ℕ => mbar) j) := fun b' _ => by
    show oTo _ _ _ (0 : OE .two (Lam 2 L N)) ≤ _
    rw [oTo_zero']; exact bot_le
  have hWi := (hAH' (ptsX x) (vwA R m b μ₀ x) (fun _ => vwB R m b μ₀ lam x) hMa (fun _ => hwB) j
    (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj hanc i hiN (fun _ => mbar) (fun _ => hmbar) hm'
    hVo hW0 k₀ hk₀ hK0 (by rw [one_mul]; exact h8) i hi1 le_rfl)
  obtain ⟨-, hWi', hKi'⟩ := hWi
  have hcR' := hcR
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  refine ⟨fun Y hY => ?_, fun b' hb' => ?_, fun B => ?_⟩
  · have hKs := M.core.vhistKD6 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (hMa i) hwB
      (oRed R m b μ₀ dxStd x) hloc0 hsymj hanc i hi1 hiN _ hKi' Y hY
    refine hKs.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold kszQ kszK
    have hA : (R.withMsq m).A = M.core.A := hRA
    simp only [hA, hcR']
    have h1 := hMa i
    have h2 := hMa j
    set KK := kseqF (8 * (kθ0 L M.core.A M.core.C₀a M.core.ηa + C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) *
      (M.core.c * M.core.ε)))
      (kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT))
      (fun i => M.core.c * (t i).1)
      (fun i => (4 * C₁w + 1) * (vwA R m b μ₀ x i * vwB R m b μ₀ lam x /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) * mbar)) j
      (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) i with hKK
    have e : vwA R m b μ₀ x i * vwB R m b μ₀ lam x * (8 * (KK / (vwA R m b μ₀ x i *
        vwB R m b μ₀ lam x / (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)))) =
        vwA R m b μ₀ x j * vwB R m b μ₀ lam x * (8 * KK) := by
      field_simp
    rw [e]
    have hjB : 0 ≤ vwA R m b μ₀ x j * vwB R m b μ₀ lam x := mul_nonneg h2.le hwB.le
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_left KK 0]) hjB
  · have hWo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
        oTo (wM (vwA R m b μ₀ x i) (vwB R m b μ₀ lam x)) i (histS (R.withMsq m) i t)
          ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) i t).W b') ≤
        ENNReal.ofReal ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar) := fun b' hb' => by
      have h := hWi' b' hb'
      simp only [hcR'] at h
      exact h
    have hr0 : 0 ≤ M.core.c * (t i).1 := by
      have h1 := (hadm i hiN).1.le
      have h2 : 0 ≤ M.core.c := by
        rw [← hcR']; unfold cR cV cW cZ
        obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
        have := H.hcmu; have := H.hC₂; positivity
      exact mul_nonneg h2 h1
    obtain ⟨hS1, hS2⟩ := M.core.vhistSLD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
      (hMa i) hwB (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj hanc i hi1 hiN mbar _ hmbar.le
      (by have := hC₁w; positivity) (fun b' hb' => hVB i hi1 hin b' hb') hWo b' hb'
    exact ⟨hS1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)), hS2⟩
  · -- the `𝒲` sizes
    have hWo : ∀ b' ∈ blockIdx (L := L) (N := N) i,
        oTo (wM (vwA R m b μ₀ x i) (vwB R m b μ₀ lam x)) i (histS (R.withMsq m) i t)
          ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) i t).W b') ≤
        ENNReal.ofReal ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar) := fun b' hb' => by
      have h := hWi' b' hb'
      simp only [hcR'] at h
      exact h
    have hWab : (hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i B :
        SA .two (Lam 2 L N)).ab =
        ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) i t).W B :
          SA .two (Lam 2 L N)).ab := emb_add_ab _ _
    show Tj 2 (L : ℝ) i (histS (R.withMsq m) i t)
      (hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i B : SA .two (Lam 2 L N)).ab ≤ _
    rw [hWab]
    by_cases hB : B = blk i (ptsX x).a ∨ B = blk i (ptsX x).b
    · have hBI : B ∈ blockIdx (L := L) (N := N) i := by
        rcases hB with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
      refine (Tj_ab_le_of_oTo_wM' (hMa i) hwB i _ _ (hWo B hBI)).trans (le_of_eq ?_)
      unfold kszW; rfl
    · push Not at hB
      rw [ab_eq_zero_of_anch (ptsX x) ((obsAnchInv_histFrom' (R.withMsq m) (ptsX x) hanc t hi1).W B)
        hB.1 hB.2, Step.Tj_zero]
      exact zero_le


set_option maxHeartbeats 4000000 in
/-- **The `M₄` seed term of `PairDefSizesR3` for the reduced states under `MasterFacts`**: only
the `ab` sizes `κ^Q`, `κ^S` of the activity and of `S` remain. -/
theorem pairDefSeed_MFD {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)))
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    (κQ κS : ℕ → ℝ) (hκQ0 : ∀ k, 0 ≤ κQ k) (hκS0 : ∀ k, 0 ≤ κS k)
    (hκQ : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      (open Classical in ∑ c ∈ blockIdx (L := L) (N := N) k,
        ∑ X ∈ (smallSets k).filter (fun X => blockSet k c ⊆ X),
          (Tj 2 (L : ℝ) k
            (PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
              (oRed R m b μ₀ dxStd x)
              (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k X : Obs.SA .two (Lam 2 L N)).ab).toReal) ≤
        κQ k)
    (hκS : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      ∑ c ∈ blockIdx (L := L) (N := N) k,
        (Tj 2 (L : ℝ) (k + 1)
          (PtCorr2.histS (R.withMsq m) (k + 1) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs2.SXO k (Obs2.histCovO (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
              (oRed R m b μ₀ dxStd x) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
              (oRed R m b μ₀ dxStd x) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (Step2.Bp (L := L) (N := N) k c) : Obs.SA .two (Lam 2 L N)).ab).toReal ≤ κS k) :
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ‖Obs2.m4Tot (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
          (oRed R m b μ₀ dxStd x) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ *
          (2 * PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ((L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x + 1) *
              (PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
                (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        Obs2.KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 * κQ k + κS k) := by
  have hL49 : 49 ≤ L := M.core.hL49
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    with ht
  have hloc0 := (hRd x hx h1 hj).2.1
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  have hloc' : ∀ k, j ≤ k → k ≤ Nh → Obs2.OLocS (ptsX x) k
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) := fun k hk hkN =>
    PtCorr2.olocS_hR (R.withMsq m) (ptsX x) t hloc0 hk fun i' _ hi' => hRI i' (by omega)
  exact pairDefSeed_le R hNh (by omega) m b μ₀ (oRed R m b μ₀ dxStd) x hx
    (PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)) (fun B => oRed_V_ab_zero R m b μ₀ dxStd x B)
    (fun k hk hkN => PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk
      fun i _ hi => hRI i (by omega))
    hVL.2.2.2.2.1 hVL.2.2.2.2.2.1 CcutE_spec.1 CcutE_spec.2
    (fun k hk hkN X hX => ((hloc' k hk (by omega)).hK X ⟨hX.1, hX.2.1⟩).2.2.2.1)
    (fun k hk hkN c _ => ((hloc' k hk (by omega)).SX_mem one_le_two (by norm_num; omega)
      (by omega) (fun u v h => (hG k (by omega)).range (by omega) u v h) c).2.2.2.1)
    κQ κS hκQ0 hκS0 hκQ hκS


set_option maxHeartbeats 8000000 in
/-- **`PairDefSizesR3P` from the non-seed defects, at given constants** (`hAH : AbwHistP C₁k C₁w`,
`hθ` the decay of the small-set recursion; see the module docstring). -/
theorem pairDefSizesR3P_of_NS_atD {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hAH : M.core.AbwHistPD6 C₁k C₁w)
    (hθ : C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) * (M.core.c * M.core.ε) ≤ 1 / 72) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl → HLam R Nh m b μ₀ lam Kl →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ mbar : ℝ, 0 < mbar →
      8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh → PairVB R m b μ₀ lam x mbar (Nh + 1)) →
    ∀ cd : ℝ, PairDefSizesNS R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      PairDefSizesR3P R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) (cd + pd5CS M C₁k C₁w mbar) := by
  have hKSW := pairKSWSizes_MFatD M hC₁k hC₁w hAH
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl hsmall mbar hmbar
    h8 hVBtop cd hNS x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hb : 0 < b := by
    have := (hadm 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL49 : 49 ≤ L := M.core.hL49
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by omega
  obtain ⟨hVv, hVL, hG, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k t := fun k => histS_pos' (R.withMsq m) hρ0 hρ8 t k
  obtain ⟨hct, -, hcg⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨q, -, -, hlp⟩ :=
    (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  have htop := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := fun k hk => by
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hlp k hk).1) htop k hk
    exact ⟨a1, a2⟩
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hβu := hBeta_up_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    exact (hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm).1
  have hc1 : 1 ≤ M.core.c := by
    rw [← hcR]
    have hcV : 0 ≤ cV (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm := by
      unfold cV cZ; have := Hap.hcmu; positivity
    have hcW : 0 ≤ cW (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x := by
      unfold cW; have := Hap.hC₂; positivity
    unfold cR; linarith
  have hc0 : 0 ≤ M.core.c := by linarith
  have hg : ∀ i ≤ Nh, 0 < (t i).1 ∧ (t i).1 ≤ M.core.ε := fun i hi =>
    ⟨(hadm i hi).1, (hadm i hi).2.1⟩
  have hε0 : 0 ≤ M.core.ε := ((hg 0 (Nat.zero_le _)).1.trans_le (hg 0 (Nat.zero_le _)).2).le
  have hcε : M.core.c * M.core.ε ≤ 1 := M.core.hcε
  -- the sequence `r`
  have hrE : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i = M.core.c * (t i).1 := fun i hi => by
    show M.core.c * max (t i).1 0 = _; rw [max_eq_left (hg i hi).1.le]
  have hrε : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i ≤ M.core.c * M.core.ε := fun i hi => by
    rw [hrE i hi]; exact mul_le_mul_of_nonneg_left (hg i hi).2 hc0
  have hr0 : ∀ i, 0 ≤ pl6r R m b μ₀ M.core.c i := fun i => mul_nonneg hc0 (le_max_right _ _)
  have hr1 : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i ≤ 1 := fun i hi => (hrε i hi).trans hcε
  have hgr : ∀ i ≤ Nh, (t i).1 ≤ pl6r R m b μ₀ M.core.c i := fun i hi => by
    rw [hrE i hi]; have := (hg i hi).1; nlinarith
  -- the ratio facts
  have H : PL6H j Nh (L : ℝ) (sXp x) (fun i => histS (R.withMsq m) i t)
      (fun i => ‖hBeta R m b μ₀ x i‖) (pl6r R m b μ₀ M.core.c) :=
    { hL := by exact_mod_cast hL49
      hs0 := hs
      hs1 := fun i => histS_succ_le_q (R.withMsq m) hρ0 hρ8 t i
      hs2 := fun i => histS_sq_ratio (R.withMsq m) hρ0 hρ8 t i
      hβ0 := fun i => norm_nonneg _
      hβp := fun i hi => by
        rcases Nat.lt_or_ge i (Nh + 1) with h | h
        · exact norm_pos_iff.2 (hβne i (by omega)).1
        · rw [show i = Nh + 1 by omega]; exact norm_pos_iff.2 (hβne Nh le_rfl).2
      hβr := hβr
      hr0 := hr0
      hr1 := hr1
      hsx := Nat.cast_nonneg _
      hsxL := by
        have h2 := two_supNorm_lt_coal (by omega : 2 ≤ L) x
        have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm (x - 0) := by
          show supNorm ((0 : Lam 2 L N) - x) = supNorm (x - 0)
          rw [supNorm_sub_comm]
        unfold sXp; rw [hsn]
        have : ((2 * supNorm (x - 0) : ℕ) : ℝ) ≤ ((L ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast h2.le
        push_cast at this; exact this }
  -- constants
  have hK4E : 0 ≤ KM4 2 CcutE := KM4_nonneg 2
  have hcNS : 0 ≤ 2 * (cNb2 : ℝ) * (cSm2 : ℝ) := by positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (d := 2) one_le_two
  have hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa := by
    unfold kθ0
    have := M.core.hA2
    exact mul_nonneg M.core.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hθa : kθ0 L M.core.A M.core.C₀a M.core.ηa ≤ 1 / 72 := (M.core.hAa M.core.hLa).2
  set Bk := kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT) with hBkd
  have hcx : 0 ≤ cx M.core.κ M.core.cT := Hap.hcx
  have hBk : 0 ≤ Bk := by rw [hBkd]; unfold kB; positivity
  have hcWc : 0 ≤ 4 * C₁w + 1 := by linarith
  have hAs : 0 ≤ pl6As L (4 * C₁w + 1) := pl6As_nonneg hcWc
  have haQ : 0 ≤ pl6aQ Bk (4 * C₁w + 1) := by unfold pl6aQ pl6ρ; positivity
  set V := vwB R m b μ₀ lam x with hVd
  have hV : 0 ≤ V := mul_nonneg (norm_nonneg _) (hg j hj).1.le
  set cu := pairUnitC M with hcud
  have hcu : 0 ≤ cu := pairUnitC_nonneg M
  set k₀ := pl6k0 M cu with hk₀d
  have hk₀ : 0 ≤ k₀ := by
    rw [hk₀d]; unfold pl6k0
    have := M.ιW_ge; have := M.core.hA2
    exact mul_nonneg hcu (pow_nonneg (by positivity) _)
  have hvwA : ∀ i ≤ Nh, vwA R m b μ₀ x i = 2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖ :=
    fun i hi => by unfold vwA; rw [if_neg (hβne i hi).1]
  -- the small-set recursion in profile form (as in `pl6_item_le`)
  set θ := 8 * (kθ0 L M.core.A M.core.C₀a M.core.ηa + C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) *
      (M.core.c * M.core.ε)) with hθd
  have hθ0 : 0 ≤ θ := by rw [hθd]; positivity
  have hθρ : θ * pl6ρ ≤ 1 / 2 := by
    have h29 : θ ≤ 2 / 9 := by rw [hθd]; linarith
    unfold pl6ρ; nlinarith
  have hK : ∀ i, j ≤ i → i ≤ Nh →
      2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        kszK R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ *
        (128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
          (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i)) := fun i hji hi =>
    pl6_kseq H (r' := fun i => M.core.c * (t i).1)
      (m' := fun i => (4 * C₁w + 1) * (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar))
      hθ0 hθρ hBk hcWc hk₀ hmbar.le (fun i hi => (hrE i hi).symm)
      (fun i hji hi => by
        show 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * ((4 * C₁w + 1) *
          (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar)) ≤
          (4 * C₁w + 1) * (2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖) * mbar
        rw [hvwA i hi, hvwA j hj]
        rcases hV.eq_or_lt with h0 | hpos
        · rw [← h0]; simp only [mul_zero, div_zero, zero_mul]
          have := hs i; positivity
        · rw [mul_div_mul_right _ _ hpos.ne']
          apply le_of_eq
          have := (hs j).ne'
          have := (H.hβp j (by omega)).ne'
          field_simp)
      hji hi
  have hkszQ : ∀ i, j ≤ i → i ≤ Nh → kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i) := by
    intro i hji hi
    have hA : 0 < 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ := by
      have := hs j; have := H.hβp j (by omega); positivity
    have hKi := hK i hji hi
    set X := 128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
      (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) with hXd
    have hP0 := pl6P_nonneg (j := j) hk₀ i
    have hQ0 := pl6Q_nonneg (j := j) (r := pl6r R m b μ₀ M.core.c) i
    have hc₁ : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) := by unfold pl6ρ; positivity
    have hX0 : 0 ≤ X := by rw [hXd]; have := hmbar.le; positivity
    have hT0 : 0 ≤ histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ := by positivity
    have hmax : 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0 ≤
        histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X := by
      rw [mul_max_of_nonneg _ _ hA.le, mul_zero]
      exact max_le hKi (mul_nonneg hT0 hX0)
    have h8' : 8 * X ≤ pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i := by
      have e : pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i =
          8 * X + 8 * (128 / 49 * (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) +
            4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i) := by
        rw [hXd]; unfold pl6aQ pl6G0; ring
      rw [e]; have : 0 ≤ mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i := mul_nonneg hmbar.le hQ0
      have : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i := mul_nonneg hc₁ hP0
      linarith
    unfold kszQ
    rw [hvwA j hj]
    calc 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * V *
          (8 * max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) =
        8 * V * (2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
          max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) := by ring
      _ ≤ 8 * V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X) := by gcongr
      _ = V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) * (8 * X) := by ring
      _ ≤ _ := by gcongr
  have hkszS : ∀ i, j ≤ i → i ≤ Nh → kszS R M C₁w mbar m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * pl6r R m b μ₀ M.core.c i)) := by
    intro i hji hi
    have e : vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar)) =
        2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * ‖hBeta R m b μ₀ x i‖ := by
      rw [hvwA i hi, hrE i hi]; unfold sO pl6As; ring
    have hB := H.hβr i hi
    have hX0 : 0 ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
        (mbar * pl6r R m b μ₀ M.core.c i) := by
      have := hr0 i; have := hmbar.le; positivity
    show max (vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar))) 0 ≤ _
    rw [e]
    have := hr0 i; have := hmbar.le
    refine max_le ?_ (by positivity)
    calc _ ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * (64 / 49 * ‖hBeta R m b μ₀ x (i + 1)‖) :=
          mul_le_mul_of_nonneg_left hB hX0
      _ = _ := by ring
  -- the weight bound `s_i²|β_{i+1}| ≤ (21/32)c_u‖M_j‖r_i`
  set Mj := ‖Mmag R m b μ₀ lam j‖ with hMjd
  have hMj : 0 ≤ Mj := norm_nonneg _
  have hvwAle : ∀ i, j ≤ i → i ≤ Nh → vwA R m b μ₀ x i ≤ cu * Mj * pl6r R m b μ₀ M.core.c i :=
    fun i hji hi => by
      refine (vwA_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl
        hsmall x h1 hji hi (hβne i hi).1).trans ?_
      exact mul_le_mul_of_nonneg_left (hgr i hi) (mul_nonneg hcu hMj)
  have hwt : ∀ i, j ≤ i → i ≤ Nh → histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ ≤
      21 / 32 * cu * Mj * pl6r R m b μ₀ M.core.c i := fun i hji hi => by
    have h1' := hβu i hi
    have h2 := hvwAle i hji hi
    rw [hvwA i hi] at h2
    have h3 : histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ ≤
        histS (R.withMsq m) i t ^ 2 * (21 / 16 * ‖hBeta R m b μ₀ x i‖) :=
      mul_le_mul_of_nonneg_left h1' (sq_nonneg _)
    nlinarith
  -- the history sizes
  have hU := pairUnitSeed_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl hsmall
  have hVB := hVBtop x hx h1 hj
  have hSz := fun i (hji : j ≤ i) (hi : i ≤ Nh) =>
    hKSW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj
      (Nh + 1) le_rfl hVB i hji (by omega) hi
  -- the reduced state
  have hRd := pairSectRed_of R m hVv hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hloc' : ∀ k, j ≤ k → k ≤ Nh → Obs2.OLocS (ptsX x) k
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) := fun k hk hkN =>
    PtCorr2.olocS_hR (R.withMsq m) (ptsX x) t hloc0 hk fun i' _ hi' => hRI i' (by omega)
  have hQK0 : ∀ i, 0 ≤ kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i := fun i => by
    unfold kszQ
    exact mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hV)
      (mul_nonneg (by norm_num) (le_max_right _ _))
  have hSK0 : ∀ i, 0 ≤ kszS R M C₁w mbar m b μ₀ lam x i := fun i => by
    unfold kszS; exact le_max_right _ _
  -- the non-seed defects
  obtain ⟨sp, sf, sL, hsp0, hNSk, hsL, hNSsum⟩ := hNS x hx h1 hj
  -- the seed term
  have hseed := pairDefSeed_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x hx h1 hj
    (fun k => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k)
    (fun k => 2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x k)
    (fun k => mul_nonneg hcNS (hQK0 k)) (fun k => mul_nonneg (by positivity) (hSK0 k))
    (fun k hk hkN => by
      have H' := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hk
      exact kappaQ_le_count (ptsX x) _ univ H'.hK (hQK0 k) (hSz k hk (by omega)).1
        (fun b' hb' => by exact_mod_cast cSm2_spec L N k b' hb')
        (fun y s hs' => by exact_mod_cast cNb2_spec L N k y s hs'))
    (fun k hk hkN => by
      have h2 := kappaS_le_count (ptsX x)
        (fun Bp => (SXO k (histCovO (R.withMsq m) t k)
          (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
          (hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) Bp : SA .two (Lam 2 L N)).ab)
        univ (fun b' hb' hn => ((hSz k hk (by omega)).2.1 b' hb').2 hn) (hSK0 k)
        (fun b' hb' => ((hSz k hk (by omega)).2.1 b' hb').1)
      exact h2)
  -- the witness
  refine ⟨fun k => histS (R.withMsq m) k t,
    fun k => cQab * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k,
    fun k => max (kszW R M C₁w mbar m b μ₀ lam x k) 0, sp, sf,
    fun k => Obs2.m4Tot (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k),
    sL, fun k => ⟨hs k, mul_nonneg cQab_nonneg (hQK0 k), le_max_right _ _, (hsp0 k).1, (hsp0 k).2⟩,
    fun k hk => ?_, hsL, ?_⟩
  · -- the items at `k`
    have hjk := (mem_Ico.1 hk).1
    have hkN : k ≤ Nh := by have := (mem_Ico.1 hk).2; omega
    obtain ⟨hp, hf⟩ := hNSk k hk
    have hS3 := hSz k hjk hkN
    have HA := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hjk
    refine ⟨hG k hkN, fun B => ?_, fun B => ((hloc' k hjk hkN).hW B).2.2.2.1, fun B => ?_, hp, hf⟩
    · exact cQab_spec L hL8 N (ptsX x) k (by omega) _ (hs k) _ _ _ HA _ (hQK0 k)
        (fun X hX => ((hloc' k hjk hkN).hK X ⟨hX.1, hX.2.1⟩).2.2.2.1) hS3.1 B
    · exact (hS3.2.2 B).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · -- the sum
    have hsplit : ∑ k ∈ Finset.Ico j (Nh + 1),
        (2 * (Q1 2 * (cQab * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k)) +
          2 * (Q1 2 * max (kszW R M C₁w mbar m b μ₀ lam x k) 0) + sp k + sf k +
          ‖Obs2.m4Tot (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)‖ *
            (2 * histS (R.withMsq m) k t ^ 2 *
              ((L : ℝ) ^ (j + 1) * (histS (R.withMsq m) k t / (L : ℝ) ^ (k + 1))) ^ 2)) =
        ∑ k ∈ Finset.Ico j (Nh + 1),
          (2 * (Q1 2 * (cQab * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k)) +
            2 * (Q1 2 * max (kszW R M C₁w mbar m b μ₀ lam x k) 0)) +
        ∑ k ∈ Finset.Ico j (Nh + 1), (sp k + sf k) +
        ∑ k ∈ Finset.Ico j (Nh + 1),
          ‖Obs2.m4Tot (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)‖ *
            (2 * histS (R.withMsq m) k t ^ 2 *
              ((L : ℝ) ^ (j + 1) * (histS (R.withMsq m) k t / (L : ℝ) ^ (k + 1))) ^ 2) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun k _ => by ring
    -- the history sum
    set aQ := pd5aQ M C₁k C₁w with haQd
    set aS := pd5S L C₁w with haSd
    have haQ0 : 0 ≤ aQ := by
      rw [haQd]; unfold pd5aQ
      exact mul_nonneg (by have := cQab_nonneg; positivity) haQ
    have haS0 : 0 ≤ aS := by rw [haSd]; unfold pd5S; positivity
    set Y := 21 / 32 * cu * Mj with hYd
    have hY : 0 ≤ Y := by positivity
    set r := pl6r R m b μ₀ M.core.c with hrd
    set g' : ℕ → ℝ := fun i => max (min (t i).1 M.core.ε) 0 with hg'd
    have hrg : ∀ i ≤ Nh, r i = M.core.c * g' i := fun i hi => by
      show M.core.c * max (t i).1 0 = M.core.c * max (min (t i).1 M.core.ε) 0
      rw [min_eq_left (hg i hi).2]
    have hitem : ∀ k ∈ Finset.Ico j (Nh + 1),
        2 * (Q1 2 * (cQab * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k)) +
          2 * (Q1 2 * max (kszW R M C₁w mbar m b μ₀ lam x k) 0) +
          16 * (KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 *
            (2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k) +
            2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x k)) ≤
        V * Y * aQ * pl6P j k₀ k + V * Y * (aQ + aS) * mbar *
          ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
            ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
            (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
      intro k hk
      have hjk := (mem_Ico.1 hk).1
      have hkN : k ≤ Nh := by have := (mem_Ico.1 hk).2; omega
      set wt := histS (R.withMsq m) k t ^ 2 * ‖hBeta R m b μ₀ x (k + 1)‖ with hwtd
      have hwt0 : 0 ≤ wt := by positivity
      have hwtk := hwt k hjk hkN
      have hrk0 := hr0 k
      have hrk1 := hr1 k hkN
      have hG0 := pl6G0_nonneg (j := j) (r := r) hk₀ hmbar.le k
      -- `kszQ`
      have hQ : kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k ≤
          V * Y * (pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar r k) := by
        refine (hkszQ k hjk hkN).trans ?_
        have h2 : wt ≤ Y :=
          calc wt ≤ 21 / 32 * cu * Mj * r k := hwtk
            _ ≤ 21 / 32 * cu * Mj * 1 :=
                mul_le_mul_of_nonneg_left hrk1 (by positivity : (0 : ℝ) ≤ 21 / 32 * cu * Mj)
            _ = Y := by rw [hYd]; ring
        have := mul_le_mul_of_nonneg_left h2 hV
        exact mul_le_mul_of_nonneg_right this (mul_nonneg haQ hG0)
      -- `kszS`
      have hS : kszS R M C₁w mbar m b μ₀ lam x k ≤
          V * Y * (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * r k ^ 2)) := by
        refine (hkszS k hjk hkN).trans ?_
        have hc' : 0 ≤ 128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) := by positivity
        have h2 := mul_le_mul_of_nonneg_left hwtk hV
        have e1 : V * wt * (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * r k)) =
            (V * wt) * (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * mbar * r k) := by ring
        have e2 : V * Y * (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * r k ^ 2)) =
            (V * (21 / 32 * cu * Mj * r k)) *
              (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * mbar * r k) := by
          rw [hYd]; ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right h2 (by have := hmbar.le; positivity)
      -- `kszW`
      have hW : max (kszW R M C₁w mbar m b μ₀ lam x k) 0 ≤
          V * Y * (32 / 21 * (4 * C₁w + 1) * (mbar * r k ^ 2)) := by
        have hW1 : kszW R M C₁w mbar m b μ₀ lam x k =
            vwA R m b μ₀ x k * V * ((4 * C₁w + 1) * r k * mbar) := by
          unfold kszW; rw [hrE k hkN]; rfl
        have hvA := hvwAle k hjk hkN
        have hvA0 := vwA_nonneg R m b μ₀ x k
        refine max_le ?_ (by have := hmbar.le; positivity)
        rw [hW1]
        have e2 : V * Y * (32 / 21 * (4 * C₁w + 1) * (mbar * r k ^ 2)) =
            (cu * Mj * r k) * V * ((4 * C₁w + 1) * r k * mbar) := by rw [hYd]; ring
        rw [e2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hvA hV)
          (by have := hmbar.le; positivity)
      -- the profile `Q`
      have hQc : pl6Q j r k ≤ ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
          ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) := by
        unfold pl6Q
        refine sum_le_sum fun i hi => ?_
        have hiN : i ≤ Nh := by have := (mem_Ico.1 hi).2; omega
        rw [hrg i hiN]
        have : 0 ≤ (M.core.c * g' i) * (M.core.c * g' k) := by
          rw [← hrg i hiN, ← hrg k hkN]; exact mul_nonneg (hr0 i) (hr0 k)
        have : 0 ≤ (1 / 2 : ℝ) ^ (k - i) := by positivity
        nlinarith
      have hlast : 0 ≤ (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k) := by
        rw [← hrg k hkN]; exact mul_nonneg (by positivity) (hr0 k)
      have hrk : r k ^ 2 = (M.core.c * g' k) ^ 2 := by rw [hrg k hkN]
      -- assembly
      have hVY : 0 ≤ V * Y := mul_nonneg hV hY
      have hQ1c : 0 ≤ 2 * Q1 2 * cQab := by have := cQab_nonneg; positivity
      have eL : 2 * (Q1 2 * (cQab * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k)) +
          2 * (Q1 2 * max (kszW R M C₁w mbar m b μ₀ lam x k) 0) +
          16 * (KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 *
            (2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k) +
            2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x k)) =
          (2 * Q1 2 * cQab + 16 * KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 * (2 * (cNb2 : ℝ) * (cSm2 : ℝ)))) *
            kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k +
          2 * Q1 2 * max (kszW R M C₁w mbar m b μ₀ lam x k) 0 +
          32 * (L : ℝ) ^ 2 * KM4 2 CcutE * kszS R M C₁w mbar m b μ₀ lam x k := by ring
      rw [eL]
      have hA0 : 0 ≤ 2 * Q1 2 * cQab + 16 * KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 *
          (2 * (cNb2 : ℝ) * (cSm2 : ℝ))) := by positivity
      have i1 := mul_le_mul_of_nonneg_left hQ hA0
      have i2 := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ 2 * Q1 2)
      have i3 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 32 * (L : ℝ) ^ 2 * KM4 2 CcutE)
      have eR : (2 * Q1 2 * cQab + 16 * KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 *
            (2 * (cNb2 : ℝ) * (cSm2 : ℝ)))) * (V * Y * (pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar r k)) +
          2 * Q1 2 * (V * Y * (32 / 21 * (4 * C₁w + 1) * (mbar * r k ^ 2))) +
          32 * (L : ℝ) ^ 2 * KM4 2 CcutE *
            (V * Y * (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * r k ^ 2))) =
          V * Y * aQ * pl6P j k₀ k + V * Y * aQ * mbar * pl6Q j r k +
            V * Y * aS * mbar * r k ^ 2 := by
        rw [haQd, haSd]; unfold pd5aQ pd5S pl6G0; rw [← hBkd]; ring
      have hfin : V * Y * aQ * pl6P j k₀ k + V * Y * aQ * mbar * pl6Q j r k +
          V * Y * aS * mbar * r k ^ 2 ≤
          V * Y * aQ * pl6P j k₀ k + V * Y * (aQ + aS) * mbar *
            ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
              ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
              (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
        rw [hrk] at *
        have hm0 := hmbar.le
        have hVYm : 0 ≤ V * Y * mbar := mul_nonneg hVY hm0
        have hQ0 := pl6Q_nonneg (j := j) (r := r) k
        have hr2 : 0 ≤ (M.core.c * g' k) ^ 2 := sq_nonneg _
        have e : V * Y * (aQ + aS) * mbar *
            ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
              ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
              (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) =
            V * Y * mbar * aQ * ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
              ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
              (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) +
            V * Y * mbar * aS * ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
              ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
              (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by ring
        rw [e]
        have hsum0 : 0 ≤ ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
            ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) := hQ0.trans hQc
        have j1 : V * Y * aQ * mbar * pl6Q j r k ≤ V * Y * mbar * aQ * ((M.core.c * g' k) ^ 2 +
            ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
              ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
            (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
          have : V * Y * aQ * mbar * pl6Q j r k = V * Y * mbar * aQ * pl6Q j r k := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hVYm haQ0)
        have j2 : V * Y * aS * mbar * (M.core.c * g' k) ^ 2 ≤ V * Y * mbar * aS *
            ((M.core.c * g' k) ^ 2 + ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) *
              ((M.core.c * g' i) ^ 2 + (M.core.c * g' i) * (M.core.c * g' k)) +
            (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
          have : V * Y * aS * mbar * (M.core.c * g' k) ^ 2 =
              V * Y * mbar * aS * (M.core.c * g' k) ^ 2 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hVYm haS0)
        linarith
      linarith
    -- `∑ǧ² ≤ G₂`
    have hG2 : ∑ k ∈ Finset.Ico j (Nh + 1), g' k ^ 2 ≤ pl6G2 L M.core.ε := by
      have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
      have hinc := M.gincD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
      have hS := sum_gsq_Ico_le (g := fun i => (t i).1) hβL hj (fun k hk hkn => hinc k hkn)
      have e : ∑ k ∈ Finset.Ico j Nh, g' k ^ 2 = ∑ k ∈ Finset.Ico j Nh, ((t k).1) ^ 2 :=
        sum_congr rfl fun k hk => by
          rw [hg'd]; dsimp only
          rw [min_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).2,
            max_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).1.le]
      rw [sum_Ico_succ_top hj, e]
      have h2 : g' Nh ^ 2 ≤ M.core.ε ^ 2 := by
        rw [hg'd]; dsimp only
        exact pow_le_pow_left₀ (le_max_right _ _) (max_le (min_le_right _ _) hε0) 2
      have h3 : 4 / betaL L * ((t Nh).1 - (t j).1) ≤ 4 * M.core.ε / betaL L := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hβL.le
        have := (hg Nh le_rfl).2; have := (hg j hj).1; nlinarith
      unfold pl6G2; linarith
    have hCE : 0 ≤ V * Y * (aQ + aS) := by positivity
    have hsum := pairLoop2_sum_le (q := 1 / 2) (by norm_num) le_rfl hc0 hCE hmbar.le
      (g := g') (fun i => le_max_right _ _) (fun i => max_le (min_le_right _ _) hε0)
      (seed := fun k => V * Y * aQ * pl6P j k₀ k) hG2 hitem
    have hseedS : ∑ k ∈ Finset.Ico j (Nh + 1), V * Y * aQ * pl6P j k₀ k ≤ 2 * (V * Y * aQ * k₀) := by
      have h := geom_decay_le (q := 1 / 2) (by norm_num) le_rfl (g := fun _ => (1 : ℝ))
        (fun _ => zero_le_one) (fun _ => le_rfl) j (Nh + 1)
      unfold pl6P
      have e : ∑ k ∈ Finset.Ico j (Nh + 1), V * Y * aQ * ((1 / 2 : ℝ) ^ (k - j) * k₀) =
          V * Y * aQ * k₀ * ∑ k ∈ Finset.Ico j (Nh + 1), (1 / 2 : ℝ) ^ (k - j) * 1 := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      rw [e]
      have : 0 ≤ V * Y * aQ * k₀ := by positivity
      nlinarith
    -- the seed term against `κ`
    have hseedK : 16 * ∑ k ∈ Finset.Ico j (Nh + 1), KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 *
        (2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k) +
          2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x k) =
        ∑ k ∈ Finset.Ico j (Nh + 1), 16 * (KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 *
          (2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k) +
            2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x k)) := by rw [mul_sum]
    have hcomb : ∑ k ∈ Finset.Ico j (Nh + 1),
          (2 * (Q1 2 * (cQab * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k)) +
            2 * (Q1 2 * max (kszW R M C₁w mbar m b μ₀ lam x k) 0)) +
        16 * ∑ k ∈ Finset.Ico j (Nh + 1), KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 *
          (2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x k) +
            2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x k) ≤
        2 * (V * Y * aQ * k₀) + V * Y * (aQ + aS) * mbar *
          (6 * M.core.c ^ 2 * pl6G2 L M.core.ε + 2 * M.core.c * M.core.ε) := by
      rw [hseedK, ← sum_add_distrib]
      exact hsum.trans (by linarith)
    have hcd : (2 * (V * Y * aQ * k₀) + V * Y * (aQ + aS) * mbar *
          (6 * M.core.c ^ 2 * pl6G2 L M.core.ε + 2 * M.core.c * M.core.ε)) =
        pd5CS M C₁k C₁w mbar * Mj ^ 2 * (t j).1 := by
      have hVe : V = Mj * (t j).1 := by rw [hVd, hMjd]; rfl
      rw [hYd, hVe, haQd, haSd, hk₀d, hcud]; unfold pd5CS; ring
    rw [hsplit]
    rw [hcd] at hcomb
    beta_reduce at hseed
    have e : (cd + pd5CS M C₁k C₁w mbar) * Mj ^ 2 * (t j).1 =
        pd5CS M C₁k C₁w mbar * Mj ^ 2 * (t j).1 + cd * Mj ^ 2 * (t j).1 := by ring
    show _ ≤ (cd + pd5CS M C₁k C₁w mbar) * Mj ^ 2 * (t j).1
    rw [e]
    have hNS' : ∑ k ∈ Finset.Ico j (Nh + 1), (sp k + sf k) + sL ≤ cd * Mj ^ 2 * (t j).1 := hNSsum
    linarith [hseed, hcomb, hNS']


/-- **`PairDefSizesR3P` from the non-seed defects at the canonical constants**
`C₁k = C₁ka`, `C₁w = C₁wa` of the master construction (`MasterCore.abwHistC`; the decay
requirement is the field `hEaB`). -/
theorem pairDefSizesR3P_of_NS_MFCD {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl → HLam R Nh m b μ₀ lam Kl →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ mbar : ℝ, 0 < mbar →
      8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        (4 * M.core.C₁wa + 1) * mbar →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh → PairVB R m b μ₀ lam x mbar (Nh + 1)) →
    ∀ cd : ℝ, PairDefSizesNS R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      PairDefSizesR3P R Nh m b μ₀ lam (oRed R m b μ₀ dxStd)
        (cd + pd5CS M M.core.C₁ka M.core.C₁wa mbar) := by
  obtain ⟨-, hC₁k, -, hθ, -, -, -, hC₁w, -⟩ := M.core.hEaB
  exact pairDefSizesR3P_of_NS_atD M hC₁k hC₁w M.core.abwHistCD6 hθ


set_option maxHeartbeats 2000000 in
/-- **`PairVB … m̄ (N_h + 1)` from `PairRRelRX`** (see the module docstring). -/
theorem pairVB_top_MFD {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁v : ℝ, 0 ≤ C₁v ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ jD ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ jD)) →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar → cr ≤ mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁v * ((4 * C₁v + 1) * mbar) →
      PairRRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → PairVB R m b μ₀ lam x mbar (Nh + 1) := by
  obtain ⟨C₁v, hC₁v, hVS⟩ := pairVStep_MFD M
  refine ⟨C₁v, hC₁v, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar hcr h8v hRX
    x hx h1 hj
  obtain ⟨hVB0, hVs⟩ := hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU
    hmbar hcr h8v x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hMs : ∀ n, n ≤ Nh + 1 → PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ dxStd) cr x n :=
    fun n hn M' hM1 hM2 X hX k hk1 hk2 => hRX x hx h1 hj M' hM1 (hM2.trans hn) X hX k hk1 hk2
  have key : ∀ d, j + d ≤ Nh + 1 → PairVB R m b μ₀ lam x mbar (j + d) := by
    intro d
    induction d with
    | zero => intro _; simpa using hVB0
    | succ d ih =>
      intro hd
      have h := hVs (j + d) (by omega) (by omega) (ih (by omega)) (hMs (j + d) (by omega))
      simpa [Nat.add_assoc] using h
  have := key (Nh + 1 - j) (by omega)
  rwa [show j + (Nh + 1 - j) = Nh + 1 by omega] at this


end

end Spin2
