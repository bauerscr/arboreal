import Spin2.Pair.PairESz4
import Spin2.Master.MasterVHist

/-!
# The `E`-step sizes (5): the history `K` and `S` sizes of the reduced states under `PairVB`

**`pairKSSizes_MF`**: under `MasterFacts`, `PairUnitSeed c_u`, the seed condition of the `ab` chain
`8c_u(2ι_WA)^{(L+18)²} ≤ (4C₁w+1)m̄` (`C₁k`, `C₁w` of `MasterCore.abwHist`) and `PairVB … m̄ n`,
for the reduced states `oRed … dxStd` in the weights `M_{a,i} = vwA i`, `M_b = vwB`:

* for `j_x ≤ i < n`, `i ≤ N_h` (`i = N_h` included, `MasterCore.vhistK`): on small sets
  `‖K_i(X)_{ab}‖_{T_i(s_i)} ≤ kszQ_i = 8M_{a,j_x}M_b·k_i`, `k_i = kseqF(8θ_b, B, cǧ, m, j_x, k₀)_i`
  the comparison sequence of the `ab` chain (`m_i = c_W(M_{a,i}/M_{a,j_x})m̄`, seed
  `k₀ = c_u(2ι_WA)^{(L+18)²}`: `k_i = θ^{i−j_x}k₀ + ∑θ^{i−1−i'}B(cǧ_{i'})²m_{i'}`);
* for `i < N_h` in addition (`MasterCore.vhistS`):
  `‖S_i(B_+)_{ab}‖_{T_{i+1}(s_{i+1})} ≤ kszS_i = M_{a,i}M_bL²s_O(cǧ_i, m̄, c_Wcǧ_im̄)`, and
  `S_i(B_+)_{ab} = 0` unless `B_+` meets `{a, b}`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The comparison sequence `k_i` of the `ab` chain of the reduced state (`C₁k`, `C₁w` of
`MasterCore.abwHist`). -/
def kszK (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (i : ℕ) : ℝ :=
  kseqF (8 * (kθ0 L M.core.A M.core.C₀a M.core.ηa + C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) *
      (M.core.c * M.core.ε)))
    (kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT))
    (fun i => M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1)
    (fun i => (4 * C₁w + 1) * (vwA R m b μ₀ x i * vwB R m b μ₀ lam x /
      (vwA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) * vwB R m b μ₀ lam x) * mbar))
    (Obs.coal L (0 : Lam 2 L N) x) (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) i

/-- The small-set `K` size `8M_{a,j_x}M_b·k_i`. -/
def kszQ (M : MasterFacts L) (C₁k C₁w mbar cu m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N)
    (i : ℕ) : ℝ :=
  vwA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) * vwB R m b μ₀ lam x *
    (8 * max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0)

/-- The `S` size `M_{a,i}M_bL²s_O(cǧ_i, m̄, c_Wcǧ_im̄)`. -/
def kszS (M : MasterFacts L) (C₁w mbar m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (i : ℕ) : ℝ :=
  max (vwA R m b μ₀ x i * vwB R m b μ₀ lam x * ((L : ℝ) ^ 2 *
    sO 2 L (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1) mbar
      ((4 * C₁w + 1) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1) * mbar))) 0

end Traj

set_option maxHeartbeats 4000000 in
/-- **`pairKSSizes_MF` at given constants** (`hAH`: `MasterCore.abwHist` at `C₁k`, `C₁w`). -/
theorem pairKSSizes_MFat {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w : ℝ} (hC₁k : 0 ≤ C₁k)
    (hC₁w : 0 ≤ C₁w) (hAH : M.core.AbwHistP C₁k C₁w) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
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
      (i < Nh → ∀ b' ∈ blockIdx (L := L) (N := N) i,
        Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t)
            (SXO i (C i) (V i) (W i) (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (kszS R M C₁w mbar m b μ₀ lam x i) ∧
        (¬ (Step2.Bp (L := L) (N := N) i b' ∩ (ptsX x).pts).Nonempty →
          (SXO i (C i) (V i) (W i) (Step2.Bp (L := L) (N := N) i b') : SA .two (Lam 2 L N)).ab = 0)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj
    n hn hVB i hi1 hin hiN
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβr := pairBetaRatio_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := by
    obtain ⟨q, -, -, hl⟩ :=
      (M.loop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
    intro k hk
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1)
      (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1 k hk
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
  obtain ⟨hpa, hpb, hK⟩ := pairSeed_hK0 M.pairInitW R hP hi0 hRℓ hRA hRρ hN2 hNh hm hadm x h1 hj
  have hU' := hU x hx h1 hj
  have hg0 : 0 ≤ ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 := (hadm.1 j hj).1.le
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
  refine ⟨fun Y hY => ?_, fun hiN' b' hb' => ?_⟩
  · have hKs := M.core.vhistK N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (hMa i) hwB
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
      have h1 := (hadm.1 i hiN).1.le
      have h2 : 0 ≤ M.core.c := by
        rw [← hcR']; unfold cR cV cW cZ
        obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
        have := H.hcmu; have := H.hC₂; positivity
      exact mul_nonneg h2 h1
    obtain ⟨hS1, hS2⟩ := M.core.vhistS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
      (hMa i) hwB (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj hanc i hi1 hiN' mbar _ hmbar.le
      (by have := hC₁w; positivity) (fun b' hb' => hVB i hi1 hin b' hb') hWo b' hb'
    exact ⟨hS1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)), hS2⟩

end

end Spin2
