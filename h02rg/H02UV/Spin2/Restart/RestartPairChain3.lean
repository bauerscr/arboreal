import Spin2.Restart.RestartPairChain1

/-!
# T5, item (5): the zero mode of the reduced chain for `j_x ≤ N_h`, linear in the `a`-side size

Pair `(0, x)` with `1 ≤ j_x ≤ N_h`, `h = 0`. For a general observable state `o` at `j_x` (local),
`o' = rpcRed o` (reduced at `j_x`), `o'' = rpcTail o` (the reduced chain at `N_h + 1`), and the
reduced objects `zCstR`, `zZmR` of `oG = fun _ => o'` (`Spin2/Pair/PairRed2`):

* **`rpc_out_eq_R`** (exact): `rpcOut o = rpTopU o·γ_{x,j_x} − (n_{ab}X' + n_{ab}Ω')`,
  `X' = zCstR oG x` (the reduced constants: chain constants and `det·e^{-u'_N}`),
  `Ω' = zZmR oG x` (the reduced zero mode);
* **`rpc_zm_le`**: from the sizes of `o''` in `wM(2s_{N_h}²σ, M_b)` at `N_h + 1`
  (`‖V‖ ≤ c_V`, `‖𝒲‖ ≤ c_Wǧ_{N_h}`, `A^{(|𝓑(X)|-4)_+}‖K‖ ≤ c_K`) and the reference one-point items
  of `rp_topE_le` (now from `pair_E_split` instead of `pairTop_E`):
  `|n_{ab}Ω'| ≤ 8(½ + (81/32)c_{Jab}c_S)c_uK₄·(σ/|β_{a,N_h}|)·‖M_{N_h}‖²ǧ_{N_h}`,
  `c_S = c_V + c_W + 8c_K + 1`; also `|lastDefR| ≤ c_{Lab}c_S·M_aM_b` (the last-step defect);
* **`rpc_out_le`**: `|rpcOut o| ≤ |rpTopU o||γ_{x,j_x}| + |n_{ab}X'| + (the bound above)`.

Linear in the `a`-side data `(rpTopU o, σ)`; the remaining input is the size of the reduced chain
(`o''` at `N_h + 1`, and `n_{ab}X'`) from the seed at `j_x` (`rpc_seed_gen`) — the pair chain above
coalescence with a general seed.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 2000000 in
/-- **The output at `j_x ≤ N_h` through the reduced objects** (exact). -/
theorem rpc_out_eq_R {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hl : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o) :
    rpcOut R m b μ₀ x o = rpTopU o * uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) -
      (PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x) +
        PtCorr2.nAB (zZmR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨hX, hΩ, -, -⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
  have e : zOm R m b μ₀ x j = zCst R Nh m b μ₀ x j * zZm R Nh m b μ₀ x :=
    hw.trans (zHi_eq R Nh m b μ₀ x)
  have hY0 : PtCorr2.sE (zOm R m b μ₀ x j) ≠ 0 := by
    rw [e, PtCorr2.sE_mul]; exact mul_ne_zero hX hΩ
  have hcore : ∀ i ≤ Nh, ValidCore (R.withMsq m) i := fun i hi => by
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · rw [show i = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU (R.withMsq m) hV hVL t
  have hoR : (rpcRef R m b μ₀ x).IsObs :=
    Obs2.obsHist_isObs (R.withMsq m) (ptsX x) _ (Obs2.obsInit_isObs .two (zV b) (ptsX x)) j t
  have hlR : PtCorr2.ObsLocInv (ptsX x) j (rpcRef R m b μ₀ x) :=
    PtCorr2.obsLocInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsLocInv_init .two (zV b) (ptsX x))
      t j fun i hi => ⟨hcore i (by omega), hRI i (by omega)⟩
  have hYo : PtCorr2.sE (rpcZ R m b μ₀ x o) ≠ 0 := by
    have hi := PtCorr2.rpc_sE_indep (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm hV hVL b μ₀ hj
      ho hl hoR hlR
    have hi' : PtCorr2.sE (rpcZ R m b μ₀ x o) = PtCorr2.sE (rpcZ R m b μ₀ x (rpcRef R m b μ₀ x)) :=
      hi
    rw [hi', rpcZ_ref]; exact hY0
  obtain ⟨-, hsplit⟩ := PtCorr2.rpc_pair_red_gen (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm hV hVL
    b μ₀ hj o ho hl (pairDCov_std Nh x hx h1 hj)
  obtain ⟨-, -, hE⟩ := hsplit hYo
  unfold rpcOut rpcE
  have hE' : PtCorr2.nAB (rpcZ R m b μ₀ x o) =
      PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x) +
        PtCorr2.nAB (zZmR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x) := hE
  rw [hE']

set_option maxHeartbeats 8000000 in
/-- **The zero mode of the reduced chain for `j_x ≤ N_h`, linear in the `a`-side size.** -/
theorem rpc_zm_le {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK0 r₀ : ℝ} (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hb : 0 < b) (hh0 : b = μ₀ + m)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) (hA2 : 2 ≤ R.A)
    (hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (R.A / 2) r₀)
    (hcW : 0 ≤ cW) (hcK0 : 0 ≤ cK0) (hCf : 0 ≤ Cf)
    (hg0 : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hs1 : 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ R.ρ)
    (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2)
    (hs3 : cRho L * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀)
    (lam : ℕ → ℂ) (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    (o : Obs2.ObsSt .two L N)
    (hl : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o)
    {σ Mb cVo cWo cKo cu K4 KA : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb) (hcVo : 0 ≤ cVo) (hcWo : 0 ≤ cWo)
    (hcKo : 0 ≤ cKo) (hcu : 0 ≤ cu)
    (hVo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rpcTail R Nh m b μ₀ x o).V b') ≤ ENNReal.ofReal cVo)
    (hWo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rpcTail R Nh m b μ₀ x o).W b') ≤
        ENNReal.ofReal (cWo * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1))
    (hKo : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rpcTail R Nh m b μ₀ x o).K X) ≤ ENNReal.ofReal cKo)
    (hMbM : Mb ≤ cu * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hβ0 : hBeta R m b μ₀ x Nh ≠ 0)
    (hone1 : ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖)
    (hone2 : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KA * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖)
    (hgam : ‖gamNa R Nh m b μ₀ x‖ ≤ K4 * ‖Mmag R m b μ₀ lam Nh‖)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2) (hmA : 8 * KA * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (cVo + cWo + 8 * cKo + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖PtCorr2.nAB (zZmR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ ≤
        8 * (1 / 2 + 81 / 32 * cJab L r₀ * (cVo + cWo + 8 * cKo + 1)) * cu * K4 *
          (σ / ‖hBeta R m b μ₀ x Nh‖) * ‖Mmag R m b μ₀ lam Nh‖ ^ 2 *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ∧
      ‖lastDefR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x‖ ≤
        cLab L * (cVo + cWo + 8 * cKo + 1) *
          (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ * Mb) := by
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set oG : Lam 2 L N → Obs2.ObsSt .two L N := fun _ => rpcRed R m b μ₀ x o with hoG
  set Mn := ‖Mmag R m b μ₀ lam Nh‖ with hMn
  set g := (t Nh).1 with hgd
  set sN := histS (R.withMsq m) Nh t with hsN
  set Ma := 2 * sN ^ 2 * σ with hMad
  set hb0 := ‖hBeta R m b μ₀ x Nh‖ with hb0d
  have hhb0 : 0 < hb0 := norm_pos_iff.2 hβ0
  have hMn0 : 0 ≤ Mn := norm_nonneg _
  have hsN : 0 < sN := histS_pos' (R.withMsq m) hρ0 hVL.2.2.2.2.2.1 t Nh
  have hMa : 0 < Ma := mul_pos (mul_pos two_pos (pow_pos hsN 2)) hσ
  -- the reference one-point items at `j_x ≤ N_h`
  obtain ⟨hX0, hΩ0, -, hω⟩ := pair_E_split R hNh m hρ1 hspl hm0 hm hV hVL hL8 hb (le_of_eq hh0) x hj
  have hr0 : 1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) = 0 := by
    rw [PtCorr2.onept_avg0_h0 hb hm0 hh0, mul_one_div_cancel
      (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]
  have hnA : PtCorr2.nA (zZm R Nh m b μ₀ x) = 0 - gamNa R Nh m b μ₀ x := by
    rw [hω, hr0, uA_add_nA_zCst R Nh m b μ₀ x (by omega) hX0]
  rw [zero_sub] at hnA
  -- the reduced chain at `N_h + 1`
  have hcore : ∀ i ≤ Nh, ValidCore (R.withMsq m) i := fun i hi => by
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · rw [show i = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU (R.withMsq m) hV hVL t
  have habT : PtCorr2.ObsAbInv (Nh + 1) (rpcTail R Nh m b μ₀ x o) :=
    PtCorr2.rpc_tail_abInv (R.withMsq m) (ptsX x) (PtCorr2.rpcRedSt_abInv _ _ _ _ _ _) t
      (by omega)
  have hlocT : PtCorr2.ObsLocInv (ptsX x) (Nh + 1) (rpcTail R Nh m b μ₀ x o) := by
    have hl0 := PtCorr2.rpcRedSt_loc hV hVL t hj hl (dxStd (L := L) (N := N) x)
    have h := PtCorr2.obsLocInv_histFrom (R := R.withMsq m) (P := ptsX x) hl0 t
      (Nh + 1 - Obs.coal L (0 : Lam 2 L N) x)
      (fun i _ hi2 => ⟨hcore i (by omega), hRI i (by omega)⟩)
    rw [show Obs.coal L (0 : Lam 2 L N) x + (Nh + 1 - Obs.coal L (0 : Lam 2 L N) x) = Nh + 1 by
      omega] at h
    exact h
  obtain ⟨s', hs', hsc1, hsc2, hc2, hε, hLD⟩ := pairLastAB_xT R hNh hV hVL hVN hLp hL8 hA2 hmN hG
    hr₀ hr₀1 hJ hcW hcK0 hCf hg0 hg1 hs1 hs2 hs3 hs4 hs5 oG x
    (PtCorr2.rpcRedSt_isObs _ _ _ _ _ _) hlocT habT hMa hMb hcVo hcWo hcKo hVo hWo hKo
  set cS := cVo + cWo + 8 * cKo + 1 with hcSd
  have hcS : 1 ≤ cS := by rw [hcSd]; linarith
  -- the coupling `β_{a,N-1}` of the reference
  set β1 := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβ1d
  have hβx : hb0 ≤ 2 * β1 := by
    set P := ptsX (L := L) (N := N) x
    have hflow := bt2_flow R P (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
    have hBB : ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ 2 * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      rw [hflow]; exact beta_step_ge htop.1 htop.2
    have hβeq : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x)‖ =
        ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      have h : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x) =
          Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (Obs2.histVO2 (R.withMsq m) P
            (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) := by
        unfold Obs2.betaTot2
        refine sum_congr rfl fun b' _ => ?_
        rw [Obs2.histVO2_a]
        congr 1
        exact Obs2.emb_add_cmp true _ _
      rw [h]; rfl
    rw [hβ1d, hβeq]; exact hBB
  have hβ10 : 0 < β1 := by linarith
  have hβ1ne : Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) ≠ 0 := norm_pos_iff.1 hβ10
  -- the constants
  have hcJ0 : 0 ≤ cJab L r₀ := by
    unfold cJab
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcS', hQ1]
    have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
    positivity
  set cJ' := cJet L * (cRho L + 4 / r₀ ^ 2) with hcJ'd
  have hcJ'0 : 0 ≤ cJ' := by
    rw [hcJ'd]
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcS', hQ1]
    exact mul_nonneg h1 (add_nonneg h2 (by positivity))
  have hcL : 0 ≤ cLab L := by
    unfold cLab
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    positivity
  -- `M_a ≤ (81/32)·2σ s'²`-type bounds
  have hs'2 : 0 < s' ^ 2 := pow_pos hs' 2
  set eY := 81 / 32 * cJab L r₀ * cS * σ * Mb with heYd
  have heY : 0 ≤ eY := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcJ0)
    (by linarith)) hσ.le) hMb.le
  have hY : ‖Suscept.c2 (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖ ≤ eY := by
    have k1 : Ma * Mb ≤ s' ^ 2 * (81 / 32 * σ * Mb) := by
      have : Ma ≤ s' ^ 2 * (81 / 32 * σ) :=
        calc Ma = 2 * σ * sN ^ 2 := by rw [hMad]; ring
          _ ≤ 2 * σ * ((9 / 8) ^ 2 * s' ^ 2) :=
              mul_le_mul_of_nonneg_left hsc1 (by linarith)
          _ = s' ^ 2 * (81 / 32 * σ) := by ring
      have := mul_le_mul_of_nonneg_right this hMb.le
      linarith
    have k2 : s' ^ 2 * ‖Suscept.c2 (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
        s' ^ 2 * eY := by
      refine hc2.trans ?_
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ0 (by linarith : (0 : ℝ) ≤ cS))
      calc cJab L r₀ * cS * (Ma * Mb) ≤ cJab L r₀ * cS * (s' ^ 2 * (81 / 32 * σ * Mb)) := this
        _ = s' ^ 2 * eY := by rw [heYd]; ring
    exact le_of_mul_le_mul_left k2 hs'2
  -- `|εF'_{ab}| ≤ |c|·½σM_b`
  set Z := (lastOut (R.withMsq m) Nh t).Z with hZd
  have hZ : Z ≠ 0 := lastOut_Z_ne (R.withMsq m) hρ0 hρ1 Nh _
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have hc := zCc_ge R hNh hm0 b μ₀ hK hmT hZ
  set Λ := (L : ℝ) ^ (2 * N) with hΛd
  have hΛ : 0 < Λ := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hmid : 1 / (2 * m * Λ) / ‖Z‖ ≤ ‖zCc R Nh m b μ₀‖ := by
    refine le_trans (le_of_eq ?_) hc
    field_simp
    exact (div_self hZn.ne').symm
  set eX := 1 / 2 * σ * Mb with heXd
  have heX : 0 ≤ eX := mul_nonneg (mul_nonneg (by norm_num) hσ.le) hMb.le
  have hX : ‖ε (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      ‖zCc R Nh m b μ₀‖ * eX := by
    have k1 : Ma * Mb ≤ 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * (σ * Mb) := by
      have : Ma ≤ 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * σ :=
        calc Ma = 2 * σ * sN ^ 2 := by rw [hMad]; ring
          _ ≤ 2 * σ * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) :=
              mul_le_mul_of_nonneg_left hsc2 (by linarith)
          _ = 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * σ := by ring
      have := mul_le_mul_of_nonneg_right this hMb.le
      linarith
    calc ‖ε (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖
        ≤ cJ' * cS * (Ma * Mb) := hε
      _ ≤ cJ' * cS * (81 / 32 * R.ℓ ^ 2 / ‖Z‖ * (σ * Mb)) :=
          mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ'0 (by linarith))
      _ = (81 / 16 * cJ' * cS * R.ℓ ^ 2) / ‖Z‖ * eX := by rw [heXd]; ring
      _ ≤ (1 / (2 * m * Λ)) / ‖Z‖ * eX := by
          have h2mΛ : 0 < 2 * m * Λ := mul_pos (mul_pos two_pos hm0) hΛ
          have hq : 81 / 16 * cJ' * cS * R.ℓ ^ 2 ≤ 1 / (2 * m * Λ) := by
            rw [le_div_iff₀ h2mΛ]
            have e : 81 / 16 * cJ' * cS * R.ℓ ^ 2 * (2 * m * Λ) =
                2 * (81 / 16 * cJ' * cS * R.ℓ ^ 2) * m * Λ := by ring
            rw [e]; exact hmAB
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hq hZn.le) heX
      _ ≤ ‖zCc R Nh m b μ₀‖ * eX := mul_le_mul_of_nonneg_right hmid heX
  -- `|εF_a| ≤ ¼|c||β|` (reference)
  have he' : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by
    have hKA : KA * (β1 / ‖Z‖) ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := by
      have hKA0 : KA ≤ 1 / (8 * m * Λ) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hq : 0 ≤ β1 / ‖Z‖ := div_nonneg hβ10.le hZn.le
      have e : 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 = 1 / (8 * m * Λ) * (β1 / ‖Z‖) := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hKA0 hq
    have hc' : 1 / (2 * m * ‖Z‖ * Λ) ≤ ‖zCc R Nh m b μ₀‖ := by
      refine le_trans (le_of_eq ?_) hmid
      field_simp
    calc ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤ KA * β1 / ‖Z‖ := hone2
      _ = KA * (β1 / ‖Z‖) := by ring
      _ ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := hKA
      _ ≤ 1 / 4 * ‖zCc R Nh m b μ₀‖ * β1 := by gcongr
      _ = 1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by ring
  -- the zero mode of the reduced state, with the reference normaliser
  set F := zFin R Nh m b μ₀ x with hFd
  set F' := zFinR R Nh m b μ₀ oG x with hF'd
  set cc := zCc R Nh m b μ₀ with hccd
  obtain ⟨s1, s2, -, -⟩ := PtCorr2.sX_omegaCO_cstC cc F
  obtain ⟨s1', -, -, s4'⟩ := PtCorr2.sX_omegaCO_cstC cc F'
  have hoGo : (oG x).IsObs := PtCorr2.redSt_isObs _ _ _ _ _ _ _ _ _ _
  have hFe : (F' : Obs.SA .two (Lam 2 L N)).e = (F : Obs.SA .two (Lam 2 L N)).e := by
    have h := congrArg (fun y : Step.EvR (Lam 2 L N) => (y : Grassmann.N (Lam 2 L N)))
      (PtCorr2.rp_bulk_finO (R.withMsq m) (ptsX x) (Nh + 1) (histOut (R.withMsq m) Nh t).st
        (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
        (histOut (R.withMsq m) Nh t).D (histOut (R.withMsq m) Nh t).K
        (PtCorr2.obsHistFrom_isObs (P := ptsX x) (j := Obs.coal L (0 : Lam 2 L N) x)
          hoGo t (Nh + 1))
        (Obs2.obsHist_isObs (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
          (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (Nh + 1) t))
    simp only [coe_bulk] at h
    exact h
  have hΩd : zZm R Nh m b μ₀ x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F := rfl
  have hΩd' : zZmR R Nh m b μ₀ oG x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F' := rfl
  set s0 := ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e
    with hs0d
  have hs0 : s0 ≠ 0 := by
    have : PtCorr2.sE (zZm R Nh m b μ₀ x) = s0 := by rw [hΩd, s1]
    rw [← this]; exact hΩ0
  have hnABΩ : PtCorr2.nAB (zZmR R Nh m b μ₀ oG x) =
      (ε (F' : Obs.SA .two (Lam 2 L N)).ab - cc * Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).ab) /
        s0 := by
    unfold PtCorr2.nAB
    rw [hΩd', s4', s1', hFe]
  have hγ : ε (F : Obs.SA .two (Lam 2 L N)).a - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).a =
      -(gamNa R Nh m b μ₀ x * s0) := by
    have h := hnA
    unfold PtCorr2.nA at h
    rw [hΩd, s1, s2] at h
    rw [div_eq_iff hs0] at h
    rw [h]; ring
  have hZm := rp_zero_abs hβ1ne hs0 heX heY hone1 he' hγ hX hY
  rw [← hnABΩ] at hZm
  -- assembly
  have hD2 : ‖PtCorr2.nAB (zZmR R Nh m b μ₀ oG x)‖ ≤
      8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * cu * K4 * (σ / hb0) * Mn ^ 2 * g := by
    refine hZm.trans ?_
    set c1 := 1 / 2 + 81 / 32 * cJab L r₀ * cS with hc1d
    have hc10 : 0 ≤ c1 := by
      rw [hc1d]
      have : 0 ≤ 81 / 32 * cJab L r₀ * cS := mul_nonneg (mul_nonneg (by norm_num) hcJ0) (by linarith)
      linarith
    have hsum : eX + eY ≤ c1 * σ * (cu * Mn * g) := by
      have e : eX + eY = c1 * σ * Mb := by rw [heXd, heYd, hc1d]; ring
      rw [e]; exact mul_le_mul_of_nonneg_left hMbM (mul_nonneg hc10 hσ.le)
    have hγ' : ‖gamNa R Nh m b μ₀ x‖ ≤ K4 * Mn := hgam
    have hinv : 1 / β1 ≤ 2 / hb0 := by
      rw [div_le_div_iff₀ hβ10 hhb0]; linarith
    have hXY0 : 0 ≤ eX + eY := add_nonneg heX heY
    calc 4 * ‖gamNa R Nh m b μ₀ x‖ * (eX + eY) / β1
        = 4 * ‖gamNa R Nh m b μ₀ x‖ * (eX + eY) * (1 / β1) := by ring
      _ ≤ 4 * (K4 * Mn) * (c1 * σ * (cu * Mn * g)) * (2 / hb0) := by
          have hK4M : 0 ≤ K4 * Mn := (norm_nonneg _).trans hγ'
          have a1 : 4 * ‖gamNa R Nh m b μ₀ x‖ * (eX + eY) ≤
              4 * (K4 * Mn) * (c1 * σ * (cu * Mn * g)) := by
            have := mul_le_mul hγ' hsum hXY0 hK4M
            linarith
          have hMg0 : 0 ≤ cu * Mn * g := mul_nonneg (mul_nonneg hcu hMn0) hg0.le
          exact mul_le_mul a1 hinv (div_nonneg zero_le_one hβ10.le)
            (mul_nonneg (mul_nonneg (by norm_num) hK4M)
              (mul_nonneg (mul_nonneg hc10 hσ.le) hMg0))
      _ = 8 * c1 * cu * K4 * (σ / hb0) * Mn ^ 2 * g := by ring
  refine ⟨hD2, ?_⟩
  exact hLD

/-- **The output bound at `j_x ≤ N_h`**: `|rpcOut o| ≤ |rpTopU o||γ_{x,j_x}| + |n_{ab}X'| + E`
whenever `|n_{ab}Ω'| ≤ E` (e.g. `E` from `rpc_zm_le`). -/
theorem rpc_out_le {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hl : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o) {E : ℝ}
    (hZ : ‖PtCorr2.nAB (zZmR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ ≤ E) :
    ‖rpcOut R m b μ₀ x o‖ ≤
      ‖rpTopU o‖ * ‖uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)‖ +
        ‖PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ + E := by
  rw [rpc_out_eq_R R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hx h1 hj o ho hl, ← norm_mul]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le (PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x))
    (PtCorr2.nAB (zZmR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x))
  linarith

end Traj

end

end Spin2
