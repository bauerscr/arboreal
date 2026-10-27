import Spin2.Restart.RestartPairChain5
import Spin2.Restart.RestartPairTop2

/-!
# T5, item (5): the combined output bound for `1 ≤ j_x ≤ N_h` along a windowed `h = 0` trajectory

**`MasterFacts.rpc_out_traj_sz`**: on the `h = 0` trajectory `(b, b − m²)` in `D_ε` up to `N_h`
(`N ≥ 3`), for `x ≠ 0` with `1 ≤ j_x ≤ N_h`, the last-step hypotheses of `rp_top_traj` (without the
reference seed `TopSeedAt`), and for **every** observable local state `o` at `j_x`, with `σ > 0`,
`0 < M_b ≤ c_u‖M_{N_h}‖ǧ_{N_h}` (`c_u = pairUnitC`; e.g. `M_b = pM(ptsS x)_{N_h}`,
`pM_le_mag_MFD`) and the sizes of the reduced chain `o'' = rpcTail o` at `N_h + 1` in
`wM(2s_{N_h}²σ, M_b)` (`c_V`, `c_Wǧ_{N_h}`, `c_K`), `|ε(u_a(o))| ≤ γ_δ`:

  `|rpcOut o| ≤ γ_δ|γ_{x,j_x}| + |n_{ab}X'| + (9/4)·K_Z(c_S)·(σ/|β_{a,N_h}|)·ϑ_{N_h}²·ǧ_{N_h}`,
  `K_Z(c_S) = 8(1/2 + (81/32)c_{Jab}c_S)·c_u·2(1 + topF' + topCL)`, `c_S = c_V + c_W + 8c_K + 1`,

and `|d'_N| = |lastDefR| ≤ c_{Lab}c_S·2s_{N_h}²σM_b` (the last-step part of `|n_{ab}X'|`,
`rpc_cst_le`).

**`MasterFacts.rpc_out_trajC`**: the same with the sizes of `o''` from the crude chain
(`rpc_chain_sizesD`): there are `C₁w, C₁t ≥ 0` such that for the seed bound `k₀` of `rpcRed o`
(`rpc_seed_gen`), `m̄ > 0` with `8k₀ ≤ vck(C)(4C+1)m̄` (`C = C₁w, C₁t`) and the per-block masses
`ρ_n` of the reduced chain with `(2s_{N_h}²σM_b)^{-1}ρ_ns_n² ≤ m̄/2` (`j_x < n ≤ N_h + 1`),
the bound holds with `c_V = m̄`, `c_W = (4C₁t+1)c·m̄`, `c_K = (4C₁t+1)m̄`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The zero-mode constant per unit `(σ/|β|)ϑ²ǧ` at size `c_S` (`rpc_out_traj_sz`). -/
def rpcKZ (r₀ cS : ℝ) : ℝ :=
  9 / 4 * (8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * pairUnitC M * (2 * (1 + M.topF' + M.topCL)))

set_option maxHeartbeats 8000000 in
/-- **The two-point output of a general state at `j_x ≤ N_h`, along one trajectory**, from the
sizes of its reduced chain at `N_h + 1`. -/
theorem rpc_out_traj_sz {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
        9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2)
    (hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ)
    (hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
      ≤ 1 / 2)
    (hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    -- the general state at `j_x`
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hlo : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o)
    {σ Mb cVo cWo cKo γδ : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb) (hcVo : 0 ≤ cVo) (hcWo : 0 ≤ cWo)
    (hcKo : 0 ≤ cKo)
    (hMbM : Mb ≤ pairUnitC M *
      ‖Mmag R m b (b - m) (lamHat2 R (ptsX x) (zV b) m b (b - m)) Nh‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
    (hVo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
          σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((rpcTail R Nh m b (b - m) x o).V b') ≤ ENNReal.ofReal cVo)
    (hWo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
          σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((rpcTail R Nh m b (b - m) x o).W b') ≤
        ENNReal.ofReal (cWo * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
    (hKo : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
          σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((rpcTail R Nh m b (b - m) x o).K X) ≤ ENNReal.ofReal cKo)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (cVo + cWo + 8 * cKo + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ) :
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * ‖uB R m b (b - m) x (Obs.coal L (0 : Lam 2 L N) x)‖ +
        ‖PtCorr2.nAB (zCstR R Nh m b (b - m) (fun _ => rpcRed R m b (b - m) x o) x)‖ +
        M.rpcKZ r₀ (cVo + cWo + 8 * cKo + 1) * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ∧
    ‖lastDefR R Nh m b (b - m) (fun _ => rpcRed R m b (b - m) x o) x‖ ≤
      cLab L * (cVo + cWo + 8 * cKo + 1) *
        (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ * Mb) := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hε1 := M.eps_le
  have hF := M.flow
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hcWL := M.cWL_nonneg
  have hcKL := M.cKL_nonneg
  have hN2 : 2 ≤ N := by omega
  have hNh1 : 1 ≤ Nh := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set μ₀ := b - m with hμ₀
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL (R.withMsq m) Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, hCf0, -, -, hρ8, hspl, -⟩ := hF
  have hh0 : b = μ₀ + m := by rw [hμ₀]; ring
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hspl' : SplitSmall R.P L R.ρ := by rw [hP, hRρ]; exact hspl
  have hVN := M.lastValid N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hG : GlueOut (R.withMsq m) Nh M.core.Cf t :=
    (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD).1
  have hg0 : 0 < (t Nh).1 := (hD Nh le_rfl).1
  have hg1 : (t Nh).1 ≤ 1 := ((hD Nh le_rfl).2.1).trans hε1
  have hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    show |m| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1
    rw [abs_of_pos hm.1]; exact h1
  have hJ' : PtCorr2.LastJetBd L (R.A / 2) r₀ := by rw [hRA]; exact hJ
  have e2 : 8 * cM * R.ℓ ^ 2 = 8 * cM * M.core.ℓ ^ 2 := by rw [hRℓ]
  have eT : cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL =
      cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL := by rw [hRℓ]
  have hs1' : 2 * (M.core.Cf * (t Nh).1) ≤ R.ρ := by rw [hRρ]; exact hs1
  have hs2' : 8 * cM * R.ℓ ^ 2 * (M.core.Cf * (t Nh).1) ≤ 1 / 2 := by rw [e2]; exact hs2
  have hs3' : PtCorr2.cRho L * (cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL * (t Nh).1) ≤ 1 := by
    rw [eT]; exact hs3
  have hs4' : 4 * (cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL * (t Nh).1) ≤ r₀ ^ 2 := by
    rw [eT]; exact hs4
  have hs5' : cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL * (t Nh).1 ≤ r₀ := by rw [eT]; exact hs5
  -- the one-point parts at `N − 1` and `γ_{a,N}` (reference)
  set lam := lamHat2 R (ptsX x) (zV b) m b μ₀ with hlamd
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX x)
  obtain ⟨-, -, hgam⟩ := M.oneTopD R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD lam hKp hl hsmall x
  -- the one-point items of the last step at `x` (reference)
  have hNh0 : 0 < Nh := by omega
  have hWx := M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hNh0
  have hKx := M.lastKD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hNh0
  have htop := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)).1
  have hl1 := M.lastL1D N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)
    (htop.1.trans (by norm_num))
  have hKR := lastKRem_x R hNh hval hvalL hVN hLp hL8 hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1
    hs1' hs2' hs3' hs4' hs5' x h1 hWx hKx htop hl1
  have hsmA' : (M.core.Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) + 9 / 4 * (cBn * Q1 2 * M.core.cWL) +
      cKAL L R.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (t Nh).1 ≤ 1 / 2 := by
    rw [hRℓ]; exact hsmA
  obtain ⟨hP0, hone1, hone2⟩ := lastOneRem_x R hNh hval hvalL hVN hLp hL8 hG hcWL hg0.le x hWx
    htop hsmA' hKR
  rw [hP0, mul_one, norm_one, mul_one] at hone1
  rw [hP0, norm_one, mul_one] at hone2
  -- `β_{a,N_h} ≠ 0` (reference)
  have hβ0 : hBeta R m b μ₀ x Nh ≠ 0 := by
    obtain ⟨q, -, -, hlq⟩ :=
      (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b)).2.2
    exact (hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hlq k hk).1) htop Nh le_rfl).1
  have hCN := lC_diag R hval hvalL hVN b μ₀ x
  have hmA' : 8 * cKAL L R.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m *
      (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmA
  have hmAB' : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (cVo + cWo + 8 * cKo + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmAB
  -- the zero mode of the reduced chain
  obtain ⟨hZm, hLD⟩ := rpc_zm_le R hNh hm.1 hm.2 hρ1 hspl' hb hh0 hval hvalL hVN hLp hL8
    (by rw [hRA]; exact M.core.hA2) hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1 hs1' hs2' hs3'
    hs4' hs5' lam x hj o hlo hσ hMb hcVo hcWo hcKo (pairUnitC_nonneg M) hVo hWo hKo hMbM htop
    hβ0 hone1 hone2 hgam hK hmT hmA' hmAB'
  have hout := rpc_out_le R hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hL8 hb (le_of_eq hh0) x hx h1 hj
    o ho hlo hZm
  refine ⟨?_, hLD⟩
  -- `‖M‖² ≤ (9/4)ϑ²`
  set Mc := Mmag R m b μ₀ lam Nh with hMcd
  set g := (t Nh).1 with hgd
  set F := max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 with hFd
  set v := varthJ R m b μ₀ Nh with hvd
  have hv : 0 ≤ v := Real.rpow_nonneg (div_pos hb hg0).le _
  have hMag := magAt_ofD R M.magD hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hMl := hMag lam M.Kp hKp hl Nh le_rfl
  have hMl' : ‖Mc - ((v : ℝ) : ℂ)‖ ≤ F * v * g :=
    hMl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
      hg0.le)
  have hFg : F * g ≤ 1 / 2 := hsmall Nh le_rfl
  have hMc : ‖Mc‖ ≤ 3 / 2 * v := by
    have h1 : ‖Mc‖ ≤ ‖Mc - ((v : ℝ) : ℂ)‖ + ‖((v : ℝ) : ℂ)‖ := norm_le_norm_sub_add _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hv] at h1
    have h2 : F * v * g ≤ 1 / 2 * v := by
      have e : F * v * g = F * g * v := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hFg hv
    linarith
  have hMc2 : ‖Mc‖ ^ 2 ≤ 9 / 4 * v ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hMc 2
    calc ‖Mc‖ ^ 2 ≤ (3 / 2 * v) ^ 2 := this
      _ = 9 / 4 * v ^ 2 := by ring
  -- the constants
  have hcJ : 0 ≤ cJab L r₀ := by
    unfold cJab
    have hL2' : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2' (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2' ?_
      linarith only [h4, h3, hcS', hQ1]
    have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
    positivity
  have hcu := pairUnitC_nonneg M
  have hTF := M.topF'_nonneg
  have hTC := M.topCL_nonneg
  set cS := cVo + cWo + 8 * cKo + 1 with hcSd
  have hK0 : 0 ≤ 8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * pairUnitC M *
      (2 * (1 + M.topF' + M.topCL)) := by
    have : 0 ≤ cS := by rw [hcSd]; linarith
    positivity
  have hq : 0 ≤ 8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * pairUnitC M *
      (2 * (1 + M.topF' + M.topCL)) * (σ / ‖hBeta R m b μ₀ x Nh‖) :=
    mul_nonneg hK0 (div_nonneg hσ.le (norm_nonneg _))
  have hγ0 : 0 ≤ γδ := (norm_nonneg _).trans hu
  have hU : ‖rpTopU o‖ ≤ γδ := by unfold rpTopU; rw [norm_neg]; exact hu
  refine hout.trans ?_
  have a1 : ‖rpTopU o‖ * ‖uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      γδ * ‖uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)‖ :=
    mul_le_mul_of_nonneg_right hU (norm_nonneg _)
  have a2 : 8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * pairUnitC M * (2 * (1 + M.topF' + M.topCL)) *
      (σ / ‖hBeta R m b μ₀ x Nh‖) * ‖Mc‖ ^ 2 * g ≤
      8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * pairUnitC M * (2 * (1 + M.topF' + M.topCL)) *
      (σ / ‖hBeta R m b μ₀ x Nh‖) * (9 / 4 * v ^ 2) * g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMc2 hq) hg0.le
  have e2 : 8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * pairUnitC M * (2 * (1 + M.topF' + M.topCL)) *
      (σ / ‖hBeta R m b μ₀ x Nh‖) * (9 / 4 * v ^ 2) * g =
      M.rpcKZ r₀ cS * (σ / ‖hBeta R m b μ₀ x Nh‖) * v ^ 2 * g := by
    unfold rpcKZ; ring
  exact le_trans (add_le_add (add_le_add a1 le_rfl) a2) (le_of_eq (congrArg (fun z => _ + z) e2))


set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
/-- **The two-point output of a general state at `j_x ≤ N_h`** with the reduced chain bounded by
the crude chain (`rpc_chain_sizesD`): inputs the seed `k₀` of `rpcRed o` in `wM(2s_{N_h}²σ, M_b)`,
the target `m̄` and the per-block masses `ρ_n` of the reduced chain. -/
theorem rpc_out_trajC : ∃ C₁w C₁t : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧
    ∀ {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
        9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2)
    (hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ)
    (hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
      ≤ 1 / 2)
    (hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    -- the general state at `j_x`
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hlo : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o)
    (hso : PtCorr2.ObsSymInv (Obs.coal L (0 : Lam 2 L N) x) o)
    {σ Mb k₀ mbar γδ : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb)
    (hMbM : Mb ≤ pairUnitC M *
      ‖Mmag R m b (b - m) (lamHat2 R (ptsX x) (zV b) m b (b - m)) Nh‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
    (hk₀ : 0 ≤ k₀)
    (hK0 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
            σ) Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((rpcRed R m b (b - m) x o).K X) ≤ ENNReal.ofReal k₀)
    (hmbar : 0 < mbar) (h8 : 8 * k₀ ≤ vck C₁w * ((4 * C₁w + 1) * mbar))
    (h8' : 8 * k₀ ≤ vck C₁t * ((4 * C₁t + 1) * mbar)) (ρ : ℕ → ℝ)
    (hρ : ∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 →
      ∀ c ∈ blockIdx (L := L) (N := N) n,
      ‖LocObs.mass2 ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (rpcRed R m b (b - m) x o) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V c :
          SA .two (Lam 2 L N)).ab‖ ≤ ρ n)
    (hρm : ∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 →
      (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ * Mb)⁻¹ *
        (ρ n * (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) *
          histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))) ≤ mbar / 2)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (mbar + (4 * C₁t + 1) * M.core.c * mbar + 8 * ((4 * C₁t + 1) * mbar) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * ‖uB R m b (b - m) x (Obs.coal L (0 : Lam 2 L N) x)‖ +
        ‖PtCorr2.nAB (zCstR R Nh m b (b - m) (fun _ => rpcRed R m b (b - m) x o) x)‖ +
        M.rpcKZ r₀ (mbar + (4 * C₁t + 1) * M.core.c * mbar + 8 * ((4 * C₁t + 1) * mbar) + 1) *
          (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ∧
    ‖lastDefR R Nh m b (b - m) (fun _ => rpcRed R m b (b - m) x o) x‖ ≤
      cLab L * (mbar + (4 * C₁t + 1) * M.core.c * mbar + 8 * ((4 * C₁t + 1) * mbar) + 1) *
        (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ * Mb) := by
  obtain ⟨C₁w, C₁t, hC₁w, hC₁t, hCH⟩ := rpc_chain_sizesD M
  refine ⟨C₁w, C₁t, hC₁w, hC₁t, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso σ Mb k₀ mbar γδ hσ hMb hMbM hk₀ hK0 hmbar h8 h8' ρ
    hρ hρm hmAB hu
  have hN2 : 2 ≤ N := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) with htd
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD
  have hρ0 : 0 ≤ (R.withMsq m).ρ := (hRI 0 (Nat.zero_le _)).1.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := ((hRI 0 (Nat.zero_le _)).1).2.2.2.2.1
  have hsN : 0 < histS (R.withMsq m) Nh t := histS_pos' (R.withMsq m) hρ0 hρ8 t Nh
  have hMa : 0 < 2 * histS (R.withMsq m) Nh t ^ 2 * σ := by positivity
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := Hap.hcmu; have := Hap.hC₂; positivity
  obtain ⟨hVt, hWt, hKt⟩ := hCH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD x hx h1 hj o
    ho hlo hso _ Mb hMa hMb k₀ hk₀ hK0 mbar hmbar h8 h8' ρ hρ
    (fun n hn1 hn2 => by
      have := hρm n hn1 hn2
      rwa [show 2 * histS (R.withMsq m) Nh t ^ 2 * σ * Mb =
        2 * histS (R.withMsq m) Nh t ^ 2 * σ * Mb from rfl] at this)
  have hcW : 0 ≤ (4 * C₁t + 1) * M.core.c * mbar := by positivity
  have hcK : 0 ≤ (4 * C₁t + 1) * mbar := by positivity
  exact M.rpc_out_traj_sz R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hσ hMb hmbar.le hcW hcK hMbM
    (fun c hc => hVt (Nh + 1) (by omega) le_rfl c hc)
    (fun c hc => (hWt c hc).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring))))
    (fun U hU => hKt U hU) hmAB hu

end MasterFacts

end

end Spin2
