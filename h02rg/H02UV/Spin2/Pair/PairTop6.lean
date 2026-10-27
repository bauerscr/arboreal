import Spin2.Pair.PairTop5

/-!
# Top coalescence along one windowed `h = 0` trajectory, from the seed sizes at `N - 1`

**`MasterFacts.fw_top_traj`**: on the `h = 0` trajectory `(b, b − m²)` in `D_ε` up to `N_h`
(`N ≥ 3`), for `x ≠ 0` with `j_x ≥ N_h + 1`: from the seed size of the reduced state at `N_h + 1`
(`TopSeedAt c_K`: `A^{(|𝓑(X)|-4)_+}‖K'_{N_h+1}(X)‖_{wM(M_a,M_b)} ≤ c_K`, `M_a = 2s_{N_h}²|β_{a,N_h}|`,
`M_b` its mirror), the last-step smallness and the mass windows,

  `|P_{1/b}[0 ↔ x] − ϑ_{N_h}²| ≤ K_top ϑ_{N_h}²/β_{N_h}`, `K_top = fwKT c_K r₀`.

Chain: `oneTopD` (`A = γ_{0,N−1}`, `B = γ_{x,N−1}` close to `M_{N_h}`, `|γ_{a,N}| ≤ K₄M`),
`lastOneRem_x` + `lastKRem_x` (one-point items of the last step), `pM_le_mag_MFD` (weights),
`pairTop_E_le` (`|E| ≤ K_EM²ǧ`), `twoPt_top_pure`, `top_conv`, `thetaSq_eq_varth`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

/-- **The seed sizes at `N_h + 1`** for the `h = 0` trajectory at `(b, μ₀)` (named here, discharged
in `Spin2/Pair/PairTopSeed*`): for `x ≠ 0` with `j_x ≥ N_h + 1`, `M_a, M_b > 0` and
`A^{(|𝓑(X)|-4)_+}‖K'_{N_h+1}(X)‖_{wM(M_a,M_b)} ≤ c_K` for the reduced state `oTop … dxTop`. -/
def TopSeedAt {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (Nh : ℕ) (m b μ₀ cK : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
    0 < pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh ∧
    0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh ∧
    ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM (pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh))
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oTop R Nh m b μ₀ (dxTop Nh) x).K X) ≤ ENNReal.ofReal cK

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- `K_O = 2(F' + F) + c_L` (the one-point constant at `N − 1`). -/
def fwKO : ℝ :=
  2 * (M.topF' + max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0) + M.topCL

/-- `K_E` (the pair part at the top). -/
def fwKEt (cK r₀ : ℝ) : ℝ :=
  cLab L * (8 * cK + 1) * pairUnitC M ^ 2 +
    4 * (pairUnitC M + 81 / 16 * cJab L r₀ * (8 * cK + 1) * pairUnitC M) *
      (2 * (1 + M.topF' + M.topCL))

/-- The final constant of the top bound. -/
def fwKT (cK r₀ : ℝ) : ℝ :=
  9 / 4 * ((2 * M.fwKO + M.fwKO ^ 2) + M.fwKEt cK r₀) +
    5 / 2 * max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0

set_option maxHeartbeats 8000000 in
/-- **`thm:multiscale` at `h = 0` for `j_x ≥ N_h + 1`, one trajectory.** -/
theorem fw_top_traj {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {cK Kt : ℝ} (hcK : 0 ≤ cK) (hseed : TopSeedAt R Nh m b (b - m) cK)
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * cK + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
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
    (x : Lam 2 L N) (hx : x ≠ 0) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x) :
    |Pconn L N (1 / b) x - thetaSq R m b (b - m) Nh| ≤
      M.fwKT cK r₀ * thetaSq R m b (b - m) Nh / betaJ R m b (b - m) Nh := by
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
  -- the one-point parts at `N − 1` and `γ_{a,N}`
  set lam := lamHat2 R (ptsX x) (zV b) m b μ₀ with hlamd
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX x)
  obtain ⟨hA, hB, hgam⟩ := M.oneTopD R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD lam hKp hl hsmall x
  -- the one-point items of the last step at `x`
  have hNh0 : 0 < Nh := by omega
  have hWx := M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hNh0
  have hKx := M.lastKD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hNh0
  have htop := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)).1
  have hl1 := M.lastL1D N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)
    (htop.1.trans (by norm_num))
  have hx1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x := by omega
  have hKR := lastKRem_x R hNh hval hvalL hVN hLp hL8 hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1
    hs1' hs2' hs3' hs4' hs5' x hx1 hWx hKx htop hl1
  have hsmA' : (M.core.Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) + 9 / 4 * (cBn * Q1 2 * M.core.cWL) +
      cKAL L R.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (t Nh).1 ≤ 1 / 2 := by
    rw [hRℓ]; exact hsmA
  obtain ⟨hP0, hone1, hone2⟩ := lastOneRem_x R hNh hval hvalL hVN hLp hL8 hG hcWL hg0.le x hWx
    htop hsmA' hKR
  rw [hP0, mul_one, norm_one, mul_one] at hone1
  rw [hP0, norm_one, mul_one] at hone2
  -- the weights
  obtain ⟨hMa, hMb, hKo⟩ := hseed x hx hj
  set Ma := pM (R.withMsq m) (ptsX x) (zV0 b) t Nh with hMad
  set Mb := pM (R.withMsq m) (ptsS x) (zV0 b) t Nh with hMbd
  have hMaM := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam M.Kp hKp hl
    hsmall (ptsX x) hNh1 le_rfl le_rfl
  have hMbM := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam M.Kp hKp hl
    hsmall (ptsS x) hNh1 le_rfl le_rfl
  have hMa2 : Ma = 2 * histS (R.withMsq m) Nh t ^ 2 * ‖hBeta R m b μ₀ x Nh‖ := by
    rw [hBeta_eq_zV0 R m b μ₀ x hNh1]; rfl
  have hβ0 : hBeta R m b μ₀ x Nh ≠ 0 := by
    intro h0; rw [hMa2, h0, norm_zero, mul_zero] at hMa; exact lt_irrefl _ hMa
  have hCN := lC_diag R hval hvalL hVN b μ₀ x
  have hmA' : 8 * cKAL L R.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m *
      (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmA
  have hmAB' : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * cK + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmAB
  -- the pair part
  obtain ⟨E, hE, hEb⟩ := pairTop_E_le R hNh hm.1 hm.2 hρ1 hspl' hb hh0 hval hvalL hVN hLp hL8
    (by rw [hRA]; exact M.core.hA2) hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1 hs1' hs2' hs3'
    hs4' hs5' lam x hj hMa hMb hcK (pairUnitC_nonneg M) hKo (le_of_eq hMa2) hMaM hMbM htop hβ0
    hone1 hone2 hgam hCN hK hmT hmA' hmAB'
  -- assembly
  set Mc := Mmag R m b μ₀ lam Nh with hMcd
  set g := (t Nh).1 with hgd
  set F := max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 with hFd
  have hKO0 : 0 ≤ M.fwKO := by
    unfold fwKO
    have := M.topF'_nonneg; have := M.topCL_nonneg; have : 0 ≤ F := le_max_right _ _
    positivity
  have hsq := twoPt_top_pure hKO0 hg0.le hg1 hA hB
  have hPc : ((Pconn L N (1 / b) x : ℝ) : ℂ) =
      uA R m b μ₀ x (Nh + 1) * uB R m b μ₀ x (Nh + 1) - E := by
    rw [Pconn_eq_avg0 hb hm.1 hh0 x, hE]
  have hPM : ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - Mc ^ 2‖ ≤
      ((2 * M.fwKO + M.fwKO ^ 2) + M.fwKEt cK r₀) * ‖Mc‖ ^ 2 * g := by
    rw [hPc]
    have e : uA R m b μ₀ x (Nh + 1) * uB R m b μ₀ x (Nh + 1) - E - Mc ^ 2 =
        (uA R m b μ₀ x (Nh + 1) * uB R m b μ₀ x (Nh + 1) - Mc ^ 2) - E := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have hE' : ‖E‖ ≤ M.fwKEt cK r₀ * ‖Mc‖ ^ 2 * g := hEb
    calc _ ≤ (2 * M.fwKO + M.fwKO ^ 2) * ‖Mc‖ ^ 2 * g + M.fwKEt cK r₀ * ‖Mc‖ ^ 2 * g :=
          add_le_add hsq hE'
      _ = _ := by ring
  have hMag := magAt_ofD R M.magD hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hMl := hMag lam M.Kp hKp hl Nh le_rfl
  have hv : 0 ≤ varthJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hb hg0).le _
  have hMl' : ‖Mc - ((varthJ R m b μ₀ Nh : ℝ) : ℂ)‖ ≤ F * varthJ R m b μ₀ Nh * g :=
    hMl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
      hg0.le)
  have hKP0 : 0 ≤ (2 * M.fwKO + M.fwKO ^ 2) + M.fwKEt cK r₀ := by
    have h1 : 0 ≤ M.fwKEt cK r₀ := by
      unfold fwKEt
      have hcu := pairUnitC_nonneg M
      have hcL : 0 ≤ cLab L := by
        unfold cLab
        have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
        positivity
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
      have := M.topF'_nonneg; have := M.topCL_nonneg
      positivity
    positivity
  have hconv := top_conv hv hg0.le hKP0 (le_max_right _ _) (hsmall Nh le_rfl) hMl' hPM
  obtain ⟨hθ1, hθ2⟩ := thetaSq_eq_varth R hb (k := Nh) (m := m) (μ₀ := μ₀) hg0
  rw [mul_div_assoc, hθ2, hθ1]
  refine hconv.trans (le_of_eq ?_)
  have eg : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 = g := rfl
  rw [eg]
  unfold fwKT
  ring

end MasterFacts

end

end Spin2
