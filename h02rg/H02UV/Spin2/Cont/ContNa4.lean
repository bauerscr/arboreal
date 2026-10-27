import Spin2.Cont.ContNa2
import Spin2.Restart.RestartPairTop2

set_option autoImplicit false

/-!
# The top output of a general state with the accumulated `a`-constant given by `n_a(lastOF)`

**`MasterFacts.na_top_traj`**: `MasterFacts.rp_top_traj` with the input `|ε(u^{obs}_a)| ≤ γ_δ`
replaced by the identity `ε(u^{obs}_a) = n_a(lastOF_{N_h+1}(o))` (hypothesis `hid`; it holds at
`h = 0` for the restarted pair-difference datum, `na_rpTopU_eq`) and the window `hmAa` of
`na_lastA_le` (`c_S = v_T + w_T + 8k_{xT} + 1`). Then `γ_δ = K_A^{na}·(σ/|β_{a,N_h}|)·(3/2)ϑ_{N_h}`
(`na_lastA_le`, the reference one-point items as in `rp_top_traj`, the reference zero mode from
`pairTop_E` with `r = 0`), and

  `|rpTopOut o| ≤ (3/2)(1 + K_O)·K_A^{na}(σ/|β_{a,N_h}|)(3/2)ϑ_{N_h}·ϑ_{N_h}
     + (9/4)K_E'·(σ/|β_{a,N_h}|)·ϑ_{N_h}²·ǧ_{N_h}`,

both terms linear in the `a`-size `σ` of `o` (no initial `ε(δ.u_a)`, no chain).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- `K_A^{na}`: the constant of `na_lastA_le` with the master `c_u` and `K₄`. -/
def naKA (cV cW cK r₀ : ℝ) : ℝ :=
  cLab L * (cV + cW + 8 * cK + 1) * pairUnitC M +
    8 * (1 / 2 + 81 / 32 * cJab L r₀ * (cV + cW + 8 * cK + 1)) * (2 * (1 + M.topF' + M.topCL))

set_option maxHeartbeats 8000000 in
/-- **`rp_top_traj` with `γ_δ` from the `h = 0` identity** (`ε(u_a) = n_a(lastOF)`). -/
theorem na_top_traj {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {cK0 Kt : ℝ} (hseed : TopSeedAt R Nh m b (b - m) cK0)
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
    (hvb : cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) +
      8 * M.core.ℓ ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hwb : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2) ≤ 1)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (x : Lam 2 L N) (hx : x ≠ 0) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    -- the general state at `N_h + 1`
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs) (hlo : PtCorr2.ObsLocInv (ptsX x) (Nh + 1) o)
    {σ vT wT kxT k2 : ℝ} (hσ : 0 < σ) (hvT : 0 ≤ vT) (hwT : 0 ≤ wT) (hkxT : 0 ≤ kxT)
    (hk2 : 0 ≤ k2)
    (hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        (o.V q) ≤ ENNReal.ofReal vT)
    (hWt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        (o.W q) ≤ ENNReal.ofReal wT)
    (hKt : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM1 (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        (o.K X) ≤ ENNReal.ofReal kxT)
    (hK2 : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.K X : Obs.SA .two (Lam 2 L N)).ab) ≤
        ENNReal.ofReal k2)
    (hsmT : M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
      kxT + k2) ≤ 1)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (8 * (2 * rpIota vT wT * M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m *
        (L : ℝ) ^ (2 * N) ≤ 1)
    (hid : ε ((o.u : Obs.SA .two (Lam 2 L N)).a) =
      PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX x) (Nh + 1) o Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))))
    (hmAa : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (vT + wT + 8 * kxT + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖rpTopOut R Nh m b (b - m) x o‖ ≤
      3 / 2 * (1 + M.fwKO) * (M.naKA vT wT kxT r₀ * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          (3 / 2 * varthJ R m b (b - m) Nh)) * varthJ R m b (b - m) Nh +
        9 / 4 * M.rpKE ((2 * rpIota vT wT * M.core.A) ^ (L ^ 2)) r₀ *
          (σ / ‖hBeta R m b (b - m) x Nh‖) * varthJ R m b (b - m) Nh ^ 2 *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
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
  obtain ⟨-, hB, hgam⟩ := M.oneTopD R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD lam hKp hl hsmall x
  -- the one-point items of the last step at `x` (reference)
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
  -- the weights (reference)
  obtain ⟨hMa, hMb, -⟩ := hseed x hx hj
  set Mb := pM (R.withMsq m) (ptsS x) (zV0 b) t Nh with hMbd
  have hMaM := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam M.Kp hKp hl
    hsmall (ptsX x) hNh1 le_rfl le_rfl
  have hMbM := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam M.Kp hKp hl
    hsmall (ptsS x) hNh1 le_rfl le_rfl
  have hMa2 : pM (R.withMsq m) (ptsX x) (zV0 b) t Nh =
      2 * histS (R.withMsq m) Nh t ^ 2 * ‖hBeta R m b μ₀ x Nh‖ := by
    rw [hBeta_eq_zV0 R m b μ₀ x hNh1]; rfl
  have hβ0 : hBeta R m b μ₀ x Nh ≠ 0 := by
    intro h0; rw [hMa2, h0, norm_zero, mul_zero] at hMa; exact lt_irrefl _ hMa
  have hMa0 : 2 * histS (R.withMsq m) Nh t ^ 2 * ‖hBeta R m b μ₀ x Nh‖ ≤
      pairUnitC M * ‖Mmag R m b μ₀ lam Nh‖ * (t Nh).1 := by rw [← hMa2]; exact hMaM
  have hCN := lC_diag R hval hvalL hVN b μ₀ x
  have hmA' : 8 * cKAL L R.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m *
      (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmA
  -- the reference zero mode (`r = 0`)
  obtain ⟨p, r, -, -, -, hr, -, hΩ0, -, -, hnA, -⟩ :=
    pairTop_E R hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hL8 hb (le_of_eq hh0) (dxTop Nh) x
      (dCov_dxTop Nh x) hj
  have hr0 : (r : ℂ) = 0 := by
    rw [← hr, PtCorr2.onept_avg0_h0 hb hm.1 hh0, mul_one_div_cancel
      (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]
  rw [hr0, zero_sub] at hnA
  -- `n_a` of the last factor of `o`
  have hmAa' : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (vT + wT + 8 * kxT + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmAa
  have hA := na_lastA_le R hNh hm.1 hm.2 hρ1 hspl' hval hvalL hVN hLp hL8
    (by rw [hRA]; exact M.core.hA2) hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1 hs1' hs2' hs3'
    hs4' hs5' lam x o ho hlo hσ hMb hvT hwT hkxT (pairUnitC_nonneg M) hVt hWt hKt hMa0 htop hβ0
    hone1 hone2 hgam hΩ0 hnA hK hmT hmA' hmAa'
  -- `|M_{N_h}| ≤ (3/2)ϑ_{N_h}`
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
  have hKA0 : 0 ≤ M.naKA vT wT kxT r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) := by
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
    unfold naKA
    positivity
  have hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤
      M.naKA vT wT kxT r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) * (3 / 2 * v) := by
    rw [hid]
    exact hA.trans (mul_le_mul_of_nonneg_left hMc hKA0)
  exact M.rp_top_traj R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hvb hwb hsmall x hx hj o ho hlo hσ hvT hwT hkxT hk2 hVt hWt hKt hK2 hsmT hmAB hu

end MasterFacts

end

end Spin2
