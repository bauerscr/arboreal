import Spin2.Restart.RestartPairTop1
import Spin2.Restart.RestartPairSeed
import Spin2.Pair.PairTop6

/-!
# T5 (pair/top restart): the bilinear output bound along a windowed `h = 0` trajectory

**`MasterFacts.rp_top_traj`**: on the `h = 0` trajectory `(b, b − m²)` in `D_ε` up to `N_h`
(`N ≥ 3`), for `x ≠ 0` with top coalescence `j_x ≥ N_h + 1` and the hypotheses of
`MasterFacts.fw_top_traj` (reference seed `TopSeedAt`, last-step smallness, mass windows), and for
**every** observable state `o` at scale `N_h + 1` (local at `N_h + 1`) with, in the weights
`wM(2s_{N_h}²σ, M_b)` (`M_b` the reference `b`-weight `pM … (ptsS x) … N_h`, `σ > 0` the `a`-side
size of `o` in coupling units),

  `‖V(B)‖ ≤ v_T`, `‖𝒲(B)‖ ≤ w_T`, `A^{(|𝓑(X)|-4)_+}‖K(X)‖_{wM1} ≤ k_{xT}`,
  `A^{(|𝓑(X)|-4)_+}w_{ab}‖K(X)_{ab}‖ ≤ k₂`, `A⁴(C_fǧ³ + k_{xT} + k₂) ≤ 1`,

and accumulated `a`-constant `|ε(u^{obs}_a)| ≤ γ_δ`:

  `|rpTopOut o| ≤ (3/2)(1 + K_O)·γ_δ·ϑ_{N_h} + (9/4)K_E'·(σ/|β_{a,N_h}|)·ϑ_{N_h}²·ǧ_{N_h}`

(`K_E' = rpKE c_K r₀`, `c_K = (2ι A)^{L²}`, `ι = e^{3/2+v_T}(2 + w_T)`). On the reference state
(`rpRef`, `σ = |β_{a,N_h}|`) the output is the two-point function (`rpTopOut_ref`); the bound is
linear in the `a`-side data `(γ_δ, σ)` of `o`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- `K_E'` (the pair part at the top for a general state, per unit `σ/|β|`). -/
def rpKE (cK r₀ : ℝ) : ℝ :=
  cLab L * (8 * cK + 1) * pairUnitC M ^ 2 +
    8 * (1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK + 1)) * pairUnitC M *
      (2 * (1 + M.topF' + M.topCL))

set_option maxHeartbeats 8000000 in
/-- **The two-point output of a general state at `N − 1`, along one trajectory.** -/
theorem rp_top_traj {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    {σ vT wT kxT k2 γδ : ℝ} (hσ : 0 < σ) (hvT : 0 ≤ vT) (hwT : 0 ≤ wT) (hkxT : 0 ≤ kxT)
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
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ) :
    ‖rpTopOut R Nh m b (b - m) x o‖ ≤
      3 / 2 * (1 + M.fwKO) * γδ * varthJ R m b (b - m) Nh +
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
  -- the seed of the general state
  set cKg := (2 * rpIota vT wT * M.core.A) ^ (L ^ 2) with hcKgd
  have hcKg : 0 ≤ cKg := by
    have hA1 : (1 : ℝ) ≤ M.core.A := by have := M.core.hA2; linarith
    have := one_le_rpIota hvT hwT
    exact pow_nonneg (by positivity) _
  have hA1 : 1 ≤ R.A := by rw [hRA]; have := M.core.hA2; linarith
  have hρ0' : 0 ≤ (R.withMsq m).ρ := hvalL.2.2.2.2.1
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := hvalL.2.2.2.2.2.1
  have hseedG := rp_topSeed_gen (R.withMsq m) hNh hval hvalL hVN hmN hL8 hρ0' hρ8' hA1 t hCf0 hG
    hg0.le hs1' hs2'
    (by show cM * R.ℓ ^ 2 * _ + 8 * R.ℓ ^ 4 * _ ≤ 1
        rw [hRℓ]; exact hvb) hwb (ptsX x) o ho (dxTop Nh x) hvT hwT hkxT hk2 hVt
    hWt hKt hK2 (by show R.A ^ 4 * _ ≤ 1
                    rw [hRA]; exact hsmT)
  have hmAB' : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * cKg + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmAB
  have hcKg' : cKg = (2 * rpIota vT wT * R.A) ^ (L ^ 2) := by rw [hcKgd, hRA]
  have hE := rp_topE_le R hNh hm.1 hm.2 hρ1 hspl' hb hh0 hval hvalL hVN hLp hL8
    (by rw [hRA]; exact M.core.hA2) hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1 hs1' hs2' hs3'
    hs4' hs5' lam x hj o ho hlo hσ hMb hcKg (pairUnitC_nonneg M)
    (fun X hX => by rw [hcKg']; exact hseedG X hX) hMa0 hMbM htop hβ0 hone1 hone2 hgam hCN hK
    hmT hmA' hmAB'
  -- assembly
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
  have hKO0 : 0 ≤ M.fwKO := by
    unfold fwKO
    have := M.topF'_nonneg; have := M.topCL_nonneg; have : 0 ≤ F := le_max_right _ _
    positivity
  have huB : ‖uB R m b μ₀ x (Nh + 1)‖ ≤ (1 + M.fwKO) * ‖Mc‖ := by
    have h1 : ‖uB R m b μ₀ x (Nh + 1)‖ ≤ ‖uB R m b μ₀ x (Nh + 1) - Mc‖ + ‖Mc‖ :=
      norm_le_norm_sub_add _ _
    have h2 : ‖uB R m b μ₀ x (Nh + 1) - Mc‖ ≤ M.fwKO * ‖Mc‖ * g := hB
    have h3 : M.fwKO * ‖Mc‖ * g ≤ M.fwKO * ‖Mc‖ :=
      mul_le_of_le_one_right (mul_nonneg hKO0 (norm_nonneg _)) hg1
    linarith
  have hKE0 : 0 ≤ M.rpKE cKg r₀ := by
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
    unfold rpKE
    positivity
  have hE' : ‖rpTopE R Nh m b μ₀ x o‖ ≤
      M.rpKE cKg r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) * ‖Mc‖ ^ 2 * g := by
    unfold rpKE; exact hE
  have hq : 0 ≤ M.rpKE cKg r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) :=
    mul_nonneg hKE0 (div_nonneg hσ.le (norm_nonneg _))
  have hMc2 : ‖Mc‖ ^ 2 ≤ 9 / 4 * v ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hMc 2
    calc ‖Mc‖ ^ 2 ≤ (3 / 2 * v) ^ 2 := this
      _ = 9 / 4 * v ^ 2 := by ring
  have hU : ‖rpTopU o‖ ≤ γδ := by unfold rpTopU; rw [norm_neg]; exact hu
  have hγ0 : 0 ≤ γδ := (norm_nonneg _).trans hu
  have hfin : ‖rpTopOut R Nh m b μ₀ x o‖ ≤
      3 / 2 * (1 + M.fwKO) * γδ * v +
        9 / 4 * M.rpKE cKg r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) * v ^ 2 * g := by
    unfold rpTopOut
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have a1 : ‖rpTopU o‖ * ‖uB R m b μ₀ x (Nh + 1)‖ ≤ γδ * ((1 + M.fwKO) * (3 / 2 * v)) :=
      mul_le_mul hU (huB.trans (mul_le_mul_of_nonneg_left hMc (by linarith)))
        (norm_nonneg _) hγ0
    have a2 : M.rpKE cKg r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) * ‖Mc‖ ^ 2 * g ≤
        M.rpKE cKg r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) * (9 / 4 * v ^ 2) * g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMc2 hq) hg0.le
    have e1 : γδ * ((1 + M.fwKO) * (3 / 2 * v)) = 3 / 2 * (1 + M.fwKO) * γδ * v := by ring
    have e2 : M.rpKE cKg r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) * (9 / 4 * v ^ 2) * g =
        9 / 4 * M.rpKE cKg r₀ * (σ / ‖hBeta R m b μ₀ x Nh‖) * v ^ 2 * g := by ring
    linarith
  exact hfin

end MasterFacts

end

end Spin2
