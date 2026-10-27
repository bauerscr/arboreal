import Spin2.Cont.ContNa3
import Spin2.Cont.ContNb5
import Spin2.Cont.ContNb7

set_option autoImplicit false

/-!
# The accumulated `a`-constant at `j_y ≤ N_h` of the pair-difference datum, without `ε(δ.u_a)`

**`MasterFacts.nb_eps_jy`** (`δ = pl2Delta`, restart data at `ms`, `ms < j_y ≤ N_h`, `h = 0`):

  `|ε(u^δ_{j_y,a})| ≤ K_A^{na}(ctVT r, w_T, k_{xT})·(σ/|β_{a,N_h}|)·(3/2)ϑ_{N_h} + nbGB`.

Proof: backward chain `nb_gam_back_top` from `N_h + 1`; at `N_h + 1` the `h = 0` identity
`ε(u^δ_{N_h+1,a}) = n_a(lastOF_{N_h+1}(δ_{N_h+1}))` (`na_rpTopU_eq`, any `y`) and `nb_naMid`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`ε(u^δ_{j_y,a})` without the initial `ε(δ.u_a)`** (`h = 0` identity plus backward chain). -/
theorem nb_eps_jy {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    (hspl : SplitSmall R.P L R.ρ) (x y : Lam 2 L N) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    -- the restart datum at `ms ≤ N_h`
    {ms : ℕ} (hms0 : 0 < ms) (hms : ms ≤ Nh)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh) (hδ : (pl2Delta R m b (b - m) x y ms).IsObs)
    (hδl : ObsLocInv (ptsX y) ms (pl2Delta R m b (b - m) x y ms)) (hδs : ObsSymInv ms (pl2Delta R m b (b - m) x y ms))
    (hδf : ∀ q, Obs2.Loc2Form (ptsX y).a ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a =
      mass2 ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a • pbp (ptsX y).a)
    -- the restart data at `ms` (those of `MasterCore.restartDT_lin`)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖Obs2.betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms)‖ +
        Obs2.shareDev2 (ptsX y).a ms (histVF2 (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms w)
    (hKR : KbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) *
      2) ≤ 1 / 1344)
    (hMR : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)
    -- the `a`-size constants at `N_h` (decayed transients)
    {mm k₁ c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hmm1 : 1 ≤ mm)
    (hmmW : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) +
        (7 / 30) ^ (Nh - ms) * (w / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) ≤ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * mm)
    (hrm : (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ mm)
    (hk1 : (56 / 75) ^ (Nh - ms) * ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) +
        8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 ≤ k₁)
    (hk₁ : k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm)
    (hkt : 8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀)
    -- the window of `na_lastA_le`
    (hmAa : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm + 8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖ε (((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).u : Obs.SA .two (Lam 2 L N)).a)‖ ≤
      M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ *
          (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) M₀ / ‖hBeta R m b (b - m) y Nh‖) *
          (3 / 2 * varthJ R m b (b - m) Nh) +
        M.nbGB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) M₀ k w (Obs.coal L (0 : Lam 2 L N) y) := by
  -- the backward chain from `N_h + 1` down to `j_y`
  have hback := M.nb_gam_back_top R hP hi0 hRℓ hRA hRρ (by omega) hNh hm hD (ptsX y)
    (obsInit .two (zV b) (ptsX y)) (obsInit_isObs .two (zV b) (ptsX y)) hms0 hms _ hδ hδl
    hδs hδf hδp hM0 hk hw hbR hWR hKR hg hMR hmy hj
  -- the `h = 0` identity at `N_h + 1`
  have hF := M.flow
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL (R.withMsq m) Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := hF
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL7 : 7 ≤ L := by have := M.core.hL49; omega
  have hU := na_rpTopU_eq R hNh m hρ1 hspl hm.1 hm.2 hval hvalL hL7 (μ₀ := b - m) hb
    (sub_add_cancel b m).symm x y ms hblk hms
  have hidA : ε (((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).u :
        Obs.SA .two (Lam 2 L N)).a) =
      PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX y) (Nh + 1)
        (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) := by
    unfold rpTopU at hU; exact neg_inj.1 hU
  have hna := M.nb_naMid R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall y h1 hms0 hms _ hδ hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg hMR
    hc₁ hmm1 hmmW hrm hk1 hk₁ hkt hmAa
  have e1 : ‖ε (((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).u : Obs.SA .two (Lam 2 L N)).a)‖ =
      ‖gamF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) (Obs.coal L (0 : Lam 2 L N) y)‖ := by
    unfold gamF cw2O; rw [norm_neg]
  have e2 : ‖gamF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) (Nh + 1)‖ =
      ‖PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX y) (Nh + 1)
        (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))‖ := by
    unfold gamF; rw [norm_neg, hidA]
  rw [e1]
  refine hback.trans (add_le_add (le_of_eq e2 |>.trans hna) le_rfl)

end MasterFacts

end

end Spin2
