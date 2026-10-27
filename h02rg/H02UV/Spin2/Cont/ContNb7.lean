import Spin2.Cont.ContNb6
import Spin2.Cont.ContArt1

set_option autoImplicit false

/-!
# `n_a(lastOF_{N_h+1})` of the restarted datum from the restart data at `ms` (any `y`)

**`MasterFacts.nb_naMid`**: `nb_naStep` with its inputs discharged from the restart data at `ms`
(`restartDT_lin`): the `a`-sizes at `N_h` in `nbWa(2s_{N_h}²σ)`, `σ = ctSig`, from
`art_aSizesD` (decayed transients `(7/30)^{N_h−ms}`, `(56/75)^{N_h−ms}`), and the share data
`aN = 8/7`, `bD = 2σ`, `e = (c_δr²(8/7) + 1/24)σ` from `ct_restartTop` (`rptfVT = ctVT`). No
coalescence condition on `y` and no `b`/`ab` sizes:

  `|n_a(lastOF_{N_h+1}(δ_{N_h+1}))| ≤ K_A^{na}(ctVT r, w_T, k_{xT})·(σ/|β_{a,N_h}|)·(3/2)ϑ_{N_h}`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`n_a(lastOF_{N_h+1})` from the restart data at `ms`, any `y`.** -/
theorem nb_naMid {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    (y : Lam 2 L N) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    -- the restart datum at `ms ≤ N_h`
    {ms : ℕ} (hms0 : 0 < ms) (hms : ms ≤ Nh) (δ : Obs2.ObsSt .two L N) (hδ : δ.IsObs)
    (hδl : ObsLocInv (ptsX y) ms δ) (hδs : ObsSymInv ms δ)
    (hδf : ∀ q, Obs2.Loc2Form (ptsX y).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      mass2 (δ.V q : SA .two (Lam 2 L N)).a • pbp (ptsX y).a)
    -- the restart data at `ms` (those of `MasterCore.restartDT_lin`)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖Obs2.betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms)‖ +
        Obs2.shareDev2 (ptsX y).a ms (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms w)
    (hKR : KbHF (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms k)
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
    ‖PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX y) (Nh + 1)
        (obsHistFrom (R.withMsq m) (ptsX y) ms δ (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))‖ ≤
      M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ *
        ((ctSig R m b Nh y ms δ M₀) / ‖hBeta R m b (b - m) y Nh‖) * (3 / 2 * varthJ R m b (b - m) Nh) := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hsN := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh
  have hsms := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms
  obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hc2 : 2 ≤ M.core.c := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hε0 : 0 ≤ M.core.ε := by have := H.hε; linarith
  have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  have hcδ : 0 ≤ M.core.cδ := M.core.consts_nonneg.2.2.2.2.2.2.2.1
  have hg0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := (hD Nh le_rfl).1.le
  have hG0 : 0 ≤ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) := by positivity
  -- the `a`-sector (restart envelope) at `N_h`, decayed transients
  obtain ⟨hAV, hAW, hAK, henv⟩ := M.core.art_aSizesD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b
    (b - m) hD (ptsX y) (zV0 b) ms δ hms0 hms hδ hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg
    hMR (Nh - ms) le_rfl
  have e : ms + (Nh - ms) = Nh := by omega
  rw [e] at hAV hAW hAK
  have hσ : 0 < (ctSig R m b Nh y ms δ M₀) := henv
  set Ma := 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh y ms δ M₀) with hMad
  have hMa : 0 < Ma := by positivity
  have hcan : ∀ c : ℝ, 0 ≤ c → ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal (c * Ma) = ENNReal.ofReal c := by
    intro c hc
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le)]
    congr 1; field_simp
  -- the share data at `N_h`
  obtain ⟨hbD, hE, hn7⟩ := M.ct_restartTop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD
    (ptsX y) ms δ hms0 hms hδ hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg hMR
  have hbDN := hbD (Nh - ms) le_rfl
  rw [e] at hbDN
  have haN : ‖1 - Obs2.frakN2F (ptsX y) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh‖ ≤ 8 / 7 := by
    have h := norm_sub_le (1 : ℂ) (Obs2.frakN2F (ptsX y) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh)
    rw [norm_one] at h
    linarith
  have he : Obs2.shareErrL1_2F (ptsX y) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histWF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histKF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh ≤
      (M.core.cδ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * (8 / 7) + 1 / 24) * (ctSig R m b Nh y ms δ M₀) := by
    refine hE.trans (mul_le_mul_of_nonneg_right ?_ hσ.le)
    have h1 : M.core.cδ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 *
        ‖1 - Obs2.frakN2F (ptsX y) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh‖ ≤
        M.core.cδ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * (8 / 7) :=
      mul_le_mul_of_nonneg_left haN (by positivity)
    have h2 : (3 / 4 : ℝ) ^ (Nh - ms) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hbD' : ‖Obs2.betaTot2 (L := L) (N := N) Nh
        (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)‖ +
      Obs2.shareDev2 (ptsX y).a Nh
        (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) ≤ 2 * (ctSig R m b Nh y ms δ M₀) := hbDN
  have hmm0 : 0 < mm := by linarith
  have hk₁0 : 0 ≤ k₁ := by
    have : 0 ≤ (56 / 75 : ℝ) ^ (Nh - ms) * ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) := by positivity
    have : 0 ≤ 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 := by positivity
    linarith
  -- the `a`-sizes at `N_h` in `nbWa M_a`
  have hVo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (nbWa Ma) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX y) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q) ≤ ENNReal.ofReal mm := by
    intro q hq
    rw [nb_oTo_wa]
    have h : Tj 2 (L : ℝ) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        (((obsHistFrom (R.withMsq m) (ptsX y) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q : Obs.OE .two (Lam 2 L N)) :
          Obs.SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal (1 * Ma) := by rw [one_mul]; exact hAV q hq
    refine (mul_le_mul_right h _).trans ?_
    rw [hcan 1 zero_le_one]
    exact ENNReal.ofReal_le_ofReal hmm1
  have hWo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (nbWa Ma) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX y) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).W q) ≤ ENNReal.ofReal ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * mm) := by
    intro q hq
    rw [nb_oTo_wa]
    refine (mul_le_mul_right (hAW q hq) _).trans (le_trans (le_of_eq (hcan _ (by positivity))) ?_)
    exact ENNReal.ofReal_le_ofReal hmmW
  have hK1 : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
      Obs2.oTo (nbWa Ma) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX y) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X) ≤ ENNReal.ofReal k₁ := by
    intro X hX
    rw [nb_oTo_wa, mul_left_comm]
    refine (mul_le_mul_right (hAK X hX) _).trans (le_trans (le_of_eq (hcan _ (by positivity))) ?_)
    exact ENNReal.ofReal_le_ofReal hk1
  have key := M.nb_naStep R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall y h1 hms δ hδ hδl hδs hδf hδp hσ hmm0 hc₁ hrm hk₁ hk₁0 hkt hVo hWo hK1
    haN hbD' he (by rw [M.ctVT_eq _ hσ]; exact hmAa)
  rw [M.ctVT_eq _ hσ] at key
  exact key

end MasterFacts

end

end Spin2
