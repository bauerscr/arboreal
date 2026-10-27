import Spin2.Cont.ContTop4
import Spin2.Cont.ContArt1

set_option autoImplicit false

/-!
# Top coalescence: `ct_T5top` with the decayed transients

**`MasterFacts.art_T5topD`**: `MasterFacts.ct_T5top` (`Spin2/Cont/ContTop4`) with `cw2_aSizes`
replaced by `MasterCore.art_aSizesD`. The size conditions now contain the transients as
`(7/30)^{N_h−ms}·w/(s_{ms}²M₀)` (in `hmmW`) and `(56/75)^{N_h−ms}(k + 120B(cε)w)/(s_{ms}²M₀)` (in `hk1`).
So `mm = O(1)` (`w_T = O(1)`) and `k₁ = O(ǧ_{N_h}²)` are admissible once `N_h − ms ≳ log(1/ǧ)`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

theorem art_cancel (a b p : ℝ) (hp : p ≠ 0) : a * (b * p) / p = a * b := by
  field_simp

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`ct_T5top` with decayed transients** (`art_aSizesD`). -/
theorem art_T5topD {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    -- the restart datum at `0 < ms ≤ N_h` (reference `b`-part)
    {ms : ℕ} (hms0 : 0 < ms) (hms : ms ≤ Nh) (δ : Obs2.ObsSt .two L N) (hδ : δ.IsObs)
    (hδl : ObsLocInv (ptsX x) ms δ) (hδs : ObsSymInv ms δ)
    (hδc : ∀ q, ((obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q :
      SA .two (Lam 2 L N)).ab = 0)
    (hδcN : ∀ q, ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q :
      SA .two (Lam 2 L N)).ab = 0)
    (hδwN : ∀ q, ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).W q :
      SA .two (Lam 2 L N)).ab = 0)
    (hδf : ∀ q, Obs2.Loc2Form (ptsX x).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      mass2 (δ.V q : SA .two (Lam 2 L N)).a • pbp (ptsX x).a)
    (hδb : Obs2.prjSt false δ = Obs2.prjSt false (Obs2.obsHist (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))))
    -- the restart data at `ms` (those of `MasterCore.restartDT_lin`)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖Obs2.betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms)‖ +
        Obs2.shareDev2 (ptsX x).a ms (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms w)
    (hKR : KbHF (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) *
      2) ≤ 1 / 1344)
    (hMR : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)
    -- the size constants at `N_h`
    {mm k₁ c₁ k2 : ℝ} (hc₁ : 0 ≤ c₁) (hk2 : 0 ≤ k2)
    (hmmV : 1 + cw2Thb M Nh Nh ≤ mm)
    (hmmW : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) +
        (7 / 30) ^ (Nh - ms) * (w / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) +
        cw2Thb M Nh Nh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm)
    (hrm : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ mm)
    (hk1 : (56 / 75) ^ (Nh - ms) * ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) +
        8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 +
        cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) ≤ k₁)
    (hk₁ : k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm)
    (hkt : 8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀)
    -- the `ab` part at `N_h + 1` (`rpab_top`)
    (hK2 : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh x ms δ M₀)) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X :
            Obs.SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2)
    -- the smallness conditions of `rp_top_traj`
    (hsmT : M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
      M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
        (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
          M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖rpTopOut R Nh m b (b - m) x
        (obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))‖ ≤
      3 / 2 * (1 + M.fwKO) *
          rptfGam (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))
            (Obs2.obsInit .two (zV b) (ptsX x)) Nh * varthJ R m b (b - m) Nh +
        9 / 4 * M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
          (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
            M.core.A) ^ (L ^ 2)) r₀ *
          ((ctSig R m b Nh x ms δ M₀) / ‖hBeta R m b (b - m) x Nh‖) * varthJ R m b (b - m) Nh ^ 2 *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  have hN2 : 2 ≤ N := by omega
  have hF := M.flow
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
  have hG0 : 0 ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by positivity
  have hΘ : 0 ≤ cw2Thb M Nh Nh := by unfold cw2Thb; positivity
  -- the `a`-sector (restart envelope) and the `b`-sector (reference) at `N_h`
  obtain ⟨hAV, hAW, hAK, henv⟩ := M.core.art_aSizesD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b
    (b - m) hD (ptsX x) (zV0 b) ms δ hms0 hms hδ hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg
    hMR (Nh - ms) le_rfl
  have e : ms + (Nh - ms) = Nh := by omega
  rw [e] at hAV hAW hAK
  obtain ⟨hBV, hBW, hBK⟩ := M.cw3_bSizes N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD x δ
    hδb hms0 hms le_rfl
  have hrat := M.cw2_pMS_ratio N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD x (le_refl Nh)
  replace hrat : 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * ‖bt2 R (ptsS x) (zV0 b) m b (b - m) Nh‖ ≤
      cw2Thb M Nh Nh * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) := by
    refine hrat.trans (le_of_eq ?_); unfold cw2Thb; ring
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hβS := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsS x)
    (zV0 b) rfl hmu (by omega) Nh le_rfl).1
  have hMb : 0 < (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) := by
    unfold pM; exact mul_pos (mul_pos two_pos (pow_pos hsN 2)) hβS
  have hσ : 0 < (ctSig R m b Nh x ms δ M₀) := henv
  have hMa : 0 < (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh x ms δ M₀)) := by positivity
  -- the share data at `N_h`
  obtain ⟨hbD, hE, hn7⟩ := M.ct_restartTop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD
    (ptsX x) ms δ hms0 hms hδ hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg hMR
  have hbDN := hbD (Nh - ms) le_rfl
  rw [e] at hbDN
  have haN : ‖1 - Obs2.frakN2F (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh‖ ≤ 8 / 7 := by
    have h := norm_sub_le (1 : ℂ) (Obs2.frakN2F (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh)
    rw [norm_one] at h
    linarith
  have he : Obs2.shareErrL1_2F (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histWF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histKF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh ≤
      (M.core.cδ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * (8 / 7) + 1 / 24) * (ctSig R m b Nh x ms δ M₀) := by
    refine hE.trans (mul_le_mul_of_nonneg_right ?_ hσ.le)
    have h1 : M.core.cδ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 *
        ‖1 - Obs2.frakN2F (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh‖ ≤
        M.core.cδ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * (8 / 7) :=
      mul_le_mul_of_nonneg_left haN (by positivity)
    have h2 : (3 / 4 : ℝ) ^ (Nh - ms) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hbD' : ‖Obs2.betaTot2 (L := L) (N := N) Nh
        (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)‖ +
      Obs2.shareDev2 (ptsX x).a Nh
        (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) ≤ 2 * (ctSig R m b Nh x ms δ M₀) := hbDN
  have hmm0 : 0 < mm := by linarith
  have hk₁0 : 0 ≤ k₁ := by
    have : 0 ≤ (56 / 75) ^ (Nh - ms) * ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) := by positivity
    have : 0 ≤ 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 := by positivity
    have : 0 ≤ cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) := by
      positivity
    linarith
  -- `V` at `N_h`
  have hVo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh x ms δ M₀)) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q) ≤ ENNReal.ofReal mm := by
    intro q hq
    have hbv : Tj 2 (L : ℝ) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (cw2Thb M Nh Nh * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) :=
      (hBV q hq).trans (ENNReal.ofReal_le_ofReal hrat)
    refine (oTo_wM_le_of_ab hMa hMb Nh _ _ (hδcN q) hMa.le (by positivity) (hAV q hq) hbv).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [div_self hMa.ne', mul_div_assoc, div_self hMb.ne', mul_one]
    exact hmmV
  -- `𝒲` at `N_h`
  have hWo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh x ms δ M₀)) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).W q) ≤
        ENNReal.ofReal (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm) := by
    intro q hq
    have hbw : Tj 2 (L : ℝ) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).W q : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * (cw2Thb M Nh Nh * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))) :=
      (hBW q hq).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hrat (by positivity)))
    have hu0 : 0 ≤ (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) +
        (7 / 30) ^ (Nh - ms) * (w / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀))) * (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh x ms δ M₀)) := by positivity
    refine (oTo_wM_le_of_ab hMa hMb Nh _ _ (hδwN q) hu0 (by positivity) (hAW q hq) hbw).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_cancel_right₀ _ hMa.ne', art_cancel _ _ _ hMb.ne']
    linarith
  -- `K` at `N_h` (one-point weights)
  have hK1 : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
      Obs2.oTo (wM1 (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh x ms δ M₀)) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X) ≤ ENNReal.ofReal k₁ := by
    intro X hX
    have hbk : ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
        Tj 2 (L : ℝ) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 *
          (cw2Thb M Nh Nh * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))) := by
      refine (hBK X hX).trans (ENNReal.ofReal_le_ofReal ?_)
      have := mul_le_mul_of_nonneg_left hrat
        (by positivity : (0 : ℝ) ≤ 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2)
      nlinarith
    have hu0 : 0 ≤ ((56 / 75) ^ (Nh - ms) * ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) +
        8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) * (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh x ms δ M₀)) := by positivity
    refine (reg_oTo_wM1_le hMa hMb Nh _ _ _ hu0 (by positivity) (hAK X hX) hbk).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_cancel_right₀ _ hMa.ne', art_cancel _ _ _ hMb.ne']
    linarith
  have key := M.ct_top_trajR R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA
    hs1 hs2 hs3 hs4 hs5 hvb hwb hsmall x hx hj hms δ hδ hδl hδs hδc hδf hδp hδb hσ hmm0 hc₁ hk2
    hrm hk₁ hk₁0 hkt hVo hWo hK1 haN hbD' he hK2 hsmT
    (by rw [M.ctVT_eq _ hσ]; exact hmAB)
  rw [M.ctVT_eq _ hσ] at key
  exact key

end MasterFacts

end

end Spin2
