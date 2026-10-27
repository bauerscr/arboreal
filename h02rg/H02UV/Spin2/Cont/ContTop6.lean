import Spin2.Cont.ContTop4
import Spin2.Cont.ContTop5
import Spin2.Pair.PairLin4

set_option autoImplicit false

/-!
# Top coalescence `N_h + 1 ≤ j_y`: `P(x) − P(y)` at `h = 0` for the pair-difference datum

* **`MasterFacts.ct_T6_inputs_top`** (top analogue of `pl4_T6_inputs`): along the `h = 0`
  trajectory `(b, b − m)` in `D_ε`, for `0 < ms < N_h`, `ms < j_x`, `N_h + 1 ≤ j_y`, `y − x` and `0`
  in one `ms`-block, `|y − x|_∞ ≤ L^{ms−r}` and the scale conditions at `ms`:
  `P(x) − P(y) = rpTopOut_y(δ restarted from ms, at N_h + 1)` exactly (`pl3_conn_diff_top`), and all
  datum inputs of `ct_T5top` for `δ = pl2Delta` (invariants; `V_{ab} = 0` at `N_h`, `N_h + 1`,
  `𝒲_{ab} = 0` at `N_h` from the relaxed coalescence invariant; `Loc2Form`, pure form, `zV`
  reference), and the restart data at `ms` with `M₀ = cddM …`, `M₀ ≤ cddRel·|β^{(0,y)}_{ms}|`.
* **`MasterFacts.ct_conn_diff_top`** (exact statement in `Log.md`): `∃ kk ww ≥ 0` (restart data of
  `δ` at `ms`, `M₀ ≤ cddRel·|β^{(0,y)}_{ms}|`) such that for all size constants `mm, k₁, c₁, k₂`
  with the inequalities of `ct_T5top`, the `ab` input at `N_h + 1` and the two smallness conditions,
  `|P(x) − P(y)| ≤ (3/2)(1 + K_O)·Γ_δ·ϑ_{N_h} + (9/4)K_E·(σ/|β_{a,N_h}|)·ϑ_{N_h}²·ǧ_{N_h}`,
  `Γ_δ = ctGamB …` (the `γ` bound of `ct_gam_top`), `σ = ctSig … M₀`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- **All datum inputs of `ct_T5top` for the pair-difference datum, and the exact identity**
(top coalescence `N_h + 1 ≤ j_y`). -/
theorem MasterFacts.ct_T6_inputs_top (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hspl : SplitSmall R.P L R.ρ)
    (x y : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
        rpTopOut R Nh m b (b - m) y (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ∧
      (pl2Delta R m b (b - m) x y ms).IsObs ∧
      ObsLocInv (ptsX y) ms (pl2Delta R m b (b - m) x y ms) ∧
      ObsSymInv ms (pl2Delta R m b (b - m) x y ms) ∧
      (∀ q, ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q : SA .two (Lam 2 L N)).ab = 0) ∧
      (∀ q, ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q : SA .two (Lam 2 L N)).ab = 0) ∧
      (∀ q, ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).W q : SA .two (Lam 2 L N)).ab = 0) ∧
      (∀ q, Obs2.Loc2Form (ptsX y).a ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a) ∧
      (∀ q, ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a =
        LocObs.mass2 ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a •
          LocObs.pbp (ptsX y).a) ∧
      prjSt false (pl2Delta R m b (b - m) x y ms) = prjSt false (obsHist (R.withMsq m) (ptsX y)
        (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ∧
      ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
        0 < (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ∧
        ‖betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX y) ms
            (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms)‖ +
          shareDev2 (ptsX y).a ms (histVF2 (R.withMsq m) (ptsX y) ms
            (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms) ≤ (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ∧
        WbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms ww ∧
        KbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms kk ∧
        1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
          histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ∧
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ≤
          M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
            (R.withMsq m).A r * ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖ := by
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := M.core.hL49; norm_num; omega
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hmy : ms < Obs.coal L (0 : Lam 2 L N) y := by omega
  have hid := pl3_conn_diff_top (μ₀ := b - m) R hNh m hρ1 hspl hm.1 hm.2 hV hVL hL8 hb (by ring)
    x y ms hblk hkN.le hmx hj
  obtain ⟨-, -, hδb, -⟩ := pl2_delta_inv R m hV hVL b (b - m) x y hkN.le hblk
  obtain ⟨h0, hl0, hs0', hf0, hp0⟩ := cdd_delta_struct R m b (b - m) x y ms hV hVL hk0 hkN.le hblk
  have hVab := (pl3_delta_ab R hNh m hV hVL hL8 b (b - m) x y hkN.le hblk hmx hmy
    (k := Nh + 1) (by omega) (le_min hj le_rfl)).1
  have hVabN := (pl3_delta_ab R hNh m hV hVL hL8 b (b - m) x y hkN.le hblk hmx hmy
    (k := Nh) (by omega) (le_min (by omega) (by omega))).1
  have hWabN := (pl3_delta_inv R hNh m hV hVL hL8 b (b - m) x y hkN.le hblk hmx hmy
    (k := Nh) (by omega) (by omega) (by omega)).Wab
  obtain ⟨kk, ww, hkk, hww, hM0, hbR, hWR, hKR, hMR⟩ := M.cdd_restart_data N R hP hi0 hRℓ hRA hRρ
    hN Nh hNh m hm b (b - m) hD x y hk0 hkN hrk hblk hdist hs0 hs hreg
  have hrel := M.cdd_restart_rel N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD x y r hk0 hkN
    hs0 hs
  exact ⟨hid, h0, hl0, hs0', hVab, hVabN, hWabN, hf0, hp0, hδb, kk, ww, hkk, hww, hM0, hbR, hWR,
    hKR, hMR, hrel⟩

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`P(x) − P(y)` at `h = 0` for top coalescence `N_h + 1 ≤ j_y`**: the restart data exist,
and for all admissible size constants the difference is bounded by the restarted output. -/
theorem ct_conn_diff_top {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    (y : Lam 2 L N) (hy : y ≠ 0) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    -- the pair-difference datum
    (hspl : SplitSmall R.P L R.ρ) (x : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hsc0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hsc : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1)
    (hgms : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * 2) ≤ 1 / 1344) :
    ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
        histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ∧
      (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ≤
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
          (R.withMsq m).A r * ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖ ∧
    ∀ {mm k₁ c₁ k2 : ℝ}, 0 ≤ c₁ → 0 ≤ k2 →
      1 + cw2Thb M Nh Nh ≤ mm →
      M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) +
          ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r)) +
          cw2Thb M Nh Nh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) ≤
        M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm →
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ mm →
      (kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
            (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r)) +
          8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 +
          cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) ≤ k₁ →
      k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm →
      8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀ →
      (∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
        ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r))) (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
          Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
            ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X : Obs.SA .two (Lam 2 L N)).ab) ≤
          ENNReal.ofReal k2) →
      M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
        M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1 →
      2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
        (8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
          (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
            M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ)‖ ≤
        3 / 2 * (1 + M.fwKO) *
            M.ctGamB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) kk ww *
            varthJ R m b (b - m) Nh +
          9 / 4 * M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
            (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
              M.core.A) ^ (L ^ 2)) r₀ *
            ((ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r)) / ‖hBeta R m b (b - m) y Nh‖) * varthJ R m b (b - m) Nh ^ 2 *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hid, h0, hl0, hs0', hVab, hVabN, hWabN, hf0, hp0, hδb, kk, ww, hkk, hww, hM0, hbR, hWR,
    hKR, hMR, hrel⟩ := M.ct_T6_inputs_top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD hspl x y hk0
      hkN hmx hj hrk hblk hdist hsc0 hsc hreg
  refine ⟨kk, ww, hkk, hww, hMR, hrel, ?_⟩
  intro mm k₁ c₁ k2 hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hK2 hsmT hmAB
  rw [hid]
  have hT := M.ct_T5top R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1
    hs2 hs3 hs4 hs5 hvb hwb hsmall y hy hj hk0 hkN.le _ h0 hl0 hs0' hVab hVabN hWabN hf0 hp0 hδb
    hM0 hkk hww hbR hWR hKR hgms hMR hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hK2 hsmT hmAB
  have hG := M.ct_gam_top R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX y)
    (obsInit .two (zV b) (ptsX y)) (obsInit_isObs .two (zV b) (ptsX y)) hk0 hkN.le _ h0 hl0 hs0'
    hf0 hp0 hM0 hkk hww hbR hWR hKR hgms hMR
  have hKO0 : 0 ≤ M.fwKO := by
    unfold fwKO
    have := M.topF'_nonneg; have := M.topCL_nonneg
    have : 0 ≤ max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 := le_max_right _ _
    positivity
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hv : 0 ≤ varthJ R m b (b - m) Nh := by
    unfold varthJ; exact Real.rpow_nonneg (div_nonneg hb.le (hD Nh le_rfl).1.le) _
  refine hT.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG (by positivity)) hv

end MasterFacts

end

end Spin2
