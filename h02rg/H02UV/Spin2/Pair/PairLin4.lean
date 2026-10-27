import Spin2.Cont.ContWire8
import Spin2.Cont.ContDiffD3

/-!
# B3, T6: the inputs of the T5 bound for the pair-difference datum (`h = 0`, `j_y ≤ N_h`)

**`MasterFacts.pl4_T6_inputs`**: along the `h = 0` trajectory `(b, b − m)` in `D_ε`, for
`0 < ms < j_x`, `ms < j_y ≤ N_h`, `y − x` and `0` in one `ms`-block, `|y − x|_∞ ≤ L^{ms − r}`, and
the scale conditions at `ms` (`K_p(ǧ + a) ≤ 1/2`, `A⁴c_xǧ³ ≤ 1`):

* `P(x) − P(y) = rpcOut_y(cw2O R m b y ms δ)` exactly (`pl3_conn_diff`), `δ = pl2Delta`;
* every datum hypothesis of `MasterFacts.cw3_T5R` for `δ` (observable, local, symmetric,
  `V_{ab} = 0` at `j_y`, `Loc2Form`, pure form, `zV` reference `σ_b` part);
* the restart data at `ms` (`∃ k w ≥ 0`, `0 < M₀`, `|β| + D ≤ M₀`, `WbHF`, `KbHF`,
  `1344(8c_Nk + Γ_ww) ≤ s²M₀`) with `M₀ = M.cddM M.Kp …` and `M₀ ≤ cddRel·|β^{(0,y)}_{ms}|`.

So `|P(x) − P(y)|` is bounded by `MasterFacts.cw3_T5R` applied to these data; the remaining open
inputs of that bound are the `σ_aσ_b` sizes `w₂`, `k₂` at `j_y`, `γ_δ ≥ ‖ε(u_a)‖`, and its scalar
conditions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- **All datum inputs of `cw3_T5R` for the pair-difference datum, and the exact identity.** -/
theorem MasterFacts.pl4_T6_inputs (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hmL : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (x y : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hmy : ms < Obs.coal L (0 : Lam 2 L N) y) (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
        rpcOut R m b (b - m) y (cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)) ∧
      (pl2Delta R m b (b - m) x y ms).IsObs ∧
      ObsLocInv (ptsX y) ms (pl2Delta R m b (b - m) x y ms) ∧
      ObsSymInv ms (pl2Delta R m b (b - m) x y ms) ∧
      (∀ q, ((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).V q : SA .two (Lam 2 L N)).ab = 0) ∧
      (∀ q, Obs2.Loc2Form (ptsX y).a
        ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a) ∧
      (∀ q, ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a =
        LocObs.mass2 ((pl2Delta R m b (b - m) x y ms).V q : SA .two (Lam 2 L N)).a •
          LocObs.pbp (ptsX y).a) ∧
      prjSt false (pl2Delta R m b (b - m) x y ms) = prjSt false (obsHist (R.withMsq m) (ptsX y)
        (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ∧
      ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
        0 < M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0)
          (R.withMsq m).A r ∧
        ‖betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX y) ms
            (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms)‖ +
          shareDev2 (ptsX y).a ms (histVF2 (R.withMsq m) (ptsX y) ms
            (pl2Delta R m b (b - m) x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms) ≤
          M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
            ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
            (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0)
            (R.withMsq m).A r ∧
        WbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms ww ∧
        KbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms kk ∧
        1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
          histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
            M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
              ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
              (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0)
              (R.withMsq m).A r ∧
        M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
            ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
            (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0)
            (R.withMsq m).A r ≤
          M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
            (R.withMsq m).A r * ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖ := by
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := M.core.hL49; norm_num; omega
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hkN : ms < Nh := by omega
  have hid := pl3_conn_diff (μ₀ := b - m) R hNh m hρ1 hspl hm0 hmL hV hVL hL8 hb (by ring) x y ms hblk hmx hmy hj
  obtain ⟨-, -, hδb, -⟩ := pl2_delta_inv R m hV hVL b (b - m) x y hkN.le hblk
  obtain ⟨h0, hl0, hs0', hf0, hp0⟩ := cdd_delta_struct R m b (b - m) x y ms hV hVL hk0 hkN.le hblk
  have hVab := (pl3_delta_ab R hNh m hV hVL hL8 b (b - m) x y hkN.le hblk hmx hmy hmy.le
    (le_min le_rfl (by omega))).1
  obtain ⟨kk, ww, hkk, hww, hM0, hbR, hWR, hKR, hMR⟩ := M.cdd_restart_data N R hP hi0 hRℓ hRA hRρ
    hN Nh hNh m hm b (b - m) hD x y hk0 hkN hrk hblk hdist hs0 hs hreg
  have hrel := M.cdd_restart_rel N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD x y r hk0 hkN
    hs0 hs
  exact ⟨hid, h0, hl0, hs0', hVab, hf0, hp0, hδb, kk, ww, hkk, hww, hM0, hbR, hWR, hKR, hMR, hrel⟩

end

end Spin2
