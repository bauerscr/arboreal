import Spin2.Cont.ContFx3a
import Spin2.Cont.ContEqS6

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`), Phase 2, layer 5a: the size parameters of the intermediate case with `Θ*`

**`MasterFacts.fx_mid_pkg`**: `eqs_mid_pkg` for the package `FxMidPkg`. The choices are those of
`eqs_mid_pkg` with `Θ(C_δ) ↦ Θ* = fxTh`, `k̄(C_δ) ↦ m̄ = fxmbar`:
`v_T = fxVT = 1 + Θ*`, `w₂ = fxW2`, `w_T = fxWT`, `m₀ = fxM0` (all `L`-constants, given `C₁*`).
The smallness hypotheses are `C_δ`-free:
* `ǧ_{N_h}, a_{ms} ≤ eqsThr(fxLg r₀)`;
* `m L^{2N} ≤ eqsThr(fxLm r₀ Kt C₁*)` (window `hmAB` at `m₀` itself).
`C_δ` occurs only in `N ≤ J + C_δ`, in the waiting hypothesis `(3/4)^{J−ms}·eqsKW(C_δ) ≤ ǧ_{ms}²`
(the `Z_{ab}` part still sees `Θ_b(ms)`, i.e. `C_δ`, through `zabQ`), and in the conclusion constant
`K_R = fxKT r₀ C₁t Λ₁ Λ₂ (fxM0 C₁*) C_δ`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- `w₂ = exp(L²C_w(c + (2m̄)²)) − 1`. -/
def fxW2 : ℝ := Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c + (2 * M.fxmbar) ^ 2))) - 1

/-- `w_T`. -/
def fxWT : ℝ := M.core.cWo * M.core.c + M.eqsTw + M.fxTh * (M.core.cWo * M.core.c) + M.fxW2

/-- `v_T = 1 + Θ*`. -/
def fxVT : ℝ := 1 + M.fxTh

/-- `m₀` of `h8*` (an `L`-constant given `C₁*`). -/
def fxM0 (C₁w C₁t C₁v C₁m : ℝ) : ℝ :=
  8 * (2 * rpIota M.fxVT M.fxWT * M.core.A) ^ ((L + 18) ^ 2) *
    (1 / (vck C₁w * (4 * C₁w + 1)) + 1 / (vck C₁t * (4 * C₁t + 1)) +
      1 / (vck C₁v * (4 * C₁v + 1)) + 1 / (vck C₁m * (4 * C₁m + 1)))

/-- The `ǧ`-type coefficients (intermediate case, `Θ*`). -/
def fxLg (r₀ : ℝ) : List ℝ :=
  [2 * (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
      9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
      cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3),
    2 * M.core.Cf / M.core.ρ,
    16 * cM * M.core.ℓ ^ 2 * M.core.Cf,
    PtCorr2.cRho L * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL,
    4 * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL / r₀ ^ 2,
    cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL / r₀,
    2 * max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0,
    4 * M.Kp,
    4 * M.core.A ^ 4 * cx M.core.κ M.core.cT,
    2688 * M.core.rdtC * M.core.cWo * M.core.c,
    32 * M.core.A ^ 4 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * (1 + M.fxTh),
    4 * M.core.A ^ 4 * M.k2cab * M.core.c * M.fxmbar ^ 2,
    8 * (cx M.core.κ M.core.cT + 1 + 8 * M.core.cWo * M.core.Bk) * M.core.c ^ 3 / M.core.ε₀,
    M.core.c]

/-- The mass coefficients (intermediate case, window at `m₀`). -/
def fxLm (r₀ Kt C₁w C₁t C₁v C₁m : ℝ) : List ℝ :=
  [2 * Kt,
    8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3,
    2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      ((M.fxM0 C₁w C₁t C₁v C₁m) +
        (4 * C₁t + 1) * M.core.c * (M.fxM0 C₁w C₁t C₁v C₁m) +
        8 * ((4 * C₁t + 1) * (M.fxM0 C₁w C₁t C₁v C₁m)) + 1) * M.core.ℓ ^ 2),
    2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * M.eqsVWK * M.core.ℓ ^ 2)]

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The size parameters of the intermediate case, `Θ*` form** (see the module docstring). -/
theorem fx_mid_pkg {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (x y : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh) (hrk : r ≤ ms)
    (hdist : supNorm (y - x) ≤ L ^ (ms - r)) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {Kt C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ} (hC₁w : 0 ≤ C₁w) (hC₁t : 0 ≤ C₁t) (hC₁v : 0 ≤ C₁v)
    (hC₁m : 0 ≤ C₁m) (hcab : 0 < M.k2cab) (hBk : 0 < M.core.Bk)
    (Cδ : ℕ) {J : ℕ} (hJy : J ≤ Obs.coal L (0 : Lam 2 L N) y) (hδ : N ≤ J + Cδ)
    (hG1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ eqsThr (M.fxLg r₀))
    (hz : zA L m ms ≤ eqsThr (M.fxLg r₀))
    (hX1 : m * (L : ℝ) ^ (2 * N) ≤ eqsThr (M.fxLm r₀ Kt C₁w C₁t C₁v C₁m))
    (hW : (3 / 4) ^ (J - ms) * M.eqsKW Cδ ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2) :
    M.FxMidPkg C₁w C₁t C₁v C₁m Λ₁ Λ₂ R m b Nh r₀ x y ms r Cδ (M.eqsKA r₀)
      (M.fxKT r₀ C₁t Λ₁ Λ₂ (M.fxM0 C₁w C₁t C₁v C₁m) Cδ) := by
  intro kk ww hkk hww hMR
  have hδ : N ≤ Obs.coal L (0 : Lam 2 L N) y + Cδ := by omega
  -- basic facts
  have hN2 : 2 ≤ N := by omega
  have hc2 : 2 ≤ M.core.c := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    exact hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hε0 : 0 ≤ M.core.ε := by
    have := (hD 0 (Nat.zero_le _)).2.1; linarith [(hD 0 (Nat.zero_le _)).1]
  have hε1 := M.eps_le
  have hgp : ∀ j ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 :=
    fun j hj => (hD j hj).1
  have hg1 : ∀ j ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 :=
    fun j hj => (hD j hj).2.1.trans hε1
  have hcst := M.core.consts_nonneg
  have hcW : 1 ≤ M.core.cWo := hcst.2.2.2.2.2.1
  have hcδ : 0 ≤ M.core.cδ := hcst.2.2.2.2.2.2.2.1
  have hΓ : 0 < M.core.rdtΓ := M.core.eqs_rdtΓ_pos (by linarith) hε0
  have hcN : (1 : ℝ) ≤ PtCorr2.csN 2 := by exact_mod_cast eqs_one_le_csN
  have hε₀ : 0 < M.core.ε₀ := M.core.hε₀
  have hCw : 0 ≤ M.core.Cw := M.core.hCw
  have hA2 := M.core.hA2
  have hKp := M.Kp_nonneg
  have hkN : ms < Nh := lt_of_lt_of_le hmy hj
  have hJN : Nh ≤ Obs.coal L (0 : Lam 2 L N) y + Cδ := by omega
  have hJd : Nh - Obs.coal L (0 : Lam 2 L N) y ≤ Cδ := by omega
  -- the three couplings
  have hGp := hgp Nh le_rfl
  have hgmp := hgp ms hkN.le
  have hgJp := hgp _ hj
  have hgm1 := hg1 ms hkN.le
  have hgJ1 := hg1 _ hj
  have hG1' := hg1 Nh le_rfl
  have hgmG := M.eqs_traj_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hkN.le le_rfl
  have hgJG := M.eqs_traj_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hj le_rfl
  have hgmJ := M.eqs_traj_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hmy.le hj
  -- the thresholds
  have hthr : ∀ a ∈ M.fxLg r₀, ∀ g' : ℝ, 0 ≤ g' →
      g' ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 → a * g' ≤ 1 :=
    fun a ha g' h0 h => eqs_le_thr ha h0 (h.trans hG1)
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.1.le (by positivity)
  have hthm : ∀ a ∈ M.fxLm r₀ Kt C₁w C₁t C₁v C₁m, a * (m * (L : ℝ) ^ (2 * N)) ≤ 1 :=
    fun a ha => eqs_le_thr ha hX0 hX1
  have fc := hthr M.core.c (by unfold fxLg; simp) _ hGp.le le_rfl
  have hcG0 : 0 < M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by positivity
  have hcG1 : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 := fc
  -- `hs0`, `hs` at `ms`
  have hz0 := zA_nonneg L hm.1.le ms
  have fK1 := hthr (4 * M.Kp) (by unfold fxLg; simp) _ hgmp.le hgmG
  have fK2 := eqs_le_thr (l := M.fxLg r₀) (a := 4 * M.Kp) (by unfold fxLg; simp) hz0 hz
  have hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) := by
    positivity
  have hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2 := by
    linarith
  -- the ratios
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := id M.core.hC2
  have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8
  have hsp := histS_pos' (R.withMsq m) hρ0' hρ8' (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms
  have hA0 : 0 ≤ (R.withMsq m).A := by
    rw [show (R.withMsq m).A = M.core.A from hRA]; linarith
  have hι : 0 ≤ rpIota 0 0 := by
    have := one_le_rpIota (le_refl (0 : ℝ)) (le_refl (0 : ℝ)); linarith
  have hM0 := M.eqs_cddM_ge (Kl := M.Kp) (z := zA L m ms)
    (bb := ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖) r hs0 hgmp.le (norm_nonneg _)
    (norm_nonneg (bt2 R (ptsX y) (zV0 b) m b (b - m) ms)) hsp hι hA0 (by linarith) hΓ.le
  have hP0 : 0 ≤ M.pl5M0 R m b x y ms r :=
    le_trans (mul_nonneg hgmp.le (norm_nonneg _)) hM0
  have hS0 : 0 ≤ histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
      (M.pl5M0 R m b x y ms r) := by positivity
  have hτw := M.eqs_ratio_w hΓ hkk hS0 hMR
  have hτk := M.eqs_ratio_k hΓ hcN (by positivity) hkk hww hS0 hMR
  have hτw0 : 0 ≤ ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
      (M.pl5M0 R m b x y ms r)) := div_nonneg hww hS0
  have hτk0 : 0 ≤ (kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
      (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
        (M.pl5M0 R m b x y ms r)) := div_nonneg (by positivity) hS0
  -- the waiting facts
  have hTw0 : 0 ≤ M.eqsTw := hτw0.trans hτw
  have hTk0 : 0 ≤ M.eqsTk := hτk0.trans hτk
  have hK₂ : 0 ≤ M.eqsK2 := by
    unfold eqsK2 zabIota; have := hcab; positivity
  have hTh := M.eqsTh_pos Cδ
  have hq : (0 : ℝ) ≤ (3 / 4) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) := by positivity
  have hKWn : 0 ≤ M.eqsTk / (8 * M.core.Bk) := div_nonneg hTk0 (by positivity)
  have hKWa : 0 ≤ M.eqsTh Cδ * M.eqsK2 := mul_nonneg hTh.le hK₂
  have hKWb : 0 ≤ M.core.A ^ 4 * M.eqsTk := by positivity
  have hKW0 : 0 ≤ M.eqsKW Cδ := by unfold eqsKW; positivity
  have hW : (3 / 4) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * M.eqsKW Cδ ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (show J - ms ≤ Obs.coal L (0 : Lam 2 L N) y - ms by omega)) hKW0) hW
  have hKWge : ∀ X, X ≤ M.eqsKW Cδ → (3 / 4) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * X ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 := fun X hX =>
    (mul_le_mul_of_nonneg_left hX hq).trans hW
  have hnn : Obs.coal L (0 : Lam 2 L N) y - ms ≤ Nh - ms := by omega
  have hg2le : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 := by
    rw [sq]; exact mul_le_of_le_one_right hgmp.le hgm1
  -- W-d: `(7/30)^{n'}τ_w ≤ cǧ_{N_h}`
  have wd : (7 / 30 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
    have h1 := mul_le_mul (eqs_pow_le_of (a := 7 / 30) (by norm_num) (by norm_num) hnn) hτw hτw0 hq
    have h2 := hKWge M.eqsTw (by unfold eqsKW; linarith)
    have h3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤
        M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 :=
      le_mul_of_one_le_left hGp.le (by linarith)
    linarith
  -- W-e: `(56/75)^{n'}τ_k ≤ (cǧ_{N_h})²`
  have we : (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
      (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
        (M.pl5M0 R m b x y ms r))) ≤
      (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 := by
    have h1 := mul_le_mul (eqs_pow_le_of (a := 56 / 75) (by norm_num) (by norm_num) hnn) hτk hτk0 hq
    have h2 := hKWge M.eqsTk (by unfold eqsKW; linarith)
    have h3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 ≤
        (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 :=
      pow_le_pow_left₀ hgmp.le (hgmG.trans (le_mul_of_one_le_left hGp.le (by linarith))) 2
    linarith
  -- W-c: `4A⁴(56/75)^nτ_k ≤ 1`
  have wc : M.core.A ^ 4 * ((56 / 75 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) *
      ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
      (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
        (M.pl5M0 R m b x y ms r)))) ≤ 1 / 4 := by
    have h1 := mul_le_mul (eqs_pow_le_of (a := 56 / 75) (by norm_num) (by norm_num) le_rfl) hτk
      hτk0 hq
    have h2 := hKWge (4 * M.core.A ^ 4 * M.eqsTk) (by unfold eqsKW; linarith)
    have hA4 : 0 ≤ M.core.A ^ 4 := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hA4
    have h4 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 ≤ 1 := hg2le.trans hgm1
    have e : (3 / 4 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (4 * M.core.A ^ 4 * M.eqsTk) =
        4 * (M.core.A ^ 4 * ((3 / 4 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * M.eqsTk)) := by ring
    linarith
  -- the choices
  obtain ⟨hmm1, hmmc, hmmW⟩ := eqs_mm hcW hcG0 (by positivity) wd
  set mm := max 1 (M.core.cWo + (7 / 30 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) /
      (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) with hmmd
  have hB8 : 0 ≤ 8 * M.core.cWo * M.core.Bk := by positivity
  obtain ⟨hc₁, hk₁, hc₁b⟩ := eqs_k1 hB8 hcG0 (by positivity) we hmm1
  have hGN0 := hGp.le
  have hcGN0 : 0 ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := hcG0.le
  have hc0 : 0 ≤ M.core.c := by linarith
  have hcGJ : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1 ≤ M.core.c := mul_le_of_le_one_right hc0 hgJ1
  have hTH0 : 0 ≤ M.fxTh := M.fxTh_pos.le
  have hTHΘ : M.fxTh ≤ M.fxTh := le_rfl
  have hp1 : (7 / 30 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp2 : (56 / 75 : ℝ) ^ (Nh - ms) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hkb0 : 0 ≤ M.fxmbar := by
    unfold fxmbar
    have := mul_nonneg (show (0 : ℝ) ≤ M.core.cWo + 1 by linarith)
      (show (0 : ℝ) ≤ 1 + M.fxTh by linarith [M.fxTh_pos])
    linarith
  have hkbK : M.fxmbar ≤ M.fxmbar := le_rfl
  -- 1, 2: `v_T`, `w_T`
  have c1 : 1 + M.fxTh ≤ M.fxVT := by unfold fxVT; linarith
  have c2 : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) + (7 / 30) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + M.fxTh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1)) + M.fxW2 ≤ M.fxWT := by
    unfold fxWT
    have a := mul_le_mul_of_nonneg_left hcGJ (by linarith : (0 : ℝ) ≤ M.core.cWo)
    have b' : (7 / 30 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.eqsTw :=
      (mul_le_of_le_one_left hτw0 hp1).trans hτw
    have c' := mul_le_mul hTHΘ a (by positivity) hTH0
    linarith
  -- 4: `w₂ ≥ 0`
  have c4 : 0 ≤ M.fxW2 := by
    unfold fxW2
    have h0 : 0 ≤ (L : ℝ) ^ 2 * (M.core.Cw * (M.core.c + (2 * M.fxmbar) ^ 2)) := by positivity
    linarith [Real.add_one_le_exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c + (2 * M.fxmbar) ^ 2)))]
  -- 6–8: `Q₀`
  have hcgm : 0 < M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 := by positivity
  obtain ⟨c6, c7, c8⟩ := eqs_Q (a := (7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))))
    (b := (7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r)))) (by positivity) (by positivity) hcgm hBk
  -- 9: waiting
  have hsup : ((supNorm (y - x) : ℕ) : ℝ) ≤ (L : ℝ) ^ ms := by
    have h1 : supNorm (y - x) ≤ L ^ ms :=
      hdist.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega))
    exact_mod_cast h1
  have hZ1 := M.eqs_zab_le N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD x y (J := Obs.coal L (0 : Lam 2 L N) y) r hk0 hkN
    hs0 hs hsup hcab (by linarith) hgm1
  have hthb := M.eqs_thb_ms hJN hmy.le
  have hZ : zabZr M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) (Obs.coal L (0 : Lam 2 L N) y) Nh /
      (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1)) ≤
      (7 / 5) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (M.eqsTh Cδ * (81 / 56) ^ (Obs.coal L (0 : Lam 2 L N) y - ms)) * M.eqsK2 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 := by
    refine hZ1.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hthb (by positivity)) hK₂
  have c9 : (8 / 15 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * zabQ M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r)
      (Obs.coal L (0 : Lam 2 L N) y) Nh ((7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) +
        (7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2)) ≤ 1 := by
    unfold zabQ
    have := eqs_wait_pure (n := Obs.coal L (0 : Lam 2 L N) y - ms) hgmp hgm1 (by linarith) hBk hτw0 hτw hτk0 hτk hTh.le hK₂ hZ
      (KW := M.eqsKW Cδ) (by unfold eqsKW; linarith) hW
    simpa only [mul_div_assoc] using this
  -- 10: `w₂`
  have c10 : Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ((Obs.coal L (0 : Lam 2 L N) y) - 1)).1 + (2 * M.fxmbar) ^ 2))) - 1 ≤ M.fxW2 := by
    unfold fxW2
    have hJ1 : (Obs.coal L (0 : Lam 2 L N) y) - 1 ≤ Nh := by omega
    have a : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ((Obs.coal L (0 : Lam 2 L N) y) - 1)).1 ≤ M.core.c := mul_le_of_le_one_right hc0 (hg1 _ hJ1)
    have b' : (2 * M.fxmbar) ^ 2 ≤ (2 * M.fxmbar) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add a b') hCw)
      (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    linarith [Real.exp_le_exp.2 this]
  have hcx0 : 0 ≤ cx M.core.κ M.core.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id M.core.hC2
    unfold cx; exact (div_pos (by linarith) (by linarith)).le
  -- 12: `hsmT`
  have c12 := eqs_smT_pure (A4 := M.core.A ^ 4) (cx := cx M.core.κ M.core.cT)
    (cW := M.core.cWo) (Bk := M.core.Bk) (c := M.core.c) (cab := M.k2cab) (Kb := M.fxmbar)
    (Θ := M.fxTh) (u := (56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))))
    (TH := M.fxTh) (kb := M.fxmbar) (by positivity) hcx0 hgJp.le hgJ1 (by linarith)
    hBk.le hc0 hTH0 hTHΘ hcab.le hkb0 hkbK wc
    (by have := hthr (4 * M.core.A ^ 4 * cx M.core.κ M.core.cT) (by unfold fxLg; simp) _ hgJp.le hgJG
        linarith)
    (hthr _ (by unfold fxLg; simp) _ hgJp.le hgJG)
    (hthr _ (by unfold fxLg; simp) _ hgJp.le hgJG)
  -- 13–17: `m₀`
  have hvT0 : 0 ≤ M.fxVT := by unfold fxVT; linarith
  have hwT0 : 0 ≤ M.fxWT := by
    unfold fxWT; have := mul_nonneg hTH0 (by positivity : (0 : ℝ) ≤ M.core.cWo * M.core.c)
    have : 0 ≤ M.core.cWo * M.core.c := by positivity
    linarith
  have hι1 := one_le_rpIota hvT0 hwT0
  have hvw := vck_pos hC₁w
  have hvt := vck_pos hC₁t
  have hvv := vck_pos hC₁v
  have hvm := vck_pos hC₁m
  have hY : 0 ≤ 8 * (2 * rpIota (M.fxVT) (M.fxWT) * M.core.A) ^ ((L + 18) ^ 2) := by
    positivity
  have s1 : 0 < 1 / (vck C₁w * (4 * C₁w + 1)) := by positivity
  have s2 : 0 < 1 / (vck C₁t * (4 * C₁t + 1)) := by positivity
  have s3 : 0 < 1 / (vck C₁v * (4 * C₁v + 1)) := by positivity
  have s4 : 0 < 1 / (vck C₁m * (4 * C₁m + 1)) := by positivity
  have c13 : 0 < M.fxM0 C₁w C₁t C₁v C₁m := by unfold fxM0; positivity
  have c14 := eqs_h8 hY hvw (by linarith : (0 : ℝ) < 4 * C₁w + 1)
    (s := 1 / (vck C₁w * (4 * C₁w + 1)) + 1 / (vck C₁t * (4 * C₁t + 1)) +
      1 / (vck C₁v * (4 * C₁v + 1)) + 1 / (vck C₁m * (4 * C₁m + 1))) (by linarith)
  have c15 := eqs_h8 hY hvt (by linarith : (0 : ℝ) < 4 * C₁t + 1)
    (s := 1 / (vck C₁w * (4 * C₁w + 1)) + 1 / (vck C₁t * (4 * C₁t + 1)) +
      1 / (vck C₁v * (4 * C₁v + 1)) + 1 / (vck C₁m * (4 * C₁m + 1))) (by linarith)
  have c16 := eqs_h8 hY hvv (by linarith : (0 : ℝ) < 4 * C₁v + 1)
    (s := 1 / (vck C₁w * (4 * C₁w + 1)) + 1 / (vck C₁t * (4 * C₁t + 1)) +
      1 / (vck C₁v * (4 * C₁v + 1)) + 1 / (vck C₁m * (4 * C₁m + 1))) (by linarith)
  have c17 := eqs_h8 hY hvm (by linarith : (0 : ℝ) < 4 * C₁m + 1)
    (s := 1 / (vck C₁w * (4 * C₁w + 1)) + 1 / (vck C₁t * (4 * C₁t + 1)) +
      1 / (vck C₁v * (4 * C₁v + 1)) + 1 / (vck C₁m * (4 * C₁m + 1))) (by linarith)
  -- 18: `hmAB`
  have c18 := hthm (2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      ((M.fxM0 C₁w C₁t C₁v C₁m) +
        (4 * C₁t + 1) * M.core.c * (M.fxM0 C₁w C₁t C₁v C₁m) +
        8 * ((4 * C₁t + 1) * (M.fxM0 C₁w C₁t C₁v C₁m)) + 1) * M.core.ℓ ^ 2))
    (by unfold fxLm; simp)
  -- 25: `hkt`
  have c25 := eqs_kt_pure (cx := cx M.core.κ M.core.cT) hB8 hcx0 hc₁b hc0 hGN0 hG1' rfl hε₀
    (hthr _ (by unfold fxLg; simp) _ hGN0 le_rfl)
  -- 26, 27: `hmAa`, `K_A`
  have hk₁0 : 0 ≤ (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 := by
    positivity
  have hk₁b : (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 ≤
      M.eqsTk + 8 * M.core.cWo * M.core.Bk := by
    have a : (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.eqsTk := (mul_le_of_le_one_left hτk0 hp2).trans hτk
    have b' : (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 ≤ 1 := pow_le_one₀ hcGN0 hcG1
    have := mul_le_mul_of_nonneg_left b' hB8
    linarith
  have hmm0 : (0 : ℝ) ≤ mm := by linarith
  have hV := M.eqs_ctVT_mono hcGN0 hcG1
  have hWm := M.eqs_rptfWT_mono hCw hmm0 hcG1 hmmc
  set k₁ := (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2
    with hk₁d
  set c₁ := k₁ / ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm) with hc₁d
  have hKx := M.eqs_rptfKx_mono hc₁ hcGN0 hmm0 hk₁0 hc₁b hcG1 hmmc hk₁b
  have c27 : M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm)
      (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ ≤ M.eqsKA r₀ :=
    M.eqs_naKA_mono hr₀ (by linarith)
  have hcJ := eqs_cJ_nonneg (L := L) hr₀
  have hsum : M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm +
      8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1 ≤ M.eqsVWK := by
    unfold eqsVWK; linarith
  have c26 : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm +
        8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum hcJ) (sq_nonneg M.core.ℓ)) (by norm_num : (0 : ℝ) ≤ 2)) hX0
    rw [mul_assoc]
    exact h.trans (hthm _ (by unfold fxLm; simp))
  refine ⟨M.fxVT, M.fxWT,
    (56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2 +
      M.fxTh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2),
    M.fxW2, M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) * M.fxmbar ^ 2,
    M.fxM0 C₁w C₁t C₁v C₁m,
    (7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) +
      (7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2),
    mm, k₁, c₁, c1, c2, le_rfl, c4, by positivity, c6, c7, c8, c9, c10, le_rfl, c12, c13, c14,
    c15, c16, c17, by rw [mul_assoc]; exact c18, hc₁, hmm1, hmmW, hcG1.trans hmm1, le_rfl, hk₁,
    c25, c26, c27, le_rfl⟩


end MasterFacts

end

end Spin2
