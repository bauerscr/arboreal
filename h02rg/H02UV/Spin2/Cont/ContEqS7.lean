import Spin2.Cont.ContEqS6

set_option autoImplicit false

/-!
# B3, `r`-dependent form: the size parameters of the top case

**`MasterFacts.eqs_top_pkg`**: the package `EqcTopPkg` (all arrows of `fin_conn_diff_top`,
`naKA ≤ K_A`, `rpKE ≤ K_E`) for the explicit choice
`mm = (1 + Θ₀)·max(1, c_W + (7/30)^nτ_w/(cǧ_{N_h}))`, `k₁ = (56/75)^nτ_k + B_t(cǧ_{N_h})²`,
`c₁ = k₁/((cǧ_{N_h})²mm)`, `k₂ = (c_{ab}/5)cǧ_{N_h}k̄²`, the `Q₀` of the intermediate case
(`n = N_h − ms`, `Θ₀ = Θ_b(N_h) = eqsTh 0`, `B_t = 8c_WB(1 + Θ₀)`), given
`ǧ_{N_h}, a_{ms} ≤ eqsThr(eqsLt r₀)`, `m²L^{2N} ≤ eqsThr(eqsLmt r₀)` and the waiting hypothesis
`(3/4)^{J−ms}·eqsKWt ≤ ǧ_{ms}²` (`J ≤ N_h`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
/-- The `K` step at the top (pure): `rptfKx ≤ 8θu + Q·G`. -/
theorem eqs_kx_top {θ C₁ cx kb c G c₁ u B T mm MM : ℝ} (hθ : 0 ≤ θ) (hC₁ : 0 ≤ C₁)
    (hcx : 0 ≤ cx) (hkb : 0 ≤ kb) (hc : 0 ≤ c) (hG : 0 ≤ G) (hG1 : G ≤ 1) (hcG : c * G ≤ 1)
    (hc₁b : c₁ ≤ 1 + B) (hu : 0 ≤ u) (huT : u ≤ T) (hB : 0 ≤ B) (hmm : 0 ≤ mm)
    (hmmM : mm ≤ MM) :
    (θ + C₁ * (2 + 2 * (8 * cx) + 8 * c₁) * (c * G)) * (8 * (u + B * (c * G) ^ 2)) +
        kb * (c * G) ^ 2 * mm ≤
      8 * θ * u + (8 * θ * B * c ^ 2 + C₁ * (10 + 16 * cx + 8 * B) * c * (8 * (T + B)) +
        kb * c ^ 2 * MM) * G := by
  have hcG0 : 0 ≤ c * G := by positivity
  have hsq : (c * G) ^ 2 ≤ c ^ 2 * G := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by rw [sq]; exact mul_le_of_le_one_right hG hG1)
      (by positivity)
  have hsq1 : (c * G) ^ 2 ≤ 1 := pow_le_one₀ hcG0 hcG
  have hk : u + B * (c * G) ^ 2 ≤ T + B := by
    have := mul_le_mul_of_nonneg_left hsq1 hB; linarith
  have hk0 : 0 ≤ u + B * (c * G) ^ 2 := by positivity
  have t1 : θ * (8 * (u + B * (c * G) ^ 2)) ≤ 8 * θ * u + 8 * θ * B * c ^ 2 * G := by
    have := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8 * θ * B by positivity)
    nlinarith
  have t2 : C₁ * (2 + 2 * (8 * cx) + 8 * c₁) * (c * G) * (8 * (u + B * (c * G) ^ 2)) ≤
      C₁ * (10 + 16 * cx + 8 * B) * c * (8 * (T + B)) * G := by
    have a : C₁ * (2 + 2 * (8 * cx) + 8 * c₁) ≤ C₁ * (10 + 16 * cx + 8 * B) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₁
    have b := mul_le_mul a (show 8 * (u + B * (c * G) ^ 2) ≤ 8 * (T + B) by linarith)
      (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_right b hcG0
    have e1 : C₁ * (2 + 2 * (8 * cx) + 8 * c₁) * (c * G) * (8 * (u + B * (c * G) ^ 2)) =
        C₁ * (2 + 2 * (8 * cx) + 8 * c₁) * (8 * (u + B * (c * G) ^ 2)) * (c * G) := by ring
    have e2 : C₁ * (10 + 16 * cx + 8 * B) * c * (8 * (T + B)) * G =
        C₁ * (10 + 16 * cx + 8 * B) * (8 * (T + B)) * (c * G) := by ring
    linarith
  have t3 : kb * (c * G) ^ 2 * mm ≤ kb * c ^ 2 * MM * G := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hsq hkb) hmmM hmm (by positivity)
    have e : kb * (c ^ 2 * G) * MM = kb * c ^ 2 * MM * G := by ring
    linarith
  have e : (θ + C₁ * (2 + 2 * (8 * cx) + 8 * c₁) * (c * G)) * (8 * (u + B * (c * G) ^ 2)) =
      θ * (8 * (u + B * (c * G) ^ 2)) +
        C₁ * (2 + 2 * (8 * cx) + 8 * c₁) * (c * G) * (8 * (u + B * (c * G) ^ 2)) := by ring
  rw [e]
  have e2 : (8 * θ * B * c ^ 2 + C₁ * (10 + 16 * cx + 8 * B) * c * (8 * (T + B)) +
        kb * c ^ 2 * MM) * G = 8 * θ * B * c ^ 2 * G + C₁ * (10 + 16 * cx + 8 * B) * c *
          (8 * (T + B)) * G + kb * c ^ 2 * MM * G := by ring
  rw [e2]; linarith

namespace MasterFacts

variable (M : MasterFacts L)

/-- `B_t = 8c_WB + Θ₀·8c_WB`. -/
def eqsBt : ℝ := 8 * M.core.cWo * M.core.Bk + M.eqsTh 0 * (8 * M.core.cWo * M.core.Bk)

/-- The bound `(1 + Θ₀)(c_W + 1)` of `mm`. -/
def eqsMMt : ℝ := (1 + M.eqsTh 0) * (M.core.cWo + 1)

/-- The `ǧ`-coefficient of the `K` step at the top. -/
def eqsQt : ℝ :=
  8 * kθ0 L M.core.A M.core.C₀o M.core.ηo * M.eqsBt * M.core.c ^ 2 +
    M.core.C₁k * (10 + 16 * cx M.core.κ M.core.cT + 8 * M.eqsBt) * M.core.c *
      (8 * (M.eqsTk + M.eqsBt)) + kB (kθ0 L M.core.A M.core.C₀o M.core.ηo) M.core.C₁k (8 * cx M.core.κ M.core.cT) * M.core.c ^ 2 * M.eqsMMt

/-- The `ǧ`-type coefficients (top case). -/
def eqsLt (r₀ : ℝ) : List ℝ :=
  [4 * M.Kp, M.core.c,
    8 * (cx M.core.κ M.core.cT + 1 + M.eqsBt) * M.core.c ^ 3 / M.core.ε₀,
    2 * M.core.A ^ 4 * (M.core.Cf + M.eqsQt + M.k2cab / 5 * M.core.c * M.eqsKb 0 ^ 2), r₀]

/-- `V + W + 8K + 1` at the top bounds. -/
def eqsVWKt : ℝ :=
  M.ctVT 1 + M.rptfWT 1 M.eqsMMt + 8 * M.rptfKx (1 + M.eqsBt) 1 M.eqsMMt (M.eqsTk + M.eqsBt) + 1

/-- The bound of the `K_A` argument (top). -/
def eqsKAt (r₀ : ℝ) : ℝ :=
  M.naKA (M.ctVT 1) (M.rptfWT 1 M.eqsMMt) (M.rptfKx (1 + M.eqsBt) 1 M.eqsMMt (M.eqsTk + M.eqsBt)) r₀

/-- `(2ι(v_T, w_T)A)^{L²}` at the top bounds. -/
def eqsIt : ℝ := (2 * rpIota (M.ctVT 1) (M.rptfWT 1 M.eqsMMt) * M.core.A) ^ (L ^ 2)

/-- The bound of the `K_E` argument (top). -/
def eqsKEt (r₀ : ℝ) : ℝ := M.rpKE M.eqsIt r₀

/-- The mass coefficients (top case). -/
def eqsLmt (r₀ : ℝ) : List ℝ :=
  [2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * M.eqsIt + 1) * M.core.ℓ ^ 2),
    2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * M.eqsVWKt * M.core.ℓ ^ 2)]

/-- The waiting constant (top). -/
def eqsKWt : ℝ :=
  2 * (M.eqsTw + M.eqsTk / (8 * M.core.Bk)) + 4 * (M.eqsTh 0 * M.eqsK2) +
    32 * M.core.A ^ 4 * kθ0 L M.core.A M.core.C₀o M.core.ηo * M.eqsTk + M.eqsTw + M.eqsTk

theorem cw2Thb_self (Nh : ℕ) : cw2Thb M Nh Nh = M.eqsTh 0 := by
  unfold cw2Thb eqsTh; simp

theorem eqs_rptfWT_nonneg {r mm : ℝ} (hCw : 0 ≤ M.core.Cw) (hr : 0 ≤ r) : 0 ≤ M.rptfWT r mm := by
  unfold rptfWT
  have h0 : 0 ≤ (L : ℝ) ^ 2 * (M.core.Cw * (r + mm ^ 2)) := by positivity
  linarith [Real.add_one_le_exp ((L : ℝ) ^ 2 * (M.core.Cw * (r + mm ^ 2)))]

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The size parameters of the top case** (see the module docstring). -/
theorem eqs_top_pkg {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (x y : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh) (hrk : r ≤ ms)
    (hdist : supNorm (y - x) ≤ L ^ (ms - r)) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcab : 0 < M.k2cab) (hBk : 0 < M.core.Bk) {J : ℕ} (hJN : J ≤ Nh)
    (hG1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ eqsThr (M.eqsLt r₀))
    (hz : zA L m ms ≤ eqsThr (M.eqsLt r₀))
    (hX1 : m * (L : ℝ) ^ (2 * N) ≤ eqsThr (M.eqsLmt r₀))
    (hW : (3 / 4) ^ (J - ms) * M.eqsKWt ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2) :
    M.EqcTopPkg R m b Nh r₀ x y ms r (M.eqsKAt r₀) (M.eqsKEt r₀) := by
  intro kk ww hkk hww hMR
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
  -- the three couplings
  have hGp := hgp Nh le_rfl
  have hgmp := hgp ms hkN.le
  have hgm1 := hg1 ms hkN.le
  have hG1' := hg1 Nh le_rfl
  have hgmG := M.eqs_traj_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hkN.le le_rfl
  -- the thresholds
  have hthr : ∀ a ∈ M.eqsLt r₀, ∀ g' : ℝ, 0 ≤ g' →
      g' ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 → a * g' ≤ 1 :=
    fun a ha g' h0 h => eqs_le_thr ha h0 (h.trans hG1)
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.1.le (by positivity)
  have hthm : ∀ a ∈ M.eqsLmt r₀, a * (m * (L : ℝ) ^ (2 * N)) ≤ 1 :=
    fun a ha => eqs_le_thr ha hX0 hX1
  have fc := hthr M.core.c (by unfold eqsLt; simp) _ hGp.le le_rfl
  have hcG0 : 0 < M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by positivity
  have hcG1 : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 := fc
  -- `hs0`, `hs` at `ms`
  have hz0 := zA_nonneg L hm.1.le ms
  have fK1 := hthr (4 * M.Kp) (by unfold eqsLt; simp) _ hgmp.le hgmG
  have fK2 := eqs_le_thr (l := M.eqsLt r₀) (a := 4 * M.Kp) (by unfold eqsLt; simp) hz0 hz
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
  have hTh := M.eqsTh_pos 0
  have hq : (0 : ℝ) ≤ (3 / 4) ^ (Nh - ms) := by positivity
  have hKWn : 0 ≤ M.eqsTk / (8 * M.core.Bk) := div_nonneg hTk0 (by positivity)
  have hKWa : 0 ≤ M.eqsTh 0 * M.eqsK2 := mul_nonneg hTh.le hK₂
  have hθ0 : 0 ≤ kθ0 L M.core.A M.core.C₀o M.core.ηo := by
    unfold kθ0
    exact mul_nonneg M.core.hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hKWb : 0 ≤ M.core.A ^ 4 * kθ0 L M.core.A M.core.C₀o M.core.ηo * M.eqsTk := by positivity
  have hKW0 : 0 ≤ M.eqsKWt := by unfold eqsKWt; positivity
  have hW : (3 / 4) ^ (Nh - ms) * M.eqsKWt ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (show J - ms ≤ Nh - ms by omega)) hKW0) hW
  have hKWge : ∀ X, X ≤ M.eqsKWt → (3 / 4) ^ (Nh - ms) * X ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 := fun X hX =>
    (mul_le_mul_of_nonneg_left hX hq).trans hW
  have hnn : Nh - ms ≤ Nh - ms := by omega
  have hg2le : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 := by
    rw [sq]; exact mul_le_of_le_one_right hgmp.le hgm1
  -- W-d: `(7/30)^{n'}τ_w ≤ cǧ_{N_h}`
  have wd : (7 / 30 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
    have h1 := mul_le_mul (eqs_pow_le_of (a := 7 / 30) (by norm_num) (by norm_num) hnn) hτw hτw0 hq
    have h2 := hKWge M.eqsTw (by unfold eqsKWt; linarith)
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
    have h2 := hKWge M.eqsTk (by unfold eqsKWt; linarith)
    have h3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 ≤
        (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 :=
      pow_le_pow_left₀ hgmp.le (hgmG.trans (le_mul_of_one_le_left hGp.le (by linarith))) 2
    linarith
  -- W-c: `8A⁴θ₀(56/75)^nτ_k ≤ 1/4`
  have wc : M.core.A ^ 4 * (8 * kθ0 L M.core.A M.core.C₀o M.core.ηo * ((56 / 75 : ℝ) ^ (Nh - ms) *
      ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
      (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
        (M.pl5M0 R m b x y ms r))))) ≤ 1 / 4 := by
    have h1 := mul_le_mul (eqs_pow_le_of (a := 56 / 75) (by norm_num) (by norm_num) le_rfl) hτk
      hτk0 hq
    have h2 := hKWge (32 * M.core.A ^ 4 * kθ0 L M.core.A M.core.C₀o M.core.ηo * M.eqsTk)
      (by unfold eqsKWt; linarith)
    have hA4 : 0 ≤ M.core.A ^ 4 * (8 * kθ0 L M.core.A M.core.C₀o M.core.ηo) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hA4
    have h4 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 ≤ 1 := hg2le.trans hgm1
    have e : (3 / 4 : ℝ) ^ (Nh - ms) * (32 * M.core.A ^ 4 * kθ0 L M.core.A M.core.C₀o M.core.ηo *
        M.eqsTk) = 4 * (M.core.A ^ 4 * (8 * kθ0 L M.core.A M.core.C₀o M.core.ηo) *
          ((3 / 4 : ℝ) ^ (Nh - ms) * M.eqsTk)) := by ring
    have e2 : M.core.A ^ 4 * (8 * kθ0 L M.core.A M.core.C₀o M.core.ηo * ((56 / 75 : ℝ) ^ (Nh - ms) *
      ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
      (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
        (M.pl5M0 R m b x y ms r))))) = M.core.A ^ 4 * (8 * kθ0 L M.core.A M.core.C₀o M.core.ηo) *
      ((56 / 75 : ℝ) ^ (Nh - ms) *
      ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
      (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
        (M.pl5M0 R m b x y ms r)))) := by ring
    linarith
  have hGN0 := hGp.le
  have hcGN0 : 0 ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := hcG0.le
  have hc0 : 0 ≤ M.core.c := by linarith
  have hcx0 : 0 ≤ cx M.core.κ M.core.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id M.core.hC2
    unfold cx; exact (div_pos (by linarith) (by linarith)).le
  have hΘe := M.cw2Thb_self Nh
  have hp2 : (56 / 75 : ℝ) ^ (Nh - ms) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hBk0 := hcst.2.2.2.2.2.2.1
  -- `mm`
  obtain ⟨hm1a, hm1c, hm1W⟩ := eqs_mm hcW hcG0 (by positivity) wd
  set m1 := max 1 (M.core.cWo + (7 / 30 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) with hm1d
  have hcWm1 : M.core.cWo ≤ m1 := by
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ (7 / 30 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) := by positivity
    linarith
  have hmm1 : 1 ≤ (1 + M.eqsTh 0) * m1 := one_le_mul_of_one_le_of_one_le (by linarith) hm1a
  have c3 : 1 + cw2Thb M Nh Nh ≤ (1 + M.eqsTh 0) * m1 := by
    rw [hΘe]; have := mul_le_mul_of_nonneg_left hm1a (by linarith : (0 : ℝ) ≤ 1 + M.eqsTh 0)
    linarith
  have c4 : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + (7 / 30) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
      cw2Thb M Nh Nh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * ((1 + M.eqsTh 0) * m1) := by
    rw [hΘe]
    have a := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcWm1 hcGN0) hTh.le
    have e : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * ((1 + M.eqsTh 0) * m1) = M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * m1 +
        M.eqsTh 0 * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * m1) := by ring
    have e2 : M.eqsTh 0 * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) =
        M.eqsTh 0 * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * M.core.cWo) := by ring
    linarith
  have hmmc : (1 + M.eqsTh 0) * m1 ≤ M.eqsMMt :=
    mul_le_mul_of_nonneg_left hm1c (by linarith)
  set mm := (1 + M.eqsTh 0) * m1 with hmmd
  have hmm0 : (0 : ℝ) ≤ mm := by linarith
  -- `k₁`, `c₁`
  have hBt : 0 ≤ M.eqsBt := by unfold eqsBt; positivity
  obtain ⟨hc₁, hk₁, hc₁b⟩ := eqs_k1 hBt hcG0 (by positivity) we hmm1
  have hk1e : (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 +
      cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) =
      (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + M.eqsBt * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 := by
    rw [hΘe]; unfold eqsBt; ring
  set k₁ := (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + M.eqsBt * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 with hk₁d
  set c₁ := k₁ / ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm) with hc₁d
  have hk₁0 : 0 ≤ k₁ := by positivity
  have hk₁b : k₁ ≤ M.eqsTk + M.eqsBt := by
    have a : (56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.eqsTk := (mul_le_of_le_one_left hτk0 hp2).trans hτk
    have := mul_le_mul_of_nonneg_left (pow_le_one₀ hcGN0 hcG1 : (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 ≤ 1) hBt
    linarith
  -- `hkt`
  have c8 := eqs_kt_pure (cx := cx M.core.κ M.core.cT) hBt hcx0 hc₁b hc0 hGN0 hG1' rfl hε₀
    (hthr _ (by unfold eqsLt; simp) _ hGN0 le_rfl)
  -- `Q₀`, waiting
  have hcgm : 0 < M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 := by positivity
  obtain ⟨c9, c10, c11⟩ := eqs_Q (a := (7 / 5 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))))
    (b := (7 / 5 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r)))) (by positivity) (by positivity) hcgm hBk
  have hsup : ((supNorm (y - x) : ℕ) : ℝ) ≤ (L : ℝ) ^ ms := by
    have h1 : supNorm (y - x) ≤ L ^ ms :=
      hdist.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega))
    exact_mod_cast h1
  have hZ1 := M.eqs_zab_le N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD x y (J := Nh) r hk0 hkN
    hs0 hs hsup hcab (by linarith) hgm1
  have hthb := M.eqs_thb_ms (Cδ := 0) (J := Nh) (Nh := Nh) (by omega) hkN.le
  have hZ : zabZr M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) Nh Nh /
      (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1)) ≤
      (7 / 5) ^ (Nh - ms) * (M.eqsTh 0 * (81 / 56) ^ (Nh - ms)) * M.eqsK2 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 := by
    refine hZ1.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hthb (by positivity)) hK₂
  have c12 : (8 / 15 : ℝ) ^ (Nh - ms) * zabQ M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r)
      Nh Nh ((7 / 5 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) +
        (7 / 5 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2)) ≤ 1 := by
    unfold zabQ
    have := eqs_wait_pure (n := Nh - ms) hgmp hgm1 (by linarith) hBk hτw0 hτw hτk0 hτk hTh.le hK₂ hZ
      (KW := M.eqsKWt) (by unfold eqsKWt; linarith) hW
    simpa only [mul_div_assoc] using this
  -- `hsmT`
  have hKx := eqs_kx_top (θ := kθ0 L M.core.A M.core.C₀o M.core.ηo) (C₁ := M.core.C₁k) (kb := kB (kθ0 L M.core.A M.core.C₀o M.core.ηo) M.core.C₁k (8 * cx M.core.κ M.core.cT)) (T := M.eqsTk) (MM := M.eqsMMt)
    (c₁ := c₁) hθ0 M.core.hC₁k hcx0 (by unfold kB; have := M.core.hC₁k; positivity) hc0 hGN0 hG1'
    hcG1 hc₁b (by positivity) ((mul_le_of_le_one_left hτk0 hp2).trans hτk) hBt hmm0 hmmc
  have hkb0 := M.k2mbar_nonneg Nh Nh
  have hkbK := M.k2mbar_le_eqsKb (Nh := Nh) (j := Nh) (Cδ := 0) (by omega)
  have hent := hthr (2 * M.core.A ^ 4 * (M.core.Cf + M.eqsQt + M.k2cab / 5 * M.core.c * M.eqsKb 0 ^ 2))
    (by unfold eqsLt; simp) _ hGN0 le_rfl
  have hCf : 0 ≤ M.core.Cf := M.flow.2.2.2.2.2.2.2.2.2.2.1
  have hG3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
    have : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 ≤ 1 := pow_le_one₀ hGN0 hG1'
    calc (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 = (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 := by ring
      _ ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * 1 := mul_le_mul_of_nonneg_left this hGN0
      _ = (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := mul_one _
  have hk2b : M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2) ≤
      M.k2cab / 5 * M.core.c * M.eqsKb 0 ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
    have := pow_le_pow_left₀ hkb0 hkbK 2
    have h1 := mul_le_mul_of_nonneg_left this (show 0 ≤ M.k2cab / 5 * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) by positivity)
    have e : M.k2cab / 5 * M.core.c * M.eqsKb 0 ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 =
        M.k2cab / 5 * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * M.eqsKb 0 ^ 2 := by ring
    have e2 : M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2) =
        M.k2cab / 5 * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2 := by ring
    linarith
  have c15 : M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 + M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ +
      M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2)) ≤ 1 := by
    have hKx' : M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ ≤
        8 * kθ0 L M.core.A M.core.C₀o M.core.ηo * ((56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r)))) + M.eqsQt * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
      unfold rptfKx eqsQt; exact hKx
    have hA4 : 0 ≤ M.core.A ^ 4 := by positivity
    have s1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG3 hCf) hA4
    have s2 := mul_le_mul_of_nonneg_left hKx' hA4
    have s3 := mul_le_mul_of_nonneg_left hk2b hA4
    have e : M.core.A ^ 4 * (8 * kθ0 L M.core.A M.core.C₀o M.core.ηo * ((56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r)))) + M.eqsQt * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) =
        M.core.A ^ 4 * (8 * kθ0 L M.core.A M.core.C₀o M.core.ηo * ((56 / 75 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))))) +
          M.core.A ^ 4 * M.eqsQt * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by ring
    have e2 : 2 * M.core.A ^ 4 * (M.core.Cf + M.eqsQt + M.k2cab / 5 * M.core.c * M.eqsKb 0 ^ 2) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 = 2 * (M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.core.A ^ 4 * M.eqsQt * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 +
          M.core.A ^ 4 * (M.k2cab / 5 * M.core.c * M.eqsKb 0 ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) := by ring
    have e3 : M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 + M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ +
      M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2)) = M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3) +
        M.core.A ^ 4 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ +
        M.core.A ^ 4 * (M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2)) := by ring
    linarith
  -- the mass windows, `K_A`, `K_E`
  have hcJ := eqs_cJ_nonneg (L := L) hr₀
  have hV := M.eqs_ctVT_mono hcGN0 hcG1
  have hWm := M.eqs_rptfWT_mono hCw hmm0 hcG1 hmmc
  have hKxm := M.eqs_rptfKx_mono hc₁ hcGN0 hmm0 hk₁0 hc₁b hcG1 hmmc hk₁b
  have hW0 := M.eqs_rptfWT_nonneg (r := M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) (mm := mm) hCw hcGN0
  have hι := eqs_rpIota_mono hW0 hV hWm
  have hι1 := one_le_rpIota (show 0 ≤ M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) by
    unfold MasterFacts.ctVT; positivity) hW0
  have hIt : (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)
      ≤ M.eqsIt := by
    unfold eqsIt
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hι (by norm_num)) (by linarith)) _
  have c16 : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * (2 * rpIota
      (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show 8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
        (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2) + 1 ≤ 8 * M.eqsIt + 1 by linarith) hcJ)
      (sq_nonneg M.core.ℓ)) (by norm_num : (0 : ℝ) ≤ 2)) hX0
    rw [mul_assoc]
    exact h.trans (hthm _ (by unfold eqsLmt; simp))
  have hsum : M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm +
      8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1 ≤ M.eqsVWKt := by
    unfold eqsVWKt; linarith
  have c17 : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm +
        8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum hcJ) (sq_nonneg M.core.ℓ)) (by norm_num : (0 : ℝ) ≤ 2)) hX0
    rw [mul_assoc]
    exact h.trans (hthm _ (by unfold eqsLmt; simp))
  have c18 : M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm)
      (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ ≤ M.eqsKAt r₀ :=
    M.eqs_naKA_mono hr₀ (by linarith)
  have c19 : M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
      M.core.A) ^ (L ^ 2)) r₀ ≤ M.eqsKEt r₀ := M.eqs_rpKE_mono hr₀ hIt
  refine ⟨mm, k₁, c₁, M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2),
    (7 / 5 : ℝ) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) +
      (7 / 5 : ℝ) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2),
    hc₁, by positivity, c3, c4, hcG1.trans hmm1, le_of_eq hk1e, hk₁, c8, c9, c10, c11, c12, le_rfl,
    c15, c16, c17, c18, c19⟩

end MasterFacts

end

end Spin2
