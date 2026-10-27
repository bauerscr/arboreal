import Spin2.Cont.ContEqS5
import Spin2.Cont.ContEqC5
import Spin2.Cont.ContEqS0

set_option autoImplicit false

/-!
# B3, `r`-dependent form: the size parameters of the intermediate case

**`MasterFacts.eqs_mid_params`**: for the inner statement of `fin_T6_mid` (equally of the
parallel `eqc_mid`, same hypotheses), with an arbitrary conclusion `Concl`, the explicit choice
`v_T = 1 + Θ(C_δ)`, `w_T = eqsWT`, `w₂ = eqsW2`, `m₀ = eqsM0`, `k₂ = c_{ab}r_{j_y}k̄²`,
`Q₀ = (7/5)^n(τ_w/(cǧ_{ms}) + τ_k/(8B(cǧ_{ms})²))`, `mm = max(1, c_W + (7/30)^{n'}τ_w/(cǧ_{N_h}))`,
`k₁ = (56/75)^{n'}τ_k + 8c_WB(cǧ_{N_h})²`, `c₁ = k₁/((cǧ_{N_h})²mm)` discharges every size
hypothesis, given
* `ǧ_{N_h}, a_{ms} ≤ eqsThr(eqsLg r₀ C_δ)` (one threshold for all `ǧ`-type conditions),
* `m²L^{2N} ≤ eqsThr(eqsLm …)` (one threshold for all mass windows),
* the waiting hypothesis `(3/4)^{j_y − ms}·eqsKW(C_δ) ≤ ǧ_{ms}²`,
* `N ≤ j_y + C_δ`.
It also bounds the `K_A` argument: `naKA(…) ≤ eqsKA r₀`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- The `ǧ`-type coefficients (intermediate case). -/
def eqsLg (r₀ : ℝ) (Cδ : ℕ) : List ℝ :=
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
    32 * M.core.A ^ 4 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * (1 + M.eqsTh Cδ),
    4 * M.core.A ^ 4 * M.k2cab * M.core.c * M.eqsKb Cδ ^ 2,
    8 * (cx M.core.κ M.core.cT + 1 + 8 * M.core.cWo * M.core.Bk) * M.core.c ^ 3 / M.core.ε₀,
    M.core.c]

/-- `V + W + 8K + 1` at the bounds `cǧ ≤ 1`, `mm ≤ c_W + 1`, `c₁ ≤ 1 + 8c_WB`, `k₁ ≤ τ_k + 8c_WB`. -/
def eqsVWK : ℝ :=
  M.ctVT 1 + M.rptfWT 1 (M.core.cWo + 1) +
    8 * M.rptfKx (1 + 8 * M.core.cWo * M.core.Bk) 1 (M.core.cWo + 1)
      (M.eqsTk + 8 * M.core.cWo * M.core.Bk) + 1

/-- The bound of the `K_A` argument. -/
def eqsKA (r₀ : ℝ) : ℝ :=
  M.naKA (M.ctVT 1) (M.rptfWT 1 (M.core.cWo + 1))
    (M.rptfKx (1 + 8 * M.core.cWo * M.core.Bk) 1 (M.core.cWo + 1)
      (M.eqsTk + 8 * M.core.cWo * M.core.Bk)) r₀

/-- The mass coefficients (intermediate case). -/
def eqsLm (r₀ Kt C₁w C₁t C₁v C₁m Λ₁ : ℝ) (Cδ : ℕ) : List ℝ :=
  [2 * Kt,
    8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3,
    2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      ((rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m Cδ) Cδ) +
        (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m Cδ) Cδ) +
        8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m Cδ) Cδ)) + 1) * M.core.ℓ ^ 2),
    2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * M.eqsVWK * M.core.ℓ ^ 2)]

/-- The waiting constant. -/
def eqsKW (Cδ : ℕ) : ℝ :=
  2 * (M.eqsTw + M.eqsTk / (8 * M.core.Bk)) + 4 * (M.eqsTh Cδ * M.eqsK2) +
    4 * M.core.A ^ 4 * M.eqsTk + M.eqsTw + M.eqsTk

end MasterFacts

theorem eqs_cJ_nonneg {r₀ : ℝ} (hr₀ : 0 < r₀) : 0 ≤ 81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) := by
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
  have h1 : 0 ≤ cJet L := by
    unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
  have h2 : 0 ≤ cRho L := by
    unfold cRho
    have : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
    have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
    refine mul_nonneg hL2 ?_
    nlinarith
  have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
  positivity

/-- `Θ_b(ms) ≤ Θ(C_δ)(81/56)^{J−ms}` for `N_h ≤ J + C_δ`, `ms ≤ J`. -/
theorem MasterFacts.eqs_thb_ms (M : MasterFacts L) {Nh J ms Cδ : ℕ} (hJ : Nh ≤ J + Cδ)
    (hms : ms ≤ J) : cw2Thb M Nh ms ≤ M.eqsTh Cδ * (81 / 56) ^ (J - ms) := by
  unfold cw2Thb MasterFacts.eqsTh
  have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 81 / 56 by norm_num)
    (show Nh - ms ≤ Cδ + (J - ms) by omega)
  rw [pow_add] at h
  calc _ ≤ Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) *
        ((81 / 56 : ℝ) ^ Cδ * (81 / 56) ^ (J - ms)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by ring

omit [NeZero L] in
/-- `a^{n'} ≤ (3/4)^n` for `0 ≤ a ≤ 3/4`, `n ≤ n'`. -/
theorem eqs_pow_le_of {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 3 / 4) {n n' : ℕ} (h : n ≤ n') :
    a ^ n' ≤ (3 / 4 : ℝ) ^ n :=
  (pow_le_pow_left₀ ha ha' n').trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) h)

omit [NeZero L] in
/-- `Y ≤ v(k(Y s))` for `1/(vk) ≤ s` (the `h8*` conditions). -/
theorem eqs_h8 {Y v k s : ℝ} (hY : 0 ≤ Y) (hv : 0 < v) (hk : 0 < k) (hs : 1 / (v * k) ≤ s) :
    Y ≤ v * (k * (Y * s)) := by
  have h1 : 1 ≤ v * k * s := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hs
  have e : v * (k * (Y * s)) = Y * (v * k * s) := by ring
  rw [e]; nlinarith

omit [NeZero L] in
/-- The choice of `mm`. -/
theorem eqs_mm {cW G t : ℝ} (hcW : 1 ≤ cW) (hG : 0 < G) (ht : 0 ≤ t) (htG : t ≤ G) :
    1 ≤ max 1 (cW + t / G) ∧ max 1 (cW + t / G) ≤ cW + 1 ∧
      cW * G + t ≤ G * max 1 (cW + t / G) := by
  have h1 : t / G ≤ 1 := by rw [div_le_one hG]; exact htG
  have h0 : 0 ≤ t / G := div_nonneg ht hG.le
  refine ⟨le_max_left _ _, max_le (by linarith) (by linarith), ?_⟩
  have := mul_le_mul_of_nonneg_left (le_max_right 1 (cW + t / G)) hG.le
  have e : G * (cW + t / G) = cW * G + t := by field_simp
  linarith

omit [NeZero L] in
/-- The choice of `k₁`, `c₁`. -/
theorem eqs_k1 {B G u mm : ℝ} (hB : 0 ≤ B) (hG : 0 < G) (hu : 0 ≤ u) (huG : u ≤ G ^ 2)
    (hmm : 1 ≤ mm) :
    0 ≤ (u + B * G ^ 2) / (G ^ 2 * mm) ∧
      u + B * G ^ 2 ≤ (u + B * G ^ 2) / (G ^ 2 * mm) * G ^ 2 * mm ∧
      (u + B * G ^ 2) / (G ^ 2 * mm) ≤ 1 + B := by
  have hG2 : 0 < G ^ 2 := by positivity
  have hd : 0 < G ^ 2 * mm := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · rw [mul_assoc, div_mul_cancel₀ _ hd.ne']
  · rw [div_le_iff₀ hd]
    have : G ^ 2 ≤ G ^ 2 * mm := le_mul_of_one_le_right hG2.le hmm
    nlinarith

omit [NeZero L] in
/-- The explicit `Q₀`. -/
theorem eqs_Q {a b u B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < u) (hB : 0 < B) :
    0 ≤ a / u + b / (8 * B * u ^ 2) ∧ a ≤ u * (a / u + b / (8 * B * u ^ 2)) ∧
      b ≤ 8 * B * u ^ 2 * (a / u + b / (8 * B * u ^ 2)) := by
  have h1 : 0 ≤ a / u := by positivity
  have h2 : 0 ≤ b / (8 * B * u ^ 2) := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · rw [mul_add, mul_div_cancel₀ _ hu.ne']
    have : 0 ≤ u * (b / (8 * B * u ^ 2)) := by positivity
    linarith
  · rw [mul_add, mul_div_cancel₀ _ (by positivity)]
    have : 0 ≤ 8 * B * u ^ 2 * (a / u) := by positivity
    linarith

omit [NeZero L] in
/-- `hsmT` (pure). -/
theorem eqs_smT_pure {A4 cx g u cW Bk c TH Θ cab kb Kb : ℝ} (hA : 0 ≤ A4) (hcx : 0 ≤ cx)
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hcW : 0 ≤ cW) (hBk : 0 ≤ Bk) (hc : 0 ≤ c) (hTH : 0 ≤ TH)
    (hTΘ : TH ≤ Θ) (hcab : 0 ≤ cab) (hkb : 0 ≤ kb) (hkK : kb ≤ Kb) (hu : A4 * u ≤ 1 / 4)
    (h1 : 4 * A4 * cx * g ≤ 1) (h3 : 32 * A4 * cW * Bk * c ^ 2 * (1 + Θ) * g ≤ 1)
    (h4 : 4 * A4 * cab * c * Kb ^ 2 * g ≤ 1) :
    A4 * (cx * g ^ 3 + (u + 8 * cW * Bk * (c * g) ^ 2 + TH * (8 * cW * Bk * (c * g) ^ 2)) +
      cab * (c * g) * kb ^ 2) ≤ 1 := by
  have hg3 : g ^ 3 ≤ g := by
    have : g ^ 2 ≤ 1 := pow_le_one₀ hg hg1
    calc g ^ 3 = g * g ^ 2 := by ring
      _ ≤ g * 1 := mul_le_mul_of_nonneg_left this hg
      _ = g := mul_one g
  have hg2 : g ^ 2 ≤ g := by rw [sq]; exact mul_le_of_le_one_right hg hg1
  have t1 : A4 * (cx * g ^ 3) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg3 hcx) hA
    nlinarith
  have hX : 8 * cW * Bk * (c * g) ^ 2 + TH * (8 * cW * Bk * (c * g) ^ 2) ≤
      8 * cW * Bk * c ^ 2 * (1 + Θ) * g := by
    have e : 8 * cW * Bk * (c * g) ^ 2 + TH * (8 * cW * Bk * (c * g) ^ 2) =
        8 * cW * Bk * c ^ 2 * (1 + TH) * g ^ 2 := by ring
    rw [e]
    have hk : 0 ≤ 8 * cW * Bk * c ^ 2 := by positivity
    have hΘ : 0 ≤ Θ := hTH.trans hTΘ
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hk) hg2 (by positivity)
      (by positivity)
  have t3 : A4 * (8 * cW * Bk * (c * g) ^ 2 + TH * (8 * cW * Bk * (c * g) ^ 2)) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hX hA
    have e : A4 * (8 * cW * Bk * c ^ 2 * (1 + Θ) * g) =
        (32 * A4 * cW * Bk * c ^ 2 * (1 + Θ) * g) / 4 := by ring
    linarith
  have hY : cab * (c * g) * kb ^ 2 ≤ cab * c * Kb ^ 2 * g := by
    have : kb ^ 2 ≤ Kb ^ 2 := pow_le_pow_left₀ hkb hkK 2
    have e : cab * (c * g) * kb ^ 2 = cab * c * g * kb ^ 2 := by ring
    rw [e, mul_right_comm (cab * c) (Kb ^ 2) g]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have t4 : A4 * (cab * (c * g) * kb ^ 2) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hY hA
    have e : A4 * (cab * c * Kb ^ 2 * g) = (4 * A4 * cab * c * Kb ^ 2 * g) / 4 := by ring
    linarith
  have e : A4 * (cx * g ^ 3 + (u + 8 * cW * Bk * (c * g) ^ 2 + TH * (8 * cW * Bk * (c * g) ^ 2)) +
      cab * (c * g) * kb ^ 2) = A4 * (cx * g ^ 3) + A4 * u +
        A4 * (8 * cW * Bk * (c * g) ^ 2 + TH * (8 * cW * Bk * (c * g) ^ 2)) +
        A4 * (cab * (c * g) * kb ^ 2) := by ring
  rw [e]; linarith

omit [NeZero L] in
/-- `hkt` (pure). -/
theorem eqs_kt_pure {cx c₁ c G P ε₀ B : ℝ} (hB : 0 ≤ B) (hcx : 0 ≤ cx) (hc₁b : c₁ ≤ 1 + B)
    (hc : 0 ≤ c) (hG : 0 ≤ G) (hG1 : G ≤ 1) (hP : P = 8 * (cx + 1 + B) * c ^ 3) (hε : 0 < ε₀)
    (h : P / ε₀ * G ≤ 1) : 8 * (cx + c₁) * (c * G) ^ 3 ≤ ε₀ := by
  have h1 : P * G ≤ ε₀ := eqs_le_of_div hε h
  have hG3 : G ^ 3 ≤ G := by
    have : G ^ 2 ≤ 1 := pow_le_one₀ hG hG1
    calc G ^ 3 = G * G ^ 2 := by ring
      _ ≤ G * 1 := mul_le_mul_of_nonneg_left this hG
      _ = G := mul_one G
  have e : 8 * (cx + c₁) * (c * G) ^ 3 = 8 * (cx + c₁) * c ^ 3 * G ^ 3 := by ring
  rw [e]
  have : 8 * (cx + c₁) * c ^ 3 * G ^ 3 ≤ 8 * (cx + 1 + B) * c ^ 3 * G :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hG3 (by positivity)
      (by positivity)
  rw [hP] at h1; linarith

namespace MasterFacts

variable (M : MasterFacts L)

/-- `ǧ_j ≤ ǧ_k` for `j ≤ k ≤ N_h` along `D_ε`. -/
theorem eqs_traj_mono {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ Nh) :
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := by
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have key : ∀ n, j + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (j + n)).1 := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (j + n) (by omega))
  have := key (k - j) (by omega)
  rwa [show j + (k - j) = k by omega] at this

end MasterFacts

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The size parameters of the intermediate case** (see the module docstring). -/
theorem eqs_mid_pkg {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    (hG1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ eqsThr (M.eqsLg r₀ Cδ))
    (hz : zA L m ms ≤ eqsThr (M.eqsLg r₀ Cδ))
    (hX1 : m * (L : ℝ) ^ (2 * N) ≤ eqsThr (M.eqsLm r₀ Kt C₁w C₁t C₁v C₁m Λ₁ Cδ))
    (hW : (3 / 4) ^ (J - ms) * M.eqsKW Cδ ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2) :
    M.EqcMidPkg C₁w C₁t C₁v C₁m Λ₁ Λ₂ R m b Nh r₀ x y ms r Cδ (M.eqsKA r₀)
      (M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m Cδ) Cδ) Cδ) := by
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
  have hthr : ∀ a ∈ M.eqsLg r₀ Cδ, ∀ g' : ℝ, 0 ≤ g' →
      g' ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 → a * g' ≤ 1 :=
    fun a ha g' h0 h => eqs_le_thr ha h0 (h.trans hG1)
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.1.le (by positivity)
  have hthm : ∀ a ∈ M.eqsLm r₀ Kt C₁w C₁t C₁v C₁m Λ₁ Cδ, a * (m * (L : ℝ) ^ (2 * N)) ≤ 1 :=
    fun a ha => eqs_le_thr ha hX0 hX1
  have fc := hthr M.core.c (by unfold eqsLg; simp) _ hGp.le le_rfl
  have hcG0 : 0 < M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by positivity
  have hcG1 : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 := fc
  -- `hs0`, `hs` at `ms`
  have hz0 := zA_nonneg L hm.1.le ms
  have fK1 := hthr (4 * M.Kp) (by unfold eqsLg; simp) _ hgmp.le hgmG
  have fK2 := eqs_le_thr (l := M.eqsLg r₀ Cδ) (a := 4 * M.Kp) (by unfold eqsLg; simp) hz0 hz
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
  have hTH0 : 0 ≤ cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y) := M.cw2Thb_nonneg _ _
  have hTHΘ : cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y) ≤ M.eqsTh Cδ := M.cw2Thb_le_eqsTh hJd
  have hp1 : (7 / 30 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp2 : (56 / 75 : ℝ) ^ (Nh - ms) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hkb0 := M.k2mbar_nonneg Nh (Obs.coal L (0 : Lam 2 L N) y)
  have hkbK := M.k2mbar_le_eqsKb hJd
  -- 1, 2: `v_T`, `w_T`
  have c1 : 1 + cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y) ≤ M.eqsVT Cδ := by unfold eqsVT; linarith
  have c2 : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) + (7 / 30) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1)) + M.eqsW2 Cδ ≤ M.eqsWT Cδ := by
    unfold eqsWT
    have a := mul_le_mul_of_nonneg_left hcGJ (by linarith : (0 : ℝ) ≤ M.core.cWo)
    have b' : (7 / 30 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.eqsTw :=
      (mul_le_of_le_one_left hτw0 hp1).trans hτw
    have c' := mul_le_mul hTHΘ a (by positivity) hTh.le
    linarith
  -- 4: `w₂ ≥ 0`
  have c4 : 0 ≤ M.eqsW2 Cδ := by
    unfold eqsW2
    have h0 : 0 ≤ (L : ℝ) ^ 2 * (M.core.Cw * (M.core.c + (2 * M.eqsKb Cδ) ^ 2)) := by positivity
    linarith [Real.add_one_le_exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c + (2 * M.eqsKb Cδ) ^ 2)))]
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
  have c10 : Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ((Obs.coal L (0 : Lam 2 L N) y) - 1)).1 + (2 * k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y)) ^ 2))) - 1 ≤ M.eqsW2 Cδ := by
    unfold eqsW2
    have hJ1 : (Obs.coal L (0 : Lam 2 L N) y) - 1 ≤ Nh := by omega
    have a : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ((Obs.coal L (0 : Lam 2 L N) y) - 1)).1 ≤ M.core.c := mul_le_of_le_one_right hc0 (hg1 _ hJ1)
    have b' : (2 * k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y)) ^ 2 ≤ (2 * M.eqsKb Cδ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add a b') hCw)
      (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    linarith [Real.exp_le_exp.2 this]
  have hcx0 : 0 ≤ cx M.core.κ M.core.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id M.core.hC2
    unfold cx; exact (div_pos (by linarith) (by linarith)).le
  -- 12: `hsmT`
  have c12 := eqs_smT_pure (A4 := M.core.A ^ 4) (cx := cx M.core.κ M.core.cT)
    (cW := M.core.cWo) (Bk := M.core.Bk) (c := M.core.c) (cab := M.k2cab) (Kb := M.eqsKb Cδ)
    (Θ := M.eqsTh Cδ) (u := (56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))))
    (TH := cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) (kb := k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y)) (by positivity) hcx0 hgJp.le hgJ1 (by linarith)
    hBk.le hc0 hTH0 hTHΘ hcab.le hkb0 hkbK wc
    (by have := hthr (4 * M.core.A ^ 4 * cx M.core.κ M.core.cT) (by unfold eqsLg; simp) _ hgJp.le hgJG
        linarith)
    (hthr _ (by unfold eqsLg; simp) _ hgJp.le hgJG)
    (hthr _ (by unfold eqsLg; simp) _ hgJp.le hgJG)
  -- 13–17: `m₀`
  have hvT0 : 0 ≤ M.eqsVT Cδ := by unfold eqsVT; linarith
  have hwT0 : 0 ≤ M.eqsWT Cδ := by
    unfold eqsWT; have := mul_nonneg hTh.le (by positivity : (0 : ℝ) ≤ M.core.cWo * M.core.c)
    have : 0 ≤ M.core.cWo * M.core.c := by positivity
    linarith
  have hι1 := one_le_rpIota hvT0 hwT0
  have hvw := vck_pos hC₁w
  have hvt := vck_pos hC₁t
  have hvv := vck_pos hC₁v
  have hvm := vck_pos hC₁m
  have hY : 0 ≤ 8 * (2 * rpIota (M.eqsVT Cδ) (M.eqsWT Cδ) * M.core.A) ^ ((L + 18) ^ 2) := by
    positivity
  have s1 : 0 < 1 / (vck C₁w * (4 * C₁w + 1)) := by positivity
  have s2 : 0 < 1 / (vck C₁t * (4 * C₁t + 1)) := by positivity
  have s3 : 0 < 1 / (vck C₁v * (4 * C₁v + 1)) := by positivity
  have s4 : 0 < 1 / (vck C₁m * (4 * C₁m + 1)) := by positivity
  have c13 : 0 < M.eqsM0 C₁w C₁t C₁v C₁m Cδ := by unfold eqsM0; positivity
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
      ((rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m Cδ) Cδ) +
        (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m Cδ) Cδ) +
        8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ (M.eqsM0 C₁w C₁t C₁v C₁m Cδ) Cδ)) + 1) * M.core.ℓ ^ 2))
    (by unfold eqsLm; simp)
  -- 25: `hkt`
  have c25 := eqs_kt_pure (cx := cx M.core.κ M.core.cT) hB8 hcx0 hc₁b hc0 hGN0 hG1' rfl hε₀
    (hthr _ (by unfold eqsLg; simp) _ hGN0 le_rfl)
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
    exact h.trans (hthm _ (by unfold eqsLm; simp))
  refine ⟨M.eqsVT Cδ, M.eqsWT Cδ,
    (56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2 +
      cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y) * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2),
    M.eqsW2 Cδ, M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) * k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y) ^ 2,
    M.eqsM0 C₁w C₁t C₁v C₁m Cδ,
    (7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) +
      (7 / 5 : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) / (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2),
    mm, k₁, c₁, c1, c2, le_rfl, c4, by positivity, c6, c7, c8, c9, c10, le_rfl, c12, c13, c14,
    c15, c16, c17, by rw [mul_assoc]; exact c18, hc₁, hmm1, hmmW, hcG1.trans hmm1, le_rfl, hk₁,
    c25, c26, c27, le_rfl⟩


end MasterFacts

end

end Spin2
