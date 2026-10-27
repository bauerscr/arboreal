import Spin2.Final.FinalNF
import Spin2.H0.H0OnePtW

/-!
# `thm:multiscale` at `h = 0` at the shooting value `β_ε = 1/b` (route (a1))

`thm_multiscale_h0_shoot` hits every target `y` between two windowed bracket ends, but `FwAt` at the
shooting value `b` still needed an admissible `μ^c` at `b` in the mass range with `ǧ^c ≤ g₀`. This
is closed here from the fixed-`β_R` flow conclusions `FixedConcl` (part of `FlowC2Concl`, i.e. of
`M.core.hC2`):

* `Ufix` (admissible, `ǧ^c_{N_h} < ε`) is order-connected (`FixedConcl.ordConnected`), and
  `b ↦ ǧ^c_{N_h}(b)` is strictly increasing on the admissible `b` (`FixedConcl.strictMono`). So for
  `b ∈ [b₁, b₂]` with `b₁, b₂ ∈ Ufix`, `(b, μ^c(b))` is admissible and
  `ǧ^c(b₁) ≤ ǧ^c(b) ≤ ǧ^c(b₂)`: the mass and `g₀` conditions at `b` follow from those at the ends
  (`fb_ufix_between`).
* **Input (i) discharged** (`Spin2/H0/H0OnePtW`): `MasterFacts.fb_h0EndsGS` (`h0EndsG` at the `p_W`
  of `h0WindowX_ofS`, so `p_Wc_μ ≤ 1/12`), `MasterFacts.fw_atG` (`fw_at` from `H0EndsConclG`: no
  premise `r ≥ 0`), `MasterFacts.fb_small` (`H0OnePtSmall … ((5/4)ǧ^c)` from `ǧ^c ≤ G₁`,
  `m²L^{2N} ≤ ǧ^c` and `K_pa_{N_h−1} ≤ 1/2`), `fb_constsG` (`g₀ = min(g₀(fw_atG), G₁)`), with the
  per-`(b, μ^c)` conclusion **`FwRes`** (`D_ε`, distance, **`FwPairBdN`**: the pair bound with the
  non-seed pair layer `fw_pairAbove5_MFD'` of `Spin2/Final/FinalNF`, inputs `PairDefSizesNF`, `PairZeroRemAB`,
  constant `fwK5`).
* **`thm_multiscale_h0_bracket`**: for admissible bracket ends (mass condition at `b₁`, `ǧ^c ≤ g₀`
  at `b₂`), every `y` inside the margins is `Re ǧ_N(b, b − m²)` of some `b ∈ [b₁, b₂]` at which the
  `h = 0` trajectory is in `D_ε` and `FwPairBdN` holds.
* **`thm_multiscale_h0_beta`**: the bracket `b₁ = bFin(y/2)`, `b₂ = bFin(2y)`, `y = 1/β_R`, and the
  margin conditions `E'ᵢ` derived: for `N ≥ 3`, `K_pa_{N_h−1} ≤ 1/2`, and `0 < β_R` with
  `4m²L^{2N} ≤ 1/β_R ≤ g₀/3`, `100 C_b/β_R ≤ 1`, there is `b > 0` with
  `Re ǧ_N(b, b − m²) = 1/β_R`, the `h = 0` trajectory in `D_ε`, and `FwPairBdN` at `b`. The only
  named inputs are the pair-layer ones inside `FwPairBdN` (`PairDefSizesNF`, `PairZeroRemAB`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

section Generic

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace ℝ (X j)]
variable {F : HData X} {Λ β κ cg cm cT : ℝ} {N : ℕ} {ε E : ℝ}

omit [∀ j, NormedSpace ℝ (X j)] in
theorem fb_adm_muc {b μ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ) :
    Admissible F Λ κ cm cT N ε b (Hist.muc F Λ κ cm cT N ε b) := by
  have h' : ∃ μ₀, Admissible F Λ κ cm cT N ε b μ₀ := ⟨μ, h⟩
  unfold Hist.muc
  rw [dif_pos h']
  exact h'.choose_spec

theorem fb_gN_eq (fc : FixedConcl F Λ β κ cg cm cT N ε E) {b μ : ℝ}
    (h : Admissible F Λ κ cm cT N ε b μ) :
    Hist.gN F Λ κ cm cT N ε b = (traj F Λ b μ N).1 := by
  unfold Hist.gN
  rw [fc.unique_mu b _ _ (fb_adm_muc h) h]

/-- **Between two `Ufix` points**: `(b, μ^c(b))` is admissible and `ǧ^c` is squeezed. -/
theorem fb_ufix_between (fc : FixedConcl F Λ β κ cg cm cT N ε E) {b₁ b₂ μ₁ μ₂ b : ℝ}
    (ha₁ : Admissible F Λ κ cm cT N ε b₁ μ₁) (ha₂ : Admissible F Λ κ cm cT N ε b₂ μ₂)
    (hg₂ : (traj F Λ b₂ μ₂ N).1 < ε) (hb : b ∈ Icc b₁ b₂) :
    Admissible F Λ κ cm cT N ε b (Hist.muc F Λ κ cm cT N ε b) ∧
      (traj F Λ b₁ μ₁ N).1 ≤ (traj F Λ b (Hist.muc F Λ κ cm cT N ε b) N).1 ∧
      (traj F Λ b (Hist.muc F Λ κ cm cT N ε b) N).1 ≤ (traj F Λ b₂ μ₂ N).1 := by
  have hm := fc.strictMono.monotoneOn
  have h12 := hm ⟨μ₁, ha₁⟩ ⟨μ₂, ha₂⟩ (hb.1.trans hb.2)
  rw [fb_gN_eq fc ha₁, fb_gN_eq fc ha₂] at h12
  have hU₁ : b₁ ∈ Ufix F Λ κ cm cT N ε := ⟨μ₁, ha₁, h12.trans_lt hg₂⟩
  have hU₂ : b₂ ∈ Ufix F Λ κ cm cT N ε := ⟨μ₂, ha₂, hg₂⟩
  obtain ⟨μ, ha, -⟩ := fc.ordConnected.out hU₁ hU₂ hb
  have ham := fb_adm_muc ha
  have e := fb_gN_eq fc ham
  have h1 := hm ⟨μ₁, ha₁⟩ ⟨_, ham⟩ hb.1
  have h2 := hm ⟨_, ham⟩ ⟨μ₂, ha₂⟩ hb.2
  rw [fb_gN_eq fc ha₁, e] at h1
  rw [fb_gN_eq fc ha₂, e] at h2
  exact ⟨ham, h1, h2⟩

end Generic

/-! ### The margin conditions -/

theorem fb_s_le {p c g : ℝ} (h : p * c ≤ 1 / 12) (hg : 0 ≤ g) :
    p * (2 * (3 / 4 * c * g)) ≤ g / 8 := by
  have := mul_le_mul_of_nonneg_right h hg
  calc p * (2 * (3 / 4 * c * g)) = 3 / 2 * (p * c * g) := by ring
    _ ≤ 3 / 2 * (1 / 12 * g) := by linarith
    _ = g / 8 := by ring

theorem fb_g0_bd {g g0 s : ℝ} (hg : 0 ≤ g) (hs : s ≤ g / 8) (hd : |g0 - g| ≤ s) :
    0 ≤ g0 ∧ g0 ≤ 9 / 8 * g := by
  have := abs_le.1 hd
  constructor <;> linarith

/-- **Lower margin** at `b₁ = bFin(y/2)`: `y/2 + E'₁ ≤ y` and `y/4 ≤ ǧ^c(b₁)`. -/
theorem fb_margin_lo {c y g g0 s : ℝ} (hc : 0 ≤ c) (hy : 0 < y) (hcy : 100 * c * y ≤ 1)
    (hg0 : 0 ≤ g) (hg : |g - y / 2| ≤ 4 * c * (y / 2) ^ 2) (hs : s ≤ g / 8) (hd : |g0 - g| ≤ s) :
    y / 2 + (s + 2 * c * g0 ^ 2 + 2 * c * g ^ 2) ≤ y ∧ y / 4 ≤ g := by
  have hcy2 : c * y ^ 2 ≤ y / 100 := by
    have := mul_le_mul_of_nonneg_right (show c * y ≤ 1 / 100 by linarith) hy.le
    calc c * y ^ 2 = c * y * y := by ring
      _ ≤ 1 / 100 * y := this
      _ = y / 100 := by ring
  have e : 4 * c * (y / 2) ^ 2 = c * y ^ 2 := by ring
  have hg' := abs_le.1 hg
  have hgu : g ≤ y := by linarith
  obtain ⟨h00, h01⟩ := fb_g0_bd hg0 hs hd
  have hq0 : g0 ^ 2 ≤ (9 / 8 * y) ^ 2 := pow_le_pow_left₀ h00 (by linarith) 2
  have hq1 : g ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hg0 hgu 2
  have k0 := mul_le_mul_of_nonneg_left hq0 hc
  have k1 := mul_le_mul_of_nonneg_left hq1 hc
  have e2 : c * (9 / 8 * y) ^ 2 = 81 / 64 * (c * y ^ 2) := by ring
  constructor <;> nlinarith

/-- **Upper margin** at `b₂ = bFin(2y)`: `y ≤ 2y − E'₂` and `ǧ^c(b₂) ≤ 3y`. -/
theorem fb_margin_hi {c y g g0 s : ℝ} (hc : 0 ≤ c) (hy : 0 < y) (hcy : 100 * c * y ≤ 1)
    (hg0 : 0 ≤ g) (hg : |g - 2 * y| ≤ 4 * c * (2 * y) ^ 2) (hs : s ≤ g / 8) (hd : |g0 - g| ≤ s) :
    y ≤ 2 * y - (s + 2 * c * g0 ^ 2 + 2 * c * g ^ 2) ∧ g ≤ 3 * y := by
  have hcy2 : c * y ^ 2 ≤ y / 100 := by
    have := mul_le_mul_of_nonneg_right (show c * y ≤ 1 / 100 by linarith) hy.le
    calc c * y ^ 2 = c * y * y := by ring
      _ ≤ 1 / 100 * y := this
      _ = y / 100 := by ring
  have e : 4 * c * (2 * y) ^ 2 = 16 * (c * y ^ 2) := by ring
  have hg' := abs_le.1 hg
  have hgu : g ≤ 3 * y := by linarith
  obtain ⟨h00, h01⟩ := fb_g0_bd hg0 hs hd
  have hq0 : g0 ^ 2 ≤ (27 / 8 * y) ^ 2 := pow_le_pow_left₀ h00 (by linarith) 2
  have hq1 : g ^ 2 ≤ (3 * y) ^ 2 := pow_le_pow_left₀ hg0 hgu 2
  have k0 := mul_le_mul_of_nonneg_left hq0 hc
  have k1 := mul_le_mul_of_nonneg_left hq1 hc
  have e2 : c * (27 / 8 * y) ^ 2 = 729 / 64 * (c * y ^ 2) := by ring
  have e3 : c * (3 * y) ^ 2 = 9 * (c * y ^ 2) := by ring
  constructor <;> nlinarith

set_option maxHeartbeats 8000000 in
/-- **`MasterFacts.h0EndsG` at the `p_W` of `h0WindowX_ofS`** (`p_Wc_μ ≤ 1/12` exported; the proof
is that of `h0EndsG`, copied, with `h0WindowX_ofS` in place of `h0WindowX_of`). -/
theorem MasterFacts.fb_h0EndsGS {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ pW r₀ : ℝ, pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      H0EndsConclG M pW r₀ := by
  set D := M.core with hDd
  obtain ⟨r₀, hr₀, hr₀1, hRe⟩ := M.onePt_re_win
  obtain ⟨pW, hpW, hX⟩ := h0WindowX_ofS D.hWin
  have hM := D.h0MassC
  refine ⟨pW, r₀, hpW, hr₀, hr₀1, fun N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV hθ
    hgy hsm => ?_⟩
  have hN : 2 ≤ N := by omega
  obtain ⟨-, -, hρ, hε, -, -, -, hcm, -, -, hCf, -, -, -, hspl, -⟩ := D.hC2
  obtain ⟨hε45, hXc, hu⟩ := D.hH0E
  have hL : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := D.hL49; omega)
  have hcμ : 0 < cmu ((L : ℝ) ^ 2) D.cm := by
    unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  set gc := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 with hgcd
  set c₁ := 3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * gc with hc₁d
  have hg := hadm.1 Nh le_rfl
  have hgc0 : 0 < gc := hg.1
  have hm0 : 0 ≤ m * (Fintype.card (Lam 2 L N) : ℝ) := mul_nonneg hm.1.le (by positivity)
  have hℓR : (R.withMsq m).ℓ = D.ℓ := hRℓ
  have hcNL : 0 ≤ cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε := by
    unfold cNuLast cNuLs cZ
    have h1 := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 16 / 7 * (L : ℝ) ^ 2 *
      (8 * (R.withMsq m).ℓ ^ 2 / 49 + 16 * (R.withMsq m).ℓ ^ 2 / 147)) hcμ.le) hε.le
    have h2 : 0 ≤ 3 * (L : ℝ) ^ 2 * (16 * (R.withMsq m).ℓ ^ 2 / 49) + 8 * (R.withMsq m).ℓ ^ 2 / 49 +
      (L : ℝ) ^ 2 * (16 * (R.withMsq m).ℓ ^ 2 / 147) := by positivity
    have h3 : 0 ≤ 16 / 7 * (L : ℝ) ^ 2 * (16 * (R.withMsq m).ℓ ^ 2 / 49) +
      3 * (R.withMsq m).ℓ ^ 2 / 7 := by positivity
    have h4 := mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2) (add_nonneg h1 h2)
    linarith
  have hK := cNuLast_win_margin (R.withMsq m) (ε := D.ε) D.hL49 (by rw [hℓR]; exact D.hcmF) hu
  have hKT := h0KT_spec (L := L) D.hZT
  have hB := h0B_spec hspl
  have hsl := h0Slack_le_win (Lr := L) (cNL := cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε)
    (ℓ := D.ℓ) hCf hcNL hKT.1 hB.1 hρ.le hcμ hgc0 hg.2.1 hm0 hmV hθ hε45 hXc
  -- the margin at the upper end: `(c_ν + 2)(5/4)ǧ^c + 55ǧ^c ≤ L⁴c₁`
  have hL49 : (49 : ℝ) ≤ L := by exact_mod_cast D.hL49
  have hmarg : (cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε + 2) * (5 / 4 * gc) + 55 * gc ≤
      (L : ℝ) ^ 4 * c₁ := by
    have hL2 : 44 ≤ (L : ℝ) ^ 2 := by nlinarith
    have e : (L : ℝ) ^ 4 * c₁ = 3 * (L : ℝ) ^ 4 * cmu ((L : ℝ) ^ 2) D.cm * gc / 4 := by
      rw [hc₁d]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hK hgc0.le
    nlinarith
  -- the window
  obtain ⟨μl, μu, h1, h2, h3, h4, h5⟩ :=
    hX N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc c₁ (3 / 4 * cmu ((L : ℝ) ^ 2) D.cm) hb hadm
      (by positivity) le_rfl hθ hgy
  have hlu : μl ≤ μu := h1.trans h2
  have hgw : ∀ μ ∈ Icc μl μu, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 ≤ gc + pW * (c₁ - -c₁) := fun μ hμ => by
    obtain ⟨k1, -, -, k4⟩ := h5 μ hμ
    exact ⟨((k1 Nh le_rfl).1).le, by linarith [(abs_le.1 k4).2]⟩
  -- lower end (as `h0EndsC`)
  obtain ⟨gl0, gl1⟩ := hgw μl ⟨le_rfl, hlu⟩
  have hlo := (hM N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μl hb h3.1).2 (by
    rw [h3.2]; have := (hsl _ gl0 gl1).2; linarith)
  have hex : H0SusceptExit L N m b μl μu := h0SusceptExit_of_re ⟨le_rfl, hlu⟩ hlo.2
  -- upper end: `Re r ≥ 0` from the one-point chain
  obtain ⟨gu0, gu1⟩ := hgw μu ⟨hlu, le_rfl⟩
  obtain ⟨hgu, hSu⟩ := hsl _ gu0 gu1
  obtain ⟨x, hx0, hx1⟩ := exists_coal_one (L := L) (N := N) (by have := D.hL49; omega) hN
  have hR := hRe N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μu hb h4.1 x hx0 (by omega) (by omega)
    (5 / 4 * gc) hgu hsm (by rw [h4.2]; linarith)
  obtain ⟨hZb, hre, hχ⟩ := hR
  obtain ⟨-, hr⟩ := onept_real_of_re hb hm.1 hZb hre hχ
  have hOP : H0OnePtUp L N m b μu := h0OnePtUp_of_re hb hm.1 hZb hr hχ
  have hmem := h0_mem_window' hb hm.1 hOP hex
  obtain ⟨k1, k2, k3, k4⟩ := h5 (b - m) ⟨hmem.1.le, hmem.2⟩
  exact ⟨μl, μu, h1, h2, h3, h4, hex, hOP, hmem, k1, abs_le.2 ⟨k2, k3⟩, k4⟩


namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

end MasterFacts

/-! ### Folding `H0OnePtSmall` into `g₀` -/

theorem fb_lin (a : ℝ) {k : ℝ} (hk : 0 < k) : ∃ G : ℝ, 0 < G ∧ ∀ g : ℝ, 0 ≤ g → g ≤ G → a * g ≤ k := by
  refine ⟨k / (|a| + 1), by positivity, fun g hg hG => ?_⟩
  have h1 : a * g ≤ |a| * g := mul_le_mul_of_nonneg_right (le_abs_self a) hg
  have h2 : |a| * g ≤ (|a| + 1) * (k / (|a| + 1)) :=
    mul_le_mul (by linarith) hG hg (by positivity)
  have h3 : (|a| + 1) * (k / (|a| + 1)) = k := by field_simp
  linarith

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- **`H0OnePtSmall … ((5/4)ǧ^c)` from `ǧ^c ≤ G₁`, the mass condition `m²L^{2N} ≤ ǧ^c` and
`K_p a_{N_h−1} ≤ 1/2`** (`a_{N_h−1} = zA L m² (N_h − 1)`). All other conditions are `c·g ≤ k`. -/
theorem MasterFacts.fb_small {L : ℕ} [NeZero L] (M : MasterFacts L) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ G₁ : ℝ, 0 < G₁ ∧ ∀ (N Nh : ℕ) (m gc : ℝ), 0 ≤ m → 0 ≤ gc → gc ≤ G₁ →
      m * (L : ℝ) ^ (2 * N) ≤ gc → M.Kp * zA L m (Nh - 1) ≤ 1 / 2 →
      H0OnePtSmall M N Nh m r₀ (5 / 4 * gc) := by
  obtain ⟨-, -, hρ, -, -, -, -, -, -, -, hCf, -⟩ := M.core.hC2
  obtain ⟨G1, p1, c1⟩ := fb_lin (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
    9 / 4 * ((cBn : ℝ) * Q1 2 * M.core.cWL) + cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3)
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨G2, p2, c2⟩ := fb_lin (2 * M.core.Cf) hρ
  obtain ⟨G3, p3, c3⟩ := fb_lin (8 * cM * M.core.ℓ ^ 2 * M.core.Cf) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨G4, p4, c4⟩ := fb_lin (cRho L * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL)
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨G5, p5, c5⟩ := fb_lin (4 * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL)
    (by positivity : (0 : ℝ) < r₀ ^ 2)
  obtain ⟨G6, p6, c6⟩ := fb_lin (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL) hr₀
  obtain ⟨G7, p7, c7⟩ := fb_lin M.Kp (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨G8, p8, c8⟩ := fb_lin ((L : ℝ) ^ 4 * M.core.Cf) (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨G9, p9, c9⟩ := fb_lin M.core.KZ (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨G10, p10, c10⟩ := fb_lin (max (spinMK L M.core.cg M.core.Ke M.core.KZ
        (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
      2 * 4 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 + h0crL M * Real.exp M.core.KZ))
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Gm1, pm1, cm1⟩ := fb_lin (8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3)
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Gm2, pm2, cm2⟩ := fb_lin (h0KT L M.core.ρ) (by norm_num : (0 : ℝ) < 1 / 2)
  set Gg := min G1 (min G2 (min G3 (min G4 (min G5 (min G6 (min G7 (min G8 (min G9
    (min G10 1))))))))) with hGg
  have pg : 0 < Gg := lt_min p1 (lt_min p2 (lt_min p3 (lt_min p4 (lt_min p5 (lt_min p6
    (lt_min p7 (lt_min p8 (lt_min p9 (lt_min p10 one_pos)))))))))
  refine ⟨min (4 / 5 * Gg) (min Gm1 Gm2), lt_min (by positivity) (lt_min pm1 pm2),
    fun N Nh m gc hm0 hgc0 hgc hmV hKz => ⟨fun g hg0 hgG => ?_, ?_, ?_⟩⟩
  · have hgg : g ≤ Gg := by
      have := min_le_left (4 / 5 * Gg) (min Gm1 Gm2)
      linarith
    have q1 : g ≤ G1 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q2 : g ≤ G2 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q3 : g ≤ G3 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q4 : g ≤ G4 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q5 : g ≤ G5 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q6 : g ≤ G6 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q7 : g ≤ G7 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q8 : g ≤ G8 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q9 : g ≤ G9 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q10 : g ≤ G10 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have q11 : g ≤ 1 := hgg.trans (by simp only [hGg, min_le_iff, le_refl, true_or, or_true])
    have k8 := mul_le_mul_of_nonneg_right (c8 g hg0 q8) hg0
    have k7 := c7 g hg0 q7
    refine ⟨c1 g hg0 q1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c9 g hg0 q9, c10 g hg0 q10⟩
    · linarith [c2 g hg0 q2]
    · linarith [c3 g hg0 q3]
    · linarith [c4 g hg0 q4]
    · linarith [c5 g hg0 q5]
    · exact c6 g hg0 q6
    · rw [mul_add]; linarith
    · have : (L : ℝ) ^ 4 * (M.core.Cf * g ^ 2) = (L : ℝ) ^ 4 * M.core.Cf * g * g := by ring
      rw [this]; linarith
  · have hx0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := by positivity
    have := cm1 _ hx0 (hmV.trans (hgc.trans ((min_le_right _ _).trans (min_le_left _ _))))
    linarith
  · have hx0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := by positivity
    have := cm2 _ hx0 (hmV.trans (hgc.trans ((min_le_right _ _).trans (min_le_right _ _))))
    linarith

/-! ### The constants -/

/-! ### The bracket theorem -/

end

end Spin2
