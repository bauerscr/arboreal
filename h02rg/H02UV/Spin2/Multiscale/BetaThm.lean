import Spin2.Master.Master

/-!
# `thm:beta` and `prop:gamma` (ii) under the master construction

* `MagConcl`, `magConcl_of`: the conclusion of `prop_gamma_M2` (the magnetisation
  `M_j = (β_j/β_ε)^{1/3}(1 + O(β_j^{-1}))`, conditional only on (H_λ)) from `SpinConcl`.
* `shoot_beta_near` (pure): `|ǧ - y| ≤ 4C_b y²`, `4C_b y ≤ 1/4` give `|1/ǧ - 1/y| ≤ (16/3)C_b`.
* `beta_eps_shoot` (pure): `|1/b - x| ≤ E + a log(ǧ/b)`, `0 < ǧ ≤ 1`, `x ≥ 1` give
  `|1/b - x| ≤ E + a log(2(x + E + a|log 2a|))`.
* `BetaConcl`, `betaConcl_of`: from `FlowC2Concl` and `SpinConcl` (the same constants): for every
  `N ≥ 2`, `N_h = N - 2`, `m² ∈ mRange L N` and `β_R ≥ 2/ε`, the shooting solution
  `b = bFin(m², 1/β_R)` (`β_ε = 1/b`) is the unique `b ∈ U(m²)` with `Re ǧ_N = 1/β_R`, its
  trajectory is admissible (`μ₀ = muc b`), `|β_{N_h} - β_R| ≤ (16/3)C_b`, the per-step band
  `|β_{k+1} - β_k + β| ≤ K_b a_k + C_gu ǧ_k`, and
  `|β_ε - β_R - N_hβ| ≤ E + a log(2(β_R + N_hβ + E + a|log 2a|))`,
  `|β_ε - (3/2π) log L^N| ≤ β_R + 2β + E + a log(…)` (`β = β_1 log L`, `β_1 = 3/2π`);
  `β_R ↦ β_ε` is strictly increasing and continuous on `[2/ε, ∞)`.
* `thm_flow_master_all`: `thm_flow_master` with `MagConcl` and `BetaConcl`; `thm_beta`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- The conclusion of `prop_gamma_M2` for given constants. -/
def MagConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl →
    (∀ k < Nh, ‖lam k - ((((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      Kl * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) →
    ∀ j ≤ Nh,
      ‖(1 - (b : ℂ) * ∑ k ∈ range j,
          lam k * GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
        (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinMK L cg Ke KZ Kl KG 0 * (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1

set_option maxHeartbeats 1000000 in
/-- **`prop:gamma` (ii) along one trajectory** (the proof of `magConcl_of`, per trajectory): from
the `D_ε` condition up to `N_h`, the magnetisation sum (`SpinSum` at this trajectory) and the
`log|Z|`/`Γ^int` bounds of `SpinConcl` at this trajectory. No final condition is used
(route (a1): windowed trajectories). -/
theorem magConcl_traj {L N : ℕ} [NeZero L] {κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : (2 : ℝ) ≤ L)
    (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ) (hKG : 0 ≤ KG) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] {Nh : ℕ} (hNh : Nh + 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (hSS : ∀ (T : ℕ → ℂ) (a : ℕ → ℝ) (B aS : ℝ), 0 ≤ B →
      (∀ k, 0 ≤ a k) → ∑ k ∈ range Nh, a k ≤ aS →
      (∀ k < Nh, ‖T k - ((betaL L / 3 * b * (((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^
          (1 / 3 : ℝ)) ^ 2 : ℝ) : ℂ)‖ ≤
        B * b * (((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 *
          ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + a k)) →
      ∀ j ≤ Nh, ‖(1 - ∑ k ∈ range j, T k) -
          (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
        spinTrajK (betaL L) cg B (eRange (betaL L) Ke 1) aS *
          (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1)
    (hZ : ∀ n ≤ Nh,
        (rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0 ∧
        |Real.log ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
            1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 / b)| ≤
          KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1)
    (hGZ : ∀ k < Nh,
        ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
            GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) -
            (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          KG * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ∧
        (rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z =
          ((‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ : ℝ) : ℂ))
    (lam : ℕ → ℂ) (Kl : ℝ) (hKl : 0 ≤ Kl)
    (hl : ∀ k < Nh, ‖lam k - ((((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      Kl * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) :
    ∀ j ≤ Nh,
      ‖(1 - (b : ℂ) * ∑ k ∈ range j,
          lam k * GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
        (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinMK L cg Ke KZ Kl KG 0 * (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 := by
  intro j hj
  set Kp : ℝ := 0 with hKpd
  have hKp : (0 : ℝ) ≤ Kp := le_rfl
  have hG := fun k (hk : k < Nh) => (hGZ k hk).1
  have hph : ∀ k < Nh, ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z -
      (‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ : ℂ)‖ ≤
      Kp * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 *
        ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ := by
    intro k hk
    have e := (hGZ k hk).2
    rw [hKpd, zero_mul, zero_mul, norm_le_zero_iff, sub_eq_zero]
    exact e
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  set γ : ℝ := Real.log L / (2 * Real.pi) with hγd
  have hγ : 0 ≤ γ := by
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have hg : ∀ n ≤ Nh, 0 < (t n).1 := fun n hn => (hD n hn).1
  have hgε : ∀ n ≤ Nh, (t n).1 ≤ ε := fun n hn => (hD n hn).2.1
  have hb : 0 < b := by have := hg 0 (Nat.zero_le _); rwa [ht, Hist.traj_zero] at this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hsa : ∑ k ∈ range Nh, zA L m k ≤ 4 := by
    have := sum_zA_le (Ln := L) rfl hL2 hm.1.le Nh
    linarith only [this, hmn Nh le_rfl]
  set Kzz := (KZ + Kp) * Real.exp KZ with hKzz
  have hKzz0 : 0 ≤ Kzz := by positivity
  have hT : ∀ k < Nh, ‖(b : ℂ) * lam k * GamInt (R.withMsq m) k t -
      ((betaL L / 3 * b * (((t k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 : ℝ) : ℂ)‖ ≤
      (Kl * (γ + 3 * gamK L KZ KG Kp) + gamK L KZ KG Kp) * b *
        (((t k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 * ((t k).1 + zA L m k) := by
    intro k hk
    set g := (t k).1 with hgdef
    set r := (g / b) ^ (1 / 3 : ℝ) with hrd
    set Z := (rawHist (R.withMsq m) (k + 1) t).Z with hZd
    have hgk := hg k hk.le
    have hg1 : g ≤ 1 := (hgε k hk.le).trans hε1
    have hr : 0 < r := cbrt_pos (div_pos hgk hb)
    have ha0 := zA_nonneg L hm.1.le k
    have ha2 : zA L m k ≤ 2 := zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)
    obtain ⟨hZne, hZlog⟩ := hZ k hk.le
    have hlogr : Real.log r = 1 / 3 * Real.log (g / b) := Real.log_rpow (div_pos hgk hb) _
    have hZi : ‖Z⁻¹ - (r : ℂ)‖ ≤ Kzz * r * g := by
      refine near_of_log (inv_ne_zero hZne) hr hgk.le hg1 hKZ hKp ?_ ?_
      · rw [norm_inv, Real.log_inv, hlogr]
        have e : -Real.log ‖Z‖ - 1 / 3 * Real.log (g / b) =
            -(Real.log ‖Z‖ + 1 / 3 * Real.log (g / b)) := by ring
        rw [e, abs_neg]; exact hZlog
      · exact phase_inv hZne (hph k hk)
    have hGam : ‖GamInt (R.withMsq m) k t - ((γ * r : ℝ) : ℂ)‖ ≤
        gamK L KZ KG Kp * r * (g + zA L m k) := by
      have e : GamInt (R.withMsq m) k t - ((γ * r : ℝ) : ℂ) =
          Z⁻¹ * (Z * GamInt (R.withMsq m) k t - (γ : ℂ)) + (γ : ℂ) * (Z⁻¹ - (r : ℂ)) := by
        have hZne' : Z ≠ 0 := hZne
        rw [mul_sub Z⁻¹, ← mul_assoc, inv_mul_cancel₀ hZne', one_mul]; push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have hZin : ‖Z⁻¹‖ ≤ r * (1 + Kzz) := by
        have := norm_le_norm_add_norm_sub' Z⁻¹ (r : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at this
        have h2 : Kzz * r * g ≤ Kzz * r := mul_le_of_le_one_right (by positivity) hg1
        linarith only [this, hZi, h2]
      have h1 : ‖Z⁻¹ * (Z * GamInt (R.withMsq m) k t - (γ : ℂ))‖ ≤
          r * (1 + Kzz) * (KG * (g + zA L m k)) := by
        rw [norm_mul]; exact mul_le_mul hZin (hG k hk) (norm_nonneg _) (by positivity)
      have h2 : ‖(γ : ℂ) * (Z⁻¹ - (r : ℂ))‖ ≤ γ * (Kzz * r * g) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ]
        exact mul_le_mul_of_nonneg_left hZi hγ
      have h3 : γ * (Kzz * r * g) ≤ γ * (Kzz * r * (g + zA L m k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [ha0])
          (by positivity)) hγ
      have e2 : gamK L KZ KG Kp * r * (g + zA L m k) =
          r * (1 + Kzz) * (KG * (g + zA L m k)) + γ * (Kzz * r * (g + zA L m k)) := by
        unfold gamK; rw [← hKzz, ← hγd]; ring
      rw [e2]; linarith only [h1, h2, h3]
    have hgK : 0 ≤ gamK L KZ KG Kp := by unfold gamK; rw [← hKzz, ← hγd]; positivity
    have key := spin_term (lam := lam k) (Gam := GamInt (R.withMsq m) k t) hr.le hγ hb.le hKl hgK
      (by linarith only [hgk, ha0]) (by linarith only [hg1, ha2]) (hl k hk) hGam
    have e : betaL L / 3 = γ := by unfold betaL; rw [hγd]; ring
    rw [e]; exact key
  have hB : 0 ≤ Kl * (γ + 3 * gamK L KZ KG Kp) + gamK L KZ KG Kp := by
    have : 0 ≤ gamK L KZ KG Kp := by unfold gamK; rw [← hKzz, ← hγd]; positivity
    positivity
  have key := hSS (fun k => (b : ℂ) * lam k * GamInt (R.withMsq m) k t) (zA L m)
    _ 4 hB (zA_nonneg L hm.1.le) hsa hT j hj
  unfold spinMK
  convert key using 3
  rw [mul_sum]; congr 1; exact sum_congr rfl fun k _ => (mul_assoc _ _ _).symm


/-- **`prop:gamma` (ii) from `SpinConcl`** (the proof of `prop_gamma_M2`). -/
theorem magConcl_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : (2 : ℝ) ≤ L)
    (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ) (hKG : 0 ≤ KG)
    (h : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm lam Kl hKl hl j hj
  obtain ⟨-, -, -, hSS, -, -, hZ, hGZ⟩ := h N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  exact magConcl_traj hL2 hε1 hKZ hKG R hNh hm hadm.1 (hSS m hm b μ₀ hadm) (hZ m hm b μ₀ hadm)
    (hGZ m hm b μ₀ hadm) lam Kl hKl hl j hj

/-- **The final coupling of the shooting is `β_R + O(1)`** (pure): `|ǧ - y| ≤ 4C_b y²` and
`4C_b y ≤ 1/4` give `|1/ǧ - 1/y| ≤ (16/3)C_b`. -/
theorem shoot_beta_near {g y Cb : ℝ} (hy : 0 < y) (hCb : 0 ≤ Cb) (hCy : 4 * Cb * y ≤ 1 / 4)
    (h : |g - y| ≤ 4 * Cb * y ^ 2) : |1 / g - 1 / y| ≤ 16 / 3 * Cb := by
  have h1 := (abs_le.1 h).1
  have hy2 : 4 * Cb * y ^ 2 ≤ y / 4 := by
    have := mul_le_mul_of_nonneg_right hCy hy.le
    linarith only [this, show 4 * Cb * y ^ 2 = 4 * Cb * y * y by ring]
  have hg : 3 / 4 * y ≤ g := by linarith only [h1, hy2]
  have hg0 : 0 < g := by linarith only [hg, hy]
  have e : 1 / g - 1 / y = (y - g) / (g * y) := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hg0 hy), div_le_iff₀ (mul_pos hg0 hy), abs_sub_comm]
  have h2 : 4 * Cb * y ^ 2 ≤ 16 / 3 * Cb * (g * y) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg hy.le)
      (by positivity : (0 : ℝ) ≤ 16 / 3 * Cb)
    linarith only [this, show 16 / 3 * Cb * (3 / 4 * y * y) = 4 * Cb * y ^ 2 by ring]
  linarith only [h, h2]

/-- **`β_ε` from the summed running coupling** (pure): if `|1/b - x| ≤ E + a log(ǧ/b)` with
`0 < ǧ ≤ 1` and `x ≥ 1`, then `|1/b - x| ≤ E + a log(2(x + E + a|log 2a|))`. -/
theorem beta_eps_shoot {b g x E a : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g ≤ 1) (ha : 0 ≤ a)
    (hE : 0 ≤ E) (hx : 1 ≤ x) (h : |1 / b - x| ≤ E + a * Real.log (g / b)) :
    |1 / b - x| ≤ E + a * Real.log (2 * (x + E + a * |Real.log (2 * a)|)) := by
  set B := 1 / b with hBd
  have hB : 0 < B := by positivity
  have hA0 : 0 ≤ a * |Real.log (2 * a)| := mul_nonneg ha (abs_nonneg _)
  have hM1 : 1 ≤ 2 * (x + E + a * |Real.log (2 * a)|) := by linarith
  have hlM : 0 ≤ Real.log (2 * (x + E + a * |Real.log (2 * a)|)) := Real.log_nonneg hM1
  have hgb : g / b = g * B := by rw [hBd]; ring
  have hlgB : Real.log (g / b) ≤ Real.log B := by
    rw [hgb, Real.log_mul hg.ne' hB.ne']
    linarith only [Real.log_nonpos hg.le hg1]
  rcases le_or_gt (Real.log (g / b)) 0 with hle | hlt
  · have := mul_nonpos_of_nonneg_of_nonpos ha hle
    have := mul_nonneg ha hlM
    linarith only [h, this, ‹a * Real.log (g / b) ≤ 0›]
  · have h3 : a * Real.log (g / b) ≤ a * Real.log B := mul_le_mul_of_nonneg_left hlgB ha
    have h5 := mul_log_le_half ha hB
    have hBup : B ≤ 2 * (x + E + a * |Real.log (2 * a)|) := by
      linarith only [(abs_le.1 h).2, h3, h5]
    have h6 : Real.log B ≤ Real.log (2 * (x + E + a * |Real.log (2 * a)|)) :=
      Real.log_le_log hB hBup
    have h7 := mul_le_mul_of_nonneg_left (hlgB.trans h6) ha
    linarith only [h, h7]

/-- The constant `E` of `BetaConcl`. -/
def betaShE (L : ℕ) (cg Ke Cb : ℝ) : ℝ :=
  betaLogE (betaL L) cg (eRange (betaL L) Ke 1) + 16 / 3 * Cb

/-- The constant `a` of `BetaConcl`. -/
def betaShA (L : ℕ) (cg : ℝ) : ℝ := Cgu (betaL L) cg / betaL L

/-- **`thm:beta` for given constants.** For every `N ≥ 2`, `N_h = N - 2`, `m² ∈ mRange L N` and
`β_R ≥ 2/ε`, with `b = bFin(m², 1/β_R)` (`β_ε = 1/b`) and `μ₀ = muc b`: `b` is the unique
`b ∈ U(m²)` with `Re ǧ_N(b) = 1/β_R`, `(b, μ₀)` is admissible, `|β_{N_h} - β_R| ≤ (16/3)C_b`,
the per-step band of `β_k = 1/ǧ_k`, the asymptotics of `β_ε` (in `N_h β` and in
`(3/2π) log L^N`); and `β_R ↦ β_ε` is strictly increasing and continuous on `[2/ε, ∞)`. -/
def BetaConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke Cb : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    (∀ βR : ℝ, 2 / ε ≤ βR →
      bFin R κ cm cT Nh ε m (1 / βR) ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
      gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m (1 / βR)) = 1 / βR ∧
      (∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε,
        gFinB R κ cm cT Nh ε m b = 1 / βR → b = bFin R κ cm cT Nh ε m (1 / βR)) ∧
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε (bFin R κ cm cT Nh ε m (1 / βR))
        (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε (bFin R κ cm cT Nh ε m (1 / βR))) ∧
      |1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) (bFin R κ cm cT Nh ε m (1 / βR))
          (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε
            (bFin R κ cm cT Nh ε m (1 / βR))) Nh).1 - βR| ≤ 16 / 3 * Cb ∧
      (∀ k < Nh,
        |1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) (bFin R κ cm cT Nh ε m (1 / βR))
            (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε
              (bFin R κ cm cT Nh ε m (1 / βR))) (k + 1)).1 -
          1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) (bFin R κ cm cT Nh ε m (1 / βR))
            (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε
              (bFin R κ cm cT Nh ε m (1 / βR))) k).1 + betaL L| ≤
          2 * (1 + betaL L) * max Ke (betaL L / 2) * zA L m k +
            Cgu (betaL L) cg * (traj (rgDataM R m) ((L : ℝ) ^ 2) (bFin R κ cm cT Nh ε m (1 / βR))
              (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε
                (bFin R κ cm cT Nh ε m (1 / βR))) k).1) ∧
      |1 / bFin R κ cm cT Nh ε m (1 / βR) - (βR + Nh * betaL L)| ≤
        betaShE L cg Ke Cb + betaShA L cg * Real.log (2 * (βR + Nh * betaL L +
          betaShE L cg Ke Cb + betaShA L cg * |Real.log (2 * betaShA L cg)|)) ∧
      |1 / bFin R κ cm cT Nh ε m (1 / βR) - 3 / (2 * Real.pi) * Real.log ((L : ℝ) ^ N)| ≤
        βR + 2 * betaL L + betaShE L cg Ke Cb + betaShA L cg * Real.log (2 * (βR + Nh * betaL L +
          betaShE L cg Ke Cb + betaShA L cg * |Real.log (2 * betaShA L cg)|))) ∧
    StrictMonoOn (fun βR => 1 / bFin R κ cm cT Nh ε m (1 / βR)) (Ici (2 / ε)) ∧
    ContinuousOn (fun βR => 1 / bFin R κ cm cT Nh ε m (1 / βR)) (Ici (2 / ε))

set_option maxHeartbeats 4000000 in
/-- **`thm:beta` from `FlowC2Concl` and `SpinConcl`** (the same constants). -/
theorem betaConcl_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hL2 : (2 : ℝ) ≤ L) (hε1 : ε ≤ 1)
    (hC2 : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb)
    (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) : BetaConcl L ℓ A ρ κ cg cm cT ε Ke Cb := by
  obtain ⟨-, -, -, hε, -, -, hcg, -, -, hKe, -, hCb, hCbε, -, -, hC⟩ := hC2
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨-, hMsq, -, hcont, s1, s2, hmono, huniq, hbfin, -⟩ :=
    hC N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  obtain ⟨-, -, -, -, hBA, hstep, -⟩ := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh.le
  set F := rgDataM R m with hFd
  set U := Ufix F ((L : ℝ) ^ 2) κ cm cT Nh ε with hUd
  set f := gFinB R κ cm cT Nh ε m with hfd
  set bs := fun y => bFin R κ cm cT Nh ε m y with hbsd
  have hβ : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have heR : 0 ≤ eRange (betaL L) Ke 1 := by unfold eRange; positivity
  have hCgu : 0 ≤ Cgu (betaL L) cg := by unfold Cgu; positivity
  have hspec : ∀ b ∈ U, Admissible F ((L : ℝ) ^ 2) κ cm cT Nh ε b
      (Hist.muc F ((L : ℝ) ^ 2) κ cm cT Nh ε b) := fun b hb => by
    obtain ⟨μ, hμ, -⟩ := hb
    have hex : ∃ μ, Admissible F ((L : ℝ) ^ 2) κ cm cT Nh ε b μ := ⟨μ, hμ⟩
    unfold Hist.muc; rw [dif_pos hex]; exact hex.choose_spec
  have hbpos : ∀ b ∈ U, 0 < b := fun b hb => by
    have := ((hspec b hb).1 0 (Nat.zero_le _)).1
    rwa [Hist.traj_zero] at this
  -- the solution for `y ∈ (0, ε/2]`
  have hsol : ∀ y ∈ Ioc 0 (ε / 2), bs y ∈ U ∧ f (bs y) = y := by
    intro y hy
    have hβR : 2 / ε ≤ 1 / y := by
      rw [div_le_div_iff₀ hε hy.1]; linarith only [hy.2]
    obtain ⟨b, hb, hby⟩ := s1 m hm (1 / y) hβR
    rw [one_div_one_div] at hby
    exact bFin_spec R ⟨b, hb, hby⟩
  have hy_of : ∀ βR : ℝ, 2 / ε ≤ βR → 1 / βR ∈ Ioc 0 (ε / 2) := fun βR hβR => by
    have hβ0 : 0 < βR := lt_of_lt_of_le (by positivity) hβR
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hβ0]
    rw [div_le_iff₀ hε] at hβR
    linarith only [hβR]
  refine ⟨fun βR hβR => ?_, ?_, ?_⟩
  · have hβ0 : 0 < βR := lt_of_lt_of_le (by positivity) hβR
    have hβ2 : 2 ≤ βR := by
      have : 2 ≤ 2 / ε := by rw [le_div_iff₀ hε]; linarith only [hε1]
      linarith only [this, hβR]
    obtain ⟨hbU, hby⟩ := hsol _ (hy_of βR hβR)
    set b := bs (1 / βR) with hbd
    set μ₀ := Hist.muc F ((L : ℝ) ^ 2) κ cm cT Nh ε b with hμd
    have hadm := hspec b hbU
    have hb0 := hbpos b hbU
    set g := (traj F ((L : ℝ) ^ 2) b μ₀ Nh).1 with hgd
    have hg : 0 < g := (hadm.1 Nh le_rfl).1
    have hg1 : g ≤ 1 := ((hadm.1 Nh le_rfl).2.1).trans hε1
    -- `β_{N_h} = β_R + O(1)`
    have hnear : |1 / g - βR| ≤ 16 / 3 * Cb := by
      have h1 := s2 m hm b hbU βR hby
      have e : Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε b = g := rfl
      rw [e] at h1
      have hCy : 4 * Cb * (1 / βR) ≤ 1 / 4 := by
        have := mul_le_mul_of_nonneg_left (hy_of βR hβR).2 (by positivity : (0 : ℝ) ≤ 4 * Cb)
        linarith only [this, hCbε]
      have := shoot_beta_near (one_div_pos.2 hβ0) hCb hCy h1
      rwa [one_div_one_div] at this
    -- the summed running coupling
    have hasym : |1 / b - (βR + Nh * betaL L)| ≤ betaShE L cg Ke Cb + betaShA L cg *
        Real.log (2 * (βR + Nh * betaL L + betaShE L cg Ke Cb +
          betaShA L cg * |Real.log (2 * betaShA L cg)|)) := by
      have h := hBA m hm b μ₀ hadm Nh le_rfl
      rw [← hgd] at h
      have hK : betaAsymK (betaL L) cg (eRange (betaL L) Ke 1) * g ≤
          |betaAsymK (betaL L) cg (eRange (betaL L) Ke 1)| :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) hg.le).trans
          (mul_le_of_le_one_right (abs_nonneg _) hg1)
      have hK' := mul_le_mul_of_nonneg_left hK hCgu
      have h' : |1 / g - 1 / b + Nh * betaL L| ≤ betaLogE (betaL L) cg (eRange (betaL L) Ke 1) +
          betaShA L cg * Real.log (g / b) := by
        refine h.trans ?_
        unfold betaLogE betaShA
        have e : Cgu (betaL L) cg * (1 / betaL L * Real.log (g / b) +
            betaAsymK (betaL L) cg (eRange (betaL L) Ke 1) * g) =
            Cgu (betaL L) cg / betaL L * Real.log (g / b) +
              Cgu (betaL L) cg * (betaAsymK (betaL L) cg (eRange (betaL L) Ke 1) * g) := by ring
        rw [e]; linarith only [hK']
      have h2 : |1 / b - (βR + Nh * betaL L)| ≤ betaShE L cg Ke Cb +
          betaShA L cg * Real.log (g / b) := by
        have e : 1 / b - (βR + Nh * betaL L) =
            -(1 / g - 1 / b + Nh * betaL L) + (1 / g - βR) := by ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
        unfold betaShE
        linarith only [h', hnear]
      have hE : 0 ≤ betaShE L cg Ke Cb := by unfold betaShE betaLogE; positivity
      have ha : 0 ≤ betaShA L cg := by unfold betaShA; positivity
      have hx : 1 ≤ βR + Nh * betaL L := by
        have : 0 ≤ (Nh : ℝ) * betaL L := by positivity
        linarith only [this, hβ2]
      exact beta_eps_shoot hb0 hg hg1 ha hE hx h2
    refine ⟨hbU, hby, fun b' hb' hb'y => ?_, hadm, hnear,
      fun k hk => hstep m hm b μ₀ hadm k hk, hasym, ?_⟩
    · obtain ⟨b₀, -, hb₀⟩ := huniq m hm βR hβR
      exact (hb₀ b' ⟨hb', hb'y⟩).trans (hb₀ b ⟨hbU, hby⟩).symm
    · -- `(3/2π) log L^N = N β = N_h β + 2β`
      have e1 : 3 / (2 * Real.pi) * Real.log ((L : ℝ) ^ N) = Nh * betaL L + 2 * betaL L := by
        rw [Real.log_pow, ← hNh]; unfold betaL; push_cast; ring
      rw [e1]
      have e2 : 1 / b - (Nh * betaL L + 2 * betaL L) =
          (1 / b - (βR + Nh * betaL L)) + (βR - 2 * betaL L) := by ring
      rw [e2]
      refine (abs_add_le _ _).trans ?_
      have h3 : |βR - 2 * betaL L| ≤ βR + 2 * betaL L := by
        rw [abs_le]; constructor <;> linarith only [hβ0, hβ]
      linarith only [hasym, h3]
  · -- monotonicity in `β_R`
    intro β₁ h₁ β₂ h₂ h12
    obtain ⟨hb₁, hy₁⟩ := hsol _ (hy_of β₁ h₁)
    obtain ⟨hb₂, hy₂⟩ := hsol _ (hy_of β₂ h₂)
    have hβ₁ : 0 < β₁ := lt_of_lt_of_le (by positivity) (show 2 / ε ≤ β₁ from h₁)
    have hlt : bs (1 / β₂) < bs (1 / β₁) := by
      by_contra hle
      push Not at hle
      have h1 : f (bs (1 / β₁)) ≤ f (bs (1 / β₂)) := (hmono m hm).monotoneOn hb₁ hb₂ hle
      rw [hy₁, hy₂] at h1
      have h' : 1 / β₂ < 1 / β₁ := one_div_lt_one_div_of_lt hβ₁ h12
      linarith only [h1, h']
    exact one_div_lt_one_div_of_lt (hbpos _ hb₂) hlt
  · -- continuity in `β_R`
    have hO : ∃ O : Set (ℝ × ℝ), IsOpen O ∧ O ∩ (Ioc 0 (ε / 2) ×ˢ univ) =
        {q | q.1 ∈ Ioc 0 (ε / 2) ∧ q.2 ∈ (fun _ : ℝ => U) q.1} := by
      obtain ⟨O, hOo, hOe⟩ := hMsq.isOpen
      refine ⟨(fun q : ℝ × ℝ => (m, q.2)) ⁻¹' O,
        hOo.preimage (continuous_const.prodMk continuous_snd), ?_⟩
      ext q
      have key : (m, q.2) ∈ O ↔ q.2 ∈ U := by
        constructor
        · intro hq
          have : (m, q.2) ∈ O ∩ (mRange L N ×ˢ univ) := ⟨hq, hm, trivial⟩
          rw [hOe] at this; exact this.2
        · intro hq
          have : (m, q.2) ∈ UfixM R κ cm cT Nh ε (mRange L N) := ⟨hm, hq⟩
          rw [← hOe] at this; exact this.1
      constructor
      · rintro ⟨hqO, hqS, -⟩; exact ⟨hqS, key.1 hqO⟩
      · rintro ⟨hqS, hqU⟩; exact ⟨key.2 hqU, hqS, trivial⟩
    have hc : ContinuousOn (fun q : ℝ × ℝ => (fun y b => f b - y) q.1 q.2)
        {q | q.1 ∈ Ioc 0 (ε / 2) ∧ q.2 ∈ (fun _ : ℝ => U) q.1} := by
      have h1 : ContinuousOn (fun q : ℝ × ℝ => f q.2)
          {q | q.1 ∈ Ioc 0 (ε / 2) ∧ q.2 ∈ (fun _ : ℝ => U) q.1} :=
        hcont.comp (f := fun q : ℝ × ℝ => (m, q.2))
          (continuous_const.prodMk continuous_snd).continuousOn fun q hq => ⟨hm, hq.2⟩
      exact h1.sub continuousOn_fst
    have hmono' : ∀ y ∈ Ioc 0 (ε / 2), StrictMonoOn ((fun y b => f b - y) y)
        ((fun _ : ℝ => U) y) :=
      fun y _ a ha b hb hab => sub_lt_sub_right (hmono m hm ha hb hab) y
    have hbs' : ∀ y ∈ Ioc 0 (ε / 2), bs y ∈ (fun _ : ℝ => U) y ∧
        (fun y b => f b - y) y (bs y) = 0 := fun y hy => by
      obtain ⟨h1, h2⟩ := hsol y hy
      exact ⟨h1, by simp only [h2, sub_self]⟩
    have hcy : ContinuousOn bs (Ioc 0 (ε / 2)) := contOn_shoot hO hc hmono' hbs'
    have hinv : ContinuousOn (fun βR : ℝ => 1 / βR) (Ici (2 / ε)) :=
      continuousOn_const.div continuousOn_id fun x hx =>
        (lt_of_lt_of_le (by positivity) (show 2 / ε ≤ x from hx)).ne'
    have hcomp : ContinuousOn (fun βR => bs (1 / βR)) (Ici (2 / ε)) :=
      hcy.comp hinv fun βR hβR => hy_of βR hβR
    exact continuousOn_const.div hcomp fun βR hβR => (hbpos _ (hsol _ (hy_of βR hβR)).1).ne'

set_option maxHeartbeats 4000000 in
/-- **The master flow theorem with `prop:gamma` (ii) and `thm:beta`**: `thm_flow_master`
together with `MagConcl` and `BetaConcl`, all with one set of constants. -/
theorem thm_flow_master_all (Aext : ℕ → ℝ → Prop)
    (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧
      ε ≤ 1 ∧ 0 ≤ KZ ∧ 0 ≤ KG ∧ SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ BetaConcl L ℓ A ρ κ cg cm cT ε Ke Cb ∧
      Aext L A ∧ ValidConcl L ℓ A ρ κ cg cm cT ε ∧
      ∃ C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx : ℝ,
        StepBounds L A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx ∧
        (∀ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ → Eext L A (cR R₀ ((L : ℝ) ^ 2) cm C₂x) (cx κ cT) ε) ∧
      ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
        R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
      ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
        ApHyp (R.withMsq m) ((L : ℝ) ^ 2) κ cg cm cT ε εsx C₀x C₂x Cqx Clx cSx ∧
        (∀ j < Nh, |(R.withMsq m).msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧
        BandF1 (R.withMsq m) Nh κ cg cm cT ε := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_master Aext hAext Eext hEext
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, rest⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp,
    magConcl_of hL2 hε1 hKZ hKG hSp, betaConcl_of hL2 hε1 hC2 hSp, rest⟩

/-- **Expected result `thm:beta`** (`h02uv-outline.tex`): one set of constants
(`L ≥ L₀`, `ε ≤ 1`, `C_b ≥ 0`) such that `FlowC2Concl` (`thm:flow`) and `BetaConcl` hold. -/
theorem thm_beta : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      BetaConcl L ℓ A ρ κ cg cm cT ε Ke Cb := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_master_all (fun _ _ => True) (fun _ => ⟨0, fun _ _ => trivial⟩)
    (fun _ _ _ _ _ => True) (fun _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, -, -, -, -, hB, -⟩ := hL₀ L hL
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hC2, hε1, hB⟩

end

end Spin2
