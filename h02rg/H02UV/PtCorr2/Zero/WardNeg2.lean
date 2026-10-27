import PtCorr2.Zero.EpsFlow
import PtCorr2.Zero.ExactHist
import PtCorr2.Zero.WardNeg1

/-!
# Route (a1), the mass flow at `h = 0`: the dressed susceptibility with a geometric error, its sign

The error bound of `suscept2_dressed` (`dress_suscept`) carries a factor
`m^{-2}∑_{j<N}|ζ_j|/(|Z_j||1+ζ_j|)` times `e^{2S} - 1 = O(ρ)`: of order `m^{-2}ρ`, which is far
larger than the scale `|Λ|/|Z_N d|` of the susceptibility on the window. Here the zero-mode
corrections `q_j - 1 = ζ_je_j/ρ_j` are used with their scale dependence `|e_j| ≤ B m² L^{2j}`
(`EpsZeroSmall`): the partial products `Q_j²q_j - 1` are `O(ρBm²L^{2j})`, and `|Z_N/Z_j| ≤ (1+ρ)^{N-j}`,
so the sum is geometric and dominated by its last term:

* **`dress_suscept_geo`** (abstract): with `|q_i - 1| ≤ (16/7)ρBm²L^{2i}`, `m²L^{2(N-1)} ≤ 1`,
  `L² ≥ 4`, `|ζ_i| ≤ ρ ≤ 1/8`:
  `|χ_dressed - (m^{-2}Z_N^{-1} - m^{-4}(A/Z_N)/(Z_NU))|
     ≤ L^{2(N-1)}/|Z_N| · e^{(64/7)ρB} · (24ρ²B + (64/7)ρB·|A/Z_N|/(m²|U|))`.
  In normalised units (`â = |Λ|A/Z_N`, `n = m²|Λ|U`) the last factor is `|â|/|n|`, so the error is
  `(|Λ|/(L²Z_N))·O(ρB)·(ρ + |â|/|n|)` — relative `O(ρB(ρ|n| + |â|)/L²)` to `|Λ|/(Z_N|n|)`.
* **`wn2_chi0_form`** (algebra): `m²|Λ|U = n := m²|Λ|(1+k⁰) + âw`, `w = m²Z_Nt_raw`, and
  `m^{-2}Z_N^{-1} - m^{-4}(A/Z_N)/(Z_NU) = |Λ|p/(Z_Nn)`, `p = 1 + k⁰ + â(w-1)/(m²|Λ|)`.
* **`wn2_re_bounds`** (sign): `|p - 1| ≤ π` and `|χ - |Λ|p/(zn)| ≤ (|Λ|/z)(c₀ + c₁a/|n|)` give
  `Re χ ∈ |Λ|/(z|n|²)·[Re n ∓ (π|n| + c₀|n|² + c₁a|n|)]`.
* **`Zr_real_pos`**: along a trajectory `Z_j` is a positive real number (`traj_real`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

local notation "cj" => starRingEnd ℂ

/-! ### Elementary bounds -/

theorem wn2_exp_sub_one_le {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) :
    Real.exp x - 1 ≤ x * Real.exp X :=
  exp_sub_one_le_mul_exp'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hX) hx)

theorem wn2_geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ range n, r ^ k ≤ 2 - 2 * r ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h1 (pow_nonneg h0 n)]

theorem wn2_norm_Z_growth {Z ζ : ℕ → ℂ} (hZs : ∀ j, Z (j + 1) = Z j * (1 + ζ j)) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) {n : ℕ} (hζ : ∀ i < n, ‖ζ i‖ ≤ ρ) (j : ℕ) :
    ∀ k, j + k ≤ n → ‖Z (j + k)‖ ≤ ‖Z j‖ * (1 + ρ) ^ k
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := wn2_norm_Z_growth hZs hρ0 hζ j k (by omega)
    rw [← add_assoc, hZs, norm_mul, pow_succ]
    have h1 : ‖1 + ζ (j + k)‖ ≤ 1 + ρ :=
      (norm_add_le _ _).trans (by rw [norm_one]; linarith [hζ (j + k) (by omega)])
    calc ‖Z (j + k)‖ * ‖1 + ζ (j + k)‖ ≤ ‖Z j‖ * (1 + ρ) ^ k * (1 + ρ) :=
          mul_le_mul ih h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- `(1 + ρ)^{n-j} L^{2j} ≤ (9/8) L^{2(n-1)} r^{n-1-j}`, `r = (9/8)/L²`. -/
theorem wn2_term_geo {ρ Lsq : ℝ} (hρ0 : 0 ≤ ρ) (hρ8 : ρ ≤ 1 / 8) (hL : 4 ≤ Lsq) {n j : ℕ}
    (hj : j < n) :
    (1 + ρ) ^ (n - j) * Lsq ^ j ≤ 9 / 8 * Lsq ^ (n - 1) * (9 / 8 / Lsq) ^ (n - 1 - j) := by
  set k := n - 1 - j
  have hnj : n - j = k + 1 := by omega
  have hn1 : n - 1 = j + k := by omega
  have hL0 : 0 < Lsq := by linarith
  rw [hnj, hn1, pow_succ, pow_add, div_pow]
  have h1 : (1 + ρ) ^ k ≤ (9 / 8) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  have hLk : 0 < Lsq ^ k := pow_pos hL0 k
  have e : 9 / 8 * (Lsq ^ j * Lsq ^ k) * ((9 / 8) ^ k / Lsq ^ k) = 9 / 8 * (9 / 8) ^ k * Lsq ^ j := by
    field_simp
  rw [e]
  have hj0 : 0 ≤ Lsq ^ j := by positivity
  have h2 : (1 + ρ) ^ k * (1 + ρ) ≤ (9 / 8) ^ k * (9 / 8) :=
    mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  nlinarith

theorem wn2_sum_geo {ρ Lsq : ℝ} (hρ0 : 0 ≤ ρ) (hρ8 : ρ ≤ 1 / 8) (hL : 4 ≤ Lsq) (n : ℕ) :
    ∑ j ∈ range n, (1 + ρ) ^ (n - j) * Lsq ^ j ≤ 9 / 4 * Lsq ^ (n - 1) := by
  have hL0 : 0 < Lsq := by linarith
  have hr0 : 0 ≤ 9 / 8 / Lsq := by positivity
  have hr1 : 9 / 8 / Lsq ≤ 1 / 2 := by rw [div_le_iff₀ hL0]; linarith
  calc ∑ j ∈ range n, (1 + ρ) ^ (n - j) * Lsq ^ j
      ≤ ∑ j ∈ range n, 9 / 8 * Lsq ^ (n - 1) * (9 / 8 / Lsq) ^ (n - 1 - j) :=
        sum_le_sum fun j hj => wn2_term_geo hρ0 hρ8 hL (mem_range.1 hj)
    _ = 9 / 8 * Lsq ^ (n - 1) * ∑ j ∈ range n, (9 / 8 / Lsq) ^ (n - 1 - j) := by rw [mul_sum]
    _ = 9 / 8 * Lsq ^ (n - 1) * ∑ k ∈ range n, (9 / 8 / Lsq) ^ k := by
        rw [sum_range_reflect (fun k => (9 / 8 / Lsq) ^ k) n]
    _ ≤ 9 / 8 * Lsq ^ (n - 1) * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := wn2_geom_le hr0 hr1 n
        have := pow_nonneg hr0 n
        linarith
    _ = 9 / 4 * Lsq ^ (n - 1) := by ring

/-! ### The dressed susceptibility with a geometric error -/

section Abstract

variable {Z ζ e : ℕ → ℂ}

/-- **The dressed susceptibility with the scale-dependent zero-mode corrections.** -/
theorem dress_suscept_geo (hZ0 : Z 0 = 1) (hZs : ∀ j, Z (j + 1) = Z j * (1 + ζ j)) {n : ℕ}
    (hn : 1 ≤ n) (hρ : ∀ i < n, dRho ζ e i ≠ 0) (hZ : ∀ i ≤ n, Z i ≠ 0)
    {Lsq ρ B mr : ℝ} (hL : 4 ≤ Lsq) (hρ0 : 0 ≤ ρ) (hρ8 : ρ ≤ 1 / 8) (hB : 0 ≤ B) (hmr : 0 < mr)
    (hmL : mr * Lsq ^ (n - 1) ≤ 1) (hζb : ∀ i < n, ‖ζ i‖ ≤ ρ)
    (hq : ∀ i < n, ‖dQ ζ e i - 1‖ ≤ 16 / 7 * ρ * B * mr * Lsq ^ i)
    {m A U : ℂ} (hm : ‖m‖ = mr) (hU : U ≠ 0) :
    ‖(1 / m - (1 / m) ^ 2 * (A * (∏ i ∈ range n, (dRho ζ e i)⁻¹ ^ 2) / U +
        ∑ j ∈ range n, m * Z j * ζ j * (∏ i ∈ range j, (dRho ζ e i)⁻¹ ^ 2) / dRho ζ e j)) -
      (1 / (m * Z n) - (1 / m) ^ 2 * (A / Z n) / (Z n * U))‖ ≤
      Lsq ^ (n - 1) / ‖Z n‖ * Real.exp (64 / 7 * ρ * B) *
        (24 * ρ ^ 2 * B + 64 / 7 * ρ * B * (‖A / Z n‖ / (mr * ‖U‖))) := by
  have hm0 : m ≠ 0 := fun h => by rw [h, norm_zero] at hm; linarith
  have hζ1 : ∀ i < n, 7 / 8 ≤ ‖1 + ζ i‖ := fun i hi => by
    have := norm_sub_norm_le (1 : ℂ) (-ζ i)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith [hζb i hi]
  have hζ : ∀ i < n, 1 + ζ i ≠ 0 := fun i hi h => by
    have := hζ1 i hi; rw [h, norm_zero] at this; linarith
  have hZn := hZ n le_rfl
  have hZn0 : 0 < ‖Z n‖ := norm_pos_iff.2 hZn
  set E2 := Real.exp (64 / 7 * ρ * B) with hE2
  have hE20 : 0 < E2 := Real.exp_pos _
  have hL1 : 1 ≤ Lsq := by linarith
  have hL2 : 2 ≤ Lsq := by linarith
  -- partial sums of `|q_i - 1|`
  have hP : ∀ j < n, ∑ i ∈ range (j + 1), ‖dQ ζ e i - 1‖ ≤ 32 / 7 * ρ * B * mr * Lsq ^ j := by
    intro j hj
    calc ∑ i ∈ range (j + 1), ‖dQ ζ e i - 1‖
        ≤ ∑ i ∈ range (j + 1), 16 / 7 * ρ * B * mr * Lsq ^ i :=
          sum_le_sum fun i hi => hq i (by have := mem_range.1 hi; omega)
      _ = 16 / 7 * ρ * B * mr * (∑ i ∈ range j, Lsq ^ i + Lsq ^ j) := by
          rw [← mul_sum, sum_range_succ]
      _ ≤ 16 / 7 * ρ * B * mr * (Lsq ^ j + Lsq ^ j) :=
          mul_le_mul_of_nonneg_left (by linarith [DressedFRD.sum_range_pow_le hL2 j])
            (by positivity)
      _ = 32 / 7 * ρ * B * mr * Lsq ^ j := by ring
  have hmLj : ∀ j < n, mr * Lsq ^ j ≤ 1 := fun j hj =>
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) hmr.le) hmL
  have hQ : ∀ j < n, Real.exp (2 * ∑ i ∈ range (j + 1), ‖dQ ζ e i - 1‖) - 1 ≤
      64 / 7 * ρ * B * mr * Lsq ^ j * E2 := by
    intro j hj
    have h1 := hP j hj
    have h0 : 0 ≤ ∑ i ∈ range (j + 1), ‖dQ ζ e i - 1‖ := sum_nonneg fun _ _ => norm_nonneg _
    have h2 : 2 * ∑ i ∈ range (j + 1), ‖dQ ζ e i - 1‖ ≤ 64 / 7 * ρ * B := by
      have := mul_le_mul_of_nonneg_left (hmLj j hj) (by positivity : (0 : ℝ) ≤ 64 / 7 * ρ * B)
      nlinarith
    refine (wn2_exp_sub_one_le (by linarith) h2).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hE20.le
  -- the decomposition of `dress_suscept`
  have hterm : ∀ j ∈ range n, m * Z j * ζ j * (∏ i ∈ range j, (dRho ζ e i)⁻¹ ^ 2) / dRho ζ e j =
      m * (1 / Z j - 1 / Z (j + 1)) + m * (1 / Z j - 1 / Z (j + 1)) *
        (dQp ζ e j ^ 2 * dQ ζ e j - 1) := fun j hj => by
    have hj := mem_range.1 hj
    rw [dress_term hZs m (hZ j hj.le) (hζ j hj) (hρ j hj)
      (dress_pi hZ0 hZs j (fun i hi => hρ i (by omega)) (fun i hi => hζ i (by omega))
        (fun i hi => hZ i (by omega)))]
    ring
  have hsum := sum_congr rfl hterm
  rw [sum_add_distrib, ← mul_sum, sum_range_sub' (fun j => 1 / Z j), hZ0] at hsum
  rw [hsum, dress_pi hZ0 hZs n hρ hζ (fun i hi => hZ i hi)]
  set T := ∑ j ∈ range n, m * (1 / Z j - 1 / Z (j + 1)) * (dQp ζ e j ^ 2 * dQ ζ e j - 1)
  -- `|T| ≤ 24 m⁴ρ²B E₂ L^{2(n-1)}/|Z_n|`
  have hT : ‖T‖ ≤ 24 * mr ^ 2 * ρ ^ 2 * B * E2 * Lsq ^ (n - 1) / ‖Z n‖ := by
    have hterm' : ∀ j ∈ range n, ‖m * (1 / Z j - 1 / Z (j + 1)) * (dQp ζ e j ^ 2 * dQ ζ e j - 1)‖ ≤
        512 / 49 * mr ^ 2 * ρ ^ 2 * B * E2 / ‖Z n‖ * ((1 + ρ) ^ (n - j) * Lsq ^ j) := by
      intro j hj
      have hj' := mem_range.1 hj
      have hZj0 : 0 < ‖Z j‖ := norm_pos_iff.2 (hZ j hj'.le)
      rw [norm_mul, norm_mul, inv_sub_inv_succ hZs (hZ j hj'.le) (hζ j hj'), norm_div, norm_mul, hm]
      have hq' := (norm_dQp_sq_dQ_sub_one_le (ζ := ζ) (e := e) (Nat.lt_succ_self j)).trans
        (hQ j hj')
      have hgrow := wn2_norm_Z_growth hZs hρ0 hζb j (n - j) (by omega)
      rw [show j + (n - j) = n by omega] at hgrow
      have hfr : ‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖) ≤ 8 / 7 * ρ * (1 + ρ) ^ (n - j) / ‖Z n‖ := by
        rw [div_le_div_iff₀ (mul_pos hZj0 (by linarith [hζ1 j hj'])) hZn0]
        have h1 := hζb j hj'
        have h2 := hζ1 j hj'
        have hp : 0 ≤ (1 + ρ) ^ (n - j) := by positivity
        have h3 : ‖ζ j‖ * ‖Z n‖ ≤ ρ * (‖Z j‖ * (1 + ρ) ^ (n - j)) :=
          mul_le_mul h1 hgrow (norm_nonneg _) hρ0
        have h4 : ρ * (‖Z j‖ * (1 + ρ) ^ (n - j)) ≤
            8 / 7 * ρ * (1 + ρ) ^ (n - j) * (‖Z j‖ * ‖1 + ζ j‖) := by
          have : ρ * (‖Z j‖ * (1 + ρ) ^ (n - j)) * 1 ≤
              ρ * (‖Z j‖ * (1 + ρ) ^ (n - j)) * (8 / 7 * ‖1 + ζ j‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
        linarith
      calc mr * (‖ζ j‖ / (‖Z j‖ * ‖1 + ζ j‖)) * ‖dQp ζ e j ^ 2 * dQ ζ e j - 1‖
          ≤ mr * (8 / 7 * ρ * (1 + ρ) ^ (n - j) / ‖Z n‖) * (64 / 7 * ρ * B * mr * Lsq ^ j * E2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hfr hmr.le) hq' (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc ‖T‖ ≤ ∑ j ∈ range n, 512 / 49 * mr ^ 2 * ρ ^ 2 * B * E2 / ‖Z n‖ *
            ((1 + ρ) ^ (n - j) * Lsq ^ j) := (norm_sum_le _ _).trans (sum_le_sum hterm')
      _ = 512 / 49 * mr ^ 2 * ρ ^ 2 * B * E2 / ‖Z n‖ *
            ∑ j ∈ range n, (1 + ρ) ^ (n - j) * Lsq ^ j := by rw [mul_sum]
      _ ≤ 512 / 49 * mr ^ 2 * ρ ^ 2 * B * E2 / ‖Z n‖ * (9 / 4 * Lsq ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left (wn2_sum_geo hρ0 hρ8 hL n) (by positivity)
      _ ≤ 24 * mr ^ 2 * ρ ^ 2 * B * E2 * Lsq ^ (n - 1) / ‖Z n‖ := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hZn0]
          have : 0 ≤ mr ^ 2 * ρ ^ 2 * B * E2 * Lsq ^ (n - 1) := by positivity
          nlinarith
  -- `|Q_n² - 1|`
  have hQn : ‖dQp ζ e n ^ 2 - 1‖ ≤ 64 / 7 * ρ * B * mr * Lsq ^ (n - 1) * E2 := by
    have h := norm_dQp_sq_sub_one_le (ζ := ζ) (e := e) n
    have h2 := hQ (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at h2
    exact h.trans h2
  have hEq : 1 / m - (1 / m) ^ 2 * (A * (dQp ζ e n ^ 2 / Z n ^ 2) / U + (m * (1 / 1 - 1 / Z n) + T)) -
      (1 / (m * Z n) - (1 / m) ^ 2 * (A / Z n) / (Z n * U)) =
      -((1 / m) ^ 2 * T) - (1 / m) ^ 2 * (A / Z n) / (Z n * U) * (dQp ζ e n ^ 2 - 1) := by
    field_simp
    ring
  rw [hEq]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  have hmi : ‖1 / m‖ = 1 / mr := by rw [norm_div, norm_one, hm]
  have hUn : 0 < ‖U‖ := norm_pos_iff.2 hU
  have hx : ‖(1 / m) ^ 2 * T‖ ≤ 24 * ρ ^ 2 * B * E2 * Lsq ^ (n - 1) / ‖Z n‖ := by
    rw [norm_mul, norm_pow, hmi]
    calc (1 / mr) ^ 2 * ‖T‖ ≤ (1 / mr) ^ 2 * (24 * mr ^ 2 * ρ ^ 2 * B * E2 * Lsq ^ (n - 1) / ‖Z n‖) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = _ := by field_simp
  have hy : ‖(1 / m) ^ 2 * (A / Z n) / (Z n * U) * (dQp ζ e n ^ 2 - 1)‖ ≤
      Lsq ^ (n - 1) / ‖Z n‖ * E2 * (64 / 7 * ρ * B * (‖A / Z n‖ / (mr * ‖U‖))) := by
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_mul (Z n), hmi]
    calc (1 / mr) ^ 2 * ‖A / Z n‖ / (‖Z n‖ * ‖U‖) * ‖dQp ζ e n ^ 2 - 1‖
        ≤ (1 / mr) ^ 2 * ‖A / Z n‖ / (‖Z n‖ * ‖U‖) * (64 / 7 * ρ * B * mr * Lsq ^ (n - 1) * E2) :=
          mul_le_mul_of_nonneg_left hQn (by positivity)
      _ = _ := by field_simp
  have e3 : Lsq ^ (n - 1) / ‖Z n‖ * E2 * (24 * ρ ^ 2 * B + 64 / 7 * ρ * B * (‖A / Z n‖ / (mr * ‖U‖))) =
      24 * ρ ^ 2 * B * E2 * Lsq ^ (n - 1) / ‖Z n‖ +
        Lsq ^ (n - 1) / ‖Z n‖ * E2 * (64 / 7 * ρ * B * (‖A / Z n‖ / (mr * ‖U‖))) := by ring
  rw [e3]
  exact add_le_add hx hy

end Abstract

/-! ### Algebra and sign -/

/-- `m²|Λ|U = m²|Λ|(1+k⁰) + âw` (`â = |Λ|A/z`, `w = m²z t_raw`). -/
theorem wn2_n_eq {m V z : ℝ} (hz : 0 < z) (A tr k0 : ℂ) :
    ((m * V : ℝ) : ℂ) * (1 + (k0 + A * tr)) =
        ((m * V : ℝ) : ℂ) * (1 + k0) + (V : ℂ) * A / (z : ℂ) * ((m : ℂ) * ((z : ℂ) * tr)) := by
  have hz' : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
  push_cast; field_simp; ring

/-- **The normalised form of the leading term.** With `â = |Λ|A/z`, `w = m²z t_raw`,
`n = m²|Λ|(1+k⁰) + âw`: `m²|Λ|U = n` and the leading term is `|Λ|p/(zn)`,
`p = 1 + k⁰ + â(w - 1)/(m²|Λ|)`. -/
theorem wn2_chi0_form {m V z : ℝ} (hm : 0 < m) (hV : 0 < V) (hz : 0 < z) {A tr k0 : ℂ}
    (hU : 1 + (k0 + A * tr) ≠ 0) :
    ((m * V : ℝ) : ℂ) * (1 + (k0 + A * tr)) =
        ((m * V : ℝ) : ℂ) * (1 + k0) + (V : ℂ) * A / (z : ℂ) * ((m : ℂ) * ((z : ℂ) * tr)) ∧
      1 / ((m : ℂ) * (z : ℂ)) - (1 / (m : ℂ)) ^ 2 * (A / (z : ℂ)) / ((z : ℂ) * (1 + (k0 + A * tr))) =
        (V : ℂ) * (1 + k0 + (V : ℂ) * A / (z : ℂ) * ((m : ℂ) * ((z : ℂ) * tr) - 1) /
          ((m * V : ℝ) : ℂ)) /
          ((z : ℂ) * (((m * V : ℝ) : ℂ) * (1 + k0) +
            (V : ℂ) * A / (z : ℂ) * ((m : ℂ) * ((z : ℂ) * tr)))) := by
  have hm' : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm.ne'
  have hV' : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hV.ne'
  have hz' : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
  have h1 : ((m * V : ℝ) : ℂ) * (1 + (k0 + A * tr)) =
      ((m * V : ℝ) : ℂ) * (1 + k0) + (V : ℂ) * A / (z : ℂ) * ((m : ℂ) * ((z : ℂ) * tr)) := by
    push_cast; field_simp; ring
  refine ⟨h1, ?_⟩
  rw [← h1]
  push_cast
  field_simp
  ring

theorem wn2_re_mul_ge (x y : ℂ) : -(‖x‖ * ‖y‖) ≤ x.re * y.re + x.im * y.im ∧
    x.re * y.re + x.im * y.im ≤ ‖x‖ * ‖y‖ := by
  have h := Complex.abs_re_le_norm (x * cj y)
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, norm_mul, Complex.norm_conj] at h
  constructor <;> [skip; skip] <;> nlinarith [abs_le.1 h]

/-- **The real part of the susceptibility on the window**: from `|p - 1| ≤ π` and
`|χ - |Λ|p/(zn)| ≤ (|Λ|/z)(c₀ + c₁a/|n|)`. -/
theorem wn2_re_bounds {V z : ℝ} (hV : 0 < V) (hz : 0 < z) {n p χ : ℂ} {π c₀ c₁ a : ℝ}
    (hn : n ≠ 0) (hp : ‖p - 1‖ ≤ π)
    (hχ : ‖χ - (V : ℂ) * p / ((z : ℂ) * n)‖ ≤ V / z * (c₀ + c₁ * a / ‖n‖)) :
    V / (z * ‖n‖ ^ 2) * (n.re - (π * ‖n‖ + c₀ * ‖n‖ ^ 2 + c₁ * a * ‖n‖)) ≤ χ.re ∧
      χ.re ≤ V / (z * ‖n‖ ^ 2) * (n.re + (π * ‖n‖ + c₀ * ‖n‖ ^ 2 + c₁ * a * ‖n‖)) := by
  have hn0 : 0 < ‖n‖ := norm_pos_iff.2 hn
  have hz' : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
  have e0 : (V : ℂ) * p / ((z : ℂ) * n) = ((V / z : ℝ) : ℂ) * (p / n) := by
    push_cast; field_simp
  have hre : ((V : ℂ) * p / ((z : ℂ) * n)).re =
      V / (z * ‖n‖ ^ 2) * (n.re + ((p - 1).re * n.re + (p - 1).im * n.im)) := by
    rw [e0, Complex.re_ofReal_mul, Complex.div_re, Complex.normSq_eq_norm_sq]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    field_simp
    ring_nf
  obtain ⟨d1, d2⟩ := wn2_re_mul_ge (p - 1) n
  have hd1 : -(π * ‖n‖) ≤ (p - 1).re * n.re + (p - 1).im * n.im :=
    le_trans (neg_le_neg (mul_le_mul_of_nonneg_right hp hn0.le)) d1
  have hd2 : (p - 1).re * n.re + (p - 1).im * n.im ≤ π * ‖n‖ :=
    d2.trans (mul_le_mul_of_nonneg_right hp hn0.le)
  have hd := Complex.abs_re_le_norm (χ - (V : ℂ) * p / ((z : ℂ) * n))
  rw [Complex.sub_re, hre] at hd
  have herr : V / z * (c₀ + c₁ * a / ‖n‖) = V / (z * ‖n‖ ^ 2) * (c₀ * ‖n‖ ^ 2 + c₁ * a * ‖n‖) := by
    field_simp
  have hk : 0 < V / (z * ‖n‖ ^ 2) := by positivity
  have hb := abs_le.1 (hd.trans (hχ.trans_eq herr))
  constructor
  · have := mul_le_mul_of_nonneg_left (by linarith : n.re - (π * ‖n‖ + c₀ * ‖n‖ ^ 2 + c₁ * a * ‖n‖) ≤
      n.re + ((p - 1).re * n.re + (p - 1).im * n.im) - (c₀ * ‖n‖ ^ 2 + c₁ * a * ‖n‖)) hk.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left (by linarith : n.re + ((p - 1).re * n.re + (p - 1).im * n.im) +
      (c₀ * ‖n‖ ^ 2 + c₁ * a * ‖n‖) ≤ n.re + (π * ‖n‖ + c₀ * ‖n‖ ^ 2 + c₁ * a * ‖n‖)) hk.le
    nlinarith

/-! ### `Z_j` is a positive real number along a trajectory -/

theorem Zr_real_pos {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1) (Λ b μ₀ : ℝ) (j : ℕ) :
    ∃ z : ℝ, 0 < z ∧ Zr R (traj (rgData R) Λ b μ₀) j = z := by
  obtain ⟨H, -, -⟩ := traj_real R hρ0 hρ1 Λ b μ₀ j
  obtain ⟨hZp, -, hb⟩ := rawHist_struct R hρ0 j (traj (rgData R) Λ b μ₀)
  set st := rawHist R j (traj (rgData R) Λ b μ₀)
  have hre : ∀ i, st.ζ i = ((st.ζ i).re : ℂ) := fun i => (Complex.conj_eq_iff_re.1 (H.ζ i)).symm
  refine ⟨∏ i ∈ range j, (1 + (st.ζ i).re), prod_pos fun i _ => ?_, ?_⟩
  · have h1 := (Complex.abs_re_le_norm (st.ζ i)).trans (hb i)
    linarith [neg_abs_le (st.ζ i).re]
  · show st.Z = _
    rw [hZp]; push_cast
    exact prod_congr rfl fun i _ => by rw [← hre i]

/-! ### Along the flow -/

section Flow

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **`suscept2_dressed` with the geometric error** (`dress_suscept_geo`, `EpsZeroSmall`). -/
theorem suscept2_dressed_geo (hL7 : 7 ≤ L) {Nh : ℕ} (hN : Nh + 2 = N) (hρ8 : R.ρ ≤ 1 / 8)
    (hspl : SplitSmall R.P L R.ρ) {B : ℝ} (hB : 0 ≤ B) (hE : EpsZeroSmall R.P L R.ρ B)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) (hu : (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) ≠ 0) :
    ‖(1 / (R.msq : ℂ) - (1 / (R.msq : ℂ)) ^ 2 *
        (aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t / (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
          ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t)) -
      (1 / ((R.msq : ℂ) * Zr R t (Nh + 2)) - (1 / (R.msq : ℂ)) ^ 2 *
        (aFin (Nh + 1) (lastOut R Nh t) / Zr R t (Nh + 2)) / (Zr R t (Nh + 2) * (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ))))‖ ≤
      ((L : ℝ) ^ 2) ^ (Nh + 1) / ‖Zr R t (Nh + 2)‖ * Real.exp (64 / 7 * R.ρ * B) *
        (24 * R.ρ ^ 2 * B + 64 / 7 * R.ρ * B *
          (‖aFin (Nh + 1) (lastOut R Nh t) / Zr R t (Nh + 2)‖ / (R.msq * ‖(1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ))‖))) := by
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hρ1 : R.ρ < 1 := by linarith
  have hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t) := rawInv_histU R hV hVL t
  have hS : ∀ j ≤ Nh + 1, SplitOK R j (rawHist R j t) :=
    fun j hj => splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega)
  have hρ : ∀ i < Nh + 2, dRho (ζr R t) (eh R t) i ≠ 0 := fun i hi => by
    rw [← ρh_eq R (hRI i (by omega))]; exact (hS i (by omega)).1 0
  have hZ : ∀ i ≤ Nh + 2, Zr R t i ≠ 0 := fun i _ => by
    obtain ⟨hZp, -, hb⟩ := rawHist_struct R hρ0 i t
    show (rawHist R i t).Z ≠ 0
    rw [hZp]
    exact prod_ne_zero_iff.2 fun k _ => Step2.one_add_ne_zero ((hb k).trans_lt hρ1)
  have hπ : ∀ j ≤ Nh + 2, πh R j t = ∏ i ∈ range j, (dRho (ζr R t) (eh R t) i)⁻¹ ^ 2 :=
    fun j hj => prod_congr rfl fun i hi => by
      rw [ρh_eq R (hRI i (by have := mem_range.1 hi; omega))]
  have hsum : ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t =
      ∑ j ∈ range (Nh + 2), (R.msq : ℂ) * Zr R t j * ζr R t j *
        (∏ i ∈ range j, (dRho (ζr R t) (eh R t) i)⁻¹ ^ 2) / dRho (ζr R t) (eh R t) j :=
    sum_congr rfl fun j hj => by
      have hj' := mem_range.1 hj
      rw [ch₀_eq R (hRI j (by omega)), hπ j hj'.le, ρh_eq R (hRI j (by omega))]
  rw [hsum, hπ (Nh + 2) le_rfl]
  have hL4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (7 : ℝ) ≤ L := by exact_mod_cast hL7
    nlinarith
  have hζb : ∀ i < Nh + 2, ‖ζr R t i‖ ≤ R.ρ := fun i _ => absorb_le R hρ0 _ _
  have hq : ∀ i < Nh + 2, ‖dQ (ζr R t) (eh R t) i - 1‖ ≤
      16 / 7 * R.ρ * B * R.msq * ((L : ℝ) ^ 2) ^ i := by
    intro i hi
    have hez := eh_zp_bound R hL7 hρ0 hE (by omega : 1 ≤ N) hm0 hm t (by omega : i < N)
      (hRI i (by omega)) (hZ i (by omega))
    have h1 := norm_dQ_sub_one_le_zp (e := eh R t) ((hζb i hi).trans hρ8) hez.1
    have h2 : ‖ζr R t i‖ * ‖eh R t i‖ ≤ R.ρ * (B * R.msq * (L : ℝ) ^ (2 * i)) :=
      mul_le_mul (hζb i hi) hez.2 (norm_nonneg _) hρ0
    rw [← pow_mul]
    nlinarith
  have hmL : R.msq * ((L : ℝ) ^ 2) ^ (Nh + 2 - 1) ≤ 1 := by
    have h := msq_mul_pow_le_one (L := L) (by omega) (by omega : 1 ≤ N) hm
    rw [show N - 1 = Nh + 1 by omega] at h
    rw [show Nh + 2 - 1 = Nh + 1 by omega, ← pow_mul]; exact h
  have h := dress_suscept_geo (Z := Zr R t) (ζ := ζr R t) (e := eh R t) (Zr_zero R t) (Zr_succ R t)
    (n := Nh + 2) (by omega) hρ hZ hL4 hρ0 hρ8 hB hm0 hmL hζb hq (m := (R.msq : ℂ))
    (A := aFin (Nh + 1) (lastOut R Nh t)) (by rw [Complex.norm_real, Real.norm_of_nonneg hm0.le]) hu
  rwa [show Nh + 2 - 1 = Nh + 1 by omega] at h

end Flow

end

end PtCorr2
