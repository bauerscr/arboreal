import Obs.FlowObsBd

/-!
# Conversion lemmas and geometric sums (Sections `sec:obs`, `sec:proofs`)

## Conversion of scale factors into powers of `|a - b|`
With `r = |a - b|_∞` (`supNorm (a - b)`), `a ≠ b`, and the coalescence scale
`j_ab = ⌊log_L (2 r)⌋` (`Obs.coal`), one has `L^{j_ab} ≤ 2 r < L^{j_ab + 1}` and
`2 r ≤ L^N` on `Λ_N`.  Hence, for `s ≥ 0` and `L ≥ 2`,
* `(L^{-s})^{j_ab} ≤ L^s r^{-s}` (`pow_coal_le`; with `θ = L^{-κ}`: `θ^{j_ab} ≤ L^κ r^{-κ}`);
* `ℓ_{j_ab}^2 ≤ ℓ₀^2 L^{d-2} r^{-(d-2)}` (`ellj_coal_sq_le`);
* `(L^{-s})^N ≤ r^{-s}` (`pow_N_le`; no hypothesis `r ≤ L^N` is needed, it holds on the
  torus), and `ℓ_N^2 ≤ ℓ₀^2 r^{-(d-2)}` (`ellj_N_sq_le`);
* the combinations `ℓ_{j_ab}^2 θ^{j_ab}`, `ℓ_{j_ab}^4 θ^{j_ab}` (`ellj_coal_sq_mul_pow_le`,
  `ellj_coal_pow_four_mul_pow_le`).
The flow bounds are stated with `L^{-(κ j)}` (a real power); `rpow_neg_mul_nat` converts this to
`(L^{-κ})^j`, `rpow_neg_mul_mono_one` compares two rates (`L^{-κ j} ≤ L^{-κ' j}` for `κ' ≤ κ`),
and `theta_one` gives `0 ≤ θ < 1` for `θ = L^{-κ}`.

This makes precise the remark of the proof of `lem:2pt` (the text writes `|a - b| ≤ L`, which
should read `L^{j_ab} ≤ 2|a - b| < L^{j_ab+1}`).

## Geometric sums
With `ρ = L^{-(d-2)} ≤ 1/2` (`d ≥ 3`, `L ≥ 2`) and `ℓ_k^2 = ℓ₀^2 ρ^k` (`Obs.ellj_sq`):
* `∑_{k ≥ m} x^k ≤ x^m / (1 - x)`, `≤ 2 x^m` for `x ≤ 1/2` (`sum_ite_pow_le`, `sum_ite_pow_le_two`,
  `sum_Ico_pow_le`);
* `∑_{k ≥ m} ℓ_k^2 θ^k ≤ 2 ℓ_m^2 θ^m` for `0 ≤ θ ≤ 1` (`sum_ite_ellj_sq_pow_le`), in particular
  `∑_{k ≥ j} ℓ_k^2 ≤ 2 ℓ_j^2` (`sum_Ico_ellj_sq_le`) and `∑_k ℓ_{k+1}^2 ≤ ℓ₀^2`
  (`sum_ellj_succ_sq_le`);
* for the covariances of the flow, `∑_{k < j, k + 1 ≥ m} θ^{k+1} |C_{k+1}(x,y)| ≤ 2 θ^m ℓ_m^2`
  (`sum_ite_pow_abs_covAt_le`) and, by finite range,
  `∑_{k < j} θ^{k+1} |C_{k+1}(a,b)| ≤ 2 θ^{j ∧ j_ab} ℓ_{j ∧ j_ab}^2` (`sum_pow_abs_covAt_le`,
  the weighted form of `Obs.sum_cov_le`).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Real powers -/

/-- `x^{-(s k)} = (x^{-s})^k`. -/
theorem rpow_neg_mul_nat {x : ℝ} (hx : 0 ≤ x) (s : ℝ) (k : ℕ) :
    x ^ (-(s * k)) = (x ^ (-s)) ^ k := by
  rw [← Real.rpow_natCast (x ^ (-s)) k, ← Real.rpow_mul hx, neg_mul]

/-- `L^{-(κ j)} ≤ L^{-(κ' j)}` for `κ' ≤ κ` and `L ≥ 1`. -/
theorem rpow_neg_mul_mono_one {L : ℝ} (hL : 1 ≤ L) {κ κ' : ℝ} (h : κ' ≤ κ) (j : ℕ) :
    L ^ (-(κ * j)) ≤ L ^ (-(κ' * j)) := by
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  have : κ' * (j : ℝ) ≤ κ * j := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg j)
  linarith

/-- `θ = L^{-κ}` satisfies `0 ≤ θ < 1` for `L > 1`, `κ > 0`. -/
theorem theta_one {L : ℝ} (hL : 1 < L) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ L ^ (-κ) ∧ L ^ (-κ) < 1 :=
  ⟨Real.rpow_nonneg (by linarith) _, Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)⟩

theorem Lr_pos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

/-- `ρ = L^{-(d-2)} ≤ 1/2`. -/
theorem rho_le_half (hd : 3 ≤ d) (hL : 2 ≤ L) : (L : ℝ) ^ (-((d : ℝ) - 2)) ≤ 1 / 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h1 : (L : ℝ) ^ (-((d : ℝ) - 2)) ≤ (L : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1
      (by have h3 : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith)
  rw [Real.rpow_neg_one] at h1
  have h2 : (L : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hL)
  linarith

/-! ### `|a - b|` and the coalescence scale -/

/-- `a ≠ b → 1 ≤ |a - b|_∞`. -/
theorem one_le_supNorm_sub {a b : Lam d L N} (hab : a ≠ b) : 1 ≤ supNorm (a - b) := by
  by_contra h
  apply hab
  have hi : ∀ i, ((a - b : Lam d L N) : Fin d → ZMod (L ^ N)) i = 0 := by
    intro i
    have hle : zabs (((a - b : Lam d L N) : Fin d → ZMod (L ^ N)) i) ≤ supNorm (a - b) :=
      Finset.le_sup (f := fun i => zabs (((a - b : Lam d L N) : Fin d → ZMod (L ^ N)) i))
        (mem_univ i)
    exact (zabs_eq_zero_iff _).1 (by omega)
  exact sub_eq_zero.1 (funext hi)

theorem supNorm_sub_pos {a b : Lam d L N} (hab : a ≠ b) : (0 : ℝ) < supNorm (a - b) := by
  have := one_le_supNorm_sub hab
  exact_mod_cast (by omega : 0 < supNorm (a - b))

/-- `2 |a - b|_∞ < L^{j_ab + 1}`. -/
theorem two_supNorm_lt_pow_coal (hL : 2 ≤ L) (a b : Lam d L N) :
    2 * (supNorm (a - b) : ℝ) < (L : ℝ) ^ (coal L a b + 1) := by
  have h := Nat.lt_pow_succ_log_self (by omega : 1 < L) (2 * supNorm (a - b))
  have : ((2 * supNorm (a - b) : ℕ) : ℝ) < ((L ^ (coal L a b + 1) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at this
  exact this

/-- `|a - b|_∞ ≤ L^N` on `Λ_N`. -/
theorem supNorm_le_pow (a b : Lam d L N) : (supNorm (a - b) : ℝ) ≤ (L : ℝ) ^ N := by
  have h := two_mul_supNorm_le (a - b)
  have : ((supNorm (a - b) : ℕ) : ℝ) ≤ ((L ^ N : ℕ) : ℝ) := by exact_mod_cast (by omega)
  push_cast at this
  exact this

/-- **Conversion**: `(L^{-s})^{j_ab} ≤ L^s |a - b|^{-s}`. -/
theorem pow_coal_le (hL : 2 ≤ L) {s : ℝ} (hs : 0 ≤ s) {a b : Lam d L N} (hab : a ≠ b) :
    ((L : ℝ) ^ (-s)) ^ coal L a b ≤ (L : ℝ) ^ s * (supNorm (a - b) : ℝ) ^ (-s) := by
  have hL0 : (0 : ℝ) < L := Lr_pos
  have hr := supNorm_sub_pos hab
  set r : ℝ := ((supNorm (a - b) : ℕ) : ℝ)
  set k := coal L a b
  have hX : r / L < (L : ℝ) ^ k := by
    have h := two_supNorm_lt_pow_coal hL a b
    rw [pow_succ] at h
    rw [div_lt_iff₀ hL0]; linarith
  have e1 : ((L : ℝ) ^ (-s)) ^ k = ((L : ℝ) ^ k) ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast (L : ℝ) k,
      ← Real.rpow_mul hL0.le, mul_comm]
  rw [e1]
  calc ((L : ℝ) ^ k) ^ (-s) ≤ (r / L) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hX.le (by linarith)
    _ = (L : ℝ) ^ s * r ^ (-s) := by
        rw [Real.div_rpow hr.le hL0.le, Real.rpow_neg hL0.le, div_eq_mul_inv, inv_inv, mul_comm]

/-- **Conversion**: `(L^{-s})^N ≤ |a - b|^{-s}` (as `|a - b| ≤ L^N`). -/
theorem pow_N_le {s : ℝ} (hs : 0 ≤ s) {a b : Lam d L N} (hab : a ≠ b) :
    ((L : ℝ) ^ (-s)) ^ N ≤ (supNorm (a - b) : ℝ) ^ (-s) := by
  have hL0 : (0 : ℝ) < L := Lr_pos
  have e1 : ((L : ℝ) ^ (-s)) ^ N = ((L : ℝ) ^ N) ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast (L : ℝ) N,
      ← Real.rpow_mul hL0.le, mul_comm]
  rw [e1]
  exact Real.rpow_le_rpow_of_nonpos (supNorm_sub_pos hab) (supNorm_le_pow a b) (by linarith)

theorem pow_mul_pow_rpow {x : ℝ} (hx : 0 < x) (s t : ℝ) (k : ℕ) :
    (x ^ (-s)) ^ k * (x ^ (-t)) ^ k = (x ^ (-(s + t))) ^ k := by
  rw [← mul_pow, ← Real.rpow_add hx, neg_add]

/-- `ℓ_{j_ab}^2 (L^{-s})^{j_ab} ≤ ℓ₀^2 L^{d-2+s} |a - b|^{-(d-2+s)}`. -/
theorem ellj_coal_sq_mul_pow_le (hd : 2 ≤ d) (hL : 2 ≤ L) (ℓ₀ : ℝ) {s : ℝ} (hs : 0 ≤ s)
    {a b : Lam d L N} (hab : a ≠ b) :
    ellj d L ℓ₀ (coal L a b) ^ 2 * ((L : ℝ) ^ (-s)) ^ coal L a b ≤
      ℓ₀ ^ 2 * ((L : ℝ) ^ ((d : ℝ) - 2 + s) *
        (supNorm (a - b) : ℝ) ^ (-((d : ℝ) - 2 + s))) := by
  have hd' : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [ellj_sq, mul_assoc, pow_mul_pow_rpow Lr_pos]
  exact mul_le_mul_of_nonneg_left (pow_coal_le hL (by linarith) hab) (sq_nonneg _)

/-- `ℓ_{j_ab}^4 (L^{-s})^{j_ab} ≤ ℓ₀^4 L^{2(d-2)+s} |a - b|^{-(2(d-2)+s)}`. -/
theorem ellj_coal_pow_four_mul_pow_le (hd : 2 ≤ d) (hL : 2 ≤ L) (ℓ₀ : ℝ) {s : ℝ} (hs : 0 ≤ s)
    {a b : Lam d L N} (hab : a ≠ b) :
    ellj d L ℓ₀ (coal L a b) ^ 4 * ((L : ℝ) ^ (-s)) ^ coal L a b ≤
      ℓ₀ ^ 4 * ((L : ℝ) ^ (2 * ((d : ℝ) - 2) + s) *
        (supNorm (a - b) : ℝ) ^ (-(2 * ((d : ℝ) - 2) + s))) := by
  have hd' : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [show ellj d L ℓ₀ (coal L a b) ^ 4 = ellj d L ℓ₀ (coal L a b) ^ 2 *
      ellj d L ℓ₀ (coal L a b) ^ 2 by ring, ellj_sq]
  rw [show ℓ₀ ^ 2 * ((L : ℝ) ^ (-((d : ℝ) - 2))) ^ coal L a b *
      (ℓ₀ ^ 2 * ((L : ℝ) ^ (-((d : ℝ) - 2))) ^ coal L a b) * ((L : ℝ) ^ (-s)) ^ coal L a b =
      ℓ₀ ^ 4 * (((L : ℝ) ^ (-((d : ℝ) - 2))) ^ coal L a b *
        ((L : ℝ) ^ (-((d : ℝ) - 2))) ^ coal L a b * ((L : ℝ) ^ (-s)) ^ coal L a b) by ring,
    pow_mul_pow_rpow Lr_pos, pow_mul_pow_rpow Lr_pos,
    show (d : ℝ) - 2 + ((d : ℝ) - 2) + s = 2 * ((d : ℝ) - 2) + s by ring]
  exact mul_le_mul_of_nonneg_left (pow_coal_le hL (by linarith) hab) (by positivity)

/-! ### Geometric sums -/

/-- `∑_{m ≤ k < n} x^k ≤ x^m / (1 - x)`. -/
theorem sum_ite_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m n : ℕ) :
    ∑ k ∈ range n, (if m ≤ k then x ^ k else 0) ≤ x ^ m / (1 - x) := by
  rw [sum_geom_ite_eq (ne_of_lt hx1) m n]
  have : 0 ≤ x ^ max m n := by positivity
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `∑_{m ≤ k < n} x^k ≤ 2 x^m` for `0 ≤ x ≤ 1/2`. -/
theorem sum_ite_pow_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (m n : ℕ) :
    ∑ k ∈ range n, (if m ≤ k then x ^ k else 0) ≤ 2 * x ^ m := by
  refine (sum_ite_pow_le hx0 (by linarith) m n).trans ?_
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ x ^ m := by positivity
  nlinarith

theorem sum_Ico_eq_sum_ite {M : Type*} [AddCommMonoid M] (f : ℕ → M) (j n : ℕ) :
    ∑ k ∈ Ico j n, f k = ∑ k ∈ range n, (if j ≤ k then f k else 0) := by
  rw [← sum_filter]
  congr 1
  ext k
  simp [mem_Ico, and_comm]

/-- `∑_{j ≤ k < n} x^k ≤ x^j / (1 - x)`. -/
theorem sum_Ico_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (j n : ℕ) :
    ∑ k ∈ Ico j n, x ^ k ≤ x ^ j / (1 - x) := by
  rw [sum_Ico_eq_sum_ite]; exact sum_ite_pow_le hx0 hx1 j n

/-- `∑_{m ≤ k < n} ℓ_k^2 θ^k ≤ 2 ℓ_m^2 θ^m` for `0 ≤ θ ≤ 1`. -/
theorem sum_ite_ellj_sq_pow_le (hd : 3 ≤ d) (hL : 2 ≤ L) (ℓ₀ : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (m n : ℕ) :
    ∑ k ∈ range n, (if m ≤ k then ellj d L ℓ₀ k ^ 2 * θ ^ k else 0) ≤
      2 * (ellj d L ℓ₀ m ^ 2 * θ ^ m) := by
  set ρ : ℝ := (L : ℝ) ^ (-((d : ℝ) - 2)) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ := rho_le_half hd hL
  have hx0 : 0 ≤ ρ * θ := mul_nonneg hρ0 hθ0
  have hx : ρ * θ ≤ 1 / 2 := (mul_le_of_le_one_right hρ0 hθ1).trans hρ
  have e : ∀ k, (if m ≤ k then ellj d L ℓ₀ k ^ 2 * θ ^ k else 0) =
      ℓ₀ ^ 2 * (if m ≤ k then (ρ * θ) ^ k else 0) := by
    intro k
    split_ifs
    · rw [ellj_sq, mul_pow]; ring
    · ring
  simp only [e, ← mul_sum]
  calc ℓ₀ ^ 2 * ∑ k ∈ range n, (if m ≤ k then (ρ * θ) ^ k else 0)
      ≤ ℓ₀ ^ 2 * (2 * (ρ * θ) ^ m) :=
        mul_le_mul_of_nonneg_left (sum_ite_pow_le_two hx0 hx m n) (sq_nonneg _)
    _ = 2 * (ellj d L ℓ₀ m ^ 2 * θ ^ m) := by rw [ellj_sq, mul_pow]; ring

/-- `∑_{j ≤ k < n} ℓ_k^2 θ^k ≤ 2 ℓ_j^2 θ^j` for `0 ≤ θ ≤ 1`. -/
theorem sum_Ico_ellj_sq_pow_le (hd : 3 ≤ d) (hL : 2 ≤ L) (ℓ₀ : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (j n : ℕ) :
    ∑ k ∈ Ico j n, ellj d L ℓ₀ k ^ 2 * θ ^ k ≤ 2 * (ellj d L ℓ₀ j ^ 2 * θ ^ j) := by
  rw [sum_Ico_eq_sum_ite]; exact sum_ite_ellj_sq_pow_le hd hL ℓ₀ hθ0 hθ1 j n

/-! ### Sums of the covariances of the flow -/

/-- `∑_{k < j, k + 1 ≥ m} θ^{k+1} |C_{k+1}(x, y)| ≤ 2 θ^m ℓ_m^2` for `0 ≤ θ ≤ 1` (any `x, y`). -/
theorem sum_ite_pow_abs_covAt_le (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (x y : Lam d L N) {j : ℕ} (hj : j ≤ N)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) :
    ∑ k ∈ range j, (if m ≤ k + 1 then θ ^ (k + 1) * |Flow.covAt d L N msq k x y| else 0) ≤
      2 * (θ ^ m * ellj d L ℓ₀ m ^ 2) := by
  have h1 : ∀ k ∈ range j,
      (if m ≤ k + 1 then θ ^ (k + 1) * |Flow.covAt d L N msq k x y| else 0) ≤
        (fun k => if m ≤ k then ellj d L ℓ₀ k ^ 2 * θ ^ k else 0) (k + 1) := by
    intro k hk
    rw [mem_range] at hk
    simp only
    split_ifs
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_cov_le hℓ₀ (hC k (by omega)) x y) (by positivity)
    · exact le_rfl
  refine (sum_le_sum h1).trans ?_
  have e := sum_range_succ' (fun k => if m ≤ k then ellj d L ℓ₀ k ^ 2 * θ ^ k else 0) j
  have h2 := sum_ite_ellj_sq_pow_le hd hL ℓ₀ hθ0 hθ1 m (j + 1)
  have h0 : 0 ≤ (fun k => if m ≤ k then ellj d L ℓ₀ k ^ 2 * θ ^ k else 0) 0 := by
    simp only; split_ifs <;> positivity
  rw [e] at h2
  have : 2 * (ellj d L ℓ₀ m ^ 2 * θ ^ m) = 2 * (θ ^ m * ellj d L ℓ₀ m ^ 2) := by ring
  linarith

/-- **Weighted form of `Obs.sum_cov_le`**: for `0 ≤ θ ≤ 1` and `j ≤ N`,
`∑_{k < j} θ^{k+1} |C_{k+1}(a, b)| ≤ 2 θ^{j ∧ j_ab} ℓ_{j ∧ j_ab}^2`. -/
theorem sum_pow_abs_covAt_le (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N) {j : ℕ} (hj : j ≤ N)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∑ k ∈ range j, θ ^ (k + 1) * |Flow.covAt d L N msq k a b| ≤
      2 * (θ ^ min j (coal L a b) * ellj d L ℓ₀ (min j (coal L a b)) ^ 2) := by
  refine le_trans (le_of_eq (sum_congr rfl fun k hk => ?_))
    (sum_ite_pow_abs_covAt_le hd hL hℓ₀ hC a b hj hθ0 hθ1 (min j (coal L a b)))
  rw [mem_range] at hk
  split_ifs with h
  · rfl
  · rw [C_eq_zero_of_lt_coal (hC k (by omega)) (by omega) (by omega), abs_zero, mul_zero]

/-- `∑_{k < j} |C_{k+1}(x, y)| ≤ 2 ℓ₀^2` for any `x, y`. -/
theorem sum_abs_covAt_le (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (x y : Lam d L N) {j : ℕ}
    (hj : j ≤ N) : ∑ k ∈ range j, |Flow.covAt d L N msq k x y| ≤ 2 * ℓ₀ ^ 2 := by
  have h := sum_ite_pow_abs_covAt_le hd hL hℓ₀ hC x y hj zero_le_one le_rfl 0
  have e : ellj d L ℓ₀ 0 = ℓ₀ := by simp [ellj]
  simpa [e] using h

end

end PtCorr
