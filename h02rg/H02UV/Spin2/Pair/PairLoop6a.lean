import Spin2.Pair.PairLoop5
import Spin2.Pair.PairEReq

/-!
# The constant loop, per scale (1): profiles and convolutions (pure)

The per-scale bookkeeping of the `E`-step sizes (`Spin2/Pair/PairLoop6b–c`) is done with three
*profiles* along the scales `n ≥ j` (`h = 1/2`, `r_i = cǧ_i`, `k₀` the seed, `m̄` the `V`-bound):

* `G₀(n) = h^{n-j}k₀ + m̄∑_{j≤i<n}h^{n-i}r_i²` (second order + seed);
* `FO(n) = G₀(n) + m̄∑_{j≤i<n}h^{n-i}r_i` (first order: the `S` sources);
* `NF(n) = G₀(n) + m̄r_n²` (the normal form of `Spin2/Pair/PairLoop5`, `q = 1/2`).

All three satisfy `f(n) ≤ 2f(n+1)`, so convolutions with kernels `a ≤ 1/4` do not increase them
(**`pl6_conv_le`**, **`pl6_conv_le_succ`**); a first-order profile times `r_n` is of normal form
(**`pl6_mul_FO`**, **`pl6_conv_rFO`**). The ratio facts of the history are collected in
**`PL6H`** (field scale `s`, `|β_{a,k}|`, `r`, `|a−b|_∞`).
-/

namespace Spin2

open Finset

noncomputable section

/-! ### Profiles -/

/-- The seed profile `h^{n-j}k₀`. -/
def pl6P (j : ℕ) (k₀ : ℝ) (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n - j) * k₀

/-- `∑_{j≤i<n}h^{n-i}r_i²`. -/
def pl6Q (j : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Ico j n, (1 / 2 : ℝ) ^ (n - i) * r i ^ 2

/-- `∑_{j≤i<n}h^{n-i}r_i`. -/
def pl6F (j : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Ico j n, (1 / 2 : ℝ) ^ (n - i) * r i

/-- `G₀ = P + m̄Q`. -/
def pl6G0 (j : ℕ) (k₀ mb : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ := pl6P j k₀ n + mb * pl6Q j r n

/-- The first-order profile `FO = G₀ + m̄F`. -/
def pl6FO (j : ℕ) (k₀ mb : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ := pl6G0 j k₀ mb r n + mb * pl6F j r n

/-- The normal form `NF = G₀ + m̄r_n²`. -/
def pl6NF (j : ℕ) (k₀ mb : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ := pl6G0 j k₀ mb r n + mb * r n ^ 2

/-- One step of a convolution: `∑_{j≤i≤k}a^{k+1-i}f_i = a(∑_{j≤i<k}a^{k-i}f_i + f_k)`. -/
theorem pl6_conv_succ (a : ℝ) (f : ℕ → ℝ) {j k : ℕ} (hjk : j ≤ k) :
    ∑ i ∈ Ico j (k + 1), a ^ (k + 1 - i) * f i =
      a * (∑ i ∈ Ico j k, a ^ (k - i) * f i + f k) := by
  rw [sum_Ico_succ_top hjk, show k + 1 - k = 1 by omega, pow_one, mul_add, mul_sum]
  congr 1
  exact sum_congr rfl fun i hi => by
    rw [show k + 1 - i = (k - i) + 1 by have := (mem_Ico.1 hi).2; omega, pow_succ]; ring

theorem pl6P_succ (j : ℕ) (k₀ : ℝ) {n : ℕ} (hn : j ≤ n) : pl6P j k₀ (n + 1) = pl6P j k₀ n / 2 := by
  unfold pl6P; rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]; ring

theorem pl6Q_succ (j : ℕ) (r : ℕ → ℝ) {n : ℕ} (hn : j ≤ n) :
    pl6Q j r (n + 1) = (pl6Q j r n + r n ^ 2) / 2 := by
  unfold pl6Q; rw [pl6_conv_succ _ _ hn]; ring

theorem pl6F_succ (j : ℕ) (r : ℕ → ℝ) {n : ℕ} (hn : j ≤ n) :
    pl6F j r (n + 1) = (pl6F j r n + r n) / 2 := by
  unfold pl6F; rw [pl6_conv_succ _ _ hn]; ring

section Prof

variable {j : ℕ} {k₀ mb : ℝ} {r : ℕ → ℝ}

theorem pl6P_nonneg (hk : 0 ≤ k₀) (n : ℕ) : 0 ≤ pl6P j k₀ n := by unfold pl6P; positivity

theorem pl6Q_nonneg (n : ℕ) : 0 ≤ pl6Q j r n := by
  unfold pl6Q; exact sum_nonneg fun i _ => by positivity

theorem pl6F_nonneg (hr : ∀ i, 0 ≤ r i) (n : ℕ) : 0 ≤ pl6F j r n := by
  unfold pl6F; exact sum_nonneg fun i _ => mul_nonneg (by positivity) (hr i)

theorem pl6G0_nonneg (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (n : ℕ) : 0 ≤ pl6G0 j k₀ mb r n := by
  unfold pl6G0; have := pl6P_nonneg (j := j) hk n; have := pl6Q_nonneg (j := j) (r := r) n
  positivity

theorem pl6FO_nonneg (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (hr : ∀ i, 0 ≤ r i) (n : ℕ) :
    0 ≤ pl6FO j k₀ mb r n := by
  unfold pl6FO; have := pl6G0_nonneg (j := j) (r := r) hk hm n
  have := pl6F_nonneg (j := j) hr n; positivity

theorem pl6NF_nonneg (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (n : ℕ) : 0 ≤ pl6NF j k₀ mb r n := by
  unfold pl6NF; have := pl6G0_nonneg (j := j) (r := r) hk hm n; positivity

theorem pl6G0_le_FO (hm : 0 ≤ mb) (hr : ∀ i, 0 ≤ r i) (n : ℕ) :
    pl6G0 j k₀ mb r n ≤ pl6FO j k₀ mb r n := by
  unfold pl6FO; have := pl6F_nonneg (j := j) hr n; nlinarith

theorem pl6G0_le_NF (hm : 0 ≤ mb) (n : ℕ) : pl6G0 j k₀ mb r n ≤ pl6NF j k₀ mb r n := by
  unfold pl6NF; have := sq_nonneg (r n); nlinarith

theorem pl6G0_two (hk : 0 ≤ k₀) (hm : 0 ≤ mb) {n : ℕ} (hn : j ≤ n) :
    pl6G0 j k₀ mb r n ≤ 2 * pl6G0 j k₀ mb r (n + 1) := by
  unfold pl6G0; rw [pl6P_succ j k₀ hn, pl6Q_succ j r hn]
  have := sq_nonneg (r n); nlinarith

theorem pl6FO_two (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (hr : ∀ i, 0 ≤ r i) {n : ℕ} (hn : j ≤ n) :
    pl6FO j k₀ mb r n ≤ 2 * pl6FO j k₀ mb r (n + 1) := by
  unfold pl6FO pl6G0; rw [pl6P_succ j k₀ hn, pl6Q_succ j r hn, pl6F_succ j r hn]
  have := sq_nonneg (r n); have := hr n; nlinarith

theorem pl6NF_two (hk : 0 ≤ k₀) (hm : 0 ≤ mb) {n : ℕ} (hn : j ≤ n) :
    pl6NF j k₀ mb r n ≤ 2 * pl6NF j k₀ mb r (n + 1) := by
  unfold pl6NF pl6G0; rw [pl6P_succ j k₀ hn, pl6Q_succ j r hn]
  have := sq_nonneg (r n); have := sq_nonneg (r (n + 1)); nlinarith

end Prof

/-! ### Convolutions -/

/-- **A convolution with `a ≤ 1/4` does not increase a doubling profile.** -/
theorem pl6_conv_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) {f : ℕ → ℝ} {j : ℕ}
    (hf0 : ∀ n, 0 ≤ f n) (hf2 : ∀ n, j ≤ n → f n ≤ 2 * f (n + 1)) (k : ℕ) :
    ∑ i ∈ Ico j k, a ^ (k - i) * f i ≤ f k := by
  rcases lt_or_ge k j with hkj | hjk
  · rw [Ico_eq_empty_of_le hkj.le, sum_empty]; exact hf0 k
  induction k, hjk using Nat.le_induction with
  | base => rw [Ico_self, sum_empty]; exact hf0 j
  | succ k hk ih =>
    rw [pl6_conv_succ a f hk]
    have h2 := hf2 k hk
    have h1 := hf0 (k + 1)
    have h3 : a * (∑ i ∈ Ico j k, a ^ (k - i) * f i + f k) ≤ a * (f k + f k) :=
      mul_le_mul_of_nonneg_left (by linarith [ih]) ha0
    nlinarith

/-- **The shifted convolution** `∑_{j≤i<k}a^{k-i}f_{i+1} ≤ f_k`. -/
theorem pl6_conv_le_succ {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) {f : ℕ → ℝ} {j : ℕ}
    (hf0 : ∀ n, 0 ≤ f n) (hf2 : ∀ n, j ≤ n → f n ≤ 2 * f (n + 1)) (k : ℕ) :
    ∑ i ∈ Ico j k, a ^ (k - i) * f (i + 1) ≤ f k := by
  rcases lt_or_ge k j with hkj | hjk
  · rw [Ico_eq_empty_of_le hkj.le, sum_empty]; exact hf0 k
  induction k, hjk using Nat.le_induction with
  | base => rw [Ico_self, sum_empty]; exact hf0 j
  | succ k hk ih =>
    rw [pl6_conv_succ a (fun i => f (i + 1)) hk]
    have h2 := hf2 k hk
    have h1 := hf0 (k + 1)
    have h3 : a * (∑ i ∈ Ico j k, a ^ (k - i) * f (i + 1) + f (k + 1)) ≤ a * (f k + f (k + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith [ih]) ha0
    nlinarith

/-- A kernel `a ≤ 1/2` against a local quantity. -/
theorem pl6_loc_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i)
    (j k : ℕ) : ∑ i ∈ Ico j k, a ^ (k - i) * u i ≤ ∑ i ∈ Ico j k, (1 / 2 : ℝ) ^ (k - i) * u i :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha _) (hu i)

section Prof2

variable {j : ℕ} {k₀ mb : ℝ} {r : ℕ → ℝ}

theorem pl6_conv_G0 {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (k : ℕ) :
    ∑ i ∈ Ico j k, a ^ (k - i) * pl6G0 j k₀ mb r i ≤ pl6G0 j k₀ mb r k :=
  pl6_conv_le ha0 ha (fun n => pl6G0_nonneg hk hm n) (fun n hn => pl6G0_two hk hm hn) k

theorem pl6_conv_FO_succ {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hk : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hr : ∀ i, 0 ≤ r i) (k : ℕ) :
    ∑ i ∈ Ico j k, a ^ (k - i) * pl6FO j k₀ mb r (i + 1) ≤ pl6FO j k₀ mb r k :=
  pl6_conv_le_succ ha0 ha (fun n => pl6FO_nonneg hk hm hr n)
    (fun n hn => pl6FO_two hk hm hr hn) k

theorem pl6_conv_NF {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (k : ℕ) :
    ∑ i ∈ Ico j k, a ^ (k - i) * pl6NF j k₀ mb r i ≤ pl6NF j k₀ mb r k :=
  pl6_conv_le ha0 ha (fun n => pl6NF_nonneg hk hm n) (fun n hn => pl6NF_two hk hm hn) k

/-- The local first-order sources: `∑a^{k-i}m̄r_i ≤ FO(k)`. -/
theorem pl6_loc_FO {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hk : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hr : ∀ i, 0 ≤ r i) (k : ℕ) :
    ∑ i ∈ Ico j k, a ^ (k - i) * (mb * r i) ≤ pl6FO j k₀ mb r k := by
  refine (pl6_loc_le ha0 ha (fun i => mul_nonneg hm (hr i)) j k).trans ?_
  have e : ∑ i ∈ Ico j k, (1 / 2 : ℝ) ^ (k - i) * (mb * r i) = mb * pl6F j r k := by
    unfold pl6F; rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [e]; unfold pl6FO; have := pl6G0_nonneg (j := j) (r := r) hk hm k; linarith

/-- The local second-order sources: `∑a^{k-i}m̄r_i² ≤ NF(k)`. -/
theorem pl6_loc_NF {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (k : ℕ) :
    ∑ i ∈ Ico j k, a ^ (k - i) * (mb * r i ^ 2) ≤ pl6NF j k₀ mb r k := by
  refine (pl6_loc_le ha0 ha (fun i => mul_nonneg hm (sq_nonneg _)) j k).trans ?_
  have e : ∑ i ∈ Ico j k, (1 / 2 : ℝ) ^ (k - i) * (mb * r i ^ 2) = mb * pl6Q j r k := by
    unfold pl6Q; rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [e]; unfold pl6NF pl6G0; have := pl6P_nonneg (j := j) hk k
  have := sq_nonneg (r k); nlinarith

/-- `r_n·F(n) ≤ (Q(n) + r_n²)/2`. -/
theorem pl6_rF_le (hr : ∀ i, 0 ≤ r i) (n : ℕ) : r n * pl6F j r n ≤ (pl6Q j r n + r n ^ 2) / 2 := by
  unfold pl6F pl6Q
  rw [mul_sum]
  have h1 : ∀ i ∈ Ico j n, r n * ((1 / 2 : ℝ) ^ (n - i) * r i) ≤
      (1 / 2 : ℝ) ^ (n - i) * r i ^ 2 / 2 + (1 / 2 : ℝ) ^ (n - i) * (r n ^ 2 / 2) := by
    intro i _
    have hp : 0 ≤ (1 / 2 : ℝ) ^ (n - i) := by positivity
    have : r n * r i ≤ r i ^ 2 / 2 + r n ^ 2 / 2 := by nlinarith [sq_nonneg (r n - r i)]
    nlinarith
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← sum_mul, ← sum_div]
  have hg := geom_Ico_le_one (q := 1 / 2) (by norm_num) le_rfl j n
  have := sq_nonneg (r n)
  nlinarith

/-- **A first-order profile times `r_n` is of normal form**: `r_n·FO(n) ≤ 2NF(n)` (`r_n ≤ 1`). -/
theorem pl6_mul_FO (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (hr : ∀ i, 0 ≤ r i) {n : ℕ} (hr1 : r n ≤ 1) :
    r n * pl6FO j k₀ mb r n ≤ 2 * pl6NF j k₀ mb r n := by
  have hF := pl6_rF_le (j := j) hr n
  have hP := pl6P_nonneg (j := j) hk n
  have hQ := pl6Q_nonneg (j := j) (r := r) n
  have hr0 := hr n
  unfold pl6FO pl6NF pl6G0
  have h1 : r n * pl6P j k₀ n ≤ pl6P j k₀ n := by nlinarith
  have h2 : r n * (mb * pl6Q j r n) ≤ mb * pl6Q j r n := by nlinarith [mul_nonneg hm hQ]
  have h3 : r n * (mb * pl6F j r n) ≤ mb * ((pl6Q j r n + r n ^ 2) / 2) := by
    rw [show r n * (mb * pl6F j r n) = mb * (r n * pl6F j r n) by ring]
    exact mul_le_mul_of_nonneg_left hF hm
  have := mul_nonneg hm (sq_nonneg (r n))
  nlinarith

/-- **The convolution of `r_i·FO(i)`**: `∑_{j≤i<k}a^{k-i}r_iFO(i) ≤ 2NF(k)`. -/
theorem pl6_conv_rFO {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hk : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hr : ∀ i, 0 ≤ r i) {k : ℕ} (hr1 : ∀ i < k, r i ≤ 1) :
    ∑ i ∈ Ico j k, a ^ (k - i) * (r i * pl6FO j k₀ mb r i) ≤ 2 * pl6NF j k₀ mb r k := by
  have h1 : ∑ i ∈ Ico j k, a ^ (k - i) * (r i * pl6FO j k₀ mb r i) ≤
      ∑ i ∈ Ico j k, a ^ (k - i) * (2 * pl6NF j k₀ mb r i) :=
    sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
      (pl6_mul_FO hk hm hr (hr1 i (mem_Ico.1 hi).2)) (pow_nonneg ha0 _)
  refine h1.trans ?_
  have e : ∑ i ∈ Ico j k, a ^ (k - i) * (2 * pl6NF j k₀ mb r i) =
      2 * ∑ i ∈ Ico j k, a ^ (k - i) * pl6NF j k₀ mb r i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (pl6_conv_NF ha0 ha hk hm k) (by norm_num)

end Prof2

/-! ### The ratio facts of the history -/

/-- **The ratio facts along the history** (field scale `s`, `β_k = |β_{a,k}|`, `r_k = cǧ_k`,
`s_x = |a − b|_∞` with `2s_x ≤ L^{j+1}`). -/
structure PL6H (j Nh : ℕ) (L sx : ℝ) (s β r : ℕ → ℝ) : Prop where
  hL : 49 ≤ L
  hs0 : ∀ i, 0 < s i
  hs1 : ∀ i, s (i + 1) ≤ 9 / 8 * s i
  hs2 : ∀ i, s i ^ 2 ≤ 6 / 5 * s (i + 1) ^ 2
  hβ0 : ∀ i, 0 ≤ β i
  hβp : ∀ i ≤ Nh + 1, 0 < β i
  hβr : ∀ i ≤ Nh, β i ≤ 64 / 49 * β (i + 1)
  hr0 : ∀ i, 0 ≤ r i
  hr1 : ∀ i ≤ Nh, r i ≤ 1
  hsx : 0 ≤ sx
  hsxL : 2 * sx ≤ L ^ (j + 1)

theorem pl6ρ_ge : 1 ≤ pl6ρ := by unfold pl6ρ; norm_num

section Ratio

variable {j Nh : ℕ} {L sx : ℝ} {s β r : ℕ → ℝ} (H : PL6H j Nh L sx s β r)
include H

theorem PL6H.L0 : 0 < L := by have := H.hL; linarith

theorem PL6H.sq_up {i k : ℕ} (hik : i ≤ k) : s k ^ 2 ≤ (81 / 64 : ℝ) ^ (k - i) * s i ^ 2 := by
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have h1 := H.hs1 k
    have h0 := (H.hs0 (k + 1)).le
    have h2 : s (k + 1) ^ 2 ≤ 81 / 64 * s k ^ 2 := by nlinarith
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ (81 / 64 : ℝ)]
    have : 0 ≤ (81 / 64 : ℝ) ^ (k - i) := by positivity
    nlinarith

theorem PL6H.sq_dn {i k : ℕ} (hik : i ≤ k) : s i ^ 2 ≤ (6 / 5 : ℝ) ^ (k - i) * s k ^ 2 := by
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have h2 := H.hs2 k
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ (6 / 5 : ℝ)]
    have : 0 ≤ (6 / 5 : ℝ) ^ (k - i) := by positivity
    nlinarith

theorem PL6H.β_up {i k : ℕ} (hik : i ≤ k) (hk : k ≤ Nh + 1) :
    β i ≤ (64 / 49 : ℝ) ^ (k - i) * β k := by
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hk' ih =>
    have h2 := H.hβr k (by omega)
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ (64 / 49 : ℝ)]
    have : 0 ≤ (64 / 49 : ℝ) ^ (k - i) := by positivity
    have := ih (by omega)
    nlinarith

/-- `s_i²β_{i+1} ≤ ρ^{k-i}s_k²β_{k+1}` for `i ≤ k ≤ N_h`. -/
theorem PL6H.sβ_dn {i k : ℕ} (hik : i ≤ k) (hk : k ≤ Nh) :
    s i ^ 2 * β (i + 1) ≤ pl6ρ ^ (k - i) * (s k ^ 2 * β (k + 1)) := by
  have h1 := H.sq_dn hik
  have h2 := H.β_up (i := i + 1) (k := k + 1) (by omega) (by omega)
  rw [show k + 1 - (i + 1) = k - i by omega] at h2
  unfold pl6ρ; rw [mul_pow]
  have := H.hβ0 (i + 1)
  have : 0 ≤ (6 / 5 : ℝ) ^ (k - i) * s k ^ 2 := by positivity
  calc s i ^ 2 * β (i + 1) ≤ ((6 / 5 : ℝ) ^ (k - i) * s k ^ 2) *
        ((64 / 49 : ℝ) ^ (k - i) * β (k + 1)) := mul_le_mul h1 h2 (H.hβ0 _) (by positivity)
    _ = _ := by ring

/-- `2s_x/L^{i+1} ≤ 1` for `j ≤ i`. -/
theorem PL6H.t_le {i : ℕ} (hi : j ≤ i) : 2 * sx * (L ^ (i + 1))⁻¹ ≤ 1 := by
  have hL1 : 1 ≤ L := by have := H.hL; linarith
  have h1 : L ^ (j + 1) ≤ L ^ (i + 1) := pow_le_pow_right₀ hL1 (by omega)
  have hp : 0 < L ^ (i + 1) := pow_pos H.L0 _
  rw [← div_eq_mul_inv, div_le_one hp]; linarith [H.hsxL]

end Ratio

/-- `(a/b)·b ≤ a` for `a, b ≥ 0`. -/
theorem pl6_div_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a / b * b ≤ a := by
  rcases hb.eq_or_lt with h | h
  · rw [← h]; simp [ha]
  · rw [div_mul_cancel₀ _ h.ne']

/-- `(L^i)²/L^{2n+2} = (L²)⁻¹((L²)⁻¹)^{n-i}` for `i ≤ n`. -/
theorem pl6_Lpow {L : ℝ} (hL : 0 < L) {i n : ℕ} (hin : i ≤ n) :
    (L ^ i) ^ 2 / L ^ (2 * n + 2) = (L ^ 2)⁻¹ * ((L ^ 2)⁻¹) ^ (n - i) := by
  have e : L ^ (2 * n + 2) = (L ^ i) ^ 2 * L ^ 2 * (L ^ 2) ^ (n - i) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; rw [Nat.mul_sub]; omega
  have h1 : (L ^ i) ^ 2 ≠ 0 := by positivity
  have h2 : (L ^ 2) ^ (n - i) ≠ 0 := by positivity
  rw [e, inv_pow]; field_simp

/-- `(L^{i+1})²/L^{2n+2} = ((L²)⁻¹)^{n-i}` for `i ≤ n`. -/
theorem pl6_Lpow1 {L : ℝ} (hL : 0 < L) {i n : ℕ} (hin : i ≤ n) :
    (L ^ (i + 1)) ^ 2 / L ^ (2 * n + 2) = ((L ^ 2)⁻¹) ^ (n - i) := by
  have e : L ^ (2 * n + 2) = (L ^ (i + 1)) ^ 2 * (L ^ 2) ^ (n - i) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; rw [Nat.mul_sub]; omega
  have h1 : (L ^ (i + 1)) ^ 2 ≠ 0 := by positivity
  have h2 : (L ^ 2) ^ (n - i) ≠ 0 := by positivity
  rw [e, inv_pow]; field_simp

end

end Spin2
