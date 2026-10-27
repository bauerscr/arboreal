import PtCorr.Conv

/-!
# Summed recursions (proofs of `lem:1pt`, `lem:2pt`)

The recursions of `lem:Vobs-recursion` (`Obs.Vobs_recursion_one/two`) are stated for one step.
Here they are summed over the scales `k < N`, in an abstract form: for sequences of complex numbers
(indexed by the scale) satisfying the one-step (in)equalities.  Nothing here refers to the
observable flow itself, so the results apply to `laOf c (flowO … k).1` etc. as well as to the
accumulated `u`-parts (`qN`, `gaN` of WP1).

Indexing convention (as in `Obs.flowO`): step `k` uses the covariance `C_k := Flow.covAt … k`
(`= C_{k+1}` of the text) and produces the couplings of scale `k + 1`; the quadratic terms of
`lem:Vobs-recursion` use the couplings of scale `k + 1` (`λ'` in `Obs.Vobs_recursion_two`).

## Abstract lemmas
* telescoping of the increments: `norm_sub_le_sum_Ico_of_step`, and for geometric increments
  `‖f (k+1) - f k‖ ≤ c θ^k` the tail bound `‖f j - f n‖ ≤ c θ^j / (1 - θ)`
  (`norm_sub_le_geom_tail`: summing the `λ` increments *backwards* from `N`);
* Case (1): with a bound `‖λ_N - λ₀‖ ≤ B` at the last scale (the finite-`N` susceptibility
  argument), `‖λ_j - λ₀‖ ≤ B + c θ^j/(1 - θ)` for all `j ≤ N` (`norm_sub_le_of_tail`), and for
  `B = B' θ^N`: `‖λ_j - λ₀‖ ≤ (B' + c/(1-θ)) θ^j` (`norm_sub_le_pow_of_tail`);
* products: `norm_mul_sub_mul_le`, `norm_mul_sub_mul_le_pow`;
* `η` exactly: `η_0 = 0`, `η_{k+1} = η_k - 2 μ_k C_k` gives `η_j = -2 ∑_{k<j} μ_k C_k`
  (`eta_eq_neg_two_sum`), and `‖η_j + 2 P ∑_{k<j} C_k‖ ≤ 2 ∑_{k<j} δ_k |C_k|` if
  `‖μ_k - P‖ ≤ δ_k` (`norm_eta_add_le`);
* the square: `(∑_{k<n} c_k)^2 = ∑_{k<n} (2 (∑_{l<k} c_l) c_k + c_k^2)` (`sq_sum_eq_sum`);
* sums `∑ x_k` with `x_k ≈ μ_k c_k - ρ_k`: `‖∑ x - P ∑ c‖ ≤ ∑ ε + ∑ δ |c| + ∑ |ρ|`
  (`norm_sum_sub_mul_sum_le`; this is the Case-(1) `q`-sum and the `γ`-sum);
* the Case-(2) `q`-sum (telescoping of the proof of `lem:2pt`): with `η_k = -2 ∑_{l<k} μ_l c_l`
  and `x_k ≈ η_k c_k - μ_k c_k^2 - ρ_k`,
  `‖∑ x + P (∑ c)^2‖ ≤ ∑ ε + ∑ |ρ| + 2 (∑ δ_k |c_k|)(∑ |c_k|)` (`norm_qsum_two_le`).

## Along the covariances of the flow
With `C_k = Flow.covAt d L N msq k` satisfying `GoodCov`, `θ ∈ [0,1)`, `ℓ_k = ellj d L ℓ₀ k`,
`j_ab = coal L a b` (and `j_ab ≤ N`, `coal_le`), and the error terms in the form produced by
`Obs.Vobs_recursion_one/two` (with `‖K^obs_k‖_k ≤ e θ^k`):
* `qsum_one_bound`: `‖∑_{k<N} Δq_k - λ₀^2 ∑_{k<N} C_k(a,b)‖ ≤
   (4 C_S e + 2 D) ℓ_{j_ab}^2 θ^{j_ab} + 4 R ℓ_{j_ab}^2` if `‖λ_{x,k} - λ₀‖ ≤ Λ θ^k`,
  `‖r_{x,k}‖ ≤ R`, `r_{x,k} = 0` for `k ≤ j_ab`, `D = Λ(‖λ₀‖ + Λ) + ‖λ₀‖ Λ`;
* `eta_bound`: `‖η_N + 2 λ_{a,N} λ_{b,N} ∑_{k<N} C_k(a,b)‖ ≤ 4 D ℓ_{j_ab}^2 θ^{j_ab}` if
  `‖λ_{x,k} - λ_{x,N}‖ ≤ Λ θ^k`, `‖λ_{x,N}‖ ≤ M`, `D = Λ(M + Λ) + M Λ`;
* `qsum_two_bound`: `‖∑_{k<N} Δq_k + λ_{a,N} λ_{b,N} (∑_{k<N} C_k(a,b))^2‖ ≤
   (4 C_S e + 8 D) ℓ_{j_ab}^4 θ^{j_ab} + 4 R ℓ_{j_ab}^2`;
* `gsum_bound`: `‖∑_{k<N} Δγ_k - λ_{x,N} ∑_{k<N} C_k(x,x)‖ ≤ 2 (C_S e + Λ) ℓ₀^2`.
Combined with `Conv` (`ellj_coal_sq_mul_pow_le`, `ellj_coal_pow_four_mul_pow_le`) these are the
`O(|a-b|^{-(d-2)-κ})` resp. `O(|a-b|^{-2(d-2)-κ})` errors of the proof of `lem:2pt`, and
`∑_{k<N} C_k(a,b) = W_N(b - a)` is `sum_covAt_eq_WN` (`PtCorr.CoupBd`).

**Deviations.** The paper's `λ_{x,j} = λ_∞ + O(θ^j)` is replaced (Tier 1) by
`λ_{x,j} = λ_{x,N} + O(θ^j)` in Case (2), i.e. the finite-`N` couplings `λ_{x,N}` play the role
of `λ_∞`; the product `λ_∞^2` becomes `λ_{a,N} λ_{b,N}` (point-dependent couplings).
In Case (1) `λ_∞ = λ₀` is replaced by the finite-`N` input `‖λ_N - λ₀‖ ≤ B`.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD

/-! ### Abstract telescoping -/

section Abstract

variable {E : Type*} [SeminormedAddCommGroup E]

/-- `‖f j - f n‖ ≤ ∑_{j ≤ k < n} g_k` if `‖f (k+1) - f k‖ ≤ g_k` for `j ≤ k < n`. -/
theorem norm_sub_le_sum_Ico_of_step (f : ℕ → E) (g : ℕ → ℝ) {j n : ℕ} (hjn : j ≤ n)
    (h : ∀ k, j ≤ k → k < n → ‖f (k + 1) - f k‖ ≤ g k) :
    ‖f j - f n‖ ≤ ∑ k ∈ Ico j n, g k := by
  induction n, hjn using Nat.le_induction with
  | base => simp
  | succ n hjn ih =>
    rw [sum_Ico_succ_top hjn]
    have e : f j - f (n + 1) = (f j - f n) - (f (n + 1) - f n) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add (ih fun k hk1 hk2 => h k hk1 (by omega)) ?_)
    exact h n hjn (by omega)

/-- **Backward summation**: `‖f (k+1) - f k‖ ≤ c θ^k` for `j ≤ k < n` gives
`‖f j - f n‖ ≤ c θ^j / (1 - θ)`. -/
theorem norm_sub_le_geom_tail (f : ℕ → E) {c θ : ℝ} (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    {j n : ℕ} (hjn : j ≤ n) (h : ∀ k, j ≤ k → k < n → ‖f (k + 1) - f k‖ ≤ c * θ ^ k) :
    ‖f j - f n‖ ≤ c * θ ^ j / (1 - θ) := by
  refine (norm_sub_le_sum_Ico_of_step f _ hjn h).trans ?_
  rw [← mul_sum, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (sum_Ico_pow_le hθ0 hθ1 j n) hc

/-- **Case (1), `λ` tails**: from a bound at the last scale `‖f n - l‖ ≤ B` and geometric
increments, `‖f j - l‖ ≤ B + c θ^j / (1 - θ)` for all `j ≤ n`. -/
theorem norm_sub_le_of_tail (f : ℕ → E) (l : E) {B c θ : ℝ} (hc : 0 ≤ c) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) {n : ℕ} (hn : ‖f n - l‖ ≤ B)
    (h : ∀ k < n, ‖f (k + 1) - f k‖ ≤ c * θ ^ k) {j : ℕ} (hj : j ≤ n) :
    ‖f j - l‖ ≤ B + c * θ ^ j / (1 - θ) := by
  have h1 := norm_sub_le_geom_tail f hc hθ0 hθ1 hj fun k _ hk => h k hk
  calc ‖f j - l‖ = ‖(f n - l) + (f j - f n)‖ := by congr 1; abel
    _ ≤ ‖f n - l‖ + ‖f j - f n‖ := norm_add_le _ _
    _ ≤ B + c * θ ^ j / (1 - θ) := add_le_add hn h1

/-- Case (1) with `B = B' θ^n`: `‖f j - l‖ ≤ (B' + c/(1 - θ)) θ^j`. -/
theorem norm_sub_le_pow_of_tail (f : ℕ → E) (l : E) {B c θ : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {n : ℕ} (hn : ‖f n - l‖ ≤ B * θ ^ n)
    (h : ∀ k < n, ‖f (k + 1) - f k‖ ≤ c * θ ^ k) {j : ℕ} (hj : j ≤ n) :
    ‖f j - l‖ ≤ (B + c / (1 - θ)) * θ ^ j := by
  have h1 := norm_sub_le_of_tail f l hc hθ0 hθ1 hn h hj
  have h2 : θ ^ n ≤ θ ^ j := pow_le_pow_of_le_one hθ0 hθ1.le hj
  have h3 : B * θ ^ n ≤ B * θ ^ j := mul_le_mul_of_nonneg_left h2 hB
  calc ‖f j - l‖ ≤ B * θ ^ n + c * θ ^ j / (1 - θ) := h1
    _ ≤ B * θ ^ j + c * θ ^ j / (1 - θ) := by linarith
    _ = (B + c / (1 - θ)) * θ ^ j := by ring

/-- `norm_sub_le_pow_of_tail` in the form of `Obs.Vobs_recursion_one`
(`‖λ_{k+1} - λ_k‖ ≤ C_S (e θ^k)`) and a finite-`N` bound `‖λ_N - λ₀‖ ≤ B θ^N`:
`‖λ_j - λ₀‖ ≤ (B + C_S e/(1-θ)) θ^j` for `j ≤ N`. -/
theorem lam_one_tail (f : ℕ → E) (l : E) {B Cs e θ : ℝ} (hB : 0 ≤ B) (hCs : 0 ≤ Cs)
    (he : 0 ≤ e) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {n : ℕ} (hn : ‖f n - l‖ ≤ B * θ ^ n)
    (h : ∀ k < n, ‖f (k + 1) - f k‖ ≤ Cs * (e * θ ^ k)) {j : ℕ} (hj : j ≤ n) :
    ‖f j - l‖ ≤ (B + Cs * e / (1 - θ)) * θ ^ j :=
  norm_sub_le_pow_of_tail f l hB (mul_nonneg hCs he) hθ0 hθ1 hn
    (fun k hk => (h k hk).trans (le_of_eq (by ring))) hj

/-- Case (2), `λ` relative to the last scale: `‖λ_{k+1} - λ_k‖ ≤ C_S (e θ^k)` for `k < N` gives
`‖λ_j - λ_N‖ ≤ (C_S e/(1-θ)) θ^j` for `j ≤ N`. -/
theorem lam_tail_N (f : ℕ → E) {Cs e θ : ℝ} (hCs : 0 ≤ Cs) (he : 0 ≤ e) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) {n : ℕ} (h : ∀ k < n, ‖f (k + 1) - f k‖ ≤ Cs * (e * θ ^ k)) {j : ℕ}
    (hj : j ≤ n) : ‖f j - f n‖ ≤ Cs * e / (1 - θ) * θ ^ j := by
  have := norm_sub_le_geom_tail f (mul_nonneg hCs he) hθ0 hθ1 hj
    (fun k _ hk => (h k hk).trans (le_of_eq (by ring)))
  exact this.trans (le_of_eq (by ring))

end Abstract

/-! ### Products -/

/-- `‖x y - u v‖ ≤ ‖x - u‖ (‖v‖ + ‖y - v‖) + ‖u‖ ‖y - v‖`. -/
theorem norm_mul_sub_mul_le (x y u v : ℂ) :
    ‖x * y - u * v‖ ≤ ‖x - u‖ * (‖v‖ + ‖y - v‖) + ‖u‖ * ‖y - v‖ := by
  have e : x * y - u * v = (x - u) * y + u * (y - v) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hy : ‖y‖ ≤ ‖v‖ + ‖y - v‖ := by
    calc ‖y‖ = ‖v + (y - v)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have := mul_le_mul_of_nonneg_left hy (norm_nonneg (x - u))
  linarith

/-- If `‖x - u‖ ≤ α t`, `‖y - v‖ ≤ β t` with `0 ≤ t ≤ 1`, then
`‖x y - u v‖ ≤ (α (‖v‖ + β) + ‖u‖ β) t`. -/
theorem norm_mul_sub_mul_le_pow {x y u v : ℂ} {α β t : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : ‖x - u‖ ≤ α * t) (hy : ‖y - v‖ ≤ β * t) :
    ‖x * y - u * v‖ ≤ (α * (‖v‖ + β) + ‖u‖ * β) * t := by
  refine (norm_mul_sub_mul_le x y u v).trans ?_
  have hy' : ‖y - v‖ ≤ β := hy.trans (by nlinarith)
  have h1 : ‖x - u‖ * (‖v‖ + ‖y - v‖) ≤ α * t * (‖v‖ + β) :=
    mul_le_mul hx (by linarith) (by positivity) (by positivity)
  have h2 : ‖u‖ * ‖y - v‖ ≤ ‖u‖ * (β * t) := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
  nlinarith

/-! ### `η` exactly, and the square of a sum -/

/-- **`η` exactly**: `η_0 = 0` and `η_{k+1} = η_k - 2 μ_k c_k` (`k < n`) give
`η_j = -2 ∑_{k<j} μ_k c_k` for `j ≤ n`. -/
theorem eta_eq_neg_two_sum (η μ c : ℕ → ℂ) {n : ℕ} (h0 : η 0 = 0)
    (h : ∀ k < n, η (k + 1) = η k - 2 * μ k * c k) :
    ∀ j ≤ n, η j = -2 * ∑ k ∈ range j, μ k * c k := by
  intro j
  induction j with
  | zero => intro _; simp [h0]
  | succ j ih =>
    intro hj
    rw [h j (by omega), ih (by omega), sum_range_succ]
    ring

/-- `(∑_{k<n} c_k)^2 = ∑_{k<n} (2 (∑_{l<k} c_l) c_k + c_k^2)`. -/
theorem sq_sum_eq_sum {R : Type*} [CommRing R] (c : ℕ → R) (n : ℕ) :
    (∑ k ∈ range n, c k) ^ 2 =
      ∑ k ∈ range n, (2 * (∑ l ∈ range k, c l) * c k + c k ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ← ih]; ring

/-- `∑_{k<n} ∑_{l ≤ k} a_l b_k ≤ (∑_{k<n} a_k)(∑_{k<n} b_k)` for nonnegative `a, b`. -/
theorem sum_sum_le_mul (a b : ℕ → ℝ) (n : ℕ) (ha : ∀ k < n, 0 ≤ a k) (hb : ∀ k < n, 0 ≤ b k) :
    ∑ k ∈ range n, (∑ l ∈ range (k + 1), a l) * b k ≤
      (∑ k ∈ range n, a k) * ∑ k ∈ range n, b k := by
  rw [mul_sum]
  refine sum_le_sum fun k hk => ?_
  rw [mem_range] at hk
  refine mul_le_mul_of_nonneg_right ?_ (hb k hk)
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
    fun l hl _ => ha l (mem_range.1 hl)

/-- `‖η_j + 2 P ∑_{k<j} c_k‖ ≤ 2 ∑_{k<j} δ_k ‖c_k‖` if `η_j = -2 ∑_{k<j} μ_k c_k` and
`‖μ_k - P‖ ≤ δ_k`. -/
theorem norm_eta_add_le (μ c : ℕ → ℂ) (δ : ℕ → ℝ) (P : ℂ) {j : ℕ}
    (hμ : ∀ k < j, ‖μ k - P‖ ≤ δ k) :
    ‖-2 * ∑ k ∈ range j, μ k * c k + 2 * P * ∑ k ∈ range j, c k‖ ≤
      2 * ∑ k ∈ range j, δ k * ‖c k‖ := by
  have e : -2 * ∑ k ∈ range j, μ k * c k + 2 * P * ∑ k ∈ range j, c k =
      -2 * ∑ k ∈ range j, (μ k - P) * c k := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => by ring
  rw [e, norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_))
    (by norm_num)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hμ k (mem_range.1 hk)) (norm_nonneg _)

/-! ### Sums of approximately quadratic terms -/

/-- **Case-(1) `q`-sum, `γ`-sum**: if `‖x_k - (μ_k c_k - ρ_k)‖ ≤ ε_k` and `‖μ_k - P‖ ≤ δ_k`
for `k < n`, then `‖∑ x - P ∑ c‖ ≤ ∑ ε + ∑ δ ‖c‖ + ∑ ‖ρ‖`. -/
theorem norm_sum_sub_mul_sum_le (x μ c ρ : ℕ → ℂ) (ε δ : ℕ → ℝ) (P : ℂ) {n : ℕ}
    (hx : ∀ k < n, ‖x k - (μ k * c k - ρ k)‖ ≤ ε k) (hμ : ∀ k < n, ‖μ k - P‖ ≤ δ k) :
    ‖∑ k ∈ range n, x k - P * ∑ k ∈ range n, c k‖ ≤
      ∑ k ∈ range n, ε k + ∑ k ∈ range n, δ k * ‖c k‖ + ∑ k ∈ range n, ‖ρ k‖ := by
  have e : ∑ k ∈ range n, x k - P * ∑ k ∈ range n, c k =
      ∑ k ∈ range n, ((x k - (μ k * c k - ρ k)) + (μ k - P) * c k - ρ k) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => by ring
  rw [e, ← sum_add_distrib, ← sum_add_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
  have hk' := mem_range.1 hk
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (hx k hk') ?_)) le_rfl)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hμ k hk') (norm_nonneg _)

/-- **Case-(2) `q`-sum** (the telescoping of the proof of `lem:2pt`): if
`η_k = -2 ∑_{l<k} μ_l c_l`, `‖x_k - (η_k c_k - μ_k c_k^2 - ρ_k)‖ ≤ ε_k` and `‖μ_k - P‖ ≤ δ_k`
for `k < n`, then
`‖∑ x + P (∑ c)^2‖ ≤ ∑ ε + ∑ ‖ρ‖ + 2 (∑ δ_k ‖c_k‖)(∑ ‖c_k‖)`. -/
theorem norm_qsum_two_le (x η μ c ρ : ℕ → ℂ) (ε δ : ℕ → ℝ) (P : ℂ) {n : ℕ}
    (hη : ∀ k < n, η k = -2 * ∑ l ∈ range k, μ l * c l)
    (hx : ∀ k < n, ‖x k - (η k * c k - μ k * c k ^ 2 - ρ k)‖ ≤ ε k)
    (hμ : ∀ k < n, ‖μ k - P‖ ≤ δ k) :
    ‖∑ k ∈ range n, x k + P * (∑ k ∈ range n, c k) ^ 2‖ ≤
      ∑ k ∈ range n, ε k + ∑ k ∈ range n, ‖ρ k‖ +
        2 * ((∑ k ∈ range n, δ k * ‖c k‖) * ∑ k ∈ range n, ‖c k‖) := by
  have hδ0 : ∀ k < n, 0 ≤ δ k := fun k hk => (norm_nonneg _).trans (hμ k hk)
  -- the main term
  set T : ℕ → ℂ := fun k => -(2 * (∑ l ∈ range k, (μ l - P) * c l) * c k + (μ k - P) * c k ^ 2)
    with hT
  have e : ∑ k ∈ range n, x k + P * (∑ k ∈ range n, c k) ^ 2 =
      ∑ k ∈ range n, ((x k - (η k * c k - μ k * c k ^ 2 - ρ k)) - ρ k + T k) := by
    rw [sq_sum_eq_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [hη k (mem_range.1 hk), hT]
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
    ring
  rw [e, sum_add_distrib, sum_sub_distrib]
  have h1 : ‖∑ k ∈ range n, (x k - (η k * c k - μ k * c k ^ 2 - ρ k))‖ ≤ ∑ k ∈ range n, ε k :=
    (norm_sum_le _ _).trans (sum_le_sum fun k hk => hx k (mem_range.1 hk))
  have h2 : ‖∑ k ∈ range n, ρ k‖ ≤ ∑ k ∈ range n, ‖ρ k‖ := norm_sum_le _ _
  have hTk : ∀ k < n, ‖T k‖ ≤ 2 * ((∑ l ∈ range (k + 1), δ l * ‖c l‖) * ‖c k‖) := by
    intro k hk
    rw [hT, norm_neg]
    refine (norm_add_le _ _).trans ?_
    have hs : ‖∑ l ∈ range k, (μ l - P) * c l‖ ≤ ∑ l ∈ range k, δ l * ‖c l‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun l hl => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hμ l (by have := mem_range.1 hl; omega))
          (norm_nonneg _))
    have ha : ‖2 * (∑ l ∈ range k, (μ l - P) * c l) * c k‖ ≤
        2 * ((∑ l ∈ range k, δ l * ‖c l‖) * ‖c k‖) := by
      rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
        (by norm_num)
    have hb : ‖(μ k - P) * c k ^ 2‖ ≤ δ k * ‖c k‖ * ‖c k‖ := by
      rw [norm_mul, norm_pow, sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hμ k hk) (norm_nonneg _))
        (norm_nonneg _)
    rw [sum_range_succ]
    have : 0 ≤ δ k * ‖c k‖ * ‖c k‖ := by have := hδ0 k hk; positivity
    nlinarith
  have h3 : ‖∑ k ∈ range n, T k‖ ≤ 2 * ((∑ k ∈ range n, δ k * ‖c k‖) * ∑ k ∈ range n, ‖c k‖) := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun k hk => hTk k (mem_range.1 hk)).trans ?_)
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact sum_sum_le_mul (fun l => δ l * ‖c l‖) (fun k => ‖c k‖) n
      (fun k hk => mul_nonneg (hδ0 k hk) (norm_nonneg _)) (fun k _ => norm_nonneg _)
  calc _ ≤ ‖∑ k ∈ range n, (x k - (η k * c k - μ k * c k ^ 2 - ρ k)) - ∑ k ∈ range n, ρ k‖ +
        ‖∑ k ∈ range n, T k‖ := norm_add_le _ _
    _ ≤ (‖∑ k ∈ range n, (x k - (η k * c k - μ k * c k ^ 2 - ρ k))‖ + ‖∑ k ∈ range n, ρ k‖) +
        ‖∑ k ∈ range n, T k‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by linarith

/-! ### Along the covariances of the flow -/

section Flow

variable {d L N : ℕ} [NeZero L]

/-- `j_ab ≤ N` on `Λ_N`. -/
theorem coal_le (hL : 2 ≤ L) (a b : Lam d L N) : coal L a b ≤ N := by
  unfold coal
  calc Nat.log L (2 * supNorm (a - b)) ≤ Nat.log L (L ^ N) :=
        Nat.log_mono_right (two_mul_supNorm_le (a - b))
    _ = N := Nat.log_pow (by omega) N

theorem ellab_one_inv (ℓ ℓ' : ℝ) : (ellab .one ℓ ℓ')⁻¹ = ℓ ^ 2 := by
  simp [ellab]

theorem ellab_two_inv (ℓ ℓ' : ℝ) : (ellab .two ℓ ℓ')⁻¹ = ℓ ^ 2 * ℓ' ^ 2 := by
  simp [ellab]; ring

theorem ellj_zero' (ℓ₀ : ℝ) : ellj d (L : ℝ) ℓ₀ 0 = ℓ₀ := by simp [ellj]

/-- The summed `ab` error terms of `Obs.Vobs_recursion_one` (with `‖K^obs_k‖_k ≤ e θ^k`):
`∑_{k<N} 2 C_S ℓ_{ab,k}^{-1} e θ^k 1_{k ≥ m} ≤ 4 C_S e ℓ_m^2 θ^m`. -/
theorem sum_err_one_le (hd : 3 ≤ d) (hL : 2 ≤ L) (ℓ₀ : ℝ) {θ Cs e : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hCs : 0 ≤ Cs) (he : 0 ≤ e) (m n : ℕ) :
    ∑ k ∈ range n, 2 * Cs * (ellab .one (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k m)))⁻¹ *
        (e * θ ^ k) * (if m ≤ k then 1 else 0) ≤
      4 * Cs * e * (ellj d L ℓ₀ m ^ 2 * θ ^ m) := by
  have e1 : ∀ k, 2 * Cs * (ellab .one (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k m)))⁻¹ *
      (e * θ ^ k) * (if m ≤ k then 1 else 0) =
      2 * Cs * e * (if m ≤ k then ellj d L ℓ₀ k ^ 2 * θ ^ k else 0) := by
    intro k; rw [ellab_one_inv]; split_ifs <;> ring
  simp only [e1, ← mul_sum]
  have := sum_ite_ellj_sq_pow_le hd hL ℓ₀ hθ0 hθ1 m n
  have h2 : 0 ≤ 2 * Cs * e := by positivity
  nlinarith

/-- The summed `ab` error terms of `Obs.Vobs_recursion_two`:
`∑_{k<N} 2 C_S ℓ_{ab,k}^{-1} e θ^k 1_{k ≥ m} ≤ 4 C_S e ℓ_m^4 θ^m`. -/
theorem sum_err_two_le (hd : 3 ≤ d) (hL : 2 ≤ L) (ℓ₀ : ℝ) {θ Cs e : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hCs : 0 ≤ Cs) (he : 0 ≤ e) (m n : ℕ) :
    ∑ k ∈ range n, 2 * Cs * (ellab .two (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k m)))⁻¹ *
        (e * θ ^ k) * (if m ≤ k then 1 else 0) ≤
      4 * Cs * e * (ellj d L ℓ₀ m ^ 4 * θ ^ m) := by
  have e1 : ∀ k, 2 * Cs * (ellab .two (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k m)))⁻¹ *
      (e * θ ^ k) * (if m ≤ k then 1 else 0) =
      2 * Cs * e * ellj d L ℓ₀ m ^ 2 * (if m ≤ k then ellj d L ℓ₀ k ^ 2 * θ ^ k else 0) := by
    intro k; rw [ellab_two_inv]
    split_ifs with h
    · rw [jwedge_eq_of_ge h]; ring
    · ring
  simp only [e1, ← mul_sum]
  have := sum_ite_ellj_sq_pow_le hd hL ℓ₀ hθ0 hθ1 m n
  have h2 : 0 ≤ 2 * Cs * e * ellj d L ℓ₀ m ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left this h2
  calc _ ≤ 2 * Cs * e * ellj d L ℓ₀ m ^ 2 * (2 * (ellj d L ℓ₀ m ^ 2 * θ ^ m)) := h3
    _ = _ := by ring

/-- The `r`-terms: if `‖r_k‖ ≤ R` and `r_k = 0` for `k ≤ m` (`k ≤ N`), then
`∑_{k<N} ‖r_{k+1} C_k(x,y)‖ ≤ 2 R ℓ_m^2`. -/
theorem sum_norm_r_covAt_le (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (x y : Lam d L N) (m : ℕ)
    (r : ℕ → ℂ) {R : ℝ} (hr : ∀ k ≤ N, ‖r k‖ ≤ R ∧ (k ≤ m → r k = 0)) :
    ∑ k ∈ range N, ‖r (k + 1) * (Flow.covAt d L N msq k x y : ℂ)‖ ≤
      2 * R * ellj d L ℓ₀ m ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (hr 0 (Nat.zero_le _)).1
  have h1 : ∀ k ∈ range N, ‖r (k + 1) * (Flow.covAt d L N msq k x y : ℂ)‖ ≤
      R * (if m ≤ k + 1 then (1 : ℝ) ^ (k + 1) * |Flow.covAt d L N msq k x y| else 0) := by
    intro k hk
    have hk' := mem_range.1 hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with h
    · rw [one_pow, one_mul]
      exact mul_le_mul_of_nonneg_right (hr (k + 1) (by omega)).1 (abs_nonneg _)
    · rw [(hr (k + 1) (by omega)).2 (by omega), norm_zero, zero_mul, mul_zero]
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  have h2 := sum_ite_pow_abs_covAt_le hd hL hℓ₀ hC x y le_rfl zero_le_one le_rfl m
  rw [one_pow, one_mul] at h2
  nlinarith

/-- `∑_{k<N} D θ^{k+1} ‖C_k(a,b)‖ ≤ 2 D θ^{j_ab} ℓ_{j_ab}^2`. -/
theorem sum_delta_covAt_le (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N) {θ D : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 ≤ D) :
    ∑ k ∈ range N, D * θ ^ (k + 1) * ‖(Flow.covAt d L N msq k a b : ℂ)‖ ≤
      2 * D * (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b) := by
  have h := sum_pow_abs_covAt_le hd hL hℓ₀ hC a b le_rfl hθ0 hθ1
  rw [min_eq_right (coal_le hL a b)] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_assoc, ← mul_sum]
  have := mul_le_mul_of_nonneg_left h hD
  linarith

/-- `∑_{k<N} ‖C_k(a,b)‖ ≤ 2 ℓ_{j_ab}^2`. -/
theorem sum_norm_covAt_le (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N) :
    ∑ k ∈ range N, ‖(Flow.covAt d L N msq k a b : ℂ)‖ ≤ 2 * ellj d L ℓ₀ (coal L a b) ^ 2 := by
  have h := sum_pow_abs_covAt_le hd hL hℓ₀ hC a b le_rfl zero_le_one le_rfl
  rw [min_eq_right (coal_le hL a b)] at h
  simpa [Complex.norm_real] using h

/-- **Summed `q`-recursion, Case (1)** (proof of `lem:2pt`, Case (1)): with the error terms of
`Obs.Vobs_recursion_one` (for `‖K^obs_k‖_k ≤ e θ^k`), `‖λ_{x,k} - λ₀‖ ≤ Λ θ^k` (e.g. from
`norm_sub_le_pow_of_tail`), `‖r_{x,k}‖ ≤ R` and `r_{x,k} = 0` for `k ≤ j_ab` (`Obs.Vobs_bd`):
`‖∑_{k<N} Δq_k - λ₀^2 ∑_{k<N} C_k(a,b)‖ ≤ (4 C_S e + 2 D) ℓ_{j_ab}^2 θ^{j_ab} + 4 R ℓ_{j_ab}^2`,
`D = Λ (‖λ₀‖ + Λ) + ‖λ₀‖ Λ`. -/
theorem qsum_one_bound (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N)
    {θ e Cs Λ R : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (he : 0 ≤ e) (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ)
    (l₀ : ℂ) (la lb ra rb dq : ℕ → ℂ)
    (hla : ∀ k ≤ N, ‖la k - l₀‖ ≤ Λ * θ ^ k) (hlb : ∀ k ≤ N, ‖lb k - l₀‖ ≤ Λ * θ ^ k)
    (hra : ∀ k ≤ N, ‖ra k‖ ≤ R ∧ (k ≤ coal L a b → ra k = 0))
    (hrb : ∀ k ≤ N, ‖rb k‖ ≤ R ∧ (k ≤ coal L a b → rb k = 0))
    (hq : ∀ k < N, ‖dq k - (la (k + 1) * lb (k + 1) * (Flow.covAt d L N msq k a b : ℂ) -
        (ra (k + 1) * (Flow.covAt d L N msq k a a : ℂ) +
          rb (k + 1) * (Flow.covAt d L N msq k b b : ℂ)))‖ ≤
      2 * Cs * (ellab .one (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k (coal L a b))))⁻¹ *
        (e * θ ^ k) * (if coal L a b ≤ k then 1 else 0)) :
    ‖∑ k ∈ range N, dq k - l₀ ^ 2 * ∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)‖ ≤
      (4 * Cs * e + 2 * (Λ * (‖l₀‖ + Λ) + ‖l₀‖ * Λ)) *
          (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b) +
        4 * R * ellj d L ℓ₀ (coal L a b) ^ 2 := by
  set D := Λ * (‖l₀‖ + Λ) + ‖l₀‖ * Λ with hDdef
  have hD : 0 ≤ D := by positivity
  have hμ : ∀ k < N, ‖la (k + 1) * lb (k + 1) - l₀ ^ 2‖ ≤ D * θ ^ (k + 1) := by
    intro k hk
    rw [sq]
    exact norm_mul_sub_mul_le_pow hΛ hΛ (by positivity) (pow_le_one₀ hθ0 hθ1)
      (hla (k + 1) (by omega)) (hlb (k + 1) (by omega))
  have h := norm_sum_sub_mul_sum_le dq (fun k => la (k + 1) * lb (k + 1))
    (fun k => (Flow.covAt d L N msq k a b : ℂ))
    (fun k => ra (k + 1) * (Flow.covAt d L N msq k a a : ℂ) +
      rb (k + 1) * (Flow.covAt d L N msq k b b : ℂ)) _ (fun k => D * θ ^ (k + 1)) (l₀ ^ 2) hq hμ
  refine h.trans ?_
  have h1 := sum_err_one_le hd hL ℓ₀ hθ0 hθ1 hCs he (coal L a b) N
  have h2 := sum_delta_covAt_le hd hL hℓ₀ hC a b hθ0 hθ1 hD
  have h3 : ∑ k ∈ range N, ‖ra (k + 1) * (Flow.covAt d L N msq k a a : ℂ) +
      rb (k + 1) * (Flow.covAt d L N msq k b b : ℂ)‖ ≤ 4 * R * ellj d L ℓ₀ (coal L a b) ^ 2 := by
    refine (sum_le_sum fun k _ => norm_add_le _ _).trans ?_
    rw [sum_add_distrib]
    have := sum_norm_r_covAt_le hd hL hℓ₀ hC a a _ ra hra
    have := sum_norm_r_covAt_le hd hL hℓ₀ hC b b _ rb hrb
    linarith
  linarith

/-- **`η_N`** (proof of `lem:2pt`, Case (2)): from `η_0 = 0` and the exact recursion
`η_{k+1} = η_k - 2 λ_{a,k+1} λ_{b,k+1} C_k(a,b)` of `Obs.Vobs_recursion_two`, with
`‖λ_{x,k} - λ_{x,N}‖ ≤ Λ θ^k`, `‖λ_{x,N}‖ ≤ M`:
`‖η_N + 2 λ_{a,N} λ_{b,N} ∑_{k<N} C_k(a,b)‖ ≤ 4 D ℓ_{j_ab}^2 θ^{j_ab}`, `D = Λ(M + Λ) + M Λ`.
The exact formula is `eta_eq_neg_two_sum`. -/
theorem eta_bound (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N)
    {θ Λ M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M)
    (la lb eta : ℕ → ℂ)
    (hla : ∀ k ≤ N, ‖la k - la N‖ ≤ Λ * θ ^ k) (hlb : ∀ k ≤ N, ‖lb k - lb N‖ ≤ Λ * θ ^ k)
    (hlaN : ‖la N‖ ≤ M) (hlbN : ‖lb N‖ ≤ M) (h0 : eta 0 = 0)
    (heta : ∀ k < N, eta (k + 1) =
      eta k - 2 * la (k + 1) * lb (k + 1) * (Flow.covAt d L N msq k a b : ℂ)) :
    ‖eta N + 2 * (la N * lb N) * ∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)‖ ≤
      4 * (Λ * (M + Λ) + M * Λ) * (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b) := by
  set D := Λ * (M + Λ) + M * Λ with hDdef
  have hD : 0 ≤ D := by positivity
  have hμ : ∀ k < N, ‖la (k + 1) * lb (k + 1) - la N * lb N‖ ≤ D * θ ^ (k + 1) := by
    intro k hk
    refine (norm_mul_sub_mul_le_pow hΛ hΛ (by positivity) (pow_le_one₀ hθ0 hθ1)
      (hla (k + 1) (by omega)) (hlb (k + 1) (by omega))).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hlbN hΛ
    have := mul_le_mul_of_nonneg_right hlaN hΛ
    nlinarith
  have hη := eta_eq_neg_two_sum eta (fun k => la (k + 1) * lb (k + 1))
    (fun k => (Flow.covAt d L N msq k a b : ℂ)) h0
    (fun k hk => by rw [heta k hk]; ring) N le_rfl
  rw [hη]
  refine (norm_eta_add_le _ _ (fun k => D * θ ^ (k + 1)) _ hμ).trans ?_
  have h2 := sum_delta_covAt_le hd hL hℓ₀ hC a b hθ0 hθ1 hD
  linarith

/-- **Summed `q`-recursion, Case (2)** (proof of `lem:2pt`, Case (2): the telescoping
`∑_k [η_{k-1} C_k - λ^2 C_k^2] = -λ^2 (∑_k C_k)^2 + …`): with the error terms of
`Obs.Vobs_recursion_two` (for `‖K^obs_k‖_k ≤ e θ^k`), the exact `η` recursion,
`‖λ_{x,k} - λ_{x,N}‖ ≤ Λ θ^k`, `‖λ_{x,N}‖ ≤ M`, `‖r_{x,k}‖ ≤ R` and `r_{x,k} = 0` for `k ≤ j_ab`:
`‖∑_{k<N} Δq_k + λ_{a,N} λ_{b,N} (∑_{k<N} C_k(a,b))^2‖ ≤
  (4 C_S e + 8 D) ℓ_{j_ab}^4 θ^{j_ab} + 4 R ℓ_{j_ab}^2`, `D = Λ(M + Λ) + M Λ`. -/
theorem qsum_two_bound (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N)
    {θ e Cs Λ M R : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (he : 0 ≤ e) (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ)
    (hM : 0 ≤ M) (la lb ra rb eta dq : ℕ → ℂ)
    (hla : ∀ k ≤ N, ‖la k - la N‖ ≤ Λ * θ ^ k) (hlb : ∀ k ≤ N, ‖lb k - lb N‖ ≤ Λ * θ ^ k)
    (hlaN : ‖la N‖ ≤ M) (hlbN : ‖lb N‖ ≤ M)
    (hra : ∀ k ≤ N, ‖ra k‖ ≤ R ∧ (k ≤ coal L a b → ra k = 0))
    (hrb : ∀ k ≤ N, ‖rb k‖ ≤ R ∧ (k ≤ coal L a b → rb k = 0))
    (h0 : eta 0 = 0)
    (heta : ∀ k < N, eta (k + 1) =
      eta k - 2 * la (k + 1) * lb (k + 1) * (Flow.covAt d L N msq k a b : ℂ))
    (hq : ∀ k < N, ‖dq k - (eta k * (Flow.covAt d L N msq k a b : ℂ) -
        la (k + 1) * lb (k + 1) * (Flow.covAt d L N msq k a b : ℂ) ^ 2 -
        (ra (k + 1) * (Flow.covAt d L N msq k a a : ℂ) +
          rb (k + 1) * (Flow.covAt d L N msq k b b : ℂ)))‖ ≤
      2 * Cs * (ellab .two (ellj d L ℓ₀ k) (ellj d L ℓ₀ (jwedge k (coal L a b))))⁻¹ *
        (e * θ ^ k) * (if coal L a b ≤ k then 1 else 0)) :
    ‖∑ k ∈ range N, dq k +
        la N * lb N * (∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)) ^ 2‖ ≤
      (4 * Cs * e + 8 * (Λ * (M + Λ) + M * Λ)) *
          (ellj d L ℓ₀ (coal L a b) ^ 4 * θ ^ coal L a b) +
        4 * R * ellj d L ℓ₀ (coal L a b) ^ 2 := by
  set D := Λ * (M + Λ) + M * Λ with hDdef
  have hD : 0 ≤ D := by positivity
  have hμ : ∀ k < N, ‖la (k + 1) * lb (k + 1) - la N * lb N‖ ≤ D * θ ^ (k + 1) := by
    intro k hk
    refine (norm_mul_sub_mul_le_pow hΛ hΛ (by positivity) (pow_le_one₀ hθ0 hθ1)
      (hla (k + 1) (by omega)) (hlb (k + 1) (by omega))).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hlbN hΛ
    have := mul_le_mul_of_nonneg_right hlaN hΛ
    nlinarith
  have hη := eta_eq_neg_two_sum eta (fun k => la (k + 1) * lb (k + 1))
    (fun k => (Flow.covAt d L N msq k a b : ℂ)) h0 (fun k hk => by rw [heta k hk]; ring)
  have h := norm_qsum_two_le dq eta (fun k => la (k + 1) * lb (k + 1))
    (fun k => (Flow.covAt d L N msq k a b : ℂ))
    (fun k => ra (k + 1) * (Flow.covAt d L N msq k a a : ℂ) +
      rb (k + 1) * (Flow.covAt d L N msq k b b : ℂ)) _ (fun k => D * θ ^ (k + 1))
    (la N * lb N) (fun k hk => hη k hk.le) hq hμ
  refine h.trans ?_
  have h1 := sum_err_two_le hd hL ℓ₀ hθ0 hθ1 hCs he (coal L a b) N
  have h2 := sum_delta_covAt_le hd hL hℓ₀ hC a b hθ0 hθ1 hD
  have h2' := sum_norm_covAt_le hd hL hℓ₀ hC a b
  have h3 : ∑ k ∈ range N, ‖ra (k + 1) * (Flow.covAt d L N msq k a a : ℂ) +
      rb (k + 1) * (Flow.covAt d L N msq k b b : ℂ)‖ ≤ 4 * R * ellj d L ℓ₀ (coal L a b) ^ 2 := by
    refine (sum_le_sum fun k _ => norm_add_le _ _).trans ?_
    rw [sum_add_distrib]
    have := sum_norm_r_covAt_le hd hL hℓ₀ hC a a _ ra hra
    have := sum_norm_r_covAt_le hd hL hℓ₀ hC b b _ rb hrb
    linarith
  set ℓc := ellj d L ℓ₀ (coal L a b)
  set tc := θ ^ coal L a b
  have hS0 : 0 ≤ ∑ k ∈ range N, D * θ ^ (k + 1) * ‖(Flow.covAt d L N msq k a b : ℂ)‖ :=
    sum_nonneg fun k _ => by positivity
  have hP : (∑ k ∈ range N, D * θ ^ (k + 1) * ‖(Flow.covAt d L N msq k a b : ℂ)‖) *
      ∑ k ∈ range N, ‖(Flow.covAt d L N msq k a b : ℂ)‖ ≤ (2 * D * (ℓc ^ 2 * tc)) * (2 * ℓc ^ 2) :=
    mul_le_mul h2 h2' (sum_nonneg fun k _ => norm_nonneg _) (by positivity)
  have e4 : ℓc ^ 4 * tc = ℓc ^ 2 * (ℓc ^ 2 * tc) := by ring
  nlinarith

/-- **Summed `γ`-recursion, Case (2)** (proof of `lem:1pt`): with the error terms of
`Obs.Vobs_recursion_two` (`‖Δγ_k - λ_{x,k+1} C_k(x,x)‖ ≤ C_S ℓ_k^2 e θ^k`) and
`‖λ_{x,k} - λ_{x,N}‖ ≤ Λ θ^k`:
`‖∑_{k<N} Δγ_k - λ_{x,N} ∑_{k<N} C_k(x,x)‖ ≤ 2 (C_S e + Λ) ℓ₀^2`. -/
theorem gsum_bound (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {msq : ℝ}
    (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (x : Lam d L N)
    {θ e Cs Λ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (he : 0 ≤ e) (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ)
    (la dg : ℕ → ℂ) (hla : ∀ k ≤ N, ‖la k - la N‖ ≤ Λ * θ ^ k)
    (hg : ∀ k < N, ‖dg k - la (k + 1) * (Flow.covAt d L N msq k x x : ℂ)‖ ≤
      Cs * ellj d L ℓ₀ k ^ 2 * (e * θ ^ k)) :
    ‖∑ k ∈ range N, dg k - la N * ∑ k ∈ range N, (Flow.covAt d L N msq k x x : ℂ)‖ ≤
      2 * (Cs * e + Λ) * ℓ₀ ^ 2 := by
  have hμ : ∀ k < N, ‖la (k + 1) - la N‖ ≤ Λ * θ ^ (k + 1) := fun k hk => hla (k + 1) (by omega)
  have h := norm_sum_sub_mul_sum_le dg (fun k => la (k + 1))
    (fun k => (Flow.covAt d L N msq k x x : ℂ)) (fun _ => 0) (fun k => Cs * ellj d L ℓ₀ k ^ 2 * (e * θ ^ k))
    (fun k => Λ * θ ^ (k + 1)) (la N) (fun k hk => by simpa using hg k hk) hμ
  simp only [norm_zero, sum_const_zero, add_zero] at h
  refine h.trans ?_
  have h1 : ∑ k ∈ range N, Cs * ellj d L ℓ₀ k ^ 2 * (e * θ ^ k) ≤ Cs * e * (2 * ℓ₀ ^ 2) := by
    have := sum_Ico_ellj_sq_pow_le hd hL ℓ₀ hθ0 hθ1 0 N
    rw [← range_eq_Ico, ellj_zero', pow_zero, mul_one] at this
    have e1 : ∀ k, Cs * ellj d L ℓ₀ k ^ 2 * (e * θ ^ k) = Cs * e * (ellj d L ℓ₀ k ^ 2 * θ ^ k) :=
      fun k => by ring
    simp only [e1, ← mul_sum]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : ∑ k ∈ range N, Λ * θ ^ (k + 1) * ‖(Flow.covAt d L N msq k x x : ℂ)‖ ≤
      Λ * (2 * ℓ₀ ^ 2) := by
    have := sum_ite_pow_abs_covAt_le hd hL hℓ₀ hC x x le_rfl hθ0 hθ1 0
    simp only [zero_le, if_true, pow_zero, one_mul, ellj_zero'] at this
    simp only [Complex.norm_real, Real.norm_eq_abs, mul_assoc, ← mul_sum]
    exact mul_le_mul_of_nonneg_left this hΛ
  linarith

end Flow

end

end PtCorr
