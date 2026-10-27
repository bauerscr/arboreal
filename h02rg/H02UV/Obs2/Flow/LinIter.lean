import Mathlib

/-!
# Forward iteration of the (linear) observable flow: abstract bounds

Given the bulk trajectory, the observable flow is linear in the observable data, and it is solved
by forward iteration (no fixed point). This file contains the two elementary facts used for it.

* `lin_iter`: the coupled linear recursion
  `m_{j+1} ≤ (1 + a_j) m_j + A k_j`, `k_{j+1} ≤ θ k_j + B g_j² m_j` (`0 ≤ θ < 1`)
  — `m_j` the size of the observable couplings, `k_j = ‖K^{obs}_j‖`, `g_j = ḡ_j`,
  `a_j = O(ḡ_j²)` — is controlled by the Lyapunov function `Φ_j = m_j + (A/(1-θ)) k_j`:
  `Φ_{j+1} ≤ (1 + a_j + A B g_j²/(1-θ)) Φ_j`, hence
  `Φ_n ≤ exp(∑_{j<n} (a_j + A B g_j²/(1-θ))) Φ_0`;
* `lin_iter_K`: then `k_n ≤ θ^n k_0 + B M ∑_{j<n} θ^{n-1-j} g_j²` with `M` the bound on `m`;
* `renorm_eq`, `renorm_bound`: for `μ_{j+1} = (1 + x_j) μ_j + e_j`,
  `μ_n = P_n (μ_0 + ∑_{j<n} e_j / P_{j+1})` with `P_n = ∏_{j<n} (1 + x_j)` (the renormalised
  coupling `μ_n / P_n` converges if `∑ |e_j/P_{j+1}| < ∞`); used for `λ_j/λ_0` in
  Proposition `prop:gamma`.
-/

open Finset

namespace Obs2

/-- **The Lyapunov step.** -/
theorem lin_step {m k m' k' a g A B θ : ℝ} (hθ : θ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (h1 : m' ≤ (1 + a) * m + A * k) (h2 : k' ≤ θ * k + B * g ^ 2 * m) :
    m' + A / (1 - θ) * k' ≤ (1 + a + A * B * g ^ 2 / (1 - θ)) * (m + A / (1 - θ) * k) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hκ : 0 ≤ A / (1 - θ) := div_nonneg hA h1θ.le
  have e : A + A / (1 - θ) * θ = A / (1 - θ) := by field_simp; ring
  have h3 : A / (1 - θ) * k' ≤ A / (1 - θ) * (θ * k + B * g ^ 2 * m) :=
    mul_le_mul_of_nonneg_left h2 hκ
  have h4 : (1 + a + A * B * g ^ 2 / (1 - θ)) * (m + A / (1 - θ) * k) =
      (1 + a + A * B * g ^ 2 / (1 - θ)) * m + A / (1 - θ) * k +
        (a + A * B * g ^ 2 / (1 - θ)) * (A / (1 - θ) * k) := by ring
  have h5 : (1 + a) * m + A * k + A / (1 - θ) * (θ * k + B * g ^ 2 * m) =
      (1 + a + A * B * g ^ 2 / (1 - θ)) * m + A / (1 - θ) * k := by
    field_simp; ring
  have h6 : 0 ≤ (a + A * B * g ^ 2 / (1 - θ)) * (A / (1 - θ) * k) :=
    mul_nonneg (add_nonneg ha (div_nonneg (by have := sq_nonneg g; positivity) h1θ.le))
      (mul_nonneg hκ hk)
  linarith [h4, h5, h3, h1, h6]

/-- **Forward iteration of the coupled linear recursion.** -/
theorem lin_iter {m k a g : ℕ → ℝ} {A B θ : ℝ} (n : ℕ) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : ∀ j, 0 ≤ m j) (hk : ∀ j, 0 ≤ k j) (ha : ∀ j, 0 ≤ a j)
    (h1 : ∀ j < n, m (j + 1) ≤ (1 + a j) * m j + A * k j)
    (h2 : ∀ j < n, k (j + 1) ≤ θ * k j + B * g j ^ 2 * m j) :
    ∀ j ≤ n, m j + A / (1 - θ) * k j ≤
      Real.exp (∑ i ∈ range j, (a i + A * B * g i ^ 2 / (1 - θ))) * (m 0 + A / (1 - θ) * k 0) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hκ : 0 ≤ A / (1 - θ) := div_nonneg hA h1θ.le
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have ih := ih (by omega)
    have hb : 0 ≤ a j + A * B * g j ^ 2 / (1 - θ) :=
      add_nonneg (ha j) (div_nonneg (by have := sq_nonneg (g j); positivity) h1θ.le)
    have hs := lin_step hθ hA hB (ha j) (hk j) (h1 j (by omega)) (h2 j (by omega))
    have hΦ : 0 ≤ m j + A / (1 - θ) * k j := add_nonneg (hm j) (mul_nonneg hκ (hk j))
    have hexp : 1 + (a j + A * B * g j ^ 2 / (1 - θ)) ≤
        Real.exp (a j + A * B * g j ^ 2 / (1 - θ)) := by
      have := Real.add_one_le_exp (a j + A * B * g j ^ 2 / (1 - θ)); linarith
    rw [sum_range_succ, Real.exp_add]
    calc m (j + 1) + A / (1 - θ) * k (j + 1)
        ≤ (1 + a j + A * B * g j ^ 2 / (1 - θ)) * (m j + A / (1 - θ) * k j) := hs
      _ ≤ Real.exp (a j + A * B * g j ^ 2 / (1 - θ)) * (m j + A / (1 - θ) * k j) := by
          rw [← add_assoc] at hexp
          exact mul_le_mul_of_nonneg_right hexp hΦ
      _ ≤ Real.exp (a j + A * B * g j ^ 2 / (1 - θ)) * (Real.exp (∑ i ∈ range j,
            (a i + A * B * g i ^ 2 / (1 - θ))) * (m 0 + A / (1 - θ) * k 0)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by ring

/-- **The bound on `k`** given a bound `M` on `m`. -/
theorem lin_iter_K {m k g : ℕ → ℝ} {B θ M : ℝ} (n : ℕ) (hθ0 : 0 ≤ θ) (hB : 0 ≤ B)
    (hM : ∀ j < n, m j ≤ M)
    (h2 : ∀ j < n, k (j + 1) ≤ θ * k j + B * g j ^ 2 * m j) :
    ∀ j ≤ n, k j ≤ θ ^ j * k 0 + B * M * ∑ i ∈ range j, θ ^ (j - 1 - i) * g i ^ 2 := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have ih := ih (by omega)
    have hg : 0 ≤ g j ^ 2 := sq_nonneg _
    have e1 : B * g j ^ 2 * m j ≤ B * M * g j ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hM j (by omega)) (mul_nonneg hB hg); nlinarith
    have e2 : θ * ∑ i ∈ range j, θ ^ (j - 1 - i) * g i ^ 2 =
        ∑ i ∈ range j, θ ^ (j + 1 - 1 - i) * g i ^ 2 := by
      rw [mul_sum]; refine sum_congr rfl fun i hi => ?_
      have hi := mem_range.1 hi
      rw [show j + 1 - 1 - i = (j - 1 - i) + 1 by omega, pow_succ]; ring
    rw [sum_range_succ, show j + 1 - 1 - j = 0 by omega, pow_zero, one_mul]
    calc k (j + 1) ≤ θ * k j + B * g j ^ 2 * m j := h2 j (by omega)
      _ ≤ θ * (θ ^ j * k 0 + B * M * ∑ i ∈ range j, θ ^ (j - 1 - i) * g i ^ 2) +
          B * M * g j ^ 2 := by
          have := mul_le_mul_of_nonneg_left ih hθ0; linarith
      _ = _ := by rw [mul_add, ← mul_assoc, ← pow_succ', mul_left_comm θ (B * M), e2]; ring

/-- **The renormalised coupling**: for `μ_{j+1} = (1 + x_j) μ_j + e_j` with `1 + x_j ≠ 0`,
`μ_n = P_n (μ_0 + ∑_{j<n} e_j / P_{j+1})`, `P_n = ∏_{j<n} (1 + x_j)`. -/
theorem renorm_eq {𝕜 : Type*} [Field 𝕜] {μ x e : ℕ → 𝕜} (hx : ∀ j, 1 + x j ≠ 0)
    (h : ∀ j, μ (j + 1) = (1 + x j) * μ j + e j) (n : ℕ) :
    μ n = (∏ j ∈ range n, (1 + x j)) *
      (μ 0 + ∑ j ∈ range n, e j / ∏ i ∈ range (j + 1), (1 + x i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (∏ i ∈ range n, (1 + x i)) * (1 + x n) ≠ 0 :=
      mul_ne_zero (prod_ne_zero_iff.2 fun i _ => hx i) (hx n)
    have key : (∏ i ∈ range n, (1 + x i)) * (1 + x n) *
        (e n / ((∏ i ∈ range n, (1 + x i)) * (1 + x n))) = e n := mul_div_cancel₀ _ hA
    rw [h n, ih, sum_range_succ, prod_range_succ]
    linear_combination -key

/-- `|μ_n / P_n - μ_0| ≤ ∑_{j<n} |e_j| / |P_{j+1}|`. -/
theorem renorm_bound {μ x e : ℕ → ℂ} (hx : ∀ j, 1 + x j ≠ 0)
    (h : ∀ j, μ (j + 1) = (1 + x j) * μ j + e j) (n : ℕ) :
    ‖μ n / (∏ j ∈ range n, (1 + x j)) - μ 0‖ ≤
      ∑ j ∈ range n, ‖e j‖ / ‖∏ i ∈ range (j + 1), (1 + x i)‖ := by
  have hP : ∏ j ∈ range n, (1 + x j) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hx i
  rw [renorm_eq hx h n, mul_div_cancel_left₀ _ hP, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun j _ => norm_div _ _

end Obs2
