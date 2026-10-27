import Mathlib

/-!
# The `K^{obs}` recursion along the flow: the comparison sequence

`kseq θ B r m`: `k_0 = 0`, `k_{j+1} = θ k_j + B r_j² m_j`, i.e.
`k_n = ∑_{j<n} θ^{n-1-j} B r_j² m_j` (`kseq_eq_sum`). **`kseq_le`**: if `r_{j+1} ≥ (5/6) r_j`,
`m_{j+1} ≥ m_j / 2` and `72(θ c_k + 8B) ≤ 25 c_k`, then `8 k_j ≤ c_k r_j² m_j` (the a priori
condition `8k ≤ c_k r² m` of `PtCorr2.kobs_raw_step` propagates).
-/

open Finset

namespace Obs2

/-- The comparison sequence of the `K^{obs}` recursion. -/
noncomputable def kseq (θ B : ℝ) (r m : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => θ * kseq θ B r m j + B * r j ^ 2 * m j

theorem kseq_zero (θ B : ℝ) (r m : ℕ → ℝ) : kseq θ B r m 0 = 0 := rfl

theorem kseq_succ (θ B : ℝ) (r m : ℕ → ℝ) (j : ℕ) :
    kseq θ B r m (j + 1) = θ * kseq θ B r m j + B * r j ^ 2 * m j := rfl

theorem kseq_nonneg {θ B : ℝ} {r m : ℕ → ℝ} (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hm : ∀ j, 0 ≤ m j) :
    ∀ j, 0 ≤ kseq θ B r m j
  | 0 => le_rfl
  | j + 1 => by
    rw [kseq_succ]
    have := kseq_nonneg (r := r) hθ hB hm j
    have := hm j
    positivity

/-- `k_n = ∑_{j<n} θ^{n-1-j} B r_j² m_j`. -/
theorem kseq_eq_sum (θ B : ℝ) (r m : ℕ → ℝ) :
    ∀ n, kseq θ B r m n = ∑ j ∈ range n, θ ^ (n - 1 - j) * (B * r j ^ 2 * m j)
  | 0 => by simp [kseq_zero]
  | n + 1 => by
    rw [kseq_succ, kseq_eq_sum θ B r m n, sum_range_succ, mul_sum, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, one_mul]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega

/-- **The a priori condition propagates.** -/
theorem kseq_le {θ B ck : ℝ} {r m : ℕ → ℝ} (n : ℕ) (hθ : 0 ≤ θ) (hck : 0 ≤ ck)
    (hr : ∀ j ≤ n, 0 ≤ r j) (hm : ∀ j ≤ n, 0 ≤ m j) (hr' : ∀ j < n, 5 / 6 * r j ≤ r (j + 1))
    (hm' : ∀ j < n, m j ≤ 2 * m (j + 1)) (hc : 72 * (θ * ck + 8 * B) ≤ 25 * ck) :
    ∀ j ≤ n, 8 * kseq θ B r m j ≤ ck * r j ^ 2 * m j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [kseq_zero, mul_zero]
    have := hr 0 (Nat.zero_le _); have := hm 0 (Nat.zero_le _)
    positivity
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    rw [kseq_succ]
    have hrj := hr' j (by omega)
    have hmj := hm' j (by omega)
    have hr0 := hr j (by omega)
    have hm0 := hm j (by omega)
    have hm1 := hm (j + 1) hj
    have h1 : r j ^ 2 ≤ 36 / 25 * r (j + 1) ^ 2 := by nlinarith
    have h2 : r j ^ 2 * m j ≤ 72 / 25 * (r (j + 1) ^ 2 * m (j + 1)) := by
      have a := mul_le_mul_of_nonneg_right h1 hm0
      have b := mul_le_mul_of_nonneg_left hmj (by positivity : (0 : ℝ) ≤ 36 / 25 * r (j + 1) ^ 2)
      linarith
    set X := r j ^ 2 * m j with hX
    have hX0 : 0 ≤ X := by positivity
    have a1 : θ * (8 * kseq θ B r m j) ≤ θ * (ck * X) := by
      refine mul_le_mul_of_nonneg_left ?_ hθ
      rw [hX, ← mul_assoc]; exact ih
    have a2 : (θ * ck + 8 * B) * X ≤ 25 / 72 * ck * X :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    have a3 : 25 / 72 * ck * X ≤ ck * (r (j + 1) ^ 2 * m (j + 1)) := by
      have := mul_le_mul_of_nonneg_left h2 hck
      linarith
    have e1 : 8 * (θ * kseq θ B r m j + B * r j ^ 2 * m j) =
        θ * (8 * kseq θ B r m j) + 8 * B * X := by rw [hX]; ring
    have e2 : (θ * ck + 8 * B) * X = θ * (ck * X) + 8 * B * X := by ring
    have e3 : ck * r (j + 1) ^ 2 * m (j + 1) = ck * (r (j + 1) ^ 2 * m (j + 1)) := by ring
    rw [e1, e3]
    linarith

end Obs2
