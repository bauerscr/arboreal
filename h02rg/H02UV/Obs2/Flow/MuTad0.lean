import Mathlib

/-!
# Unrolling the recursion of the tadpole functional (pure algebra)

The functional `G_j(Γ) = ∑_B m(e^{ℒ_Γ} 𝒲_j(B)_a)` of `Obs2.Flow.MuTad1` satisfies
`G_{k+1}(Γ) = T_k(Γ) + (G_k(Γ + C_k) - G_k(C_k))` (`wTad_step`, with `T_k` the one-loop tadpole plus
the product part). Unrolled (`tad_unroll`):

  `G_j(Γ) = G_j(0) + ∑_{k<j} (T_k(Γ + S_{k,j}) - T_k(S_{k,j}))`,  `S_{k,j} = ∑_{k<i<j} C_i`

(`cumBetween`): the contribution of step `k` is contracted by the covariances of the later steps.

`drift_sum_le`: `∑_{k<j} |x_k - x_j| |t_k| ≤ A B q/(1-q)²` if `|x_k - x_j| ≤ A (j-k)` and
`|t_k| ≤ B q^{j-k}` (`0 ≤ q < 1`): the bound for the drift term `∑_{k<j}(β_kg_k - β_jg_j) τ(C_k, C_j)`
of the `μ` flow.
-/

open Finset

namespace Obs2

/-- `S_{k,j} = ∑_{k < i < j} C_i`. -/
def cumBetween {M : Type*} [AddCommMonoid M] (C : ℕ → M) (k j : ℕ) : M := ∑ i ∈ Ioo k j, C i

theorem cumBetween_succ {M : Type*} [AddCommMonoid M] (C : ℕ → M) {k j : ℕ} (h : k < j) :
    cumBetween C k (j + 1) = cumBetween C k j + C j := by
  unfold cumBetween
  have e : Ioo k (j + 1) = insert j (Ioo k j) := by
    ext i; simp only [mem_Ioo, mem_insert]; omega
  rw [e, sum_insert (by simp), add_comm]

theorem cumBetween_self_succ {M : Type*} [AddCommMonoid M] (C : ℕ → M) (j : ℕ) :
    cumBetween C j (j + 1) = 0 := by
  unfold cumBetween
  have e : Ioo j (j + 1) = ∅ := by ext i; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega
  rw [e, sum_empty]

/-- **Unrolling the tadpole recursion.** -/
theorem tad_unroll {M : Type*} [AddCommMonoid M] (G T : ℕ → M → ℂ) (C : ℕ → M)
    (h0 : ∀ Γ, G 0 Γ = G 0 0)
    (hs : ∀ k Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k))) :
    ∀ j Γ, G j Γ = G j 0 +
      ∑ k ∈ range j, (T k (Γ + cumBetween C k j) - T k (cumBetween C k j)) := by
  intro j
  induction j with
  | zero => intro Γ; rw [h0 Γ, range_zero, sum_empty, add_zero]
  | succ j ih =>
    intro Γ
    have hG0 : G (j + 1) 0 = T j 0 := by rw [hs j 0, zero_add, sub_self, add_zero]
    rw [hs j Γ, hG0, ih (Γ + C j), ih (C j), sum_range_succ, cumBetween_self_succ, add_zero]
    have e : ∀ k ∈ range j, T k (Γ + cumBetween C k (j + 1)) - T k (cumBetween C k (j + 1)) =
        T k (Γ + C j + cumBetween C k j) - T k (C j + cumBetween C k j) := by
      intro k hk
      rw [cumBetween_succ C (mem_range.1 hk), add_comm (cumBetween C k j) (C j), add_assoc]
    rw [sum_congr rfl e]
    have hsum : ∑ k ∈ range j, (T k (Γ + C j + cumBetween C k j) - T k (cumBetween C k j)) -
        ∑ k ∈ range j, (T k (C j + cumBetween C k j) - T k (cumBetween C k j)) =
        ∑ k ∈ range j, (T k (Γ + C j + cumBetween C k j) - T k (C j + cumBetween C k j)) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    linear_combination hsum

/-- **The drift sum.** -/
theorem drift_sum_le {x t : ℕ → ℂ} {A B q : ℝ} (j : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hq0 : 0 ≤ q)
    (hq : q < 1) (hx : ∀ k < j, ‖x k - x j‖ ≤ A * (j - k : ℕ))
    (ht : ∀ k < j, ‖t k‖ ≤ B * q ^ (j - k)) :
    ‖∑ k ∈ range j, (x k - x j) * t k‖ ≤ A * B * (q / (1 - q) ^ 2) := by
  have hq' : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one hq').summable
  have h1 : ∑ k ∈ range j, ‖(x k - x j) * t k‖ ≤
      A * B * ∑ k ∈ range j, ((j - k : ℕ) : ℝ) * q ^ (j - k) := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk' := mem_range.1 hk
    rw [norm_mul]
    calc ‖x k - x j‖ * ‖t k‖ ≤ (A * (j - k : ℕ)) * (B * q ^ (j - k)) :=
          mul_le_mul (hx k hk') (ht k hk') (norm_nonneg _) (by positivity)
      _ = A * B * (((j - k : ℕ) : ℝ) * q ^ (j - k)) := by ring
  have h2 : ∑ k ∈ range j, ((j - k : ℕ) : ℝ) * q ^ (j - k) ≤ q / (1 - q) ^ 2 := by
    have e : ∑ k ∈ range j, ((j - k : ℕ) : ℝ) * q ^ (j - k) =
        ∑ n ∈ (range (j + 1)).filter (· ≠ 0), (n : ℝ) * q ^ n := by
      refine sum_nbij' (fun k => j - k) (fun n => j - n) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [mem_range, mem_filter] at hk ⊢; omega
      · intro n hn; simp only [mem_range, mem_filter] at hn ⊢; omega
      · intro k hk; simp only [mem_range] at hk; omega
      · intro n hn; simp only [mem_range, mem_filter] at hn; omega
      · intro k _; rfl
    rw [e, ← (hasSum_coe_mul_geometric_of_norm_lt_one hq').tsum_eq]
    exact Summable.sum_le_tsum _ (fun n _ => by positivity) hsum
  calc ‖∑ k ∈ range j, (x k - x j) * t k‖ ≤ ∑ k ∈ range j, ‖(x k - x j) * t k‖ := norm_sum_le _ _
    _ ≤ A * B * ∑ k ∈ range j, ((j - k : ℕ) : ℝ) * q ^ (j - k) := h1
    _ ≤ A * B * (q / (1 - q) ^ 2) := mul_le_mul_of_nonneg_left h2 (mul_nonneg hA hB)

end Obs2
