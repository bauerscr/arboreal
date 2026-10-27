import H02.Tree
import Loc.Polymer
import FRD.LatticeSum
import H02.Symm

/-!
# Definitions for Section `sec:ward`

* `nnW d L N β`: the nearest-neighbour weight matrix of the torus `Λ_N`,
  `nnW x y = β · #{e ∈ 𝓔_d : y = x + e}` (for `L^N ≥ 3` this is `β 1[x ∼ y]`).
  `sum_nnW_mul`: `∑_y nnW x y f y = β ∑_e f (x + e)`.
* `toT N x`: the projection `ℤ^d → Λ_N`.
* `eNorm x`: the Euclidean norm `|x|` of `x ∈ ℤ^d`.
* `H02.expTree`, `H02.ghostW`, `H02.base` are defined in `H02/Tree.lean` (re-exported here).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

variable (d L N) in
/-- The nearest-neighbour weights `β_{xy} = β · #{e ∈ 𝓔_d : y = x + e}` on `Λ_N`. -/
def nnW (β : ℝ) (x y : Lam d L N) : ℝ := β * (univ.filter fun e : Dir d => y = x + dirVec e).card

theorem card_dir_symm (x y : Lam d L N) :
    (univ.filter fun e : Dir d => y = x + dirVec e).card =
      (univ.filter fun e : Dir d => x = y + dirVec e).card := by
  refine Finset.card_bij (fun e _ => e.swap) (fun e he => ?_) (fun e _ e' _ h => ?_) (fun e he => ?_)
  · simp only [mem_filter, mem_univ, true_and] at he ⊢
    rw [dirVec_swap, he]; abel
  · simpa using congrArg Sum.swap h
  · refine ⟨e.swap, ?_, Sum.swap_swap e⟩
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    rw [dirVec_swap, he]; abel

theorem nnW_symm (β : ℝ) : ∀ x y : Lam d L N, nnW d L N β x y = nnW d L N β y x := by
  intro x y; rw [nnW, nnW, card_dir_symm]

theorem nnW_nonneg {β : ℝ} (hβ : 0 ≤ β) : ∀ x y : Lam d L N, 0 ≤ nnW d L N β x y :=
  fun _ _ => mul_nonneg hβ (Nat.cast_nonneg _)

/-- `∑_y β_{xy} f(y) = β ∑_{e ∈ 𝓔_d} f(x + e)`. -/
theorem sum_nnW_mul {M : Type*} [AddCommMonoid M] [Module ℝ M] (β : ℝ) (x : Lam d L N)
    (f : Lam d L N → M) : ∑ y, nnW d L N β x y • f y = β • ∑ e : Dir d, f (x + dirVec e) := by
  have h1 : ∀ y, (((univ.filter fun e : Dir d => y = x + dirVec e).card : ℕ) : ℝ) • f y =
      ∑ e : Dir d, if y = x + dirVec e then f y else 0 := by
    intro y
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_smul, Finset.sum_filter]
    refine sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  calc ∑ y, nnW d L N β x y • f y
      = ∑ y, β • ((((univ.filter fun e : Dir d => y = x + dirVec e).card : ℕ) : ℝ) • f y) := by
        simp only [nnW, mul_smul]
    _ = β • ∑ e : Dir d, f (x + dirVec e) := by
        rw [← smul_sum, sum_congr rfl fun y _ => h1 y, sum_comm]
        simp [sum_ite_eq']

variable (L N) in
/-- The projection `ℤ^d → Λ_N`. -/
abbrev toT (x : Zd d) : Lam d L N := prj x

/-- The Euclidean norm `|x| = (∑_i x_i²)^{1/2}` on `ℤ^d` (`= FRD.eNorm`). -/
abbrev eNorm (x : Zd d) : ℝ := FRD.eNorm x

/-- `⟨ξ_a η_b⟩_{β,h} = ⟨ξ_b η_a⟩_{β,h}`. -/
theorem avg_ξη_symm_nnW (β h : ℝ) (a b : Lam d L N) :
    H02.avg (nnW d L N β) (fun _ => h) (H02.ξ a * H02.η b) =
      H02.avg (nnW d L N β) (fun _ => h) (H02.ξ b * H02.η a) :=
  H02.avg_ξη_symm _ (nnW_symm β) _ a b

end

end Ward
