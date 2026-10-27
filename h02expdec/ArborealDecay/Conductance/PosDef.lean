module

public import ArborealDecay.Conductance.Basic

/-!
# Positive definiteness of the interior Laplacian block

If every interior vertex is joined to a terminal by a path of positive conductances, then
`lapII c a b` is positive definite (`posDef_lapII`).
-/

@[expose] public section

namespace ArborealDecay.Conductance

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex other than the terminals is joined to `a` or `b` by a path of positive
conductances. -/
def JoinedToTerminals (c : V → V → ℝ) (a b : V) : Prop :=
  ∀ v : V, v ≠ a → v ≠ b →
    Relation.ReflTransGen (fun i j => 0 < c i j) v a ∨
      Relation.ReflTransGen (fun i j => 0 < c i j) v b

theorem energy_eq_zero_imp {c : V → V → ℝ} (hc : ∀ i j, 0 ≤ c i j) {g : V → ℝ}
    (h : energy c g = 0) {i j : V} (hij : 0 < c i j) : g i = g j := by
  unfold energy at h
  have h0 : ∑ i, ∑ j, c i j * (g i - g j) ^ 2 = 0 := by
    rcases mul_eq_zero.1 h with h | h
    · norm_num at h
    · exact h
  have hnn : ∀ i j, 0 ≤ c i j * (g i - g j) ^ 2 := fun i j => mul_nonneg (hc i j) (sq_nonneg _)
  have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg fun j _ => hnn i j)).1 h0 i (mem_univ i)
  have h2 := (sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 h1 j (mem_univ j)
  have : (g i - g j) ^ 2 = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hij.ne'
    · exact h
  linarith [pow_eq_zero_iff (two_ne_zero) |>.1 this]

/-- The quadratic form of `lapII` is the energy of the zero-extended potential. -/
theorem dotProduct_lapII_mulVec {a b : V} (hab : a ≠ b) {c : V → V → ℝ}
    (hs : ∀ i j, c i j = c j i) (x : Interior a b → ℝ) :
    x ⬝ᵥ (lapII c a b *ᵥ x) = energy c (glue a b 0 0 x) := by
  rw [energy_eq_form, energyForm_eq_sum_flow hs, sum_split hab]
  simp only [glue_a hab, glue_b hab, zero_mul, zero_add, glue_interior, dotProduct]
  exact sum_congr rfl fun i _ => by rw [lapII_mulVec_apply hab]

theorem posDef_lapII {a b : V} (hab : a ≠ b) {c : V → V → ℝ} (hs : ∀ i j, c i j = c j i)
    (hc : ∀ i j, 0 ≤ c i j) (hj : JoinedToTerminals c a b) : (lapII c a b).PosDef := by
  have hherm : (lapII c a b).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, star_trivial, lapII, submatrix_apply]
    by_cases h : i.1 = j.1
    · rw [Subtype.ext h]
    · rw [MatrixForest.lap_apply_of_ne c h, MatrixForest.lap_apply_of_ne c (Ne.symm h), hs]
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨hherm, fun x hx => ?_⟩
  simp only [star_trivial]
  rw [dotProduct_lapII_mulVec hab hs]
  have hnn : 0 ≤ energy c (glue a b 0 0 x) := by
    rw [energy_eq_form]; exact energyForm_nonneg hc _
  refine lt_of_le_of_ne hnn (fun h0 => hx ?_)
  have hprop : ∀ {v t : V}, Relation.ReflTransGen (fun i j => 0 < c i j) v t →
      glue a b 0 0 x v = glue a b 0 0 x t := by
    intro v t hvt
    induction hvt with
    | refl => rfl
    | tail _ hm ih => exact ih.trans (energy_eq_zero_imp hc h0.symm hm)
  funext i
  have hi := i.2
  rcases hj i.1 hi.1 hi.2 with hp | hp
  · have := hprop hp
    simpa [glue_a hab] using this
  · have := hprop hp
    simpa [glue_b hab] using this
