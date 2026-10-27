module

public import ArborealDecay.Superpoly.Core

/-!
# Diagonal weights are irrelevant
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The weights with the diagonal set to zero. -/
def diagZero (β : V → V → ℝ) (u v : V) : ℝ := if u = v then 0 else β u v

theorem diagZero_symm {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (u v : V) :
    diagZero β u v = diagZero β v u := by
  unfold diagZero
  by_cases h : u = v
  · subst h; rfl
  · simp [h, Ne.symm h, hβ u v]

theorem forestWeight_diagZero {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (F : SimpleGraph V) :
    H02.forestWeight (diagZero β) (diagZero_symm hβ) F = H02.forestWeight β hβ F := by
  unfold H02.forestWeight
  refine Finset.prod_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | h a b =>
    have : a ≠ b := (SimpleGraph.mem_edgeFinset.1 he).ne
    simp [diagZero, this]

theorem connProb_diagZero {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (x z : V) :
    connProb (diagZero β) (diagZero_symm hβ) x z = connProb β hβ x z := by
  unfold connProb H02.arborealProb H02.Zforest
  simp only [forestWeight_diagZero hβ]

/-- **Superpolynomial bound for an arbitrary finite weighted graph with lattice positions**
(from `(W)` and `(AN)`); no assumption on the diagonal weights. -/
theorem superpoly_general_of_inputs
    (hW : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
      ∀ (S : Finset V) (a b : V), a ∉ S → b ∉ S →
        (∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) →
        connProb β hβ a b ≤
          connProb (mapW β (collapse S)) (mapW_symm hβ _) (collapse S a) (collapse S b))
    (hAN : ∀ B : ℝ, 0 ≤ B → ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
      (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * (r : ℤ)) →
      ∀ (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i), (∀ i j, 0 ≤ w i j) →
        (∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j) → (∀ i j, w i j ≤ B) →
        connProb (mapW w (annulusCollapse r Λ)) (mapW_symm hw _) (Sum.inl false) (Sum.inl true)
          ≤ C * (r : ℝ) ^ (-κ)) :
    ∀ B : ℝ, 0 ≤ B → ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (φ : V → ℤ × ℤ), Function.Injective φ →
        ∀ (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
        (∀ i j, β i j ≤ B) →
        (∀ u v, β u v ≠ 0 → |supNorm (φ u) - supNorm (φ v)| ≤ 1) → ∀ (x z : V),
        supNorm (φ x) = 0 →
        (∀ R : ℤ, 2 * R ≤ supNorm (φ z) → ∀ u v, u ≠ v → β u v ≠ 0 → supNorm (φ u) ≤ R →
          supNorm (φ v) ≤ R → IsNN (φ u) (φ v)) →
        connProb β hβ x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + (supNorm (φ z) : ℝ)) ^ 2)) := by
  intro B hB
  obtain ⟨A, a, hA, ha, h⟩ := superpoly_abstract_of_inputs hW hAN B hB
  refine ⟨A, a, hA, ha, ?_⟩
  intro V _ _ φ hφ β hβ hβ0 hβB hLip x z hx hNN
  rw [← connProb_diagZero hβ]
  have hne : ∀ u v, diagZero β u v ≠ 0 → u ≠ v ∧ β u v ≠ 0 := by
    intro u v h
    by_cases huv : u = v
    · simp [diagZero, huv] at h
    · exact ⟨huv, by simpa [diagZero, huv] using h⟩
  refine h V φ hφ (diagZero β) (diagZero_symm hβ) ?_ ?_ ?_ ?_ x z hx ?_
  · intro i j; unfold diagZero; split_ifs
    · exact le_rfl
    · exact hβ0 i j
  · intro i j; unfold diagZero; split_ifs
    · exact hB
    · exact hβB i j
  · intro u; simp [diagZero]
  · intro u v huv; exact hLip u v (hne u v huv).2
  · intro R hR u v huv h1 h2
    exact hNN R hR u v (hne u v huv).1 (hne u v huv).2 h1 h2

end

end ArborealDecay.Superpoly
