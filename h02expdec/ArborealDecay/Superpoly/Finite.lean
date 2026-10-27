module

public import ArborealDecay.Superpoly.Diag

/-!
# `prop:superpoly` for finite nearest-neighbour subgraphs of `ℤ²`
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

theorem isNN_sub_left {a u v : ℤ × ℤ} (h : IsNN u v) : IsNN (a - u) (a - v) := by
  unfold IsNN at h ⊢
  simp only [Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_left]
  rwa [abs_sub_comm (v.1) (u.1), abs_sub_comm (v.2) (u.2)]

/-- **`prop:superpoly` for finite `ℤ²` subgraphs** (from `(W)` and `(AN)`), in the form consumed
by `expDecay_finite_of_inputs`. -/
theorem superpoly_finite_of_inputs
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
      ∀ (Λ : Finset (ℤ × ℤ)) (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i)
        (_ : ∀ i j, 0 ≤ β i j) (_ : ∀ i j, β i j ≠ 0 → IsNN (i : ℤ × ℤ) j)
        (_ : ∀ i j, β i j ≤ B) (x z : Λ),
        connProb β hβ x z ≤ min 1 (A * Real.exp (-a * Real.log (2 + (supDist x z : ℝ)) ^ 2)) := by
  intro B hB
  obtain ⟨A, a, hA, ha, h⟩ := superpoly_general_of_inputs hW hAN B hB
  refine ⟨A, a, hA, ha, ?_⟩
  intro Λ β hβ hβ0 hNN hβB x z
  have hinj : Function.Injective (fun u : Λ => (x : ℤ × ℤ) - (u : ℤ × ℤ)) := by
    intro u v huv
    have : (u : ℤ × ℤ) = v := by
      exact sub_right_injective huv
    exact Subtype.ext this
  have := h Λ (fun u : Λ => (x : ℤ × ℤ) - (u : ℤ × ℤ)) hinj β hβ hβ0 hβB
    (fun u v huv => by
      have := abs_supDist_sub_le' (hNN u v huv) (x : ℤ × ℤ)
      exact this)
    x z (by simp [supNorm])
    (fun R _ u v _ huv _ _ => isNN_sub_left (hNN u v huv))
  exact this

end

end ArborealDecay.Superpoly
