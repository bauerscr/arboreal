module

public import ArborealDecay.Superpoly.TorusPos

/-!
# `prop:superpoly` on the torus
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

/-- **`prop:superpoly` on the torus** (from `(W)` and `(AN)`), in the form consumed by
`expDecay_torus_of_inputs`. -/
theorem superpoly_torus_of_inputs
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
      ∀ (L : ℕ) [NeZero L] (β : ZMod L × ZMod L → ZMod L × ZMod L → ℝ)
        (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j)
        (_ : ∀ i j, β i j ≠ 0 → IsTorusNN L i j) (_ : ∀ i j, β i j ≤ B)
        (x z : ZMod L × ZMod L),
        connProb β hβ x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + (torusSupDist L x z : ℝ)) ^ 2)) := by
  intro B hB
  obtain ⟨A, a, hA, ha, h⟩ := superpoly_general_of_inputs hW hAN B hB
  refine ⟨A, a, hA, ha, ?_⟩
  intro L _ β hβ hβ0 hNN hβB x z
  have := h (ZMod L × ZMod L) (torusPos L x) (torusPos_injective x) β hβ hβ0 hβB
    (fun u v huv => by
      rw [supNorm_torusPos, supNorm_torusPos]
      exact abs_torusSupDist_sub_le' (hNN u v huv) x)
    x z (by rw [supNorm_torusPos, torusSupDist_self]; rfl)
    (fun R hR u v huv hne h1 h2 => by
      have hz := torusSupDist_le_half x z
      rw [supNorm_torusPos] at hR
      exact isNN_torusPos (x := x) (R := R) (by omega) huv (hNN u v hne) h1 h2)
  rw [supNorm_torusPos] at this
  exact this

end

end ArborealDecay.Superpoly
