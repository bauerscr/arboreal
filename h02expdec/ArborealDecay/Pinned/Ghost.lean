module

public import ArborealDecay.Pinned.Main
public import ArborealDecay.Pinned.ForestInsert

/-!
# Supplement `lem:ghost` (iii): the forest identities of the ghost bijection

For real symmetric weights `β` on `V`, `ρ ∈ V`, `Λ_ρ = V \ {ρ}`, `h_i = β_{ρ i}`:

* `Z_Γ = ∑_{F ∈ 𝓕(K_{Λ_ρ})} β(F) ∏_τ (1 + h(τ))`;
* for `a, b ∈ Λ_ρ`: `∑_{F' ∈ 𝓕(K_V) : a ↔ b, a ↮ ρ} β(F') =
  ∑_{F ∈ 𝓕(K_{Λ_ρ}) : a ↔_F b} β(F) ∏_{τ ≠ τ_F(a)} (1 + h(τ))`.

They are obtained here by evaluating both sides as the same Grassmann integral
(`thm_H02_pinned_denominator`/`thm_H02_pinned_numerator` and `H02.thm_H02forest`/
`expect_ξη_forest`), rather than through the explicit bijection `Ψ` of the supplement.
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Supplement `lem:ghost` (iii), partition function**: `Z_Γ = ∑_F β(F) ∏_τ (1 + h(τ))`,
the sum over forests `F` of `K_{Λ_ρ}` and `τ` over the trees of `F`. Real symmetric weights. -/
theorem lem_ghost_Z {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V) :
    Zforest β hβ = ∑ F : SimpleGraph {v // v ≠ ρ} with F.IsAcyclic,
      (∏ e ∈ F.edgeFinset, Sym2.lift ⟨fun a b : {v // v ≠ ρ} => β a b, restrictW_symm hβ ρ⟩ e) *
        ∏ T : F.ConnectedComponent,
          (1 + ∑ i with F.connectedComponentMk i = T, β ρ i) := by
  rw [← thm_H02_pinned_denominator hβ ρ, thm_H02forest]

/-- **Supplement `lem:ghost` (iii), the event `a ↔ b, a ↮ ρ`**: for `a, b ∈ Λ_ρ`,
`∑_{F' ∈ 𝓕(K_V) : a ↔ b, a ↮ ρ} β(F') = ∑_{F ∈ 𝓕(K_{Λ_ρ}) : a ↔_F b} β(F)
  ∏_{τ ≠ τ_F(a)} (1 + h(τ))`. Real symmetric weights. -/
theorem lem_ghost_event {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V)
    (a b : {v // v ≠ ρ}) :
    ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable a b ∧ ¬F.Reachable a ρ,
        forestWeight β hβ F =
      ∑ F : SimpleGraph {v // v ≠ ρ} with F.IsAcyclic ∧ F.Reachable a b,
        (∏ e ∈ F.edgeFinset,
            Sym2.lift ⟨fun a b : {v // v ≠ ρ} => β a b, restrictW_symm hβ ρ⟩ e) *
          ∏ T : F.ConnectedComponent with T ≠ F.connectedComponentMk a,
            (1 + ∑ i with F.connectedComponentMk i = T, β ρ i) := by
  rw [← thm_H02_pinned_numerator hβ ρ, expect_ξη_forest]

end

end ArborealDecay.Pinned

end
