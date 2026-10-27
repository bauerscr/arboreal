module

public import ArborealDecay.H02

/-!
# Transport of forest sums along a relabelling of the vertices

For an equivalence `e : W ≃ V` and weights `β` on `V`, `β'` on `W` agreeing off the diagonal
(`β' x y = β (e x) (e y)` for `x ≠ y`), forest sums over `W` and over `V` agree, with graphs
transported by `F ↦ F.comap e.symm`.  Applied to `e = Equiv.optionSubtypeNe ρ`, this identifies
the ghost graph `Λ_ρ ∪ {g}` with weights `ghostW (β|_{Λ_ρ}) (β_{ρ ·})` with the original graph
`Γ = (V, β)`, the ghost `g` becoming `ρ`.
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02

section Equiv

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

theorem forestWeight_comap_equiv (e : W ≃ V) {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    {β' : W → W → ℝ} (hβ' : ∀ i j, β' i j = β' j i)
    (hcomp : ∀ x y, x ≠ y → β' x y = β (e x) (e y)) (F : SimpleGraph W) :
    forestWeight β hβ (F.comap e.symm) = forestWeight β' hβ' F := by
  rw [forestWeight_eq, forestWeight_eq]
  refine Finset.prod_nbij' (Sym2.map e.symm) (Sym2.map e) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    induction s using Sym2.ind with
    | h x y => simpa using hs
  · intro t ht
    induction t using Sym2.ind with
    | h x y => simpa using ht
  · intro s _
    simp [Sym2.map_map]
  · intro t _
    simp [Sym2.map_map]
  · intro s hs
    induction s using Sym2.ind with
    | h x y =>
      simp only [mem_E, SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj] at hs
      simp only [Sym2.map_mk, Sym2.lift_mk]
      rw [hcomp _ _ hs.ne, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem isAcyclic_comap_equiv (e : W ≃ V) (F : SimpleGraph W) :
    (F.comap e.symm).IsAcyclic ↔ F.IsAcyclic :=
  (SimpleGraph.Iso.comap e.symm F).isAcyclic_iff

theorem reachable_comap_equiv (e : W ≃ V) (F : SimpleGraph W) (x y : V) :
    (F.comap e.symm).Reachable x y ↔ F.Reachable (e.symm x) (e.symm y) :=
  (SimpleGraph.Iso.reachable_iff (φ := SimpleGraph.Iso.comap e.symm F)).symm

/-- Forest sums are invariant under relabelling the vertices. -/
theorem fsum_comap_equiv (e : W ≃ V) {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    {β' : W → W → ℝ} (hβ' : ∀ i j, β' i j = β' j i)
    (hcomp : ∀ x y, x ≠ y → β' x y = β (e x) (e y)) (P : SimpleGraph V → Prop) :
    fsum β' hβ' (fun F => P (F.comap e.symm)) = fsum β hβ P := by
  simp only [fsum, fset, Finset.sum_filter]
  refine Fintype.sum_equiv e.simpleGraph _ _ fun F => ?_
  simp only [Equiv.simpleGraph_apply]
  rw [forestWeight_comap_equiv e hβ hβ' hcomp F]

end Equiv

section Ghost

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weights `β|_{Λ_ρ}` on `Λ_ρ = V \ {ρ}`. -/
abbrev restrictW (β : V → V → ℝ) (ρ : V) : {v // v ≠ ρ} → {v // v ≠ ρ} → ℝ :=
  fun a b => β a b

/-- The field `h_j = β_{ρ j}` on `Λ_ρ`. -/
abbrev pinField (β : V → V → ℝ) (ρ : V) : {v // v ≠ ρ} → ℝ := fun a => β ρ a

theorem restrictW_symm {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V) :
    ∀ i j, restrictW β ρ i j = restrictW β ρ j i := fun i j => hβ i j

theorem ghostW_restrict_comp {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V)
    (x y : Option {v // v ≠ ρ}) (hxy : x ≠ y) :
    ghostW (restrictW β ρ) (pinField β ρ) x y =
      β (Equiv.optionSubtypeNe ρ x) (Equiv.optionSubtypeNe ρ y) := by
  rcases x with _ | a <;> rcases y with _ | b
  · exact absurd rfl hxy
  · rfl
  · simp [hβ]
  · rfl

theorem optionSubtypeNe_symm_coe (ρ : V) (i : {v // v ≠ ρ}) :
    (Equiv.optionSubtypeNe ρ).symm i = some i := by
  rw [Equiv.optionSubtypeNe_symm_of_ne i.2]

/-- Forest sums on the ghost graph `Λ_ρ ∪ {g}` are forest sums on `Γ`, with `g ↦ ρ`. -/
theorem fsum_ghost_eq {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V)
    (P : SimpleGraph V → Prop) :
    fsum (ghostW (restrictW β ρ) (pinField β ρ)) (ghostW_symm (restrictW_symm hβ ρ) _)
        (fun F => P (F.comap (Equiv.optionSubtypeNe ρ).symm)) = fsum β hβ P :=
  fsum_comap_equiv _ hβ _ (ghostW_restrict_comp hβ ρ) P

end Ghost

end

end ArborealDecay.Pinned

end
