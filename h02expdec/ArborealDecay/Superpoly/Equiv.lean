module

public import ArborealDecay.Surgery
public import ArborealDecay.Superpoly.MapW

/-!
# Invariance of the arboreal gas under relabelling of the vertices
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem forestWeight_comap_equiv (e : V ≃ W) {β : V → V → ℝ} {γ : W → W → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hγ : ∀ i j, γ i j = γ j i)
    (hw : ∀ a b, γ (e a) (e b) = β a b) (F : SimpleGraph V) :
    H02.forestWeight γ hγ (F.comap e.symm) = H02.forestWeight β hβ F := by
  refine forestWeight_eq_of_edge_bij (β := β) (hβ := hβ) (γ := γ) (hγ := hγ) F (F.comap e.symm)
    (Sym2.map e) ?_ ?_ ?_ ?_
  · exact (Sym2.map.injective e.injective).injOn
  · intro y hy
    refine ⟨Sym2.map e.symm y, ?_, ?_⟩
    · induction y using Sym2.ind with
      | h p q => simpa using hy
    · rw [Sym2.map_map]; simp
  · intro x hx
    induction x using Sym2.ind with
    | h p q => simpa using hx
  · intro x _
    induction x using Sym2.ind with
    | h a b => simp [hw]

theorem sum_forest_equiv (e : V ≃ W) {β : V → V → ℝ} {γ : W → W → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hγ : ∀ i j, γ i j = γ j i)
    (hw : ∀ a b, γ (e a) (e b) = β a b) (P : SimpleGraph V → Prop) (P' : SimpleGraph W → Prop)
    (hP : ∀ F : SimpleGraph V, P F ↔ P' (F.comap e.symm)) :
    ∑ F : SimpleGraph V with F.IsAcyclic ∧ P F, H02.forestWeight β hβ F =
      ∑ G : SimpleGraph W with G.IsAcyclic ∧ P' G, H02.forestWeight γ hγ G := by
  refine Finset.sum_nbij' (fun F => F.comap e.symm) (fun G => G.comap e) ?_ ?_ ?_ ?_ ?_
  · intro F hF
    simp only [mem_filter, mem_univ, true_and] at hF ⊢
    exact ⟨(SimpleGraph.Iso.comap e.symm F).isAcyclic_iff.2 hF.1, (hP F).1 hF.2⟩
  · intro G hG
    simp only [mem_filter, mem_univ, true_and] at hG ⊢
    have h1 : (G.comap e).comap e.symm = G := by ext a b; simp
    refine ⟨(SimpleGraph.Iso.comap e G).isAcyclic_iff.2 hG.1, (hP _).2 (by rw [h1]; exact hG.2)⟩
  · intro F _; ext a b; simp
  · intro G _; ext a b; simp
  · intro F _
    exact (forestWeight_comap_equiv e hβ hγ hw F).symm

theorem Zforest_equiv (e : V ≃ W) {β : V → V → ℝ} {γ : W → W → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hγ : ∀ i j, γ i j = γ j i)
    (hw : ∀ a b, γ (e a) (e b) = β a b) :
    H02.Zforest β hβ = H02.Zforest γ hγ := by
  have := sum_forest_equiv e hβ hγ hw (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)
  simpa [H02.Zforest] using this

/-- Relabelling the vertices by an equivalence does not change two-point functions. -/
theorem arborealProb_reach_equiv (e : V ≃ W) {β : V → V → ℝ} {γ : W → W → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hγ : ∀ i j, γ i j = γ j i)
    (hw : ∀ a b, γ (e a) (e b) = β a b) (a b : V) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) =
      H02.arborealProb γ hγ (fun G => G.Reachable (e a) (e b)) := by
  unfold H02.arborealProb
  rw [Zforest_equiv e hβ hγ hw]
  congr 1
  refine sum_forest_equiv e hβ hγ hw _ _ fun F => ?_
  have := (SimpleGraph.Iso.comap e.symm F).reachable_iff (u := e a) (v := e b)
  simpa using this

end

end ArborealDecay.Superpoly
