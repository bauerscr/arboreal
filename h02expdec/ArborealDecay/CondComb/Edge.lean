module

public import ArborealDecay.Forest
public import ArborealDecay.H02

/-!
# First-edge decomposition of connected forests

For `x ≠ y`, a forest `F` of `G` with `x ↔ y` is uniquely `F₁ + xi`, where `i` is the second vertex of
the `x`–`y` path in `F`, `F₁` is a forest with `x ↮ i` and `i ↔ y`.  `sum_conn_eq` is the resulting
weight identity (with an arbitrary observable `h` of the forest).
-/

@[expose] public section

namespace ArborealDecay.CondComb

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex `i` with `xi` a bridge separating `x` from `y` is determined by `F`. -/
theorem eq_of_bridge_edges {F : SimpleGraph V} {x y i i' : V} (hr : F.Reachable x y)
    (hi : ¬ (F.deleteEdges {s(x, i)}).Reachable x y)
    (hi' : ¬ (F.deleteEdges {s(x, i')}).Reachable x y) : i = i' := by
  obtain ⟨p, hp⟩ := hr.exists_isPath
  have mem : ∀ j, ¬ (F.deleteEdges {s(x, j)}).Reachable x y → s(x, j) ∈ p.edges := by
    intro j hj
    by_contra h
    exact hj ⟨p.toDeleteEdge _ h⟩
  have h1 := mem i hi
  have h2 := mem i' hi'
  cases p with
  | nil => simp at h1
  | @cons _ z _ hadj q =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have key : ∀ j, s(x, j) ∈ (SimpleGraph.Walk.cons hadj q).edges → j = z := by
      intro j hj
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hj
      rcases hj with hj | hj
      · rw [Sym2.eq_iff] at hj
        rcases hj with ⟨_, h⟩ | ⟨h, h'⟩
        · exact h
        · subst h; subst h'; rfl
      · exact absurd (q.fst_mem_support_of_mem_edges hj) hp.2
    exact (key i h1).trans (key i' h2).symm

/-- In a forest, the first edge of the `x`–`y` path is a bridge separating `x` from `y`. -/
theorem exists_first_edge {F : SimpleGraph V} (hF : F.IsAcyclic) {x y : V} (hxy : x ≠ y)
    (hr : F.Reachable x y) :
    ∃ z, F.Adj x z ∧ ¬ (F.deleteEdges {s(x, z)}).Reachable x z ∧
      (F.deleteEdges {s(x, z)}).Reachable z y := by
  obtain ⟨p, hp⟩ := hr.exists_isPath
  cases p with
  | nil => exact absurd rfl hxy
  | @cons _ z _ hadj q =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    refine ⟨z, hadj, ?_, ?_⟩
    · have := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hF) hadj
      rw [SimpleGraph.isBridge_iff] at this
      exact this
    · have hn : s(x, z) ∉ q.edges := fun h => hp.2 (q.fst_mem_support_of_mem_edges h)
      exact ⟨q.toDeleteEdge _ hn⟩

/-- The weight identity for the first-edge decomposition. -/
theorem sum_conn_eq {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {x y : V} (hxy : x ≠ y)
    (h : SimpleGraph V → ℝ) :
    ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable x y, H02.forestWeight β hβ F * h F =
      ∑ i : V with i ≠ x, β x i *
        ∑ F₁ : SimpleGraph V with F₁.IsAcyclic ∧ ¬ F₁.Reachable x i ∧ F₁.Reachable i y,
          H02.forestWeight β hβ F₁ * h (F₁ ⊔ SimpleGraph.edge x i) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_sigma' (Finset.univ.filter fun i : V => i ≠ x)
    (fun i => Finset.univ.filter fun F₁ : SimpleGraph V =>
      F₁.IsAcyclic ∧ ¬ F₁.Reachable x i ∧ F₁.Reachable i y)]
  symm
  refine Finset.sum_bij (fun p _ => p.2 ⊔ SimpleGraph.edge x p.1) ?_ ?_ ?_ ?_
  · rintro ⟨i, F₁⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hi, hac, hnr, hiy⟩ := hp
    refine ⟨(SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable x i hnr).2 hac, ?_⟩
    have hxi : (F₁ ⊔ SimpleGraph.edge x i).Reachable x i := by
      refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, Ne.symm hi⟩
    exact hxi.trans (hiy.mono le_sup_left)
  · rintro ⟨i, F₁⟩ hp ⟨i', F₁'⟩ hp' heq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    simp only at heq
    obtain ⟨hi, hac, hnr, hiy⟩ := hp
    obtain ⟨hi', hac', hnr', hiy'⟩ := hp'
    have hnadj : ¬ F₁.Adj x i := fun h => hnr h.reachable
    have hnadj' : ¬ F₁'.Adj x i' := fun h => hnr' h.reachable
    have hdel : (F₁ ⊔ SimpleGraph.edge x i).deleteEdges {s(x, i)} = F₁ :=
      H02.sup_edge_deleteEdges hnadj
    have hdel' : (F₁' ⊔ SimpleGraph.edge x i').deleteEdges {s(x, i')} = F₁' :=
      H02.sup_edge_deleteEdges hnadj'
    have hnxy : ¬ F₁.Reachable x y := fun hh => hnr (hh.trans hiy.symm)
    have hnxy' : ¬ F₁'.Reachable x y := fun hh => hnr' (hh.trans hiy'.symm)
    have hr : (F₁ ⊔ SimpleGraph.edge x i).Reachable x y := by
      have hxi : (F₁ ⊔ SimpleGraph.edge x i).Reachable x i := by
        refine SimpleGraph.Adj.reachable ?_
        rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, Ne.symm hi⟩
      exact hxi.trans (hiy.mono le_sup_left)
    have hii : i = i' := by
      refine eq_of_bridge_edges hr ?_ ?_
      · rw [hdel]; exact hnxy
      · rw [heq, hdel']; exact hnxy'
    subst hii
    have : F₁ = F₁' := by rw [← hdel, ← hdel', heq]
    subst this
    rfl
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    obtain ⟨z, hadj, hnr, hzy⟩ := exists_first_edge hF.1 hxy hF.2
    refine ⟨⟨z, F.deleteEdges {s(x, z)}⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj.ne.symm, hF.1.anti (SimpleGraph.deleteEdges_le _), hnr, hzy⟩
    · exact H02.deleteEdges_sup_edge hadj
  · rintro ⟨i, F₁⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hi, hac, hnr, hiy⟩ := hp
    have hnadj : ¬ F₁.Adj x i := fun h => hnr h.reachable
    simp only
    rw [Forest.forestWeight_sup_edge hβ (Ne.symm hi) F₁ hnadj]
    ring

end

end ArborealDecay.CondComb
