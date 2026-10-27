module

public import ArborealDecay.Surgery.Cond

/-!
# Lifting graphs along embeddings

Reachability and acyclicity of `G.map ι` for an embedding `ι`, and the comparison of forest
weights along a bijection of edge sets.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

theorem reachable_map_iff {V V' : Type*} (ι : V ↪ V') (G : SimpleGraph V) (u v : V) :
    (G.map ι).Reachable (ι u) (ι v) ↔ G.Reachable u v := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    have key : ∀ x y, Relation.ReflTransGen (G.map ι).Adj x y → ∀ a, ι a = x →
        ∃ b, ι b = y ∧ Relation.ReflTransGen G.Adj a b := by
      intro x y hxy
      induction hxy with
      | refl => intro a ha; exact ⟨a, ha, Relation.ReflTransGen.refl⟩
      | @tail y z _ hyz ih =>
        intro a ha
        obtain ⟨b, hb, hab⟩ := ih a ha
        rw [SimpleGraph.map_adj] at hyz
        obtain ⟨b', c, hbc, hb', hc⟩ := hyz
        have : b' = b := ι.injective (hb'.trans hb.symm)
        subst this
        exact ⟨c, hc, hab.tail hbc⟩
    obtain ⟨b, hb, hab⟩ := key _ _ h u rfl
    rwa [ι.injective hb] at hab
  · intro h
    exact h.map (SimpleGraph.Embedding.map ι G).toHom

theorem isAcyclic_map {V V' : Type*} (ι : V ↪ V') {G : SimpleGraph V} (hG : G.IsAcyclic) :
    (G.map ι).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj ι G x y).1 hxy
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hG) huv
  rw [SimpleGraph.isBridge_iff] at hb ⊢
  intro hr
  apply hb
  have heq : (G.map ι).deleteEdges {s(ι u, ι v)} = (G.deleteEdges {s(u, v)}).map ι := by
    ext a b
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, SimpleGraph.map_adj,
      Sym2.eq_iff]
    constructor
    · rintro ⟨⟨a', b', hab, rfl, rfl⟩, h2⟩
      refine ⟨a', b', ⟨hab, ?_⟩, rfl, rfl⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact h2 (Or.inl ⟨rfl, rfl⟩)
      · exact h2 (Or.inr ⟨rfl, rfl⟩)
    · rintro ⟨a', b', ⟨hab, h2⟩, rfl, rfl⟩
      refine ⟨⟨a', b', hab, rfl, rfl⟩, ?_⟩
      rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
      · exact h2 (Or.inl ⟨ι.injective h3, ι.injective h4⟩)
      · exact h2 (Or.inr ⟨ι.injective h3, ι.injective h4⟩)
  rw [heq] at hr
  exact (reachable_map_iff ι _ u v).1 hr

theorem forestWeight_eq_of_edge_bij {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {γ : W → W → ℝ}
    (hγ : ∀ i j, γ i j = γ j i) (G : SimpleGraph V) (G' : SimpleGraph W) (e : Sym2 V → Sym2 W)
    (hinj : Set.InjOn e G.edgeSet) (hsurj : ∀ y ∈ G'.edgeSet, ∃ x ∈ G.edgeSet, e x = y)
    (hmaps : ∀ x ∈ G.edgeSet, e x ∈ G'.edgeSet)
    (hval : ∀ x ∈ G.edgeSet, Sym2.lift ⟨γ, hγ⟩ (e x) = Sym2.lift ⟨β, hβ⟩ x) :
    H02.forestWeight γ hγ G' = H02.forestWeight β hβ G := by
  unfold H02.forestWeight
  symm
  refine Finset.prod_bij (fun x _ => e x) ?_ ?_ ?_ ?_
  · intro x hx; exact SimpleGraph.mem_edgeFinset.2 (hmaps x (SimpleGraph.mem_edgeFinset.1 hx))
  · intro x hx y hy hxy
    exact hinj (SimpleGraph.mem_edgeFinset.1 hx) (SimpleGraph.mem_edgeFinset.1 hy) hxy
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y (SimpleGraph.mem_edgeFinset.1 hy)
    exact ⟨x, SimpleGraph.mem_edgeFinset.2 hx, rfl⟩
  · intro x hx
    exact (hval x (SimpleGraph.mem_edgeFinset.1 hx)).symm

end

end ArborealDecay.Surgery
