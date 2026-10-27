module

public import ArborealDecay.SimonLieb.TwoTrees
public import ArborealDecay.Forest.PathSum

/-!
# Path factorization (`eq:path-factor`)

For a simple path `γ = α · uv · δ` in the complete graph (`α : x → u`, `δ : v → z`),
`μ(γ ⊆ F) ≤ μ(uv ∈ F) μ(α ⊆ F) μ(δ ⊆ F)` (conditional on `hstab`), by two applications of
`two_trees_of_stable`: to `α` and `{uv} ∪ δ` (sharing `u`), then to `{uv}` and `δ` (sharing `v`).
-/

@[expose] public section

namespace ArborealDecay.SimonLieb

universe u

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical SimpleGraph

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- The graph whose edges are the edges of a walk. -/
def walkGraph {a b : Λ} (w : (⊤ : SimpleGraph Λ).Walk a b) : SimpleGraph Λ :=
  fromEdgeSet {e | e ∈ w.edges}

theorem mem_edgeSet_walkGraph {a b : Λ} (w : (⊤ : SimpleGraph Λ).Walk a b) (e : Sym2 Λ) :
    e ∈ (walkGraph w).edgeSet ↔ e ∈ w.edges := by
  unfold walkGraph
  rw [edgeSet_fromEdgeSet]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact (⊤ : SimpleGraph Λ).not_isDiag_of_mem_edgeSet (w.edges_subset_edgeSet h)

theorem walkGraph_le_iff {a b : Λ} (w : (⊤ : SimpleGraph Λ).Walk a b) (F : SimpleGraph Λ) :
    walkGraph w ≤ F ↔ ∀ e ∈ w.edges, e ∈ F.edgeSet := by
  rw [← edgeSet_subset_edgeSet]
  refine ⟨fun h e he => h ((mem_edgeSet_walkGraph w e).2 he),
    fun h e he => h e ((mem_edgeSet_walkGraph w e).1 he)⟩

theorem walkGraph_reachable {a b : Λ} (w : (⊤ : SimpleGraph Λ).Walk a b) :
    ∀ y ∈ w.support, (walkGraph w).Reachable a y := by
  induction w with
  | nil =>
    intro y hy
    rw [Walk.support_nil, List.mem_singleton] at hy
    rw [hy]
  | @cons a c b h p ih =>
    intro y hy
    rw [Walk.support_cons, List.mem_cons] at hy
    have hle : walkGraph p ≤ walkGraph (Walk.cons h p) := by
      rw [← edgeSet_subset_edgeSet]
      intro e he
      rw [mem_edgeSet_walkGraph] at he ⊢
      rw [Walk.edges_cons]
      exact List.mem_cons_of_mem _ he
    have hadj : (walkGraph (Walk.cons h p)).Adj a c := by
      rw [← mem_edgeSet, mem_edgeSet_walkGraph, Walk.edges_cons]
      exact List.mem_cons_self
    rcases hy with rfl | hy
    · rfl
    · exact hadj.reachable.trans ((ih y hy).mono hle)

theorem walkGraph_adj_mem {a b : Λ} (w : (⊤ : SimpleGraph Λ).Walk a b) {c d : Λ}
    (h : (walkGraph w).Adj c d) : c ∈ w.support := by
  rw [← mem_edgeSet, mem_edgeSet_walkGraph] at h
  exact w.fst_mem_support_of_mem_edges h

/-- Every edge of the walk graph lies in the component of the end vertex. -/
theorem walkGraph_reach_end {a b : Λ} (w : (⊤ : SimpleGraph Λ).Walk a b) :
    ∀ c d, (walkGraph w).Adj c d → (walkGraph w).Reachable b c := fun _ _ h =>
  (walkGraph_reachable w b w.end_mem_support).symm.trans
    (walkGraph_reachable w _ (walkGraph_adj_mem w h))

theorem walkGraph_reach_start {a b : Λ} (w : (⊤ : SimpleGraph Λ).Walk a b) :
    ∀ c d, (walkGraph w).Adj c d → (walkGraph w).Reachable a c := fun _ _ h =>
  walkGraph_reachable w _ (walkGraph_adj_mem w h)

/-- **Path factorization** (`eq:path-factor`; conditional on `hstab`). -/
theorem path_factor_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {x u v z : Λ} (huv : (⊤ : SimpleGraph Λ).Adj u v) (α : (⊤ : SimpleGraph Λ).Walk x u)
    (δ : (⊤ : SimpleGraph Λ).Walk v z) (hγ : (α.append (Walk.cons huv δ)).IsPath) :
    H02.arborealProb β hβ (fun F => ∀ e ∈ (α.append (Walk.cons huv δ)).edges, e ∈ F.edgeSet) ≤
      H02.arborealProb β hβ (fun F => F.Adj u v) *
        H02.arborealProb β hβ (fun F => ∀ e ∈ α.edges, e ∈ F.edgeSet) *
        H02.arborealProb β hβ (fun F => ∀ e ∈ δ.edges, e ∈ F.edgeSet) := by
  have hne : u ≠ v := huv.ne
  have hnd := hγ.isTrail.edges_nodup
  rw [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hnd
  obtain ⟨_, ⟨hδuv, _⟩, hdis⟩ := hnd
  set A := walkGraph α
  set Bδ := walkGraph δ
  set B := edge u v ⊔ Bδ
  have hedge : ∀ e, e ∈ (edge u v).edgeSet ↔ e = s(u, v) := by
    intro e; rw [edgeSet_edge_of_ne hne, Set.mem_singleton_iff]
  -- first application: `A` and `B`, sharing `u`
  have hA : ∀ c d, A.Adj c d → A.Reachable u c := walkGraph_reach_end α
  have hB : ∀ c d, B.Adj c d → B.Reachable u c := by
    have huvB : B.Adj u v := Or.inl (by simp [edge_adj, hne])
    intro c d hcd
    rcases hcd with h | h
    · rw [edge_adj] at h
      rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact huvB.reachable
    · exact huvB.reachable.trans ((walkGraph_reach_start δ c d h).mono le_sup_right)
  have hAB : Disjoint A.edgeSet B.edgeSet := by
    rw [Set.disjoint_left]
    intro e heA heB
    rw [mem_edgeSet_walkGraph] at heA
    rw [edgeSet_sup, Set.mem_union, hedge, mem_edgeSet_walkGraph] at heB
    rcases heB with rfl | heB
    · exact hdis _ heA _ List.mem_cons_self rfl
    · exact hdis _ heA _ (List.mem_cons_of_mem _ heB) rfl
  have h1 := two_trees_of_stable hβ hβ0 hstab u A B hA hB hAB
  -- second application: `edge u v` and `Bδ`, sharing `v`
  have hA' : ∀ c d, (edge u v).Adj c d → (edge u v).Reachable v c := by
    intro c d h
    rw [edge_adj] at h
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (Adj.reachable (by simp [edge_adj, hne, hne.symm] : (edge c d).Adj d c))
    · rfl
  have hAB' : Disjoint (edge u v).edgeSet Bδ.edgeSet := by
    rw [Set.disjoint_left]
    intro e he heB
    rw [hedge] at he
    rw [mem_edgeSet_walkGraph, he] at heB
    exact hδuv heB
  have h2 := two_trees_of_stable hβ hβ0 hstab v (edge u v) Bδ hA' (walkGraph_reach_start δ) hAB'
  -- events
  have eγ : (fun F : SimpleGraph Λ => ∀ e ∈ (α.append (Walk.cons huv δ)).edges, e ∈ F.edgeSet) =
      fun F => A ⊔ B ≤ F := by
    funext F
    rw [sup_le_iff, sup_le_iff, walkGraph_le_iff, walkGraph_le_iff, edge_le_iff,
      Walk.edges_append, Walk.edges_cons]
    simp only [List.mem_append, List.mem_cons, hne, false_or]
    apply propext
    constructor
    · intro h
      exact ⟨fun e he => h e (Or.inl he), h _ (Or.inr (Or.inl rfl)),
        fun e he => h e (Or.inr (Or.inr he))⟩
    · rintro ⟨h1, h2, h3⟩ e (he | rfl | he)
      · exact h1 e he
      · exact h2
      · exact h3 e he
  have eα : (fun F : SimpleGraph Λ => ∀ e ∈ α.edges, e ∈ F.edgeSet) = fun F => A ≤ F := by
    funext F; rw [walkGraph_le_iff]
  have eδ : (fun F : SimpleGraph Λ => ∀ e ∈ δ.edges, e ∈ F.edgeSet) = fun F => Bδ ≤ F := by
    funext F; rw [walkGraph_le_iff]
  have euv : (fun F : SimpleGraph Λ => F.Adj u v) = fun F => edge u v ≤ F := by
    funext F; rw [edge_le_iff]; simp [hne]
  rw [eγ, eα, eδ, euv]
  have hA0 := H02.arborealProb_nonneg hβ hβ0 (fun F => A ≤ F)
  calc H02.arborealProb β hβ (fun F => A ⊔ B ≤ F)
      ≤ H02.arborealProb β hβ (fun F => A ≤ F) * H02.arborealProb β hβ (fun F => B ≤ F) := h1
    _ ≤ H02.arborealProb β hβ (fun F => A ≤ F) * (H02.arborealProb β hβ (fun F => edge u v ≤ F) *
          H02.arborealProb β hβ (fun F => Bδ ≤ F)) := mul_le_mul_of_nonneg_left h2 hA0
    _ = _ := by ring

end

end ArborealDecay.SimonLieb
