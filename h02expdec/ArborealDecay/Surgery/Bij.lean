module

public import ArborealDecay.Surgery.Core

/-!
# Bijections for contraction

* forests `F ⊇ A` correspond to the edge sets `S = E(F) ∖ E(A)` (`sum_forests_eq`);
* the image graph of `A ⊔ S` is `edgeQuot f S` (`quotGraph_sup`);
* the lifted weight of a quotient edge is the sum over its lifts (`mapW_eq_sum`, `weight_quot`).
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
variable (f : Λ → Λ') {A : SimpleGraph Λ}

/-- The non-loop edges not in `A`. -/
def NA (A : SimpleGraph Λ) : Finset (Sym2 Λ) := univ.filter fun e => ¬ e.IsDiag ∧ e ∉ A.edgeSet

theorem mem_NA {e : Sym2 Λ} : e ∈ NA A ↔ ¬ e.IsDiag ∧ e ∉ A.edgeSet := by simp [NA]

theorem Ncross_subset_NA (hA : ∀ u v, A.Reachable u v ↔ f u = f v) : Ncross f ⊆ NA A := by
  intro e he
  rw [mem_Ncross] at he
  rw [mem_NA]
  refine ⟨fun h => he h.map, ?_⟩
  induction e using Sym2.ind with
  | h x y =>
    intro h
    exact he (by simpa [Sym2.map_mk] using (hA x y).1 ((SimpleGraph.mem_edgeSet A).1 h).reachable)

theorem graph_eq_sup_sdiff {F : SimpleGraph Λ} (hAF : A ≤ F) :
    A ⊔ SimpleGraph.fromEdgeSet (↑(F.edgeFinset \ A.edgeFinset) : Set (Sym2 Λ)) = F := by
  ext a b
  simp only [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Finset.coe_sdiff,
    SimpleGraph.coe_edgeFinset, Set.mem_sdiff, SimpleGraph.mem_edgeSet]
  constructor
  · rintro (h | ⟨⟨h, _⟩, _⟩)
    · exact hAF h
    · exact h
  · intro h
    by_cases hA : A.Adj a b
    · exact Or.inl hA
    · exact Or.inr ⟨⟨h, hA⟩, h.ne⟩

theorem sdiff_eq_of_subset_NA {S : Finset (Sym2 Λ)} (hS : S ⊆ NA A)
    {inst : Fintype (A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))).edgeSet} :
    @SimpleGraph.edgeFinset Λ (A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))) inst \
      A.edgeFinset = S := by
  ext e
  simp only [mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sup,
    SimpleGraph.edgeSet_fromEdgeSet, Set.mem_union, Set.mem_sdiff, Finset.mem_coe,
    Sym2.mem_diagSet]
  constructor
  · rintro ⟨h | ⟨h, _⟩, h2⟩
    · exact absurd h h2
    · exact h
  · intro h
    obtain ⟨h1, h2⟩ := mem_NA.1 (hS h)
    exact ⟨Or.inr ⟨h, h1⟩, h2⟩

theorem sum_forests_eq {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (R : SimpleGraph Λ → Prop) [DecidablePred R] :
    ∑ F ∈ univ.filter (fun F : SimpleGraph Λ => F.IsAcyclic ∧ A ≤ F ∧ R F),
        H02.forestWeight β hβ F =
      H02.forestWeight β hβ A *
        ∑ S ∈ (NA A).powerset.filter (fun S : Finset (Sym2 Λ) =>
            (A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))).IsAcyclic ∧
              R (A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ)))),
          ∏ e ∈ S, Sym2.lift ⟨β, hβ⟩ e := by
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun F => F.edgeFinset \ A.edgeFinset)
    (fun S => A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))) ?_ ?_ ?_ ?_ ?_
  · intro F hF
    simp only [mem_filter, mem_univ, true_and, mem_powerset] at hF ⊢
    have hsub : F.edgeFinset \ A.edgeFinset ⊆ NA A := by
      intro e he
      simp only [mem_sdiff, SimpleGraph.mem_edgeFinset] at he
      exact mem_NA.2 ⟨F.not_isDiag_of_mem_edgeSet he.1, he.2⟩
    refine ⟨hsub, ?_⟩
    rw [graph_eq_sup_sdiff hF.2.1]
    exact ⟨hF.1, hF.2.2⟩
  · intro S hS
    simp only [mem_filter, mem_univ, true_and, mem_powerset] at hS ⊢
    exact ⟨hS.2.1, le_sup_left, hS.2.2⟩
  · intro F hF
    simp only [mem_filter, mem_univ, true_and] at hF
    exact graph_eq_sup_sdiff hF.2.1
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    exact sdiff_eq_of_subset_NA hS.1
  · intro F hF
    simp only [mem_filter, mem_univ, true_and] at hF
    have := Finset.prod_sdiff (f := fun e => Sym2.lift ⟨β, hβ⟩ e)
      (SimpleGraph.edgeFinset_mono hF.2.1)
    unfold H02.forestWeight
    rw [← this]
    ring

theorem quotGraph_sup (hA : ∀ u v, A.Reachable u v ↔ f u = f v) (S : Finset (Sym2 Λ)) :
    quotGraph f (A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))) = edgeQuot f S := by
  ext a b
  rw [quotGraph_adj, edgeQuot_adj]
  constructor
  · rintro ⟨hab, u, v, rfl, rfl, h⟩
    refine ⟨?_, hab⟩
    rw [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj] at h
    rcases h with h | h
    · exact absurd ((hA u v).1 h.reachable) hab
    · exact mem_image.2 ⟨s(u, v), by simpa using h.1, rfl⟩
  · rintro ⟨hm, hab⟩
    obtain ⟨e, he, hea⟩ := mem_image.1 hm
    induction e using Sym2.ind with
    | h x y =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at hea
      have hxy : x ≠ y := by
        rintro rfl
        rcases hea with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first | exact hab (h1.symm.trans h2) | exact hab (h2.symm.trans h1)
      have hadj : (A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))).Adj x y := by
        rw [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
        exact Or.inr ⟨by simpa using he, hxy⟩
      refine ⟨hab, ?_⟩
      rcases hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨x, y, h1, h2, hadj⟩
      · exact ⟨y, x, h2, h1, hadj.symm⟩

theorem mapW_eq_sum {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) {a b : Λ'} (hab : a ≠ b) :
    mapW β f a b = ∑ e ∈ (Ncross f).filter (fun e => Sym2.map f e = s(a, b)),
      Sym2.lift ⟨β, hβ⟩ e := by
  unfold mapW
  simp only [hab, ite_false]
  rw [← Finset.sum_product' (univ.filter fun u => f u = a) (univ.filter fun v => f v = b)
    (fun u v => β u v)]
  refine Finset.sum_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    simp only [mem_product, mem_filter, mem_univ, true_and] at hp
    simp only [mem_filter, mem_Ncross, Sym2.map_mk, hp.1, hp.2, and_true]
    simpa using hab
  · rintro ⟨u, v⟩ hp ⟨u', v'⟩ hp' h
    simp only [mem_product, mem_filter, mem_univ, true_and] at hp hp'
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (hp.1.symm.trans hp'.2) hab
  · intro e he
    simp only [mem_filter] at he
    induction e using Sym2.ind with
    | h x y =>
      have hm := he.2
      simp only [Sym2.map_mk, Sym2.eq_iff] at hm
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(x, y), by simp [h1, h2], rfl⟩
      · exact ⟨(y, x), by simp [h1, h2], Sym2.eq_swap⟩
  · rintro ⟨u, v⟩ _
    rfl

theorem weight_quot {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (F' : SimpleGraph Λ') :
    H02.forestWeight (mapW β f) (mapW_symm hβ f) F' =
      ∏ t ∈ F'.edgeFinset, ∑ e ∈ (Ncross f).filter (fun e => Sym2.map f e = t),
        Sym2.lift ⟨β, hβ⟩ e := by
  unfold H02.forestWeight
  refine Finset.prod_congr rfl fun t ht => ?_
  have hnd := F'.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 ht)
  induction t using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using hnd
    show mapW β f a b = _
    rw [mapW_eq_sum f hβ hab]

end

end ArborealDecay.Surgery
