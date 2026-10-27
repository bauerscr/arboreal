module

public import ArborealDecay.Surgery.Defs
public import ArborealDecay.H02.Ghost

/-!
# Acyclicity criterion for contraction

Let `A` be an acyclic graph whose connected components are the fibres of `f`
(`hA : A.Reachable u v ↔ f u = f v`).  For a finite set `S` of non-loop edges not in `A`,
`A ⊔ S` is acyclic iff `f` is injective on `S`, maps no edge of `S` to a loop, and the image
graph `edgeQuot f S` is acyclic.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
variable (f : Λ → Λ') {A : SimpleGraph Λ}

/-- Reachability in `A ⊔ S` is reachability of the images in the quotient. -/
theorem reach_sup_iff (hA : ∀ u v, A.Reachable u v ↔ f u = f v) (S : Finset (Sym2 Λ))
    (u v : Λ) :
    (A ⊔ SimpleGraph.fromEdgeSet ↑S).Reachable u v ↔ (edgeQuot f S).Reachable (f u) (f v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen, SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      rw [SimpleGraph.sup_adj] at hbc
      rcases hbc with hbc | hbc
      · have := (hA b c).1 hbc.reachable
        rw [this] at ih; exact ih
      · rw [SimpleGraph.fromEdgeSet_adj] at hbc
        by_cases hfb : f b = f c
        · rw [← hfb]; exact ih
        · refine ih.tail ?_
          rw [edgeQuot_adj]
          refine ⟨?_, hfb⟩
          have : s(f b, f c) = Sym2.map f s(b, c) := rfl
          rw [this]
          exact mem_image_of_mem _ (by simpa using hbc.1)
  · intro h
    have key : ∀ a b : Λ', Relation.ReflTransGen (edgeQuot f S).Adj a b →
        ∀ u v, f u = a → f v = b → Relation.ReflTransGen (A ⊔ SimpleGraph.fromEdgeSet ↑S).Adj u v := by
      intro a b hab
      induction hab with
      | refl =>
        intro u v hu hv
        rw [← SimpleGraph.reachable_iff_reflTransGen]
        exact ((hA u v).2 (hu.trans hv.symm)).mono le_sup_left
      | @tail b c _ hbc ih =>
        intro u v hu hv
        rw [edgeQuot_adj] at hbc
        obtain ⟨hmem, hbc'⟩ := hbc
        obtain ⟨e, heS, hec⟩ := mem_image.1 hmem
        induction e using Sym2.ind with
        | h x y =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at hec
          have hstep : ∀ x y : Λ, s(x, y) ∈ S → f x ≠ f y →
              Relation.ReflTransGen (A ⊔ SimpleGraph.fromEdgeSet ↑S).Adj x y := by
            intro x y hxy hne
            refine Relation.ReflTransGen.single ?_
            rw [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
            refine Or.inr ⟨by simpa using hxy, fun h => hne (by rw [h])⟩
          have hfin : ∀ y : Λ, f y = c → Relation.ReflTransGen
              (A ⊔ SimpleGraph.fromEdgeSet ↑S).Adj y v := by
            intro y hy
            rw [← SimpleGraph.reachable_iff_reflTransGen]
            exact ((hA y v).2 (hy.trans hv.symm)).mono le_sup_left
          rcases hec with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact (ih u x hu hx).trans ((hstep x y heS (by rw [hx, hy]; exact hbc')).trans
              (hfin y hy))
          · have heS' : s(y, x) ∈ S := by rwa [Sym2.eq_swap]
            exact (ih u y hu hy).trans ((hstep y x heS' (by rw [hx, hy]; exact hbc')).trans
              (hfin x hx))
    exact key _ _ h u v rfl rfl

theorem edge_graph_insert (S : Finset (Sym2 Λ)) (u v : Λ) :
    A ⊔ SimpleGraph.fromEdgeSet ↑(insert s(u, v) S) =
      (A ⊔ SimpleGraph.fromEdgeSet ↑S) ⊔ SimpleGraph.edge u v := by
  ext a b
  simp only [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Finset.coe_insert,
    Set.mem_insert_iff, Finset.mem_coe, SimpleGraph.edge_adj, Sym2.eq_iff]
  tauto

theorem edgeQuot_insert (S : Finset (Sym2 Λ)) (u v : Λ) :
    edgeQuot f (insert s(u, v) S) = edgeQuot f S ⊔ SimpleGraph.edge (f u) (f v) := by
  ext a b
  simp only [edgeQuot, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Finset.image_insert,
    Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, SimpleGraph.edge_adj, Sym2.eq_iff,
    Sym2.map_mk]
  tauto

/-- The acyclicity condition on the quotient side. -/
def QuotOK (S : Finset (Sym2 Λ)) : Prop :=
  (edgeQuot f S).IsAcyclic ∧ Set.InjOn (Sym2.map f) ↑S ∧ ∀ e ∈ S, ¬ (Sym2.map f e).IsDiag

theorem crit (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v) :
    ∀ S : Finset (Sym2 Λ), (∀ e ∈ S, ¬ e.IsDiag ∧ e ∉ A.edgeSet) →
      ((A ⊔ SimpleGraph.fromEdgeSet ↑S).IsAcyclic ↔ QuotOK f S) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have h1 : A ⊔ SimpleGraph.fromEdgeSet ↑(∅ : Finset (Sym2 Λ)) = A := by
      ext a b; simp
    have h2 : edgeQuot f (∅ : Finset (Sym2 Λ)) = ⊥ := by
      ext a b; simp [edgeQuot_adj]
    rw [h1]
    unfold QuotOK
    simp [h2, hAc]
  | @insert e S he ih =>
    intro hS
    have hS' : ∀ x ∈ S, ¬ x.IsDiag ∧ x ∉ A.edgeSet := fun x hx => hS x (mem_insert_of_mem hx)
    revert he hS
    refine Sym2.ind (fun u v => ?_) e
    intro he hS
    obtain ⟨hdiag, hnA⟩ := hS s(u, v) (mem_insert_self _ _)
    have huv : u ≠ v := by simpa using hdiag
    have hnA' : ¬ A.Adj u v := by simpa using hnA
    have hna : ¬ (A ⊔ SimpleGraph.fromEdgeSet ↑S).Adj u v := by
      rw [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
      rintro (h | h)
      · exact hnA' h
      · exact he (by simpa using h.1)
    rw [edge_graph_insert, H02.acyclic_sup_edge_iff huv hna, reach_sup_iff f hA, ih hS']
    have hmem : ∀ a b : Λ', s(a, b) ∈ S.image (Sym2.map f) → a ≠ b →
        (edgeQuot f S).Reachable a b := fun a b h hab =>
      (SimpleGraph.Adj.reachable ((edgeQuot_adj f S a b).2 ⟨h, hab⟩))
    constructor
    · rintro ⟨hC, hnr⟩
      have hfuv : f u ≠ f v := fun h => hnr (h ▸ SimpleGraph.Reachable.refl _)
      have hnotimg : s(f u, f v) ∉ S.image (Sym2.map f) := fun h => hnr (hmem _ _ h hfuv)
      have hnadj : ¬ (edgeQuot f S).Adj (f u) (f v) := fun h => hnotimg ((edgeQuot_adj f S _ _).1 h).1
      refine ⟨?_, ?_, ?_⟩
      · rw [edgeQuot_insert, H02.acyclic_sup_edge_iff hfuv hnadj]
        exact ⟨hC.1, hnr⟩
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert (by simpa using he)).2 ⟨hC.2.1, ?_⟩
        rintro ⟨x, hx, hxe⟩
        apply hnotimg
        have : Sym2.map f x ∈ S.image (Sym2.map f) := mem_image_of_mem _ (by simpa using hx)
        rwa [hxe] at this
      · intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · simpa [Sym2.map_mk] using hfuv
        · exact hC.2.2 x hx
    · intro hQ
      have hQS : QuotOK f S := by
        refine ⟨?_, ?_, fun x hx => hQ.2.2 x (mem_insert_of_mem hx)⟩
        · refine hQ.1.anti ?_
          rw [edgeQuot_insert]; exact le_sup_left
        · exact hQ.2.1.mono (by simp)
      refine ⟨hQS, fun hr => ?_⟩
      have hfuv : f u ≠ f v := by
        have := hQ.2.2 s(u, v) (mem_insert_self _ _)
        simpa [Sym2.map_mk] using this
      have hac := hQ.1
      rw [edgeQuot_insert] at hac
      rcases (SimpleGraph.isAcyclic_sup_fromEdgeSet_iff.1 hac).2 hr with h | h
      · exact hfuv h
      · obtain ⟨hm, _⟩ := (edgeQuot_adj f S _ _).1 h
        obtain ⟨x, hx, hxe⟩ := mem_image.1 hm
        have := hQ.2.1 (by simp [hx] : x ∈ (↑(insert s(u, v) S) : Set (Sym2 Λ)))
          (by simp : s(u, v) ∈ (↑(insert s(u, v) S) : Set (Sym2 Λ))) (by simpa [Sym2.map_mk] using hxe)
        exact he (this ▸ hx)

end

end ArborealDecay.Surgery
