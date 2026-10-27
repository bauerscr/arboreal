module

public import ArborealDecay.Forest.SingleEdge

/-!
# Vertex identification: pushed-forward weights and quotient graphs

* `mapW β f` : the weights of the graph obtained by identifying the vertices in each fibre of `f`
  (parallel edges are replaced by the sum of their weights).
* `quotGraph f F` : the image `F/f` of a graph `F`; `a ~ b` iff `a ≠ b` and some edge of `F`
  joins the fibre of `a` to the fibre of `b`.
* `edgeQuot f S` : the same for a finite set of edges.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']

/-- The pushed-forward weights: the total weight between the fibres of `a` and of `b`
(and `0` on the diagonal). -/
def mapW (β : Λ → Λ → ℝ) (f : Λ → Λ') (a b : Λ') : ℝ :=
  if a = b then 0 else ∑ u with f u = a, ∑ v with f v = b, β u v

theorem mapW_symm {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (f : Λ → Λ') (a b : Λ') :
    mapW β f a b = mapW β f b a := by
  unfold mapW
  by_cases hab : a = b
  · subst hab; rfl
  · simp only [hab, Ne.symm hab, ite_false]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => hβ _ _

theorem mapW_nonneg {β : Λ → Λ → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j) (f : Λ → Λ') (a b : Λ') :
    0 ≤ mapW β f a b := by
  unfold mapW
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hβ0 _ _

variable (f : Λ → Λ')

/-- The quotient `F/f` of a graph: `a ~ b` iff `a ≠ b` and an edge of `F` joins `f⁻¹ a` to
`f⁻¹ b`. -/
def quotGraph (F : SimpleGraph Λ) : SimpleGraph Λ' :=
  SimpleGraph.fromRel fun a b => ∃ u v, f u = a ∧ f v = b ∧ F.Adj u v

theorem quotGraph_adj (F : SimpleGraph Λ) (a b : Λ') :
    (quotGraph f F).Adj a b ↔ a ≠ b ∧ ∃ u v, f u = a ∧ f v = b ∧ F.Adj u v := by
  unfold quotGraph
  rw [SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨?_, fun h => Or.inl h⟩
  rintro (h | ⟨u, v, hu, hv, h⟩)
  · exact h
  · exact ⟨v, u, hv, hu, h.symm⟩

/-- The quotient of a finite set of edges, as a graph on `Λ'` (loops are discarded). -/
def edgeQuot (S : Finset (Sym2 Λ)) : SimpleGraph Λ' :=
  SimpleGraph.fromEdgeSet ↑(S.image (Sym2.map f))

theorem edgeQuot_adj (S : Finset (Sym2 Λ)) (a b : Λ') :
    (edgeQuot f S).Adj a b ↔ s(a, b) ∈ S.image (Sym2.map f) ∧ a ≠ b := by
  unfold edgeQuot
  rw [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe]

end

end ArborealDecay.Surgery
