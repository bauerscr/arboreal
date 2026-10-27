module

public import ArborealDecay.Surgery.Crit
public import ArborealDecay.Surgery.Fibre

/-!
# The fibre sum over quotient forests

`sum_quot_core`: for a set `N₁` of edges all of which are mapped by `f` to non-loops, the weighted
sum over the sets `S ⊆ N₁` with `QuotOK f S` (and an event `Q` on the image graph) equals the sum
over forests `F'` of `Λ'` (with the event `Q`) of the product over the edges `t` of `F'` of the
total weight `∑_{e ∈ N₁, f(e) = t} g e` of the lifts of `t`.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
variable (f : Λ → Λ')

/-- The edge finset of `fromEdgeSet T` (for any `Fintype` instance on its edge set). -/
theorem edgeFinset_fromEdgeSet_eq {V : Type*} {T : Finset (Sym2 V)} (hT : ∀ t ∈ T, ¬ t.IsDiag)
    {inst : Fintype (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 V))).edgeSet} :
    @SimpleGraph.edgeFinset V (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 V))) inst = T := by
  ext t
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  exact ⟨fun h => h.1, fun h => ⟨h, hT t h⟩⟩

/-- The edges of `Λ` joining two different fibres of `f`. -/
def Ncross : Finset (Sym2 Λ) := univ.filter fun e => ¬ (Sym2.map f e).IsDiag

theorem mem_Ncross {e : Sym2 Λ} : e ∈ Ncross f ↔ ¬ (Sym2.map f e).IsDiag := by
  simp [Ncross]

theorem sum_quot_core (Q : SimpleGraph Λ' → Prop) [DecidablePred Q] (g : Sym2 Λ → ℝ) (N₁ : Finset (Sym2 Λ))
    (hN₁ : N₁ ⊆ Ncross f) :
    ∑ S ∈ N₁.powerset.filter (fun S => QuotOK f S ∧ Q (edgeQuot f S)), ∏ e ∈ S, g e =
      ∑ F' ∈ univ.filter (fun F' : SimpleGraph Λ' => F'.IsAcyclic ∧ Q F'),
        ∏ t ∈ F'.edgeFinset, ∑ e ∈ N₁.filter (fun e => Sym2.map f e = t), g e := by
  set M : Finset (Sym2 Λ') := N₁.image (Sym2.map f) with hM
  have hMnd : ∀ t ∈ M, ¬ t.IsDiag := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.1 ht
    exact (mem_Ncross f).1 (hN₁ he)
  have hfs : ∀ F' : SimpleGraph Λ', SimpleGraph.fromEdgeSet (↑F'.edgeFinset : Set (Sym2 Λ')) = F' := by
    intro F'; rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  rw [← Finset.sum_fiberwise_of_maps_to (s := N₁.powerset.filter
      (fun S => QuotOK f S ∧ Q (edgeQuot f S))) (t := M.powerset) (g := fun S => S.image (Sym2.map f))
      (by
        intro S hS
        simp only [mem_filter, mem_powerset] at hS
        exact mem_powerset.2 (image_subset_image hS.1))]
  have hinner : ∀ T ∈ M.powerset,
      ∑ S ∈ (N₁.powerset.filter (fun S => QuotOK f S ∧ Q (edgeQuot f S))).filter
        (fun S => S.image (Sym2.map f) = T), ∏ e ∈ S, g e =
      if (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 Λ'))).IsAcyclic ∧
          Q (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 Λ')))
        then ∏ t ∈ T, ∑ e ∈ N₁.filter (fun e => Sym2.map f e = t), g e else 0 := by
    intro T hT
    split_ifs with hc
    · rw [← fibre_prod (Sym2.map f) g T N₁]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext S
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨⟨hS, hq, _⟩, himg⟩
        exact ⟨hS, hq.2.1, himg⟩
      · rintro ⟨hS, hinj, himg⟩
        refine ⟨⟨hS, ⟨?_, hinj, fun e he => (mem_Ncross f).1 (hN₁ (hS he))⟩, ?_⟩, himg⟩
        · show (SimpleGraph.fromEdgeSet (↑(S.image (Sym2.map f)) : Set (Sym2 Λ'))).IsAcyclic
          rw [himg]; exact hc.1
        · show Q (SimpleGraph.fromEdgeSet (↑(S.image (Sym2.map f)) : Set (Sym2 Λ')))
          rw [himg]; exact hc.2
    · refine Finset.sum_eq_zero fun S hS => ?_
      exfalso
      simp only [mem_filter, mem_powerset] at hS
      obtain ⟨⟨_, hq, hQ⟩, himg⟩ := hS
      apply hc
      have e1 : edgeQuot f S = SimpleGraph.fromEdgeSet ↑T := by
        show SimpleGraph.fromEdgeSet (↑(S.image (Sym2.map f)) : Set (Sym2 Λ')) = _
        rw [himg]
      rw [← e1]; exact ⟨hq.1, hQ⟩
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  rw [← Finset.sum_filter_of_ne (p := fun F' : SimpleGraph Λ' => F'.edgeFinset ⊆ M)
    (s := univ.filter (fun F' : SimpleGraph Λ' => F'.IsAcyclic ∧ Q F'))]
  · refine Finset.sum_nbij' (fun T => SimpleGraph.fromEdgeSet (↑T : Set (Sym2 Λ')))
      (fun F' => F'.edgeFinset) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      simp only [mem_filter, mem_univ, true_and, mem_powerset] at hT ⊢
      rw [edgeFinset_fromEdgeSet_eq fun t ht => hMnd t (hT.1 ht)]
      exact ⟨hT.2, hT.1⟩
    · intro F' hF'
      simp only [mem_filter, mem_univ, true_and, mem_powerset] at hF' ⊢
      rw [hfs]
      exact ⟨hF'.2, hF'.1.1, hF'.1.2⟩
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      exact edgeFinset_fromEdgeSet_eq fun t ht => hMnd t (hT.1 ht)
    · intro F' _
      exact hfs F'
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      rw [edgeFinset_fromEdgeSet_eq fun t ht => hMnd t (hT.1 ht)]
  · intro F' _ hne
    have : ∀ t ∈ F'.edgeFinset, t ∈ M := by
      intro t ht
      by_contra hnt
      refine hne (Finset.prod_eq_zero ht ?_)
      refine Finset.sum_eq_zero fun e he => ?_
      exfalso
      simp only [mem_filter] at he
      exact hnt (he.2 ▸ mem_image_of_mem _ he.1)
    exact fun t ht => this t ht

end

end ArborealDecay.Surgery
