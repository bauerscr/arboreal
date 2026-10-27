module

public import ArborealDecay.Surgery.Contract

/-!
# Conditioning on a forest: the conditional law is the arboreal gas on the contraction

For `A` acyclic with components the fibres of `f` (e.g. `f` the component map), and `w(A) ≠ 0`:

* `condProb_adj`: `μ(e ∈ F | A ⊆ F) = (β_e / m_{[p][i]}) · μ_{G/A}([p][i] ∈ F')`, `e = pi`,
  `[p] ≠ [i]`, where `m = mapW β f` is the summed weight of the image edge;
* `condProb_adj_adj`: the same for two edges whose images are different edges of `G/A`;
* `condProb_adj_adj_parallel`: two different edges with the same image are never both present.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
variable (f : Λ → Λ') {A : SimpleGraph Λ}

/-- Conditional arboreal probability `μ(P | E) = μ(E ∧ P) / μ(E)`. -/
def condProb {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (E P : SimpleGraph Λ → Prop) : ℝ :=
  H02.arborealProb β hβ (fun F => E F ∧ P F) / H02.arborealProb β hβ E

theorem condProb_eq {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (E P : SimpleGraph Λ → Prop) [DecidablePred E] [DecidablePred P] :
    condProb hβ E P =
      (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ (E F ∧ P F), H02.forestWeight β hβ F) /
        ∑ F : SimpleGraph Λ with F.IsAcyclic ∧ E F, H02.forestWeight β hβ F := by
  unfold condProb H02.arborealProb
  rw [div_div_div_cancel_right₀ (H02.Zforest_pos hβ hβ0).ne']
  refine congrArg₂ _ ?_ ?_ <;> exact sum_filter_iff _ _ _ (fun _ => Iff.rfl) _

theorem le_mapW {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {u v : Λ} (huv : f u ≠ f v) : β u v ≤ mapW β f (f u) (f v) := by
  rw [mapW_eq_sum f hβ huv]
  have hmem : s(u, v) ∈ (Ncross f).filter (fun e => Sym2.map f e = s(f u, f v)) := by
    simp [mem_Ncross, Sym2.map_mk, huv]
  have := Finset.single_le_sum (f := fun e => Sym2.lift ⟨β, hβ⟩ e)
    (s := (Ncross f).filter (fun e => Sym2.map f e = s(f u, f v)))
    (fun e _ => by
      induction e using Sym2.ind with | h x y => exact hβ0 x y) hmem
  simpa using this

/-- A forest `F ⊇ A` cannot contain two different edges with the same image in the quotient. -/
theorem no_parallel_lifts (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {F : SimpleGraph Λ} (hF : F.IsAcyclic) (hAF : A ≤ F) {e g : Sym2 Λ}
    (he : e ∈ F.edgeSet) (hg : g ∈ F.edgeSet) (heA : e ∉ A.edgeSet) (hgA : g ∉ A.edgeSet)
    (hπ : Sym2.map f e = Sym2.map f g) : e = g := by
  have hS : (F.edgeFinset \ A.edgeFinset) ⊆ NA A := by
    intro x hx
    simp only [mem_sdiff, SimpleGraph.mem_edgeFinset] at hx
    exact mem_NA.2 ⟨F.not_isDiag_of_mem_edgeSet hx.1, hx.2⟩
  have hq := (crit f hAc hA _ (fun x hx => mem_NA.1 (hS hx))).1
    (by rw [graph_eq_sup_sdiff hAF]; exact hF)
  refine hq.2.1 ?_ ?_ hπ
  · simp [he, heA]
  · simp [hg, hgA]

/-- A forest `F ⊇ A` has no edge, other than the edges of `A`, inside a fibre. -/
theorem no_internal_edge (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {F : SimpleGraph Λ} (hF : F.IsAcyclic) (hAF : A ≤ F) {u v : Λ} (huv : F.Adj u v)
    (hAuv : ¬ A.Adj u v) : f u ≠ f v := by
  have hS : (F.edgeFinset \ A.edgeFinset) ⊆ NA A := by
    intro x hx
    simp only [mem_sdiff, SimpleGraph.mem_edgeFinset] at hx
    exact mem_NA.2 ⟨F.not_isDiag_of_mem_edgeSet hx.1, hx.2⟩
  have hq := (crit f hAc hA _ (fun x hx => mem_NA.1 (hS hx))).1
    (by rw [graph_eq_sup_sdiff hAF]; exact hF)
  have := hq.2.2 s(u, v) (by simp [huv, hAuv])
  simpa [Sym2.map_mk] using this

/-- **One edge** (product form): for `e = pi` with `[p] ≠ [i]`,
`m_{[p][i]} · ∑_{F ⊇ A, e ∈ F} w(F) = β_e · w(A) · ∑_{F' ∋ [p][i]} w(F')`. -/
theorem sum_adj_contract (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) {p i : Λ} (hpi : f p ≠ f i) :
    mapW β f (f p) (f i) *
        ∑ F ∈ univ.filter (fun F : SimpleGraph Λ => F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i),
          H02.forestWeight β hβ F =
      β p i * H02.forestWeight β hβ A *
        ∑ F' ∈ univ.filter (fun F' : SimpleGraph Λ' => F'.IsAcyclic ∧ F'.Adj (f p) (f i)),
          H02.forestWeight (mapW β f) (mapW_symm hβ f) F' := by
  have hP : ({s(p, i)} : Finset (Sym2 Λ)) ⊆ Ncross f := by
    intro e he
    rw [mem_singleton] at he
    subst he
    simp [mem_Ncross, Sym2.map_mk, hpi]
  have := contract_pin_event f hAc hA hβ {s(p, i)} hP (by simp) (fun _ => True)
  simp only [prod_singleton, Sym2.lift_mk, image_singleton, Sym2.map_mk, singleton_subset_iff,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, and_true] at this
  refine Eq.trans ?_ (this.trans ?_)
  · congr 1
  · congr 1

/-- **Two edges** (product form), with different images in the quotient. -/
theorem sum_adj_adj_contract (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) {p i q j : Λ} (hpi : f p ≠ f i)
    (hqj : f q ≠ f j) (hne : s(f p, f i) ≠ s(f q, f j)) :
    mapW β f (f p) (f i) * mapW β f (f q) (f j) *
        ∑ F ∈ univ.filter (fun F : SimpleGraph Λ =>
            F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i ∧ F.Adj q j),
          H02.forestWeight β hβ F =
      β p i * β q j * H02.forestWeight β hβ A *
        ∑ F' ∈ univ.filter (fun F' : SimpleGraph Λ' =>
            F'.IsAcyclic ∧ F'.Adj (f p) (f i) ∧ F'.Adj (f q) (f j)),
          H02.forestWeight (mapW β f) (mapW_symm hβ f) F' := by
  have hegne : s(p, i) ≠ s(q, j) := fun h => hne (by rw [← Sym2.map_mk f p i, h]; rfl)
  have hP : ({s(p, i), s(q, j)} : Finset (Sym2 Λ)) ⊆ Ncross f := by
    intro e he
    rcases mem_insert.1 he with rfl | he
    · simp [mem_Ncross, Sym2.map_mk, hpi]
    · rw [mem_singleton] at he
      subst he
      simp [mem_Ncross, Sym2.map_mk, hqj]
  have hinj : Set.InjOn (Sym2.map f) ↑({s(p, i), s(q, j)} : Finset (Sym2 Λ)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact absurd hxy hne
    · exact absurd hxy.symm hne
    · rfl
  have := contract_pin_event f hAc hA hβ {s(p, i), s(q, j)} hP hinj (fun _ => True)
  rw [Finset.prod_pair hegne, Finset.prod_pair hegne] at this
  simp only [Sym2.lift_mk, Finset.image_insert, image_singleton, Sym2.map_mk,
    Finset.insert_subset_iff, singleton_subset_iff, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, and_true] at this
  refine Eq.trans ?_ (this.trans ?_)
  · congr 1
  · congr 1

theorem forestWeight_eq_zero_of_adj {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) {p i : Λ}
    (hb : β p i = 0) {F : SimpleGraph Λ} (hF : F.Adj p i) : H02.forestWeight β hβ F = 0 := by
  unfold H02.forestWeight
  exact Finset.prod_eq_zero (i := s(p, i)) (SimpleGraph.mem_edgeFinset.2 hF) (by simpa using hb)

/-- **Conditioning on a forest, one edge.**  For `A` acyclic with `w(A) ≠ 0`, nonnegative
weights, and `e = pi` with `[p] ≠ [i]`:
`μ(e ∈ F | A ⊆ F) = (β_e / m_{[p][i]}) · μ_{G/A}([p][i] ∈ F')`, `m = mapW β f`. -/
theorem condProb_adj (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hw : H02.forestWeight β hβ A ≠ 0) {p i : Λ} (hpi : f p ≠ f i) :
    condProb hβ (fun F => A ≤ F) (fun F => F.Adj p i) =
      (β p i / mapW β f (f p) (f i)) *
        H02.arborealProb (mapW β f) (mapW_symm hβ f) (fun F' => F'.Adj (f p) (f i)) := by
  have hZ := H02.Zforest_pos (mapW_symm hβ f) (mapW_nonneg hβ0 f)
  rw [condProb_eq hβ hβ0]
  have hden := contract_sum f hAc hA hβ
  have hnum := sum_adj_contract f hAc hA hβ hpi
  unfold H02.arborealProb
  rw [hden]
  by_cases hm : mapW β f (f p) (f i) = 0
  · have hb : β p i = 0 :=
      le_antisymm (hm ▸ le_mapW f hβ hβ0 hpi) (hβ0 _ _)
    have hN : (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i,
        H02.forestWeight β hβ F) = 0 := by
      refine Finset.sum_eq_zero fun F hF => ?_
      simp only [mem_filter, mem_univ, true_and] at hF
      exact forestWeight_eq_zero_of_adj hβ hb hF.2.2
    simp [hm, hb, hN]
  · have hN : (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i,
        H02.forestWeight β hβ F) = β p i * H02.forestWeight β hβ A *
          (∑ F' : SimpleGraph Λ' with F'.IsAcyclic ∧ F'.Adj (f p) (f i),
            H02.forestWeight (mapW β f) (mapW_symm hβ f) F') / mapW β f (f p) (f i) := by
      rw [eq_div_iff hm, mul_comm]; exact hnum
    rw [hN]
    field_simp

/-- **Conditioning on a forest, two edges** with different images in `G/A`:
`μ(e, g ∈ F | A ⊆ F) = (β_e/m_e)(β_g/m_g) · μ_{G/A}(t_e, t_g ∈ F')`. -/
theorem condProb_adj_adj (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hw : H02.forestWeight β hβ A ≠ 0) {p i q j : Λ} (hpi : f p ≠ f i) (hqj : f q ≠ f j)
    (hne : s(f p, f i) ≠ s(f q, f j)) :
    condProb hβ (fun F => A ≤ F) (fun F => F.Adj p i ∧ F.Adj q j) =
      (β p i / mapW β f (f p) (f i)) * (β q j / mapW β f (f q) (f j)) *
        H02.arborealProb (mapW β f) (mapW_symm hβ f)
          (fun F' => F'.Adj (f p) (f i) ∧ F'.Adj (f q) (f j)) := by
  have hZ := H02.Zforest_pos (mapW_symm hβ f) (mapW_nonneg hβ0 f)
  rw [condProb_eq hβ hβ0]
  have hden := contract_sum f hAc hA hβ
  have hnum := sum_adj_adj_contract f hAc hA hβ hpi hqj hne
  unfold H02.arborealProb
  rw [hden]
  by_cases hm1 : mapW β f (f p) (f i) = 0
  · have hb : β p i = 0 :=
      le_antisymm (hm1 ▸ le_mapW f hβ hβ0 hpi) (hβ0 _ _)
    have hN : (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i ∧ F.Adj q j,
        H02.forestWeight β hβ F) = 0 := by
      refine Finset.sum_eq_zero fun F hF => ?_
      simp only [mem_filter, mem_univ, true_and] at hF
      exact forestWeight_eq_zero_of_adj hβ hb hF.2.2.1
    simp [hm1, hb, hN]
  by_cases hm2 : mapW β f (f q) (f j) = 0
  · have hb : β q j = 0 :=
      le_antisymm (hm2 ▸ le_mapW f hβ hβ0 hqj) (hβ0 _ _)
    have hN : (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i ∧ F.Adj q j,
        H02.forestWeight β hβ F) = 0 := by
      refine Finset.sum_eq_zero fun F hF => ?_
      simp only [mem_filter, mem_univ, true_and] at hF
      exact forestWeight_eq_zero_of_adj hβ hb hF.2.2.2
    simp [hm2, hb, hN]
  have hN : (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i ∧ F.Adj q j,
      H02.forestWeight β hβ F) = β p i * β q j * H02.forestWeight β hβ A *
        (∑ F' : SimpleGraph Λ' with F'.IsAcyclic ∧ F'.Adj (f p) (f i) ∧ F'.Adj (f q) (f j),
          H02.forestWeight (mapW β f) (mapW_symm hβ f) F') /
        (mapW β f (f p) (f i) * mapW β f (f q) (f j)) := by
    rw [eq_div_iff (mul_ne_zero hm1 hm2), mul_comm]; exact hnum
  rw [hN]
  field_simp

/-- Two different edges with the same image in `G/A` are never both present in a forest
containing `A`: the conditional probability is `0`. -/
theorem condProb_adj_adj_parallel (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {p i q j : Λ} (hpi : f p ≠ f i) (hqj : f q ≠ f j) (hπ : s(f p, f i) = s(f q, f j))
    (hne : s(p, i) ≠ s(q, j)) :
    condProb hβ (fun F => A ≤ F) (fun F => F.Adj p i ∧ F.Adj q j) = 0 := by
  rw [condProb_eq hβ hβ0]
  have : (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ A ≤ F ∧ F.Adj p i ∧ F.Adj q j,
      H02.forestWeight β hβ F) = 0 := by
    refine Finset.sum_eq_zero fun F hF => ?_
    exfalso
    simp only [mem_filter, mem_univ, true_and] at hF
    obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
    refine hne (no_parallel_lifts f hAc hA hF1 hF2 (by simpa using hF3) (by simpa using hF4)
      ?_ ?_ (by simpa [Sym2.map_mk] using hπ))
    · intro h
      exact hpi ((hA p i).1 (SimpleGraph.mem_edgeSet A |>.1 h).reachable)
    · intro h
      exact hqj ((hA q j).1 (SimpleGraph.mem_edgeSet A |>.1 h).reachable)
  rw [this, zero_div]

/-! ### The component map -/

theorem hA_components (A : SimpleGraph Λ) :
    ∀ u v, A.Reachable u v ↔ A.connectedComponentMk u = A.connectedComponentMk v :=
  fun _ _ => SimpleGraph.ConnectedComponent.eq.symm

/-- **Contraction along the component map of `A`.** -/
theorem contract_sum_components (hAc : A.IsAcyclic) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i) :
    ∑ F ∈ univ.filter (fun F : SimpleGraph Λ => F.IsAcyclic ∧ A ≤ F),
        H02.forestWeight β hβ F =
      H02.forestWeight β hβ A *
        H02.Zforest (mapW β A.connectedComponentMk) (mapW_symm hβ A.connectedComponentMk) :=
  contract_sum _ hAc (hA_components A) hβ

/-- Conditioning on `A ⊆ F`, one edge, in terms of the component map. -/
theorem condProb_adj_components (hAc : A.IsAcyclic) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hw : H02.forestWeight β hβ A ≠ 0) {p i : Λ} (hpi : ¬ A.Reachable p i) :
    condProb hβ (fun F => A ≤ F) (fun F => F.Adj p i) =
      (β p i / mapW β A.connectedComponentMk (A.connectedComponentMk p)
          (A.connectedComponentMk i)) *
        H02.arborealProb (mapW β A.connectedComponentMk) (mapW_symm hβ A.connectedComponentMk)
          (fun F' => F'.Adj (A.connectedComponentMk p) (A.connectedComponentMk i)) :=
  condProb_adj _ hAc (hA_components A) hβ hβ0 hw (fun h => hpi ((hA_components A p i).2 h))

/-- Conditioning on `A ⊆ F`, two edges, in terms of the component map. -/
theorem condProb_adj_adj_components (hAc : A.IsAcyclic) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hw : H02.forestWeight β hβ A ≠ 0) {p i q j : Λ} (hpi : ¬ A.Reachable p i)
    (hqj : ¬ A.Reachable q j)
    (hne : s(A.connectedComponentMk p, A.connectedComponentMk i) ≠
      s(A.connectedComponentMk q, A.connectedComponentMk j)) :
    condProb hβ (fun F => A ≤ F) (fun F => F.Adj p i ∧ F.Adj q j) =
      (β p i / mapW β A.connectedComponentMk (A.connectedComponentMk p)
          (A.connectedComponentMk i)) *
        (β q j / mapW β A.connectedComponentMk (A.connectedComponentMk q)
          (A.connectedComponentMk j)) *
        H02.arborealProb (mapW β A.connectedComponentMk) (mapW_symm hβ A.connectedComponentMk)
          (fun F' => F'.Adj (A.connectedComponentMk p) (A.connectedComponentMk i) ∧
            F'.Adj (A.connectedComponentMk q) (A.connectedComponentMk j)) :=
  condProb_adj_adj _ hAc (hA_components A) hβ hβ0 hw (fun h => hpi ((hA_components A p i).2 h))
    (fun h => hqj ((hA_components A q j).2 h)) hne

end

end ArborealDecay.Surgery
