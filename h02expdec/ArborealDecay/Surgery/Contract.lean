module

public import ArborealDecay.Surgery.Bij

/-!
# Contraction of a conditioned forest

Let `A` be an acyclic graph on `Λ` whose connected components are the fibres of `f : Λ → Λ'`
(`hA : A.Reachable u v ↔ f u = f v`; for `f = c`, the component map of `A`, this holds by
`SimpleGraph.ConnectedComponent.eq`).  Then forests `F ⊇ A` correspond to forests `F/A` on `Λ'`
together with a choice of one lift (an edge of `Λ`) of each edge of `F/A`, and
`w(F) = w(A) ∏_{e ∈ F ∖ A} β_e`.  Summing over the lifts gives
`∑_{F ⊇ A} w(F) = w(A) · Z_{mapW β f}` (`contract_sum`), and more generally with an event on the
quotient forest `F/A` and with a set `P` of edges, pairwise non-parallel, that is pinned to lie in
`F` (`contract_pin_event`).
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
variable (f : Λ → Λ') {A : SimpleGraph Λ}

theorem mem_edgeSet_edgeQuot (S : Finset (Sym2 Λ)) {t : Sym2 Λ'} :
    t ∈ (edgeQuot f S).edgeSet ↔ t ∈ S.image (Sym2.map f) ∧ ¬ t.IsDiag := by
  unfold edgeQuot
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  simp [Sym2.mem_diagSet]

theorem sum_filter_iff {α : Type*} (s : Finset α) (p q : α → Prop) {i1 : DecidablePred p}
    {i2 : DecidablePred q} (h : ∀ x, p x ↔ q x) (g : α → ℝ) :
    ∑ x ∈ @Finset.filter α p i1 s, g x = ∑ x ∈ @Finset.filter α q i2 s, g x :=
  Finset.sum_congr (Finset.filter_congr fun x _ => h x) fun _ _ => rfl

/-- The edges of `Ncross` over which no pinned edge lies, together with the pinned edges. -/
def Nfree (P : Finset (Sym2 Λ)) : Finset (Sym2 Λ) :=
  (Ncross f).filter fun e => e ∈ P ∨ Sym2.map f e ∉ P.image (Sym2.map f)

theorem Nfree_subset (P : Finset (Sym2 Λ)) : Nfree f P ⊆ Ncross f := filter_subset _ _

theorem pin_equiv (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    (P : Finset (Sym2 Λ)) (hP : P ⊆ Ncross f) (hPinj : Set.InjOn (Sym2.map f) ↑P)
    (S : Finset (Sym2 Λ)) (hS : S ⊆ NA A) :
    ((A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))).IsAcyclic ∧
        ∀ p ∈ P, p ∈ (A ⊔ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 Λ))).edgeSet) ↔
      ((∀ e ∈ S, e ∈ Nfree f P) ∧ QuotOK f S ∧
        ∀ t ∈ P.image (Sym2.map f), t ∈ (edgeQuot f S).edgeSet) := by
  rw [crit f hAc hA S (fun e he => mem_NA.1 (hS he))]
  constructor
  · rintro ⟨hq, hPS⟩
    have hPS' : P ⊆ S := by
      intro p hp
      have h1 := hPS p hp
      rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 (mem_NA.1 (Ncross_subset_NA f hA (hP hp))).2
      · exact h1.1
    refine ⟨?_, hq, ?_⟩
    · intro e he
      refine mem_filter.2 ⟨(mem_Ncross f).2 (hq.2.2 e he), ?_⟩
      by_cases h : Sym2.map f e ∈ P.image (Sym2.map f)
      · left
        obtain ⟨p, hp, hpe⟩ := mem_image.1 h
        have := hq.2.1 (hPS' hp) he hpe
        rw [← this]; exact hp
      · right; exact h
    · intro t ht
      obtain ⟨p, hp, rfl⟩ := mem_image.1 ht
      rw [mem_edgeSet_edgeQuot]
      exact ⟨mem_image_of_mem _ (hPS' hp), (mem_Ncross f).1 (hP hp)⟩
  · rintro ⟨hN, hq, hπ⟩
    have hPS' : P ⊆ S := by
      intro p hp
      have h1 := hπ _ (mem_image_of_mem _ hp)
      rw [mem_edgeSet_edgeQuot] at h1
      obtain ⟨e, he, hep⟩ := mem_image.1 h1.1
      have h2 := (mem_filter.1 (hN e he)).2
      have : e ∈ P := by
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd (by rw [hep]; exact mem_image_of_mem _ hp) h2
      rw [← hPinj this hp hep]; exact he
    refine ⟨hq, ?_⟩
    intro p hp
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet]
    refine Or.inr ⟨hPS' hp, ?_⟩
    simpa using (mem_NA.1 (Ncross_subset_NA f hA (hP hp))).1

/-- **Contraction with pinned edges and a quotient event.**  `P` is a set of edges joining
different fibres, no two parallel (with the same image in `Λ'`).  Summing over forests `F ⊇ A`
containing `P` with the event `Q (F/A)`: after multiplying by the weights `(β_f)_{Sym2.map f e}`,
`e ∈ P`, of the images of the pinned edges, this equals `w(A) ∏_{e ∈ P} β_e` times the sum over
forests `F'` of the quotient containing `π(P)` with the event `Q F'`. -/
theorem contract_pin_event (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (P : Finset (Sym2 Λ)) (hP : P ⊆ Ncross f) (hPinj : Set.InjOn (Sym2.map f) ↑P)
    (Q : SimpleGraph Λ' → Prop) :
    (∏ e ∈ P, Sym2.lift ⟨mapW β f, mapW_symm hβ f⟩ (Sym2.map f e)) *
        ∑ F ∈ univ.filter (fun F : SimpleGraph Λ =>
            F.IsAcyclic ∧ A ≤ F ∧ P ⊆ F.edgeFinset ∧ Q (quotGraph f F)),
          H02.forestWeight β hβ F =
      (∏ e ∈ P, Sym2.lift ⟨β, hβ⟩ e) * H02.forestWeight β hβ A *
        ∑ F' ∈ univ.filter (fun F' : SimpleGraph Λ' =>
            F'.IsAcyclic ∧ P.image (Sym2.map f) ⊆ F'.edgeFinset ∧ Q F'),
          H02.forestWeight (mapW β f) (mapW_symm hβ f) F' := by
  have h1 := sum_forests_eq (A := A) hβ
    (fun F => P ⊆ F.edgeFinset ∧ Q (quotGraph f F))
  have core := sum_quot_core f (fun F' => P.image (Sym2.map f) ⊆ F'.edgeFinset ∧ Q F')
    (fun e => Sym2.lift ⟨β, hβ⟩ e) (Nfree f P) (Nfree_subset f P)
  beta_reduce at h1 core
  have core' := core
  have h2 : (∑ F ∈ univ.filter (fun F : SimpleGraph Λ =>
            F.IsAcyclic ∧ A ≤ F ∧ P ⊆ F.edgeFinset ∧ Q (quotGraph f F)),
          H02.forestWeight β hβ F) =
      H02.forestWeight β hβ A *
        ∑ F' ∈ univ.filter (fun F' : SimpleGraph Λ' =>
            F'.IsAcyclic ∧ P.image (Sym2.map f) ⊆ F'.edgeFinset ∧ Q F'),
          ∏ t ∈ F'.edgeFinset, ∑ e ∈ (Nfree f P).filter (fun e => Sym2.map f e = t),
            Sym2.lift ⟨β, hβ⟩ e := by
    rw [h1]
    congr 1
    refine Eq.trans ?_ core'
    refine Finset.sum_congr (Finset.ext fun S => ?_) fun _ _ => rfl
    simp only [mem_filter, mem_powerset, Finset.subset_iff, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨hS, hq, hP', hQ⟩
      have := (pin_equiv f hAc hA P hP hPinj S (fun e he => hS he)).1 ⟨hq, hP'⟩
      rw [quotGraph_sup f hA] at hQ
      exact ⟨this.1, this.2.1, this.2.2, hQ⟩
    · rintro ⟨hS, hq, hP', hQ⟩
      have hS' : S ⊆ NA A := fun e he => Ncross_subset_NA f hA (Nfree_subset f P (hS he))
      rw [quotGraph_sup f hA]
      have := (pin_equiv f hAc hA P hP hPinj S hS').2 ⟨hS, hq, hP'⟩
      exact ⟨hS', this.1, this.2, hQ⟩
  rw [h2]
  -- the algebra of the weights
  have c1 : ∀ p ∈ P, ∑ e ∈ (Nfree f P).filter (fun e => Sym2.map f e = Sym2.map f p), Sym2.lift ⟨β, hβ⟩ e =
      Sym2.lift ⟨β, hβ⟩ p := by
    intro p hp
    have : (Nfree f P).filter (fun e => Sym2.map f e = Sym2.map f p) = {p} := by
      ext e
      simp only [mem_filter, mem_singleton, Nfree]
      constructor
      · rintro ⟨⟨_, h | h⟩, he⟩
        · exact hPinj h hp he
        · exact absurd (by rw [he]; exact mem_image_of_mem _ hp) h
      · rintro rfl
        exact ⟨⟨hP hp, Or.inl hp⟩, rfl⟩
    rw [this, sum_singleton]
  have c2 : ∀ t ∉ P.image (Sym2.map f), ∑ e ∈ (Nfree f P).filter (fun e => Sym2.map f e = t), Sym2.lift ⟨β, hβ⟩ e =
      ∑ e ∈ (Ncross f).filter (fun e => Sym2.map f e = t), Sym2.lift ⟨β, hβ⟩ e := by
    intro t ht
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp only [mem_filter, Nfree]
    constructor
    · rintro ⟨⟨h, _⟩, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨⟨h, Or.inr (by rw [h2]; exact ht)⟩, h2⟩
  have c3 : ∀ p ∈ P, Sym2.lift ⟨mapW β f, mapW_symm hβ f⟩ (Sym2.map f p) =
      ∑ e ∈ (Ncross f).filter (fun e => Sym2.map f e = Sym2.map f p), Sym2.lift ⟨β, hβ⟩ e := by
    intro p hp
    have hnd := (mem_Ncross f).1 (hP hp)
    induction p using Sym2.ind with
    | h x y =>
      have hxy : f x ≠ f y := by simpa [Sym2.map_mk] using hnd
      show mapW β f (f x) (f y) = _
      rw [mapW_eq_sum f hβ hxy]
      rfl
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  -- reduce to a pointwise identity
  have hw : ∀ F' ∈ univ.filter (fun F' : SimpleGraph Λ' =>
      F'.IsAcyclic ∧ P.image (Sym2.map f) ⊆ F'.edgeFinset ∧ Q F'),
      (∏ e ∈ P, Sym2.lift ⟨mapW β f, mapW_symm hβ f⟩ (Sym2.map f e)) *
        (H02.forestWeight β hβ A * ∏ t ∈ F'.edgeFinset,
          ∑ e ∈ (Nfree f P).filter (fun e => Sym2.map f e = t), Sym2.lift ⟨β, hβ⟩ e) =
      (∏ e ∈ P, Sym2.lift ⟨β, hβ⟩ e) * H02.forestWeight β hβ A *
        H02.forestWeight (mapW β f) (mapW_symm hβ f) F' := by
    intro F' hF'
    simp only [mem_filter, mem_univ, true_and] at hF'
    rw [weight_quot f hβ]
    have hsub := Finset.prod_sdiff (f := fun t => ∑ e ∈ (Nfree f P).filter (fun e => Sym2.map f e = t),
      Sym2.lift ⟨β, hβ⟩ e) hF'.2.1
    have hsub2 := Finset.prod_sdiff (f := fun t => ∑ e ∈ (Ncross f).filter (fun e => Sym2.map f e = t),
      Sym2.lift ⟨β, hβ⟩ e) hF'.2.1
    have hrest : ∏ t ∈ F'.edgeFinset \ P.image (Sym2.map f), ∑ e ∈ (Nfree f P).filter (fun e => Sym2.map f e = t),
        Sym2.lift ⟨β, hβ⟩ e = ∏ t ∈ F'.edgeFinset \ P.image (Sym2.map f),
          ∑ e ∈ (Ncross f).filter (fun e => Sym2.map f e = t), Sym2.lift ⟨β, hβ⟩ e :=
      Finset.prod_congr rfl fun t ht => c2 t (mem_sdiff.1 ht).2
    have hP1 : ∏ t ∈ P.image (Sym2.map f), ∑ e ∈ (Nfree f P).filter (fun e => Sym2.map f e = t),
        Sym2.lift ⟨β, hβ⟩ e = ∏ e ∈ P, Sym2.lift ⟨β, hβ⟩ e := by
      rw [Finset.prod_image hPinj]
      exact Finset.prod_congr rfl c1
    have hP2 : ∏ t ∈ P.image (Sym2.map f), ∑ e ∈ (Ncross f).filter (fun e => Sym2.map f e = t),
        Sym2.lift ⟨β, hβ⟩ e = ∏ e ∈ P, Sym2.lift ⟨mapW β f, mapW_symm hβ f⟩ (Sym2.map f e) := by
      rw [Finset.prod_image hPinj]
      exact (Finset.prod_congr rfl fun p hp => (c3 p hp).symm)
    rw [← hsub, ← hsub2, hrest, hP1, ← hP2]
    ring
  refine Finset.sum_congr rfl fun F' hF' => ?_
  rw [← hw F' hF']

/-- **Contraction with an event on the quotient forest.**  For `A` acyclic with components the
fibres of `f`, and any event `Q` on forests of `Λ'`,
`∑_{F ⊇ A acyclic, Q(F/A)} w(F) = w(A) · ∑_{F' acyclic, Q F'} w_{mapW β f}(F')`. -/
theorem contract_sum_event (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (Q : SimpleGraph Λ' → Prop) :
    ∑ F ∈ univ.filter (fun F : SimpleGraph Λ => F.IsAcyclic ∧ A ≤ F ∧ Q (quotGraph f F)),
        H02.forestWeight β hβ F =
      H02.forestWeight β hβ A *
        ∑ F' ∈ univ.filter (fun F' : SimpleGraph Λ' => F'.IsAcyclic ∧ Q F'),
          H02.forestWeight (mapW β f) (mapW_symm hβ f) F' := by
  have := contract_pin_event f hAc hA hβ ∅ (empty_subset _) (by simp) Q
  simp only [prod_empty, one_mul, image_empty, empty_subset, true_and] at this
  rw [this]

/-- **Contraction of a conditioned forest.**  `∑_{F ⊇ A acyclic} w(F) = w(A) · Z_{mapW β f}`. -/
theorem contract_sum (hAc : A.IsAcyclic) (hA : ∀ u v, A.Reachable u v ↔ f u = f v)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) :
    ∑ F ∈ univ.filter (fun F : SimpleGraph Λ => F.IsAcyclic ∧ A ≤ F), H02.forestWeight β hβ F =
      H02.forestWeight β hβ A * H02.Zforest (mapW β f) (mapW_symm hβ f) := by
  have := contract_sum_event f hAc hA hβ (fun _ => True)
  simp only [and_true] at this
  rw [this]
  rfl

end

end ArborealDecay.Surgery
