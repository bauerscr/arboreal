module

public import ArborealDecay.Wiring.Contract
public import ArborealDecay.Wiring.PolyProps

/-!
# The four coefficient events

For `U ∈ {S, S ∪ {a}, S ∪ {b}, S ∪ {a, b}}` (as sets of variables of `p`) the condition
"`cmp` is injective on `U`" is translated into `SepS S F` together with an event of the
quotient forest `F/S` on `Γ = G/S`; `sum_inj_eq` then expresses the corresponding coefficient of
`p` as a sum over forests of `Γ`.
-/

@[expose] public section

namespace ArborealDecay.Wiring

noncomputable section

open Finset Classical ArborealDecay.Surgery

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reachability in the quotient forest. -/
theorem reach_edgeQuot_iff {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S) (F0 : SimpleGraph V) (x y : V) :
    (edgeQuot (collapse S) F0.edgeFinset).Reachable (collapse S x) (collapse S y) ↔
      F0.Reachable x y ∨ ∃ s ∈ S, ∃ s' ∈ S, F0.Reachable x s ∧ F0.Reachable s' y := by
  rw [← reach_sup_iff (collapse S) (starA_hA hs₀) F0.edgeFinset x y, SimpleGraph.coe_edgeFinset,
    SimpleGraph.fromEdgeSet_edgeSet]
  constructor
  · exact reach_sup_cases (fun u v h => starA_mem hs₀ h)
  · rintro (h | ⟨s, hs, s', hs', h1, h2⟩)
    · exact h.mono le_sup_right
    · exact (h1.mono le_sup_right).trans ((starA_reachable hs₀ hs hs').mono le_sup_left |>.trans
        (h2.mono le_sup_right))

theorem reach_none_iff {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S) (F0 : SimpleGraph V) {a : V} (ha : a ∉ S) :
    (edgeQuot (collapse S) F0.edgeFinset).Reachable (some ⟨a, ha⟩) none ↔
      ∃ s ∈ S, F0.Reachable a s := by
  have h := reach_edgeQuot_iff hs₀ F0 a s₀
  rw [collapse_of_notMem ha, collapse_of_mem hs₀] at h
  rw [h]
  constructor
  · rintro (h | ⟨s, hs, s', _, h1, _⟩)
    · exact ⟨s₀, hs₀, h⟩
    · exact ⟨s, hs, h1⟩
  · rintro ⟨s, hs, h1⟩
    exact Or.inr ⟨s, hs, s₀, hs₀, h1, SimpleGraph.Reachable.refl _⟩

theorem reach_some_iff {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S) (F0 : SimpleGraph V) {a b : V} (ha : a ∉ S) (hb : b ∉ S)
    (hna : ¬ ∃ s ∈ S, F0.Reachable a s) :
    (edgeQuot (collapse S) F0.edgeFinset).Reachable (some ⟨a, ha⟩) (some ⟨b, hb⟩) ↔
      F0.Reachable a b := by
  have h := reach_edgeQuot_iff hs₀ F0 a b
  rw [collapse_of_notMem ha, collapse_of_notMem hb] at h
  rw [h]
  constructor
  · rintro (h | ⟨s, hs, s', _, h1, _⟩)
    · exact h
    · exact absurd ⟨s, hs, h1⟩ hna
  · exact Or.inl


/-- The variables `s_v`. -/
def US (S : Finset V) : Finset (Var S) := Finset.univ.image Sum.inr

theorem cmp_inl_zero (a b : V) (S : Finset V) (F : SimpleGraph V) :
    cmp a b S F (Sum.inl 0) = F.connectedComponentMk a := rfl

theorem cmp_inl_one (a b : V) (S : Finset V) (F : SimpleGraph V) :
    cmp a b S F (Sum.inl 1) = F.connectedComponentMk b := rfl

theorem cmp_inr (a b : V) (S : Finset V) (F : SimpleGraph V) (s : ↥S) :
    cmp a b S F (Sum.inr s) = F.connectedComponentMk s.1 := rfl

theorem injOn_US (a b : V) (S : Finset V) (F : SimpleGraph V) : Set.InjOn (cmp a b S F) ↑(US S) ↔ SepS S F := by
  constructor
  · intro h s hs s' hs' hr
    have := @h (Sum.inr ⟨s, hs⟩) (by simp [US]) (Sum.inr ⟨s', hs'⟩) (by simp [US])
      (SimpleGraph.ConnectedComponent.eq.2 hr)
    exact congrArg Subtype.val (Sum.inr_injective this)
  · intro h u hu v hv huv
    simp only [US, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hu hv
    obtain ⟨s, rfl⟩ := hu
    obtain ⟨t, rfl⟩ := hv
    exact congrArg Sum.inr (Subtype.ext (h _ s.2 _ t.2 (SimpleGraph.ConnectedComponent.eq.1 huv)))

theorem injOn_insert_inl (a b : V) (S : Finset V) (F : SimpleGraph V) (i : Fin 2) (U : Finset (Var S))
    (hi : Sum.inl i ∉ U) :
    Set.InjOn (cmp a b S F) ↑(insert (Sum.inl i) U) ↔
      Set.InjOn (cmp a b S F) ↑U ∧ ∀ u ∈ U, cmp a b S F (Sum.inl i) ≠ cmp a b S F u := by
  rw [Finset.coe_insert, Set.injOn_insert (by simpa using hi)]
  simp only [Set.mem_image, Finset.mem_coe, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu h => h2 u hu h.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu h => h2 u hu h.symm⟩

theorem inl_notMem_US (S : Finset V) (i : Fin 2) : (Sum.inl i : Var S) ∉ US S := by simp [US]

theorem injOn_Ux (a b : V) (S : Finset V) (F : SimpleGraph V) :
    Set.InjOn (cmp a b S F) ↑(insert (Sum.inl 0) (US S)) ↔
      SepS S F ∧ ∀ s ∈ S, ¬ F.Reachable a s := by
  rw [injOn_insert_inl a b S F 0 _ (inl_notMem_US S 0), injOn_US a b S]
  refine and_congr Iff.rfl ⟨fun h s hs hr => h (Sum.inr ⟨s, hs⟩) (by simp [US])
    (SimpleGraph.ConnectedComponent.eq.2 hr), fun h u hu he => ?_⟩
  simp only [US, Finset.mem_image, Finset.mem_univ, true_and] at hu
  obtain ⟨s, rfl⟩ := hu
  exact h s.1 s.2 (SimpleGraph.ConnectedComponent.eq.1 he)

theorem injOn_Uy (a b : V) (S : Finset V) (F : SimpleGraph V) :
    Set.InjOn (cmp a b S F) ↑(insert (Sum.inl 1) (US S)) ↔
      SepS S F ∧ ∀ s ∈ S, ¬ F.Reachable b s := by
  rw [injOn_insert_inl a b S F 1 _ (inl_notMem_US S 1), injOn_US a b S]
  refine and_congr Iff.rfl ⟨fun h s hs hr => h (Sum.inr ⟨s, hs⟩) (by simp [US])
    (SimpleGraph.ConnectedComponent.eq.2 hr), fun h u hu he => ?_⟩
  simp only [US, Finset.mem_image, Finset.mem_univ, true_and] at hu
  obtain ⟨s, rfl⟩ := hu
  exact h s.1 s.2 (SimpleGraph.ConnectedComponent.eq.1 he)

theorem injOn_Uxy (a b : V) (S : Finset V) (F : SimpleGraph V) :
    Set.InjOn (cmp a b S F) ↑(insert (Sum.inl 0) (insert (Sum.inl 1) (US S))) ↔
      SepS S F ∧ (∀ s ∈ S, ¬ F.Reachable a s) ∧ (∀ s ∈ S, ¬ F.Reachable b s) ∧
        ¬ F.Reachable a b := by
  have h0 : (Sum.inl 0 : Var S) ∉ insert (Sum.inl 1) (US S) := by
    simp [inl_notMem_US S 0]
  rw [injOn_insert_inl a b S F 0 _ h0, injOn_Uy a b S F]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_, h2, ?_⟩
    · intro s hs hr
      exact h3 (Sum.inr ⟨s, hs⟩) (by simp [US]) (SimpleGraph.ConnectedComponent.eq.2 hr)
    · intro hr
      exact h3 (Sum.inl 1) (by simp) (SimpleGraph.ConnectedComponent.eq.2 hr)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h3⟩, fun u hu he => ?_⟩
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact h4 (SimpleGraph.ConnectedComponent.eq.1 he)
    · simp only [US, Finset.mem_image, Finset.mem_univ, true_and] at hu
      obtain ⟨s, rfl⟩ := hu
      exact h2 s.1 s.2 (SimpleGraph.ConnectedComponent.eq.1 he)

/-- The coefficient of `p` as a sum over forests of `Γ = G/S`. -/
theorem sum_inj_eq {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S) (a b : V) {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (U : Finset (Var S))
    (Q : SimpleGraph (Option {v // v ∉ S}) → Prop)
    (hU : ∀ F : SimpleGraph V,
      Set.InjOn (cmp a b S F) ↑U ↔ (SepS S F ∧ Q (edgeQuot (collapse S) F.edgeFinset))) :
    (∑ F : SimpleGraph V with F.IsAcyclic, (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        if Set.InjOn (cmp a b S F) ↑U then 1 else 0) =
      ∑ F' : SimpleGraph (Option {v // v ∉ S}) with F'.IsAcyclic ∧ Q F',
        H02.forestWeight (mapW β (collapse S)) (mapW_symm hβ (collapse S)) F' := by
  rw [← sum_sep_eq hs₀ hβ Q, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases h : F.IsAcyclic
  · simp only [h, true_and, if_true]
    by_cases hi : Set.InjOn (cmp a b S F) ↑U
    · have := (hU F).1 hi
      simp [hi, this, H02.forestWeight]
    · have : ¬ (SepS S F ∧ Q (edgeQuot (collapse S) F.edgeFinset)) := fun h' => hi ((hU F).2 h')
      simp [hi, this]
  · simp [h]

end

end ArborealDecay.Wiring
