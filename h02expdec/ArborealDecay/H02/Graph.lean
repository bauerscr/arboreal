module

public import Mathlib

/-!
# Combinatorial lemmas on forests
-/

@[expose] public section

namespace H02

open Finset

set_option linter.unusedSectionVars false

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `S` is acyclic and no two distinct vertices of `R` lie in the same component of `S`. -/
def Good (S : SimpleGraph Λ) (R : Finset Λ) : Prop :=
  S.IsAcyclic ∧ ∀ x ∈ R, ∀ y ∈ R, S.Reachable x y → x = y

theorem good_empty_iff (S : SimpleGraph Λ) (v : Λ) : Good S ∅ ↔ Good S {v} := by
  simp [Good]

theorem not_good_of_adj {S : SimpleGraph Λ} {R : Finset Λ} {v w : Λ} (hv : v ∈ R) (hw : w ∈ R)
    (h : S.Adj v w) : ¬Good S R := by
  exact fun hg => S.ne_of_adj h (hg.2 v hv w hw h.reachable)

theorem reachable_sup_edge {G : SimpleGraph Λ} {v w x y : Λ}
    (h : (G ⊔ SimpleGraph.edge v w).Reachable x y) :
    G.Reachable x y ∨ (G.Reachable x v ∧ G.Reachable w y) ∨
      (G.Reachable x w ∧ G.Reachable v y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl SimpleGraph.Reachable.rfl
  | @cons a b c hadj p ih =>
    rcases (SimpleGraph.sup_adj _ _ _ _).1 hadj with hG | hE
    · have hab := hG.reachable
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hab.trans h1)
      · exact Or.inr (Or.inl ⟨hab.trans h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hab.trans h1, h2⟩)
    · rw [SimpleGraph.edge_adj] at hE
      rcases hE.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h1 | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.rfl, h1⟩)
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.rfl, h2⟩)
        · exact Or.inl h2
      · rcases ih with h1 | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.rfl, h1⟩)
        · exact Or.inl h2
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.rfl, h2⟩)

theorem deleteEdges_sup_edge {S : SimpleGraph Λ} {v w : Λ} (h : S.Adj v w) :
    S.deleteEdges {s(v, w)} ⊔ SimpleGraph.edge v w = S := by
  ext a b
  simp only [SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
    SimpleGraph.edge_adj, Sym2.eq_iff]
  constructor
  · rintro (⟨hab, _⟩ | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
    · exact hab
    · exact h
    · exact h.symm
  · intro hab
    by_cases hc : (a = v ∧ b = w) ∨ (a = w ∧ b = v)
    · exact Or.inr ⟨hc, S.ne_of_adj hab⟩
    · exact Or.inl ⟨hab, hc⟩

theorem good_iff_deleteEdges {S : SimpleGraph Λ} {R : Finset Λ} {v w : Λ} (hv : v ∈ R)
    (hw : w ∉ R) (h : S.Adj v w) :
    Good S R ↔ Good (S.deleteEdges {s(v, w)}) (insert w R) := by
  set G := S.deleteEdges {s(v, w)} with hGdef
  have hS : G ⊔ SimpleGraph.edge v w = S := deleteEdges_sup_edge h
  have hvw : v ≠ w := S.ne_of_adj h
  have hnadj : ¬G.Adj v w := by simp [hGdef]
  have hle : G ≤ S := SimpleGraph.deleteEdges_le _
  have hacyc : S.IsAcyclic ↔ G.IsAcyclic ∧ ¬G.Reachable v w := by
    rw [← hS, SimpleGraph.isAcyclic_sup_fromEdgeSet_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun hr => (h2 hr).elim hvw hnadj⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun hr => (h2 hr).elim⟩
  have hSreach : ∀ x y, S.Reachable x y → G.Reachable x y ∨
      (G.Reachable x v ∧ G.Reachable w y) ∨ (G.Reachable x w ∧ G.Reachable v y) := by
    intro x y hxy; rw [← hS] at hxy; exact reachable_sup_edge hxy
  constructor
  · rintro ⟨hA, hR⟩
    obtain ⟨hGA, hnr⟩ := hacyc.1 hA
    refine ⟨hGA, fun x hx y hy hxy => ?_⟩
    rw [mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd (hxy.symm.mono hle |>.trans h.symm.reachable |>.symm |> fun r =>
        (hR v hv y hy r) ▸ hxy.symm) hnr
    · exact absurd ((hxy.mono hle |>.trans h.symm.reachable) |> fun r =>
        (hR x hx v hv r) ▸ hxy) hnr
    · exact hR x hx y hy (hxy.mono hle)
  · rintro ⟨hGA, hR⟩
    have hnr : ¬G.Reachable v w := fun r =>
      hvw (hR v (mem_insert_of_mem hv) w (mem_insert_self w R) r)
    refine ⟨hacyc.2 ⟨hGA, hnr⟩, fun x hx y hy hxy => ?_⟩
    have hx' : x ∈ insert w R := mem_insert_of_mem hx
    have hy' : y ∈ insert w R := mem_insert_of_mem hy
    rcases hSreach x y hxy with h1 | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hR x hx' y hy' h1
    · exact absurd ((hR w (mem_insert_self w R) y hy' h2) ▸ hy) hw
    · exact absurd ((hR x hx' w (mem_insert_self w R) h1) ▸ hx) hw

theorem good_iff_erase {S : SimpleGraph Λ} {R : Finset Λ} {v : Λ} (hv : v ∈ R)
    (hiso : ∀ w, ¬S.Adj v w) : Good S R ↔ Good S (R.erase v) := by
  have key : ∀ y, S.Reachable v y → v = y := by
    rintro y ⟨p⟩
    cases p with
    | nil => rfl
    | cons ha _ => exact absurd ha (hiso _)
  refine ⟨fun hg => ⟨hg.1, fun x hx y hy => hg.2 x (mem_of_mem_erase hx) y
    (mem_of_mem_erase hy)⟩, fun hg => ⟨hg.1, fun x hx y hy hxy => ?_⟩⟩
  by_cases hxv : x = v
  · subst hxv; exact key y hxy
  by_cases hyv : y = v
  · subst hyv; exact (key x hxy.symm).symm
  exact hg.2 x (mem_erase.2 ⟨hxv, hx⟩) y (mem_erase.2 ⟨hyv, hy⟩) hxy

open Classical in
theorem sum_injOn_aux {κ : Type*} [Fintype κ] [DecidableEq κ] (f : Λ → κ) (h : Λ → ℝ)
    (s : Finset Λ) :
    ∑ R ∈ s.powerset, (if Set.InjOn f (R : Set Λ) then ∏ i ∈ R, h i else 0) =
      ∏ c : κ, (1 + ∑ i ∈ s with f i = c, h i) := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  set s0 := s.erase a with hs0
  have has0 : a ∉ s0 := notMem_erase a s
  have hs : s = insert a s0 := (insert_erase ha).symm
  set s1 := s0.filter (fun i => f i ≠ f a) with hs1
  have ih0 := ih s0 (erase_ssubset ha)
  have ih1 := ih s1 (Finset.ssubset_of_subset_of_ssubset (filter_subset _ _) (erase_ssubset ha))
  have hF : ∀ t ∈ s0.powerset,
      (if Set.InjOn f ((insert a t : Finset Λ) : Set Λ) then ∏ i ∈ insert a t, h i else 0) =
        if t ⊆ s1 then h a * (if Set.InjOn f (t : Set Λ) then ∏ i ∈ t, h i else 0) else 0 := by
    intro t ht
    rw [mem_powerset] at ht
    have hat : a ∉ t := fun h' => has0 (ht h')
    have e : t ⊆ s1 ↔ f a ∉ f '' (t : Set Λ) := by
      constructor
      · rintro hts ⟨x, hx, hfx⟩; exact (mem_filter.1 (hts hx)).2 hfx
      · intro hn x hx; exact mem_filter.2 ⟨ht hx, fun hfx => hn ⟨x, hx, hfx⟩⟩
    have hinj : Set.InjOn f ((insert a t : Finset Λ) : Set Λ) ↔
        Set.InjOn f (t : Set Λ) ∧ t ⊆ s1 := by
      rw [coe_insert, Set.injOn_insert (by simpa using hat), e]
    rw [prod_insert hat]
    by_cases h1 : Set.InjOn f (t : Set Λ) <;> by_cases h2 : t ⊆ s1
    · rw [if_pos (hinj.2 ⟨h1, h2⟩), if_pos h2, if_pos h1]
    · rw [if_neg (fun hh => h2 (hinj.1 hh).2), if_neg h2]
    · rw [if_neg (fun hh => h1 (hinj.1 hh).1), if_pos h2, if_neg h1, mul_zero]
    · rw [if_neg (fun hh => h2 (hinj.1 hh).2), if_neg h2]
  rw [hs, sum_powerset_insert has0, ih0, sum_congr rfl hF,
    ← sum_subset (powerset_mono.2 (filter_subset (fun i => f i ≠ f a) s0))]
  swap
  · intro t _ ht
    rw [mem_powerset] at ht
    rw [if_neg ht]
  rw [sum_congr rfl (fun t ht => if_pos (mem_powerset.1 ht)), ← mul_sum, ih1]
  have hc1 : ∀ c, ∑ i ∈ insert a s0 with f i = c, h i =
      (if f a = c then h a else 0) + ∑ i ∈ s0 with f i = c, h i := by
    intro c
    rw [filter_insert]
    split_ifs with hc
    · rw [sum_insert (fun hm => has0 (mem_filter.1 hm).1)]
    · rw [zero_add]
  have hc2 : ∀ c, c ≠ f a → ∑ i ∈ s1 with f i = c, h i = ∑ i ∈ s0 with f i = c, h i := by
    intro c hc
    rw [hs1, filter_filter]
    congr 1
    ext i
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, fun h4 => hc (h3 ▸ h4), h3⟩
  have hc3 : ∑ i ∈ s1 with f i = f a, h i = 0 := by
    rw [hs1, filter_filter]
    apply sum_eq_zero
    intro i hi
    simp only [mem_filter] at hi
    exact absurd hi.2.2 hi.2.1
  simp_rw [hc1]
  rw [Fintype.prod_eq_mul_prod_compl (f a)
    (fun c => 1 + ((if f a = c then h a else 0) + ∑ i ∈ s0 with f i = c, h i)),
    Fintype.prod_eq_mul_prod_compl (f a) (fun c => 1 + ∑ i ∈ s0 with f i = c, h i),
    Fintype.prod_eq_mul_prod_compl (f a) (fun c => 1 + ∑ i ∈ s1 with f i = c, h i), hc3]
  have hrest : ∏ c ∈ {f a}ᶜ, (1 + ((if f a = c then h a else 0) + ∑ i ∈ s0 with f i = c, h i)) =
      ∏ c ∈ {f a}ᶜ, (1 + ∑ i ∈ s0 with f i = c, h i) := by
    apply prod_congr rfl
    intro c hc
    have hc' : f a ≠ c := fun e => by simp [e] at hc
    rw [if_neg hc', zero_add]
  have hrest' : ∏ c ∈ {f a}ᶜ, (1 + ∑ i ∈ s1 with f i = c, h i) =
      ∏ c ∈ {f a}ᶜ, (1 + ∑ i ∈ s0 with f i = c, h i) := by
    apply prod_congr rfl
    intro c hc
    have hc' : c ≠ f a := fun e => by simp [e] at hc
    rw [hc2 c hc']
  rw [hrest, hrest', if_pos rfl]
  ring

theorem sum_injOn {κ : Type*} [Fintype κ] [DecidableEq κ] (f : Λ → κ) (h : Λ → ℝ)
    [DecidablePred fun R : Finset Λ => Set.InjOn f R] :
    ∑ R ∈ (univ : Finset Λ).powerset, (if Set.InjOn f R then ∏ i ∈ R, h i else 0) =
      ∏ c : κ, (1 + ∑ i with f i = c, h i) := by
  classical
  rw [← sum_injOn_aux f h univ]
  refine sum_congr rfl fun R _ => ?_
  congr 1

theorem sum_good (S : SimpleGraph Λ) [Fintype S.ConnectedComponent]
    [DecidableEq S.ConnectedComponent] [DecidablePred (Good S)] [Decidable S.IsAcyclic]
    (h : Λ → ℝ) :
    ∑ R ∈ (univ : Finset Λ).powerset, (if Good S R then ∏ i ∈ R, h i else 0) =
      if S.IsAcyclic then
        ∏ T : S.ConnectedComponent, (1 + ∑ i with S.connectedComponentMk i = T, h i)
      else 0 := by
  classical
  by_cases hA : S.IsAcyclic
  · rw [if_pos hA, ← sum_injOn S.connectedComponentMk h]
    refine sum_congr rfl fun R _ => ?_
    have key : Good S R ↔ Set.InjOn S.connectedComponentMk (R : Set Λ) :=
      ⟨fun hg x hx y hy hxy => hg.2 x hx y hy (SimpleGraph.ConnectedComponent.eq.1 hxy),
        fun hi => ⟨hA, fun x hx y hy hr => hi hx hy (SimpleGraph.ConnectedComponent.eq.2 hr)⟩⟩
    by_cases hg : Good S R
    · rw [if_pos hg, if_pos (key.1 hg)]
    · rw [if_neg hg, if_neg (mt key.2 hg)]
  · rw [if_neg hA]
    exact sum_eq_zero fun R _ => if_neg fun hg => hA hg.1

theorem edgeFinset_eq_of {G : SimpleGraph Λ} {inst : Fintype G.edgeSet} {t : Finset (Sym2 Λ)}
    (h : ∀ e, e ∈ G.edgeSet ↔ e ∈ t) : @SimpleGraph.edgeFinset _ G inst = t := by
  ext e; rw [SimpleGraph.mem_edgeFinset]; exact h e

theorem sum_edgeFinset_powerset {M : Type*} [AddCommMonoid M] [DecidableRel (⊤ : SimpleGraph Λ).Adj]
    [∀ G : SimpleGraph Λ, DecidableRel G.Adj] (f : Finset (Sym2 Λ) → M) :
    ∑ t ∈ (⊤ : SimpleGraph Λ).edgeFinset.powerset, f t = ∑ G : SimpleGraph Λ, f G.edgeFinset := by
  have hmem : ∀ t ∈ (⊤ : SimpleGraph Λ).edgeFinset.powerset, ∀ e,
      e ∈ (SimpleGraph.fromEdgeSet (t : Set (Sym2 Λ))).edgeSet ↔ e ∈ t := by
    intro t ht e
    rw [mem_powerset] at ht
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · exact fun he => he.1
    · intro he
      refine ⟨he, ?_⟩
      have := ht he
      rw [SimpleGraph.mem_edgeFinset] at this
      exact (⊤ : SimpleGraph Λ).not_isDiag_of_mem_edgeSet this
  refine Finset.sum_nbij' (fun t => SimpleGraph.fromEdgeSet (t : Set (Sym2 Λ)))
    (fun G => G.edgeFinset) (fun _ _ => mem_univ _) ?_
    (fun t ht => edgeFinset_eq_of (hmem t ht)) ?_ ?_
  · intro G _
    rw [mem_powerset]
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono le_top he
  · intro G _
    ext a b
    simp
  · intro t ht
    rw [edgeFinset_eq_of (hmem t ht)]

theorem sum_sum_eq_two_nsmul {M : Type*} [AddCommMonoid M] [DecidableRel (⊤ : SimpleGraph Λ).Adj]
    (g : Λ → Λ → M) (hg : ∀ i j, g i j = g j i) (hd : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = 2 • ∑ e ∈ (⊤ : SimpleGraph Λ).edgeFinset, Sym2.lift ⟨g, hg⟩ e := by
  classical
  have hfib : ∀ e : Sym2 Λ, ∑ p ∈ (univ ×ˢ univ).filter (fun p : Λ × Λ => s(p.1, p.2) = e),
      g p.1 p.2 = if e.IsDiag then 0 else 2 • Sym2.lift ⟨g, hg⟩ e := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
    by_cases hab : a = b
    · subst hab
      have : (univ ×ˢ univ).filter (fun p : Λ × Λ => s(p.1, p.2) = s(a, a)) = {(a, a)} := by
        ext ⟨x, y⟩; simp
      rw [this, sum_singleton, if_pos (Sym2.mk_isDiag_iff.2 rfl), hd]
    · have : (univ ×ˢ univ).filter (fun p : Λ × Λ => s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩; simp
      have hne : (a, b) ≠ (b, a) := fun e => hab (Prod.mk.inj e).1
      rw [this, sum_pair hne, if_neg (fun h' => hab (Sym2.mk_isDiag_iff.1 h')), Sym2.lift_mk,
        hg b a, two_nsmul]
  have htop : (⊤ : SimpleGraph Λ).edgeFinset = univ.filter (fun e : Sym2 Λ => ¬e.IsDiag) :=
    edgeFinset_eq_of fun e => by simp [SimpleGraph.edgeSet_top]
  rw [← Finset.sum_product' univ univ g,
    ← Finset.sum_fiberwise_of_maps_to (g := fun p : Λ × Λ => s(p.1, p.2)) (t := univ)
      (fun _ _ => mem_univ _), sum_congr rfl (fun e _ => hfib e), htop, sum_filter, smul_sum]
  refine sum_congr rfl fun e _ => ?_
  by_cases he : e.IsDiag <;> simp [he]

end H02

end
