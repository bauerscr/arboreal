module

public import ArborealDecay.MatrixForest.Laplacian
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Rooted parent functions versus forests with one root per tree

A rooted parent function `f : V → Option V` (`MatrixForest.IsRooted`) determines the forest
`parentGraph f` (edges `{i, j}` with `f i = some j`) and the root set `roots f`
(`f i = none`). This file proves that `f ↦ (parentGraph f, roots f)` is a bijection onto the pairs
`(F, S)` with `F` acyclic and `S` meeting every connected component of `F` exactly once
(`MatrixForest.IsTransversal`), and deduces the forest form of the rooted expansion:

* `MatrixForest.sum_isRooted_eq_sum_isAcyclic`:
  `∑_{f rooted} ∏_i c_i(f i) = ∑_{F acyclic} ∏_{e ∈ F} w_e ∏_{T ∈ comp F} ∑_{i ∈ T} x_i`
  for symmetric `w`.
-/

@[expose] public section

namespace MatrixForest

open Finset SimpleGraph Relation

variable {V : Type*}

/-- `Up f a b`: `b` is the parent of `a`. -/
abbrev Up (f : V → Option V) (a b : V) : Prop := f a = some b

/-- The forest of a parent function: `{a, b}` is an edge iff `b` is the parent of `a` or
vice versa. -/
def parentGraph (f : V → Option V) : SimpleGraph V := SimpleGraph.fromRel (Up f)

theorem parentGraph_adj (f : V → Option V) (a b : V) :
    (parentGraph f).Adj a b ↔ a ≠ b ∧ (f a = some b ∨ f b = some a) :=
  fromRel_adj _ a b

/-- The roots of a parent function. -/
def roots [Fintype V] (f : V → Option V) : Finset V := {i | f i = none}

theorem mem_roots [Fintype V] {f : V → Option V} {i : V} : i ∈ roots f ↔ f i = none := by
  simp [roots]

/-- `S` meets every connected component of `F` in exactly one vertex. -/
def IsTransversal (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ i, ∃! s, s ∈ S ∧ F.Reachable i s

theorem wellFounded_irrefl {α : Type*} {r : α → α → Prop} (h : WellFounded r) (a : α) :
    ¬r a a :=
  h.induction (C := fun a => ¬r a a) a fun _ ih ha => ih _ ha ha

/-- Transport of a property along reachability, when it is preserved by adjacency. -/
theorem reachable_transport {G : SimpleGraph V} (P : V → Prop)
    (hP : ∀ a b, G.Adj a b → P a → P b) {a b : V} (h : G.Reachable a b) (ha : P a) : P b := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hP _ _ hbc ih

theorem reflTransGen_up_iff {f : V → Option V} {t a b : V} (hab : f a = some b) (hat : a ≠ t) :
    ReflTransGen (Up f) a t ↔ ReflTransGen (Up f) b t := by
  refine ⟨fun h => ?_, fun h => .head hab h⟩
  rcases h.cases_head with h | ⟨c, hc, hct⟩
  · exact absurd h hat
  · have : c = b := Option.some.inj (hc.symm.trans hab)
    exact this ▸ hct

theorem eq_of_reflTransGen_up_of_root {f : V → Option V} {s b : V} (hs : f s = none)
    (h : ReflTransGen (Up f) s b) : b = s := by
  rcases h.cases_head with h | ⟨c, hc, _⟩
  · exact h.symm
  · simp [Up, hs] at hc

namespace IsRooted

variable {f : V → Option V}

theorem not_transGen (hf : IsRooted f) (a : V) : ¬TransGen (Up f) a a := fun h =>
  wellFounded_irrefl hf.transGen a ((transGen_swap (r := fun b a => f a = some b) (a := a) (b := a)).1 h)

theorem ne_of_up (hf : IsRooted f) {a b : V} (h : f a = some b) : a ≠ b := by
  rintro rfl
  exact hf.not_transGen a (.single h)

theorem exists_root (hf : IsRooted f) (a : V) :
    ∃ s, ReflTransGen (Up f) a s ∧ f s = none := by
  refine hf.induction (C := fun a => ∃ s, ReflTransGen (Up f) a s ∧ f s = none) a
    fun a ih => ?_
  rcases h : f a with _ | b
  · exact ⟨a, .refl, h⟩
  · obtain ⟨s, hbs, hs⟩ := ih b h
    exact ⟨s, .head h hbs, hs⟩

theorem adj_of_up (hf : IsRooted f) {a b : V} (h : f a = some b) : (parentGraph f).Adj a b :=
  (parentGraph_adj f a b).2 ⟨hf.ne_of_up h, Or.inl h⟩

theorem reachable_of_reflTransGen (hf : IsRooted f) {a b : V} (h : ReflTransGen (Up f) a b) :
    (parentGraph f).Reachable a b := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hf.adj_of_up hbc).reachable

/-- The parent forest of a rooted parent function is acyclic. -/
theorem isAcyclic_parentGraph (hf : IsRooted f) : (parentGraph f).IsAcyclic := by
  have key : ∀ v w, f v = some w → (parentGraph f).IsBridge s(v, w) := by
    intro v w hvw
    rw [isBridge_iff]
    intro hr
    refine hf.not_transGen v (.head' hvw (reachable_transport
      (G := (parentGraph f).deleteEdges {s(v, w)}) (fun a => ReflTransGen (Up f) a v) ?_ hr .refl))
    intro a b hab ha
    rw [deleteEdges_adj, parentGraph_adj] at hab
    obtain ⟨⟨_, h | h⟩, hnot⟩ := hab
    · have hav : a ≠ v := by
        rintro rfl
        have : b = w := Option.some.inj (h.symm.trans hvw)
        exact hnot (by simp [this])
      exact (reflTransGen_up_iff h hav).1 ha
    · exact .head h ha
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w hadj
  rw [parentGraph_adj] at hadj
  rcases hadj.2 with h | h
  · exact key v w h
  · rw [Sym2.eq_swap]; exact key w v h

/-- The roots of a rooted parent function meet every tree of its forest exactly once. -/
theorem isTransversal_roots [Fintype V] (hf : IsRooted f) :
    IsTransversal (parentGraph f) (roots f) := by
  intro i
  obtain ⟨s, his, hs⟩ := hf.exists_root i
  refine ⟨s, ⟨mem_roots.2 hs, hf.reachable_of_reflTransGen his⟩, ?_⟩
  rintro s' ⟨hs', hr'⟩
  rw [mem_roots] at hs'
  have hss' : (parentGraph f).Reachable s s' := (hf.reachable_of_reflTransGen his).symm.trans hr'
  refine (eq_of_reflTransGen_up_of_root hs' (reachable_transport
    (fun a => ReflTransGen (Up f) a s) ?_ hss' .refl)).symm
  intro a b hab ha
  rw [parentGraph_adj] at hab
  rcases hab.2 with h | h
  · exact (reflTransGen_up_iff h (by rintro rfl; simp [hs] at h)).1 ha
  · exact .head h ha

theorem reachable_deleteEdges (hf : IsRooted f) {i p : V} (hfi : f i = some p) {a : V}
    (h : ReflTransGen (Up f) p a) :
    ((parentGraph f).deleteEdges {s(i, p)}).Reachable p a := by
  induction h with
  | refl => rfl
  | @tail a b hpa hab ih =>
    refine ih.trans (Adj.reachable ?_)
    rw [deleteEdges_adj]
    refine ⟨hf.adj_of_up hab, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hf.not_transGen _ (.head' hab hpa)
    · exact hf.not_transGen _ (.head hab (.single hfi))

/-- A rooted parent function is determined by its forest and its roots. -/
theorem eq_of_parentGraph_eq [Fintype V] {g : V → Option V} (hf : IsRooted f)
    (_hg : IsRooted g) (hF : parentGraph f = parentGraph g) (hS : roots f = roots g) : f = g := by
  have hroot : ∀ i, f i = none ↔ g i = none := fun i => by
    rw [← mem_roots, hS, mem_roots]
  funext i
  rcases hfi : f i with _ | p
  · exact ((hroot i).1 hfi).symm
  rcases hgi : g i with _ | q
  · exact absurd ((hroot i).2 hgi) (by simp [hfi])
  have hadj : (parentGraph g).Adj i p := hF ▸ hf.adj_of_up hfi
  rw [parentGraph_adj] at hadj
  rcases hadj.2 with h | h
  · exact (hgi.symm.trans h).symm
  exfalso
  obtain ⟨s, hps, hs⟩ := hf.exists_root p
  have hreach := hf.reachable_deleteEdges hfi hps
  rw [hF] at hreach
  have hsp := reachable_transport (G := (parentGraph g).deleteEdges {s(i, p)})
    (fun a => ReflTransGen (Up g) a p) ?_ hreach .refl
  · have hgs : g s = none := (hroot s).1 hs
    have := eq_of_reflTransGen_up_of_root hgs hsp
    subst this
    rw [hgs] at h
    cases h
  · intro a b hab ha
    rw [deleteEdges_adj, parentGraph_adj] at hab
    obtain ⟨⟨_, h1 | h1⟩, hnot⟩ := hab
    · have hap : a ≠ p := by
        rintro rfl
        have : b = i := Option.some.inj (h1.symm.trans h)
        exact hnot (by simp [this, Sym2.eq_swap])
      exact (reflTransGen_up_iff h1 hap).1 ha
    · exact .head h1 ha

end IsRooted

/-- Every acyclic graph with a transversal of its components is the parent forest of a rooted
parent function with that root set (orient every edge towards the root of its tree). -/
theorem exists_isRooted_of_isAcyclic [Fintype V] {F : SimpleGraph V} (hF : F.IsAcyclic)
    {S : Finset V} (hS : IsTransversal F S) :
    ∃ f : V → Option V, IsRooted f ∧ parentGraph f = F ∧ roots f = S := by
  classical
  choose r hr hru using hS
  have hrr : ∀ i j, F.Reachable i j → r i = r j := fun i j h =>
    (hru i (r j) ⟨(hr j).1, h.trans (hr j).2⟩).symm
  have hrS : ∀ i ∈ S, r i = i := fun i hi => (hru i i ⟨hi, .refl _⟩).symm
  have hrne : ∀ i, i ∉ S → r i ≠ i := fun i hi h => hi (h ▸ (hr i).1)
  let d : V → ℕ := fun i => F.dist (r i) i
  have hpath : ∀ i, ∃ p : F.Walk (r i) i, p.IsPath ∧ p.length = d i := fun i =>
    (hr i).2.symm.exists_path_of_dist
  choose P hPp hPl using hpath
  have hnil : ∀ i, i ∉ S → ¬(P i).Nil := fun i hi => Walk.not_nil_of_ne (hrne i hi)
  have hadjP : ∀ i, i ∉ S → F.Adj i (P i).penultimate := fun i hi =>
    (Walk.adj_penultimate (hnil i hi)).symm
  have hltP : ∀ i, i ∉ S → d (P i).penultimate < d i := by
    intro i hi
    have hrq : r (P i).penultimate = r i := (hrr _ _ (hadjP i hi).reachable).symm
    have h1 := dist_le (P i).dropLast
    have h2 := Walk.length_dropLast_add_one (hnil i hi)
    have : d (P i).penultimate = F.dist (r i) (P i).penultimate := by simp only [d, hrq]
    rw [this, ← hPl i]
    lia
  have huniq : ∀ i b, i ∉ S → F.Adj i b → d b < d i → b = (P i).penultimate := by
    intro i b hi hadj hlt
    have hrb : r b = r i := (hrr _ _ hadj.reachable).symm
    obtain ⟨q, hq, hql⟩ := (show F.Reachable (r i) b from hrb ▸ (hr b).2.symm).exists_path_of_dist
    have hv : i ∉ q.support := by
      intro hmem
      have h1 := dist_le (q.takeUntil i hmem)
      have h2 := q.length_takeUntil_le_length hmem
      simp only [d, hrb] at hlt
      lia
    have hsupp := hF.mem_support_of_ne_mem_support_of_adj_of_isPath (hPp i) hq hadj hv
    exact hF.eq_penultimate_of_adj_end (hPp i) hadj hsupp
  let f : V → Option V := fun i => if i ∈ S then none else some (P i).penultimate
  have hfsome : ∀ a b, f a = some b → a ∉ S ∧ b = (P a).penultimate := by
    intro a b h
    by_cases ha : a ∈ S
    · simp [f, ha] at h
    · simp only [f, ha, ite_false, Option.some.injEq] at h
      exact ⟨ha, h.symm⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · refine Subrelation.wf (r := InvImage (· < ·) d) ?_ (InvImage.wf d wellFounded_lt)
    intro b a h
    obtain ⟨ha, rfl⟩ := hfsome a b h
    exact hltP a ha
  · ext a b
    rw [parentGraph_adj]
    constructor
    · rintro ⟨_, h | h⟩
      · obtain ⟨ha, rfl⟩ := hfsome a b h
        exact hadjP a ha
      · obtain ⟨hb, rfl⟩ := hfsome b a h
        exact (hadjP b hb).symm
    · intro hadj
      refine ⟨hadj.ne, ?_⟩
      have hrab : r a = r b := hrr _ _ hadj.reachable
      have hne : d a ≠ d b := by
        have := hF.dist_ne_of_adj hadj (hr a).2.symm
        simpa [d, hrab] using this
      rcases lt_or_gt_of_ne hne with h | h
      · have hb : b ∉ S := fun hb => by
          have : d b = 0 := by simp [d, hrS b hb]
          lia
        right
        simp only [f, hb, ite_false, ← huniq b a hb hadj.symm h]
      · have ha : a ∉ S := fun ha => by
          have : d a = 0 := by simp [d, hrS a ha]
          lia
        left
        simp only [f, ha, ite_false, ← huniq a b ha hadj h]
  · ext i
    by_cases hi : i ∈ S <;> simp [mem_roots, f, hi]

section Weights

variable [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

omit [DecidableEq V] in
open Classical in
/-- The weight of a rooted parent function factors as edge weights of its forest times the root
weights. -/
theorem IsRooted.prod_coef_eq {f : V → Option V} (hf : IsRooted f) (w : V → V → R)
    (hw : ∀ i j, w i j = w j i) (x : V → R) :
    ∏ i, coef w x i (f i) =
      (∏ e ∈ (parentGraph f).edgeFinset, Sym2.lift ⟨w, hw⟩ e) * ∏ i ∈ roots f, x i := by
  rw [← Finset.prod_filter_not_mul_prod_filter univ (fun i => f i = none)]
  congr 1
  · refine Finset.prod_bij (fun a _ => s(a, (f a).getD a)) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 ha
      simp [hb, hf.adj_of_up hb]
    · intro a ha a' ha' h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 ha
      obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 ha'
      simp only [hb, hb', Option.getD_some, Sym2.eq_iff] at h
      rcases h with ⟨h, _⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact absurd (TransGen.head (r := Up f) hb (.single hb')) (hf.not_transGen _)
    · intro e he
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeFinset, mem_edgeSet, parentGraph_adj] at he
        rcases he.2 with h | h
        · exact ⟨a, by simp [h], by simp [h]⟩
        · exact ⟨b, by simp [h], by simp [h, Sym2.eq_swap]⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 ha
      simp [hb, coef]
  · rw [roots]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi, coef]

open Classical in
/-- The product over the components of `F` of the component sums of `x` is the sum over the
transversals `S` of the components of `∏_{i ∈ S} x i`. -/
theorem prod_sum_connectedComponent_eq (F : SimpleGraph V) (x : V → R) :
    ∏ T : F.ConnectedComponent, (∑ i with F.connectedComponentMk i = T, x i) =
      ∑ S : Finset V with IsTransversal F S, ∏ i ∈ S, x i := by
  rw [Finset.prod_univ_sum]
  have hmem : ∀ ρ : F.ConnectedComponent → V,
      ρ ∈ Fintype.piFinset (fun T => ({i | F.connectedComponentMk i = T} : Finset V)) ↔
        ∀ T, F.connectedComponentMk (ρ T) = T := by
    intro ρ; simp [Fintype.mem_piFinset]
  refine Finset.sum_bij (fun ρ _ => univ.image ρ) ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [hmem] at hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    refine ⟨ρ (F.connectedComponentMk i), ⟨by simp, ?_⟩, ?_⟩
    · exact ConnectedComponent.exact (hρ _).symm
    · rintro s ⟨hs, hr⟩
      obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hs
      rw [ConnectedComponent.sound hr, hρ]
  · intro ρ hρ ρ' hρ' h
    rw [hmem] at hρ hρ'
    funext T
    have : ρ T ∈ univ.image ρ' := h ▸ Finset.mem_image_of_mem ρ (Finset.mem_univ T)
    obtain ⟨T', -, hT'⟩ := Finset.mem_image.1 this
    have : T' = T := by rw [← hρ' T', hT', hρ]
    rw [← hT', this]
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have : ∀ T : F.ConnectedComponent, ∃ s ∈ S, F.connectedComponentMk s = T := by
      intro T
      obtain ⟨i, rfl⟩ := T.exists_rep
      obtain ⟨s, ⟨hs, hr⟩, -⟩ := hS i
      exact ⟨s, hs, (ConnectedComponent.sound hr).symm⟩
    choose ρ hρS hρmk using this
    refine ⟨ρ, (hmem ρ).2 hρmk, ?_⟩
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨T, rfl⟩; exact hρS T
    · intro hs
      refine ⟨F.connectedComponentMk s, ?_⟩
      obtain ⟨s', -, hu⟩ := hS s
      have h1 := hu s ⟨hs, .refl _⟩
      have h2 := hu (ρ (F.connectedComponentMk s))
        ⟨hρS _, ConnectedComponent.exact (hρmk _).symm⟩
      exact h2.trans h1.symm
  · intro ρ hρ
    rw [hmem] at hρ
    rw [Finset.prod_image]
    intro T _ T' _ h
    rw [← hρ T, ← hρ T', h]

open Classical in
/-- **Matrix-forest theorem, combinatorial part**: for symmetric `w`, the sum over rooted parent
functions equals the forest sum `∑_{F acyclic} ∏_{e ∈ F} w_e ∏_{T ∈ comp F} ∑_{i ∈ T} x_i`. -/
theorem sum_isRooted_eq_sum_isAcyclic (w : V → V → R) (hw : ∀ i j, w i j = w j i)
    (x : V → R) :
    (∑ f : V → Option V, if IsRooted f then ∏ i, coef w x i (f i) else 0) =
      ∑ F : SimpleGraph V with F.IsAcyclic,
        (∏ e ∈ F.edgeFinset, Sym2.lift ⟨w, hw⟩ e) *
          ∏ T : F.ConnectedComponent, (∑ i with F.connectedComponentMk i = T, x i) := by
  simp_rw [prod_sum_connectedComponent_eq, Finset.mul_sum]
  rw [← Finset.sum_filter, Finset.sum_sigma']
  refine Finset.sum_bij (fun f _ => ⟨parentGraph f, roots f⟩) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hf.isAcyclic_parentGraph, hf.isTransversal_roots⟩
  · intro f hf g hg h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    exact hf.eq_of_parentGraph_eq hg h.1 h.2
  · rintro ⟨F, S⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨f, hf, rfl, rfl⟩ := exists_isRooted_of_isAcyclic h.1 h.2
    exact ⟨f, by simpa using hf, rfl⟩
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact hf.prod_coef_eq w hw x

end Weights

end MatrixForest
