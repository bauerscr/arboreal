module

public import ArborealDecay.Surgery.Lift
public import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# The cone identity (vertex deletion)

For a vertex `ρ` of `Λ`, let `H = {v // v ≠ ρ}` carry the weights `β` restricted, and set
`h_v = β ρ v`.  Forests `F` of `Λ` correspond to forests `B = F|_H` of `H` together with a choice,
for each tree `T` of `B`, of at most one edge from `ρ` into `T`.  Hence for every event `P` on
forests of `H`,
`∑_{F acyclic, P(F|_H)} w(F) = ∑_{B acyclic, P B} w_H(B) ∏_{T ∈ comp B} (1 + ∑_{v ∈ T} β ρ v)`
(`cone_sum_event`); for `P = ⊤` this is `Z_G = P_H(h)` (`Zforest_cone`).

The proof contracts `B ⊆ F` (`contract_sum_event`): the quotient is a star centred at the vertex
`[ρ]`, whose forests are all edge subsets.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (ρ : Λ)

/-- The restriction `F|_H` of a graph on `Λ` to the vertices different from `ρ`. -/
def restr (F : SimpleGraph Λ) : SimpleGraph {v : Λ // v ≠ ρ} := F.comap Subtype.val

/-- The graph on `Λ` with the edges of `B` (and `ρ` isolated). -/
def liftG (B : SimpleGraph {v : Λ // v ≠ ρ}) : SimpleGraph Λ :=
  B.map (Function.Embedding.subtype _)

/-- The identification map: `ρ ↦ none`, `v ↦ some (component of v in B)`. -/
def coneMap (B : SimpleGraph {v : Λ // v ≠ ρ}) : Λ → Option B.ConnectedComponent :=
  fun v => if h : v = ρ then none else some (B.connectedComponentMk ⟨v, h⟩)

variable {ρ}

theorem restr_adj (F : SimpleGraph Λ) (a b : {v : Λ // v ≠ ρ}) :
    (restr ρ F).Adj a b ↔ F.Adj a b := Iff.rfl

theorem liftG_adj_apply (B : SimpleGraph {v : Λ // v ≠ ρ}) (a b : {v : Λ // v ≠ ρ}) :
    (liftG ρ B).Adj a b ↔ B.Adj a b :=
  SimpleGraph.map_adj_apply (f := Function.Embedding.subtype _)

theorem restr_liftG (B : SimpleGraph {v : Λ // v ≠ ρ}) : restr ρ (liftG ρ B) = B := by
  ext a b
  exact liftG_adj_apply B a b

theorem liftG_isAcyclic {B : SimpleGraph {v : Λ // v ≠ ρ}} (hB : B.IsAcyclic) :
    (liftG ρ B).IsAcyclic := isAcyclic_map _ hB

theorem not_liftG_adj_rho (B : SimpleGraph {v : Λ // v ≠ ρ}) (x : Λ) : ¬ (liftG ρ B).Adj ρ x := by
  intro h
  obtain ⟨a, b, _, ha, _⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
  exact a.2 ha

theorem liftG_reach_rho (B : SimpleGraph {v : Λ // v ≠ ρ}) {v : Λ}
    (h : (liftG ρ B).Reachable ρ v) : v = ρ := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    subst ih
    exact absurd hbc (not_liftG_adj_rho B c)

theorem coneMap_rho (B : SimpleGraph {v : Λ // v ≠ ρ}) : coneMap ρ B ρ = none := by
  simp [coneMap]

theorem coneMap_of_ne (B : SimpleGraph {v : Λ // v ≠ ρ}) {v : Λ} (hv : v ≠ ρ) :
    coneMap ρ B v = some (B.connectedComponentMk ⟨v, hv⟩) := by
  simp [coneMap, hv]

theorem liftG_reachable_iff (B : SimpleGraph {v : Λ // v ≠ ρ}) (u v : Λ) :
    (liftG ρ B).Reachable u v ↔ coneMap ρ B u = coneMap ρ B v := by
  by_cases hu : u = ρ
  · rw [hu]
    constructor
    · intro h; rw [liftG_reach_rho B h]
    · intro h
      by_cases hv : v = ρ
      · rw [hv]
      · rw [coneMap_rho, coneMap_of_ne B hv] at h
        exact absurd h (by simp)
  · by_cases hv : v = ρ
    · rw [hv]
      constructor
      · intro h; exact absurd (liftG_reach_rho B h.symm) hu
      · intro h
        rw [coneMap_rho, coneMap_of_ne B hu] at h
        exact absurd h (by simp)
    · rw [coneMap_of_ne B hu, coneMap_of_ne B hv, Option.some_inj,
        SimpleGraph.ConnectedComponent.eq]
      exact reachable_map_iff (Function.Embedding.subtype _) B ⟨u, hu⟩ ⟨v, hv⟩

theorem forestWeight_liftG {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (B : SimpleGraph {v : Λ // v ≠ ρ}) :
    H02.forestWeight β hβ (liftG ρ B) =
      H02.forestWeight (fun a b : {v : Λ // v ≠ ρ} => β a b) (fun a b => hβ a b) B := by
  refine forestWeight_eq_of_edge_bij (β := fun a b : {v : Λ // v ≠ ρ} => β a b)
    (hβ := fun a b => hβ a b) (γ := β) (hγ := hβ) B (liftG ρ B)
    (Function.Embedding.subtype _).sym2Map ?_ ?_ ?_ ?_
  · exact ((Function.Embedding.subtype _).sym2Map.injective).injOn
  · intro y hy
    have := hy
    unfold liftG at this
    rw [SimpleGraph.edgeSet_map] at this
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, hx, rfl⟩
  · intro x hx
    unfold liftG
    rw [SimpleGraph.edgeSet_map]
    exact ⟨x, hx, rfl⟩
  · intro x _
    induction x using Sym2.ind with
    | h a b => rfl

/-- The event on forests of `Option X`: every edge is incident to `none`. -/
def StarEvent {X : Type*} (F' : SimpleGraph (Option X)) : Prop :=
  ∀ a b, F'.Adj a b → a = none ∨ b = none

theorem restr_iff {B : SimpleGraph {v : Λ // v ≠ ρ}} (hB : B.IsAcyclic) {F : SimpleGraph Λ}
    (hF : F.IsAcyclic) :
    (liftG ρ B ≤ F ∧ StarEvent (quotGraph (coneMap ρ B) F)) ↔ restr ρ F = B := by
  have hA := liftG_reachable_iff B
  have hAc := liftG_isAcyclic hB
  constructor
  · rintro ⟨hle, hQ⟩
    ext a b
    rw [restr_adj]
    constructor
    · intro hab
      by_contra hnB
      have hnA : ¬ (liftG ρ B).Adj a b := fun h => hnB ((liftG_adj_apply B a b).1 h)
      have hne := no_internal_edge (coneMap ρ B) hAc hA hF hle hab hnA
      have := hQ (coneMap ρ B a) (coneMap ρ B b)
        ((quotGraph_adj _ _ _ _).2 ⟨hne, a, b, rfl, rfl, hab⟩)
      rw [coneMap_of_ne B a.2, coneMap_of_ne B b.2] at this
      simp at this
    · intro hab
      exact hle ((liftG_adj_apply B a b).2 hab)
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 huv
      have : (restr ρ F).Adj a b := by rw [h]; exact hab
      exact this
    · intro a' b' hab
      rw [quotGraph_adj] at hab
      obtain ⟨hne, u, v, hu, hv, huv⟩ := hab
      by_contra hcon
      push Not at hcon
      have hu' : u ≠ ρ := by
        rintro rfl
        rw [coneMap_rho] at hu
        exact hcon.1 hu.symm
      have hv' : v ≠ ρ := by
        rintro rfl
        rw [coneMap_rho] at hv
        exact hcon.2 hv.symm
      have hB' : B.Adj ⟨u, hu'⟩ ⟨v, hv'⟩ := by
        have : (restr ρ F).Adj ⟨u, hu'⟩ ⟨v, hv'⟩ := huv
        rwa [h] at this
      have hA' : (liftG ρ B).Reachable u v :=
        ((liftG_adj_apply B ⟨u, hu'⟩ ⟨v, hv'⟩).2 hB').reachable
      exact hne (hu.symm.trans (((hA u v).1 hA').trans hv))

/-- Forests of a star: every edge subset is a forest, so the partition function is a product. -/
theorem star_sum {X : Type*} [Fintype X] [DecidableEq X] (m : Option X → Option X → ℝ)
    (hm : ∀ a b, m a b = m b a) :
    ∑ F' ∈ univ.filter (fun F' : SimpleGraph (Option X) => F'.IsAcyclic ∧ StarEvent F'),
        H02.forestWeight m hm F' = ∏ T : X, (1 + m none (some T)) := by
  set M : Finset (Sym2 (Option X)) := univ.image (fun T : X => s(none, some T)) with hM
  have hMnd : ∀ t ∈ M, ¬ t.IsDiag := by
    intro t ht
    obtain ⟨T, _, rfl⟩ := mem_image.1 ht
    simp
  have hMmem : ∀ a b : Option X, a ≠ b → (a = none ∨ b = none) → s(a, b) ∈ M := by
    intro a b hab h
    rcases h with rfl | rfl
    · obtain ⟨T, rfl⟩ := Option.ne_none_iff_exists'.1 (Ne.symm hab)
      exact mem_image.2 ⟨T, mem_univ _, rfl⟩
    · obtain ⟨T, rfl⟩ := Option.ne_none_iff_exists'.1 hab
      exact mem_image.2 ⟨T, mem_univ _, Sym2.eq_swap⟩
  have hMstar : ∀ a b : Option X, s(a, b) ∈ M → a ≠ b ∧ (a = none ∨ b = none) := by
    intro a b h
    obtain ⟨T, _, hT⟩ := mem_image.1 h
    simp only [Sym2.eq_iff] at hT
    rcases hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inr rfl⟩
  have hfs : ∀ F' : SimpleGraph (Option X),
      SimpleGraph.fromEdgeSet (↑F'.edgeFinset : Set (Sym2 (Option X))) = F' := by
    intro F'; rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  have step1 : ∑ F' ∈ univ.filter (fun F' : SimpleGraph (Option X) =>
        F'.IsAcyclic ∧ StarEvent F'), H02.forestWeight m hm F' =
      ∑ T ∈ M.powerset, ∏ t ∈ T, Sym2.lift ⟨m, hm⟩ t := by
    refine Finset.sum_nbij' (fun F' => F'.edgeFinset)
      (fun T => SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Option X)))) ?_ ?_ ?_ ?_ ?_
    · intro F' hF'
      simp only [mem_filter, mem_univ, true_and] at hF'
      simp only [mem_powerset]
      intro t ht
      have ht' := SimpleGraph.mem_edgeFinset.1 ht
      induction t using Sym2.ind with
      | h a b =>
        have hadj : F'.Adj a b := ht'
        exact hMmem a b hadj.ne (hF'.2 a b hadj)
    · intro T hT
      simp only [mem_powerset] at hT
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · refine (SimpleGraph.isAcyclic_starGraph (none : Option X)).anti ?_
        intro a b hab
        rw [SimpleGraph.fromEdgeSet_adj] at hab
        have := hMstar a b (hT (by simpa using hab.1))
        rw [SimpleGraph.starGraph_adj]
        exact this
      · intro a b hab
        rw [SimpleGraph.fromEdgeSet_adj] at hab
        exact (hMstar a b (hT (by simpa using hab.1))).2
    · intro F' _
      exact hfs F'
    · intro T hT
      simp only [mem_powerset] at hT
      exact edgeFinset_fromEdgeSet_eq fun t ht => hMnd t (hT ht)
    · intro F' _
      rfl
  rw [step1, ← Finset.prod_one_add M (f := fun t => Sym2.lift ⟨m, hm⟩ t), hM,
    Finset.prod_image]
  · rfl
  · intro T _ T' _ h
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨_, h⟩ | ⟨h1, _⟩
    · exact Option.some.inj h
    · exact absurd h1 (by simp)

/-- The weight of the edge from `[ρ]` to the tree `T`: the total weight `∑_{v ∈ T} β ρ v`. -/
theorem mapW_none_some {β : Λ → Λ → ℝ} (B : SimpleGraph {v : Λ // v ≠ ρ})
    (T : B.ConnectedComponent) :
    mapW β (coneMap ρ B) none (some T) =
      ∑ v : {v : Λ // v ≠ ρ} with B.connectedComponentMk v = T, β ρ v := by
  unfold mapW
  simp only [reduceCtorEq, ite_false]
  rw [Finset.sum_eq_single ρ]
  · refine (Finset.sum_bij (fun (w : {v : Λ // v ≠ ρ}) _ => w.val) ?_ ?_ ?_ ?_).symm
    · intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      rw [coneMap_of_ne B w.2, hw]
    · intro a _ b _ h; exact Subtype.ext h
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      have hvρ : v ≠ ρ := by
        rintro rfl
        rw [coneMap_rho] at hv
        exact absurd hv (by simp)
      refine ⟨⟨v, hvρ⟩, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [coneMap_of_ne B hvρ] at hv
      exact Option.some.inj hv
    · intro w _; rfl
  · intro u hu hne
    simp only [mem_filter, mem_univ, true_and] at hu
    by_cases hρ : u = ρ
    · exact absurd hρ hne
    · rw [coneMap_of_ne B hρ] at hu
      exact absurd hu (by simp)
  · intro h
    exact absurd (by simp [mem_filter, coneMap_rho]) h

/-- **Fibre sum.**  For an acyclic `B` on `H`, the forests of `Λ` restricting to `B` have total
weight `w_H(B) ∏_{T ∈ comp B} (1 + ∑_{v ∈ T} β ρ v)`. -/
theorem fibre_sum {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    {B : SimpleGraph {v : Λ // v ≠ ρ}} (hB : B.IsAcyclic) :
    ∑ F ∈ univ.filter (fun F : SimpleGraph Λ => F.IsAcyclic ∧ restr ρ F = B),
        H02.forestWeight β hβ F =
      H02.forestWeight (fun a b : {v : Λ // v ≠ ρ} => β a b) (fun a b => hβ a b) B *
        ∏ T : B.ConnectedComponent,
          (1 + ∑ v : {v : Λ // v ≠ ρ} with B.connectedComponentMk v = T, β ρ v) := by
  have key := contract_sum_event (coneMap ρ B) (liftG_isAcyclic hB) (liftG_reachable_iff B) hβ
    StarEvent
  refine (Finset.sum_congr (Finset.ext fun F => ?_) fun _ _ => rfl).trans (key.trans ?_)
  · simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨hF, (restr_iff hB hF).2 h⟩
    · rintro ⟨hF, h⟩
      exact ⟨hF, (restr_iff hB hF).1 h⟩
  · rw [forestWeight_liftG hβ B]
    congr 1
    rw [star_sum]
    exact Finset.prod_congr rfl fun T _ => by rw [mapW_none_some]

/-- **The cone identity with an event.**  For `ρ ∈ Λ`, `H = {v // v ≠ ρ}` with the restricted
weights and every event `P` on forests of `H`:
`∑_{F acyclic on Λ, P(F|_H)} w(F) = ∑_{B acyclic on H, P B} w_H(B) ∏_{T ∈ comp B}
(1 + ∑_{v ∈ T} β ρ v)`. -/
theorem cone_sum_event {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (P : SimpleGraph {v : Λ // v ≠ ρ} → Prop) :
    ∑ F ∈ univ.filter (fun F : SimpleGraph Λ => F.IsAcyclic ∧ P (restr ρ F)),
        H02.forestWeight β hβ F =
      ∑ B ∈ univ.filter (fun B : SimpleGraph {v : Λ // v ≠ ρ} => B.IsAcyclic ∧ P B),
        H02.forestWeight (fun a b : {v : Λ // v ≠ ρ} => β a b) (fun a b => hβ a b) B *
          ∏ T : B.ConnectedComponent,
            (1 + ∑ v : {v : Λ // v ≠ ρ} with B.connectedComponentMk v = T, β ρ v) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun F : SimpleGraph Λ =>
      F.IsAcyclic ∧ P (restr ρ F))
    (t := univ.filter fun B : SimpleGraph {v : Λ // v ≠ ρ} => B.IsAcyclic ∧ P B)
    (g := restr ρ) ?_]
  · refine Finset.sum_congr rfl fun B hB => ?_
    simp only [mem_filter, mem_univ, true_and] at hB
    rw [← fibre_sum hβ hB.1]
    refine Finset.sum_congr (Finset.ext fun F => ?_) fun _ _ => rfl
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hF, _⟩, h⟩; exact ⟨hF, h⟩
    · rintro ⟨hF, h⟩; exact ⟨⟨hF, h ▸ hB.2⟩, h⟩
  · intro F hF
    simp only [mem_filter, mem_univ, true_and] at hF ⊢
    exact ⟨SimpleGraph.IsAcyclic.of_comap (Function.Embedding.subtype _) hF.1, hF.2⟩

/-- **`Z_G = P_H(h)`**, the cone identity: `Z_G = ∑_{F_H acyclic} w_H(F_H) ∏_{T} (1 + ∑_{v∈T} β ρ v)`
(the right side is `[1]_{β_H,h}` for `h_v = β ρ v`, see `Zforest_eq_expect_cone`). -/
theorem Zforest_cone {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) :
    H02.Zforest β hβ =
      ∑ B : SimpleGraph {v : Λ // v ≠ ρ} with B.IsAcyclic,
        H02.forestWeight (fun a b : {v : Λ // v ≠ ρ} => β a b) (fun a b => hβ a b) B *
          ∏ T : B.ConnectedComponent,
            (1 + ∑ v : {v : Λ // v ≠ ρ} with B.connectedComponentMk v = T, β ρ v) := by
  have := cone_sum_event (ρ := ρ) hβ (fun _ => True)
  simp only [and_true] at this
  exact this

/-- The cone identity in terms of the Grassmann expectation `[1]_{β_H, h}`, `h_v = β ρ v`. -/
theorem Zforest_eq_expect_cone {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) :
    H02.Zforest β hβ =
      H02.expect (fun a b : {v : Λ // v ≠ ρ} => β a b) (fun v => β ρ v) 1 := by
  rw [Zforest_cone (ρ := ρ) hβ, H02.thm_H02forest (fun a b : {v : Λ // v ≠ ρ} => β a b)
    (fun a b => hβ a b) (fun v => β ρ v)]
  rfl

/-- The cone identity for probabilities: an event on `F|_H`. -/
theorem arborealProb_cone {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (P : SimpleGraph {v : Λ // v ≠ ρ} → Prop) :
    H02.arborealProb β hβ (fun F => P (restr ρ F)) =
      (∑ B ∈ univ.filter (fun B : SimpleGraph {v : Λ // v ≠ ρ} => B.IsAcyclic ∧ P B),
        H02.forestWeight (fun a b : {v : Λ // v ≠ ρ} => β a b) (fun a b => hβ a b) B *
          ∏ T : B.ConnectedComponent,
            (1 + ∑ v : {v : Λ // v ≠ ρ} with B.connectedComponentMk v = T, β ρ v)) /
        H02.Zforest β hβ := by
  unfold H02.arborealProb
  rw [← cone_sum_event (ρ := ρ) hβ P]

end

end ArborealDecay.Surgery
