module

public import ArborealDecay.Surgery.Glue

/-!
# Factorisation over a one-vertex union

`V₁ ∪ V₂ = Λ`, `V₁ ∩ V₂ = {ρ}`, and `β u v = 0` for `u ∈ V₁ ∖ {ρ}`, `v ∈ V₂ ∖ {ρ}`.  A forest of
positive weight has no edge between the two pieces, hence is determined by its restrictions
`F|_{V₁}`, `F|_{V₂}`, which are arbitrary forests on `V₁`, `V₂`, and the weight is the product.

* `sum_union_event`: `∑_{F, P₁(F|V₁) ∧ P₂(F|V₂)} w(F) = (∑_{F₁, P₁} w₁(F₁)) (∑_{F₂, P₂} w₂(F₂))`;
* `Zforest_union`: `Z_β = Z_{β|V₁} Z_{β|V₂}`;
* `arborealProb_union`: events depending on the two pieces are independent;
* `arborealProb_reachable_union`: `μ(a ↔ b) = μ(a ↔ ρ) μ(ρ ↔ b)` for `a ∈ V₁`, `b ∈ V₂`.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `Λ = V₁ ∪ V₂` with `V₁ ∩ V₂ = {ρ}`. -/
structure OneVertexUnion (V₁ V₂ : Finset Λ) (ρ : Λ) : Prop where
  cover : ∀ x, x ∈ V₁ ∨ x ∈ V₂
  inter : ∀ x, x ∈ V₁ → x ∈ V₂ → x = ρ
  mem₁ : ρ ∈ V₁
  mem₂ : ρ ∈ V₂

/-- A graph has no edge from `V₁ ∖ {ρ}` to `V₂ ∖ {ρ}`. -/
def NoCross (V₁ V₂ : Finset Λ) (ρ : Λ) (F : SimpleGraph Λ) : Prop :=
  ∀ u v, F.Adj u v → u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → False

variable {V₁ V₂ : Finset Λ} {ρ : Λ}

theorem OneVertexUnion.adj_cases (hU : OneVertexUnion V₁ V₂ ρ) {F : SimpleGraph Λ}
    (hF : NoCross V₁ V₂ ρ F) {x y : Λ} (h : F.Adj x y) :
    (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂) := by
  rcases hU.cover x with hx | hx <;> rcases hU.cover y with hy | hy
  · exact Or.inl ⟨hx, hy⟩
  · by_cases hxρ : x = ρ
    · exact Or.inr ⟨hxρ ▸ hU.mem₂, hy⟩
    · by_cases hyρ : y = ρ
      · exact Or.inl ⟨hx, hyρ ▸ hU.mem₁⟩
      · exact (hF x y h hx hxρ hy hyρ).elim
  · by_cases hxρ : x = ρ
    · exact Or.inl ⟨hxρ ▸ hU.mem₁, hy⟩
    · by_cases hyρ : y = ρ
      · exact Or.inr ⟨hx, hyρ ▸ hU.mem₂⟩
      · exact (hF y x h.symm hy hyρ hx hxρ).elim
  · exact Or.inr ⟨hx, hy⟩

theorem glue_resFin (hU : OneVertexUnion V₁ V₂ ρ) {F : SimpleGraph Λ} (hF : NoCross V₁ V₂ ρ F) :
    glue V₁ V₂ (resFin V₁ F) (resFin V₂ F) = F := by
  ext x y
  unfold glue
  rw [SimpleGraph.sup_adj]
  constructor
  · rintro (h | h)
    · obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
      exact hab
    · obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
      exact hab
  · intro h
    rcases hU.adj_cases hF h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ((SimpleGraph.map_adj _ _ _ _).2 ⟨⟨x, hx⟩, ⟨y, hy⟩, h, rfl, rfl⟩)
    · exact Or.inr ((SimpleGraph.map_adj _ _ _ _).2 ⟨⟨x, hx⟩, ⟨y, hy⟩, h, rfl, rfl⟩)

theorem resFin_glue_left (hU : OneVertexUnion V₁ V₂ ρ) (F₁ : SimpleGraph V₁)
    (F₂ : SimpleGraph V₂) : resFin V₁ (glue V₁ V₂ F₁ F₂) = F₁ := by
  ext a b
  rw [resFin_adj]
  unfold glue
  rw [SimpleGraph.sup_adj, map_embFin_adj]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      obtain ⟨c, d, hcd, hc, hd⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
      have h1 : (a : Λ) = ρ := hU.inter a a.2 (by rw [← hc]; exact c.2)
      have h2 : (b : Λ) = ρ := hU.inter b b.2 (by rw [← hd]; exact d.2)
      have : c = d := Subtype.ext (by simp only [embFin_apply] at hc hd; rw [hc, hd, h1, h2])
      exact hcd.ne this
  · intro h; exact Or.inl h

theorem resFin_glue_right (hU : OneVertexUnion V₁ V₂ ρ) (F₁ : SimpleGraph V₁)
    (F₂ : SimpleGraph V₂) : resFin V₂ (glue V₁ V₂ F₁ F₂) = F₂ := by
  ext a b
  rw [resFin_adj]
  unfold glue
  rw [SimpleGraph.sup_adj, map_embFin_adj]
  constructor
  · rintro (h | h)
    · exfalso
      obtain ⟨c, d, hcd, hc, hd⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
      have h1 : (a : Λ) = ρ := hU.inter a (by rw [← hc]; exact c.2) a.2
      have h2 : (b : Λ) = ρ := hU.inter b (by rw [← hd]; exact d.2) b.2
      have : c = d := Subtype.ext (by simp only [embFin_apply] at hc hd; rw [hc, hd, h1, h2])
      exact hcd.ne this
    · exact h
  · intro h; exact Or.inr h

theorem noCross_glue (hU : OneVertexUnion V₁ V₂ ρ) (F₁ : SimpleGraph V₁) (F₂ : SimpleGraph V₂) :
    NoCross V₁ V₂ ρ (glue V₁ V₂ F₁ F₂) := by
  intro u v h hu hu' hv hv'
  unfold glue at h
  rw [SimpleGraph.sup_adj] at h
  rcases h with h | h
  · obtain ⟨a, b, _, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
    exact hv' (hU.inter _ b.2 hv)
  · obtain ⟨a, b, _, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
    exact hu' (hU.inter _ hu a.2)

theorem forestWeight_map {S : Finset Λ} {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (B : SimpleGraph S) :
    H02.forestWeight β hβ (B.map (embFin S)) =
      H02.forestWeight (fun a b : S => β a b) (fun a b => hβ a b) B := by
  refine forestWeight_eq_of_edge_bij (β := fun a b : S => β a b) (hβ := fun a b => hβ a b)
    (γ := β) (hγ := hβ) B (B.map (embFin S)) (embFin S).sym2Map ?_ ?_ ?_ ?_
  · exact ((embFin S).sym2Map.injective).injOn
  · intro y hy
    rw [SimpleGraph.edgeSet_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  · intro x hx
    rw [SimpleGraph.edgeSet_map]
    exact ⟨x, hx, rfl⟩
  · intro x _
    induction x using Sym2.ind with
    | h a b => rfl

theorem forestWeight_sup_disjoint {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    {G₁ G₂ : SimpleGraph Λ} (hd : Disjoint G₁.edgeSet G₂.edgeSet) :
    H02.forestWeight β hβ (G₁ ⊔ G₂) =
      H02.forestWeight β hβ G₁ * H02.forestWeight β hβ G₂ := by
  unfold H02.forestWeight
  have : ∀ {i : Fintype (G₁ ⊔ G₂).edgeSet},
      @SimpleGraph.edgeFinset Λ (G₁ ⊔ G₂) i = G₁.edgeFinset ∪ G₂.edgeFinset := by
    intro i
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [this, Finset.prod_union]
  rw [Finset.disjoint_left]
  intro e h1 h2
  rw [SimpleGraph.mem_edgeFinset] at h1 h2
  exact Set.disjoint_left.1 hd h1 h2

theorem forestWeight_glue (hU : OneVertexUnion V₁ V₂ ρ) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i) (F₁ : SimpleGraph V₁) (F₂ : SimpleGraph V₂) :
    H02.forestWeight β hβ (glue V₁ V₂ F₁ F₂) =
      H02.forestWeight (fun a b : V₁ => β a b) (fun a b => hβ a b) F₁ *
        H02.forestWeight (fun a b : V₂ => β a b) (fun a b => hβ a b) F₂ := by
  unfold glue
  rw [forestWeight_sup_disjoint hβ, forestWeight_map, forestWeight_map]
  rw [Set.disjoint_left]
  intro e h1 h2
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj _ _ _ _).1 h1
    obtain ⟨c, d, hcd, hc, hd⟩ := (SimpleGraph.map_adj _ _ _ _).1 h2
    simp only [embFin_apply] at ha hb hc hd
    have h1' : x = ρ := hU.inter x (ha ▸ a.2) (hc ▸ c.2)
    have h2' : y = ρ := hU.inter y (hb ▸ b.2) (hd ▸ d.2)
    exact hab.ne (Subtype.ext (by rw [ha, hb, h1', h2']))

theorem forestWeight_eq_zero_of_not_noCross {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → β u v = 0) {F : SimpleGraph Λ}
    (hF : ¬ NoCross V₁ V₂ ρ F) : H02.forestWeight β hβ F = 0 := by
  unfold NoCross at hF
  push Not at hF
  obtain ⟨u, v, huv, hu1, hu2, hv1, hv2⟩ := hF
  unfold H02.forestWeight
  exact Finset.prod_eq_zero (i := s(u, v)) (SimpleGraph.mem_edgeFinset.2 huv)
    (by simpa using hcross u v hu1 hu2 hv1 hv2.1)

/-- **Factorisation of forest sums over a one-vertex union**, with events on the two pieces. -/
theorem sum_union_event (hU : OneVertexUnion V₁ V₂ ρ) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → β u v = 0)
    (P₁ : SimpleGraph V₁ → Prop) (P₂ : SimpleGraph V₂ → Prop) :
    ∑ F ∈ univ.filter (fun F : SimpleGraph Λ =>
        F.IsAcyclic ∧ (P₁ (resFin V₁ F) ∧ P₂ (resFin V₂ F))), H02.forestWeight β hβ F =
      (∑ F₁ ∈ univ.filter (fun F₁ : SimpleGraph V₁ => F₁.IsAcyclic ∧ P₁ F₁),
          H02.forestWeight (fun a b : V₁ => β a b) (fun a b => hβ a b) F₁) *
        ∑ F₂ ∈ univ.filter (fun F₂ : SimpleGraph V₂ => F₂.IsAcyclic ∧ P₂ F₂),
          H02.forestWeight (fun a b : V₂ => β a b) (fun a b => hβ a b) F₂ := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_subset (s₁ := univ.filter (fun F : SimpleGraph Λ =>
      F.IsAcyclic ∧ (P₁ (resFin V₁ F) ∧ P₂ (resFin V₂ F)) ∧ NoCross V₁ V₂ ρ F))]
  · refine Finset.sum_nbij' (fun F => (resFin V₁ F, resFin V₂ F))
      (fun p => glue V₁ V₂ p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro F hF
      simp only [mem_filter, mem_univ, true_and, mem_product] at hF ⊢
      exact ⟨⟨SimpleGraph.IsAcyclic.of_comap (embFin V₁) hF.1, hF.2.1.1⟩,
        ⟨SimpleGraph.IsAcyclic.of_comap (embFin V₂) hF.1, hF.2.1.2⟩⟩
    · rintro ⟨F₁, F₂⟩ hp
      simp only [mem_filter, mem_univ, true_and, mem_product] at hp ⊢
      refine ⟨glue_isAcyclic V₁ V₂ hU.mem₁ hU.mem₂ hU.inter hp.1.1 hp.2.1, ?_,
        noCross_glue hU F₁ F₂⟩
      rw [resFin_glue_left hU, resFin_glue_right hU]
      exact ⟨hp.1.2, hp.2.2⟩
    · intro F hF
      simp only [mem_filter, mem_univ, true_and] at hF
      exact glue_resFin hU hF.2.2
    · rintro ⟨F₁, F₂⟩ _
      simp only [Prod.mk.injEq]
      exact ⟨resFin_glue_left hU F₁ F₂, resFin_glue_right hU F₁ F₂⟩
    · intro F hF
      simp only [mem_filter, mem_univ, true_and] at hF
      have := forestWeight_glue hU hβ (resFin V₁ F) (resFin V₂ F)
      rw [glue_resFin hU hF.2.2] at this
      exact this
  · intro F hF
    simp only [mem_filter, mem_univ, true_and] at hF ⊢
    exact ⟨hF.1, hF.2.1⟩
  · intro F hF hnF
    simp only [mem_filter, mem_univ, true_and, not_and] at hF hnF
    exact forestWeight_eq_zero_of_not_noCross hβ hcross fun h => hnF hF.1 hF.2 h

/-- **`Z_β = Z_{β|V₁} · Z_{β|V₂}`** for a one-vertex union. -/
theorem Zforest_union (hU : OneVertexUnion V₁ V₂ ρ) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → β u v = 0) :
    H02.Zforest β hβ =
      H02.Zforest (fun a b : V₁ => β a b) (fun a b => hβ a b) *
        H02.Zforest (fun a b : V₂ => β a b) (fun a b => hβ a b) := by
  have := sum_union_event hU hβ hcross (fun _ => True) (fun _ => True)
  simp only [and_self, and_true] at this
  exact this

/-- **Independence over a one-vertex union**: for events `P₁` on forests of `V₁` and `P₂` on
forests of `V₂`, `μ_β[P₁(F|V₁) ∧ P₂(F|V₂)] = μ_{β|V₁}[P₁] μ_{β|V₂}[P₂]`. -/
theorem arborealProb_union (hU : OneVertexUnion V₁ V₂ ρ) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → β u v = 0)
    (P₁ : SimpleGraph V₁ → Prop) (P₂ : SimpleGraph V₂ → Prop) :
    H02.arborealProb β hβ (fun F => P₁ (resFin V₁ F) ∧ P₂ (resFin V₂ F)) =
      H02.arborealProb (fun a b : V₁ => β a b) (fun a b => hβ a b) P₁ *
        H02.arborealProb (fun a b : V₂ => β a b) (fun a b => hβ a b) P₂ := by
  unfold H02.arborealProb
  rw [Zforest_union hU hβ hcross]
  have hs := sum_union_event hU hβ hcross P₁ P₂
  rw [← mul_div_mul_comm, ← hs]
  exact congrArg (· / _) (sum_filter_iff _ _ _ (fun _ => Iff.rfl) _)

/-- The probability of an event depends only on its restriction to forests of no cross edge
(the others have weight zero). -/
theorem arborealProb_congr_noCross {β' : Λ → Λ → ℝ} (hβ : ∀ i j, β' i j = β' j i)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → β' u v = 0) (E E' : SimpleGraph Λ → Prop)
    (h : ∀ F : SimpleGraph Λ, F.IsAcyclic → NoCross V₁ V₂ ρ F → (E F ↔ E' F)) :
    H02.arborealProb β' hβ E = H02.arborealProb β' hβ E' := by
  unfold H02.arborealProb
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases hF : NoCross V₁ V₂ ρ F
  · by_cases hac : F.IsAcyclic
    · simp only [hac, true_and]
      by_cases hE : E F
      · simp [hE, (h F hac hF).1 hE]
      · have hE' : ¬ E' F := fun h' => hE ((h F hac hF).2 h')
        simp [hE, hE']
    · simp [hac]
  · have := forestWeight_eq_zero_of_not_noCross hβ hcross hF
    simp only [this, ite_self]

/-! ### Connectivity across a one-vertex union -/

theorem reach_retr {V V' : Finset Λ} {ρ : Λ} (hρ : ρ ∈ V) (hint : ∀ x, x ∈ V → x ∈ V' → x = ρ)
    {F : SimpleGraph Λ}
    (hc : ∀ x y, F.Adj x y → (x ∈ V ∧ y ∈ V) ∨ (x ∈ V' ∧ y ∈ V')) {x y : Λ}
    (h : F.Reachable x y) :
    (resFin V F).Reachable (retr V ρ hρ x) (retr V ρ hρ y) := by
  refine reach_weakHom (retr V ρ hρ) ?_ h
  intro p q hpq
  rcases hc p q hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · right
    rw [retr_of_mem hρ hp, retr_of_mem hρ hq]
    exact hpq
  · left
    rw [retr_of_mem_other hρ hint hp, retr_of_mem_other hρ hint hq]

theorem reach_of_res (S : Finset Λ) {F : SimpleGraph Λ} {a b : S}
    (h : (resFin S F).Reachable a b) : F.Reachable a.val b.val :=
  h.map (SimpleGraph.Hom.comap Subtype.val F)

theorem reach_iff_res₁ (hU : OneVertexUnion V₁ V₂ ρ) {F : SimpleGraph Λ}
    (hF : NoCross V₁ V₂ ρ F) {x : Λ} (hx : x ∈ V₁) :
    F.Reachable x ρ ↔ (resFin V₁ F).Reachable ⟨x, hx⟩ ⟨ρ, hU.mem₁⟩ := by
  constructor
  · intro h
    have := reach_retr hU.mem₁ hU.inter (fun x y h => hU.adj_cases hF h) h
    rwa [retr_of_mem hU.mem₁ hx, retr_of_mem hU.mem₁ hU.mem₁] at this
  · intro h; exact reach_of_res V₁ h

theorem reach_iff_res₂ (hU : OneVertexUnion V₁ V₂ ρ) {F : SimpleGraph Λ}
    (hF : NoCross V₁ V₂ ρ F) {y : Λ} (hy : y ∈ V₂) :
    F.Reachable ρ y ↔ (resFin V₂ F).Reachable ⟨ρ, hU.mem₂⟩ ⟨y, hy⟩ := by
  constructor
  · intro h
    have := reach_retr hU.mem₂ (fun x h2 h1 => hU.inter x h1 h2)
      (fun x y h => (hU.adj_cases hF h).symm) h
    rwa [retr_of_mem hU.mem₂ hy, retr_of_mem hU.mem₂ hU.mem₂] at this
  · intro h; exact reach_of_res V₂ h

theorem reach_iff_res (hU : OneVertexUnion V₁ V₂ ρ) {F : SimpleGraph Λ}
    (hF : NoCross V₁ V₂ ρ F) {a b : Λ} (ha : a ∈ V₁) (hb : b ∈ V₂) :
    F.Reachable a b ↔ ((resFin V₁ F).Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩ ∧
      (resFin V₂ F).Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩) := by
  rw [← reach_iff_res₁ hU hF ha, ← reach_iff_res₂ hU hF hb]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := reach_retr hU.mem₁ hU.inter (fun x y h => hU.adj_cases hF h) h
      rw [retr_of_mem hU.mem₁ ha, retr_of_mem_other hU.mem₁ hU.inter hb] at this
      exact reach_of_res V₁ this
    · have := reach_retr hU.mem₂ (fun x h2 h1 => hU.inter x h1 h2)
        (fun x y h => (hU.adj_cases hF h).symm) h
      rw [retr_of_mem hU.mem₂ hb, retr_of_mem_other hU.mem₂ (fun x h2 h1 => hU.inter x h1 h2) ha]
        at this
      exact reach_of_res V₂ this
  · rintro ⟨h1, h2⟩
    exact h1.trans h2

/-- **One-vertex union and connectivity**: for `a ∈ V₁`, `b ∈ V₂`,
`μ(a ↔ b) = μ(a ↔ ρ) μ(ρ ↔ b)`. -/
theorem arborealProb_reachable_union (hU : OneVertexUnion V₁ V₂ ρ) {β : Λ → Λ → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → β u v = 0) {a b : Λ} (ha : a ∈ V₁)
    (hb : b ∈ V₂) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) =
      H02.arborealProb β hβ (fun F => F.Reachable a ρ) *
        H02.arborealProb β hβ (fun F => F.Reachable ρ b) := by
  have t1 := H02.arborealProb_true (w := fun a b : V₁ => β a b) (fun a b => hβ a b)
    (fun a b => hβ0 a b)
  have t2 := H02.arborealProb_true (w := fun a b : V₂ => β a b) (fun a b => hβ a b)
    (fun a b => hβ0 a b)
  have e1 := arborealProb_union hU hβ hcross
    (fun G => G.Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩) (fun G => G.Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩)
  have e2 := arborealProb_union hU hβ hcross
    (fun G => G.Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩) (fun _ => True)
  have e3 := arborealProb_union hU hβ hcross
    (fun _ => True) (fun G => G.Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩)
  rw [t2, mul_one] at e2
  rw [t1, one_mul] at e3
  have c1 := arborealProb_congr_noCross hβ hcross (fun F => F.Reachable a b)
    (fun F => (resFin V₁ F).Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩ ∧
      (resFin V₂ F).Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩) (fun F _ hF => reach_iff_res hU hF ha hb)
  have c2 := arborealProb_congr_noCross hβ hcross (fun F => F.Reachable a ρ)
    (fun F => (resFin V₁ F).Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩ ∧ True)
    (fun F _ hF => (reach_iff_res₁ hU hF ha).trans (and_true _).symm.to_iff)
  have c3 := arborealProb_congr_noCross hβ hcross (fun F => F.Reachable ρ b)
    (fun F => True ∧ (resFin V₂ F).Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩)
    (fun F _ hF => (reach_iff_res₂ hU hF hb).trans (true_and _).symm.to_iff)
  rw [c1, c2, c3, e1, e2, e3]

end

end ArborealDecay.Surgery
