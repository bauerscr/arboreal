module

public import ArborealDecay.Surgery.Lift

/-!
# Gluing two forests at one vertex

`V₁, V₂ ⊆ Λ` with `V₁ ∩ V₂ = {ρ}`.  `glue F₁ F₂` is the graph on `Λ` with the edges of `F₁`
(on `V₁`) and of `F₂` (on `V₂`).  It is acyclic iff both pieces are, and its weight is the product.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Reachability is preserved by a "weak homomorphism" (adjacent vertices are sent to equal or
adjacent vertices). -/
theorem reach_weakHom {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (r : V → W)
    (h : ∀ x y, G.Adj x y → r x = r y ∨ G'.Adj (r x) (r y)) {u v : V}
    (huv : G.Reachable u v) : G'.Reachable (r u) (r v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv ⊢
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rcases h b c hbc with h1 | h1
    · rw [← h1]; exact ih
    · exact ih.tail h1

/-- Restriction of a graph on `Λ` to a finset `S`. -/
def resFin (S : Finset Λ) (F : SimpleGraph Λ) : SimpleGraph S := F.comap Subtype.val

/-- The inclusion of a finset in `Λ`. -/
def embFin (S : Finset Λ) : S ↪ Λ := Function.Embedding.subtype _

/-- The union of the edges of `F₁` (on `V₁`) and `F₂` (on `V₂`). -/
def glue (V₁ V₂ : Finset Λ) (F₁ : SimpleGraph V₁) (F₂ : SimpleGraph V₂) : SimpleGraph Λ :=
  F₁.map (embFin V₁) ⊔ F₂.map (embFin V₂)

@[simp] theorem embFin_apply (S : Finset Λ) (x : S) : embFin S x = x.val := rfl

theorem resFin_adj (S : Finset Λ) (F : SimpleGraph Λ) (a b : S) :
    (resFin S F).Adj a b ↔ F.Adj a b := Iff.rfl

theorem map_embFin_adj (S : Finset Λ) (F : SimpleGraph S) (a b : S) :
    (F.map (embFin S)).Adj a b ↔ F.Adj a b :=
  SimpleGraph.map_adj_apply (f := embFin S)

/-- The retraction of `Λ` onto `V`, sending the points outside `V` to `ρ`. -/
def retr (V : Finset Λ) (ρ : Λ) (hρ : ρ ∈ V) (x : Λ) : V :=
  if h : x ∈ V then ⟨x, h⟩ else ⟨ρ, hρ⟩

theorem retr_of_mem {V : Finset Λ} {ρ : Λ} (hρ : ρ ∈ V) {x : Λ} (hx : x ∈ V) :
    retr V ρ hρ x = ⟨x, hx⟩ := by simp [retr, hx]

theorem retr_of_mem_other {V V' : Finset Λ} {ρ : Λ} (hρ : ρ ∈ V)
    (hint : ∀ x, x ∈ V → x ∈ V' → x = ρ) {x : Λ} (hx : x ∈ V') :
    retr V ρ hρ x = ⟨ρ, hρ⟩ := by
  by_cases h : x ∈ V
  · rw [retr_of_mem hρ h]
    exact Subtype.ext (hint x h hx)
  · simp [retr, h]

theorem glue_edge_bridge {V V' : Finset Λ} {ρ : Λ} (hρ : ρ ∈ V)
    (hint : ∀ x, x ∈ V → x ∈ V' → x = ρ) {G : SimpleGraph V} (hG : G.IsAcyclic)
    (G' : SimpleGraph V') {a b : V} (hab : G.Adj a b) :
    (G.map (embFin V) ⊔ G'.map (embFin V')).IsBridge s(a.val, b.val) := by
  rw [SimpleGraph.isBridge_iff]
  intro hr
  have hbr := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hG) hab
  rw [SimpleGraph.isBridge_iff] at hbr
  refine hbr ?_
  have := reach_weakHom (G' := G.deleteEdges {s(a, b)}) (retr V ρ hρ) ?_ hr
  · rwa [retr_of_mem hρ a.2, retr_of_mem hρ b.2] at this
  · intro p q hpq
    rw [SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj] at hpq
    obtain ⟨hpq, hne⟩ := hpq
    rcases hpq with h1 | h1
    · obtain ⟨p', q', hp'q', rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h1
      right
      simp only [embFin_apply]
      rw [retr_of_mem hρ p'.2, retr_of_mem hρ q'.2]
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hp'q', ?_⟩
      intro h
      apply hne
      rw [Set.mem_singleton_iff] at h ⊢
      have := congrArg (Sym2.map (embFin V)) h
      simpa [Sym2.map_mk, embFin] using this
    · left
      obtain ⟨p', q', _, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h1
      simp only [embFin_apply]
      rw [retr_of_mem_other hρ hint p'.2, retr_of_mem_other hρ hint q'.2]

variable (V₁ V₂ : Finset Λ)

theorem glue_isAcyclic {ρ : Λ} (hρ₁ : ρ ∈ V₁) (hρ₂ : ρ ∈ V₂)
    (hint : ∀ x, x ∈ V₁ → x ∈ V₂ → x = ρ) {F₁ : SimpleGraph V₁} {F₂ : SimpleGraph V₂}
    (h₁ : F₁.IsAcyclic) (h₂ : F₂.IsAcyclic) : (glue V₁ V₂ F₁ F₂).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  unfold glue at hxy ⊢
  rw [SimpleGraph.sup_adj] at hxy
  rcases hxy with hxy | hxy
  · obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hxy
    exact glue_edge_bridge hρ₁ hint h₁ F₂ hab
  · obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hxy
    rw [sup_comm]
    exact glue_edge_bridge hρ₂ (fun x h1 h2 => hint x h2 h1) h₂ F₁ hab

end

end ArborealDecay.Surgery
