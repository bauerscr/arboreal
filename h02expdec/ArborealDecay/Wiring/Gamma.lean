module

public import ArborealDecay.Wiring.Star
public import ArborealDecay.Surgery

/-!
# `Γ = G/S` is a one-vertex union at `ρ`

If `S` separates `a` from `b` in the support graph of `β`, then `Γ = G/S` (vertex set
`Option {v // v ∉ S}`, weights `mapW β (collapse S)`) is a one-vertex union at `ρ = none` of a piece
containing `a` and a piece containing `b`.
-/

@[expose] public section

namespace ArborealDecay.Wiring

noncomputable section

open Finset Classical ArborealDecay.Surgery

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The support graph of the weights `β`: `i ~ j` iff `i ≠ j` and `β i j ≠ 0`. -/
def suppGraph (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) : SimpleGraph V where
  Adj i j := i ≠ j ∧ β i j ≠ 0
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [hβ]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem mapW_some_some {β : V → V → ℝ} {S : Finset V} (u v : {v // v ∉ S}) (huv : u ≠ v) :
    mapW β (collapse S) (some u) (some v) = β u.1 v.1 := by
  have hfib : ∀ u : {v // v ∉ S}, (Finset.univ.filter fun x => collapse S x = some u) = {u.1} := by
    intro u
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_cases hx : x ∈ S
      · rw [collapse_of_mem hx] at h; exact absurd h (by simp)
      · rw [collapse_of_notMem hx] at h
        exact congrArg Subtype.val (Option.some_injective _ h)
    · intro h
      subst h
      exact collapse_of_notMem u.2
  unfold mapW
  rw [if_neg (by simpa using huv), hfib u, hfib v]
  simp

/-- Membership in the first piece: `ρ`, or a vertex reachable from `a` away from `S`. -/
def inV₁ {S : Finset V} (H : SimpleGraph {v // v ∉ S}) (a₀ : {v // v ∉ S}) :
    Option {v // v ∉ S} → Prop
  | none => True
  | some v => H.Reachable a₀ v

/-- Membership in the second piece. -/
def inV₂ {S : Finset V} (H : SimpleGraph {v // v ∉ S}) (a₀ : {v // v ∉ S}) :
    Option {v // v ∉ S} → Prop
  | none => True
  | some v => ¬ H.Reachable a₀ v

theorem gamma_structure {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {S : Finset V} {a b : V}
    (ha : a ∉ S) (hb : b ∉ S)
    (hsep : ∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) :
    ∃ V₁ V₂ : Finset (Option {v // v ∉ S}),
      OneVertexUnion V₁ V₂ none ∧
      (∀ u v, u ∈ V₁ → u ≠ none → v ∈ V₂ → v ≠ none →
        mapW β (collapse S) u v = 0) ∧
      some ⟨a, ha⟩ ∈ V₁ ∧ some ⟨b, hb⟩ ∈ V₂ := by
  set H : SimpleGraph {v // v ∉ S} := (suppGraph β hβ).comap Subtype.val with hH
  set a₀ : {v // v ∉ S} := ⟨a, ha⟩ with ha₀
  refine ⟨Finset.univ.filter (inV₁ H a₀), Finset.univ.filter (inV₂ H a₀), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases x with _ | v
    · exact Or.inl trivial
    · by_cases h : H.Reachable a₀ v
      · exact Or.inl h
      · exact Or.inr h
  · intro x h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases x with _ | v
    · rfl
    · exact absurd h1 h2
  · simp [inV₁]
  · simp [inV₂]
  · intro u v hu hu' hv hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    rcases u with _ | u
    · exact absurd rfl hu'
    rcases v with _ | v
    · exact absurd rfl hv'
    have hne : u ≠ v := by
      rintro rfl
      exact hv hu
    rw [mapW_some_some u v hne]
    by_contra hne0
    apply hv
    refine hu.trans (SimpleGraph.Adj.reachable ?_)
    exact (show u.1 ≠ v.1 ∧ β u.1 v.1 ≠ 0 from ⟨fun h => hne (Subtype.ext h), hne0⟩)
  · simp [inV₁]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, inV₂]
    intro hr
    obtain ⟨p⟩ := hr
    let q : (suppGraph β hβ).Walk a b := p.map (SimpleGraph.Hom.comap Subtype.val (suppGraph β hβ))
    obtain ⟨v, hv, hvS⟩ := hsep q
    have hv' : v ∈ p.support.map (SimpleGraph.Hom.comap Subtype.val (suppGraph β hβ)) := by
      rw [← SimpleGraph.Walk.support_map]; exact hv
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hv'
    exact x.2 hvS

end

end ArborealDecay.Wiring
