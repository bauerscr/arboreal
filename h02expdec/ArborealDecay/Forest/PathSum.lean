module

public import ArborealDecay.Forest.Basic

/-!
# Path-sum identity (`eq:path-sum`)

Simple `x`–`z` paths are represented as elements of `(⊤ : SimpleGraph Λ).Path x z`, i.e. walks in
the complete graph on `Λ` together with a proof of `Walk.IsPath` (a `Fintype`, by Mathlib).
The event "`γ ⊆ F`" is `pathEvent γ F : ∀ e ∈ γ.1.edges, e ∈ F.edgeSet`.

* `arborealProb_reachable_eq_sum`: `P[x ↔ z] = ∑_γ P[γ ⊆ F]` (valid also for `x = z`, where the
  only path is the trivial one and both sides are `1`).
* `sum_arborealProb_pathEvent_le`: for any finite set `𝒫` of simple paths,
  `∑_{γ ∈ S} P[γ ⊆ F] ≤ P[x ↔ z]`.
-/

@[expose] public section

namespace ArborealDecay.Forest

noncomputable section

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The event that the simple path `γ` (in the complete graph) has all its edges in `F`. -/
def pathEvent {x z : Λ} (γ : (⊤ : SimpleGraph Λ).Path x z) (F : SimpleGraph Λ) : Prop :=
  ∀ e ∈ γ.1.edges, e ∈ F.edgeSet

/-- In a forest, at most one simple path is contained. -/
theorem pathEvent_unique {F : SimpleGraph Λ} (hF : F.IsAcyclic) {x z : Λ}
    {γ γ' : (⊤ : SimpleGraph Λ).Path x z} (h : pathEvent γ F) (h' : pathEvent γ' F) : γ = γ' := by
  have h1 : (γ.1.transfer F h).IsPath := γ.2.transfer h
  have h2 : (γ'.1.transfer F h').IsPath := γ'.2.transfer h'
  have := Subtype.ext_iff.1 ((hF.subsingleton_path x z).elim ⟨_, h1⟩ ⟨_, h2⟩)
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_support
  have h3 : (γ.1.transfer F h).support = (γ'.1.transfer F h').support :=
    congrArg SimpleGraph.Walk.support this
  exact (SimpleGraph.Walk.support_transfer (p := γ.1) (H := F) h).symm.trans
    (h3.trans (SimpleGraph.Walk.support_transfer (p := γ'.1) (H := F) h'))

/-- In a forest, `x ↔ z` iff some simple path is contained. -/
theorem reachable_iff_exists_pathEvent {F : SimpleGraph Λ} {x z : Λ} :
    F.Reachable x z ↔ ∃ γ : (⊤ : SimpleGraph Λ).Path x z, pathEvent γ F := by
  constructor
  · intro hr
    obtain ⟨q, hq⟩ := hr.exists_isPath
    have hsub : ∀ e ∈ q.edges, e ∈ (⊤ : SimpleGraph Λ).edgeSet :=
      fun e he => SimpleGraph.edgeSet_mono le_top (q.edges_subset_edgeSet he)
    refine ⟨⟨q.transfer ⊤ hsub, hq.transfer hsub⟩, ?_⟩
    intro e he
    rw [SimpleGraph.Walk.edges_transfer] at he
    exact q.edges_subset_edgeSet he
  · rintro ⟨γ, hγ⟩
    exact ⟨γ.1.transfer F hγ⟩

/-- Path-sum identity (`eq:path-sum`): `P[x ↔ z] = ∑_{γ} P[γ ⊆ F]`, the sum over all simple paths
`γ` from `x` to `z` in the complete graph. -/
theorem arborealProb_reachable_eq_sum {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (x z : Λ) :
    H02.arborealProb β hβ (fun F => F.Reachable x z) =
      ∑ γ : (⊤ : SimpleGraph Λ).Path x z, H02.arborealProb β hβ (pathEvent γ) := by
  rw [← arborealProb_exists_mem hβ (Finset.univ : Finset ((⊤ : SimpleGraph Λ).Path x z))
    pathEvent (fun F hF i _ j _ hi hj => pathEvent_unique hF hi hj)]
  refine arborealProb_congr hβ fun F _ => ?_
  rw [reachable_iff_exists_pathEvent]
  simp

/-- Subfamily bound (`prop:Simon-Lieb`): for any set `𝒫` of simple `x`–`u` paths,
`∑_{γ ∈ S} P[γ ⊆ F] ≤ P[x ↔ u]`. -/
theorem sum_arborealProb_pathEvent_le {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) {x u : Λ} (S : Finset ((⊤ : SimpleGraph Λ).Path x u)) :
    ∑ γ ∈ S, H02.arborealProb β hβ (pathEvent γ) ≤
      H02.arborealProb β hβ (fun F => F.Reachable x u) := by
  rw [← arborealProb_exists_mem hβ S pathEvent
    (fun F hF i _ j _ hi hj => pathEvent_unique hF hi hj)]
  refine arborealProb_mono hβ hβ0 fun F _ hF => ?_
  obtain ⟨γ, _, hγ⟩ := hF
  exact reachable_iff_exists_pathEvent.2 ⟨γ, hγ⟩

end

end ArborealDecay.Forest
