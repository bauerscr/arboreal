module

public import ArborealDecay.SimonLieb.Main
public import ArborealDecay.ForestPoly

/-!
# Unconditional versions

The stability input `hstab` is discharged by `ForestPoly.forestPolynomial_isRealStable`
(note `lem:PG-stable`); the local `forestPolynomial` agrees with `ForestPoly.forestPolynomial`
(`forestPolynomial_eq_forestPoly`; the two bodies are identical up to instances).

* `incident_NC` (`prop:incident-NC`), `two_trees` (`lem:two-trees`),
  `simon_lieb` (`prop:Simon-Lieb`).
-/

@[expose] public section

namespace ArborealDecay.SimonLieb

universe u

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

theorem forestPolynomial_eq_forestPoly {U : Type u} [Fintype U] [DecidableEq U]
    (β : U → U → ℝ) (hβ : ∀ i j, β i j = β j i) :
    forestPolynomial β hβ = ForestPoly.forestPolynomial β hβ := by
  unfold forestPolynomial ForestPoly.forestPolynomial
  refine Finset.sum_congr (by ext F; simp) fun F _ => ?_
  congr! 3

/-- The stability input, proved. -/
theorem forestPolynomial_stable :
    ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0 := by
  intro U _ _ β hβ hβ0
  rw [forestPolynomial_eq_forestPoly]
  exact ForestPoly.forestPolynomial_isRealStable β hβ hβ0

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- **Incident-edge negative correlation** (`prop:incident-NC`, conditional form). -/
theorem incident_NC {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (A : SimpleGraph Λ) (hA : A.IsAcyclic) (p i q j : Λ) (hpq : A.Reachable p q)
    (hef : s(p, i) ≠ s(q, j)) :
    H02.arborealProb β hβ (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet ∧ s(q, j) ∈ F.edgeSet) *
        H02.arborealProb β hβ (fun F => A ≤ F) ≤
      H02.arborealProb β hβ (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet) *
        H02.arborealProb β hβ (fun F => A ≤ F ∧ s(q, j) ∈ F.edgeSet) :=
  incident_NC_of_stable forestPolynomial_stable hβ hβ0 A hA p i q j hpq hef

/-- **Two rooted trees** (`lem:two-trees`), for edge-disjoint `A`, `B` whose edges lie in the
component of `r` (in particular two edge-disjoint trees sharing `r`). -/
theorem two_trees {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (r : Λ) (A B : SimpleGraph Λ) (hA : ∀ u v, A.Adj u v → A.Reachable r u)
    (hB : ∀ u v, B.Adj u v → B.Reachable r u) (hAB : Disjoint A.edgeSet B.edgeSet) :
    H02.arborealProb β hβ (fun F => A ⊔ B ≤ F) ≤
      H02.arborealProb β hβ (fun F => A ≤ F) * H02.arborealProb β hβ (fun F => B ≤ F) :=
  two_trees_of_stable hβ hβ0 forestPolynomial_stable r A B hA hB hAB

theorem reachable_of_isTree_induce_support {A : SimpleGraph Λ}
    (hT : (A.induce A.support).IsTree) {r : Λ} (hr : r ∈ A.support) :
    ∀ u v, A.Adj u v → A.Reachable r u := by
  intro u v huv
  have hu : u ∈ A.support := ⟨v, huv⟩
  exact (hT.connected.preconnected ⟨r, hr⟩ ⟨u, hu⟩).map (SimpleGraph.Embedding.induce _).toHom

/-- **Two rooted trees** (`lem:two-trees`) with the hypotheses of the note: `A`, `B` are trees
on their supports, edge-disjoint, sharing exactly the vertex `r`, with `A ∪ B` a forest.
(Only connectivity of the supports, `r` in both supports, and edge-disjointness are used.) -/
theorem two_trees_paper {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (r : Λ) (A B : SimpleGraph Λ) (hA : (A.induce A.support).IsTree)
    (hB : (B.induce B.support).IsTree) (hAB : Disjoint A.edgeSet B.edgeSet)
    (hshare : A.support ∩ B.support = {r}) (_hacyc : (A ⊔ B).IsAcyclic) :
    H02.arborealProb β hβ (fun F => A ⊔ B ≤ F) ≤
      H02.arborealProb β hβ (fun F => A ≤ F) * H02.arborealProb β hβ (fun F => B ≤ F) := by
  have hr : r ∈ A.support ∩ B.support := by rw [hshare]; rfl
  exact two_trees hβ hβ0 r A B (reachable_of_isTree_induce_support hA hr.1)
    (reachable_of_isTree_induce_support hB hr.2) hAB

/-- **Global Simon–Lieb inequality** (`prop:Simon-Lieb`). -/
theorem simon_lieb {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (D : Finset Λ) (x z : Λ) (hx : x ∈ D) (hz : z ∉ D) :
    H02.arborealProb β hβ (fun F => F.Reachable x z) ≤
      ∑ u ∈ D, ∑ v ∈ Dᶜ, if u ≠ v ∧ β u v ≠ 0 then
        H02.arborealProb β hβ (fun F => F.Adj u v) *
          H02.arborealProb β hβ (fun F => F.Reachable x u) *
          H02.arborealProb β hβ (fun F => F.Reachable v z) else 0 :=
  simon_lieb_of_stable forestPolynomial_stable hβ hβ0 D x z hx hz

end

end ArborealDecay.SimonLieb
