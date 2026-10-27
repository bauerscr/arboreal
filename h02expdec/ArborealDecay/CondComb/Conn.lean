module

public import ArborealDecay.CondComb.Main

/-!
# The connected-terminal partition function

`Zc_eq`: `Z_c = w_ab Z_Γ + ∑_{i,j ∈ I} w_ai w_jb Z_Γ[i ↔ j, i ↮ ρ]`, by applying the first-edge
decomposition `sum_conn_eq` at `a` and then at `b`, and the forest bijection `sum_sep_eq`.
-/

@[expose] public section

namespace ArborealDecay.CondComb

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.Wiring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Translation of the middle event of the second decomposition to `SepS` and an event on `Γ`. -/
theorem midEvent_iff {a b : V} (hab : a ≠ b) (i j : {v : V // v ∉ ({a, b} : Finset V)})
    (F : SimpleGraph V) :
    ((¬ F.Reachable b j.1 ∧ F.Reachable j.1 i.1) ∧
        ¬ (F ⊔ SimpleGraph.edge b j.1).Reachable a i.1) ↔
      (SepS ({a, b} : Finset V) F ∧
        EvIJ a b i j (edgeQuot (collapse ({a, b} : Finset V)) F.edgeFinset)) := by
  have hs : (a ∈ ({a, b} : Finset V)) := by simp
  have hnone := reach_none_iff hs F i.2
  have hna : ∀ s ∈ ({a, b} : Finset V), s = a ∨ s = b := by simp
  rw [sepS_pair_iff hab, EvIJ]
  have hnex : (∃ s ∈ ({a, b} : Finset V), F.Reachable i.1 s) ↔
      (F.Reachable i.1 a ∨ F.Reachable i.1 b) := by simp
  constructor
  · rintro ⟨⟨hbj, hji⟩, hn⟩
    have h1 : ¬ F.Reachable a i.1 := fun h => hn (h.mono le_sup_left)
    have h2 : ¬ F.Reachable b i.1 := fun h => hbj (h.trans hji.symm)
    have h3 : ¬ F.Reachable a b := fun h =>
      hn ((h.mono le_sup_left).trans
        ((SimpleGraph.Adj.reachable (by
          rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
          exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, fun h => hbj (h ▸ SimpleGraph.Reachable.refl _)⟩)).trans
          (hji.mono le_sup_left)))
    have h4 : ¬ F.Reachable i.1 a ∧ ¬ F.Reachable i.1 b := ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
    have hnn : ¬ (edgeQuot (collapse ({a, b} : Finset V)) F.edgeFinset).Reachable
        (some i) none := by
      rw [hnone, hnex]; tauto
    refine ⟨h3, ?_, hnn⟩
    have := reach_some_iff hs F i.2 j.2 (by rw [hnex]; tauto)
    exact this.2 hji.symm
  · rintro ⟨h3, hA, hnn⟩
    rw [hnone, hnex] at hnn
    have hnn' : ¬ F.Reachable i.1 a ∧ ¬ F.Reachable i.1 b := by tauto
    have hij : F.Reachable i.1 j.1 :=
      (reach_some_iff hs F i.2 j.2 (by rw [hnex]; tauto)).1 hA
    refine ⟨⟨fun h => hnn'.2 (hij.trans h.symm |>.symm |>.symm), hij.symm⟩, ?_⟩
    intro hr
    rcases H02.reachable_sup_edge hr with h | ⟨h, _⟩ | ⟨_, h⟩
    · exact hnn'.1 h.symm
    · exact h3 h
    · exact hnn'.2 h.symm

theorem inner_eq {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {a b : V} (hab : a ≠ b)
    (i j : {v : V // v ∉ ({a, b} : Finset V)}) :
    ∑ F : SimpleGraph V with F.IsAcyclic ∧ ¬ F.Reachable b j.1 ∧ F.Reachable j.1 i.1,
        H02.forestWeight β hβ F *
          (if (F ⊔ SimpleGraph.edge b j.1).Reachable a i.1 then 0 else 1) =
      ∑ F' : SimpleGraph (GamV V a b) with F'.IsAcyclic ∧ EvIJ a b i j F',
        H02.forestWeight (gammaW β a b) (gammaW_symm hβ a b) F' := by
  have h := sum_sep_eq (S := ({a, b} : Finset V)) (s₀ := a) (by simp) hβ (EvIJ a b i j)
  unfold gammaW
  rw [← h, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases hac : F.IsAcyclic
  · have key := midEvent_iff hab i j F
    by_cases hE : SepS ({a, b} : Finset V) F ∧
        EvIJ a b i j (edgeQuot (collapse ({a, b} : Finset V)) F.edgeFinset)
    · have := key.2 hE
      simp [hac, hE, this.1, this.2]
    · have hn : ¬ ((¬ F.Reachable b j.1 ∧ F.Reachable j.1 i.1) ∧
          ¬ (F ⊔ SimpleGraph.edge b j.1).Reachable a i.1) := fun h => hE (key.1 h)
      by_cases h1 : ¬ F.Reachable b j.1 ∧ F.Reachable j.1 i.1
      · have h2 : (F ⊔ SimpleGraph.edge b j.1).Reachable a i.1 := by
          by_contra h2; exact hn ⟨h1, h2⟩
        simp [hac, hE, h1, h2]
      · simp [hac, hE, h1]
  · simp [hac]

end

end ArborealDecay.CondComb
