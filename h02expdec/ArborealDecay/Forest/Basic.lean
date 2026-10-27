module

public import ArborealDecay.H02.Tree

/-!
# Basic combinatorics of arboreal gas events

Monotonicity and finite additivity of `H02.arborealProb` in the event.
Events are predicates on `SimpleGraph Λ`; only their values on acyclic graphs matter.
-/

@[expose] public section

namespace ArborealDecay.Forest

noncomputable section

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- Monotonicity in the event (it suffices that `P → Q` on forests). -/
theorem arborealProb_mono {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {P Q : SimpleGraph Λ → Prop} (h : ∀ F : SimpleGraph Λ, F.IsAcyclic → P F → Q F) :
    H02.arborealProb β hβ P ≤ H02.arborealProb β hβ Q := by
  unfold H02.arborealProb
  refine div_le_div_of_nonneg_right ?_ (H02.Zforest_pos hβ hβ0).le
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun F _ _ => H02.forestWeight_nonneg hβ hβ0 F
  intro F hF
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF ⊢
  exact ⟨hF.1, h F hF.1 hF.2⟩

/-- Finite additivity: the probability of a union of events that are pairwise disjoint on
forests is the sum of the probabilities. -/
theorem arborealProb_exists_mem {ι : Type*} {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (s : Finset ι) (P : ι → SimpleGraph Λ → Prop)
    (hdisj : ∀ F : SimpleGraph Λ, F.IsAcyclic → ∀ i ∈ s, ∀ j ∈ s, P i F → P j F → i = j) :
    H02.arborealProb β hβ (fun F => ∃ i ∈ s, P i F) = ∑ i ∈ s, H02.arborealProb β hβ (P i) := by
  unfold H02.arborealProb
  rw [← Finset.sum_div]
  congr 1
  have h1 : ∀ i, (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ P i F, H02.forestWeight β hβ F) =
      ∑ F : SimpleGraph Λ with F.IsAcyclic,
        if P i F then H02.forestWeight β hβ F else 0 := by
    intro i
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h1 : F.IsAcyclic <;> by_cases h2 : P i F <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases hF : F.IsAcyclic
  · simp only [hF, true_and, if_true]
    by_cases hex : ∃ i ∈ s, P i F
    · obtain ⟨i, hi, hPi⟩ := hex
      rw [if_pos ⟨i, hi, hPi⟩, Finset.sum_eq_single i]
      · simp [hPi]
      · intro j hj hji
        have : ¬ P j F := fun hj' => hji (hdisj F hF j hj i hi hj' hPi)
        simp [this]
      · intro h; exact absurd hi h
    · rw [if_neg hex]
      symm; refine Finset.sum_eq_zero fun i hi => ?_
      have : ¬ P i F := fun h => hex ⟨i, hi, h⟩
      simp [this]
  · simp [hF]

/-- Additivity over two events that are disjoint on forests. -/
theorem arborealProb_or {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    {P Q : SimpleGraph Λ → Prop} (h : ∀ F : SimpleGraph Λ, F.IsAcyclic → P F → Q F → False) :
    H02.arborealProb β hβ (fun F => P F ∨ Q F) =
      H02.arborealProb β hβ P + H02.arborealProb β hβ Q := by
  have := arborealProb_exists_mem hβ (Finset.univ : Finset Bool)
    (fun b F => if b then P F else Q F) (by
      intro F hF i _ j _ hi hj
      cases i <;> cases j <;> simp_all)
  simpa [Fintype.sum_bool, or_comm] using this

/-- The probability only depends on the event restricted to forests. -/
theorem arborealProb_congr {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    {P Q : SimpleGraph Λ → Prop} (h : ∀ F : SimpleGraph Λ, F.IsAcyclic → (P F ↔ Q F)) :
    H02.arborealProb β hβ P = H02.arborealProb β hβ Q := by
  unfold H02.arborealProb
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h F h1).1 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h F h1).2 h2⟩

end

end ArborealDecay.Forest
