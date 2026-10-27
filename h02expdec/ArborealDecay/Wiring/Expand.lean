module

public import Mathlib

/-!
# Expansion of a product over blocks

For a map `c : σ → K` and elements `x : σ → R` of a commutative semiring,
`∏_{T ∈ B} (1 + ∑_{u ∈ s, c u = T} x u) = ∑_{U ⊆ s, c injective on U, c U ⊆ B} ∏_{u ∈ U} x u`.
This is the monomial expansion of `∏_T (1 + ∑_{i ∈ T} X i)` used for the forest polynomial.
-/

@[expose] public section

namespace ArborealDecay.Wiring

open Finset

theorem prod_one_add_sum_fiber {σ K R : Type*} [CommSemiring R] [DecidableEq σ] [DecidableEq K]
    (c : σ → K) (x : σ → R) (s : Finset σ) :
    ∀ B : Finset K, ∏ T ∈ B, (1 + ∑ u ∈ s with c u = T, x u) =
      ∑ U ∈ s.powerset, if (Set.InjOn c ↑U ∧ ∀ u ∈ U, c u ∈ B) then ∏ u ∈ U, x u else 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro B
    simp
  | @insert u0 s hu0 ih =>
    intro B
    rw [Finset.sum_powerset_insert hu0]
    have hsum : ∀ T, ∑ u ∈ (insert u0 s) with c u = T, x u =
        (if c u0 = T then x u0 else 0) + ∑ u ∈ s with c u = T, x u := by
      intro T
      rw [Finset.filter_insert]
      by_cases h : c u0 = T
      · rw [if_pos h, if_pos h, Finset.sum_insert (by simp [hu0])]
      · rw [if_neg h, if_neg h, zero_add]
    simp only [hsum]
    by_cases hB : c u0 ∈ B
    · -- second sum
      have h2 : ∑ t ∈ s.powerset, (if (Set.InjOn c ↑(insert u0 t) ∧ ∀ u ∈ insert u0 t, c u ∈ B)
          then ∏ u ∈ insert u0 t, x u else 0) =
          x u0 * ∏ T ∈ B.erase (c u0), (1 + ∑ u ∈ s with c u = T, x u) := by
        rw [ih, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have hts : u0 ∉ t := fun h => hu0 (Finset.mem_powerset.1 ht h)
        rw [Finset.prod_insert hts]
        have hiff : (Set.InjOn c ↑(insert u0 t) ∧ ∀ u ∈ insert u0 t, c u ∈ B) ↔
            (Set.InjOn c ↑t ∧ ∀ u ∈ t, c u ∈ B.erase (c u0)) := by
          constructor
          · rintro ⟨hinj, hmem⟩
            refine ⟨hinj.mono (by simp), fun u hu => ?_⟩
            refine Finset.mem_erase.2 ⟨fun h => ?_, hmem u (Finset.mem_insert_of_mem hu)⟩
            have := hinj (by simp [hu]) (by simp) h
            exact hts (this ▸ hu)
          · rintro ⟨hinj, hmem⟩
            refine ⟨?_, fun u hu => ?_⟩
            · rw [Finset.coe_insert]
              refine (Set.injOn_insert (by simpa using hts)).2 ⟨hinj, ?_⟩
              rintro ⟨y, hy, hyc⟩
              exact (Finset.mem_erase.1 (hmem y hy)).1 hyc
            · rcases Finset.mem_insert.1 hu with rfl | hu
              · exact hB
              · exact (Finset.mem_erase.1 (hmem u hu)).2
        by_cases hc : (Set.InjOn c ↑t ∧ ∀ u ∈ t, c u ∈ B.erase (c u0))
        · rw [if_pos (hiff.2 hc), if_pos hc]
        · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, mul_zero]
      rw [h2]
      have h1 := ih B
      have hprod : ∏ T ∈ B, (1 + ((if c u0 = T then x u0 else 0) + ∑ u ∈ s with c u = T, x u)) =
          ∏ T ∈ B, (1 + ∑ u ∈ s with c u = T, x u) +
            x u0 * ∏ T ∈ B.erase (c u0), (1 + ∑ u ∈ s with c u = T, x u) := by
        rw [← Finset.mul_prod_erase B _ hB, ← Finset.mul_prod_erase B
          (fun T => 1 + ∑ u ∈ s with c u = T, x u) hB]
        have : ∏ T ∈ B.erase (c u0), (1 + ((if c u0 = T then x u0 else 0) +
            ∑ u ∈ s with c u = T, x u)) =
            ∏ T ∈ B.erase (c u0), (1 + ∑ u ∈ s with c u = T, x u) := by
          refine Finset.prod_congr rfl fun T hT => ?_
          rw [if_neg (Finset.ne_of_mem_erase hT).symm, zero_add]
        rw [this]
        simp only [if_true]
        ring
      rw [hprod, h1]
    · have h2 : ∑ t ∈ s.powerset, (if (Set.InjOn c ↑(insert u0 t) ∧ ∀ u ∈ insert u0 t, c u ∈ B)
          then ∏ u ∈ insert u0 t, x u else 0) = 0 := by
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [if_neg]
        rintro ⟨_, h⟩
        exact hB (h u0 (Finset.mem_insert_self _ _))
      rw [h2, add_zero, ← ih B]
      refine Finset.prod_congr rfl fun T hT => ?_
      have : c u0 ≠ T := fun h => hB (h ▸ hT)
      rw [if_neg this, zero_add]

end ArborealDecay.Wiring
