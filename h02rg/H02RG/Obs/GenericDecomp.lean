import Obs.GenericZVK

/-!
# The linear part of the generic `K_{j+1}` and the remainders

The generic versions of `Step.Decomp`: `LlinG` is `𝓛_{j+1}(U)` (`e:K-linear`), `LlinSG`,
`LlinLG` its contributions from small and large polymers, `R1G`, `R2G`, `R3G` the remainders
of `e:KminuscL`, and `K_{j+1} = 𝓛_{j+1} + 𝓡^1 + 𝓡^2 + 𝓡^3` (`KnextG_eq_decomp`).  The proof is
that of `Step.Knext_eq_decomp` and uses no hypotheses on the data.
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

section

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]
  (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)

/-- `e^{u_{j+1}(U)} e^{-(u+V)_{j+1}(U ∖ X)}`. -/
def prefG (U X : Finset (Lam d L N)) : R := PrefG j F U * ItPow j F (U \ X)

/-- The contribution to `𝓛_{j+1}(U)` from the polymers in `S`. -/
def LsumG (S : Finset (Finset (Lam d L N))) (U : Finset (Lam d L N)) : R :=
  open Classical in
  (∑ X ∈ S.filter (fun X => IsConn j X ∧ clo j X = U),
      prefG j F U X * A.E (A.θ (F.K X) - ∑ b ∈ blocks j X, A.θ (F.J b X))) +
    ∑ X ∈ S.filter (fun X => IsPolymer j X ∧ clo j X = U), prefG j F U X * A.E (dIPowG A j F X)

/-- `𝓛_{j+1}(U)` (`e:K-linear`). -/
def LlinG (U : Finset (Lam d L N)) : R := LsumG A j F univ U

/-- `𝓛_{j+1,𝒮}(U)`. -/
def LlinSG (U : Finset (Lam d L N)) : R := LsumG A j F (smallSets j) U

/-- `𝓛_{j+1,𝒫∖𝒮}(U)`. -/
def LlinLG (U : Finset (Lam d L N)) : R := LsumG A j F (univ \ smallSets j) U

/-- `𝓡^1(U)`: `|𝒳| = 1`, `X̌ = ∅`. -/
def R1G (U : Finset (Lam d L N)) : R :=
  open Classical in
  PrefG j F U * ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ItPow j F (U \ Xcal g.1) * A.E (JprodG A F g.1)

/-- `𝓡^2(U)`: `X_𝒳 ∪ X̌` has at least two components. -/
def R2G (U : Finset (Lam d L N)) : R :=
  open Classical in
  PrefG j F U * ∑ g ∈ (Gset j U).filter (fun g => 2 ≤ g.1.card + (Comp j g.2).card),
      ItPow j F (U \ (g.2 ∪ Xcal g.1)) *
        A.E ((KchkG A j F g.2 - if g.1 = ∅ then dIPowG A j F g.2 else 0) * JprodG A F g.1)

/-- `𝓡^3(U)`: `|𝒳| = 0`, `X̌` connected. -/
def R3G (U : Finset (Lam d L N)) : R :=
  open Classical in
  PrefG j F U * ∑ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      ItPow j F (U \ g.2) *
        A.E (KchkG A j F g.2 - A.θ (F.K g.2) - dIPowG A j F g.2 +
          ∑ b ∈ blocks j g.2, A.θ (F.J b g.2))

theorem KchkG_empty : KchkG A j F ∅ = 1 := by
  rw [KchkG, comp_empty, prod_empty]

theorem LlinG_eq (U : Finset (Lam d L N)) : LlinG A j F U = LlinSG A j F U + LlinLG A j F U := by
  have key : ∀ f : Finset (Lam d L N) → R,
      ∑ X, f X = ∑ X ∈ smallSets j, f X + ∑ X ∈ (smallSets j)ᶜ, f X :=
    fun f => (sum_add_sum_compl _ f).symm
  simp only [LlinG, LlinSG, LlinLG, LsumG, ← compl_eq_univ_sdiff, sum_filter]
  rw [key, key]
  abel

/-- `e:KminuscL`: `K_{j+1}(U) = 𝓛_{j+1}(U) + 𝓡^1(U) + 𝓡^2(U) + 𝓡^3(U)`. -/
theorem KnextG_eq_decomp (U : Finset (Lam d L N)) :
    KnextG A j F U = LlinG A j F U + R1G A j F U + R2G A j F U + R3G A j F U := by
  classical
  set e := PrefG j F U with he
  have h1 : (∑ X ∈ univ.filter (fun X => IsConn j X ∧ clo j X = U),
      prefG j F U X * A.E (A.θ (F.K X) - ∑ b ∈ blocks j X, A.θ (F.J b X))) =
      e * ∑ g ∈ Gset j U, if g.1 = ∅ ∧ IsConn j g.2 then ItPow j F (U \ g.2) *
        A.E (A.θ (F.K g.2) - ∑ b ∈ blocks j g.2, A.θ (F.J b g.2)) else 0 := by
    rw [← sum_filter, mul_sum]
    refine sum_nbij' (fun X => ((∅ : Finset ((Fin d → ℕ) × Finset (Lam d L N))), X))
      (fun g => g.2) ?_ ?_ ?_ ?_ ?_
    · intro X hX
      obtain ⟨-, hc, hU⟩ := mem_filter.1 hX
      exact mem_filter.2 ⟨mem_Gset_empty.2 ⟨hc.1, hU⟩, rfl, hc⟩
    · intro g hg
      obtain ⟨hg, h0, hc⟩ := mem_filter.1 hg
      rw [eq_empty_left_of_mem_Gset h0] at hg
      exact mem_filter.2 ⟨mem_univ _, hc, (mem_Gset_empty.1 hg).2⟩
    · intro X _; rfl
    · intro g hg
      exact (eq_empty_left_of_mem_Gset (mem_filter.1 hg).2.1).symm
    · intro X _
      rw [prefG, mul_assoc]
  have h2 : (∑ X ∈ univ.filter (fun X => IsPolymer j X ∧ clo j X = U),
      prefG j F U X * A.E (dIPowG A j F X)) =
      e * ∑ g ∈ Gset j U, if g.1 = ∅ then ItPow j F (U \ g.2) *
        A.E (dIPowG A j F g.2) else 0 := by
    rw [← sum_filter, mul_sum]
    refine sum_nbij' (fun X => ((∅ : Finset ((Fin d → ℕ) × Finset (Lam d L N))), X))
      (fun g => g.2) ?_ ?_ ?_ ?_ ?_
    · intro X hX
      obtain ⟨-, hc, hU⟩ := mem_filter.1 hX
      exact mem_filter.2 ⟨mem_Gset_empty.2 ⟨hc, hU⟩, rfl⟩
    · intro g hg
      obtain ⟨hg, h0⟩ := mem_filter.1 hg
      rw [eq_empty_left_of_mem_Gset h0] at hg
      exact mem_filter.2 ⟨mem_univ _, mem_Gset_empty.1 hg⟩
    · intro X _; rfl
    · intro g hg
      exact (eq_empty_left_of_mem_Gset (mem_filter.1 hg).2).symm
    · intro X _
      rw [prefG, mul_assoc]
  rw [LlinG, LsumG, h1, h2, KnextG, R1G, R2G, R3G, ← he, ← mul_add, ← mul_add, ← mul_add,
    ← mul_add]
  congr 1
  simp only [sum_filter, ← sum_add_distrib, KtermG, JprodG]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨X1, X2⟩ := g
  have hp : IsPolymer j X2 := (mem_Gset.1 hg).1
  simp only
  by_cases hA : X1 = ∅
  · subst hA
    simp only [card_empty, Xcal_empty, prod_empty, mul_one, union_empty, sdiff_empty, zero_add,
      true_and, if_true, zero_ne_one, false_and, if_false, add_zero]
    by_cases h0 : X2 = ∅
    · subst h0
      simp [KchkG_empty, dIPowG_empty, comp_empty, not_isConn_empty]
    · by_cases hc : IsConn j X2
      · have h2 : ¬ 2 ≤ (Comp j X2).card := by rw [(comp_card_eq_one_iff hp).2 hc]; omega
        simp only [hc, h2, if_true, if_false, map_add, map_sub]
        ring
      · have h2 : 2 ≤ (Comp j X2).card := by
          have := (comp_card_eq_zero_iff hp).not.2 h0
          have := (comp_card_eq_one_iff hp).not.2 hc
          omega
        simp only [hc, h2, if_true, if_false, zero_add, map_sub, add_zero]
        ring
  · simp only [hA, false_and, if_false, sub_zero, zero_add, add_zero]
    by_cases h1 : X1.card = 1 ∧ X2 = ∅
    · obtain ⟨h1, rfl⟩ := h1
      have h2 : ¬ 2 ≤ X1.card + (Comp j (∅ : Finset (Lam d L N))).card := by
        rw [h1, comp_empty]; simp
      simp [h1, comp_empty, KchkG_empty]
    · have h2 : 2 ≤ X1.card + (Comp j X2).card := by
        have h3 : X1.card ≠ 0 := fun h => hA (card_eq_zero.1 h)
        by_cases h0 : X2 = ∅
        · have h4 : X1.card ≠ 1 := fun h => h1 ⟨h, h0⟩
          omega
        · have := (comp_card_eq_zero_iff hp).not.2 h0
          omega
      simp only [h1, h2, if_true, if_false, zero_add]

end

end

end Obs.Gen
