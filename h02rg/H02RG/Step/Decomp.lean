import Step.ZVK

/-!
# The linear part of `K_{j+1}` and the remainders (Section `sec:step`)

* `Llin` is the leading part `𝓛_{j+1}(U)` (`e:K-linear`); `LlinS`, `LlinL` its contributions
  from small and large polymers (`e:K-linear-split`).
* `R1`, `R2`, `R3` are the remainders `𝓡^1, 𝓡^2, 𝓡^3` of `e:KminuscL`, and
  `K_{j+1} = 𝓛_{j+1} + 𝓡^1 + 𝓡^2 + 𝓡^3` (`Knext_eq_decomp`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

section

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)

/-- `e^{-V_{j+1}(U ∖ X)} e^{u_{j+1}|X|} = e^{u_{j+1}|U|} e^{-(u+V)_{j+1}(U ∖ X)}`. -/
def pref (U X : Finset (Lam d L N)) : EvR (Lam d L N) :=
  Complex.exp ((uVnext j C V K).1 * U.card) • InextPow j C V K (U \ X)

/-- The contribution to `𝓛_{j+1}(U)` from the polymers in `S`. -/
def Lsum (S : Finset (Finset (Lam d L N))) (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  (∑ X ∈ S.filter (fun X => IsConn j X ∧ clo j X = U),
      pref j C V K U X * ECE C (thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X))) +
    ∑ X ∈ S.filter (fun X => IsPolymer j X ∧ clo j X = U), pref j C V K U X * ECE C (dIPow j C V K X)

/-- `𝓛_{j+1}(U)` (`e:K-linear`). -/
def Llin (U : Finset (Lam d L N)) : EvR (Lam d L N) := Lsum j C V K univ U

/-- `𝓛_{j+1,𝒮}(U)`. -/
def LlinS (U : Finset (Lam d L N)) : EvR (Lam d L N) := Lsum j C V K (smallSets j) U

/-- `𝓛_{j+1,𝒫∖𝒮}(U)`. -/
def LlinL (U : Finset (Lam d L N)) : EvR (Lam d L N) := Lsum j C V K (univ \ smallSets j) U

/-- `∏_{(B,X) ∈ 𝒳} θ J(B, X)`. -/
def Jprod (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) : EvR (Lam d L N ⊕ Lam d L N) :=
  ∏ p ∈ 𝒳, thetaE (Jb j K p.1 p.2)

/-- `𝓡^1(U)`: `|𝒳| = 1`, `X̌ = ∅`. -/
def R1 (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  Complex.exp ((uVnext j C V K).1 * U.card) •
    ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      InextPow j C V K (U \ Xcal g.1) * ECE C (Jprod j K g.1)

/-- `𝓡^2(U)`: `X_𝒳 ∪ X̌` has at least two components. -/
def R2 (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  Complex.exp ((uVnext j C V K).1 * U.card) •
    ∑ g ∈ (Gset j U).filter (fun g => 2 ≤ g.1.card + (Comp j g.2).card),
      InextPow j C V K (U \ (g.2 ∪ Xcal g.1)) *
        ECE C ((Kchk j C V K g.2 - if g.1 = ∅ then dIPow j C V K g.2 else 0) * Jprod j K g.1)

/-- `𝓡^3(U)`: `|𝒳| = 0`, `X̌` connected. -/
def R3 (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  Complex.exp ((uVnext j C V K).1 * U.card) •
    ∑ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      InextPow j C V K (U \ g.2) *
        ECE C (Kchk j C V K g.2 - thetaE (K g.2) - dIPow j C V K g.2 +
          ∑ b ∈ blocks j g.2, thetaE (Jb j K b g.2))

end

section Aux

variable {j : ℕ}

theorem comp_card_eq_zero_iff {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    (Comp j X).card = 0 ↔ X = ∅ := by
  constructor
  · intro h
    rw [← biUnion_comp hX, card_eq_zero.1 h, biUnion_empty]
  · rintro rfl
    rw [comp_empty, card_empty]

theorem comp_card_eq_one_iff {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    (Comp j X).card = 1 ↔ IsConn j X := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := card_eq_one.1 h
    have hXa : X = a := by rw [← biUnion_comp hX, ha, singleton_biUnion, id]
    rw [hXa]
    exact isConn_of_mem_comp hX (ha ▸ mem_singleton_self a)
  · intro h
    rw [comp_of_isConn h, card_singleton]

theorem not_isConn_empty : ¬ IsConn j (∅ : Finset (Lam d L N)) := fun h => by
  have := (comp_card_eq_one_iff (isPolymer_empty j)).2 h
  rw [comp_empty, card_empty] at this
  exact zero_ne_one this

@[simp] theorem Xcal_empty : Xcal (∅ : Finset ((Fin d → ℕ) × Finset (Lam d L N))) = ∅ := rfl

@[simp] theorem Bbox_empty : Bbox j (∅ : Finset ((Fin d → ℕ) × Finset (Lam d L N))) = ∅ := rfl

theorem Kchk_empty (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N) :
    Kchk j C V K ∅ = 1 := by
  rw [Kchk, comp_empty, prod_empty]

theorem not_touch_empty_left (X : Finset (Lam d L N)) : ¬ Touch ∅ X := by
  rintro ⟨x, hx, -⟩
  exact notMem_empty x hx

theorem mem_Gset {U : Finset (Lam d L N)}
    {g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)} :
    g ∈ Gset j U ↔ GCond j U g := by
  simp only [Gset, mem_filter, mem_product, mem_powerset, mem_Pj, subset_univ, true_and]
  exact ⟨And.right, fun h => ⟨⟨h.2.1, h.1⟩, h⟩⟩

/-- `(∅, X) ∈ 𝒢(U)` iff `X` is a polymer with closure `U`. -/
theorem mem_Gset_empty {U X : Finset (Lam d L N)} :
    ((∅, X) : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)) ∈ Gset j U ↔
      IsPolymer j X ∧ clo j X = U := by
  rw [mem_Gset, GCond]
  simp only [empty_subset, notMem_empty, IsEmpty.forall_iff, implies_true, true_and, Xcal_empty,
    Bbox_empty, union_empty, not_touch_empty_left, not_false_eq_true]

theorem eq_empty_left_of_mem_Gset
    {g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)} (h : g.1 = ∅) :
    g = (∅, g.2) :=
  Prod.ext h rfl

end Aux

theorem Llin_eq {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    (U : Finset (Lam d L N)) : Llin j C V K U = LlinS j C V K U + LlinL j C V K U := by
  have key : ∀ f : Finset (Lam d L N) → EvR (Lam d L N),
      ∑ X, f X = ∑ X ∈ smallSets j, f X + ∑ X ∈ (smallSets j)ᶜ, f X :=
    fun f => (sum_add_sum_compl _ f).symm
  simp only [Llin, LlinS, LlinL, Lsum, ← compl_eq_univ_sdiff, sum_filter]
  rw [key, key]
  abel

/-- `e:KminuscL`: `K_{j+1}(U) = 𝓛_{j+1}(U) + 𝓡^1(U) + 𝓡^2(U) + 𝓡^3(U)`. -/
theorem Knext_eq_decomp {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup)
    (K : Act d L N) (U : Finset (Lam d L N)) :
    Knext j C V K U = Llin j C V K U + R1 j C V K U + R2 j C V K U + R3 j C V K U := by
  classical
  set e := Complex.exp ((uVnext j C V K).1 * U.card) with he
  have h1 : (∑ X ∈ univ.filter (fun X => IsConn j X ∧ clo j X = U),
      pref j C V K U X * ECE C (thetaE (K X) - ∑ b ∈ blocks j X, thetaE (Jb j K b X))) =
      e • ∑ g ∈ Gset j U, if g.1 = ∅ ∧ IsConn j g.2 then InextPow j C V K (U \ g.2) *
        ECE C (thetaE (K g.2) - ∑ b ∈ blocks j g.2, thetaE (Jb j K b g.2)) else 0 := by
    rw [← sum_filter, smul_sum]
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
      rw [pref, smul_mul_assoc]
  have h2 : (∑ X ∈ univ.filter (fun X => IsPolymer j X ∧ clo j X = U),
      pref j C V K U X * ECE C (dIPow j C V K X)) =
      e • ∑ g ∈ Gset j U, if g.1 = ∅ then InextPow j C V K (U \ g.2) *
        ECE C (dIPow j C V K g.2) else 0 := by
    rw [← sum_filter, smul_sum]
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
      rw [pref, smul_mul_assoc]
  rw [Llin, Lsum, h1, h2, Knext, R1, R2, R3, ← he, ← smul_add, ← smul_add, ← smul_add,
    ← smul_add]
  congr 1
  simp only [sum_filter, ← sum_add_distrib, Jprod]
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
      simp [Kchk_empty, dIPow_empty, comp_empty, not_isConn_empty]
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
      simp [h1, comp_empty, Kchk_empty]
    · have h2 : 2 ≤ X1.card + (Comp j X2).card := by
        have h3 : X1.card ≠ 0 := fun h => hA (card_eq_zero.1 h)
        by_cases h0 : X2 = ∅
        · have h4 : X1.card ≠ 1 := fun h => h1 ⟨h, h0⟩
          omega
        · have := (comp_card_eq_zero_iff hp).not.2 h0
          omega
      simp only [h1, h2, if_true, if_false, zero_add]

end

end Step
