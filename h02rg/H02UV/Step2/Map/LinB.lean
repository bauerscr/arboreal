import Step2.Map.Lin
import Step.EstSmall

/-!
# The linear part `𝓛(K)` as a sum of `(1 - Loc)` terms

For `j + 1 < N` (`Llin2_eq`):

  `𝓛(K)(U) = ∑_{X ∈ 𝒮_j, \bar X = U} 𝔼θ (1 - Loc_X) K(X) + ∑_{X ∈ 𝒞_j ∖ 𝒮_j, \bar X = U} 𝔼θ K(X)`,

by the cancellation `∑_X J(B, X) = 0` (`e:J-zero`), the additivity of `Loc_{X,Y}` in `Y`, and
`-J(B, B) - Q(B) = -Loc_{B,B} K(B)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### `∑_X J(B, X) = 0` -/

section JZero

variable {j : ℕ}

theorem J2_sum_zero (K : Act d L N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X), J2 j K b X = 0 := by
  classical
  by_cases hN : j + 1 < N
  · have hBs := isSmall_blockSet_of_mem hb
    have hBm : blockSet j b ∈ (smallSets (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X) := mem_filter.2 ⟨mem_smallSets.2 hBs, subset_rfl⟩
    rw [← add_sum_erase _ _ hBm, J2, if_pos ⟨hN, hBs, subset_rfl⟩, if_pos rfl,
      neg_add_eq_zero]
    refine sum_congr ?_ fun Y hY => ?_
    · ext Y; simp only [mem_erase, mem_filter]; tauto
    · obtain ⟨hne, hY'⟩ := mem_erase.1 hY
      obtain ⟨hYs, hBY⟩ := mem_filter.1 hY'
      rw [J2, if_pos ⟨hN, mem_smallSets.1 hYs, hBY⟩, if_neg hne]
  · exact sum_eq_zero fun X _ => by rw [J2, if_neg (fun h => hN h.1)]

theorem J2prod_sum (K : Act d L N) (U : Finset (Lam d L N)) :
    ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ∏ p ∈ g.1, thetaE (J2 j K p.1 p.2) = 0 := by
  classical
  set P1 := (pairsU (L := L) (N := N) j).filter
    (fun p => clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U)
  have hbij : ∑ p ∈ P1, thetaE (J2 j K p.1 p.2) =
      ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
        ∏ p ∈ g.1, thetaE (J2 j K p.1 p.2) := by
    refine sum_bij (fun p _ => (({p} : Finset _), (∅ : Finset (Lam d L N)))) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      refine mem_filter.2 ⟨mem_Gset.2 ⟨isPolymer_empty j, singleton_subset_iff.2 hp1, ?_, ?_, ?_,
        ?_⟩, card_singleton p, rfl⟩
      · intro a ha b hb _; rw [mem_singleton.1 ha, mem_singleton.1 hb]
      · intro a ha b hb hne
        exact absurd (by rw [mem_singleton.1 ha, mem_singleton.1 hb]) hne
      · exact fun h => not_touch_empty_left _ (touch_symm h)
      · simpa [Bbox] using hp2
    · intro a _ b _ e
      simpa using congrArg Prod.fst e
    · intro g hg
      obtain ⟨hg, h1, h2⟩ := mem_filter.1 hg
      obtain ⟨p, hp⟩ := card_eq_one.1 h1
      obtain ⟨-, hsub, -, -, -, hclo⟩ := mem_Gset'.1 hg
      refine ⟨p, mem_filter.2 ⟨singleton_subset_iff.1 (hp ▸ hsub), ?_⟩, ?_⟩
      · rw [hp, h2] at hclo; simpa [Bbox] using hclo
      · exact Prod.ext hp.symm h2.symm
    · intro p _
      rw [prod_singleton]
  rw [← hbij, ← map_sum]
  have h0 : ∑ p ∈ P1, J2 j K p.1 p.2 = 0 := by
    have eP : P1 = (blockIdx (L := L) (N := N) j ×ˢ smallSets (L := L) (N := N) j).filter
        (fun p => blockSet j p.1 ⊆ p.2 ∧
          clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U) := by
      ext p; simp [P1, pairsU, and_assoc]
    rw [eP, sum_filter, sum_product]
    refine sum_eq_zero fun b hb => ?_
    by_cases hc : clo j (nbhd j (blockSet (L := L) (N := N) j b)) = U
    · simp only [hc, and_true]
      rw [← sum_filter]
      exact J2_sum_zero K hb
    · simp [hc]
  rw [h0, map_zero]

end JZero

/-! ### Additivity of `Loc_{X,Y}` in `Y` -/

/-- The density of `Loc_{X,·} F`. -/
def locDen (X : Finset (Lam d L N)) (F : Alg d L N) (x : Lam d L N) : Alg d L N :=
  (ε F / X.card) • (1 : Alg d L N) + ∑ M, locCoef X F M • monoAt M x +
    ∑ i, ∑ k, (mu4 (base X) i k F / X.card) • mono4s i k x

theorem Loc2XY_eq_sum (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Loc2sXY X Y F = ∑ x ∈ Y, locDen X F x := by
  simp only [Loc2sXY, LocXY, Loc4sXY, monoSet, mono4sSet, locDen, sum_add_distrib, smul_sum,
    sum_const]
  rw [sum_comm (s := Y) (t := (univ : Finset (Mono d)))]
  congr 1
  · congr 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1; ring
  · calc ∑ i, ∑ k, ∑ x ∈ Y, (mu4 (base X) i k F / X.card) • mono4s i k x
        = ∑ i, ∑ x ∈ Y, ∑ k, (mu4 (base X) i k F / X.card) • mono4s i k x :=
          sum_congr rfl fun i _ => sum_comm
      _ = _ := sum_comm

theorem Loc2E_sum_blocks {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (F : EvR (Lam d L N)) :
    ∑ b ∈ blocks j X, Loc2E X (blockSet j b) F = Loc2E X X F := by
  refine Subtype.ext ?_
  simp only [AddSubmonoidClass.coe_finsetSum, coe_Loc2E, Loc2XY_eq_sum]
  have := sum_biUnion (s := blocks j X) (t := blockSet j)
    (fun b _ b' _ hne => blockSet_disjoint hne) (f := locDen X (F : Alg d L N))
  rw [biUnion_blocks hX] at this
  exact this.symm

/-! ### The identity -/

theorem eq_blockSet_of_nb_one {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    {b : Fin d → ℕ} (hb : blocks j X = {b}) : X = blockSet j b := by
  rw [← biUnion_blocks hX, hb, singleton_biUnion]

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : Act d L N)

theorem Q2_split (hN : j + 1 < N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Q2 j K b = Loc2E (blockSet j b) (blockSet j b) (K (blockSet j b)) - J2 j K b (blockSet j b) := by
  classical
  have hBs := isSmall_blockSet_of_mem hb
  have hBm : blockSet j b ∈ (smallSets (L := L) (N := N) j).filter
      (fun X => blockSet j b ⊆ X) := mem_filter.2 ⟨mem_smallSets.2 hBs, subset_rfl⟩
  rw [Q2, if_pos hN, ← add_sum_erase _ _ hBm, J2, if_pos ⟨hN, hBs, subset_rfl⟩, if_pos rfl,
    sub_neg_eq_add]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext Y; simp only [mem_erase, mem_filter]; tauto

open Classical in
/-- The summand of `𝓛(K)` for a connected `X`. -/
theorem Lterm_eq (hN : j + 1 < N) {X : Finset (Lam d L N)} (hX : IsConn j X) :
    ECCE C (thetaE (K X) + dIlin j C K X - ∑ b ∈ blocks j X, thetaE (J2 j K b X)) =
      if IsSmall j X then EthE C (K X - Loc2E X X (K X)) else EthE C (K X) := by
  have hXp := hX.1
  by_cases h1 : nb j X = 1
  · obtain ⟨b, hb⟩ := card_eq_one.1 h1
    have hXb := eq_blockSet_of_nb_one hXp hb
    have hbI : b ∈ blockIdx (L := L) (N := N) j :=
      mem_blockIdx_of_mem_blocks (show b ∈ blocks j X by rw [hb]; exact mem_singleton_self b)
    have hs : IsSmall j X := hXb ▸ isSmall_blockSet_of_mem hbI
    rw [if_pos hs, dIlin, if_pos h1, hb, sum_singleton, sum_singleton, map_sub, map_add,
      map_neg, ECCE_inclE, ECCE_thetaE, ECCE_thetaE, Q2_split j K hN hbI, hXb, EthE_sub,
      EthE_sub]
    abel
  · have hdl : dIlin j C K X = 0 := by rw [dIlin, if_neg h1]
    rw [hdl, add_zero]
    by_cases hs : IsSmall j X
    · rw [if_pos hs]
      have hJ : ∀ b ∈ blocks j X, J2 j K b X = Loc2E X (blockSet j b) (K X) := by
        intro b hbX
        have hsub : blockSet j b ⊆ X := blockSet_subset_of_mem_blocks hXp hbX
        have hne : X ≠ blockSet j b := by
          intro he
          apply h1
          rw [he]
          have hbI : b ∈ blockIdx (L := L) (N := N) j := mem_blockIdx_of_mem_blocks hbX
          exact le_antisymm (nb_blockSet_le j b)
            (card_pos.2 ⟨b, by
              obtain ⟨x, hx, rfl⟩ := mem_image.1 hbI
              exact blk_mem_blocks (mem_blockSet_blk j x)⟩)
        rw [J2, if_pos ⟨hN, hs, hsub⟩, if_neg hne]
      rw [sum_congr rfl fun b hb => by rw [hJ b hb], ← map_sum, Loc2E_sum_blocks hXp,
        map_sub, ECCE_thetaE, ECCE_thetaE, EthE_sub]
    · rw [if_neg hs]
      have hJ : ∑ b ∈ blocks j X, thetaE (J2 j K b X) = 0 :=
        sum_eq_zero fun b _ => by rw [J2_of_not_small j K b X hs, map_zero]
      rw [hJ, sub_zero, ECCE_thetaE]

open Classical in
/-- **`𝓛(K)` as a sum of `(1 - Loc)` terms** (`j + 1 < N`). -/
theorem Llin2_eq (hN : j + 1 < N) (U : Finset (Lam d L N)) :
    Llin2 j C K U =
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
          EthE C (K X - Loc2E X X (K X))) +
        ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
          EthE C (K X) := by
  classical
  rw [Llin2, show (∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ECCE C (∏ p ∈ g.1, thetaE (J2 j K p.1 p.2))) = 0 by
    rw [← map_sum, J2prod_sum, map_zero], add_zero]
  -- reindex the sum over `g = (∅, X)`
  have e1 : ∑ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      ECCE C (thetaE (K g.2) + dIlin j C K g.2 - ∑ b ∈ blocks j g.2, thetaE (J2 j K b g.2)) =
      ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ clo j X = U),
        ECCE C (thetaE (K X) + dIlin j C K X - ∑ b ∈ blocks j X, thetaE (J2 j K b X)) := by
    refine sum_nbij' (fun g => g.2) (fun X => (∅, X)) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      obtain ⟨hg, h0, hc⟩ := mem_filter.1 hg
      rw [eq_empty_left_of_mem_Gset h0] at hg
      obtain ⟨hp, hcl⟩ := mem_Gset_empty.1 hg
      exact mem_filter.2 ⟨mem_Pj.2 ⟨subset_univ _, hp⟩, hc, hcl⟩
    · intro X hX
      obtain ⟨hX, hc, hcl⟩ := mem_filter.1 hX
      exact mem_filter.2 ⟨mem_Gset_empty.2 ⟨(mem_Pj.1 hX).2, hcl⟩, rfl, hc⟩
    · intro g hg
      exact (eq_empty_left_of_mem_Gset (mem_filter.1 hg).2.1).symm
    · intro X _; rfl
    · intro g _; rfl
  rw [e1, ← sum_filter_add_sum_filter_not _ (fun X => IsSmall j X)]
  congr 1
  · refine sum_congr ?_ fun X hX => ?_
    · ext X
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hP, -, hcl⟩, hs⟩; exact ⟨hP, hs, hcl⟩
      · rintro ⟨hP, hs, hcl⟩; exact ⟨⟨hP, ⟨hs.1, hs.2.1⟩, hcl⟩, hs⟩
    · obtain ⟨-, hs, -⟩ := mem_filter.1 hX
      rw [Lterm_eq j C K hN ⟨hs.1, hs.2.1⟩, if_pos hs]
  · refine sum_congr ?_ fun X hX => ?_
    · ext X
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hP, hc, hcl⟩, hs⟩; exact ⟨hP, hc, hs, hcl⟩
      · rintro ⟨hP, hc, hs, hcl⟩; exact ⟨⟨hP, hc, hcl⟩, hs⟩
    · obtain ⟨-, hc, hs, -⟩ := mem_filter.1 hX
      rw [Lterm_eq j C K hN hc, if_neg hs]

end

end Step2
