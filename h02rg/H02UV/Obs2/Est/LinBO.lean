import Obs2.Est.LinO

/-!
# The linear part with sources as a sum of `(1 - Loc)` terms (`Step2.Map.LinB` on `OE`)

For `j + 1 < N` (`Llin2O_eq`):

  `𝓛(K)(U) = ∑_{X ∈ 𝒮_j, \bar X = U} 𝔼θ (1 - Loc_X) K(X) + ∑_{X ∈ 𝒞_j ∖ 𝒮_j, \bar X = U} 𝔼θ K(X)`,

with the pointed/barycentric `Loc = LocO2`. The additivity of `Loc_{X,Y}` in `Y` holds for every
component (`LocO2_sum_blocks`): the bulk part is `Step2.Loc2E_sum_blocks`, the pointed parts are
`locOdd_eq_sum`/`locEven_eq_sum` for `a ∈ X` and `∑_B |B|/|X| = 1` for `a ∉ X`, and the
barycentric part is `∑_B |B ∩ {a,b}| / |X ∩ {a,b}| = 1`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD PolyAux

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Additivity of `Loc_{X,Y}` in `Y` -/

section Add

variable {j : ℕ} {X : Finset (Lam d L N)}

theorem locA_sum_blocks (hX : IsPolymer j X) (o : ObsCase) (a : Lam d L N) (F : Alg d L N) :
    ∑ b ∈ blocks j X, locA o a X (blockSet j b) F = locA o a X X F := by
  have hX' := biUnion_blocks hX
  cases o
  · have := locOdd_eq_sum (blocks j X) (blockSet j) (pairwiseDisjoint_blockSet j _) (-1) {a} F
    rw [hX'] at this
    exact this.symm
  · have := locEven_eq_sum (blocks j X) (blockSet j) (pairwiseDisjoint_blockSet j _) {a} F
    rw [hX'] at this
    exact this.symm

theorem locB_sum_blocks (hX : IsPolymer j X) (o : ObsCase) (a : Lam d L N) (F : Alg d L N) :
    ∑ b ∈ blocks j X, locB o a X (blockSet j b) F = locB o a X X F := by
  have hX' := biUnion_blocks hX
  cases o
  · have := locOdd_eq_sum (blocks j X) (blockSet j) (pairwiseDisjoint_blockSet j _) 1 {a} F
    rw [hX'] at this
    exact this.symm
  · have := locEven_eq_sum (blocks j X) (blockSet j) (pairwiseDisjoint_blockSet j _) {a} F
    rw [hX'] at this
    exact this.symm

theorem card_sum_blocks (hX : IsPolymer j X) :
    ∑ b ∈ blocks j X, ((blockSet (L := L) (N := N) j b).card : ℂ) = (X.card : ℂ) := by
  rw [← Nat.cast_sum, ← card_biUnion (pairwiseDisjoint_blockSet j _), biUnion_blocks hX]

theorem card_inter_sum_blocks (hX : IsPolymer j X) (S : Finset (Lam d L N)) :
    ∑ b ∈ blocks j X, ((blockSet (L := L) (N := N) j b ∩ S).card : ℂ) = ((X ∩ S).card : ℂ) := by
  have e : (blocks j X).biUnion (fun b => blockSet (L := L) (N := N) j b ∩ S) = X ∩ S := by
    ext x
    simp only [mem_biUnion, mem_inter]
    conv_rhs => rw [← biUnion_blocks hX, mem_biUnion]
    tauto
  rw [← Nat.cast_sum, ← card_biUnion, e]
  intro b hb b' hb' hne
  exact Disjoint.mono inter_subset_left inter_subset_left
    (pairwiseDisjoint_blockSet j (blocks j X) hb hb' hne)

theorem frac_sum_blocks {f : (Fin d → ℕ) → ℂ} {T : ℂ} (h : ∑ b ∈ blocks j X, f b = T)
    (V : Alg d L N) : ∑ b ∈ blocks j X, (f b / T) • V = (T / T) • V := by
  rw [← sum_smul, ← sum_div, h]

theorem locAp_sum_blocks (hX : IsPolymer j X) (a : Lam d L N) (F : Alg d L N) :
    ∑ b ∈ blocks j X, locAp c a X (blockSet j b) F = locAp c a X X F := by
  by_cases ha : a ∈ X
  · simp only [locAp_of_mem _ ha]
    exact locA_sum_blocks hX _ a F
  · simp only [locAp_of_not_mem _ ha]
    exact frac_sum_blocks (card_sum_blocks hX) _

theorem locBp_sum_blocks (hX : IsPolymer j X) (a : Lam d L N) (F : Alg d L N) :
    ∑ b ∈ blocks j X, locBp c a X (blockSet j b) F = locBp c a X X F := by
  by_cases ha : a ∈ X
  · simp only [locBp, if_pos ha]
    exact locB_sum_blocks hX _ a F
  · simp only [locBp, if_neg ha]
    exact frac_sum_blocks (card_sum_blocks hX) _

theorem locABtXY_sum_blocks (P : ObsPts d L N) (hX : IsPolymer j X) (F : Alg d L N) :
    ∑ b ∈ blocks j X, locABtXY P X (blockSet j b) F = locABtXY P X X F := by
  simp only [locABtXY]
  exact frac_sum_blocks (card_inter_sum_blocks hX P.pts) _

/-- **Additivity of `Loc_{X,·}` with sources.** -/
theorem LocO2_sum_blocks (P : ObsPts d L N) (hX : IsPolymer j X) (F : OE c (Lam d L N)) :
    ∑ b ∈ blocks j X, LocO2 P X (blockSet j b) F = LocO2 P X X F := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [AddSubmonoidClass.coe_finsetSum]
    show eL (∑ b ∈ blocks j X, (LocO2 P X (blockSet j b) F : SA c (Lam d L N))) = _
    rw [map_sum]
    have := congrArg Subtype.val (Loc2E_sum_blocks hX (bulk F))
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this
  · rw [AddSubmonoidClass.coe_finsetSum]
    show aL (∑ b ∈ blocks j X, (LocO2 P X (blockSet j b) F : SA c (Lam d L N))) = _
    rw [map_sum]
    exact locAp_sum_blocks hX P.a _
  · rw [AddSubmonoidClass.coe_finsetSum]
    show bL (∑ b ∈ blocks j X, (LocO2 P X (blockSet j b) F : SA c (Lam d L N))) = _
    rw [map_sum]
    exact locBp_sum_blocks hX P.b _
  · rw [AddSubmonoidClass.coe_finsetSum]
    show abL (∑ b ∈ blocks j X, (LocO2 P X (blockSet j b) F : SA c (Lam d L N))) = _
    rw [map_sum]
    exact locABtXY_sum_blocks P hX _

end Add

/-! ### `∑_X J(B, X) = 0` -/

section JZero

variable (P : ObsPts d L N) {j : ℕ}

theorem J2O_sum_zero (K : OAct c d L N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X), J2O P j K b X = 0 := by
  classical
  by_cases hN : j + 1 < N
  · have hBs := isSmall_blockSet_of_mem hb
    have hBm : blockSet j b ∈ (smallSets (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X) := mem_filter.2 ⟨mem_smallSets.2 hBs, subset_rfl⟩
    rw [← add_sum_erase _ _ hBm, J2O, if_pos ⟨hN, hBs, subset_rfl⟩, if_pos rfl,
      neg_add_eq_zero]
    refine sum_congr ?_ fun Y hY => ?_
    · ext Y; simp only [mem_erase, mem_filter]; tauto
    · obtain ⟨hne, hY'⟩ := mem_erase.1 hY
      obtain ⟨hYs, hBY⟩ := mem_filter.1 hY'
      rw [J2O, if_pos ⟨hN, mem_smallSets.1 hYs, hBY⟩, if_neg hne]
  · exact sum_eq_zero fun X _ => by rw [J2O, if_neg (fun h => hN h.1)]

theorem J2Oprod_sum (K : OAct c d L N) (U : Finset (Lam d L N)) :
    ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ∏ p ∈ g.1, thetaO (J2O P j K p.1 p.2) = 0 := by
  classical
  set P1 := (pairsU (L := L) (N := N) j).filter
    (fun p => clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U)
  have hbij : ∑ p ∈ P1, thetaO (J2O P j K p.1 p.2) =
      ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
        ∏ p ∈ g.1, thetaO (J2O P j K p.1 p.2) := by
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
  have h0 : ∑ p ∈ P1, J2O P j K p.1 p.2 = 0 := by
    have eP : P1 = (blockIdx (L := L) (N := N) j ×ˢ smallSets (L := L) (N := N) j).filter
        (fun p => blockSet j p.1 ⊆ p.2 ∧
          clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U) := by
      ext p; simp [P1, pairsU, and_assoc]
    rw [eP, sum_filter, sum_product]
    refine sum_eq_zero fun b hb => ?_
    by_cases hc : clo j (nbhd j (blockSet (L := L) (N := N) j b)) = U
    · simp only [hc, and_true]
      rw [← sum_filter]
      exact J2O_sum_zero P K hb
    · simp [hc]
  rw [h0, map_zero]

end JZero

/-! ### The identity -/

section Ident

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : OAct c d L N)

theorem Q2O_split (hN : j + 1 < N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Q2O P j K b = LocO2 P (blockSet j b) (blockSet j b) (K (blockSet j b)) -
      J2O P j K b (blockSet j b) := by
  classical
  have hBs := isSmall_blockSet_of_mem hb
  have hBm : blockSet j b ∈ (smallSets (L := L) (N := N) j).filter
      (fun X => blockSet j b ⊆ X) := mem_filter.2 ⟨mem_smallSets.2 hBs, subset_rfl⟩
  rw [Q2O, if_pos hN, ← add_sum_erase _ _ hBm, J2O, if_pos ⟨hN, hBs, subset_rfl⟩, if_pos rfl,
    sub_neg_eq_add]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext Y; simp only [mem_erase, mem_filter]; tauto

open Classical in
/-- The summand of `𝓛(K)` for a connected `X`. -/
theorem LtermO_eq (hN : j + 1 < N) {X : Finset (Lam d L N)} (hX : IsConn j X) :
    ECCO C (thetaO (K X) + dIlinO P j C K X - ∑ b ∈ blocks j X, thetaO (J2O P j K b X)) =
      if IsSmall j X then EthO C (K X - LocO2 P X X (K X)) else EthO C (K X) := by
  have hXp := hX.1
  by_cases h1 : nb j X = 1
  · obtain ⟨b, hb⟩ := card_eq_one.1 h1
    have hXb := eq_blockSet_of_nb_one hXp hb
    have hbI : b ∈ blockIdx (L := L) (N := N) j :=
      mem_blockIdx_of_mem_blocks (show b ∈ blocks j X by rw [hb]; exact mem_singleton_self b)
    have hs : IsSmall j X := hXb ▸ isSmall_blockSet_of_mem hbI
    rw [if_pos hs, dIlinO, if_pos h1, hb, sum_singleton, sum_singleton, map_sub, map_add,
      map_neg, ECCO_inclO, ECCO_thetaO, ECCO_thetaO, Q2O_split P j K hN hbI, hXb, EthO_sub,
      EthO_sub]
    abel
  · have hdl : dIlinO P j C K X = 0 := by rw [dIlinO, if_neg h1]
    rw [hdl, add_zero]
    by_cases hs : IsSmall j X
    · rw [if_pos hs]
      have hJ : ∀ b ∈ blocks j X, J2O P j K b X = LocO2 P X (blockSet j b) (K X) := by
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
        rw [J2O, if_pos ⟨hN, hs, hsub⟩, if_neg hne]
      rw [sum_congr rfl fun b hb => by rw [hJ b hb], ← map_sum, LocO2_sum_blocks P hXp,
        map_sub, ECCO_thetaO, ECCO_thetaO, EthO_sub]
    · rw [if_neg hs]
      have hJ : ∑ b ∈ blocks j X, thetaO (J2O P j K b X) = 0 :=
        sum_eq_zero fun b _ => by rw [J2O_of_not_small P j K b X hs, map_zero]
      rw [hJ, sub_zero, ECCO_thetaO]

open Classical in
/-- **`𝓛(K)` with sources as a sum of `(1 - Loc)` terms** (`j + 1 < N`). -/
theorem Llin2O_eq (hN : j + 1 < N) (U : Finset (Lam d L N)) :
    Llin2O P j C K U =
      (∑ X ∈ (Pj j univ).filter (fun X => IsSmall j X ∧ clo j X = U),
          EthO C (K X - LocO2 P X X (K X))) +
        ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ ¬ IsSmall j X ∧ clo j X = U),
          EthO C (K X) := by
  classical
  rw [Llin2O, show (∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ECCO C (∏ p ∈ g.1, thetaO (J2O P j K p.1 p.2))) = 0 by
    rw [← map_sum, J2Oprod_sum, map_zero], add_zero]
  have e1 : ∑ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      ECCO C (thetaO (K g.2) + dIlinO P j C K g.2 - ∑ b ∈ blocks j g.2, thetaO (J2O P j K b g.2)) =
      ∑ X ∈ (Pj j univ).filter (fun X => IsConn j X ∧ clo j X = U),
        ECCO C (thetaO (K X) + dIlinO P j C K X - ∑ b ∈ blocks j X, thetaO (J2O P j K b X)) := by
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
      rw [LtermO_eq P j C K hN ⟨hs.1, hs.2.1⟩, if_pos hs]
  · refine sum_congr ?_ fun X hX => ?_
    · ext X
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hP, hc, hcl⟩, hs⟩; exact ⟨hP, hc, hs, hcl⟩
      · rintro ⟨hP, hc, hs, hcl⟩; exact ⟨⟨hP, hc, hcl⟩, hs⟩
    · obtain ⟨-, hc, hs, -⟩ := mem_filter.1 hX
      rw [LtermO_eq P j C K hN hc, if_neg hs]

end Ident

end

end Obs2
