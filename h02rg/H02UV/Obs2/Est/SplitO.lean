import Obs2.Loc.LocFlow

/-!
# `∑_U J(B_+, U) = 0` with sources, and the split of `K_out` (`Step2.Map.Split`, `Step2.Map.ReblockBound`)

* `kapO_sum_zero`: `∑_X κ(X, B_+) = 0` (pure algebra, as `Step2.kap_sum_zero`);
* `kapO_of_not_small`: `κ(X, B_+) = 0` if `\bar X` is not small, under the strong locality
  `V(B) ∈ 𝒩^{obs}(B^□)` of `OLocS` (then `F_C(V'_B, V'_{B'}) = 0` exactly for far blocks,
  `OLocS.FCO_Vpr_far`, including the `σ_aσ_b` component);
* **`JhO_sum_U`**: `∑_{U ⊇ B_+} J(B_+, U) = 0` (Brydges–Slade (5.19)) with sources;
* **`KoutO_split`**: for connected `W`, `K_out(W) = M(W) + ∑_{g ∈ Rset} R_g(W)`
  (`Step2.Kout_split` on `OE`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

section Kap

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam c d L N)

theorem kapO_sum_zero (c' : Fin d → ℕ) :
    ∑ X ∈ Pj (d := d) (L := L) (N := N) j univ, kapO j C V X c' = 0 := by
  classical
  set T := blockIdx (L := L) (N := N) j
  set f : (Fin d → ℕ) → OE c (Lam d L N) := fun b =>
    (-(1 / 2 : ℂ)) • FCO C (VprO C V b) (VprLO j C V - VprO C V b) - SCorO j C V b
  set F : (Fin d → ℕ) → (Fin d → ℕ) → OE c (Lam d L N) := fun b b' =>
    FCO C (VprO C V b) (VprO C V b') + GO C V b b'
  set φ : Finset (Fin d → ℕ) → OE c (Lam d L N) := fun S =>
    if S.card = 1 then ∑ b ∈ S.filter (fun b => par L b = c'), f b
    else if S.card = 2 then
      (1 / 2 : ℂ) • ∑ b ∈ S.filter (fun b => par L b = c'), ∑ b' ∈ S.erase b, F b b'
    else 0
  have e1 : ∑ X ∈ Pj (d := d) (L := L) (N := N) j univ, kapO j C V X c' =
      ∑ X ∈ Pj (d := d) (L := L) (N := N) j univ, φ (blocks j X) := rfl
  rw [e1, sum_Pj_eq_sum_powerset j φ]
  have e2 : ∑ S ∈ T.powerset, φ S = ∑ S ∈ T.powersetCard 1, φ S + ∑ S ∈ T.powersetCard 2, φ S := by
    rw [← sum_union (disjoint_left.2 fun S h1 h2 => by
      have := (mem_powersetCard.1 h1).2; have := (mem_powersetCard.1 h2).2; omega)]
    symm
    refine sum_subset (fun S hS => ?_) fun S hS hS' => ?_
    · rcases mem_union.1 hS with h | h <;> exact mem_powerset.2 (mem_powersetCard.1 h).1
    · have h1 : S.card ≠ 1 := fun h => hS' (mem_union_left _ (mem_powersetCard.2
        ⟨mem_powerset.1 hS, h⟩))
      have h2 : S.card ≠ 2 := fun h => hS' (mem_union_right _ (mem_powersetCard.2
        ⟨mem_powerset.1 hS, h⟩))
      simp [φ, h1, h2]
  rw [e2]
  have e3 : ∑ S ∈ T.powersetCard 1, φ S = ∑ b ∈ T.filter (fun b => par L b = c'), f b := by
    rw [sum_filter, ← sum_powersetCard_one T]
    refine sum_congr rfl fun S hS => ?_
    simp only [φ, (mem_powersetCard.1 hS).2, if_true, sum_filter]
  have e4' : ∑ b ∈ T.filter (fun b => par L b = c'), ∑ b' ∈ T.erase b, F b b' =
      ∑ b ∈ T, ∑ b' ∈ T.erase b, (if par L b = c' then F b b' else 0) := by
    rw [sum_filter]; refine sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  have e4 : ∑ S ∈ T.powersetCard 2, φ S = (1 / 2 : ℂ) •
      ∑ b ∈ T.filter (fun b => par L b = c'), ∑ b' ∈ T.erase b, F b b' := by
    rw [e4', ← sum_powersetCard_two T (fun b b' => if par L b = c' then F b b' else 0), smul_sum]
    refine sum_congr rfl fun S hS => ?_
    simp only [φ, (mem_powersetCard.1 hS).2, show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true]
    congr 1
    rw [sum_filter]; refine sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  rw [e3, e4, smul_sum, ← sum_add_distrib]
  refine sum_eq_zero fun b hb => ?_
  have hbT := (mem_filter.1 hb).1
  have hG : ∑ b' ∈ T.erase b, GO C V b b' = (2 : ℂ) • SCorO j C V b := by
    rw [SCorO_eq_sum, smul_smul, ← sum_erase_add _ _ hbT, GO_self, add_zero]
    norm_num
  simp only [f, F]
  rw [sum_add_distrib, hG, ← FCO_sum_right, VprLO, sum_erase_eq_sub hbT]
  module

variable {P : ObsPts d L N} {W : OFam c d L N} {K : OAct c d L N} {j C V}

omit [NeZero L] in
/-- Two `j`-blocks `B, B'` such that `\bar{B ∪ B'}` is not small are not near. -/
theorem not_near_of_not_small [NeZero L] (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L)
    (hjN : j + 1 < N) {b b' : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (hs : ¬ IsSmall (j + 1) (clo j (blockSet (L := L) (N := N) j b ∪ blockSet j b'))) :
    b' ∉ nearSet (L := L) (N := N) j b := by
  rw [clo_union, clo_blockSet hb, clo_blockSet hb'] at hs
  set U₁ := blockSet (L := L) (N := N) (j + 1) (par L b)
  set U₂ := blockSet (L := L) (N := N) (j + 1) (par L b')
  have hsub : ∀ b₀ : Fin d → ℕ, blockSet (L := L) (N := N) j b₀ ⊆ blockSet (j + 1) (par L b₀) :=
    fun b₀ z hz => mem_blockSet.2 (by rw [blk_succ, mem_blockSet.1 hz])
  have hp₁ : par L b ∈ blockIdx (L := L) (N := N) (j + 1) := by
    obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
    exact mem_blockIdx.2 ⟨x, hsub b hx⟩
  have hp₂ : par L b' ∈ blockIdx (L := L) (N := N) (j + 1) := by
    obtain ⟨x, hx⟩ := mem_blockIdx.1 hb'
    exact mem_blockIdx.2 ⟨x, hsub b' hx⟩
  have hnt : ¬ Touch U₁ U₂ := fun ht => hs (isSmall_two_blocks hd hp₁ hp₂ ht)
  intro hnear
  obtain ⟨-, x, hx, y, hy, hxy⟩ := mem_filter.1 hnear
  have hx' : x ∈ nbhd j U₁ := nbhd_mono (hsub b) hx
  have hy' : y ∈ nbhd j U₂ := nbhd_mono (hsub b') hy
  have := lt_two_mul_supNorm_of_nbhd hL hjN.le (isPolymer_blockSet (j + 1) _)
    (isPolymer_blockSet (j + 1) _) hnt hx' hy'
  omega

/-- `F(V'_B, V'_{B'}) + G(B, B') = 0` for `j`-blocks `B, B'` such that `\bar{B ∪ B'}` is not
small. -/
theorem FCO_far_of_not_small (H : OLocS P j V W K) (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L)
    (hjN : j + 1 < N) (hC : CovRange j C) {b b' : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (hs : ¬ IsSmall (j + 1) (clo j (blockSet (L := L) (N := N) j b ∪ blockSet j b'))) :
    FCO C (VprO C V b) (VprO C V b') + GO C V b b' = 0 := by
  have hn := not_near_of_not_small hd hL hjN hb hb' hs
  rw [H.FCO_Vpr_far hC hb' hn, GO, OLocS.FCO_far_gen hC hb' hn (πobs_mem_osub (H.Vpr_mem b))
    (H.Vpr_mem b'), OLocS.FCO_far_gen hC hb' hn (H.Vpr_mem b) (πobs_mem_osub (H.Vpr_mem b')),
    sub_zero, add_zero]

theorem kapO_of_not_small (H : OLocS P j V W K) (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L)
    (hjN : j + 1 < N) (hC : CovRange j C) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hs : ¬ IsSmall (j + 1) (clo j X)) (c' : Fin d → ℕ) : kapO j C V X c' = 0 := by
  classical
  unfold kapO
  split_ifs with h1 h2
  · exfalso
    obtain ⟨b, hb⟩ := card_eq_one.1 h1
    have hbI : b ∈ blockIdx (L := L) (N := N) j :=
      mem_blockIdx_of_mem_blocks (hb ▸ mem_singleton_self b)
    rw [eq_blockSet_of_nb_one hX hb] at hs
    exact hs (isSmall_clo (isSmall_blockSet_of_mem hbI))
  · obtain ⟨b₁, b₂, h12, hb⟩ := card_eq_two.1 h2
    have hX12 : X = blockSet (L := L) (N := N) j b₁ ∪ blockSet j b₂ := by
      rw [← biUnion_blocks hX, hb, biUnion_insert, singleton_biUnion]
    have hI : ∀ b ∈ blocks j X, b ∈ blockIdx (L := L) (N := N) j :=
      fun b hb => mem_blockIdx_of_mem_blocks hb
    have hb₁ := hI b₁ (hb ▸ mem_insert_self _ _)
    have hb₂ := hI b₂ (hb ▸ mem_insert_of_mem (mem_singleton_self _))
    have hs' := hX12 ▸ hs
    have hz : ∀ b ∈ blocks j X, ∀ b' ∈ (blocks j X).erase b,
        FCO C (VprO C V b) (VprO C V b') + GO C V b b' = 0 := by
      intro b hbX b' hb'
      have hne := ne_of_mem_erase hb'
      have hb'X := mem_of_mem_erase hb'
      rw [hb] at hbX hb'X
      simp only [mem_insert, mem_singleton] at hbX hb'X
      rcases hbX with rfl | rfl <;> rcases hb'X with rfl | rfl
      · exact absurd rfl hne
      · exact FCO_far_of_not_small H hd hL hjN hC hb₁ hb₂ hs'
      · exact FCO_far_of_not_small H hd hL hjN hC hb₂ hb₁ (by rwa [union_comm])
      · exact absurd rfl hne
    rw [sum_eq_zero fun b hb => sum_eq_zero fun b' hb' => hz b (mem_filter.1 hb).1 b' hb',
      smul_zero]
  · rfl

/-- **`∑_{U ⊇ B_+} J(B_+, U) = 0`** with sources (Brydges–Slade (5.19)). -/
theorem JhO_sum_U (H : OLocS P j V W K) (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hjN : j + 1 < N)
    (hC : CovRange j C) (c' : Fin d → ℕ) :
    ∑ U ∈ (smallSets (d := d) (L := L) (N := N) (j + 1)).filter
      (fun U => blockSet (j + 1) c' ⊆ U), JhO j C V c' U = 0 := by
  classical
  set Sc := (smallSets (d := d) (L := L) (N := N) (j + 1)).filter
    (fun U => blockSet (j + 1) c' ⊆ U)
  have e1 : ∑ U ∈ Sc, JhO j C V c' U = ∑ U ∈ Sc,
      ∑ X ∈ ((Pj (d := d) (L := L) (N := N) j univ).filter (fun X => clo j X ∈ Sc)).filter
        (fun X => clo j X = U), kapO j C V X c' := by
    refine sum_congr rfl fun U hU => ?_
    rw [JhO, if_pos (mem_smallSets_filter.1 hU).1, filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext X; simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ hU, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  rw [e1, sum_fiberwise_of_maps_to (fun X hX => (mem_filter.1 hX).2)]
  have h := kapO_sum_zero (L := L) (N := N) j C V c'
  rw [← sum_filter_add_sum_filter_not (Pj (d := d) (L := L) (N := N) j univ)
    (fun X => clo j X ∈ Sc)] at h
  rw [← h]
  refine (add_eq_left.2 ?_).symm
  refine sum_eq_zero ?_
  · intro X hX
    obtain ⟨hX1, hX2⟩ := mem_filter.1 hX
    have hXp := (mem_Pj.1 hX1).2
    by_cases hs : IsSmall (j + 1) (clo j X)
    · have hc : ¬ blockSet (L := L) (N := N) (j + 1) c' ⊆ clo j X := fun h =>
        hX2 (mem_smallSets_filter.2 ⟨hs, h⟩)
      have hcX : c' ∉ blocks (j + 1) X := fun hc' => hc (by
        rw [← blocks_clo] at hc'; exact blockSet_subset (isPolymer_clo j X) hc')
      have hf : (blocks j X).filter (fun b => par L b = c') = ∅ :=
        filter_eq_empty_iff.2 fun b hb hbc => hcX (hbc ▸ par_mem_blocks hb)
      unfold kapO; simp only [hf, sum_empty, smul_zero]; split_ifs <;> rfl
    · exact kapO_of_not_small H hd hL hjN hC hXp hs c'

end Kap

/-! ### The split of `K_out` -/

section Split

variable {k : ℕ} {I : OFam c d L N} {M : OAct c d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)}

theorem KoutO_split (hJ0 : ∀ b ∈ blockIdx (L := L) (N := N) k,
      ∑ U ∈ (smallSets (d := d) (L := L) (N := N) k).filter (fun U => blockSet k b ⊆ U), J b U = 0)
    {W : Finset (Lam d L N)} (hW : IsConn k W) :
    KoutO k I M J W = M W + ∑ g ∈ Rset k W, RtermO k I M J W g := by
  classical
  set F := (G0 (L := L) (N := N) k).filter (fun g => g.2 ∪ Bbox k g.1 = W) with hF
  have hBbox0 : Bbox k (∅ : Finset ((Fin d → ℕ) × Finset (Lam d L N))) = ∅ := by simp [Bbox]
  have hT0 : F.filter (fun g => g.1 = ∅) = {(∅, W)} := by
    ext g
    simp only [mem_filter, mem_singleton, hF]
    constructor
    · rintro ⟨⟨-, hgW⟩, h1⟩
      rw [h1, hBbox0, union_empty] at hgW
      exact Prod.ext h1 hgW
    · rintro rfl
      refine ⟨⟨(mem_G0 k).2 ⟨hW.1, empty_subset _, by simp, by simp, ?_⟩, ?_⟩, rfl⟩
      · rintro ⟨x, hx, -⟩; simp [Xcal] at hx
      · show W ∪ Bbox k ∅ = W; rw [hBbox0, union_empty]
  have hR0 : RtermO k I M J W (∅, W) = M W := by
    simp only [RtermO, Xcal, biUnion_empty, union_empty, sdiff_self, prod_empty, mul_one]
    rw [show (⊥ : Finset (Lam d L N)) = ∅ from rfl, KextO, comp_of_isConn hW, prod_singleton]
    simp [bpowO, blocks]
  have hT1 : ∑ g ∈ (F.filter fun g => g.1 ≠ ∅).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      RtermO k I M J W g = 0 := by
    set PW := (pairsU (L := L) (N := N) k).filter (fun p => nbhd k (blockSet k p.1) = W)
    have e : ∑ g ∈ (F.filter fun g => g.1 ≠ ∅).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
        RtermO k I M J W g = ∑ p ∈ PW, bpowO k I W * J p.1 p.2 := by
      symm
      refine sum_bij (fun p _ => (({p} : Finset _), (∅ : Finset (Lam d L N)))) ?_ ?_ ?_ ?_
      · intro p hp
        obtain ⟨hp1, hpW⟩ := mem_filter.1 hp
        simp only [mem_filter, hF]
        refine ⟨⟨⟨(mem_G0 k).2 ⟨isPolymer_empty k, singleton_subset_iff.2 hp1, by simp, by simp,
          by rintro ⟨x, -, y, hy, -⟩; simp at hy⟩, ?_⟩, by simp⟩, by simp⟩
        show ∅ ∪ Bbox k {p} = W
        rw [empty_union, Bbox, singleton_biUnion, hpW]
      · intro p _ q _ h
        simpa using congrArg Prod.fst h
      · intro g hg
        simp only [mem_filter, hF] at hg
        obtain ⟨⟨⟨hg0, hgW⟩, -⟩, hc1, hg2⟩ := hg
        obtain ⟨p, hp⟩ := card_eq_one.1 hc1
        obtain ⟨-, h2, -, -, -⟩ := (mem_G0 k).1 hg0
        refine ⟨p, mem_filter.2 ⟨h2 (hp ▸ mem_singleton_self p), ?_⟩, ?_⟩
        · rw [hg2, hp, empty_union, Bbox, singleton_biUnion] at hgW; exact hgW
        · exact Prod.ext hp.symm hg2.symm
      · intro p hp
        obtain ⟨hp1, hpW⟩ := mem_filter.1 hp
        have hpsub : p.2 ⊆ W := hpW ▸ (pair_sub_nbhd hp1).2
        simp only [RtermO, Xcal, singleton_biUnion, empty_union, KextO_empty, one_mul,
          prod_singleton, JbarO]
        rw [← mul_assoc, ← bpowO_union k I (IsPolymer.sdiff (hW.1) (mem_pairsU.1 hp1).2.1.1)
          (mem_pairsU.1 hp1).2.1.1 sdiff_disjoint, sdiff_union_of_subset hpsub]
    rw [e, ← mul_sum]
    have h2 : ∑ p ∈ PW, J p.1 p.2 = 0 := by
      rw [← sum_fiberwise_of_maps_to (s := PW) (t := (blockIdx (L := L) (N := N) k))
        (g := Prod.fst) (fun p hp => (mem_pairsU.1 (mem_filter.1 hp).1).1)]
      refine sum_eq_zero fun b hb => ?_
      by_cases hbW : nbhd k (blockSet (L := L) (N := N) k b) = W
      · rw [← hJ0 b hb]
        refine sum_nbij' (fun p => p.2) (fun U => (b, U)) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          obtain ⟨hp1, hpb⟩ := mem_filter.1 hp
          obtain ⟨-, hs, hbs⟩ := mem_pairsU.1 (mem_filter.1 hp1).1
          exact mem_smallSets_filter.2 ⟨hs, hpb ▸ hbs⟩
        · intro U hU
          obtain ⟨hs, hbU⟩ := mem_smallSets_filter.1 hU
          exact mem_filter.2 ⟨mem_filter.2 ⟨mem_pairsU.2 ⟨hb, hs, hbU⟩, hbW⟩, rfl⟩
        · intro p hp; exact Prod.ext (mem_filter.1 hp).2.symm rfl
        · intro U _; rfl
        · intro p hp; rw [(mem_filter.1 hp).2]
      · refine sum_eq_zero fun p hp => absurd ?_ hbW
        obtain ⟨hp1, hpb⟩ := mem_filter.1 hp
        rw [← hpb]; exact (mem_filter.1 hp1).2
    rw [h2, mul_zero]
  rw [KoutO, ← hF, ← sum_filter_add_sum_filter_not F (fun g => g.1 = ∅), hT0, sum_singleton, hR0,
    ← sum_filter_add_sum_filter_not (F.filter fun g => ¬ g.1 = ∅) (fun g => g.1.card = 1 ∧ g.2 = ∅),
    hT1, zero_add]
  congr 1
  unfold Rset
  rw [← hF, filter_filter]

end Split

end

end Obs2
