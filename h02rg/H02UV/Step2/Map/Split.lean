import Step2.Map.ReblockBound

/-!
# The scale-`(j+1)` data of the reapportionment

* `It c = Ĩ_{j+1}(B_+) = ∏_{B ⊆ B_+} Ĩ_{j+1}(B)` for the `(j+1)`-block `B_+ = B(c)`, so that
  `It^X = Ĩ^X` (`bpow_It`);
* the split `J(B_+, U)` of `K^{(2)}` over the `(j+1)`-blocks (`Jh`): the part `κ(X, c)` of
  `k^{(2)}(X)` coming from the `j`-blocks of `X` in `B_+ = B(c)`, summed over `X` with `\bar X = U`,
  and set to `0` unless `U` is small. Then
  - `∑_{B_+ ⊆ U} J(B_+, U) = K^{(2)}(U)` for connected `U` (`Jh_sum`);
  - `∑_{U ⊇ B_+} J(B_+, U) = 0` (`Jh_sum_U`, Brydges–Slade (5.19)). This uses that `F(V'_B, V'_{B'})`
    vanishes if `B, B'` lie in non-touching `(j+1)`-blocks (finite range).
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step PolyAux

variable {d L N : ℕ} [NeZero L]

/-! ### Blocks at two scales -/

theorem mem_blocks_blockSet_succ {j : ℕ} {b c : Fin d → ℕ} :
    b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c) ↔
      b ∈ blockIdx (L := L) (N := N) j ∧ par L b = c := by
  constructor
  · intro hb
    obtain ⟨x, hx, rfl⟩ := mem_blocks.1 hb
    exact ⟨mem_blockIdx_of_mem_blocks hb, by rw [← blk_succ]; exact mem_blockSet.1 hx⟩
  · rintro ⟨hb, rfl⟩
    obtain ⟨x, -, rfl⟩ := mem_image.1 hb
    exact mem_blocks.2 ⟨x, mem_blockSet.2 (blk_succ j x), rfl⟩

theorem filter_par_eq {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer (j + 1) X) {c : Fin d → ℕ}
    (hc : c ∈ blocks (j + 1) X) :
    (blocks j X).filter (fun b => par L b = c) = blocks j (blockSet (L := L) (N := N) (j + 1) c) := by
  ext b
  rw [mem_filter, mem_blocks_blockSet_succ]
  constructor
  · rintro ⟨hb, hbc⟩; exact ⟨mem_blockIdx_of_mem_blocks hb, hbc⟩
  · rintro ⟨hb, hbc⟩
    refine ⟨?_, hbc⟩
    obtain ⟨y, hy, hyc⟩ := mem_blocks.1 hc
    obtain ⟨x, -, rfl⟩ := mem_image.1 hb
    have : x ∈ X := hX y x (by rw [hyc, blk_succ, hbc]) hy
    exact blk_mem_blocks this

theorem par_mem_blocks {j : ℕ} {X : Finset (Lam d L N)} {b : Fin d → ℕ} (hb : b ∈ blocks j X) :
    par L b ∈ blocks (j + 1) X := by
  rw [blocks_succ]; exact mem_image_of_mem _ hb

theorem prod_blocks_succ {M : Type*} [CommMonoid M] {j : ℕ} {X : Finset (Lam d L N)}
    (hX : IsPolymer (j + 1) X) (f : (Fin d → ℕ) → M) :
    ∏ b ∈ blocks j X, f b = ∏ c ∈ blocks (j + 1) X,
      ∏ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), f b := by
  rw [← prod_fiberwise_of_maps_to (g := par L) (t := blocks (j + 1) X)
    (fun b hb => par_mem_blocks hb)]
  exact prod_congr rfl fun c hc => by rw [filter_par_eq hX hc]

theorem clo_blockSet {j : ℕ} {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    clo j (blockSet (L := L) (N := N) j b) = blockSet (j + 1) (par L b) := by
  ext x
  rw [mem_clo, mem_blockSet]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := mem_blocks.1 hx
    rw [← hyx, blk_succ, mem_blockSet.1 hy]
  · intro hx
    obtain ⟨y, hy⟩ := mem_blockIdx.1 hb
    exact mem_blocks.2 ⟨y, hy, by rw [blk_succ, mem_blockSet.1 hy, hx]⟩

/-! ### The block factor at scale `j + 1` -/

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (K : Act d L N)

/-- `Ĩ_{j+1}(B_+) = ∏_{B ⊆ B_+} Ĩ_{j+1}(B)`. -/
def It (c : Fin d → ℕ) : EvR (Lam d L N) :=
  bpow j (Gp j C V W K) (blockSet (L := L) (N := N) (j + 1) c)

theorem bpow_It {X : Finset (Lam d L N)} (hX : IsPolymer (j + 1) X) :
    bpow (j + 1) (It j C V W K) X = bpow j (Gp j C V W K) X := by
  unfold bpow It bpow
  exact (prod_blocks_succ hX _).symm

/-! ### The split of `K^{(2)}` -/

/-- The part of `k^{(2)}(X)` from the `j`-blocks in `B(c)`. -/
def kap (X : Finset (Lam d L N)) (c : Fin d → ℕ) : EvR (Lam d L N) :=
  if nb j X = 1 then
    ∑ b ∈ (blocks j X).filter (fun b => par L b = c),
      (-(1 / 2 : ℂ)) • FCE C (Vpr C V b) (VprL j C V - Vpr C V b)
  else if nb j X = 2 then
    (1 / 2 : ℂ) • ∑ b ∈ (blocks j X).filter (fun b => par L b = c),
      ∑ b' ∈ (blocks j X).erase b, FCE C (Vpr C V b) (Vpr C V b')
  else 0

/-- **The split `J(B_+, U)` of `K^{(2)}`.** -/
def Jh (c : Fin d → ℕ) (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  if IsSmall (j + 1) U then ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U), kap j C V X c else 0

theorem Jh_of_not_small (c : Fin d → ℕ) {U : Finset (Lam d L N)} (hU : ¬ IsSmall (j + 1) U) :
    Jh j C V c U = 0 := by
  rw [Jh, if_neg hU]

theorem sum_kap (X : Finset (Lam d L N)) :
    ∑ c ∈ blocks (j + 1) X, kap j C V X c = k2 j C V X := by
  classical
  unfold kap k2
  split_ifs with h1 h2
  · exact sum_fiberwise_of_maps_to (fun b hb => par_mem_blocks hb) _
  · rw [← smul_sum]
    congr 1
    exact sum_fiberwise_of_maps_to (fun b hb => par_mem_blocks hb) _
  · exact sum_const_zero

theorem Jh_sum (hd : 1 ≤ d) {U : Finset (Lam d L N)} (hU : IsConn (j + 1) U) :
    ∑ c ∈ blocks (j + 1) U, Jh j C V c U = K2 j C V U := by
  classical
  by_cases hs : IsSmall (j + 1) U
  · simp only [Jh, if_pos hs]
    rw [sum_comm, K2]
    refine sum_congr rfl fun X hX => ?_
    rw [← (mem_filter.1 hX).2, blocks_clo]
    exact sum_kap j C V X
  · rw [sum_eq_zero fun c _ => Jh_of_not_small j C V c hs]
    have h2 : 2 < nb (j + 1) U := by
      by_contra h
      push Not at h
      exact hs ⟨hU.1, hU.2, h.trans (by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd)⟩
    exact (K2_eq_zero j C V h2).symm

/-! #### `∑_U J(B_+, U) = 0` -/

theorem kap_sum_zero (c : Fin d → ℕ) :
    ∑ X ∈ Pj (d := d) (L := L) (N := N) j univ, kap j C V X c = 0 := by
  classical
  set T := blockIdx (L := L) (N := N) j
  set f : (Fin d → ℕ) → EvR (Lam d L N) := fun b =>
    (-(1 / 2 : ℂ)) • FCE C (Vpr C V b) (VprL j C V - Vpr C V b)
  set F : (Fin d → ℕ) → (Fin d → ℕ) → EvR (Lam d L N) := fun b b' =>
    FCE C (Vpr C V b) (Vpr C V b')
  set φ : Finset (Fin d → ℕ) → EvR (Lam d L N) := fun S =>
    if S.card = 1 then ∑ b ∈ S.filter (fun b => par L b = c), f b
    else if S.card = 2 then
      (1 / 2 : ℂ) • ∑ b ∈ S.filter (fun b => par L b = c), ∑ b' ∈ S.erase b, F b b'
    else 0
  have e1 : ∑ X ∈ Pj (d := d) (L := L) (N := N) j univ, kap j C V X c =
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
  have e3 : ∑ S ∈ T.powersetCard 1, φ S = ∑ b ∈ T.filter (fun b => par L b = c), f b := by
    rw [sum_filter, ← sum_powersetCard_one T]
    refine sum_congr rfl fun S hS => ?_
    simp only [φ, (mem_powersetCard.1 hS).2, if_true, sum_filter]
  have e4' : ∑ b ∈ T.filter (fun b => par L b = c), ∑ b' ∈ T.erase b, F b b' =
      ∑ b ∈ T, ∑ b' ∈ T.erase b, (if par L b = c then F b b' else 0) := by
    rw [sum_filter]; refine sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  have e4 : ∑ S ∈ T.powersetCard 2, φ S = (1 / 2 : ℂ) •
      ∑ b ∈ T.filter (fun b => par L b = c), ∑ b' ∈ T.erase b, F b b' := by
    rw [e4', ← sum_powersetCard_two T (fun b b' => if par L b = c then F b b' else 0), smul_sum]
    refine sum_congr rfl fun S hS => ?_
    simp only [φ, (mem_powersetCard.1 hS).2, show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true]
    congr 1
    rw [sum_filter]; refine sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  rw [e3, e4, smul_sum, ← sum_add_distrib]
  refine sum_eq_zero fun b hb => ?_
  simp only [f, F]
  rw [← FCE_sum_right, sum_erase_eq_sub (mem_filter.1 hb).1, neg_smul]
  exact neg_add_cancel _

theorem blocks_blockSet_eq {k : ℕ} {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) k) :
    blocks k (blockSet (L := L) (N := N) k c) = {c} := by
  ext a
  rw [mem_singleton]
  constructor
  · intro ha
    obtain ⟨x, hx, rfl⟩ := mem_blocks.1 ha
    exact mem_blockSet.1 hx
  · rintro rfl
    obtain ⟨x, hx⟩ := mem_blockIdx.1 hc
    exact mem_blocks.2 ⟨x, hx, mem_blockSet.1 hx⟩

theorem isSmall_two_blocks (hd : 1 ≤ d) {k : ℕ} {c₁ c₂ : Fin d → ℕ}
    (h₁ : c₁ ∈ blockIdx (L := L) (N := N) k) (h₂ : c₂ ∈ blockIdx (L := L) (N := N) k)
    (ht : Touch (blockSet (L := L) (N := N) k c₁) (blockSet k c₂)) :
    IsSmall k (blockSet (L := L) (N := N) k c₁ ∪ blockSet k c₂) := by
  classical
  have hb : blocks k (blockSet (L := L) (N := N) k c₁ ∪ blockSet k c₂) = {c₁, c₂} := by
    rw [blocks_union, blocks_blockSet_eq h₁, blocks_blockSet_eq h₂]; rfl
  refine ⟨IsPolymer.union (isPolymer_blockSet k c₁) (isPolymer_blockSet k c₂), ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := mem_blockIdx.1 h₁
    exact ⟨x, mem_union_left _ hx⟩
  · intro a ha a' ha'
    rw [hb] at ha ha'
    have hadj : ∀ u v, u ∈ ({c₁, c₂} : Finset _) → v ∈ ({c₁, c₂} : Finset _) → u ≠ v →
        BlockAdj k (blockSet (L := L) (N := N) k c₁ ∪ blockSet k c₂) u v := by
      intro u v hu hv huv
      refine ⟨hb ▸ hu, hb ▸ hv, ?_⟩
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · exact ht
      · exact touch_symm ht
      · exact absurd rfl huv
    by_cases h : a = a'
    · rw [h]
    · exact Relation.ReflTransGen.single (hadj a a' ha ha' h)
  · rw [hb]
    calc ({c₁, c₂} : Finset (Fin d → ℕ)).card ≤ 2 := card_le_two
      _ = 2 ^ 1 := rfl
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd

variable {j C V}

/-- `F(V'_B, V'_{B'}) = 0` for `j`-blocks `B, B'` such that `\bar{B ∪ B'}` is not small. -/
theorem FCE_far_of_not_small (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hjN : j + 1 < N) {ℓ : ℝ}
    (hC : GoodCov2 j ℓ C) (hV : InF j V) {b b' : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (hs : ¬ IsSmall (j + 1) (clo j (blockSet (L := L) (N := N) j b ∪ blockSet j b'))) :
    FCE C (Vpr C V b) (Vpr C V b') = 0 := by
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
  refine FCE_Vpr_far hjN hC hV hb' fun hnear => ?_
  obtain ⟨-, x, hx, y, hy, hxy⟩ := mem_filter.1 hnear
  have hx' : x ∈ nbhd j U₁ := nbhd_mono (hsub b) hx
  have hy' : y ∈ nbhd j U₂ := nbhd_mono (hsub b') hy
  have := lt_two_mul_supNorm_of_nbhd hL hjN.le (isPolymer_blockSet (j + 1) _)
    (isPolymer_blockSet (j + 1) _) hnt hx' hy'
  omega

theorem kap_of_not_small (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hjN : j + 1 < N) {ℓ : ℝ}
    (hC : GoodCov2 j ℓ C) (hV : InF j V) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hs : ¬ IsSmall (j + 1) (clo j X)) (c : Fin d → ℕ) : kap j C V X c = 0 := by
  classical
  unfold kap
  split_ifs with h1 h2
  · exfalso
    obtain ⟨b, hb⟩ := card_eq_one.1 h1
    have hbI : b ∈ blockIdx (L := L) (N := N) j := mem_blockIdx_of_mem_blocks (hb ▸ mem_singleton_self b)
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
    have hz : ∀ b ∈ blocks j X, ∀ b' ∈ (blocks j X).erase b, FCE C (Vpr C V b) (Vpr C V b') = 0 := by
      intro b hbX b' hb'
      have hne := ne_of_mem_erase hb'
      have hb'X := mem_of_mem_erase hb'
      rw [hb] at hbX hb'X
      simp only [mem_insert, mem_singleton] at hbX hb'X
      rcases hbX with rfl | rfl <;> rcases hb'X with rfl | rfl
      · exact absurd rfl hne
      · exact FCE_far_of_not_small hd hL hjN hC hV hb₁ hb₂ hs'
      · exact FCE_far_of_not_small hd hL hjN hC hV hb₂ hb₁ (by rwa [union_comm])
      · exact absurd rfl hne
    rw [sum_eq_zero fun b hb => sum_eq_zero fun b' hb' => hz b (mem_filter.1 hb).1 b' hb',
      smul_zero]
  · rfl

/-- **`∑_{U ⊇ B_+} J(B_+, U) = 0`** (Brydges–Slade (5.19)). -/
theorem Jh_sum_U (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hjN : j + 1 < N) {ℓ : ℝ}
    (hC : GoodCov2 j ℓ C) (hV : InF j V) (c : Fin d → ℕ) :
    ∑ U ∈ (smallSets (d := d) (L := L) (N := N) (j + 1)).filter (fun U => blockSet (j + 1) c ⊆ U),
      Jh j C V c U = 0 := by
  classical
  set Sc := (smallSets (d := d) (L := L) (N := N) (j + 1)).filter (fun U => blockSet (j + 1) c ⊆ U)
  have e1 : ∑ U ∈ Sc, Jh j C V c U = ∑ U ∈ Sc,
      ∑ X ∈ ((Pj (d := d) (L := L) (N := N) j univ).filter (fun X => clo j X ∈ Sc)).filter
        (fun X => clo j X = U), kap j C V X c := by
    refine sum_congr rfl fun U hU => ?_
    rw [Jh, if_pos (mem_smallSets_filter.1 hU).1, filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext X; simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ hU, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  rw [e1, sum_fiberwise_of_maps_to (fun X hX => (mem_filter.1 hX).2)]
  have h := kap_sum_zero (L := L) (N := N) j C V c
  rw [← sum_filter_add_sum_filter_not (Pj (d := d) (L := L) (N := N) j univ)
    (fun X => clo j X ∈ Sc)] at h
  rw [← h]
  refine (add_eq_left.2 ?_).symm
  refine sum_eq_zero ?_
  · intro X hX
    obtain ⟨hX1, hX2⟩ := mem_filter.1 hX
    have hXp := (mem_Pj.1 hX1).2
    by_cases hs : IsSmall (j + 1) (clo j X)
    · have hc : ¬ blockSet (L := L) (N := N) (j + 1) c ⊆ clo j X := fun h =>
        hX2 (mem_smallSets_filter.2 ⟨hs, h⟩)
      have hcX : c ∉ blocks (j + 1) X := fun hc' => hc (by
        rw [← blocks_clo] at hc'; exact blockSet_subset (isPolymer_clo j X) hc')
      have hf : (blocks j X).filter (fun b => par L b = c) = ∅ :=
        filter_eq_empty_iff.2 fun b hb hbc => hcX (hbc ▸ par_mem_blocks hb)
      unfold kap; simp only [hf, sum_empty, smul_zero]; split_ifs <;> rfl
    · exact kap_of_not_small hd hL hjN hC hV hXp hs c

end Map

end

end Step2
