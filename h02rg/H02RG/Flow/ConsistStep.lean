import Flow.EmbLoc

/-!
# `emb` and the renormalisation group map

For a `(j+1)`-polymer `U ⊆ Λ_N` near the origin, all ingredients of `K_{j+1}(U)` are supported
near `U`, where `emb` preserves the geometry and the algebra.  Hence `emb` maps each ingredient
on `Λ_N` to the corresponding one on `Λ_M` (`E_Inext`, …, `E_Kterm`), and the index sets `𝒢(U)`
and `𝒢(emb U)` correspond (`gemb`, `gpre`), which gives `emb K_{j+1}(U) = K'_{j+1}(emb U)`
(`E_Knext`).  The analogue of this argument for automorphisms is `AE_Knext`.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L : ℕ} [NeZero L] {N M : ℕ}

/-- `x` is within `r` of `U`. -/
def InB (U : Finset (Lam d L N)) (r : ℕ) (x : Lam d L N) : Prop := ∃ u ∈ U, supNorm (x - u) ≤ r

theorem inB_of_mem {U : Finset (Lam d L N)} {x : Lam d L N} (hx : x ∈ U) (r : ℕ) : InB U r x :=
  ⟨x, hx, by rw [sub_self, supNorm_zero]; exact Nat.zero_le _⟩

theorem InB.near {U : Finset (Lam d L N)} {r s : ℕ} {x y : Lam d L N} (h : InB U r x)
    (hy : supNorm (y - x) ≤ s) : InB U (r + s) y := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨u, hu, ?_⟩
  have := supNorm_add_le (y - x) (x - u)
  rw [sub_add_sub_cancel] at this
  omega

theorem InB.nbhd {U X : Finset (Lam d L N)} {r : ℕ} {j : ℕ} (hX : ∀ x ∈ X, InB U r x)
    {y : Lam d L N} (hy : y ∈ nbhd j X) : InB U (r + 2 ^ d * L ^ j) y := by
  obtain ⟨x, hx, h⟩ := exists_near_of_mem_nbhd hy
  exact (hX x hx).near h

theorem InB.blk {U : Finset (Lam d L N)} {r : ℕ} {j : ℕ} {x y : Lam d L N} (h : InB U r x)
    (hxy : blk j y = blk j x) : InB U (r + L ^ j) y :=
  h.near (supNorm_lt_of_blk_eq hxy).le

theorem hPj {j N : ℕ} (hj : j + 2 ≤ N) : j ≤ N := by omega

/-! ### The setting -/

section Setting

variable (hNM : N ≤ M) (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 2 ≤ N)
  {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
  (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N)

include hd hL hj in
theorem num_facts : 16 * L ^ (j + 1) ≤ L ^ N ∧ 2 ^ (d + 6) * L ^ j ≤ L ^ N ∧
    16 * L ^ j ≤ L ^ N ∧ 16 ≤ L ^ N := by
  have h16 : 16 ≤ L := by
    have : 2 ^ 4 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hLL : 2 ^ (d + 6) ≤ L * L := by
    calc 2 ^ (d + 6) ≤ 2 ^ (d + 3) * 2 ^ (d + 3) := by
          rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ L * L := Nat.mul_le_mul hL hL
  have hP : 0 < L ^ j := pow_pos (by omega) j
  have hN : L ^ (j + 2) ≤ L ^ N := Nat.pow_le_pow_right (by omega) hj
  have e1 : L ^ (j + 2) = L * L * L ^ j := by ring
  have e2 : L ^ (j + 1) = L * L ^ j := by ring
  rw [e1] at hN
  have k1 : 16 * L ^ (j + 1) ≤ L ^ N := by
    rw [e2]
    calc 16 * (L * L ^ j) ≤ L * (L * L ^ j) := Nat.mul_le_mul_right _ h16
      _ = L * L * L ^ j := by ring
      _ ≤ L ^ N := hN
  have k2 : 16 * L ^ j ≤ 16 * L ^ (j + 1) := by
    rw [e2]; exact Nat.mul_le_mul_left 16 (Nat.le_mul_of_pos_left _ (by omega))
  refine ⟨k1, (Nat.mul_le_mul_right _ hLL).trans hN, k2.trans k1, ?_⟩
  have : 16 ≤ 16 * L ^ j := Nat.le_mul_of_pos_right 16 hP
  omega

include hd hL hj hUc hUd

theorem inB_pt {r : ℕ} (hr : r ≤ 2 ^ (d + 2) * L ^ j) {x : Lam d L N} (hx : InB U r x) :
    16 * supNorm x ≤ 5 * L ^ N := by
  obtain ⟨-, h2, -, -⟩ := num_facts hd hL hj
  obtain ⟨u, hu, h⟩ := hx
  have h1 := hUc u hu
  have h3 := supNorm_add_le (x - u) u
  rw [sub_add_cancel] at h3
  have : 16 * (2 ^ (d + 2) * L ^ j) ≤ L ^ N := by
    calc 16 * (2 ^ (d + 2) * L ^ j) = 2 ^ (d + 6) * L ^ j := by ring
      _ ≤ L ^ N := h2
  omega

theorem inB_pt6 {r : ℕ} (hr : r ≤ 2 ^ (d + 2) * L ^ j) {x : Lam d L N} (hx : InB U r x) :
    16 * supNorm x ≤ 6 * L ^ N := by
  have := inB_pt hd hL hj hUc hUd hr hx; omega

theorem inB_two {r : ℕ} (hr : r ≤ 2 ^ (d + 2) * L ^ j) {x : Lam d L N} (hx : InB U r x) :
    2 * supNorm x + 2 < L ^ N := by
  have := inB_pt hd hL hj hUc hUd hr hx
  obtain ⟨-, -, -, h4⟩ := num_facts hd hL hj
  omega

theorem inB_near {r : ℕ} (hr : r ≤ 2 ^ (d + 2) * L ^ j) {x y : Lam d L N} (hx : InB U r x)
    (hy : InB U r y) : supNorm x + supNorm y + supNorm (x - y) < L ^ N := by
  have h1 := inB_pt hd hL hj hUc hUd hr hx
  have h2 := inB_pt hd hL hj hUc hUd hr hy
  obtain ⟨-, h3, -, h4⟩ := num_facts hd hL hj
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  have h5 := hUd u hu v hv
  have e : x - y = (x - u) + ((u - v) + (v - y)) := by abel
  have h6 := supNorm_add_le (x - u) ((u - v) + (v - y))
  have h7 := supNorm_add_le (u - v) (v - y)
  rw [supNorm_sub_comm v y] at h7
  rw [← e] at h6
  have : 32 * (2 ^ (d + 2) * L ^ j) ≤ 2 * L ^ N := by
    calc 32 * (2 ^ (d + 2) * L ^ j) = 2 * (2 ^ (d + 6) * L ^ j) := by ring
      _ ≤ 2 * L ^ N := Nat.mul_le_mul_left 2 h3
  omega

end Setting

theorem embE_gexp {x : EvR (Lam d L N)} (hx : IsNilpotent x) :
    embE N M (gexp x) = gexp (embE N M x) := IsNilpotent.map_exp hx (embE N M)

/-! ### The ingredients of `K_{j+1}` -/

section Ingredients

variable (hNM : N ≤ M) (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 2 ≤ N)
  {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
  (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N)
  {C : Matrix (Lam d L N) (Lam d L N) ℝ} {C' : Matrix (Lam d L M) (Lam d L M) ℝ} {V : Vcoup}
  {K : Act d L N} {K' : Act d L M}
include hNM hd hL hj hUc hUd

theorem pt6_of_mem {x : Lam d L N} (hx : x ∈ U) : 16 * supNorm x ≤ 6 * L ^ N :=
  inB_pt6 hd hL hj hUc hUd (Nat.zero_le _) (inB_of_mem hx 0)

theorem pt5_of_mem {x : Lam d L N} (hx : x ∈ U) : 16 * supNorm x ≤ 5 * L ^ N :=
  inB_pt hd hL hj hUc hUd (Nat.zero_le _) (inB_of_mem hx 0)

theorem P_le : L ^ j ≤ 2 ^ (d + 2) * L ^ j := Nat.le_mul_of_pos_left _ (by positivity)

theorem blockSet_bemb' {x : Lam d L N} (hx : x ∈ U) :
    blockSet j (bemb L N M j (blk j x)) = (blockSet (L := L) (N := N) j (blk j x)).image (emb N M) :=
  blockSet_bemb hNM (hPj hj) (num_facts hd hL hj).2.2.1 (pt6_of_mem hNM hd hL hj hUc hUd hx)

theorem block_two {x : Lam d L N} (hx : x ∈ U) :
    ∀ y ∈ blockSet (L := L) (N := N) j (blk j x), 2 * supNorm y + 2 < L ^ N := fun y hy => by
  have h := (inB_of_mem hx 0).blk (Loc.mem_blockSet.1 hy)
  rw [zero_add] at h
  exact inB_two hd hL hj hUc hUd (P_le hNM hd hL hj hUc hUd) h

theorem E_Inext (huV : uVnext j C' V K' = uVnext j C V K) {x : Lam d L N} (hx : x ∈ U) :
    embE N M (Inext j C V K (blk j x)) = Inext j C' V K' (bemb L N M j (blk j x)) := by
  rw [Inext, Inext, blockSet_bemb' hNM hd hL hj hUc hUd hx, card_image_emb hNM, huV, map_smul,
    embE_gexp (isNilpotent_VE _ _).neg, map_neg, embE_VE hNM _ (block_two hNM hd hL hj hUc hUd hx)]

theorem blocks_image' {W : Finset (Lam d L N)} (hW : W ⊆ U) :
    blocks j (W.image (emb N M)) = (blocks j W).image (bemb L N M j) :=
  blocks_image hNM (hPj hj) (num_facts hd hL hj).2.2.1 fun x hx =>
    pt6_of_mem hNM hd hL hj hUc hUd (hW hx)

theorem bemb_injOn' {W : Finset (Lam d L N)} (hW : W ⊆ U) :
    Set.InjOn (bemb L N M j) (blocks j W : Set (Fin d → ℕ)) :=
  bemb_injOn hNM (hPj hj) (num_facts hd hL hj).2.2.1 fun x hx =>
    pt6_of_mem hNM hd hL hj hUc hUd (hW hx)

theorem E_InextPow (huV : uVnext j C' V K' = uVnext j C V K) {W : Finset (Lam d L N)}
    (hW : W ⊆ U) : embE N M (InextPow j C V K W) = InextPow j C' V K' (W.image (emb N M)) := by
  rw [InextPow, InextPow, map_prod, blocks_image' hNM hd hL hj hUc hUd hW,
    prod_image (bemb_injOn' hNM hd hL hj hUc hUd hW)]
  refine prod_congr rfl fun b hb => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  exact E_Inext hNM hd hL hj hUc hUd huV (hW hx)

theorem E_dI (huV : uVnext j C' V K' = uVnext j C V K) {x : Lam d L N} (hx : x ∈ U) :
    embE2 N M (dI j C V K (blk j x)) = dI j C' V K' (bemb L N M j (blk j x)) := by
  rw [dI, dI, map_sub, embE2_thetaE hNM, embE2_inclE hNM, E_Inext hNM hd hL hj hUc hUd huV hx,
    embE_gexp (isNilpotent_VE _ _).neg, map_neg, embE_VE hNM _ (block_two hNM hd hL hj hUc hUd hx),
    blockSet_bemb' hNM hd hL hj hUc hUd hx]

theorem E_dIPow (huV : uVnext j C' V K' = uVnext j C V K) {W : Finset (Lam d L N)}
    (hW : W ⊆ U) : embE2 N M (dIPow j C V K W) = dIPow j C' V K' (W.image (emb N M)) := by
  rw [dIPow, dIPow, map_prod, blocks_image' hNM hd hL hj hUc hUd hW,
    prod_image (bemb_injOn' hNM hd hL hj hUc hUd hW)]
  refine prod_congr rfl fun b hb => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  exact E_dI hNM hd hL hj hUc hUd huV (hW hx)

theorem E_Kext
    (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB U (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)))
    {W : Finset (Lam d L N)} (hWp : IsPolymer j W) (hW : W ⊆ U) :
    embE N M (Kext j K W) = Kext j K' (W.image (emb N M)) := by
  rw [Kext, Kext, map_prod, comp_image hNM (hPj hj) (num_facts hd hL hj).2.2.1
      fun x hx => pt5_of_mem hNM hd hL hj hUc hUd (hW hx),
    prod_image fun Y _ Y' _ e => image_emb_injective hNM e]
  refine prod_congr rfl fun Y hY => ?_
  exact hKK Y (isConn_of_mem_comp hWp hY) fun x hx =>
    inB_of_mem (hW (subset_of_mem_comp hY hx)) _

theorem E_Ktil (huV : uVnext j C' V K' = uVnext j C V K)
    (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB U (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)))
    {W : Finset (Lam d L N)} (hWp : IsPolymer j W) (hW : W ⊆ U) :
    embE2 N M (Ktil j C V K W) = Ktil j C' V K' (W.image (emb N M)) := by
  rw [Ktil, Ktil, map_sum, Pj_image hNM (hPj hj) (num_facts hd hL hj).2.2.1
      fun x hx => pt5_of_mem hNM hd hL hj hUc hUd (hW hx),
    sum_image fun Y _ Y' _ e => image_emb_injective hNM e]
  refine sum_congr rfl fun Y hY => ?_
  obtain ⟨hYW, hYp⟩ := mem_Pj.1 hY
  rw [map_mul, embE2_thetaE hNM,
    E_Kext hNM hd hL hj hUc hUd hKK (IsPolymer.sdiff hWp hYp) (sdiff_subset.trans hW),
    E_dIPow hNM hd hL hj hUc hUd huV (hYW.trans hW), image_sdiff _ _ (emb_injective' hNM)]

theorem smallSets_image {x₀ : Lam d L N} (hx₀ : x₀ ∈ U) :
    (smallSets j).filter (fun Y' : Finset (Lam d L M) =>
        blockSet j (bemb L N M j (blk j x₀)) ⊆ Y') =
      ((smallSets j).filter fun Y => blockSet (L := L) (N := N) j (blk j x₀) ⊆ Y).image
        fun Y => Y.image (emb N M) := by
  obtain ⟨-, h2, h3, -⟩ := num_facts hd hL hj
  have h2d : 16 * (2 ^ d * L ^ j) ≤ L ^ N := by
    calc 16 * (2 ^ d * L ^ j) = 2 ^ (d + 4) * L ^ j := by ring
      _ ≤ 2 ^ (d + 6) * L ^ j :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ L ^ N := h2
  have hr : 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hB : ∀ y : Lam d L N, supNorm (y - x₀) ≤ 2 ^ d * L ^ j → 16 * supNorm y ≤ 5 * L ^ N :=
    fun y hy => inB_pt hd hL hj hUc hUd hr ⟨x₀, hx₀, hy⟩
  have hx6 := pt6_of_mem hNM hd hL hj hUc hUd hx₀
  rw [bemb_blk hNM (hPj hj) h3 hx6]
  ext Y'
  simp only [mem_filter, mem_smallSets, mem_image]
  constructor
  · rintro ⟨hS', hb⟩
    obtain ⟨T, hT, eT, hbT, -⟩ := small_pullback hNM (hPj hj) h3 h2d
      (pt5_of_mem hNM hd hL hj hUc hUd hx₀) hB hS' hb
    exact ⟨T, ⟨hT, hbT⟩, eT⟩
  · rintro ⟨T, ⟨hT, hbT⟩, rfl⟩
    have hT' : ∀ z ∈ T, 16 * supNorm z ≤ 5 * L ^ N := fun z hz =>
      hB z (supNorm_le_of_isSmall hT hz (hbT (mem_blockSet_blk j x₀)))
    refine ⟨(isSmall_image_iff hNM (hPj hj) h3 hT').2 hT, ?_⟩
    rw [← bemb_blk hNM (hPj hj) h3 hx6, blockSet_bemb hNM (hPj hj) h3 hx6]
    exact image_subset_image hbT

theorem E_LocE (hK : InK j K) {Y : Finset (Lam d L N)} (hY : IsSmall j Y)
    (hYU : ∀ y ∈ Y, InB U (2 ^ d * L ^ j) y) (hKY : embE N M (K Y) = K' (Y.image (emb N M)))
    {B : Finset (Lam d L N)} (hB : ∀ y ∈ B, 2 * supNorm y + 2 < L ^ N) :
    embE N M (LocE Y B (K Y)) = LocE (Y.image (emb N M)) (B.image (emb N M)) (K' (Y.image (emb N M))) := by
  have hr1 : 2 ^ d * L ^ j + 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by
    calc 2 ^ d * L ^ j + 2 ^ d * L ^ j = 2 * (2 ^ d * L ^ j) := by ring
      _ ≤ 4 * (2 ^ d * L ^ j) := by omega
      _ = 2 ^ (d + 2) * L ^ j := by ring
  have hr0 : 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by omega
  have hRn : ∀ x ∈ (nbhd j Y : Set (Lam d L N)), ∀ y ∈ (nbhd j Y : Set (Lam d L N)),
      supNorm x + supNorm y + supNorm (x - y) < L ^ N := fun x hx y hy =>
    inB_near hd hL hj hUc hUd hr1 (InB.nbhd hYU (mem_coe.1 hx)) (InB.nbhd hYU (mem_coe.1 hy))
  refine Subtype.ext ?_
  rw [coe_embE, coe_LocE, coe_LocE, ← hKY, coe_embE]
  exact LocXY_emb hNM (region_small hd hL (by omega) hY) hRn hY.2.1.1
    (fun y hy => inB_two hd hL hj hUc hUd hr0 (hYU y hy)) B hB _ (hK.loc Y ⟨hY.1, hY.2.1⟩)

theorem E_Jb (hK : InK j K)
    (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB U (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)))
    {x₀ : Lam d L N} (hx₀ : x₀ ∈ U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    embE N M (Jb j K (blk j x₀) X) = Jb j K' (bemb L N M j (blk j x₀)) (X.image (emb N M)) := by
  obtain ⟨-, -, h3, -⟩ := num_facts hd hL hj
  have hB' := blockSet_bemb' hNM hd hL hj hUc hUd (M := M) hx₀
  have hX5 : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N := fun x hx =>
    pt5_of_mem hNM hd hL hj hUc hUd (hX hx)
  have hinj := emb_injective' (d := d) (L := L) hNM
  have hjM : j + 1 < M := by omega
  have hjN : j + 1 < N := by omega
  have c1 : (j + 1 < M ∧ IsSmall j (X.image (emb N M)) ∧
      blockSet j (bemb L N M j (blk j x₀)) ⊆ X.image (emb N M)) ↔
      (j + 1 < N ∧ IsSmall j X ∧ blockSet (L := L) (N := N) j (blk j x₀) ⊆ X) := by
    rw [hB', image_emb_subset_iff hNM, isSmall_image_iff hNM (hPj hj) h3 hX5]
    simp only [hjM, hjN, true_and]
  have c2 : X.image (emb N M) = blockSet j (bemb L N M j (blk j x₀)) ↔
      X = blockSet (L := L) (N := N) j (blk j x₀) := by
    rw [hB']; exact (image_emb_injective hNM).eq_iff
  have hr : 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hBt := block_two hNM hd hL hj hUc hUd (M := M) hx₀
  unfold Jb
  by_cases hc : j + 1 < N ∧ IsSmall j X ∧ blockSet (L := L) (N := N) j (blk j x₀) ⊆ X
  · rw [if_pos hc, if_pos (c1.2 hc)]
    by_cases hx : X = blockSet (L := L) (N := N) j (blk j x₀)
    · rw [if_pos hx, if_pos (c2.2 hx), map_neg, map_sum]
      refine congrArg Neg.neg ?_
      have hS : ((smallSets j).filter fun Y' : Finset (Lam d L M) =>
          blockSet j (bemb L N M j (blk j x₀)) ⊆ Y' ∧ Y' ≠ blockSet j (bemb L N M j (blk j x₀))) =
          ((smallSets j).filter fun Y => blockSet (L := L) (N := N) j (blk j x₀) ⊆ Y ∧
            Y ≠ blockSet (L := L) (N := N) j (blk j x₀)).image fun Y => Y.image (emb N M) := by
        rw [← filter_filter, smallSets_image hNM hd hL hj hUc hUd hx₀, filter_image, ← filter_filter]
        refine congrArg _ (filter_congr fun Y _ => ?_)
        rw [hB']
        exact not_congr (image_emb_injective hNM).eq_iff
      rw [hS, sum_image fun Y _ Y' _ e => image_emb_injective hNM e]
      refine sum_congr rfl fun Y hY => ?_
      obtain ⟨hY1, hY2, -⟩ := mem_filter.1 hY
      have hYs := mem_smallSets.1 hY1
      have hYU : ∀ y ∈ Y, InB U (2 ^ d * L ^ j) y := fun y hy =>
        ⟨x₀, hx₀, supNorm_le_of_isSmall hYs hy (hY2 (mem_blockSet_blk j x₀))⟩
      rw [E_LocE hNM hd hL hj hUc hUd hK hYs hYU (hKK Y ⟨hYs.1, hYs.2.1⟩ hYU) hBt, hB']
    · rw [if_neg hx, if_neg (mt c2.1 hx)]
      have hYU : ∀ y ∈ X, InB U (2 ^ d * L ^ j) y := fun y hy => inB_of_mem (hX hy) _
      rw [E_LocE hNM hd hL hj hUc hUd hK hc.2.1 hYU (hKK X ⟨hc.2.1.1, hc.2.1.2.1⟩ hYU) hBt, hB']
  · rw [if_neg hc, if_neg (mt c1.1 hc), _root_.map_zero]

theorem E_KchkC (huV : uVnext j C' V K' = uVnext j C V K) (hK : InK j K)
    (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB U (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)))
    {W : Finset (Lam d L N)} (hWp : IsPolymer j W) (hW : W ⊆ U) :
    embE2 N M (KchkC j C V K W) = KchkC j C' V K' (W.image (emb N M)) := by
  rw [KchkC, KchkC, map_sub, E_Ktil hNM hd hL hj hUc hUd huV hKK hWp hW, map_sum,
    blocks_image' hNM hd hL hj hUc hUd hW, sum_image (bemb_injOn' hNM hd hL hj hUc hUd hW)]
  refine congrArg (fun t => Ktil j C' V K' (W.image (emb N M)) - t) ?_
  refine sum_congr rfl fun b hb => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  rw [embE2_thetaE hNM, E_Jb hNM hd hL hj hUc hUd hK hKK (hW hx) hW]

theorem E_Kchk (huV : uVnext j C' V K' = uVnext j C V K) (hK : InK j K)
    (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB U (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)))
    {X : Finset (Lam d L N)} (hXp : IsPolymer j X) (hX : X ⊆ U) :
    embE2 N M (Kchk j C V K X) = Kchk j C' V K' (X.image (emb N M)) := by
  rw [Kchk, Kchk, map_prod, comp_image hNM (hPj hj) (num_facts hd hL hj).2.2.1
      fun x hx => pt5_of_mem hNM hd hL hj hUc hUd (hX hx),
    prod_image fun Y _ Y' _ e => image_emb_injective hNM e]
  exact prod_congr rfl fun W hW => E_KchkC hNM hd hL hj hUc hUd huV hK hKK
    (isPolymer_of_mem_comp hXp hW) ((subset_of_mem_comp hW).trans hX)

end Ingredients

/-! ### The index sets `𝒢(U)` and `𝒢(emb U)` -/

/-- `emb` on pairs `(B, X)`. -/
def pemb (L N M j : ℕ) [NeZero L] (p : (Fin d → ℕ) × Finset (Lam d L N)) :
    (Fin d → ℕ) × Finset (Lam d L M) := (bemb L N M j p.1, p.2.image (emb N M))

/-- The inverse of `pemb`. -/
def ppre (L N M j : ℕ) [NeZero L] (p : (Fin d → ℕ) × Finset (Lam d L M)) :
    (Fin d → ℕ) × Finset (Lam d L N) := (bpre L N M j p.1, p.2.image (emb M N))

/-- `emb` on `𝒢(U)`. -/
def gemb (L N M j : ℕ) [NeZero L] (g : GT d L N) : GT d L M :=
  (g.1.image (pemb L N M j), g.2.image (emb N M))

/-- The inverse of `gemb`. -/
def gpre (L N M j : ℕ) [NeZero L] (g : GT d L M) : GT d L N :=
  (g.1.image (ppre L N M j), g.2.image (emb M N))

/-- A pair `(B, X)` in `U`. -/
def FitsP (j : ℕ) (U : Finset (Lam d L N)) (p : (Fin d → ℕ) × Finset (Lam d L N)) : Prop :=
  p.2 ⊆ U ∧ ∃ x ∈ U, p.1 = blk j x

/-- An element of `𝒢` in `U`. -/
def Fits (j : ℕ) (U : Finset (Lam d L N)) (g : GT d L N) : Prop :=
  g.2 ⊆ U ∧ ∀ p ∈ g.1, FitsP j U p

theorem fits_of_mem {j : ℕ} {U : Finset (Lam d L N)} {g : GT d L N} (hg : g ∈ Gset j U) :
    Fits j U g := by
  obtain ⟨-, f2, -, f4⟩ := Gset_facts hg
  refine ⟨f2, fun p hp => ⟨(f4 p hp).2.2.2, ?_⟩⟩
  obtain ⟨x, hx⟩ := nonempty_of_mem_pairsU (f4 p hp).1
  exact ⟨x, (f4 p hp).2.2.1 hx, (Loc.mem_blockSet.1 hx).symm⟩

theorem Xcal_gemb (L N M j : ℕ) [NeZero L] (g : GT d L N) :
    Xcal (gemb L N M j g).1 = (Xcal g.1).image (emb N M) := by
  show (g.1.image (pemb L N M j)).biUnion Prod.snd = (g.1.biUnion Prod.snd).image (emb N M)
  rw [image_biUnion, biUnion_image]; rfl

theorem image_image_emb_of_subset (hNM : N ≤ M) {U : Finset (Lam d L N)}
    {Z : Finset (Lam d L M)} (hZ : Z ⊆ U.image (emb N M)) :
    (Z.image (emb M N)).image (emb N M) = Z ∧ Z.image (emb M N) ⊆ U := by
  constructor
  · rw [image_image]
    conv_rhs => rw [← image_id (s := Z)]
    refine image_congr fun z hz => ?_
    obtain ⟨x, -, rfl⟩ := mem_image.1 (hZ hz)
    simp only [Function.comp_apply, id, emb_emb hNM]
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 (hZ hz)
    rwa [emb_emb hNM]

theorem image_image_emb (hNM : N ≤ M) (Z : Finset (Lam d L N)) :
    (Z.image (emb N M)).image (emb M N) = Z := by
  rw [image_image]
  conv_rhs => rw [← image_id (s := Z)]
  exact image_congr fun z _ => by simp only [Function.comp_apply, id, emb_emb hNM]

section Gcal

variable (hNM : N ≤ M) (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 2 ≤ N)
  {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
  (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N)
include hNM hd hL hj hUc hUd

theorem pemb_inj {p q : (Fin d → ℕ) × Finset (Lam d L N)} (hp : FitsP j U p) (hq : FitsP j U q) :
    pemb L N M j p = pemb L N M j q ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨-, x, hx, e1⟩ := hp
  obtain ⟨-, y, hy, e2⟩ := hq
  have h3 := (num_facts hd hL hj).2.2.1
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [pemb] at h1 h2
  refine Prod.ext ?_ (image_emb_injective hNM h2)
  rw [e1, e2] at h1 ⊢
  rw [← bpre_bemb hNM (hPj hj) h3 (pt6_of_mem hNM hd hL hj hUc hUd hx),
    ← bpre_bemb hNM (hPj hj) h3 (pt6_of_mem hNM hd hL hj hUc hUd hy), h1]

theorem pemb_injOn {s : Finset ((Fin d → ℕ) × Finset (Lam d L N))} (hs : ∀ p ∈ s, FitsP j U p) :
    Set.InjOn (pemb L N M j) (↑s : Set ((Fin d → ℕ) × Finset (Lam d L N))) := fun p hp q hq e =>
  (pemb_inj hNM hd hL hj hUc hUd (hs p hp) (hs q hq)).1 e

theorem pairsU_iff {p : (Fin d → ℕ) × Finset (Lam d L N)} (hp : FitsP j U p) :
    pemb L N M j p ∈ pairsU j ↔ p ∈ pairsU j := by
  obtain ⟨hp2, x, hx, e⟩ := hp
  have h3 := (num_facts hd hL hj).2.2.1
  have hB' := blockSet_bemb' hNM hd hL hj hUc hUd (M := M) hx
  rw [mem_pairsU, mem_pairsU]
  simp only [pemb]
  rw [e, hB', mem_blockIdx, mem_blockIdx, hB', image_nonempty, image_emb_subset_iff hNM,
    isSmall_image_iff hNM (hPj hj) h3 fun y hy => pt5_of_mem hNM hd hL hj hUc hUd (hp2 hy)]

theorem inB_bbox {s : Finset ((Fin d → ℕ) × Finset (Lam d L N))} (hs : ∀ p ∈ s, FitsP j U p)
    {y : Lam d L N} (hy : y ∈ Bbox j s) : InB U (L ^ j + 2 ^ d * L ^ j) y := by
  obtain ⟨p, hp, hy⟩ := mem_biUnion.1 hy
  obtain ⟨-, x, hx, e⟩ := hs p hp
  rw [e] at hy
  refine InB.nbhd (fun z hz => ?_) hy
  have := (inB_of_mem hx 0).blk (Loc.mem_blockSet.1 hz)
  rwa [zero_add] at this

theorem r_bbox : L ^ j + 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  calc L ^ j + 2 ^ d * L ^ j = (1 + 2 ^ d) * L ^ j := by ring
    _ ≤ (2 ^ d + 2 ^ d) * L ^ j := Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 ^ (d + 2) * L ^ j := Nat.mul_le_mul_right _ (by rw [pow_add]; omega)

theorem nbhd_blockSet_image {x : Lam d L N} (hx : x ∈ U) :
    nbhd j (blockSet j (bemb L N M j (blk j x))) =
      (nbhd j (blockSet (L := L) (N := N) j (blk j x))).image (emb N M) := by
  obtain ⟨-, h2, h3, -⟩ := num_facts hd hL hj
  have h2d : 16 * (2 ^ d * L ^ j) ≤ L ^ N := by
    calc 16 * (2 ^ d * L ^ j) = 2 ^ (d + 4) * L ^ j := by ring
      _ ≤ 2 ^ (d + 6) * L ^ j :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ L ^ N := h2
  rw [blockSet_bemb' hNM hd hL hj hUc hUd hx]
  refine nbhd_image hNM (hPj hj) h3 h2d fun y ⟨z, hz, hyz⟩ => ?_
  have h1 := (inB_of_mem hx 0).blk (Loc.mem_blockSet.1 hz)
  rw [zero_add] at h1
  exact inB_pt hd hL hj hUc hUd (r_bbox hNM hd hL hj hUc hUd) (h1.near hyz)

theorem Bbox_gemb {g : GT d L N} (hg : Fits j U g) :
    Bbox j (gemb L N M j g).1 = (Bbox j g.1).image (emb N M) := by
  show (g.1.image (pemb L N M j)).biUnion (fun p => nbhd j (blockSet j p.1)) =
    (g.1.biUnion fun p => nbhd j (blockSet (L := L) (N := N) j p.1)).image (emb N M)
  rw [image_biUnion, biUnion_image]
  refine biUnion_congr rfl fun p hp => ?_
  obtain ⟨-, x, hx, e⟩ := hg.2 p hp
  simp only [pemb]
  rw [e, nbhd_blockSet_image hNM hd hL hj hUc hUd hx]

theorem GCond_iff {g : GT d L N} (hg : Fits j U g) :
    GCond j U g ↔ GCond j (U.image (emb N M)) (gemb L N M j g) := by
  obtain ⟨-, -, h3, -⟩ := num_facts hd hL hj
  have hj1 : j + 1 ≤ N := by omega
  have hQ := (num_facts hd hL hj).1
  have hsub : ∀ {X : Finset (Lam d L N)}, X ⊆ U → ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N :=
    fun hX x hx => pt6_of_mem hNM hd hL hj hUc hUd (hX hx)
  have hXc : Xcal g.1 ⊆ U := biUnion_subset.2 fun p hp => (hg.2 p hp).1
  unfold GCond
  refine and_congr (isPolymer_image_iff hNM (hPj hj) h3 (hsub hg.1)).symm ?_
  refine and_congr ?_ ?_
  · show _ ↔ g.1.image (pemb L N M j) ⊆ pairsU j
    rw [image_subset_iff]
    exact ⟨fun h p hp => (pairsU_iff hNM hd hL hj hUc hUd (hg.2 p hp)).2 (h hp),
      fun h p hp => (pairsU_iff hNM hd hL hj hUc hUd (hg.2 p hp)).1 (h p hp)⟩
  refine and_congr ?_ ?_
  · show _ ↔ ∀ p ∈ g.1.image (pemb L N M j), ∀ q ∈ g.1.image (pemb L N M j), p.2 = q.2 → p = q
    simp only [forall_mem_image]
    refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
    rw [pemb_inj hNM hd hL hj hUc hUd (hg.2 p hp) (hg.2 q hq)]
    simp only [pemb]
    rw [(image_emb_injective hNM).eq_iff]
  refine and_congr ?_ ?_
  · show _ ↔ ∀ p ∈ g.1.image (pemb L N M j), ∀ q ∈ g.1.image (pemb L N M j),
      p.2 ≠ q.2 → ¬ Touch p.2 q.2
    simp only [forall_mem_image]
    refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
    simp only [pemb]
    rw [(image_emb_injective hNM).ne_iff, touch_image_iff hNM (hPj hj) h3
      (hsub (hg.2 p hp).1) (hsub (hg.2 q hq).1)]
  refine and_congr ?_ ?_
  · show _ ↔ ¬ Touch (Xcal (gemb L N M j g).1) (g.2.image (emb N M))
    rw [Xcal_gemb, touch_image_iff hNM (hPj hj) h3 (hsub hXc) (hsub hg.1)]
  · show _ ↔ clo j (g.2.image (emb N M) ∪ Bbox j (gemb L N M j g).1) = U.image (emb N M)
    have hA : ∀ x ∈ g.2 ∪ Bbox j g.1, 16 * supNorm x ≤ 6 * L ^ N := by
      intro x hx
      rcases mem_union.1 hx with hx | hx
      · exact hsub hg.1 x hx
      · exact inB_pt6 hd hL hj hUc hUd (r_bbox hNM hd hL hj hUc hUd) (inB_bbox hNM hd hL hj hUc hUd hg.2 hx)
    rw [Bbox_gemb hNM hd hL hj hUc hUd hg, ← image_union, clo_image hNM hj1 hQ hA,
      (image_emb_injective hNM).eq_iff]

theorem gpre_spec {g : GT d L M} (hg : g ∈ Gset j (U.image (emb N M))) :
    Fits j U (gpre L N M j g) ∧ gemb L N M j (gpre L N M j g) = g := by
  obtain ⟨-, f2, -, f4⟩ := Gset_facts hg
  have h3 := (num_facts hd hL hj).2.2.1
  have hp : ∀ p ∈ g.1, ∃ x ∈ U, p.1 = blk j (emb N M x) := fun p hp => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (f4 p hp).1
    obtain ⟨x, hx, rfl⟩ := mem_image.1 ((f4 p hp).2.2.1 hz)
    exact ⟨x, hx, (Loc.mem_blockSet.1 hz).symm⟩
  have hppre : ∀ p ∈ g.1, FitsP j U (ppre L N M j p) ∧ pemb L N M j (ppre L N M j p) = p := by
    intro p hp'
    obtain ⟨x, hx, e⟩ := hp p hp'
    have hx6 := pt6_of_mem hNM hd hL hj hUc hUd hx
    obtain ⟨i1, i2⟩ := image_image_emb_of_subset hNM (f4 p hp').2.2.2
    refine ⟨⟨i2, x, hx, ?_⟩, ?_⟩
    · show bpre L N M j p.1 = blk j x
      rw [e, bpre_blk hNM (hPj hj) h3 hx6]
    · show (bemb L N M j (bpre L N M j p.1), (p.2.image (emb M N)).image (emb N M)) = p
      rw [i1, e, bpre_blk hNM (hPj hj) h3 hx6, bemb_blk hNM (hPj hj) h3 hx6, ← e]
  obtain ⟨i1, i2⟩ := image_image_emb_of_subset hNM f2
  refine ⟨⟨i2, fun p hp => ?_⟩, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    exact (hppre q hq).1
  · show ((g.1.image (ppre L N M j)).image (pemb L N M j), (g.2.image (emb M N)).image (emb N M)) = g
    rw [i1, image_image]
    refine Prod.ext ?_ rfl
    conv_rhs => rw [← image_id (s := g.1)]
    exact image_congr fun p hp => (hppre p hp).2

theorem gpre_gemb {g : GT d L N} (hg : Fits j U g) : gpre L N M j (gemb L N M j g) = g := by
  have h3 := (num_facts hd hL hj).2.2.1
  show ((g.1.image (pemb L N M j)).image (ppre L N M j), (g.2.image (emb N M)).image (emb M N)) = g
  rw [image_image_emb hNM, image_image]
  refine Prod.ext ?_ rfl
  conv_rhs => rw [← image_id (s := g.1)]
  refine image_congr fun p hp => ?_
  obtain ⟨-, x, hx, e⟩ := hg.2 p hp
  show (bpre L N M j (bemb L N M j p.1), (p.2.image (emb N M)).image (emb M N)) = p
  rw [image_image_emb hNM, e, bpre_bemb hNM (hPj hj) h3 (pt6_of_mem hNM hd hL hj hUc hUd hx), ← e]

theorem gemb_mem {g : GT d L N} (hg : g ∈ Gset j U) : gemb L N M j g ∈ Gset j (U.image (emb N M)) :=
  mem_Gset.2 ((GCond_iff hNM hd hL hj hUc hUd (fits_of_mem hg)).1 (mem_Gset.1 hg))

theorem gpre_mem {g : GT d L M} (hg : g ∈ Gset j (U.image (emb N M))) :
    gpre L N M j g ∈ Gset j U := by
  obtain ⟨h1, h2⟩ := gpre_spec hNM hd hL hj hUc hUd hg
  refine mem_Gset.2 ((GCond_iff hNM hd hL hj hUc hUd h1).2 ?_)
  rw [h2]; exact mem_Gset.1 hg

end Gcal

/-! ### `K_{j+1}` -/

section Knext

variable (hNM : N ≤ M) (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 2 ≤ N)
  {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
  (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N)
  {C : Matrix (Lam d L N) (Lam d L N) ℝ} {C' : Matrix (Lam d L M) (Lam d L M) ℝ} {V : Vcoup}
  {K : Act d L N} {K' : Act d L M}
  (huV : uVnext j C' V K' = uVnext j C V K) (hK : InK j K)
  (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, InB U (2 ^ d * L ^ j) x) →
      embE N M (K X) = K' (X.image (emb N M)))
  (hCC : ∀ x ∈ (nbhd j U : Set (Lam d L N)), ∀ y ∈ (nbhd j U : Set (Lam d L N)),
      C' (emb N M x) (emb N M y) = C x y)
  (hU : IsPolymer (j + 1) U)
include hNM hd hL hj hUc hUd huV hK hKK hCC hU

theorem E_Kterm {g : GT d L N} (hg : g ∈ Gset j U) :
    embE N M (Kterm j C V K U g) = Kterm j C' V K' (U.image (emb N M)) (gemb L N M j g) := by
  obtain ⟨a1, -, a3, -, -, -⟩ := mem_Gset'.1 hg
  obtain ⟨f1, f2, -, f4⟩ := Gset_facts hg
  have hfit := fits_of_mem hg
  have hinj := emb_injective' (d := d) (L := L) hNM
  have hF := (memHyp_loc (C := C) (V := V) (U := U) hd hK).inner_mem (IsPolymer.of_succ hU) f1 f2
    fun p hp => (f4 p hp).2.2.1
  unfold Kterm
  rw [map_mul, E_InextPow hNM hd hL hj hUc hUd huV sdiff_subset, ECE_emb hNM hCC (mem_SE.1 hF),
    map_mul, E_Kchk hNM hd hL hj hUc hUd huV hK hKK f1 f2, map_prod,
    image_sdiff _ _ hinj, image_union, ← Xcal_gemb]
  refine congrArg (fun t => InextPow j C' V K'
    ((U.image (emb N M)) \ ((gemb L N M j g).2 ∪ Xcal (gemb L N M j g).1)) *
      ECE C' (Kchk j C' V K' (g.2.image (emb N M)) * t)) ?_
  show _ = ∏ p ∈ g.1.image (pemb L N M j), thetaE (Jb j K' p.1 p.2)
  rw [prod_image (pemb_injOn hNM hd hL hj hUc hUd hfit.2)]
  refine prod_congr rfl fun p hp => ?_
  obtain ⟨hp2, x, hx, e⟩ := hfit.2 p hp
  rw [embE2_thetaE hNM, e, E_Jb hNM hd hL hj hUc hUd hK hKK hx hp2]
  simp only [pemb, e]

/-- **`emb K_{j+1}(U) = K'_{j+1}(emb U)`**. -/
theorem E_Knext :
    embE N M (Knext j C V K U) = Knext j C' V K' (U.image (emb N M)) := by
  rw [Knext_eq_Kterm, Knext_eq_Kterm, map_smul, map_sum, card_image_emb hNM, huV]
  refine congrArg (fun t => Complex.exp ((uVnext j C V K).1 * U.card) • t) ?_
  exact sum_nbij' (gemb L N M j) (gpre L N M j)
    (fun g hg => gemb_mem hNM hd hL hj hUc hUd hg)
    (fun g hg => gpre_mem hNM hd hL hj hUc hUd hg)
    (fun g hg => gpre_gemb hNM hd hL hj hUc hUd (fits_of_mem hg))
    (fun g hg => (gpre_spec hNM hd hL hj hUc hUd hg).2)
    (fun g hg => E_Kterm hNM hd hL hj hUc hUd huV hK hKK hCC hU hg)

end Knext

end

end Flow
