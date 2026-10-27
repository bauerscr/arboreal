import Step2.Map.WContract
import Flow.ConsistTransl

/-!
# Translation covariance of the coordinates (`h02uv-outline.tex`, Proposition `prop:W-contract`)

`FamCovG j F`: `F(B + t) = τ_t F(B)` for all translations `t ∈ L^j ℤ^d` (block index map `bmap`);
it implies the block-`0` form `FamCov` (`FamCovG.toFamCov`). `KCov j K`: `K(X + t) = τ_t K(X)`.

For translation-invariant `C`, covariant `V`, `𝒲` (and `K`), the outputs are covariant at scale
`j + 1` (if `j + 2 < N`): `Wnext2_cov`, `Vnext2_cov`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- Translation covariance of a block family at scale `j`, for all block-preserving
translations. -/
def FamCovG (j : ℕ) (F : Fam d L N) : Prop :=
  ∀ t : Lam d L N, (∀ i, L ^ j ∣ (co t i).val) → ∀ b ∈ blockIdx (L := L) (N := N) j,
    (F (bmap j (AffAut.transl t) b) : Alg d L N) = autAlg (Equiv.addRight t) (F b)

/-- Translation covariance of a polymer activity at scale `j`. -/
def KCov (j : ℕ) (K : Act d L N) : Prop :=
  ∀ t : Lam d L N, (∀ i, L ^ j ∣ (co t i).val) → ∀ X : Finset (Lam d L N),
    (K ((AffAut.transl t).img X) : Alg d L N) = autAlg (Equiv.addRight t) (K X)

theorem bmap_corner_zero {j : ℕ} (hj : j ≤ N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    bmap j (AffAut.transl (corner (L := L) (N := N) j b)) 0 = b := by
  have hP := Flow.presBlocks_transl' hj _ (dvd_val_corner (L := L) (N := N) hj b)
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  have e1 := img_blockSet_bmap (IsGen.transl _) hj hP h0
  rw [transl_corner_img hj hb] at e1
  have e2 := congrArg (blocks j) e1
  rw [blocks_blockSet_eq hb, blocks_blockSet_eq (bmap_mem_blockIdx (IsGen.transl _) hj hP h0)]
    at e2
  exact (Finset.singleton_injective e2).symm

theorem FamCovG.toFamCov {j : ℕ} (hj : j ≤ N) {F : Fam d L N} (h : FamCovG j F) :
    FamCov j F := by
  intro b hb
  have := h _ (dvd_val_corner (L := L) (N := N) hj b) 0 (zero_mem_blockIdx j)
  rwa [bmap_corner_zero hj hb] at this

section Transl

variable {t : Lam d L N}

theorem FC_autAlg {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : TInv C) (A B : Alg d L N) :
    autAlg (Equiv.addRight t) (FC C A B) =
      FC C (autAlg (Equiv.addRight t) A) (autAlg (Equiv.addRight t) B) := by
  have h1 : ∀ x y, C ((Equiv.addRight t) x) ((Equiv.addRight t) y) = C x y :=
    fun x y => hC t x y
  have h2 : ∀ x y, (-C) ((Equiv.addRight t) x) ((Equiv.addRight t) y) = (-C) x y :=
    fun x y => by simp only [Matrix.neg_apply, Equiv.coe_addRight, hC t x y]
  simp only [FC, map_sub, map_mul, ← expLC_autAlg _ h1, ← expLC_autAlg _ h2]

theorem bmap_image_blockIdx {j : ℕ} (hj : j ≤ N) (hP : PresBlocks j (AffAut.transl t)) :
    (blockIdx (d := d) (L := L) (N := N) j).image (bmap j (AffAut.transl t)) =
      blockIdx (d := d) (L := L) (N := N) j := by
  refine eq_of_subset_of_card_le (fun b hb => ?_) ?_
  · obtain ⟨b', hb', rfl⟩ := mem_image.1 hb
    exact bmap_mem_blockIdx (IsGen.transl t) hj hP hb'
  · rw [card_image_of_injOn (bmap_injOn (IsGen.transl t) hj hP)]

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N} {K : Act d L N}

theorem Vpr_transl (hC : TInv C) (hV : FamCovG j V) (ht : ∀ i, L ^ j ∣ (co t i).val)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Vpr C V (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (Vpr C V b) := by
  have h1 : ∀ x y, C ((Equiv.addRight t) x) ((Equiv.addRight t) y) = C x y :=
    fun x y => hC t x y
  rw [Vpr, Vpr, coe_EthE, coe_EthE, hV t ht b hb, expLC_autAlg _ h1]

theorem VprL_transl (hj : j ≤ N) (hC : TInv C) (hV : FamCovG j V)
    (ht : ∀ i, L ^ j ∣ (co t i).val) :
    autAlg (Equiv.addRight t) (VprL j C V : Alg d L N) = (VprL j C V : Alg d L N) := by
  have hP := Flow.presBlocks_transl' hj t ht
  rw [VprL, AddSubmonoidClass.coe_finsetSum, map_sum]
  conv_rhs => rw [← bmap_image_blockIdx hj hP]
  rw [sum_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) hj hP hb hb' e]
  exact sum_congr rfl fun b hb => (Vpr_transl hC hV ht hb).symm

theorem Sb_transl (hj : j ≤ N) (hC : TInv C) (hV : FamCovG j V) (hW : FamCovG j W)
    (ht : ∀ i, L ^ j ∣ (co t i).val) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Sb j C V W (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (Sb j C V W b) := by
  have h1 : ∀ x y, C ((Equiv.addRight t) x) ((Equiv.addRight t) y) = C x y :=
    fun x y => hC t x y
  rw [Sb, Sb, Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_smul,
    coe_FCE, coe_FCE, coe_EthE, coe_EthE, map_add, map_smul, FC_autAlg hC,
    ← Vpr_transl hC hV ht hb, VprL_transl hj hC hV ht, hW t ht b hb, expLC_autAlg _ h1]

theorem SX_transl (hj : j ≤ N) (hC : TInv C) (hV : FamCovG j V) (hW : FamCovG j W)
    (ht : ∀ i, L ^ j ∣ (co t i).val) (X : Finset (Lam d L N)) :
    (SX j C V W ((AffAut.transl t).img X) : Alg d L N) =
      autAlg (Equiv.addRight t) (SX j C V W X) := by
  have hP := Flow.presBlocks_transl' hj t ht
  rw [SX, SX, blocks_img_bmap hP, AddSubmonoidClass.coe_finsetSum,
    AddSubmonoidClass.coe_finsetSum, map_sum,
    sum_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) hj hP
      (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
  exact sum_congr rfl fun b hb => Sb_transl hj hC hV hW ht (mem_blockIdx_of_mem_blocks hb)

theorem Bp_transl (hj : j + 1 ≤ N) (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (AffAut.transl t).img (Bp (L := L) (N := N) j b) = Bp j (bmap j (AffAut.transl t) b) := by
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hP1 := Flow.presBlocks_transl' hj t ht
  obtain ⟨x, -, rfl⟩ := mem_image.1 hb
  have hb1 : blk (j + 1) x ∈ blockIdx (L := L) (N := N) (j + 1) := mem_image_of_mem _ (mem_univ _)
  rw [Bp, Bp, clo_blockSet hb, clo_blockSet (bmap_mem_blockIdx (IsGen.transl t) (by omega) hP hb),
    ← blk_succ, img_blockSet_bmap (IsGen.transl t) hj hP1 hb1, bmap_blk hP1, bmap_blk hP, blk_succ]

theorem LS_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V) (hWc : FamCovG j W)
    (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (LS j C V W (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (LS j C V W b) := by
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hsm : IsSmall (j + 1) (Bp (L := L) (N := N) j b) :=
    isSmall_clo (isSmall_blockSet_of_mem hb)
  have hR := region_small hd hL (by omega : (j + 1) + 1 < N) hsm
  have hF := SX_mem' hd hL (by omega) hC hV hW b
  rw [LS, LS, coe_Loc2E, coe_Loc2E, Loc2XY_transl hR hsm.2.1.1 t _ hF,
    Bp_transl (by omega) ht hb, img_blockSet_bmap (IsGen.transl t) (by omega) hP hb,
    ← SX_transl (by omega) hCt hVc hWc ht', Bp_transl (by omega) ht hb]

theorem Wp_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V) (hWc : FamCovG j W)
    (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Wp j C V W (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (Wp j C V W b) := by
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  rw [Wp, Wp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub,
    Sb_transl (by omega) hCt hVc hWc ht' hb, LS_transl hd hL hj2 hC hCt hV hW hVc hWc ht hb]

/-- **Covariance of `𝒲_{j+1}`** at scale `j + 1`. -/
theorem Wnext2_cov (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N)
    (hC : GoodCov2 j ℓ C) (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hVc : FamCovG j V)
    (hWc : FamCovG j W) : FamCovG (j + 1) (Wnext2 j C V W) := by
  intro t ht c hc
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hP1 := Flow.presBlocks_transl' (by omega) t ht
  have hWp : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c),
      Wp j C V W (bmap j (AffAut.transl t) b) = AE (AffAut.transl t) (Wp j C V W b) :=
    fun b hb => Subtype.ext (by
      rw [coe_AE]; exact Wp_transl hd hL hj2 hC hCt hV hW hVc hWc ht (mem_blockIdx_of_mem_blocks hb))
  have e : Wnext2 j C V W (bmap (j + 1) (AffAut.transl t) c) =
      AE (AffAut.transl t) (Wnext2 j C V W c) := by
    rw [Wnext2, Wnext2, ← img_blockSet_bmap (IsGen.transl t) (by omega) hP1 hc,
      blocks_img_bmap hP, map_sub, map_prod, map_one,
      prod_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) (by omega) hP
        (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
    congr 1
    refine prod_congr rfl fun b hb => ?_
    rw [map_add, map_one, hWp b hb]
  rw [e, coe_AE]; rfl

theorem Q2_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hK : InK2 j K)
    (hKc : KCov j K) (ht : ∀ i, L ^ j ∣ (co t i).val) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Q2 j K (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (Q2 j K b) := by
  classical
  set T := AffAut.transl (d := d) (L := L) (N := N) t
  have hT : IsGen T := IsGen.transl t
  have hj : j ≤ N := by omega
  have hP := Flow.presBlocks_transl' hj t ht
  have hB := img_blockSet_bmap hT hj hP hb
  obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
  have hS : ((smallSets j).filter fun Y => blockSet j (bmap j T b) ⊆ Y) =
      ((smallSets j).filter fun Y => blockSet (L := L) (N := N) j b ⊆ Y).image T.img := by
    ext Y
    simp only [mem_filter, mem_image, mem_smallSets]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨T'.img Y, ⟨(hP'.isSmall_img hT' hj).2 h1, ?_⟩, e' Y⟩
      have := img_mono T' h2
      rwa [← hB, e] at this
    · rintro ⟨Y', ⟨h1, h2⟩, rfl⟩
      exact ⟨(hP.isSmall_img hT hj).2 h1, by rw [← hB]; exact img_mono T h2⟩
  rw [Q2, Q2, if_pos hjN, if_pos hjN, hS, sum_image fun Y _ Y' _ e => img_injective T e,
    AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum, map_sum]
  refine sum_congr rfl fun X hX => ?_
  have hs := mem_smallSets.1 (mem_filter.1 hX).1
  have hR := region_small hd hL hjN hs
  have hKX : (K X : Alg d L N) ∈ NX (nbhd j X : Set (Lam d L N)) := hK.loc X ⟨hs.1, hs.2.1⟩
  rw [coe_Loc2E, coe_Loc2E, hKc t ht X, ← hB]
  exact (Loc2XY_transl hR hs.2.1.1 t _ hKX).symm

theorem uVp_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hK : InK2 j K) (hVc : FamCovG j V)
    (hWc : FamCovG j W) (hKc : KCov j K) (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (uVp j C V W K (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (uVp j C V W K b) := by
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have h1 : ∀ x y, C ((Equiv.addRight t) x) ((Equiv.addRight t) y) = C x y :=
    fun x y => hCt t x y
  rw [uVp, uVp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub,
    AddSubgroupClass.coe_sub, map_sub, map_sub, Vpr_transl hCt hVc ht' hb, coe_EthE, coe_EthE,
    Q2_transl hd hL (by omega) hK hKc ht' hb, expLC_autAlg _ h1,
    LS_transl hd hL hj2 hC hCt hV hW hVc hWc ht hb]

theorem Vp_transl (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hK : InK2 j K) (hVc : FamCovG j V)
    (hWc : FamCovG j W) (hKc : KCov j K) (ht : ∀ i, L ^ (j + 1) ∣ (co t i).val)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Vp j C V W K (bmap j (AffAut.transl t) b) : Alg d L N) =
      autAlg (Equiv.addRight t) (Vp j C V W K b) := by
  have e := uVp_transl hd hL hj2 hC hCt hV hW hK hVc hWc hKc ht hb
  have hu : up j C V W K (bmap j (AffAut.transl t) b) = up j C V W K b := by
    rw [up, up, e, ε_autAlg]
  rw [Vp, Vp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, e, hu, map_sub,
    Subalgebra.coe_algebraMap, AlgHom.commutes]

/-- **Covariance of `V_{j+1}`** at scale `j + 1`. -/
theorem Vnext2_cov (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N)
    (hC : GoodCov2 j ℓ C) (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hK : InK2 j K)
    (hVc : FamCovG j V) (hWc : FamCovG j W) (hKc : KCov j K) :
    FamCovG (j + 1) (Vnext2 j C V W K) := by
  intro t ht c hc
  have ht' : ∀ i, L ^ j ∣ (co t i).val := fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (ht i)
  have hP := Flow.presBlocks_transl' (by omega) t ht'
  have hP1 := Flow.presBlocks_transl' (by omega) t ht
  rw [Vnext2, Vnext2, ← img_blockSet_bmap (IsGen.transl t) (by omega) hP1 hc, blocks_img_bmap hP,
    sum_image fun b hb b' hb' e => bmap_injOn (IsGen.transl t) (by omega) hP
      (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e,
    AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum, map_sum]
  exact sum_congr rfl fun b hb =>
    Vp_transl hd hL hj2 hC hCt hV hW hK hVc hWc hKc ht (mem_blockIdx_of_mem_blocks hb)

end Transl

end

end Step2
