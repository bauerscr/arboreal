import Step2.Last.LastKCov

/-!
# The step at `j = N - 2`: lattice-symmetry covariance

A copy of `SymHyp` and its consequences from `Step2.Map.SymCov` with `j + 2 < N` replaced by
`j + 1 < N` and `L > 2^{d+4} + 4` (namespace `Step2.Last`). The localisation over the closure of
a `j`-block is covariant by `region_small_L` (`Step2.Last.LastGeo`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix PolyAux

variable {d L N : ℕ} [NeZero L]

namespace Last

/-- The hypotheses for the covariance of the step under `T`. -/
structure SymHyp (j : ℕ) (ℓ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (K : Act d L N) (T : AffAut d L N) : Prop where
  hd : 1 ≤ d
  hL : 2 ^ (d + 3) ≤ L
  hj2 : j + 1 < N
  hLg : 2 ^ (d + 4) + 4 < L
  hC : GoodCov2 j ℓ C
  hCs : CSym C
  hV : InF j V
  hW : InF j W
  hV0 : ∀ b, ε (V b : Alg d L N) = 0
  hK : InK2 j K
  hVs : FamSym j V
  hWs : FamSym j W
  hKs : KSym j K
  hT : IsGen T
  hP1 : PresBlocks (j + 1) T

namespace SymHyp

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {T : AffAut d L N} (H : SymHyp j ℓ C V W K T)
include H

theorem hj : j ≤ N := by have := H.hj2; omega

theorem hP : PresBlocks j T := H.hP1.of_succ H.hT (by have := H.hj2; omega)

theorem hCE : ∀ x y, C (T.E x) (T.E y) = C x y := H.hCs T H.hT

theorem hCE' : ∀ x y, (-C) (T.E x) (T.E y) = (-C) x y :=
  fun x y => by simp only [Matrix.neg_apply, H.hCE x y]

theorem AE_EthE (F : EvR (Lam d L N)) : AE T (EthE C F) = EthE C (AE T F) :=
  Subtype.ext (by rw [coe_AE, coe_EthE, coe_EthE, coe_AE, expLC_autAlg _ H.hCE])

theorem AE_FCE (A B : EvR (Lam d L N)) : AE T (FCE C A B) = FCE C (AE T A) (AE T B) :=
  Subtype.ext (by
    rw [coe_AE, coe_FCE, coe_FCE, coe_AE, coe_AE]
    simp only [FC, map_sub, map_mul, ← expLC_autAlg _ H.hCE, ← expLC_autAlg _ H.hCE'])

theorem AE_Vpr {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Vpr C V b) = Vpr C V (bmap j T b) := by
  rw [Vpr, Vpr, H.AE_EthE, H.hVs T H.hT H.hP b hb]

theorem bmap_image : (blockIdx (d := d) (L := L) (N := N) j).image (bmap j T) =
    blockIdx (d := d) (L := L) (N := N) j := by
  refine eq_of_subset_of_card_le (fun b hb => ?_) ?_
  · obtain ⟨b', hb', rfl⟩ := mem_image.1 hb
    exact bmap_mem_blockIdx H.hT H.hj H.hP hb'
  · rw [card_image_of_injOn (bmap_injOn H.hT H.hj H.hP)]

theorem AE_VprL : AE T (VprL j C V) = VprL j C V := by
  rw [VprL, map_sum]
  conv_rhs => rw [← H.bmap_image]
  rw [sum_image fun b hb b' hb' e => bmap_injOn H.hT H.hj H.hP hb hb' e]
  exact sum_congr rfl fun b hb => H.AE_Vpr hb

theorem AE_Sb {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Sb j C V W b) = Sb j C V W (bmap j T b) := by
  rw [Sb, Sb, map_add, map_smul, H.AE_FCE, H.AE_Vpr hb, H.AE_VprL, H.AE_EthE,
    H.hWs T H.hT H.hP b hb]

theorem AE_SX (X : Finset (Lam d L N)) : AE T (SX j C V W X) = SX j C V W (T.img X) := by
  rw [SX, SX, blocks_img_bmap H.hP, map_sum,
    sum_image fun b hb b' hb' e => bmap_injOn H.hT H.hj H.hP
      (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
  exact sum_congr rfl fun b hb => H.AE_Sb (mem_blockIdx_of_mem_blocks hb)

theorem img_Bp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    T.img (Bp (L := L) (N := N) j b) = Bp j (bmap j T b) := by
  obtain ⟨x, -, rfl⟩ := mem_image.1 hb
  have hb1 : blk (j + 1) x ∈ blockIdx (L := L) (N := N) (j + 1) := mem_image_of_mem _ (mem_univ _)
  rw [Bp, Bp, clo_blockSet hb, clo_blockSet (bmap_mem_blockIdx H.hT H.hj H.hP hb),
    ← blk_succ, img_blockSet_bmap H.hT (by have := H.hj2; omega) H.hP1 hb1, bmap_blk H.hP1,
    bmap_blk H.hP, blk_succ]

theorem AE_Loc2E {X : Finset (Lam d L N)} {k : ℕ} (hk : k < N) (hX : IsSmall k X)
    (Y : Finset (Lam d L N)) {F : EvR (Lam d L N)}
    (hF : (F : Alg d L N) ∈ NX (nbhd k X : Set (Lam d L N))) :
    AE T (Loc2E X Y F) = Loc2E (T.img X) (T.img Y) (AE T F) :=
  Subtype.ext (by
    rw [coe_AE, coe_Loc2E, coe_Loc2E, coe_AE]
    exact Loc2sXY_aut H.hT (region_small_L H.hd H.hLg hk hX) hX.2.1.1 Y hF)

theorem AE_LS {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (LS j C V W b) = LS j C V W (bmap j T b) := by
  have hsm : IsSmall (j + 1) (Bp (L := L) (N := N) j b) :=
    isSmall_clo (isSmall_blockSet_of_mem hb)
  have hF := SX_mem' H.hd H.hL (by have := H.hj2; omega) H.hC H.hV H.hW b
  rw [LS, LS, H.AE_Loc2E (by have := H.hj2; omega) hsm _ hF, H.img_Bp hb,
    img_blockSet_bmap H.hT H.hj H.hP hb, H.AE_SX, H.img_Bp hb]

theorem AE_Wp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Wp j C V W b) = Wp j C V W (bmap j T b) := by
  rw [Wp, Wp, map_sub, H.AE_Sb hb, H.AE_LS hb]

theorem AE_Loc2E_K {Y : Finset (Lam d L N)} (hY : IsSmall j Y) (B : Finset (Lam d L N)) :
    AE T (Loc2E Y B (K Y)) = Loc2E (T.img Y) (T.img B) (K (T.img Y)) := by
  rw [H.AE_Loc2E (by have := H.hj2; omega) hY B (H.hK.loc Y ⟨hY.1, hY.2.1⟩),
    H.hKs T H.hT H.hP Y]

theorem AE_Q2 {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Q2 j K b) = Q2 j K (bmap j T b) := by
  classical
  have hjN : j + 1 < N := by have := H.hj2; omega
  have hB := img_blockSet_bmap H.hT H.hj H.hP hb
  obtain ⟨T', hT', hP', e, e'⟩ := H.hP.exists_inv H.hT H.hj
  have hS : ((smallSets j).filter fun Y => blockSet j (bmap j T b) ⊆ Y) =
      ((smallSets j).filter fun Y => blockSet (L := L) (N := N) j b ⊆ Y).image T.img := by
    ext Y
    simp only [mem_filter, mem_image, mem_smallSets]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨T'.img Y, ⟨(hP'.isSmall_img hT' H.hj).2 h1, ?_⟩, e' Y⟩
      have := img_mono T' h2
      rwa [← hB, e] at this
    · rintro ⟨Y', ⟨h1, h2⟩, rfl⟩
      exact ⟨(H.hP.isSmall_img H.hT H.hj).2 h1, by rw [← hB]; exact img_mono T h2⟩
  rw [Q2, Q2, if_pos hjN, if_pos hjN, hS, sum_image fun Y _ Y' _ e => img_injective T e, map_sum]
  refine sum_congr rfl fun X hX => ?_
  rw [H.AE_Loc2E_K (mem_smallSets.1 (mem_filter.1 hX).1), hB]

theorem AE_uVp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (uVp j C V W K b) = uVp j C V W K (bmap j T b) := by
  rw [uVp, uVp, map_sub, map_sub, H.AE_Vpr hb, H.AE_EthE, H.AE_Q2 hb, H.AE_LS hb]

theorem up_sym {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    up j C V W K (bmap j T b) = up j C V W K b := by
  rw [up, up, ← H.AE_uVp hb, coe_AE, ε_autAlg]

theorem AE_Vp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Vp j C V W K b) = Vp j C V W K (bmap j T b) := by
  rw [Vp, Vp, map_sub, H.AE_uVp hb, H.up_sym hb, AlgHom.commutes]

/-! ### The coordinates at scale `j + 1` -/

theorem AE_Wnext2 {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1)) :
    AE T (Wnext2 j C V W c) = Wnext2 j C V W (bmap (j + 1) T c) := by
  rw [Wnext2, Wnext2, ← img_blockSet_bmap H.hT (by have := H.hj2; omega) H.hP1 hc,
    blocks_img_bmap H.hP, map_sub, map_prod, map_one,
    prod_image fun b hb b' hb' e => bmap_injOn H.hT H.hj H.hP
      (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
  congr 1
  refine prod_congr rfl fun b hb => ?_
  rw [map_add, map_one, H.AE_Wp (mem_blockIdx_of_mem_blocks hb)]

theorem AE_Vnext2 {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1)) :
    AE T (Vnext2 j C V W K c) = Vnext2 j C V W K (bmap (j + 1) T c) := by
  rw [Vnext2, Vnext2, ← img_blockSet_bmap H.hT (by have := H.hj2; omega) H.hP1 hc,
    blocks_img_bmap H.hP, map_sum,
    sum_image fun b hb b' hb' e => bmap_injOn H.hT H.hj H.hP
      (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
  exact sum_congr rfl fun b hb => H.AE_Vp (mem_blockIdx_of_mem_blocks hb)

/-! ### The polymer activity -/

theorem AE_Ib {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Ib V W b) = Ib V W (bmap j T b) := by
  have hn : IsNilpotent (-V b) := (isNilpotent_of_ε' (H.hV0 b)).neg
  rw [Ib, Ib, map_mul, AE_gexp _ hn, map_neg, map_add, map_one, H.hVs T H.hT H.hP b hb,
    H.hWs T H.hT H.hP b hb]

theorem AE_Gp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Gp j C V W K b) = Gp j C V W K (bmap j T b) := by
  have hn : IsNilpotent (-Vp j C V W K b) := (isNilpotent_of_ε' (ε_Vp j C V W K b)).neg
  rw [Gp, Gp, map_mul, AE_gexp _ hn, map_neg, map_add, map_one, H.AE_Vp hb, H.AE_Wp hb]

theorem AE_Ip {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Ip j C V W K b) = Ip j C V W K (bmap j T b) := by
  have hn : IsNilpotent (-Vp j C V W K b) := (isNilpotent_of_ε' (ε_Vp j C V W K b)).neg
  rw [Ip, Ip, map_smul, map_mul, AE_gexp _ hn, map_neg, map_add, map_one, H.AE_Vp hb,
    H.AE_Wp hb, H.up_sym hb]

theorem AE_J2 {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) (X : Finset (Lam d L N)) :
    AE T (J2 j K b X) = J2 j K (bmap j T b) (T.img X) := by
  classical
  have hT := H.hT
  have hj := H.hj
  have hP := H.hP
  have hB := img_blockSet_bmap hT hj hP hb
  have c1 : (j + 1 < N ∧ IsSmall j (T.img X) ∧ blockSet j (bmap j T b) ⊆ T.img X) ↔
      (j + 1 < N ∧ IsSmall j X ∧ blockSet j b ⊆ X) := by
    rw [← hB, hP.isSmall_img hT hj, AffAut.img, AffAut.img, Finset.map_subset_map]
  have c2 : T.img X = blockSet j (bmap j T b) ↔ X = blockSet j b := by
    rw [← hB]; exact (img_injective T).eq_iff
  unfold J2
  by_cases hc : j + 1 < N ∧ IsSmall j X ∧ blockSet j b ⊆ X
  · rw [if_pos hc, if_pos (c1.2 hc)]
    by_cases hx : X = blockSet j b
    · rw [if_pos hx, if_pos (c2.2 hx), map_neg, map_sum]
      congr 1
      obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
      have hS : ((smallSets j).filter fun Y => blockSet j (bmap j T b) ⊆ Y ∧
          Y ≠ blockSet j (bmap j T b)) =
          ((smallSets j).filter fun Y => blockSet j b ⊆ Y ∧ Y ≠ blockSet j b).image T.img := by
        ext Y
        simp only [mem_filter, mem_image, mem_smallSets]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨T'.img Y, ⟨(hP'.isSmall_img hT' hj).2 h1, ?_, ?_⟩, e' Y⟩
          · have := img_mono T' h2
            rwa [← hB, e] at this
          · intro h4
            apply h3
            rw [← e' Y, h4, hB]
        · rintro ⟨Y', ⟨h1, h2, h3⟩, rfl⟩
          refine ⟨(hP.isSmall_img hT hj).2 h1, ?_, ?_⟩
          · rw [← hB]; exact img_mono T h2
          · rw [← hB]; exact fun h4 => h3 (img_injective T h4)
      rw [hS, sum_image fun Y _ Y' _ e => img_injective T e]
      refine sum_congr rfl fun Y hY => ?_
      rw [H.AE_Loc2E_K (mem_smallSets.1 (mem_filter.1 hY).1), hB]
    · rw [if_neg hx, if_neg (mt c2.1 hx), H.AE_Loc2E_K hc.2.1, hB]
  · rw [if_neg hc, if_neg (mt c1.1 hc), map_zero]

theorem uX_sym (X : Finset (Lam d L N)) : uX j C V W K (T.img X) = uX j C V W K X := by
  rw [uX, uX, blocks_img_bmap H.hP,
    sum_image fun b hb b' hb' => bmap_injOn H.hT H.hj H.hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  exact sum_congr rfl fun b hb => H.up_sym (blocks_subset_blockIdx X hb)

theorem AE_Knext2 (U : Finset (Lam d L N)) :
    AE T (Knext2 j C V W K U) = Knext2 j C V W K (T.img U) := by
  rw [Knext2, Knext2, map_smul, H.uX_sym,
    AE_gKnext (Ib := Ib V W) (Ip := Ip j C V W K) (K := K) (J := J2 j K) H.hT
      (by have := H.hj2; omega) H.hP H.hCE (fun b hb => H.AE_Ib hb) (fun b hb => H.AE_Ip hb)
      (fun Y _ => H.hKs T H.hT H.hP Y) (fun b hb X => H.AE_J2 hb X) H.hP1]

theorem AE_k2 (X : Finset (Lam d L N)) : AE T (k2 j C V X) = k2 j C V (T.img X) := by
  have hinj : Set.InjOn (bmap j T) (blocks j X : Set (Fin d → ℕ)) :=
    fun b hb b' hb' e => bmap_injOn H.hT H.hj H.hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb') e
  have hnb := H.hP.nb_img H.hT H.hj X
  unfold k2
  rw [hnb]
  split_ifs
  · rw [map_sum, blocks_img_bmap H.hP, sum_image hinj]
    refine sum_congr rfl fun b hb => ?_
    have hb' := blocks_subset_blockIdx X hb
    rw [map_smul, H.AE_FCE, map_sub, H.AE_Vpr hb', H.AE_VprL]
  · rw [map_smul, map_sum, blocks_img_bmap H.hP, sum_image hinj]
    congr 1
    refine sum_congr rfl fun b hb => ?_
    have hb' := blocks_subset_blockIdx X hb
    rw [map_sum, CovHyp.image_erase_of_injOn hinj hb, sum_image fun x hx y hy e =>
      hinj (mem_of_mem_erase hx) (mem_of_mem_erase hy) e]
    refine sum_congr rfl fun b' hb'' => ?_
    rw [H.AE_FCE, H.AE_Vpr hb', H.AE_Vpr (blocks_subset_blockIdx X (mem_of_mem_erase hb''))]
  · rw [map_zero]

theorem sum_clo_sym {M : Type*} [AddCommMonoid M] (U : Finset (Lam d L N))
    (f : Finset (Lam d L N) → M) :
    (open Classical in
      ∑ X ∈ (Pj j univ).filter (fun X => clo j X = T.img U), f X) =
      (open Classical in ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U), f (T.img X)) := by
  classical
  have hPj : Pj j (univ : Finset (Lam d L N)) = (Pj j univ).image T.img := by
    have := Pj_img H.hT H.hj H.hP (univ : Finset (Lam d L N))
    rwa [img_univ] at this
  have hfil : ∀ X : Finset (Lam d L N), (clo j (T.img X) = T.img U) ↔ clo j X = U := fun X => by
    rw [H.hP1.clo_img H.hT (by have := H.hj2; omega)]
    exact (img_injective _).eq_iff
  conv_lhs => rw [hPj, filter_image]
  rw [sum_image fun X _ Y _ e => img_injective _ e]
  refine sum_congr ?_ fun _ _ => rfl
  ext X
  simp only [mem_filter, hfil]

theorem AE_K2 (U : Finset (Lam d L N)) : AE T (K2 j C V U) = K2 j C V (T.img U) := by
  classical
  rw [K2, K2, map_sum, H.sum_clo_sym]
  exact sum_congr rfl fun X _ => H.AE_k2 X

theorem AE_Knew (U : Finset (Lam d L N)) :
    AE T (Knew j C V W K U) = Knew j C V W K (T.img U) := by
  rw [Knew, Knew, map_sub, map_mul, H.AE_Knext2,
    AE_bpow (I := Gp j C V W K) H.hT H.hj H.hP (fun b hb => H.AE_Gp hb), H.AE_K2]

theorem par_bmap {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    par L (bmap j T b) = bmap (j + 1) T (par L b) := by
  obtain ⟨x, -, rfl⟩ := mem_image.1 hb
  rw [← blk_succ, bmap_blk H.hP1, bmap_blk H.hP, blk_succ]

theorem AE_It {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1)) :
    AE T (It j C V W K c) = It j C V W K (bmap (j + 1) T c) := by
  rw [It, It, AE_bpow (I := Gp j C V W K) H.hT H.hj H.hP (fun b hb => H.AE_Gp hb),
    img_blockSet_bmap H.hT (by have := H.hj2; omega) H.hP1 hc]

theorem AE_kap {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1))
    (X : Finset (Lam d L N)) : AE T (kap j C V X c) = kap j C V (T.img X) (bmap (j + 1) T c) := by
  have hinj : Set.InjOn (bmap j T) (blocks j X : Set (Fin d → ℕ)) :=
    fun b hb b' hb' e => bmap_injOn H.hT H.hj H.hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb') e
  have hfil : ((blocks j (T.img X)).filter fun b => par L b = bmap (j + 1) T c) =
      ((blocks j X).filter fun b => par L b = c).image (bmap j T) := by
    rw [blocks_img_bmap H.hP, filter_image]
    congr 1
    ext b
    simp only [mem_filter]
    constructor
    · rintro ⟨hb, h⟩
      refine ⟨hb, bmap_injOn H.hT (by have := H.hj2; omega) H.hP1
        (CovHyp.par_mem (blocks_subset_blockIdx X hb)) hc ?_⟩
      rw [← H.par_bmap (blocks_subset_blockIdx X hb)]; exact h
    · rintro ⟨hb, rfl⟩
      exact ⟨hb, H.par_bmap (blocks_subset_blockIdx X hb)⟩
  have hinj' : Set.InjOn (bmap j T)
      (((blocks j X).filter fun b => par L b = c : Finset _) : Set (Fin d → ℕ)) :=
    fun b hb b' hb' e => hinj (mem_filter.1 hb).1 (mem_filter.1 hb').1 e
  have hnb := H.hP.nb_img H.hT H.hj X
  unfold kap
  rw [hnb]
  split_ifs
  · rw [map_sum, hfil, sum_image hinj']
    refine sum_congr rfl fun b hb => ?_
    have hb' := blocks_subset_blockIdx X (mem_filter.1 hb).1
    rw [map_smul, H.AE_FCE, map_sub, H.AE_Vpr hb', H.AE_VprL]
  · rw [map_smul, map_sum, hfil, sum_image hinj']
    congr 1
    refine sum_congr rfl fun b hb => ?_
    have hbX := (mem_filter.1 hb).1
    have hb' := blocks_subset_blockIdx X hbX
    rw [map_sum, blocks_img_bmap H.hP, CovHyp.image_erase_of_injOn hinj hbX,
      sum_image fun x hx y hy e => hinj (mem_of_mem_erase hx) (mem_of_mem_erase hy) e]
    refine sum_congr rfl fun b' hb'' => ?_
    rw [H.AE_FCE, H.AE_Vpr hb', H.AE_Vpr (blocks_subset_blockIdx X (mem_of_mem_erase hb''))]
  · rw [map_zero]

theorem AE_Jh {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1))
    (U : Finset (Lam d L N)) : AE T (Jh j C V c U) = Jh j C V (bmap (j + 1) T c) (T.img U) := by
  classical
  have hs : IsSmall (j + 1) (T.img U) ↔ IsSmall (j + 1) U :=
    H.hP1.isSmall_img H.hT (by have := H.hj2; omega)
  unfold Jh
  by_cases hU : IsSmall (j + 1) U
  · rw [if_pos hU, if_pos (hs.2 hU), map_sum, H.sum_clo_sym]
    exact sum_congr rfl fun X _ => H.AE_kap hc X
  · rw [if_neg hU, if_neg (mt hs.1 hU), map_zero]

theorem AE_Kplus (U : Finset (Lam d L N)) :
    AE T (Kplus j C V W K U) = Kplus j C V W K (T.img U) :=
  AE_Kout (I := It j C V W K) (M := Knew j C V W K) (J := Jh j C V) H.hT
    (by have := H.hj2; omega) H.hP1 (fun c hc => H.AE_It hc) (fun Y _ => H.AE_Knew Y)
    (fun c hc X => H.AE_Jh hc X) U

end SymHyp

/-! ### Proposition `prop:C1` -/

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N}

/-- **Proposition `prop:C1`** for `𝒲_{j+1}`. -/
theorem Wnext2_latsym (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L) (hC : GoodCov2 j ℓ C)
    (hCs : CSym C) (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0)
    (hK : InK2 j K) (hVs : FamSym j V) (hWs : FamSym j W) (hKs : KSym j K) :
    FamSym (j + 1) (Wnext2 j C V W) := fun T hT hP1 c hc =>
  (SymHyp.mk (K := K) hd hL hj2 hLg hC hCs hV hW hV0 hK hVs hWs hKs hT hP1).AE_Wnext2 hc

/-- **Proposition `prop:C1`** for `V_{j+1}`. -/
theorem Vnext2_latsym (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L) (hC : GoodCov2 j ℓ C)
    (hCs : CSym C) (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0)
    (hK : InK2 j K) (hVs : FamSym j V) (hWs : FamSym j W) (hKs : KSym j K) :
    FamSym (j + 1) (Vnext2 j C V W K) := fun T hT hP1 c hc =>
  (SymHyp.mk hd hL hj2 hLg hC hCs hV hW hV0 hK hVs hWs hKs hT hP1).AE_Vnext2 hc

/-- **Proposition `prop:C1`** for `K_{j+1}`. -/
theorem Kplus_latsym (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 1 < N) (hLg : 2 ^ (d + 4) + 4 < L) (hC : GoodCov2 j ℓ C)
    (hCs : CSym C) (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0)
    (hK : InK2 j K) (hVs : FamSym j V) (hWs : FamSym j W) (hKs : KSym j K) :
    KSym (j + 1) (Kplus j C V W K) := fun T hT hP1 X =>
  (SymHyp.mk hd hL hj2 hLg hC hCs hV hW hV0 hK hVs hWs hKs hT hP1).AE_Kplus X

end Last

end

end Step2
