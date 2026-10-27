import Step2.Map.WCov

/-!
# Translation covariance of `K_{j+1}` (`h02uv-outline.tex`, Proposition `prop:W-contract`)

* A generic covariance theorem for the polymer formula `gKnext` (`AE_gKnext`): if the block
  factors, `K` and `J` are covariant under a lattice map `T` preserving `j`- and `(j+1)`-blocks
  and `C` is `T`-invariant, then `T K_{j+1}(U) = K_{j+1}(T U)`. This is the argument of
  `Step.AE_Knext`, for complex covariances and general block factors.
* The same for the change of variables `K_out` (`AE_Kout`).
* For the map of `Step2` and translations `t ∈ L^{j+1} ℤ^d`: `Kplus_cov`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix PolyAux

variable {d L N : ℕ} [NeZero L]

/-! ### `𝔼_C` and lattice maps -/

theorem ECC_autAlg2 (E : Lam d L N ≃ Lam d L N) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : ∀ x y, C (E x) (E y) = C x y) (F : Alg2 d L N) :
    ECC C (autAlg2 E F) = autAlg E (ECC C F) := by
  refine ECC_comm_of _ _ (fun G => ?_) (fun G => ?_) F
  · have hD : ∀ (b : Lam d L N ⊕ Lam d L N) (σ : ℤˣ) (H : Alg2 d L N),
        D (b, σ) (autAlg2 E H) = autAlg2 E (D (Sum.map E.symm E.symm b, σ) H) := by
      intro b σ H
      rw [autAlg2, D_map]; rfl
    simp only [LζC_apply, hD, map_sum, map_smul, Sum.map_inr]
    rw [← Equiv.sum_comp E]
    refine sum_congr rfl fun x _ => ?_
    rw [← Equiv.sum_comp E]
    refine sum_congr rfl fun y _ => ?_
    simp [hC]
  · simp only [proj, autAlg2, autAlg, map_map_apply]
    exact map_congr_apply (fun v b => rfl) G

theorem AE_ECCE (T : AffAut d L N) {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : ∀ x y, C (T.E x) (T.E y) = C x y) (F : EvR (Lam d L N ⊕ Lam d L N)) :
    AE T (ECCE C F) = ECCE C (AE2 T F) :=
  Subtype.ext (by simp only [coe_AE, coe_ECCE, coe_AE2]; exact (ECC_autAlg2 T.E hC F).symm)

/-! ### The generic polymer formula -/

section Generic

variable {T : AffAut d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)} {K : Act d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)}

theorem AE_bpow (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T)
    {I : (Fin d → ℕ) → EvR (Lam d L N)}
    (hI : ∀ b ∈ blockIdx (L := L) (N := N) j, AE T (I b) = I (bmap j T b))
    (X : Finset (Lam d L N)) : AE T (bpow j I X) = bpow j I (T.img X) := by
  rw [bpow, bpow, map_prod, blocks_img_bmap hP,
    prod_image fun b hb b' hb' => bmap_injOn hT hj hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  exact prod_congr rfl fun b hb => hI b (blocks_subset_blockIdx X hb)

theorem AE_Kext' (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) {M : Act d L N}
    (hM : ∀ Y, IsConn j Y → AE T (M Y) = M (T.img Y)) {W : Finset (Lam d L N)}
    (hW : IsPolymer j W) : AE T (Kext j M W) = Kext j M (T.img W) := by
  rw [Kext, Kext, map_prod, hP.comp_img hT hj, prod_image fun Y _ Y' _ e => img_injective T e]
  exact prod_congr rfl fun Y hY => hM Y (isConn_of_mem_comp hW hY)

variable (hT : IsGen T) (hj : j + 1 < N) (hP : PresBlocks j T)
  (hC : ∀ x y, C (T.E x) (T.E y) = C x y)
  (hIb : ∀ b ∈ blockIdx (L := L) (N := N) j, AE T (Ib b) = Ib (bmap j T b))
  (hIp : ∀ b ∈ blockIdx (L := L) (N := N) j, AE T (Ip b) = Ip (bmap j T b))
  (hK : ∀ Y, IsConn j Y → AE T (K Y) = K (T.img Y))
  (hJ : ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X, AE T (J b X) = J (bmap j T b) (T.img X))
include hT hj hP

include hIb hIp in
theorem AE2_gdIPow (X : Finset (Lam d L N)) :
    AE2 T (gdIPow j Ib Ip X) = gdIPow j Ib Ip (T.img X) := by
  rw [gdIPow, gdIPow, map_prod, blocks_img_bmap hP,
    prod_image fun b hb b' hb' => bmap_injOn hT (by omega) hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  refine prod_congr rfl fun b hb => ?_
  have hb' := blocks_subset_blockIdx X hb
  rw [gdI, gdI, map_sub, AE2_thetaE, AE2_inclE, hIb b hb', hIp b hb']

include hIb hIp hK in
theorem AE2_gKtil {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    AE2 T (gKtil j Ib Ip K W) = gKtil j Ib Ip K (T.img W) := by
  rw [gKtil, gKtil, map_sum, Pj_img hT (by omega) hP, sum_image fun Y _ Y' _ e => img_injective T e]
  refine sum_congr rfl fun Y hY => ?_
  rw [map_mul, AE2_thetaE, AE_Kext' hT (by omega) hP hK (IsPolymer.sdiff hW (mem_Pj.1 hY).2),
    AE2_gdIPow hT hj hP hIb hIp, img_sdiff]

include hIb hIp hK hJ in
theorem AE2_gKchkC {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    AE2 T (gKchkC j Ib Ip K J W) = gKchkC j Ib Ip K J (T.img W) := by
  rw [gKchkC, gKchkC, map_sub, AE2_gKtil hT hj hP hIb hIp hK hW, map_sum, blocks_img_bmap hP,
    sum_image fun b hb b' hb' => bmap_injOn hT (by omega) hP (blocks_subset_blockIdx W hb)
      (blocks_subset_blockIdx W hb')]
  congr 1
  refine sum_congr rfl fun b hb => ?_
  rw [AE2_thetaE, hJ b (blocks_subset_blockIdx W hb)]

include hIb hIp hK hJ in
theorem AE2_gKchk {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    AE2 T (gKchk j Ib Ip K J X) = gKchk j Ib Ip K J (T.img X) := by
  rw [gKchk, gKchk, map_prod, hP.comp_img hT (by omega),
    prod_image fun Y _ Y' _ e => img_injective T e]
  exact prod_congr rfl fun W hW =>
    AE2_gKchkC hT hj hP hIb hIp hK hJ (isPolymer_of_mem_comp hX hW)

include hC hIb hIp hK hJ in
theorem AE_gKterm {U : Finset (Lam d L N)} {g : GT d L N} (hg : g ∈ Gset j U) :
    AE T (bpow j Ip (U \ (g.2 ∪ Xcal g.1)) *
        ECCE C (gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2))) =
      bpow j Ip (T.img U \ ((gimg j T g).2 ∪ Xcal (gimg j T g).1)) *
        ECCE C (gKchk j Ib Ip K J (gimg j T g).2 *
          ∏ p ∈ (gimg j T g).1, thetaE (J p.1 p.2)) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := mem_Gset'.1 hg
  have hinj : Set.InjOn (fun p : (Fin d → ℕ) × Finset (Lam d L N) => (bmap j T p.1, T.img p.2))
      (g.1 : Set _) := by
    intro p hp q hq e
    exact h3 p hp q hq (img_injective T (congrArg Prod.snd e))
  rw [map_mul, AE_bpow hT (by omega) hP hIp, AE_ECCE T hC, map_mul,
    AE2_gKchk hT hj hP hIb hIp hK hJ h1, map_prod, img_sdiff, img_union, ← Xcal_gimg]
  simp only [gimg]
  rw [prod_image hinj]
  congr 3
  refine prod_congr rfl fun p hp => ?_
  rw [AE2_thetaE, hJ _ (mem_pairsU.1 (h2 hp)).1]

include hC hIb hIp hK hJ in
/-- **Covariance of the polymer formula.** -/
theorem AE_gKnext (hP1 : PresBlocks (j + 1) T) (U : Finset (Lam d L N)) :
    AE T (gKnext j C Ib Ip K J U) = gKnext j C Ib Ip K J (T.img U) := by
  obtain ⟨T', hT', hP1', e, e'⟩ := hP1.exists_inv hT (by omega : j + 1 ≤ N)
  have hP' := hP1'.of_succ hT' hj
  rw [gKnext, gKnext, map_sum]
  refine sum_nbij' (gimg j T) (gimg j T') (fun g hg => gimg_mem hT (by omega) hP hP1 hg)
    (fun g hg => ?_) (fun g hg => gimg_gimg hP hP' e hg) (fun g hg => gimg_gimg hP' hP e' hg)
    (fun g hg => AE_gKterm hT hj hP hC hIb hIp hK hJ hg)
  have := gimg_mem hT' (by omega) hP' hP1' hg
  rwa [e] at this

end Generic

/-! ### The change of variables `K_out` -/

section Kout

variable {T : AffAut d L N} {k : ℕ}

theorem gimg0_mem (hT : IsGen T) (hk : k ≤ N) (hP : PresBlocks k T) {g : GT d L N}
    (hg : g ∈ G0 k) : gimg k T g ∈ G0 k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (mem_G0 k).1 hg
  refine (mem_G0 k).2 ⟨(hP.isPolymer_img hT hk).2 h1, ?_, ?_, ?_, ?_⟩
  · intro p' hp'
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
    obtain ⟨hb, hs, hbs⟩ := mem_pairsU.1 (h2 hp)
    refine mem_pairsU.2 ⟨bmap_mem_blockIdx hT hk hP hb, (hP.isSmall_img hT hk).2 hs, ?_⟩
    rw [← img_blockSet_bmap hT hk hP hb]
    exact img_mono T hbs
  · intro p' hp' q' hq' e
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hq'
    rw [h3 p hp q hq (img_injective T e)]
  · intro p' hp' q' hq' e
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hq'
    rw [hT.touch_img]
    exact h4 p hp q hq fun e' => e (by simp only [e'])
  · show ¬ Touch (Xcal (gimg k T g).1) (T.img g.2)
    rw [Xcal_gimg, hT.touch_img]; exact h5

theorem gimg_gimg0 {T' : AffAut d L N} (hP : PresBlocks k T) (hP' : PresBlocks k T')
    (e : ∀ X, T'.img (T.img X) = X) {g : GT d L N} (hg : g ∈ G0 k) :
    gimg k T' (gimg k T g) = g := by
  obtain ⟨-, h2, -, -, -⟩ := (mem_G0 k).1 hg
  have e₁ := E_inv_of_img e
  simp only [gimg, image_image, e]
  refine Prod.ext ?_ rfl
  conv_rhs => rw [← image_id (s := g.1)]
  refine image_congr fun p hp => ?_
  simp only [Function.comp_apply, id, e]
  rw [bmap_bmap hP hP' e₁ (mem_pairsU.1 (h2 hp)).1]

theorem gimg0_cond (hT : IsGen T) (hk : k ≤ N) (hP : PresBlocks k T) {g : GT d L N}
    (hg : g ∈ G0 k) :
    (gimg k T g).2 ∪ Bbox k (gimg k T g).1 = T.img (g.2 ∪ Bbox k g.1) := by
  obtain ⟨-, h2, -, -, -⟩ := (mem_G0 k).1 hg
  rw [Bbox_gimg hT hk hP h2, img_union]; rfl

variable {I : (Fin d → ℕ) → EvR (Lam d L N)} {M : Act d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)}

/-- **Covariance of `K_out`.** -/
theorem AE_Kout (hT : IsGen T) (hk : k ≤ N) (hP : PresBlocks k T)
    (hI : ∀ b ∈ blockIdx (L := L) (N := N) k, AE T (I b) = I (bmap k T b))
    (hM : ∀ Y, IsConn k Y → AE T (M Y) = M (T.img Y))
    (hJ : ∀ b ∈ blockIdx (L := L) (N := N) k, ∀ X, AE T (J b X) = J (bmap k T b) (T.img X))
    (W : Finset (Lam d L N)) : AE T (Kout k I M J W) = Kout k I M J (T.img W) := by
  obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hk
  rw [Kout, Kout, map_sum]
  refine sum_nbij' (gimg k T) (gimg k T') (fun g hg => ?_) (fun g hg => ?_)
    (fun g hg => gimg_gimg0 hP hP' e (mem_filter.1 hg).1)
    (fun g hg => gimg_gimg0 hP' hP e' (mem_filter.1 hg).1) (fun g hg => ?_)
  · obtain ⟨h1, h2⟩ := mem_filter.1 hg
    exact mem_filter.2 ⟨gimg0_mem hT hk hP h1, by rw [gimg0_cond hT hk hP h1, h2]⟩
  · obtain ⟨h1, h2⟩ := mem_filter.1 hg
    refine mem_filter.2 ⟨gimg0_mem hT' hk hP' h1, ?_⟩
    rw [gimg0_cond hT' hk hP' h1, h2, e]
  · obtain ⟨hg0, -⟩ := mem_filter.1 hg
    obtain ⟨h1, h2, h3, -, -⟩ := (mem_G0 k).1 hg0
    have hinj : Set.InjOn
        (fun p : (Fin d → ℕ) × Finset (Lam d L N) => (bmap k T p.1, T.img p.2)) (g.1 : Set _) := by
      intro p hp q hq e
      exact h3 p hp q hq (img_injective T (congrArg Prod.snd e))
    rw [Rterm, Rterm, map_mul, AE_bpow hT hk hP hI, map_mul, AE_Kext' hT hk hP hM h1, map_prod,
      img_sdiff, img_union, ← Xcal_gimg]
    simp only [gimg]
    rw [prod_image hinj]
    congr 2
    refine prod_congr rfl fun p hp => ?_
    rw [Jbar, Jbar, map_mul, AE_bpow hT hk hP hI, hJ _ (mem_pairsU.1 (h2 hp)).1]

end Kout


/-! ### The map of `Step2` -/

/-- The hypotheses for the covariance of the step under the translation by `t ∈ L^{j+1} ℤ^d`. -/
structure CovHyp (j : ℕ) (ℓ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)
    (K : Act d L N) (t : Lam d L N) : Prop where
  hd : 1 ≤ d
  hL : 2 ^ (d + 3) ≤ L
  hj2 : j + 2 < N
  hC : GoodCov2 j ℓ C
  hCt : TInv C
  hV : InF j V
  hW : InF j W
  hV0 : ∀ b, ε (V b : Alg d L N) = 0
  hK : InK2 j K
  hVc : FamCovG j V
  hWc : FamCovG j W
  hKc : KCov j K
  ht : ∀ i, L ^ (j + 1) ∣ (co t i).val

namespace CovHyp

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N} {t : Lam d L N} (H : CovHyp j ℓ C V W K t)
include H

theorem ht' : ∀ i, L ^ j ∣ (co t i).val :=
  fun i => (pow_dvd_pow L (Nat.le_succ j)).trans (H.ht i)

theorem hP : PresBlocks j (AffAut.transl t) := Flow.presBlocks_transl' (by have := H.hj2; omega) t H.ht'

theorem hP1 : PresBlocks (j + 1) (AffAut.transl t) :=
  Flow.presBlocks_transl' (by have := H.hj2; omega) t H.ht

theorem hCE : ∀ x y, C ((AffAut.transl t).E x) ((AffAut.transl t).E y) = C x y :=
  fun x y => H.hCt t x y

theorem AE_fam {F : Fam d L N} (hF : FamCovG j F) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE (AffAut.transl t) (F b) = F (bmap j (AffAut.transl t) b) :=
  Subtype.ext (by rw [coe_AE, hF t H.ht' b hb]; rfl)

theorem AE_Ib {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE (AffAut.transl t) (Ib V W b) = Ib V W (bmap j (AffAut.transl t) b) := by
  have hn : IsNilpotent (-V b) := (isNilpotent_of_ε' (H.hV0 b)).neg
  rw [Ib, Ib, map_mul, AE_gexp _ hn, map_neg, map_add, map_one, H.AE_fam H.hVc hb,
    H.AE_fam H.hWc hb]

theorem up_transl {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    up j C V W K (bmap j (AffAut.transl t) b) = up j C V W K b := by
  rw [up, up, uVp_transl H.hd H.hL H.hj2 H.hC H.hCt H.hV H.hW H.hK H.hVc H.hWc H.hKc H.ht hb,
    ε_autAlg]

theorem AE_Vp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE (AffAut.transl t) (Vp j C V W K b) = Vp j C V W K (bmap j (AffAut.transl t) b) :=
  Subtype.ext (by
    rw [coe_AE, Vp_transl H.hd H.hL H.hj2 H.hC H.hCt H.hV H.hW H.hK H.hVc H.hWc H.hKc H.ht hb]
    rfl)

theorem AE_Wp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE (AffAut.transl t) (Wp j C V W b) = Wp j C V W (bmap j (AffAut.transl t) b) :=
  Subtype.ext (by
    rw [coe_AE, Wp_transl H.hd H.hL H.hj2 H.hC H.hCt H.hV H.hW H.hVc H.hWc H.ht hb]
    rfl)

theorem AE_Gp {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE (AffAut.transl t) (Gp j C V W K b) = Gp j C V W K (bmap j (AffAut.transl t) b) := by
  have hn : IsNilpotent (-Vp j C V W K b) := (isNilpotent_of_ε' (ε_Vp j C V W K b)).neg
  rw [Gp, Gp, map_mul, AE_gexp _ hn, map_neg, map_add, map_one, H.AE_Vp hb, H.AE_Wp hb]

theorem AE_Ip {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE (AffAut.transl t) (Ip j C V W K b) = Ip j C V W K (bmap j (AffAut.transl t) b) := by
  have hn : IsNilpotent (-Vp j C V W K b) := (isNilpotent_of_ε' (ε_Vp j C V W K b)).neg
  rw [Ip, Ip, map_smul, map_mul, AE_gexp _ hn, map_neg, map_add, map_one, H.AE_Vp hb,
    H.AE_Wp hb, H.up_transl hb]

theorem AE_K (X : Finset (Lam d L N)) :
    AE (AffAut.transl t) (K X) = K ((AffAut.transl t).img X) :=
  Subtype.ext (by rw [coe_AE, H.hKc t H.ht' X]; rfl)

theorem AE_Loc2E_K {Y : Finset (Lam d L N)} (hY : IsSmall j Y) (B : Finset (Lam d L N)) :
    AE (AffAut.transl t) (Loc2E Y B (K Y)) =
      Loc2E ((AffAut.transl t).img Y) ((AffAut.transl t).img B) (K ((AffAut.transl t).img Y)) :=
  Subtype.ext (by
    rw [coe_AE, coe_Loc2E, coe_Loc2E, ← H.AE_K Y, coe_AE]
    exact Loc2XY_transl (region_small H.hd H.hL (by have := H.hj2; omega) hY) hY.2.1.1 t B
      (H.hK.loc Y ⟨hY.1, hY.2.1⟩))

theorem AE_J2 {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) (X : Finset (Lam d L N)) :
    AE (AffAut.transl t) (J2 j K b X) =
      J2 j K (bmap j (AffAut.transl t) b) ((AffAut.transl t).img X) := by
  classical
  set T := AffAut.transl (d := d) (L := L) (N := N) t
  have hT := (IsGen.transl t)
  have hj : j ≤ N := by have := H.hj2; omega
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

theorem uX_transl (X : Finset (Lam d L N)) :
    uX j C V W K ((AffAut.transl t).img X) = uX j C V W K X := by
  have hj : j ≤ N := by have := H.hj2; omega
  rw [uX, uX, blocks_img_bmap H.hP,
    sum_image fun b hb b' hb' => bmap_injOn (IsGen.transl t) hj H.hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  exact sum_congr rfl fun b hb => H.up_transl (blocks_subset_blockIdx X hb)

/-- **Covariance of `K^{pf}_{j+1}`.** -/
theorem AE_Knext2 (U : Finset (Lam d L N)) :
    AE (AffAut.transl t) (Knext2 j C V W K U) = Knext2 j C V W K ((AffAut.transl t).img U) := by
  rw [Knext2, Knext2, map_smul, H.uX_transl,
    AE_gKnext (Ib := Ib V W) (Ip := Ip j C V W K) (K := K) (J := J2 j K) (IsGen.transl t)
      (by have := H.hj2; omega) H.hP H.hCE (fun b hb => H.AE_Ib hb)
      (fun b hb => H.AE_Ip hb) (fun Y _ => H.AE_K Y) (fun b hb X => H.AE_J2 hb X) H.hP1]

theorem AE_Vpr {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE (AffAut.transl t) (Vpr C V b) = Vpr C V (bmap j (AffAut.transl t) b) :=
  Subtype.ext (by rw [coe_AE, Vpr_transl H.hCt H.hVc H.ht' hb]; rfl)

theorem AE_VprL : AE (AffAut.transl t) (VprL j C V) = VprL j C V :=
  Subtype.ext (by rw [coe_AE]; exact VprL_transl (by have := H.hj2; omega) H.hCt H.hVc H.ht')

theorem AE_FCE (A B : EvR (Lam d L N)) :
    AE (AffAut.transl t) (FCE C A B) = FCE C (AE (AffAut.transl t) A) (AE (AffAut.transl t) B) :=
  Subtype.ext (by rw [coe_AE, coe_FCE, coe_FCE, coe_AE, coe_AE]; exact FC_autAlg H.hCt _ _)

omit H in
theorem image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s : Finset α} (hf : Set.InjOn f s) {a : α} (ha : a ∈ s) :
    (s.image f).erase (f a) = (s.erase a).image f := by
  ext y
  simp only [mem_erase, mem_image]
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨fun h => hy (by rw [h]), hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxa, hx⟩, rfl⟩
    exact ⟨fun h => hxa (hf hx ha h), x, hx, rfl⟩

theorem AE_k2 (X : Finset (Lam d L N)) :
    AE (AffAut.transl t) (k2 j C V X) = k2 j C V ((AffAut.transl t).img X) := by
  have hj : j ≤ N := by have := H.hj2; omega
  have hinj : Set.InjOn (bmap j (AffAut.transl t)) (blocks j X : Set (Fin d → ℕ)) :=
    fun b hb b' hb' e => bmap_injOn (IsGen.transl t) hj H.hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb') e
  have hnb := H.hP.nb_img (IsGen.transl t) hj X
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
    rw [map_sum, image_erase_of_injOn hinj hb, sum_image fun x hx y hy e =>
      hinj (mem_of_mem_erase hx) (mem_of_mem_erase hy) e]
    refine sum_congr rfl fun b' hb'' => ?_
    rw [H.AE_FCE, H.AE_Vpr hb', H.AE_Vpr (blocks_subset_blockIdx X (mem_of_mem_erase hb''))]
  · rw [map_zero]

theorem sum_clo_transl {M : Type*} [AddCommMonoid M] (U : Finset (Lam d L N))
    (f : Finset (Lam d L N) → M) :
    (open Classical in
      ∑ X ∈ (Pj j univ).filter (fun X => clo j X = (AffAut.transl t).img U), f X) =
      (open Classical in ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U),
        f ((AffAut.transl t).img X)) := by
  classical
  have hj : j ≤ N := by have := H.hj2; omega
  have hPj : Pj j (univ : Finset (Lam d L N)) = (Pj j univ).image (AffAut.transl t).img := by
    have := Pj_img (IsGen.transl t) hj H.hP (univ : Finset (Lam d L N))
    rwa [img_univ] at this
  have hfil : ∀ X : Finset (Lam d L N),
      (clo j ((AffAut.transl t).img X) = (AffAut.transl t).img U) ↔ clo j X = U := fun X => by
    rw [H.hP1.clo_img (IsGen.transl t) (by have := H.hj2; omega)]
    exact (img_injective _).eq_iff
  conv_lhs => rw [hPj, filter_image]
  rw [sum_image fun X _ Y _ e => img_injective _ e]
  refine sum_congr ?_ fun _ _ => rfl
  ext X
  simp only [mem_filter, hfil]

theorem AE_K2 (U : Finset (Lam d L N)) :
    AE (AffAut.transl t) (K2 j C V U) = K2 j C V ((AffAut.transl t).img U) := by
  classical
  rw [K2, K2, map_sum, H.sum_clo_transl]
  exact sum_congr rfl fun X _ => H.AE_k2 X

theorem AE_Knew (U : Finset (Lam d L N)) :
    AE (AffAut.transl t) (Knew j C V W K U) = Knew j C V W K ((AffAut.transl t).img U) := by
  rw [Knew, Knew, map_sub, map_mul, H.AE_Knext2,
    AE_bpow (I := Gp j C V W K) (IsGen.transl t) (by have := H.hj2; omega) H.hP
      (fun b hb => H.AE_Gp hb), H.AE_K2]

theorem par_bmap {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    par L (bmap j (AffAut.transl t) b) = bmap (j + 1) (AffAut.transl t) (par L b) := by
  obtain ⟨x, -, rfl⟩ := mem_image.1 hb
  rw [← blk_succ, bmap_blk H.hP1, bmap_blk H.hP, blk_succ]

omit H in
theorem par_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    par L b ∈ blockIdx (L := L) (N := N) (j + 1) := by
  obtain ⟨x, -, rfl⟩ := mem_image.1 hb
  rw [← blk_succ]; exact mem_image_of_mem _ (mem_univ _)

theorem AE_It {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1)) :
    AE (AffAut.transl t) (It j C V W K c) = It j C V W K (bmap (j + 1) (AffAut.transl t) c) := by
  rw [It, It, AE_bpow (I := Gp j C V W K) (IsGen.transl t) (by have := H.hj2; omega) H.hP
      (fun b hb => H.AE_Gp hb),
    img_blockSet_bmap (IsGen.transl t) (by have := H.hj2; omega) H.hP1 hc]

theorem AE_kap {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1))
    (X : Finset (Lam d L N)) :
    AE (AffAut.transl t) (kap j C V X c) =
      kap j C V ((AffAut.transl t).img X) (bmap (j + 1) (AffAut.transl t) c) := by
  have hj : j ≤ N := by have := H.hj2; omega
  have hinj : Set.InjOn (bmap j (AffAut.transl t)) (blocks j X : Set (Fin d → ℕ)) :=
    fun b hb b' hb' e => bmap_injOn (IsGen.transl t) hj H.hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb') e
  have hfil : ((blocks j ((AffAut.transl t).img X)).filter
      fun b => par L b = bmap (j + 1) (AffAut.transl t) c) =
      ((blocks j X).filter fun b => par L b = c).image (bmap j (AffAut.transl t)) := by
    rw [blocks_img_bmap H.hP, filter_image]
    congr 1
    ext b
    simp only [mem_filter]
    constructor
    · rintro ⟨hb, h⟩
      refine ⟨hb, bmap_injOn (IsGen.transl t) (by have := H.hj2; omega) H.hP1
        (par_mem (blocks_subset_blockIdx X hb)) hc ?_⟩
      rw [← H.par_bmap (blocks_subset_blockIdx X hb)]; exact h
    · rintro ⟨hb, rfl⟩
      exact ⟨hb, H.par_bmap (blocks_subset_blockIdx X hb)⟩
  have hinj' : Set.InjOn (bmap j (AffAut.transl t))
      (((blocks j X).filter fun b => par L b = c : Finset _) : Set (Fin d → ℕ)) :=
    fun b hb b' hb' e => hinj (mem_filter.1 hb).1 (mem_filter.1 hb').1 e
  have hnb := H.hP.nb_img (IsGen.transl t) hj X
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
    rw [map_sum, blocks_img_bmap H.hP, image_erase_of_injOn hinj hbX,
      sum_image fun x hx y hy e => hinj (mem_of_mem_erase hx) (mem_of_mem_erase hy) e]
    refine sum_congr rfl fun b' hb'' => ?_
    rw [H.AE_FCE, H.AE_Vpr hb', H.AE_Vpr (blocks_subset_blockIdx X (mem_of_mem_erase hb''))]
  · rw [map_zero]

theorem AE_Jh {c : Fin d → ℕ} (hc : c ∈ blockIdx (L := L) (N := N) (j + 1))
    (U : Finset (Lam d L N)) :
    AE (AffAut.transl t) (Jh j C V c U) =
      Jh j C V (bmap (j + 1) (AffAut.transl t) c) ((AffAut.transl t).img U) := by
  classical
  have hs : IsSmall (j + 1) ((AffAut.transl t).img U) ↔ IsSmall (j + 1) U :=
    H.hP1.isSmall_img (IsGen.transl t) (by have := H.hj2; omega)
  unfold Jh
  by_cases hU : IsSmall (j + 1) U
  · rw [if_pos hU, if_pos (hs.2 hU), map_sum, H.sum_clo_transl]
    exact sum_congr rfl fun X _ => H.AE_kap hc X
  · rw [if_neg hU, if_neg (mt hs.1 hU), map_zero]

/-- **Covariance of `K_{j+1}`** under one translation. -/
theorem AE_Kplus (U : Finset (Lam d L N)) :
    AE (AffAut.transl t) (Kplus j C V W K U) = Kplus j C V W K ((AffAut.transl t).img U) := by
  exact AE_Kout (I := It j C V W K) (M := Knew j C V W K) (J := Jh j C V) (IsGen.transl t)
    (by have := H.hj2; omega) H.hP1 (fun c hc => H.AE_It hc) (fun Y _ => H.AE_Knew Y)
    (fun c hc X => H.AE_Jh hc X) U

end CovHyp

/-- **Translation covariance of `K_{j+1}`** at scale `j + 1` (Proposition `prop:W-contract`). -/
theorem Kplus_cov {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
    {K : Act d L N} (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj2 : j + 2 < N) (hC : GoodCov2 j ℓ C)
    (hCt : TInv C) (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0)
    (hK : InK2 j K) (hVc : FamCovG j V) (hWc : FamCovG j W) (hKc : KCov j K) :
    KCov (j + 1) (Kplus j C V W K) := by
  intro t ht X
  have H : CovHyp j ℓ C V W K t := ⟨hd, hL, hj2, hC, hCt, hV, hW, hV0, hK, hVc, hWc, hKc, ht⟩
  have := congrArg Subtype.val (H.AE_Kplus X)
  rw [coe_AE] at this
  exact this.symm


end

end Step2
