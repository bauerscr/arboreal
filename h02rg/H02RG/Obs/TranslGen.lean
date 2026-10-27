import Obs.GenericStructure

/-!
# Relabelling the generic renormalisation group map by a block preserving automorphism

Let `T` be a generated lattice automorphism mapping `j`- and `(j+1)`-blocks to blocks, and let
`G`, `F` be ingredients of the generic map (`Obs.Gen.RGIngr`) with
`G(B) = F(T B)` for the block quantities, `G.J(B, X) = F.J(T B, T X)` and
`G.K(Y) = F.K(T Y)` for connected `Y` (`Relabel`).  Then
`K_{j+1}[G](U) = K_{j+1}[F](T U)` (`KnextG_relabel`).

This is the purely combinatorial part of the automorphism covariance of the map (the bulk
version is `Step.AE_Knext`); combined with `map_KnextG` for an algebra automorphism it gives the
covariance of the observable map (`Obs.Transl`).
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

/-- `G` is the relabelling of `F` by `T` at scale `j`. -/
structure Relabel {R : Type*} (j : ℕ) (T : AffAut d L N) (G F : RGIngr d L N R) : Prop where
  I0 : ∀ b ∈ blockIdx (L := L) (N := N) j, G.I0 b = F.I0 (bmap j T b)
  eV : ∀ b ∈ blockIdx (L := L) (N := N) j, G.eV b = F.eV (bmap j T b)
  eu : ∀ b ∈ blockIdx (L := L) (N := N) j, G.eu b = F.eu (bmap j T b)
  eum : ∀ b ∈ blockIdx (L := L) (N := N) j, G.eum b = F.eum (bmap j T b)
  J : ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X, G.J b X = F.J (bmap j T b) (T.img X)
  K : ∀ Y, IsConn j Y → G.K Y = F.K (T.img Y)

section Relabel

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]
  (A : RGAlg R R2) {j : ℕ} {T : AffAut d L N} (hT : IsGen T) (hj : j ≤ N)
  (hP : PresBlocks j T) {G F : RGIngr d L N R} (h : Relabel j T G F)
include hT hj hP

theorem bpow_relabel {M : Type*} [CommMonoid M] {f g : (Fin d → ℕ) → M}
    (hfg : ∀ b ∈ blockIdx (L := L) (N := N) j, f b = g (bmap j T b)) (X : Finset (Lam d L N)) :
    bpow j f X = bpow j g (T.img X) := by
  rw [bpow, bpow, blocks_img_bmap hP,
    prod_image fun b hb b' hb' => bmap_injOn hT hj hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  exact prod_congr rfl fun b hb => hfg b (blocks_subset_blockIdx X hb)

theorem sum_blocks_relabel {M : Type*} [AddCommMonoid M] {f g : (Fin d → ℕ) → M}
    (hfg : ∀ b ∈ blockIdx (L := L) (N := N) j, f b = g (bmap j T b)) (X : Finset (Lam d L N)) :
    ∑ b ∈ blocks j X, f b = ∑ b ∈ blocks j (T.img X), g b := by
  rw [blocks_img_bmap hP,
    sum_image fun b hb b' hb' => bmap_injOn hT hj hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  exact sum_congr rfl fun b hb => hfg b (blocks_subset_blockIdx X hb)

include h

theorem KextG_relabel {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    KextG j G.K W = KextG j F.K (T.img W) := by
  rw [KextG, KextG, hP.comp_img hT hj, prod_image fun Y _ Y' _ e => img_injective T e]
  exact prod_congr rfl fun Y hY => h.K Y (isConn_of_mem_comp hW hY)

theorem It_relabel : ∀ b ∈ blockIdx (L := L) (N := N) j, It G b = It F (bmap j T b) :=
  fun b hb => by rw [It, It, h.eum b hb, h.eV b hb]

theorem ItPow_relabel (X : Finset (Lam d L N)) : ItPow j G X = ItPow j F (T.img X) :=
  bpow_relabel hT hj hP (It_relabel hT hj hP h) X

theorem PrefG_relabel (X : Finset (Lam d L N)) : PrefG j G X = PrefG j F (T.img X) :=
  bpow_relabel hT hj hP h.eu X

theorem dIG_relabel : ∀ b ∈ blockIdx (L := L) (N := N) j, dIG A G b = dIG A F (bmap j T b) :=
  fun b hb => by rw [dIG, dIG, h.I0 b hb, It_relabel hT hj hP h b hb]

theorem dIPowG_relabel (X : Finset (Lam d L N)) : dIPowG A j G X = dIPowG A j F (T.img X) :=
  bpow_relabel hT hj hP (dIG_relabel A hT hj hP h) X

theorem KtilG_relabel {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    KtilG A j G W = KtilG A j F (T.img W) := by
  rw [KtilG, KtilG, Pj_img hT hj hP, sum_image fun Y _ Y' _ e => img_injective T e]
  refine sum_congr rfl fun Y hY => ?_
  rw [KextG_relabel hT hj hP h (IsPolymer.sdiff hW (mem_Pj.1 hY).2),
    dIPowG_relabel A hT hj hP h, img_sdiff]

theorem KchkCG_relabel {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    KchkCG A j G W = KchkCG A j F (T.img W) := by
  rw [KchkCG, KchkCG, KtilG_relabel A hT hj hP h hW]
  congr 1
  exact sum_blocks_relabel hT hj hP (fun b hb => by rw [h.J b hb]) W

theorem KchkG_relabel {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    KchkG A j G X = KchkG A j F (T.img X) := by
  rw [KchkG, KchkG, hP.comp_img hT hj, prod_image fun Y _ Y' _ e => img_injective T e]
  exact prod_congr rfl fun W hW => KchkCG_relabel A hT hj hP h (isPolymer_of_mem_comp hX hW)

theorem KtermG_relabel {U : Finset (Lam d L N)} {g : GT d L N} (hg : g ∈ Gset j U) :
    KtermG A j G U g = KtermG A j F (T.img U) (gimg j T g) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := mem_Gset'.1 hg
  have hinj : Set.InjOn (fun p : (Fin d → ℕ) × Finset (Lam d L N) => (bmap j T p.1, T.img p.2))
      (g.1 : Set _) := by
    intro p hp q hq e
    exact h3 p hp q hq (img_injective T (congrArg Prod.snd e))
  rw [KtermG, KtermG, ItPow_relabel hT hj hP h, KchkG_relabel A hT hj hP h h1, img_sdiff,
    img_union, ← Xcal_gimg]
  simp only [gimg]
  congr 3
  rw [JprodG, JprodG, prod_image hinj]
  refine prod_congr rfl fun p hp => ?_
  rw [h.J p.1 (mem_pairsU.1 (h2 hp)).1]

omit hP in
/-- **Relabelling**: `K_{j+1}[G](U) = K_{j+1}[F](T U)`. -/
theorem KnextG_relabel (hj1 : j + 1 ≤ N) (hP1 : PresBlocks (j + 1) T)
    (hP : PresBlocks j T) (U : Finset (Lam d L N)) :
    KnextG A j G U = KnextG A j F (T.img U) := by
  obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
  have eE : ∀ x, T'.E (T.E x) = x := E_inv_of_img e
  have eE' : ∀ x, T.E (T'.E x) = x := E_inv_of_img e'
  have hP1' : PresBlocks (j + 1) T' := by
    intro x y hxy
    rw [← (hP1.blk_iff hT hj1), eE', eE']; exact hxy
  rw [KnextG, KnextG, PrefG_relabel hT hj hP h]
  congr 1
  refine sum_nbij' (gimg j T) (gimg j T') (fun g hg => gimg_mem hT hj1 hP hP1 hg)
    (fun g hg => ?_) (fun g hg => gimg_gimg hP hP' e hg) (fun g hg => gimg_gimg hP' hP e' hg)
    (fun g hg => KtermG_relabel A hT hj hP h hg)
  have := gimg_mem hT' hj1 hP' hP1' hg
  rwa [e] at this

end Relabel

end

end Obs.Gen
