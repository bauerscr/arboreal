import Obs.Generic
import Flow.ConsistStep

/-!
# The generic renormalisation group map and the embedding of tori (`prop:consistency`)

For `N ≤ M`, `Flow.emb N M : Λ_N → Λ_M` identifies `Λ_N` near the origin with `Λ_M`.  If two
instances of the generic map of `Obs.GenericDefs` (on `Λ_N` over `R`, `R2` and on `Λ_M` over `R'`,
`R2'`) are related by algebra homomorphisms `φ : R → R'`, `φ₂ : R2 → R2'` which commute with
`θ` and `ι`, and all ingredients of `K_{j+1}(U)` for a `(j+1)`-polymer `U` near the origin are
mapped to the corresponding ingredients (`φ ∘ I0 = I0' ∘ bemb`, …, `φ K(X) = K'(emb X)`), and `φ`
intertwines `E` and `E'` on the arguments of `E` in `K_{j+1}(U)`, then
`φ K_{j+1}(U) = K'_{j+1}(emb U)` (`E_KnextG`).

This is the generic form of `Flow.E_Knext`; the combinatorics (the correspondence of the index
sets `𝒢(U)` and `𝒢(emb U)`, `Flow.gemb`, `Flow.gpre`) is that of `Flow.ConsistStep`.
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L : ℕ} [NeZero L] {N M : ℕ}

section EmbGen

variable {R R2 R' R2' : Type*} [CommRing R] [CommRing R2] [CommRing R'] [CommRing R2']
  [Algebra ℂ R] [Algebra ℂ R2] [Algebra ℂ R'] [Algebra ℂ R2']
  {A : RGAlg R R2} {A' : RGAlg R' R2'} (φ : R →ₐ[ℂ] R') (φ₂ : R2 →ₐ[ℂ] R2')
  (hNM : N ≤ M) (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 2 ≤ N)
  {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
  (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N)
  {F : RGIngr d L N R} {F' : RGIngr d L M R'}

/-- The hypotheses of `E_KnextG`: `φ`, `φ₂` commute with `θ`, `ι` and map the ingredients of
`K_{j+1}(U)` to those on `Λ_M`. -/
structure EmbHyp (A : RGAlg R R2) (A' : RGAlg R' R2') (φ : R →ₐ[ℂ] R') (φ₂ : R2 →ₐ[ℂ] R2')
    (j : ℕ) (U : Finset (Lam d L N)) (F : RGIngr d L N R) (F' : RGIngr d L M R') : Prop where
  hθ : ∀ x, φ₂ (A.θ x) = A'.θ (φ x)
  hι : ∀ x, φ₂ (A.ι x) = A'.ι (φ x)
  hI0 : ∀ x ∈ U, φ (F.I0 (blk j x)) = F'.I0 (Flow.bemb L N M j (blk j x))
  heV : ∀ x ∈ U, φ (F.eV (blk j x)) = F'.eV (Flow.bemb L N M j (blk j x))
  heu : ∀ x ∈ U, φ (F.eu (blk j x)) = F'.eu (Flow.bemb L N M j (blk j x))
  heum : ∀ x ∈ U, φ (F.eum (blk j x)) = F'.eum (Flow.bemb L N M j (blk j x))
  hJ : ∀ x ∈ U, ∀ X ⊆ U,
    φ (F.J (blk j x) X) = F'.J (Flow.bemb L N M j (blk j x)) (X.image (Flow.emb N M))
  hK : ∀ X ⊆ U, IsConn j X → φ (F.K X) = F'.K (X.image (Flow.emb N M))
  hE : ∀ g ∈ Gset j U, φ (A.E (KchkG A j F g.2 * JprodG A F g.1)) =
    A'.E (φ₂ (KchkG A j F g.2 * JprodG A F g.1))

include hNM hd hL hj hUc hUd

theorem E_bpow {S S' G : Type*} [CommMonoid S] [CommMonoid S'] [FunLike G S S']
    [MonoidHomClass G S S'] (ψ : G) {f : (Fin d → ℕ) → S} {f' : (Fin d → ℕ) → S'}
    (hf : ∀ x ∈ U, ψ (f (blk j x)) = f' (Flow.bemb L N M j (blk j x)))
    {W : Finset (Lam d L N)} (hW : W ⊆ U) :
    ψ (bpow j f W) = bpow j f' (W.image (Flow.emb N M)) := by
  rw [bpow, bpow, map_prod, Flow.blocks_image' hNM hd hL hj hUc hUd hW,
    prod_image (Flow.bemb_injOn' hNM hd hL hj hUc hUd hW)]
  refine prod_congr rfl fun b hb => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  exact hf x (hW hx)

variable {φ φ₂}

theorem E_ItPow (h : EmbHyp A A' φ φ₂ j U F F') {W : Finset (Lam d L N)} (hW : W ⊆ U) :
    φ (ItPow j F W) = ItPow j F' (W.image (Flow.emb N M)) :=
  E_bpow hNM hd hL hj hUc hUd φ (fun x hx => by
    rw [It, It, map_mul, h.heum x hx, h.heV x hx]) hW

theorem E_PrefG (h : EmbHyp A A' φ φ₂ j U F F') :
    φ (PrefG j F U) = PrefG j F' (U.image (Flow.emb N M)) :=
  E_bpow hNM hd hL hj hUc hUd φ h.heu subset_rfl

theorem E_dIPowG (h : EmbHyp A A' φ φ₂ j U F F') {W : Finset (Lam d L N)} (hW : W ⊆ U) :
    φ₂ (dIPowG A j F W) = dIPowG A' j F' (W.image (Flow.emb N M)) :=
  E_bpow hNM hd hL hj hUc hUd φ₂ (fun x hx => by
    rw [dIG, dIG, map_sub, h.hθ, h.hι, h.hI0 x hx, It, It, map_mul, h.heum x hx,
      h.heV x hx]) hW

theorem E_KextG (h : EmbHyp A A' φ φ₂ j U F F') {W : Finset (Lam d L N)} (hWp : IsPolymer j W)
    (hW : W ⊆ U) : φ (KextG j F.K W) = KextG j F'.K (W.image (Flow.emb N M)) := by
  rw [KextG, KextG, map_prod, Flow.comp_image hNM (Flow.hPj hj) (Flow.num_facts hd hL hj).2.2.1
      fun x hx => Flow.pt5_of_mem hNM hd hL hj hUc hUd (hW hx),
    prod_image fun Y _ Y' _ e => Flow.image_emb_injective hNM e]
  refine prod_congr rfl fun Y hY => ?_
  exact h.hK Y ((subset_of_mem_comp hY).trans hW) (isConn_of_mem_comp hWp hY)

theorem E_KtilG (h : EmbHyp A A' φ φ₂ j U F F') {W : Finset (Lam d L N)} (hWp : IsPolymer j W)
    (hW : W ⊆ U) : φ₂ (KtilG A j F W) = KtilG A' j F' (W.image (Flow.emb N M)) := by
  rw [KtilG, KtilG, map_sum, Flow.Pj_image hNM (Flow.hPj hj) (Flow.num_facts hd hL hj).2.2.1
      fun x hx => Flow.pt5_of_mem hNM hd hL hj hUc hUd (hW hx),
    sum_image fun Y _ Y' _ e => Flow.image_emb_injective hNM e]
  refine sum_congr rfl fun Y hY => ?_
  obtain ⟨hYW, hYp⟩ := mem_Pj.1 hY
  rw [map_mul, h.hθ, E_KextG hNM hd hL hj hUc hUd h (IsPolymer.sdiff hWp hYp) (sdiff_subset.trans hW),
    E_dIPowG hNM hd hL hj hUc hUd h (hYW.trans hW), image_sdiff _ _ (Flow.emb_injective' hNM)]

theorem E_KchkCG (h : EmbHyp A A' φ φ₂ j U F F') {W : Finset (Lam d L N)}
    (hWp : IsPolymer j W) (hW : W ⊆ U) :
    φ₂ (KchkCG A j F W) = KchkCG A' j F' (W.image (Flow.emb N M)) := by
  rw [KchkCG, KchkCG, map_sub, E_KtilG hNM hd hL hj hUc hUd h hWp hW, map_sum,
    Flow.blocks_image' hNM hd hL hj hUc hUd hW,
    sum_image (Flow.bemb_injOn' hNM hd hL hj hUc hUd hW)]
  refine congrArg (fun t => KtilG A' j F' (W.image (Flow.emb N M)) - t) ?_
  refine sum_congr rfl fun b hb => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  rw [h.hθ, h.hJ x (hW hx) W hW]

theorem E_KchkG (h : EmbHyp A A' φ φ₂ j U F F') {X : Finset (Lam d L N)}
    (hXp : IsPolymer j X) (hX : X ⊆ U) :
    φ₂ (KchkG A j F X) = KchkG A' j F' (X.image (Flow.emb N M)) := by
  rw [KchkG, KchkG, map_prod, Flow.comp_image hNM (Flow.hPj hj) (Flow.num_facts hd hL hj).2.2.1
      fun x hx => Flow.pt5_of_mem hNM hd hL hj hUc hUd (hX hx),
    prod_image fun Y _ Y' _ e => Flow.image_emb_injective hNM e]
  exact prod_congr rfl fun W hW => E_KchkCG hNM hd hL hj hUc hUd h
    (isPolymer_of_mem_comp hXp hW) ((subset_of_mem_comp hW).trans hX)

theorem E_JprodG (h : EmbHyp A A' φ φ₂ j U F F') {g : GT d L N} (hfit : Flow.Fits j U g) :
    φ₂ (JprodG A F g.1) = JprodG A' F' (Flow.gemb L N M j g).1 := by
  show _ = ∏ p ∈ g.1.image (Flow.pemb L N M j), A'.θ (F'.J p.1 p.2)
  rw [JprodG, map_prod, prod_image (Flow.pemb_injOn hNM hd hL hj hUc hUd hfit.2)]
  refine prod_congr rfl fun p hp => ?_
  obtain ⟨hp2, x, hx, e⟩ := hfit.2 p hp
  rw [h.hθ, e, h.hJ x hx p.2 hp2]
  simp only [Flow.pemb, e]

theorem E_KtermG (h : EmbHyp A A' φ φ₂ j U F F') {g : GT d L N} (hg : g ∈ Gset j U) :
    φ (KtermG A j F U g) = KtermG A' j F' (U.image (Flow.emb N M)) (Flow.gemb L N M j g) := by
  obtain ⟨f1, f2, -, -⟩ := Gset_facts hg
  have hfit := Flow.fits_of_mem hg
  have hinj := Flow.emb_injective' (d := d) (L := L) hNM
  unfold KtermG
  rw [map_mul, E_ItPow hNM hd hL hj hUc hUd h sdiff_subset, h.hE g hg, map_mul,
    E_KchkG hNM hd hL hj hUc hUd h f1 f2, E_JprodG hNM hd hL hj hUc hUd h hfit,
    image_sdiff _ _ hinj, image_union, ← Flow.Xcal_gemb]
  rfl

/-- **`φ K_{j+1}(U) = K'_{j+1}(emb U)`** for the generic map. -/
theorem E_KnextG (h : EmbHyp A A' φ φ₂ j U F F') :
    φ (KnextG A j F U) = KnextG A' j F' (U.image (Flow.emb N M)) := by
  rw [KnextG, KnextG, map_mul, map_sum, E_PrefG hNM hd hL hj hUc hUd h]
  refine congrArg (fun t => PrefG j F' (U.image (Flow.emb N M)) * t) ?_
  exact sum_nbij' (Flow.gemb L N M j) (Flow.gpre L N M j)
    (fun g hg => Flow.gemb_mem hNM hd hL hj hUc hUd hg)
    (fun g hg => Flow.gpre_mem hNM hd hL hj hUc hUd hg)
    (fun g hg => Flow.gpre_gemb hNM hd hL hj hUc hUd (Flow.fits_of_mem hg))
    (fun g hg => (Flow.gpre_spec hNM hd hL hj hUc hUd hg).2)
    (fun g hg => E_KtermG hNM hd hL hj hUc hUd h hg)

end EmbGen

end

end Obs.Gen
