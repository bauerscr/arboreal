import Obs.GenericDecomp

/-!
# Factorisation of the generic `K_{j+1}` and compatibility with homomorphisms

* **Supports** (`SuppHyp`): families `S U ⊆ R`, `S2 U ⊆ R2` of subalgebras (the elements
  "belonging to" the `(j+1)`-polymer `U`, e.g. `𝒩(U^□)`), compatible with `θ` and `ι`, and
  containing the ingredients located in `U`.  The building blocks of `K_{j+1}(U)` then lie in
  `S U` resp. `S2 U` (`SuppHyp.inner_mem`, `SuppHyp.KnextG_mem`: the membership principle of
  `Step.MemHyp`).
* **Factorisation** (`KnextG_union`): if `E (f g) = E f E g` for `f ∈ S2 U₁`, `g ∈ S2 U₂`, then
  `K_{j+1}(U₁ ∪ U₂) = K_{j+1}(U₁) K_{j+1}(U₂)` for non-touching `(j+1)`-polymers, hence
  `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` (`KnextG_eq_KextG`) and `ZVK_G'`.  The separation
  hypothesis follows from a distance condition `> L^{j+1}/2` on a family `T2` with
  `S2 U = T2 (U^□)` (`sepE_of_dist`).
* **Homomorphisms** (`map_KnextG`, `map_ZnextG`, …): algebra homomorphisms commuting with
  `θ`, `ι`, `E` commute with the renormalisation group map.
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]

/-! ### Supports and the membership principle -/

/-- The support hypotheses: `S U`, `S2 U` are the elements belonging to `U`. -/
structure SuppHyp (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)
    (S : Finset (Lam d L N) → Subalgebra ℂ R) (S2 : Finset (Lam d L N) → Subalgebra ℂ R2) :
    Prop where
  hθ : ∀ U, ∀ f ∈ S U, A.θ f ∈ S2 U
  hι : ∀ U, ∀ f ∈ S U, A.ι f ∈ S2 U
  hK : ∀ U Y, IsConn j Y → Y ⊆ U → F.K Y ∈ S U
  hJ : ∀ U b Y, blockSet j b ⊆ Y → Y ⊆ U → F.J b Y ∈ S U
  hI0 : ∀ U b, blockSet j b ⊆ U → F.I0 b ∈ S U
  heV : ∀ U b, blockSet j b ⊆ U → F.eV b ∈ S U
  heum : ∀ U b, blockSet j b ⊆ U → F.eum b ∈ S U

section Mem

variable {A : RGAlg R R2} {j : ℕ} {F : RGIngr d L N R}
  {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}
  {U : Finset (Lam d L N)}

theorem SuppHyp.KextG_mem (h : SuppHyp A j F S S2) {W : Finset (Lam d L N)}
    (hW : IsPolymer j W) (hWU : W ⊆ U) : KextG j F.K W ∈ S U :=
  prod_mem fun Y hY => h.hK U Y (isConn_of_mem_comp hW hY) ((subset_of_mem_comp hY).trans hWU)

theorem SuppHyp.It_mem (h : SuppHyp A j F S S2) {b : Fin d → ℕ} (hb : blockSet j b ⊆ U) :
    It F b ∈ S U :=
  mul_mem (h.heum U b hb) (h.heV U b hb)

theorem SuppHyp.ItPow_mem (h : SuppHyp A j F S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : X ⊆ U) : ItPow j F X ∈ S U :=
  prod_mem fun _ hb => h.It_mem (blockSet_subset hU (blocks_mono hX hb))

theorem SuppHyp.dIG_mem (h : SuppHyp A j F S S2) {b : Fin d → ℕ} (hb : blockSet j b ⊆ U) :
    dIG A F b ∈ S2 U :=
  sub_mem (h.hθ U _ (h.hI0 U b hb)) (h.hι U _ (h.It_mem hb))

theorem SuppHyp.dIPowG_mem (h : SuppHyp A j F S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : X ⊆ U) : dIPowG A j F X ∈ S2 U :=
  prod_mem fun _ hb => h.dIG_mem (blockSet_subset hU (blocks_mono hX hb))

theorem SuppHyp.KtilG_mem (h : SuppHyp A j F S S2) (hU : IsPolymer j U)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) : KtilG A j F W ∈ S2 U :=
  Subalgebra.sum_mem _ fun _ hY => mul_mem
    (h.hθ U _ (h.KextG_mem (IsPolymer.sdiff hW (mem_Pj.1 hY).2) (sdiff_subset.trans hWU)))
    (h.dIPowG_mem hU ((mem_Pj.1 hY).1.trans hWU))

theorem SuppHyp.KchkCG_mem (h : SuppHyp A j F S S2) (hU : IsPolymer j U)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) : KchkCG A j F W ∈ S2 U :=
  sub_mem (h.KtilG_mem hU hW hWU) (Subalgebra.sum_mem _ fun b hb =>
    h.hθ U _ (h.hJ U b W (blockSet_subset hW hb) hWU))

theorem SuppHyp.KchkG_mem (h : SuppHyp A j F S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : IsPolymer j X) (hXU : X ⊆ U) : KchkG A j F X ∈ S2 U :=
  prod_mem fun _ hW => h.KchkCG_mem hU (isPolymer_of_mem_comp hX hW)
    ((subset_of_mem_comp hW).trans hXU)

/-- The argument of `E` in `K_{j+1}(U)` lies in `S2 U`. -/
theorem SuppHyp.inner_mem (h : SuppHyp A j F S S2) (hU : IsPolymer j U) {g : GT d L N}
    (h2 : IsPolymer j g.2) (h2U : g.2 ⊆ U) (h1 : ∀ p ∈ g.1, p ∈ pairsU j ∧ p.2 ⊆ U) :
    KchkG A j F g.2 * JprodG A F g.1 ∈ S2 U :=
  mul_mem (h.KchkG_mem hU h2 h2U) (prod_mem fun p hp => h.hθ U _
    (h.hJ U p.1 p.2 (mem_pairsU.1 (h1 p hp).1).2.2 (h1 p hp).2))

/-- **The membership principle**: `K_{j+1}(U) ∈ S U` if `E` maps `S2 U` to `S U` and the
prefactor lies in `S U`. -/
theorem SuppHyp.KnextG_mem (h : SuppHyp A j F S S2) (hU : IsPolymer (j + 1) U)
    (hE : ∀ f ∈ S2 U, A.E f ∈ S U) (heu : ∀ b, blockSet j b ⊆ U → F.eu b ∈ S U) :
    KnextG A j F U ∈ S U := by
  have hU' := IsPolymer.of_succ hU
  refine mul_mem (prod_mem fun b hb => heu b (blockSet_subset hU' hb))
    (Subalgebra.sum_mem _ fun g hg => ?_)
  obtain ⟨h1, h2, -, h4⟩ := Gset_facts hg
  exact mul_mem (h.ItPow_mem hU' sdiff_subset)
    (hE _ (h.inner_mem hU' h1 h2 fun p hp => ⟨(h4 p hp).1, (h4 p hp).2.2.2⟩))

end Mem

/-! ### Separation from distance -/

/-! ### Factorisation over non-touching polymers -/

section Union

variable {A : RGAlg R R2} {F : RGIngr d L N R}
  {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}

theorem KchkG_union (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R) {X Y : Finset (Lam d L N)}
    (hA : IsPolymer j X) (hB : IsPolymer j Y) (hAB : ¬ Touch X Y) :
    KchkG A j F (X ∪ Y) = KchkG A j F X * KchkG A j F Y := by
  rw [KchkG, comp_union hA hB hAB, prod_union (disjoint_comp hA hAB), KchkG, KchkG]

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
  {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
  (h : ¬ Touch U₁ U₂)
include hU₁ hU₂ h

/-- The summands factorise. -/
theorem KtermG_gjoin (hS : SuppHyp A j F S S2)
    (hsep : ∀ f ∈ S2 U₁, ∀ g ∈ S2 U₂, A.E (f * g) = A.E f * A.E g)
    {x : GT d L N × GT d L N} (h₁ : x.1 ∈ Gset j U₁) (h₂ : x.2 ∈ Gset j U₂) :
    KtermG A j F (U₁ ∪ U₂) (gjoin x) = KtermG A j F U₁ x.1 * KtermG A j F U₂ x.2 := by
  obtain ⟨a1, a2, -, -, -, -⟩ := mem_Gset'.1 h₁
  obtain ⟨b1, b2, -, -, -, -⟩ := mem_Gset'.1 h₂
  obtain ⟨-, fa2, fa3, fa4⟩ := Gset_facts h₁
  obtain ⟨-, fb2, fb3, fb4⟩ := Gset_facts h₂
  have hD := disjoint_of_not_touch h
  have hP₁ := IsPolymer.of_succ hU₁
  have hP₂ := IsPolymer.of_succ hU₂
  have e1 : (U₁ ∪ U₂) \ (x.1.2 ∪ x.2.2 ∪ Xcal (x.1.1 ∪ x.2.1)) =
      (U₁ \ (x.1.2 ∪ Xcal x.1.1)) ∪ (U₂ \ (x.2.2 ∪ Xcal x.2.1)) := by
    rw [Xcal_union]
    ext z
    have i1 := @fa2 z
    have i2 := @fa3 z
    have i3 := @fb2 z
    have i4 := @fb3 z
    have i5 : z ∈ U₁ → z ∉ U₂ := fun hz => Finset.disjoint_left.1 hD hz
    simp only [mem_union, mem_sdiff]
    exact prop_aux i1 i2 i3 i4 i5
  have hI := ItPow_union j F
    (IsPolymer.sdiff hP₁ (IsPolymer.union a1 (isPolymer_Xcal a2)))
    (IsPolymer.sdiff hP₂ (IsPolymer.union b1 (isPolymer_Xcal b2)))
    (hD.mono sdiff_subset sdiff_subset)
  have hdisj : Disjoint x.1.1 x.2.1 := Finset.disjoint_left.2 fun p hp hq => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (fa4 p hp).1
    exact Finset.disjoint_left.1 hD ((fa4 p hp).2.2.1 hz) ((fb4 p hq).2.2.1 hz)
  have hF₁ := hS.inner_mem hP₁ a1 fa2 fun p hp => ⟨(fa4 p hp).1, (fa4 p hp).2.2.2⟩
  have hF₂ := hS.inner_mem hP₂ b1 fb2 fun p hp => ⟨(fb4 p hp).1, (fb4 p hp).2.2.2⟩
  simp only [KtermG, gjoin]
  rw [e1, hI, KchkG_union A j F a1 b1 (not_touch_mono h fa2 fb2), JprodG, prod_union hdisj,
    show ∀ a b c e : R2, a * b * (c * e) = (a * c) * (b * e) from
      fun a b c e => by ring]
  have hs := hsep _ hF₁ _ hF₂
  simp only [JprodG] at hs ⊢
  rw [hs]
  ring

include hd hL hj in
/-- **Factorisation** (Proposition `prop:ZVK`): `K_{j+1}(U₁ ∪ U₂) = K_{j+1}(U₁) K_{j+1}(U₂)` for
non-touching `(j+1)`-polymers, if `E` factorises on the elements belonging to `U₁` and `U₂`. -/
theorem KnextG_union (hS : SuppHyp A j F S S2)
    (hsep : ∀ f ∈ S2 U₁, ∀ g ∈ S2 U₂, A.E (f * g) = A.E f * A.E g) :
    KnextG A j F (U₁ ∪ U₂) = KnextG A j F U₁ * KnextG A j F U₂ := by
  have hD := disjoint_of_not_touch h
  rw [KnextG, KnextG, KnextG, PrefG_union j F (IsPolymer.of_succ hU₁) (IsPolymer.of_succ hU₂) hD,
    mul_mul_mul_comm, sum_mul_sum, ← sum_product']
  congr 1
  symm
  refine sum_nbij' gjoin (gsplit j U₁ U₂) (fun x hx => ?_) (fun g hg => ?_) (fun x hx => ?_)
    (fun g hg => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gjoin_mem hU₁ hU₂ h h1 h2
  · exact mem_product.2 (gsplit_mem hd hL hj hU₁ hU₂ h hg)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gsplit_gjoin hU₁ hU₂ h h1 h2
  · exact gjoin_gsplit hU₁ hU₂ h hg
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact (KtermG_gjoin hU₁ hU₂ h hS hsep h1 h2).symm

end Union

theorem KnextG_empty (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R) (hE1 : A.E 1 = 1) :
    KnextG A j F (∅ : Finset (Lam d L N)) = 1 := by
  rw [KnextG, Gset_empty, sum_singleton, KtermG, PrefG_empty]
  simp only [Xcal_empty, empty_union, empty_sdiff, KchkG_empty, JprodG, prod_empty, mul_one, hE1]
  simp [ItPow, bpow, blocks]

/-! ### Compatibility with homomorphisms -/

section Hom

variable {S S2 : Type*} [CommRing S] [CommRing S2] [Algebra ℂ S] [Algebra ℂ S2]
  {A : RGAlg R R2} {A' : RGAlg S S2} (φ : R →ₐ[ℂ] S) (φ₂ : R2 →ₐ[ℂ] S2)
  (hθ : ∀ x, φ₂ (A.θ x) = A'.θ (φ x)) (hι : ∀ x, φ₂ (A.ι x) = A'.ι (φ x))
  (hE : ∀ y, φ (A.E y) = A'.E (φ₂ y))
  (j : ℕ) (F : RGIngr d L N R)

theorem map_KextG (K : Finset (Lam d L N) → R) (X : Finset (Lam d L N)) :
    φ (KextG j K X) = KextG j (fun Y => φ (K Y)) X := by
  simp only [KextG, map_prod]

theorem map_ItPow (X : Finset (Lam d L N)) : φ (ItPow j F X) = ItPow j (F.map φ) X := by
  simp only [ItPow, bpow, It, map_prod, map_mul, RGIngr.map]

theorem map_PrefG (X : Finset (Lam d L N)) : φ (PrefG j F X) = PrefG j (F.map φ) X := by
  simp only [PrefG, bpow, map_prod, RGIngr.map]

include hθ hι in
theorem map_dIPowG (X : Finset (Lam d L N)) :
    φ₂ (dIPowG A j F X) = dIPowG A' j (F.map φ) X := by
  simp only [dIPowG, bpow, dIG, It, map_prod, map_sub, map_mul, hθ, hι, RGIngr.map]

include hθ hι in
theorem map_KtilG (W : Finset (Lam d L N)) :
    φ₂ (KtilG A j F W) = KtilG A' j (F.map φ) W := by
  simp only [KtilG, map_sum, map_mul, hθ, map_KextG, map_dIPowG φ φ₂ hθ hι]
  rfl

include hθ hι in
theorem map_KchkG (X : Finset (Lam d L N)) :
    φ₂ (KchkG A j F X) = KchkG A' j (F.map φ) X := by
  simp only [KchkG, KchkCG, map_prod, map_sub, map_sum, hθ, map_KtilG φ φ₂ hθ hι]
  rfl

include hθ in
theorem map_JprodG (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    φ₂ (JprodG A F 𝒳) = JprodG A' (F.map φ) 𝒳 := by
  simp only [JprodG, map_prod, hθ]
  rfl

include hθ hι hE in
/-- **Compatibility with homomorphisms**: `φ K_{j+1}(U) = K_{j+1}(U)` computed from the
images `φ ∘ (ingredients)`. -/
theorem map_KnextG (U : Finset (Lam d L N)) :
    φ (KnextG A j F U) = KnextG A' j (F.map φ) U := by
  simp only [KnextG, KtermG, map_mul, map_sum, map_PrefG, map_ItPow, hE,
    map_KchkG φ φ₂ hθ hι, map_JprodG φ φ₂ hθ]

end Hom

end

end Obs.Gen
