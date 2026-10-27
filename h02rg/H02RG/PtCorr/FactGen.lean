import Obs.GenericStructure

/-!
# Factorisation of the generic `K_{j+1}` with nonlocal `ψ`-dependence of `e^{-(u+V)_{j+1}}`

`Obs.Gen.KnextG_union` requires *all* ingredients (including `e^{-V_{j+1}(B)}` and
`e^{-u_{j+1}(B)}`) to lie in supports `S U` whose `θ`-images lie in the factorising supports
`S2 U`.  In Case (2) of the observable flow, `V^obs_{j+1}` contains the nonlocal term
`σ_aσ_b (η_{j+1}/4) (ψ̄_aψ_b + ψ̄_bψ_a)` in the half at `a` (split evaluation), and at the
step `j = j_ab` the points `a, b` need not be close at scale `j`; so these hypotheses fail.

However `e^{-(u+V)_{j+1}(B)}` only enters `K_{j+1}` through `ι` (as a function of the fluctuation
field it is constant), and `𝔼` does not see it.  `SuppHyp'` records this: the ingredients
`e^{-V_{j+1}(B)}`, `e^{-u_{j+1}(B)}` need not lie in `S U`; instead `ι` maps *everything* into
`S2 U`.  Under this weaker hypothesis the factorisation `KnextG_union'` and
`K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` (`KnextG_eq_KextG'`) hold, with the same proofs as
`Obs.Gen.KnextG_union`, `Obs.Gen.KnextG_eq_KextG`.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc FRD Step Obs.Gen

variable {d L N : ℕ} [NeZero L]

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]

/-- The relaxed support hypotheses: `θ` maps `S U` into `S2 U`, `ι` maps everything into
`S2 U`, and `K`, `J`, `e^{-V_j(B)}` are located (`e^{-(u+V)_{j+1}(B)}` need not be). -/
structure SuppHyp' (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)
    (S : Finset (Lam d L N) → Subalgebra ℂ R) (S2 : Finset (Lam d L N) → Subalgebra ℂ R2) :
    Prop where
  hθ : ∀ U, ∀ f ∈ S U, A.θ f ∈ S2 U
  hι : ∀ U, ∀ f : R, A.ι f ∈ S2 U
  hK : ∀ U Y, IsConn j Y → Y ⊆ U → F.K Y ∈ S U
  hJ : ∀ U b Y, blockSet j b ⊆ Y → Y ⊆ U → F.J b Y ∈ S U
  hI0 : ∀ U b, blockSet j b ⊆ U → F.I0 b ∈ S U

section Mem

variable {A : RGAlg R R2} {j : ℕ} {F : RGIngr d L N R}
  {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}
  {U : Finset (Lam d L N)}

theorem SuppHyp'.KextG_mem (h : SuppHyp' A j F S S2) {W : Finset (Lam d L N)}
    (hW : IsPolymer j W) (hWU : W ⊆ U) : KextG j F.K W ∈ S U :=
  prod_mem fun Y hY => h.hK U Y (isConn_of_mem_comp hW hY) ((subset_of_mem_comp hY).trans hWU)

theorem SuppHyp'.dIG_mem (h : SuppHyp' A j F S S2) {b : Fin d → ℕ} (hb : blockSet j b ⊆ U) :
    dIG A F b ∈ S2 U :=
  sub_mem (h.hθ U _ (h.hI0 U b hb)) (h.hι U _)

theorem SuppHyp'.dIPowG_mem (h : SuppHyp' A j F S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : X ⊆ U) : dIPowG A j F X ∈ S2 U :=
  prod_mem fun _ hb => h.dIG_mem (blockSet_subset hU (blocks_mono hX hb))

theorem SuppHyp'.KtilG_mem (h : SuppHyp' A j F S S2) (hU : IsPolymer j U)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) : KtilG A j F W ∈ S2 U :=
  Subalgebra.sum_mem _ fun _ hY => mul_mem
    (h.hθ U _ (h.KextG_mem (IsPolymer.sdiff hW (mem_Pj.1 hY).2) (sdiff_subset.trans hWU)))
    (h.dIPowG_mem hU ((mem_Pj.1 hY).1.trans hWU))

theorem SuppHyp'.KchkCG_mem (h : SuppHyp' A j F S S2) (hU : IsPolymer j U)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) : KchkCG A j F W ∈ S2 U :=
  sub_mem (h.KtilG_mem hU hW hWU) (Subalgebra.sum_mem _ fun b hb =>
    h.hθ U _ (h.hJ U b W (blockSet_subset hW hb) hWU))

theorem SuppHyp'.KchkG_mem (h : SuppHyp' A j F S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : IsPolymer j X) (hXU : X ⊆ U) : KchkG A j F X ∈ S2 U :=
  prod_mem fun _ hW => h.KchkCG_mem hU (isPolymer_of_mem_comp hX hW)
    ((subset_of_mem_comp hW).trans hXU)

/-- The argument of `E` in `K_{j+1}(U)` lies in `S2 U`. -/
theorem SuppHyp'.inner_mem (h : SuppHyp' A j F S S2) (hU : IsPolymer j U) {g : GT d L N}
    (h2 : IsPolymer j g.2) (h2U : g.2 ⊆ U) (h1 : ∀ p ∈ g.1, p ∈ pairsU j ∧ p.2 ⊆ U) :
    KchkG A j F g.2 * JprodG A F g.1 ∈ S2 U :=
  mul_mem (h.KchkG_mem hU h2 h2U) (prod_mem fun p hp => h.hθ U _
    (h.hJ U p.1 p.2 (mem_pairsU.1 (h1 p hp).1).2.2 (h1 p hp).2))

end Mem

/-! ### Factorisation over non-touching polymers -/

section Union

variable {A : RGAlg R R2} {F : RGIngr d L N R}
  {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
  {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
  (h : ¬ Touch U₁ U₂)
include hU₁ hU₂ h

/-- The summands factorise. -/
theorem KtermG_gjoin' (hS : SuppHyp' A j F S S2)
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
/-- **Factorisation** under the relaxed support hypotheses. -/
theorem KnextG_union' (hS : SuppHyp' A j F S S2)
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
    exact (KtermG_gjoin' hU₁ hU₂ h hS hsep h1 h2).symm

end Union

/-- `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` under the relaxed support hypotheses. -/
theorem KnextG_eq_KextG' (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    {A : RGAlg R R2} {F : RGIngr d L N R}
    {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}
    (hS : SuppHyp' A j F S S2) (hE1 : A.E 1 = 1)
    (hsep : ∀ U₁ U₂ : Finset (Lam d L N), IsPolymer (j + 1) U₁ → IsPolymer (j + 1) U₂ →
      ¬ Touch U₁ U₂ → ∀ f ∈ S2 U₁, ∀ g ∈ S2 U₂, A.E (f * g) = A.E f * A.E g)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnextG A j F U = KextG (j + 1) (KnextG A j F) U :=
  eq_prod_comp_of_mul (KnextG A j F) (KnextG_empty A j F hE1)
    (fun _ _ hA hB hAB => KnextG_union' hd hL hj hA hB hAB hS (hsep _ _ hA hB hAB)) hU

end

end PtCorr
