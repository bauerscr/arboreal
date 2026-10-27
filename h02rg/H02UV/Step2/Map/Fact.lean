import Step2.Map.ZetaFact

/-!
# Factorisation of the polymer formula over non-touching polymers

`Knext2_union`: for non-touching `(j+1)`-polymers `U₁, U₂`,

  `K^{pf}_{j+1}(U₁ ∪ U₂) = K^{pf}_{j+1}(U₁) K^{pf}_{j+1}(U₂)`

(Expected result `thm:closure`(c)). As in `Step.Knext_union'`, the summands over `𝒢(U₁ ∪ U₂)`
factorise along the bijection `gjoin`/`gsplit`. The expectation factorises by
`ECC_mul_of_sepZ`: the fluctuation (`ζ`) fields of the parts belonging to `U_i` lie in the
scale-`j` neighbourhood `U_i^□`, and these are at distance `> L^{j+1}/2`. The block factors
`I_{j+1}(B)` (which contain the nonlocal `𝒲_{j+1}(B)`) enter only through the inclusion and do not
contain `ζ`.
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

/-! ### `ζ`-locality of the integrand -/

section Gen

variable {j : ℕ} {Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)} {K : Act d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)} {U : Finset (Lam d L N)}
  {S2 : Subalgebra ℂ (Alg2 d L N)}

/-- Hypotheses for the membership of the integrand of `K_{j+1}(U)` in `S₂`. -/
structure GMemI (j : ℕ) (Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)) (K : Act d L N)
    (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)) (U : Finset (Lam d L N))
    (S2 : Subalgebra ℂ (Alg2 d L N)) : Prop where
  hK : ∀ Y, IsConn j Y → Y ⊆ U → thetaE (K Y) ∈ SE S2
  hJ : ∀ b X, b ∈ blockIdx (L := L) (N := N) j → blockSet j b ⊆ U → thetaE (J b X) ∈ SE S2
  hdI : ∀ b, b ∈ blockIdx (L := L) (N := N) j → blockSet j b ⊆ U → gdI Ib Ip b ∈ SE S2

namespace GMemI

variable (h : GMemI j Ib Ip K J U S2)
include h

theorem Kext_mem {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) :
    thetaE (Kext j K W) ∈ SE S2 := by
  rw [Kext, map_prod]
  exact prod_mem fun Y hY => h.hK Y (isConn_of_mem_comp hW hY) ((subset_of_mem_comp hY).trans hWU)

theorem dIPow_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    gdIPow j Ib Ip X ∈ SE S2 :=
  prod_mem fun b hb => h.hdI b (mem_blockIdx_of_mem_blocks hb)
    (blockSet_subset hU (blocks_mono hX hb))

theorem Kchk_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hXU : X ⊆ U) : gKchk j Ib Ip K J X ∈ SE S2 :=
  prod_mem fun W hW => sub_mem (Subalgebra.sum_mem _ fun Y hY => mul_mem
    (h.Kext_mem (IsPolymer.sdiff (isPolymer_of_mem_comp hX hW) (mem_Pj.1 hY).2)
      (sdiff_subset.trans ((subset_of_mem_comp hW).trans hXU)))
    (h.dIPow_mem hU ((mem_Pj.1 hY).1.trans ((subset_of_mem_comp hW).trans hXU))))
    (Subalgebra.sum_mem _ fun b hb => h.hJ b W (mem_blockIdx_of_mem_blocks hb)
      (blockSet_subset hU (blocks_mono ((subset_of_mem_comp hW).trans hXU) hb)))

theorem inner_mem (hU : IsPolymer j U) {g : GT d L N} (hg : g ∈ Gset j U) :
    gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2) ∈ SE S2 := by
  obtain ⟨h1, h2, -, h4⟩ := Gset_facts hg
  exact mul_mem (h.Kchk_mem hU h1 h2)
    (prod_mem fun p hp => h.hJ p.1 p.2 (mem_pairsU.1 (h4 p hp).1).1 (h4 p hp).2.2.1)

end GMemI

theorem gKchk_union {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B)
    (hAB : ¬ Touch A B) :
    gKchk j Ib Ip K J (A ∪ B) = gKchk j Ib Ip K J A * gKchk j Ib Ip K J B := by
  rw [gKchk, comp_union hA hB hAB, prod_union (disjoint_comp hA hAB), gKchk, gKchk]

end Gen

/-! ### Separation -/

theorem C2_eq_zero_of_nbhd (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N) {ℓ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (h : ¬ Touch U₁ U₂) {x y : Lam d L N} (hx : x ∈ nbhd j U₁) (hy : y ∈ nbhd j U₂) :
    x ≠ y ∧ C x y = 0 ∧ C y x = 0 := by
  have h1 := lt_two_mul_supNorm_of_nbhd hL hj hU₁ hU₂ h hx hy
  have h2 := lt_two_mul_supNorm_of_nbhd hL hj hU₂ hU₁ (fun t => h (touch_symm t)) hy hx
  have hjN : j + 1 < N := by
    rcases hj.lt_or_eq with hj' | hj'
    · exact hj'
    · exfalso
      have := two_mul_supNorm_le (x - y)
      rw [hj'] at h1
      omega
  refine ⟨?_, hC.range hjN x y ?_, hC.range hjN y x ?_⟩
  · rintro rfl
    rw [sub_self, supNorm_zero] at h1
    omega
  · have : ((L ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (supNorm (x - y) : ℝ) := by exact_mod_cast h1.le
    push_cast at this
    linarith
  · have : ((L ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (supNorm (y - x) : ℝ) := by exact_mod_cast h2.le
    push_cast at this
    linarith

/-! ### The concrete map -/

section Main

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}
  {K : Act d L N}

theorem gmemI (hd : 1 ≤ d) (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0)
    (hK : InK2 j K) (U : Finset (Lam d L N)) :
    GMemI j (Ib V W) (Ip j C V W K) K (J2 j K) U (NZ (nbhd j U : Set (Lam d L N))) where
  hK Y hY hYU := theta_mem_NZ (NX_mono (coe_subset.2 (nbhd_mono hYU)) (hK.loc Y hY))
  hJ b X hb hbU := theta_mem_NZ (NX_mono (coe_subset.2 (nbhd_mono hbU)) (J2_mem_NB hd hb X))
  hdI b _ hbU := sub_mem (theta_mem_NZ (NX_mono (coe_subset.2 (nbhd_mono hbU))
    (Ib_mem hV0 hV hW b))) (incl_mem_NZ _ _)

/-- The summand of `K^{pf}_{j+1}(U)`. -/
def Kterm2 (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (K : Act d L N)
    (U : Finset (Lam d L N)) (g : GT d L N) : EvR (Lam d L N) :=
  bpow j (Ip j C V W K) (U \ (g.2 ∪ Xcal g.1)) *
    ECCE C (gKchk j (Ib V W) (Ip j C V W K) K (J2 j K) g.2 * ∏ p ∈ g.1, thetaE (J2 j K p.1 p.2))

section Union

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hj : j + 1 ≤ N)
  {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
  (h : ¬ Touch U₁ U₂)
include hd hL hj hU₁ hU₂ h

theorem Kterm2_gjoin (hC : GoodCov2 j ℓ C) (hV : InF j V) (hW : InF j W)
    (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K) {x : GT d L N × GT d L N}
    (h₁ : x.1 ∈ Gset j U₁) (h₂ : x.2 ∈ Gset j U₂) :
    Kterm2 j C V W K (U₁ ∪ U₂) (gjoin x) = Kterm2 j C V W K U₁ x.1 * Kterm2 j C V W K U₂ x.2 := by
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
  have hI := bpow_union j (Ip j C V W K)
    (IsPolymer.sdiff hP₁ (IsPolymer.union a1 (isPolymer_Xcal a2)))
    (IsPolymer.sdiff hP₂ (IsPolymer.union b1 (isPolymer_Xcal b2)))
    (hD.mono sdiff_subset sdiff_subset)
  have hdisj : Disjoint x.1.1 x.2.1 := Finset.disjoint_left.2 fun p hp hq => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (fa4 p hp).1
    exact Finset.disjoint_left.1 hD ((fa4 p hp).2.2.1 hz) ((fb4 p hq).2.2.1 hz)
  have hsepX : Disjoint (nbhd j U₁ : Set (Lam d L N)) (nbhd j U₂ : Set (Lam d L N)) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact (C2_eq_zero_of_nbhd hL hj hC hU₁ hU₂ h hy hy').1 rfl
  have hsepC : ∀ y ∈ (nbhd j U₁ : Set (Lam d L N)), ∀ z ∈ (nbhd j U₂ : Set (Lam d L N)),
      C y z = 0 ∧ C z y = 0 := fun y hy z hz =>
    (C2_eq_zero_of_nbhd hL hj hC hU₁ hU₂ h hy hz).2
  have hF₁ := (gmemI (C := C) hd hV hW hV0 hK U₁).inner_mem hP₁ h₁
  have hF₂ := (gmemI (C := C) hd hV hW hV0 hK U₂).inner_mem hP₂ h₂
  have hE : ECCE C ((gKchk j (Ib V W) (Ip j C V W K) K (J2 j K) x.1.2 *
        ∏ p ∈ x.1.1, thetaE (J2 j K p.1 p.2)) *
      (gKchk j (Ib V W) (Ip j C V W K) K (J2 j K) x.2.2 *
        ∏ p ∈ x.2.1, thetaE (J2 j K p.1 p.2))) =
      ECCE C (gKchk j (Ib V W) (Ip j C V W K) K (J2 j K) x.1.2 *
        ∏ p ∈ x.1.1, thetaE (J2 j K p.1 p.2)) *
      ECCE C (gKchk j (Ib V W) (Ip j C V W K) K (J2 j K) x.2.2 *
        ∏ p ∈ x.2.1, thetaE (J2 j K p.1 p.2)) :=
    Subtype.ext (by
      simp only [coe_ECCE, MulMemClass.coe_mul]
      exact ECC_mul_of_sepZ C hsepX hsepC (mem_SE.1 hF₁) (mem_SE.1 hF₂))
  simp only [Kterm2, gjoin]
  rw [e1, hI, gKchk_union a1 b1 (not_touch_mono h fa2 fb2), prod_union hdisj,
    show ∀ a b c e : EvR (Lam d L N ⊕ Lam d L N), a * b * (c * e) = (a * c) * (b * e) from
      fun a b c e => by ring, hE]
  ring

theorem uX_union (hD : Disjoint U₁ U₂) :
    uX j C V W K (U₁ ∪ U₂) = uX j C V W K U₁ + uX j C V W K U₂ := by
  rw [uX, uX, uX, blocks_union, sum_union (disjoint_blocks (IsPolymer.of_succ hU₁)
    (IsPolymer.of_succ hU₂) hD)]

/-- **Factorisation of `K^{pf}_{j+1}`.** -/
theorem Knext2_union (hC : GoodCov2 j ℓ C) (hV : InF j V) (hW : InF j W)
    (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K) :
    Knext2 j C V W K (U₁ ∪ U₂) = Knext2 j C V W K U₁ * Knext2 j C V W K U₂ := by
  have hD := disjoint_of_not_touch h
  have e : ∀ U, gKnext j C (Ib V W) (Ip j C V W K) K (J2 j K) U =
      ∑ g ∈ Gset j U, Kterm2 j C V W K U g := fun U => rfl
  rw [Knext2, Knext2, Knext2, e, e, e, smul_mul_smul_comm, sum_mul_sum, ← sum_product',
    uX_union hd hL hj hU₁ hU₂ h hD, Complex.exp_add]
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
    exact (Kterm2_gjoin hd hL hj hU₁ hU₂ h hC hV hW hV0 hK h1 h2).symm

end Union

end Main

end

end Step2
