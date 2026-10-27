import Obs2.Map.Supp
import Obs.MapSupp
import Obs.GenericStructure
import Step.EstCoupling

/-!
# Factorisation of the generic `K_{j+1}` with nonlocal block factors of scale `j + 1`

`Obs.Gen.SuppHyp` asks the block factors `e^{-V_{j+1}(B)}`, `e^{-u_{j+1}(B)}` of the new scale to
belong to the polymer (`heV`, `heum`). In the second-order map of `Step2` (and of `Obs2.Map.Map`) the
block factor of scale `j + 1` is `Ĩ_{j+1}(B) = e^{-V_{j+1}(B)}(1 + 𝒲_{j+1}(B))`, and `𝒲_{j+1}(B)`
is not local at scale `j`. It enters `K_{j+1}(U)` only through the inclusion `ι` (it contains no
fluctuation field), so it suffices that `ι` maps *everything* into the doubled support algebras.
`SuppHypW` is this variant; `KnextG_unionW`, `KnextG_eq_KextGW`, `ZVK_GW` are the factorisation
statements of `Obs.GenericStructure` under it (same proofs).
-/

namespace Obs2

noncomputable section

open Finset Grassmann Loc FRD Step Obs.Gen

variable {d L N : ℕ} [NeZero L]

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]

/-- Support hypotheses with arbitrary (nonlocal) block factors of scale `j + 1`: `ι` maps every
element into `S2 U`. -/
structure SuppHypW (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)
    (S : Finset (Lam d L N) → Subalgebra ℂ R) (S2 : Finset (Lam d L N) → Subalgebra ℂ R2) :
    Prop where
  hθ : ∀ U, ∀ f ∈ S U, A.θ f ∈ S2 U
  hι : ∀ U f, A.ι f ∈ S2 U
  hK : ∀ U Y, IsConn j Y → Y ⊆ U → F.K Y ∈ S U
  hJ : ∀ U b Y, b ∈ blockIdx (L := L) (N := N) j → blockSet j b ⊆ Y → Y ⊆ U → F.J b Y ∈ S U
  hI0 : ∀ U b, blockSet j b ⊆ U → F.I0 b ∈ S U

namespace SuppHypW

variable {A : RGAlg R R2} {j : ℕ} {F : RGIngr d L N R}
  {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}
  {U : Finset (Lam d L N)} (h : SuppHypW A j F S S2)
include h

theorem KextG_mem {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) :
    KextG j F.K W ∈ S U :=
  prod_mem fun Y hY => h.hK U Y (isConn_of_mem_comp hW hY) ((subset_of_mem_comp hY).trans hWU)

theorem dIG_mem {b : Fin d → ℕ} (hb : blockSet j b ⊆ U) : dIG A F b ∈ S2 U :=
  sub_mem (h.hθ U _ (h.hI0 U b hb)) (h.hι U _)

theorem dIPowG_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    dIPowG A j F X ∈ S2 U :=
  prod_mem fun _ hb => h.dIG_mem (blockSet_subset hU (blocks_mono hX hb))

theorem KtilG_mem (hU : IsPolymer j U) {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    (hWU : W ⊆ U) : KtilG A j F W ∈ S2 U :=
  Subalgebra.sum_mem _ fun _ hY => mul_mem
    (h.hθ U _ (h.KextG_mem (IsPolymer.sdiff hW (mem_Pj.1 hY).2) (sdiff_subset.trans hWU)))
    (h.dIPowG_mem hU ((mem_Pj.1 hY).1.trans hWU))

theorem KchkCG_mem (hU : IsPolymer j U) {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    (hWU : W ⊆ U) : KchkCG A j F W ∈ S2 U :=
  sub_mem (h.KtilG_mem hU hW hWU) (Subalgebra.sum_mem _ fun b hb =>
    h.hθ U _ (h.hJ U b W (mem_blockIdx_of_mem_blocks hb) (blockSet_subset hW hb) hWU))

theorem KchkG_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hXU : X ⊆ U) : KchkG A j F X ∈ S2 U :=
  prod_mem fun _ hW => h.KchkCG_mem hU (isPolymer_of_mem_comp hX hW)
    ((subset_of_mem_comp hW).trans hXU)

theorem inner_mem (hU : IsPolymer j U) {g : GT d L N}
    (h2 : IsPolymer j g.2) (h2U : g.2 ⊆ U) (h1 : ∀ p ∈ g.1, p ∈ pairsU j ∧ p.2 ⊆ U) :
    KchkG A j F g.2 * JprodG A F g.1 ∈ S2 U :=
  mul_mem (h.KchkG_mem hU h2 h2U) (prod_mem fun p hp => h.hθ U _
    (h.hJ U p.1 p.2 (mem_pairsU.1 (h1 p hp).1).1 (mem_pairsU.1 (h1 p hp).1).2.2 (h1 p hp).2))

end SuppHypW

section Union

variable {A : RGAlg R R2} {F : RGIngr d L N R}
  {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
  {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
  (h : ¬ Touch U₁ U₂)
include hU₁ hU₂ h

theorem KtermG_gjoinW (hS : SuppHypW A j F S S2)
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
/-- **Factorisation** of the generic `K_{j+1}` under `SuppHypW`. -/
theorem KnextG_unionW (hS : SuppHypW A j F S S2)
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
    exact (KtermG_gjoinW hU₁ hU₂ h hS hsep h1 h2).symm

end Union

/-- `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` under `SuppHypW`. -/
theorem KnextG_eq_KextGW (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    {A : RGAlg R R2} {F : RGIngr d L N R}
    {S : Finset (Lam d L N) → Subalgebra ℂ R} {S2 : Finset (Lam d L N) → Subalgebra ℂ R2}
    (hS : SuppHypW A j F S S2) (hE1 : A.E 1 = 1)
    (hsep : ∀ U₁ U₂ : Finset (Lam d L N), IsPolymer (j + 1) U₁ → IsPolymer (j + 1) U₂ →
      ¬ Touch U₁ U₂ → ∀ f ∈ S2 U₁, ∀ g ∈ S2 U₂, A.E (f * g) = A.E f * A.E g)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnextG A j F U = KextG (j + 1) (KnextG A j F) U :=
  eq_prod_comp_of_mul (KnextG A j F) (KnextG_empty A j F hE1)
    (fun _ _ hA hB hAB => KnextG_unionW hd hL hj hA hB hAB hS (hsep _ _ hA hB hAB)) hU

end

end Obs2


/-!
# The exact polymer formula with sources and its factorisation (`sec:obs-flow`)

The second-order map with sources of `Obs2.Map.Map` is an instance of the generic map of
`Obs.GenericDefs` (`algO`, `ingrO`): `R = OE c Λ`, `R2 = OE c (Λ ⊔ Λ)`, `θ = thetaO`,
`ι = inclO`, `E = ECCO C`, block factors `I_j(B) = e^{-V(B)}(1 + 𝒲(B))`,
`I_{j+1}(B) = e^{-u_{j+1}(B)} Ĩ_{j+1}(B)` with the extended `e^{±u} = expU`, and `J = J2O`.

* `Knext2O_eq_KnextG`: `K_{j+1}` of `Obs2.Map.Map` is the generic `KnextG`;
* **`stepO_ZVK`** (exact, no hypotheses): `𝔼_C θ Z_j = e^{-u_{j+1}(Λ)} ∑_U Ĩ_{j+1}^{Λ∖U} K_{j+1}(U)`
  on the algebra with sources (`Z_j = gZO j I_j K`);
* **`Knext2O_eq_KextO`** (factorisation): `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` under the
  locality hypothesis `OLocHyp` and a finite-range covariance.

## The pointed localisation and the factorisation
The pointed `loc^a_{X,Y}` of `Obs2.Loc.Loc` localises at `a` also for `X ∌ a`, so `J(B, Y)` has a
field at `a` which need not lie in `Y`. The factorisation needs every piece of `K_{j+1}(U)` to be
local in a neighbourhood of `U`. This holds with the doubled neighbourhood
`U^{□□} = nb2 j U` (`J2O_mem`) provided the source components of `K(Y)`, `Y` small, vanish unless
the corresponding point lies in `Y^□` (`OLocHyp.hKa`, `hKb`, the support property of the
observable flow, cf. `Obs2.Pair.Coal`); the price is `L ≥ 2^{d+3}` instead of `2^{d+2}`
(`lt_two_mul_supNorm_of_nb2`). The block factors of scale `j + 1` (which contain the nonlocal
`𝒲_{j+1}`) enter only through `ι` (`Obs2.ExactGen`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs.Gen LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### The extended exponential -/

section ExpU

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem oexp_add_obs {F G : OE c Λ} (hF : bulk F = 0) (hG : bulk G = 0) :
    oexp (F + G) = oexp F * oexp G :=
  IsNilpotent.exp_add_of_commute (Commute.all F G) (isNilpotent_of_obs hF) (isNilpotent_of_obs hG)

theorem expU_mul_expU (x y : ℂ) {F G : OE c Λ} (hF : bulk F = 0) (hG : bulk G = 0) :
    expU x F * expU y G = expU (x + y) (F + G) := by
  rw [expU, expU, expU, smul_mul_smul_comm, ← Complex.exp_add, oexp_add_obs hF hG]

theorem expU_zero_zero : expU (0 : ℂ) (0 : OE c Λ) = 1 := by
  rw [expU, Complex.exp_zero, one_smul, oexp, IsNilpotent.exp_zero]

theorem prod_expU {ι : Type*} (s : Finset ι) (x : ι → ℂ) (F : ι → OE c Λ)
    (hF : ∀ i ∈ s, bulk (F i) = 0) :
    ∏ i ∈ s, expU (x i) (F i) = expU (∑ i ∈ s, x i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, sum_empty, sum_empty, expU_zero_zero]
  | insert i s hi ih =>
    have hs : bulk (∑ k ∈ s, F k) = 0 := by
      rw [map_sum]; exact sum_eq_zero fun k hk => hF k (mem_insert_of_mem hk)
    rw [prod_insert hi, sum_insert hi, sum_insert hi,
      ih (fun k hk => hF k (mem_insert_of_mem hk)),
      expU_mul_expU _ _ (hF i (mem_insert_self i s)) hs]

theorem expU_mul_expU_neg (x : ℂ) {F : OE c Λ} (hF : bulk F = 0) :
    expU x F * expU (-x) (-F) = 1 := by
  rw [expU_mul_expU _ _ hF (by rw [map_neg, hF, neg_zero]), add_neg_cancel, add_neg_cancel,
    expU_zero_zero]

end ExpU

/-! ### The instance -/

/-- The algebraic data of one step with sources. -/
def algO (C : Matrix (Lam d L N) (Lam d L N) ℂ) :
    RGAlg (OE c (Lam d L N)) (OE c (Lam d L N ⊕ Lam d L N)) :=
  ⟨thetaO, inclO, ECCO C⟩

/-- The ingredients of the second-order map with sources. -/
def ingrO (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (K : OAct c d L N) : RGIngr d L N (OE c (Lam d L N)) where
  I0 := IbO V W
  eV := GpO P j C V W K
  eu b := expU (upB P j C V W K b) (upO P j C V W K b)
  eum b := expU (-upB P j C V W K b) (-upO P j C V W K b)
  J := J2O P j K
  K := K

/-- `Z_j = ∑_{X ∈ 𝒫_j} I^{Λ∖X} K(X)` with sources. -/
def gZO (j : ℕ) (I : OFam c d L N) (K : OAct c d L N) : OE c (Lam d L N) :=
  ∑ X ∈ Pj j (univ : Finset (Lam d L N)), bpowO j I (univ \ X) * KextO j K X

section Inst

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

theorem PrefG_ingrO (U : Finset (Lam d L N)) :
    PrefG j (ingrO P j C V W K) U = expU (uXB P j C V W K U) (uXO P j C V W K U) := by
  show ∏ b ∈ blocks j U, expU (upB P j C V W K b) (upO P j C V W K b) = _
  exact prod_expU _ _ _ fun b _ => bulk_upO P j C V W K b

theorem IpO_eq_It : IpO P j C V W K = It (ingrO P j C V W K) := rfl

set_option maxHeartbeats 4000000 in
theorem gKnextO_eq_sum (U : Finset (Lam d L N)) :
    gKnextO j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U =
      ∑ g ∈ Gset j U, KtermG (algO C) j (ingrO P j C V W K) U g := by
  rw [IpO_eq_It]
  exact sum_congr rfl fun _ _ => rfl

/-- **`K_{j+1}` of `Obs2.Map.Map` is the generic `KnextG`.** -/
theorem Knext2O_eq_KnextG (U : Finset (Lam d L N)) :
    Knext2O P j C V W K U = KnextG (algO C) j (ingrO P j C V W K) U := by
  show expU (uXB P j C V W K U) (uXO P j C V W K U) *
      gKnextO j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U =
    PrefG j (ingrO P j C V W K) U * ∑ g ∈ Gset j U, KtermG (algO C) j (ingrO P j C V W K) U g
  rw [PrefG_ingrO, gKnextO_eq_sum]

theorem bpow_eum_ingrO :
    bpow j (ingrO P j C V W K).eum (univ : Finset (Lam d L N)) =
      expU (-uXB P j C V W K univ) (-uXO P j C V W K univ) := by
  show ∏ b ∈ blocks j univ, expU (-upB P j C V W K b) (-upO P j C V W K b) = _
  rw [prod_expU _ _ _ fun b _ => by rw [map_neg, bulk_upO, neg_zero], sum_neg_distrib,
    sum_neg_distrib]
  rfl

/-- **Proposition `prop:ZVK` with sources** (exact, no hypotheses):
`𝔼_C θ Z_j = e^{-u_{j+1}(Λ)} ∑_{U ∈ 𝒫_{j+1}} Ĩ_{j+1}^{Λ∖U} K_{j+1}(U)`, with the extended
constant `e^{-u} = expU (-u^∅) (-u^{obs})`. -/
theorem stepO_ZVK :
    ECCO C (thetaO (gZO j (IbO V W) K)) =
      expU (-uXB P j C V W K univ) (-uXO P j C V W K univ) *
        ∑ U ∈ Pj (j + 1) (univ : Finset (Lam d L N)),
          bpowO j (GpO P j C V W K) (univ \ U) * Knext2O P j C V W K U := by
  have h := ZVK_G (algO C) j (ingrO P j C V W K) (fun a g => ECCO_inclO_mul C a g)
    (fun b X hX => J2O_of_not_small P j K b X hX)
    (fun b _ => expU_mul_expU_neg _ (bulk_upO P j C V W K b))
  rw [ZnextG, bpow_eum_ingrO] at h
  refine h.trans ?_
  congr 1
  refine sum_congr rfl fun U _ => ?_
  rw [Knext2O_eq_KnextG]
  rfl

end Inst

/-! ### Geometry: the doubled neighbourhood -/

/-- `X^{□□}`. -/
def nb2 (j : ℕ) (X : Finset (Lam d L N)) : Finset (Lam d L N) := nbhd j (nbhd j X)

theorem exists_near_of_mem_nb2 {j : ℕ} {X : Finset (Lam d L N)} {y : Lam d L N}
    (hy : y ∈ nb2 j X) : ∃ x ∈ X, supNorm (y - x) ≤ 2 * (2 ^ d * L ^ j) := by
  obtain ⟨z, hz, h1⟩ := exists_near_of_mem_nbhd hy
  obtain ⟨x, hx, h2⟩ := exists_near_of_mem_nbhd hz
  refine ⟨x, hx, ?_⟩
  have e : y - x = (y - z) + (z - x) := by abel
  have h3 := supNorm_add_le (y - z) (z - x)
  rw [← e] at h3
  omega

theorem nb2_mono {j : ℕ} {X Y : Finset (Lam d L N)} (h : X ⊆ Y) : nb2 j X ⊆ nb2 j Y :=
  nbhd_mono (nbhd_mono h)

theorem nbhd_subset_nb2 (j : ℕ) (X : Finset (Lam d L N)) : nbhd j X ⊆ nb2 j X :=
  subset_nbhd (isPolymer_nbhd j X)

/-- For non-touching `(j+1)`-polymers, `U_1^{□□}` and `U_2^{□□}` are at distance
`> L^{j+1}/2` (`L ≥ 2^{d+3}`). -/
theorem lt_two_mul_supNorm_of_nb2 (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (h : ¬ Touch U₁ U₂) {x y : Lam d L N} (hx : x ∈ nb2 j U₁) (hy : y ∈ nb2 j U₂) :
    L ^ (j + 1) < 2 * supNorm (x - y) := by
  obtain ⟨x₁, hx₁, h1⟩ := exists_near_of_mem_nb2 hx
  obtain ⟨y₁, hy₁, h2⟩ := exists_near_of_mem_nb2 hy
  have h3 := lt_supNorm_of_not_touch hj hU₁ hU₂ h hx₁ hy₁
  have e : x₁ - y₁ = (x₁ - x) + ((x - y) + (y - y₁)) := by abel
  have h4 := supNorm_add_le (x₁ - x) ((x - y) + (y - y₁))
  have h5 := supNorm_add_le (x - y) (y - y₁)
  rw [supNorm_sub_comm] at h1
  have h6 : 8 * (2 ^ d * L ^ j) ≤ L ^ (j + 1) := by
    calc 8 * (2 ^ d * L ^ j) = 2 ^ (d + 3) * L ^ j := by ring
      _ ≤ L * L ^ j := Nat.mul_le_mul_right _ hL
      _ = L ^ (j + 1) := by ring
  rw [e] at h3
  omega

/-- Range of a covariance: `C(x, y) = 0` for `|x - y|_∞ ≥ L^{j+1}/2`. -/
def CovRange (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) : Prop :=
  ∀ x y : Lam d L N, (L : ℝ) ^ (j + 1) / 2 ≤ supNorm (x - y) → C x y = 0

theorem C_zero_of_nb2 (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : CovRange j C)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (h : ¬ Touch U₁ U₂) {x y : Lam d L N} (hx : x ∈ nb2 j U₁) (hy : y ∈ nb2 j U₂) :
    x ≠ y ∧ C x y = 0 ∧ C y x = 0 := by
  have h1 := lt_two_mul_supNorm_of_nb2 hL hj hU₁ hU₂ h hx hy
  have h2 := lt_two_mul_supNorm_of_nb2 hL hj hU₂ hU₁ (fun t => h (touch_symm t)) hy hx
  refine ⟨?_, hC x y ?_, hC y x ?_⟩
  · rintro rfl
    rw [sub_self, supNorm_zero] at h1
    omega
  · have : ((L ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (supNorm (x - y) : ℝ) := by exact_mod_cast h1.le
    push_cast at this
    linarith
  · have : ((L ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (supNorm (y - x) : ℝ) := by exact_mod_cast h2.le
    push_cast at this
    linarith

/-! ### Componentwise supports -/

section Comp

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem thetaO_mem_cZ {S : Set Λ} {F : OE c Λ}
    (hF : F ∈ (compSub (NX S) True True : Subalgebra ℂ (OE c Λ))) :
    thetaO F ∈ (compSub (NZ S) True True : Subalgebra ℂ (OE c (Λ ⊕ Λ))) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hF
  exact ⟨theta_mem_NZ h1, theta_mem_NZ h2, theta_mem_NZ h3, theta_mem_NZ h4,
    fun h => absurd trivial h, fun h => absurd trivial h⟩

theorem inclO_mem_cZ (S : Set Λ) (F : OE c Λ) :
    inclO F ∈ (compSub (NZ S) True True : Subalgebra ℂ (OE c (Λ ⊕ Λ))) :=
  ⟨incl_mem_NZ S _, incl_mem_NZ S _, incl_mem_NZ S _, incl_mem_NZ S _,
    fun h => absurd trivial h, fun h => absurd trivial h⟩

/-- **Factorisation of `𝔼_C` with sources** over separated `ζ`-supports (componentwise from
`Step2.ECC_mul_of_sepZ`). -/
theorem ECCO_mul_of_sepZ (C : Matrix Λ Λ ℂ) {X₁ X₂ : Set Λ} (hX : Disjoint X₁ X₂)
    (hC : ∀ x ∈ X₁, ∀ y ∈ X₂, C x y = 0 ∧ C y x = 0) {pa pb pa' pb' : Prop}
    {F G : OE c (Λ ⊕ Λ)} (hF : F ∈ (compSub (NZ X₁) pa pb : Subalgebra ℂ (OE c (Λ ⊕ Λ))))
    (hG : G ∈ (compSub (NZ X₂) pa' pb' : Subalgebra ℂ (OE c (Λ ⊕ Λ)))) :
    ECCO C (F * G) = ECCO C F * ECCO C G := by
  obtain ⟨f1, f2, f3, f4, -, -⟩ := hF
  obtain ⟨g1, g2, g3, g4, -, -⟩ := hG
  have m := fun {x y : Grassmann.N (Λ ⊕ Λ)} (hx : x ∈ NZ X₁) (hy : y ∈ NZ X₂) =>
    ECC_mul_of_sepZ C hX hC hx hy
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [OE.mul_e, coe_ECCO, ECCS_e, OE.mul_e, coe_ECCO, coe_ECCO, ECCS_e, ECCS_e, m f1 g1]
  · rw [OE.mul_a, coe_ECCO, ECCS_a, OE.mul_a, coe_ECCO, coe_ECCO, ECCS_e, ECCS_e, ECCS_a,
      ECCS_a, map_add, m f1 g2, m f2 g1]
  · rw [OE.mul_b, coe_ECCO, ECCS_b, OE.mul_b, coe_ECCO, coe_ECCO, ECCS_e, ECCS_e, ECCS_b,
      ECCS_b, map_add, m f1 g3, m f3 g1]
  · rw [OE.mul_ab, coe_ECCO, ECCS_ab, OE.mul_ab, coe_ECCO, coe_ECCO, ECCS_e, ECCS_e, ECCS_a,
      ECCS_a, ECCS_b, ECCS_b, ECCS_ab, ECCS_ab, map_add, map_add, map_add, map_smul, m f1 g4,
      m f2 g3, m f3 g2, m f4 g1]

end Comp

/-! ### Locality of the localised components -/

section LocMem

theorem psi_mem_NX' {S : Set (Lam d L N)} {x : Lam d L N} (hx : x ∈ S) : psi x ∈ NX S :=
  ψ_mem_NX (a := (x, 1)) hx

theorem psibar_mem_NX' {S : Set (Lam d L N)} {x : Lam d L N} (hx : x ∈ S) : psibar x ∈ NX S :=
  ψ_mem_NX (a := (x, -1)) hx

theorem locABt_mem (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    locABt X a b F ∈ NX ({a, b} : Set (Lam d L N)) := by
  have ha : a ∈ ({a, b} : Set (Lam d L N)) := by simp
  have hb : b ∈ ({a, b} : Set (Lam d L N)) := by simp
  have h0 : locEven {a} X X F ∈ NX ({a} : Set (Lam d L N)) := locA_mem (c := Obs.Case.two) a X X F
  have hpa := psi_mem_NX' ha
  have hpb := psi_mem_NX' hb
  have hqa := psibar_mem_NX' ha
  have hqb := psibar_mem_NX' hb
  have hdb : dbar a b ∈ NX ({a, b} : Set (Lam d L N)) := sub_mem hqb hqa
  have hdl : dlt a b ∈ NX ({a, b} : Set (Lam d L N)) := sub_mem hpb hpa
  have hpbp : pbp a ∈ NX ({a, b} : Set (Lam d L N)) := mul_mem hqa hpa
  refine add_mem (NX_mono (by simp) h0) ?_
  unfold Dt
  exact add_mem (add_mem (add_mem (Subalgebra.smul_mem _ (mul_mem hdb hpa) _)
    (Subalgebra.smul_mem _ (mul_mem hqa hdl) _)) (Subalgebra.smul_mem _ (mul_mem hdb hdl) _))
    (Subalgebra.smul_mem _ (mul_mem hpbp (mul_mem hdb hdl)) _)

theorem locABtXY_mem (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locABtXY P X Y F ∈ NX ({P.a, P.b} : Set (Lam d L N)) := by
  refine Subalgebra.smul_mem _ ?_ _
  unfold locABtX
  split_ifs
  · exact locABt_mem _ _ _ _
  · rw [Set.pair_comm]; exact locABt_mem _ _ _ _

variable (P : ObsPts d L N) {j : ℕ}

/-- **`Loc_{Y,B} F` lies in `B^{□□}`** if the source components of `F` vanish unless the
corresponding points lie in `Y^□` (`Y` small, `B ⊆ Y`). -/
theorem LocO2_mem_nb2 (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    {Y : Finset (Lam d L N)} (hY : IsSmall j Y) (hbY : blockSet j b ⊆ Y) {F : OE c (Lam d L N)}
    (hFa : P.a ∉ nbhd j Y → (F : SA c (Lam d L N)).a = 0 ∧ (F : SA c (Lam d L N)).ab = 0)
    (hFb : P.b ∉ nbhd j Y → (F : SA c (Lam d L N)).b = 0 ∧ (F : SA c (Lam d L N)).ab = 0) :
    LocO2 P Y (blockSet j b) F ∈ (compSub (NX (nb2 j (blockSet (L := L) (N := N) j b) :
      Set (Lam d L N))) True True : Subalgebra ℂ (OE c (Lam d L N))) := by
  have hne : (blockSet (L := L) (N := N) j b).Nonempty := by
    obtain ⟨x, -, rfl⟩ := mem_image.1 hb
    exact ⟨x, mem_blockSet_blk j x⟩
  have hYn : nbhd j Y ⊆ nb2 j (blockSet (L := L) (N := N) j b) :=
    nbhd_mono (subset_nbhd_of_small hY hbY hne)
  have hpt : ∀ p ∈ nbhd j Y, NX ({p} : Set (Lam d L N)) ≤
      NX (nb2 j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) := fun p hp =>
    NX_mono (by simpa using hYn hp)
  refine ⟨?_, ?_, ?_, ?_, fun h => absurd trivial h, fun h => absurd trivial h⟩
  · exact NX_mono (coe_subset.2 (nbhd_subset_nb2 j _)) (Loc2E_mem_NB hd hb Y (bulk F))
  · show locAp c P.a Y (blockSet j b) (F : SA c (Lam d L N)).a ∈ _
    by_cases ha : P.a ∈ nbhd j Y
    · exact hpt _ ha (locAp_mem _ _ _ _)
    · rw [(hFa ha).1, locAp_zero]; exact zero_mem _
  · show locBp c P.b Y (blockSet j b) (F : SA c (Lam d L N)).b ∈ _
    by_cases hb' : P.b ∈ nbhd j Y
    · exact hpt _ hb' (locBp_mem _ _ _ _)
    · rw [(hFb hb').1, locBp_zero]; exact zero_mem _
  · show locABtXY P Y (blockSet j b) (F : SA c (Lam d L N)).ab ∈ _
    by_cases ha : P.a ∈ nbhd j Y
    · by_cases hb' : P.b ∈ nbhd j Y
      · refine NX_mono ?_ (locABtXY_mem P _ _ _)
        intro x hx
        rcases hx with rfl | rfl
        · exact mem_coe.2 (hYn ha)
        · exact mem_coe.2 (hYn hb')
      · rw [(hFb hb').2, locABtXY_zero]; exact zero_mem _
    · rw [(hFa ha).2, locABtXY_zero]; exact zero_mem _

end LocMem

/-! ### The locality hypothesis and the factorisation -/

/-- **Locality of the input of one step with sources.** All components of `V(B)`, `𝒲(B)` lie in
`𝒩(B^□)` and those of `K(Y)` in `𝒩(Y^□)`; for small `Y` the `σ_a` (`σ_b`) and `σ_aσ_b`
components of `K(Y)` vanish unless `a ∈ Y^□` (`b ∈ Y^□`). -/
structure OLocHyp (P : ObsPts d L N) (j : ℕ) (V W : OFam c d L N) (K : OAct c d L N) : Prop where
  hV : ∀ b, V b ∈ (compSub (NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)))
    True True : Subalgebra ℂ (OE c (Lam d L N)))
  hW : ∀ b, W b ∈ (compSub (NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)))
    True True : Subalgebra ℂ (OE c (Lam d L N)))
  hK : ∀ Y, IsConn j Y → K Y ∈ (compSub (NX (nbhd j Y : Set (Lam d L N))) True True :
    Subalgebra ℂ (OE c (Lam d L N)))
  hKa : ∀ Y, IsSmall j Y → P.a ∉ nbhd j Y →
    (K Y : SA c (Lam d L N)).a = 0 ∧ (K Y : SA c (Lam d L N)).ab = 0
  hKb : ∀ Y, IsSmall j Y → P.b ∉ nbhd j Y →
    (K Y : SA c (Lam d L N)).b = 0 ∧ (K Y : SA c (Lam d L N)).ab = 0

section Fact

variable {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N}

theorem J2O_mem (hd : 1 ≤ d) (H : OLocHyp P j V W K) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (Y : Finset (Lam d L N)) :
    J2O P j K b Y ∈ (compSub (NX (nb2 j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)))
      True True : Subalgebra ℂ (OE c (Lam d L N))) := by
  unfold J2O
  split_ifs with h1 h2
  · refine neg_mem (Subalgebra.sum_mem _ fun Y' hY' => ?_)
    obtain ⟨hs, hbY', -⟩ := mem_filter.1 hY'
    have hs' := mem_smallSets.1 hs
    exact LocO2_mem_nb2 P hd hb hs' hbY' (H.hKa Y' hs') (H.hKb Y' hs')
  · exact LocO2_mem_nb2 P hd hb h1.2.1 h1.2.2 (H.hKa Y h1.2.1) (H.hKb Y h1.2.1)
  · exact zero_mem _

/-- The support hypotheses of the generic factorisation for the map with sources, with the
supports `𝒩(U^{□□})`. -/
theorem suppHypW_O (hd : 1 ≤ d) (H : OLocHyp P j V W K) :
    SuppHypW (algO C) j (ingrO P j C V W K)
      (fun U => compSub (NX (nb2 j U : Set (Lam d L N))) True True)
      (fun U => compSub (NZ (nb2 j U : Set (Lam d L N))) True True) where
  hθ _ _ hf := thetaO_mem_cZ hf
  hι U f := inclO_mem_cZ _ f
  hK U Y hY hYU := compSub_mono (NX_mono (coe_subset.2 ((nbhd_mono hYU).trans
    (nbhd_subset_nb2 j U)))) id id (H.hK Y hY)
  hJ U b Y hb hbY hYU := compSub_mono (NX_mono (coe_subset.2 (nb2_mono (hbY.trans hYU))))
    id id (J2O_mem hd H hb Y)
  hI0 U b hbU := by
    have hV := compSub_mono (NX_mono (coe_subset.2 ((nbhd_mono hbU).trans
      (nbhd_subset_nb2 j U)))) id id (H.hV b)
    have hW := compSub_mono (NX_mono (coe_subset.2 ((nbhd_mono hbU).trans
      (nbhd_subset_nb2 j U)))) id id (H.hW b)
    exact mul_mem (oexp_mem (neg_mem hV)) (add_mem (one_mem _) hW)

theorem sepO (hL : 2 ^ (d + 3) ≤ L) (hj : j + 1 ≤ N) (hC : CovRange j C)
    (U₁ U₂ : Finset (Lam d L N)) (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (h : ¬ Touch U₁ U₂) :
    ∀ f ∈ (compSub (NZ (nb2 j U₁ : Set (Lam d L N))) True True :
        Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))),
      ∀ g ∈ (compSub (NZ (nb2 j U₂ : Set (Lam d L N))) True True :
        Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))),
      (algO C).E (f * g) = (algO C).E f * (algO C).E g :=
  fun _ hf _ hg => ECCO_mul_of_sepZ C
    (Set.disjoint_left.2 fun _ hx hx' => (C_zero_of_nb2 hL hj hC hU₁ hU₂ h hx hx').1 rfl)
    (fun _ hx _ hy => (C_zero_of_nb2 hL hj hC hU₁ hU₂ h hx hy).2) hf hg

/-- **Factorisation of `K_{j+1}` with sources**: `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)`. -/
theorem Knext2O_eq_KextO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j + 1 ≤ N)
    (hC : CovRange j C) (H : OLocHyp P j V W K) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) :
    Knext2O P j C V W K U = KextO (j + 1) (Knext2O P j C V W K) U := by
  have hL' : 2 ^ (d + 2) ≤ L := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hL
  have h := KnextG_eq_KextGW hd hL' hj (suppHypW_O (C := C) hd H) (ECCO_one C)
    (fun U₁ U₂ h1 h2 h3 => sepO hL hj hC U₁ U₂ h1 h2 h3) hU
  rw [Knext2O_eq_KnextG, h, KextG, KextO]
  exact prod_congr rfl fun Y _ => (Knext2O_eq_KnextG P j C V W K Y).symm

end Fact

end

end Obs2


/-!
# The change of variables with sources and the exact one-step identity (`sec:obs-flow`)

Copies of `Step2.Map.Reblock` (`reblock_ZVK`, `Kout_union`) and of the algebraic parts of
`Step2.Map.Split`/`Step2.Map.Reapp` (`bpow_It`, `Jh_sum`) on the algebra with sources; they only use the
ring axioms. Combined with `Obs2.ExactInst`:

* **`stepK_ZVKO`** (the analogue of `Step2.stepK_ZVK`):
  `𝔼_C θ Z_j = e^{-u_{j+1}(Λ)} Z_{j+1}`, `Z_{j+1} = ∑_{U ∈ 𝒫_{j+1}} Ĩ_{j+1}^{Λ∖U} K_{j+1}^U`,
  with `Ĩ_{j+1}(B_+) = ItO`, `K_{j+1} = KplusO`, on the algebra with sources; under `OLocHyp`
  (locality and point support of the input) and a covariance of range `L^{j+1}/2`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

section Gen

theorem KextO_empty (k : ℕ) (K : OAct c d L N) : KextO k K ∅ = 1 := by
  simp [KextO, comp_empty]

theorem KextO_union (k : ℕ) (K : OAct c d L N) {A B : Finset (Lam d L N)}
    (hA : IsPolymer k A) (hB : IsPolymer k B) (h : ¬ Touch A B) :
    KextO k K (A ∪ B) = KextO k K A * KextO k K B := by
  rw [KextO, comp_union hA hB h, prod_union (disjoint_comp hA h), KextO, KextO]

theorem bpowO_union (k : ℕ) (I : OFam c d L N) {A B : Finset (Lam d L N)}
    (hA : IsPolymer k A) (hB : IsPolymer k B) (h : Disjoint A B) :
    bpowO k I (A ∪ B) = bpowO k I A * bpowO k I B :=
  prod_blocks_union _ hA hB h

theorem bpowO_sdiff_mul (k : ℕ) (I : OFam c d L N) {A B : Finset (Lam d L N)}
    (hA : IsPolymer k A) (hB : IsPolymer k B) (hBA : B ⊆ A) :
    bpowO k I (univ \ A) * bpowO k I (A \ B) = bpowO k I (univ \ B) := by
  rw [← bpowO_union k I (IsPolymer.sdiff (isPolymer_univ k) hA) (IsPolymer.sdiff hA hB)
    (disjoint_sdiff_self_left.mono_right sdiff_subset)]
  congr 1
  ext x; simp only [mem_union, mem_sdiff, mem_univ, true_and]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact fun hB' => h (hBA hB')
    · exact h
  · intro h
    by_cases hx : x ∈ A
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl hx

theorem KextO_eq_of_union (k : ℕ) (F : OAct c d L N) (h0 : F ∅ = 1)
    (hmul : ∀ A B, IsPolymer k A → IsPolymer k B → ¬ Touch A B → F (A ∪ B) = F A * F B)
    {U : Finset (Lam d L N)} (hU : IsPolymer k U) : KextO k F U = F U :=
  (eq_prod_comp_of_mul F h0 hmul hU).symm

end Gen

/-! ### The identity (D.4) with sources -/

section Reblock

variable {k : ℕ} {I : OFam c d L N} {M : OAct c d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)}

/-- **The identity (D.4)** with sources. -/
theorem reblock_ZVKO (hJs : ∀ b c, ¬ IsSmall k c → J b c = 0) (Kin : OAct c d L N)
    (hKin : ∀ c, IsConn k c → Kin c = M c + ∑ b ∈ blocks k c, JbarO k I J b c) :
    ∑ U ∈ Pj k univ, bpowO k I (univ \ U) * KextO k Kin U =
      ∑ W ∈ Pj k univ, bpowO k I (univ \ W) * KoutO k I M J W := by
  classical
  have hU : ∀ U ∈ Pj (L := L) (N := N) k univ, KextO k Kin U =
      ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Xcal g.1 = U),
        KextO k M g.2 * ∏ p ∈ g.1, JbarO k I J p.1 p.2 := by
    intro U hU'
    have hUp := (mem_Pj.1 hU').2
    simp only [KextO]
    rw [← prod_comp_add_eq_sum_G0 k hUp M (fun p => JbarO k I J p.1 p.2)]
    refine prod_congr rfl fun c hc => ?_
    rw [hKin c (isConn_of_mem_comp hUp hc)]
    congr 1
    by_cases hs : IsSmall k c
    · rw [tSmall, if_pos hs]
    · rw [tSmall, if_neg hs, sum_empty]
      exact sum_eq_zero fun b _ => by rw [JbarO, hJs b c hs, mul_zero]
  have e1 : ∀ U ∈ Pj (L := L) (N := N) k univ, bpowO k I (univ \ U) * KextO k Kin U =
      ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Xcal g.1 = U),
        bpowO k I (univ \ (g.2 ∪ Xcal g.1)) *
          (KextO k M g.2 * ∏ p ∈ g.1, JbarO k I J p.1 p.2) := by
    intro U hU'
    rw [hU U hU', mul_sum]
    refine sum_congr rfl fun g hg => ?_
    rw [(mem_filter.1 hg).2]
  have e2 : ∀ W ∈ Pj (L := L) (N := N) k univ, bpowO k I (univ \ W) * KoutO k I M J W =
      ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W),
        bpowO k I (univ \ (g.2 ∪ Bbox k g.1)) * RtermO k I M J (g.2 ∪ Bbox k g.1) g := by
    intro W _
    rw [KoutO, mul_sum]
    refine sum_congr rfl fun g hg => ?_
    rw [(mem_filter.1 hg).2]
  have hmem : ∀ g ∈ G0 (d := d) (L := L) (N := N) k,
      g.2 ∪ Xcal g.1 ∈ Pj (L := L) (N := N) k univ ∧
      g.2 ∪ Bbox k g.1 ∈ Pj (L := L) (N := N) k univ := fun g hg => by
    obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 hg
    exact ⟨mem_Pj.2 ⟨subset_univ _, IsPolymer.union h1 (isPolymer_Xcal h2)⟩,
      mem_Pj.2 ⟨subset_univ _, IsPolymer.union h1 (isPolymer_Bbox k _)⟩⟩
  rw [sum_congr rfl e1, sum_congr rfl e2,
    sum_fiberwise_of_maps_to (fun g hg => (hmem g hg).1),
    sum_fiberwise_of_maps_to (fun g hg => (hmem g hg).2)]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 hg
  rw [RtermO, ← bpowO_sdiff_mul k I (IsPolymer.union h1 (isPolymer_Bbox k _))
    (IsPolymer.union h1 (isPolymer_Xcal h2))
    (union_subset_union subset_rfl (Xcal_subset_Bbox k h2))]
  ring

end Reblock

/-! ### Factorisation of `K_out` -/

section Fact

variable {k : ℕ} {W₁ W₂ : Finset (Lam d L N)} (hW₁ : IsPolymer k W₁) (hW₂ : IsPolymer k W₂)
  (h : ¬ Touch W₁ W₂)
include hW₁ hW₂ h

theorem RtermO_gjoin (I : OFam c d L N) (M : OAct c d L N)
    (J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)) {x : GT d L N × GT d L N}
    (h₁ : x.1 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁))
    (h₂ : x.2 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₂)) :
    RtermO k I M J (W₁ ∪ W₂) (gjoin x) = RtermO k I M J W₁ x.1 * RtermO k I M J W₂ x.2 := by
  obtain ⟨a1, a2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 h₁).1
  obtain ⟨b1, b2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 h₂).1
  obtain ⟨fa2, fa3, fa4⟩ := G0W_facts h₁
  obtain ⟨fb2, fb3, fb4⟩ := G0W_facts h₂
  have hD := disjoint_of_not_touch h
  have e1 : (W₁ ∪ W₂) \ (x.1.2 ∪ x.2.2 ∪ Xcal (x.1.1 ∪ x.2.1)) =
      (W₁ \ (x.1.2 ∪ Xcal x.1.1)) ∪ (W₂ \ (x.2.2 ∪ Xcal x.2.1)) := by
    rw [Xcal_union]
    ext z
    have i1 := @fa2 z
    have i2 := @fa3 z
    have i3 := @fb2 z
    have i4 := @fb3 z
    have i5 : z ∈ W₁ → z ∉ W₂ := fun hz => Finset.disjoint_left.1 hD hz
    simp only [mem_union, mem_sdiff]
    exact prop_aux i1 i2 i3 i4 i5
  have hI := bpowO_union k I (IsPolymer.sdiff hW₁ (IsPolymer.union a1 (isPolymer_Xcal a2)))
    (IsPolymer.sdiff hW₂ (IsPolymer.union b1 (isPolymer_Xcal b2)))
    (hD.mono sdiff_subset sdiff_subset)
  have hdisj : Disjoint x.1.1 x.2.1 := Finset.disjoint_left.2 fun p hp hq => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (a2 hp)
    exact Finset.disjoint_left.1 hD ((fa4 p hp).1 hz) ((fb4 p hq).1 hz)
  simp only [RtermO, gjoin]
  rw [e1, hI, KextO_union k M a1 b1 (not_touch_mono h fa2 fb2), prod_union hdisj]
  ring

/-- **Factorisation of `K_out`** with sources. -/
theorem KoutO_union (I : OFam c d L N) (M : OAct c d L N)
    (J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)) :
    KoutO k I M J (W₁ ∪ W₂) = KoutO k I M J W₁ * KoutO k I M J W₂ := by
  rw [KoutO, KoutO, KoutO, sum_mul_sum, ← sum_product']
  symm
  refine sum_nbij' gjoin (gsplit0 k W₁ W₂) (fun x hx => ?_) (fun g hg => ?_) (fun x hx => ?_)
    (fun g hg => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gjoin0_mem hW₁ hW₂ h h1 h2
  · exact mem_product.2 (gsplit0_mem hW₁ hW₂ h hg)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gsplit0_gjoin hW₁ hW₂ h h1 h2
  · exact gjoin_gsplit0 hg
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact (RtermO_gjoin hW₁ hW₂ h I M J h1 h2).symm

end Fact

theorem KoutO_empty (k : ℕ) (I : OFam c d L N) (M : OAct c d L N)
    (J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)) : KoutO k I M J ∅ = 1 := by
  classical
  have hF : (G0 (d := d) (L := L) (N := N) k).filter (fun g => g.2 ∪ Bbox k g.1 = ∅) =
      {(∅, ∅)} := by
    ext g
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hg, hgW⟩
      obtain ⟨-, h2, -, -, -⟩ := (mem_G0 k).1 hg
      have h2' := union_eq_empty.1 hgW
      refine Prod.ext ?_ h2'.1
      refine eq_empty_of_forall_notMem fun p hp => ?_
      obtain ⟨hb, -, -⟩ := mem_pairsU.1 (h2 hp)
      obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
      have : x ∈ Bbox k g.1 := mem_biUnion.2 ⟨p, hp,
        subset_nbhd (isPolymer_blockSet k p.1) hx⟩
      rw [h2'.2] at this; exact notMem_empty x this
    · rintro rfl
      refine ⟨(mem_G0 k).2 ⟨isPolymer_empty k, empty_subset _, by simp, by simp, ?_⟩, ?_⟩
      · rintro ⟨x, hx, -⟩; simp [Xcal] at hx
      · show ∅ ∪ Bbox k ∅ = ∅; simp [Bbox]
  rw [KoutO, hF, sum_singleton, RtermO]
  simp [Xcal, bpowO, blocks, KextO_empty]

/-! ### The split of `K^{(2)}` and `Ĩ_{j+1}` -/

section Split

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

theorem bpow_ItO {X : Finset (Lam d L N)} (hX : IsPolymer (j + 1) X) :
    bpowO (j + 1) (ItO P j C V W K) X = bpowO j (GpO P j C V W K) X := by
  unfold bpowO ItO bpowO
  exact (prod_blocks_succ hX _).symm

theorem sum_kapO (X : Finset (Lam d L N)) :
    ∑ c' ∈ blocks (j + 1) X, kapO j C V X c' = k2O j C V X := by
  classical
  unfold kapO k2O
  split_ifs with h1 h2
  · exact sum_fiberwise_of_maps_to (fun b hb => par_mem_blocks hb) _
  · rw [← smul_sum]
    congr 1
    rw [sum_fiberwise_of_maps_to (fun b hb => par_mem_blocks hb)]
    simp only [sum_add_distrib, sum_sum_GO_erase, add_zero]
  · exact sum_const_zero

theorem K2O_eq_zero {U : Finset (Lam d L N)} (hU : 2 < nb (j + 1) U) : K2O j C V U = 0 := by
  classical
  unfold K2O
  refine sum_eq_zero fun X hX => ?_
  have hcl := (mem_filter.1 hX).2
  have h3 : 2 < nb j X := by
    have := nb_clo_le (L := L) (N := N) j X
    rw [hcl] at this; omega
  unfold k2O
  rw [if_neg (by intro h; rw [h] at h3; omega), if_neg (by intro h; rw [h] at h3; omega)]

theorem JhO_of_not_small (c' : Fin d → ℕ) {U : Finset (Lam d L N)} (hU : ¬ IsSmall (j + 1) U) :
    JhO j C V c' U = 0 := by
  rw [JhO, if_neg hU]

theorem JhO_sum (hd : 1 ≤ d) {U : Finset (Lam d L N)} (hU : IsConn (j + 1) U) :
    ∑ c' ∈ blocks (j + 1) U, JhO j C V c' U = K2O j C V U := by
  classical
  by_cases hs : IsSmall (j + 1) U
  · simp only [JhO, if_pos hs]
    rw [sum_comm, K2O]
    refine sum_congr rfl fun X hX => ?_
    rw [← (mem_filter.1 hX).2, blocks_clo]
    exact sum_kapO j C V X
  · rw [sum_eq_zero fun c' _ => JhO_of_not_small j C V c' hs]
    have h2 : 2 < nb (j + 1) U := by
      by_contra h
      push Not at h
      exact hs ⟨hU.1, hU.2, h.trans (by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd)⟩
    exact (K2O_eq_zero j C V h2).symm

theorem hKinO (hd : 1 ≤ d) {c' : Finset (Lam d L N)} (hc : IsConn (j + 1) c') :
    Knext2O P j C V W K c' = KnewO P j C V W K c' +
      ∑ b ∈ blocks (j + 1) c', JbarO (j + 1) (ItO P j C V W K) (JhO j C V) b c' := by
  simp only [JbarO, bpow_ItO P j C V W K hc.1, ← mul_sum, JhO_sum j C V hd hc, KnewO]
  abel

end Split

/-! ### The exact one-step identity -/

section Step

variable {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N}

/-- **`𝔼_C θ Z_j = e^{-u_{j+1}(Λ)} Z_{j+1}` with sources** (the analogue of
`Step2.stepK_ZVK`): `Z_{j+1} = gZO (j+1) Ĩ_{j+1} K_{j+1}` with `K_{j+1} = KplusO` and the
extended `e^{-u_{j+1}(Λ)} = expU (-u^∅_{j+1}(Λ)) (-u^{obs}_{j+1}(Λ))`. Hypotheses: locality of
the input (`OLocHyp`, including the point support of the source components of small polymer
activities) and the range of the covariance. -/
theorem stepK_ZVKO (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : CovRange j C)
    (H : OLocHyp P j V W K) :
    ECCO C (thetaO (gZO j (IbO V W) K)) =
      expU (-uXB P j C V W K univ) (-uXO P j C V W K univ) *
        gZO (j + 1) (ItO P j C V W K) (KplusO P j C V W K) := by
  classical
  rw [stepO_ZVK]
  congr 1
  have hJs : ∀ b c', ¬ IsSmall (j + 1) c' → JhO j C V b c' = 0 :=
    fun b c' hc => JhO_of_not_small j C V b hc
  have h1 : ∀ U ∈ Pj (L := L) (N := N) (j + 1) univ,
      Knext2O P j C V W K U = KextO (j + 1) (Knext2O P j C V W K) U := fun U hU =>
    Knext2O_eq_KextO hd hL hjN.le hC H (mem_Pj.1 hU).2
  have h2 : ∀ U ∈ Pj (L := L) (N := N) (j + 1) univ,
      KextO (j + 1) (KplusO P j C V W K) U = KplusO P j C V W K U := fun U hU =>
    KextO_eq_of_union (j + 1) _ (KoutO_empty _ _ _ _)
      (fun A B hA hB h => KoutO_union hA hB h _ _ _) (mem_Pj.1 hU).2
  calc ∑ U ∈ Pj (j + 1) univ, bpowO j (GpO P j C V W K) (univ \ U) * Knext2O P j C V W K U
      = ∑ U ∈ Pj (j + 1) univ, bpowO (j + 1) (ItO P j C V W K) (univ \ U) *
          KextO (j + 1) (Knext2O P j C V W K) U := sum_congr rfl fun U hU => by
        rw [← h1 U hU, bpow_ItO P j C V W K (IsPolymer.sdiff (isPolymer_univ _)
          (mem_Pj.1 hU).2)]
    _ = ∑ U ∈ Pj (j + 1) univ, bpowO (j + 1) (ItO P j C V W K) (univ \ U) *
          KoutO (j + 1) (ItO P j C V W K) (KnewO P j C V W K) (JhO j C V) U :=
        reblock_ZVKO hJs _ fun c' hc => hKinO P j C V W K hd hc
    _ = _ := by
        rw [gZO]
        exact sum_congr rfl fun U hU => by rw [h2 U hU]; rfl

end Step

end

end Obs2
