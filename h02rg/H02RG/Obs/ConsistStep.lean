import Obs.ConsistEmb

/-!
# Proposition `prop:consistency` for the observable map: one step

## Supports
`LSub T T'` are the even elements with bulk component in `T ⊓ T'` and observable components in
`T'`.  For a polymer `U`, `SL a b j U = LSub 𝒩(U^□) 𝒩(U^□ ∪ {a, b})` (on `Λ ⊔ Λ`: `SL2`).  The
split evaluations of the coupling constants at `a, b` (in Case (2) including the nonlocal term
`η ψ̄_aψ_b`, attached to the blocks of `a` and of `b`) lie in `SL a b j U` for every block
`B ⊆ U`, so the ingredients of `K_{j+1}` satisfy the support hypotheses of `Obs.Gen`
(`suppHyp_SL`) whenever `K_j` does (`ObsSupp`), without any condition on the coupling constants,
and `K_{j+1}` again satisfies them (`obsSupp_KnextO`).

## The step
`CompatO j R D K K'`: `embO K(X) = K'(emb X)` for connected `j`-polymers `X ⊆ {|x|_∞ ≤ R}` of
diameter `≤ D` (no translation invariance is available for the observable components, since
`a, b` are fixed; so compatibility is required in the region near the origin which contains
`a, b` and the relevant neighbourhoods).  For covariances agreeing near the origin
(`C'(emb x, emb y) = C(x, y)` if `|x| + |y| + |x - y| < L^N`, e.g. `Cfrd`, `Flow.Cfrd_emb_of`)
and `a, b` in the central region (`8|a|_∞ ≤ L^N`):

* `nextObs_consist`: the observable coupling constants agree;
* `KnextO_consist`: if moreover the bulk coupling constants agree (`Flow.uVnext_consist`), the
  next activities are compatible on a smaller region `R' = R - 2^d L^j`, `D' = D - 2^{d+1} L^j`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

/-! ### Supports -/

section LSub

variable {c : Case} {Λ : Type*} [DecidableEq Λ]

/-- Bulk component in `T ⊓ T'`, observable components in `T'`. -/
def LSub (T T' : Subalgebra ℂ (N Λ)) : Subalgebra ℂ (OE c Λ) where
  carrier := {F | (F : SA c Λ).e ∈ T ∧ (F : SA c Λ).e ∈ T' ∧ (F : SA c Λ).a ∈ T' ∧
    (F : SA c Λ).b ∈ T' ∧ (F : SA c Λ).ab ∈ T'}
  mul_mem' := by
    rintro F G ⟨h1, h1', h2, h3, h4⟩ ⟨g1, g1', g2, g3, g4⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [OE.mul_e]; exact mul_mem h1 g1
    · rw [OE.mul_e]; exact mul_mem h1' g1'
    · rw [OE.mul_a]; exact add_mem (mul_mem h1' g2) (mul_mem h2 g1')
    · rw [OE.mul_b]; exact add_mem (mul_mem h1' g3) (mul_mem h3 g1')
    · rw [OE.mul_ab]
      exact add_mem (add_mem (add_mem (mul_mem h1' g4) (Subalgebra.smul_mem _ (mul_mem h2 g3) _))
        (mul_mem h3 g2)) (mul_mem h4 g1')
  add_mem' := by
    rintro F G ⟨h1, h1', h2, h3, h4⟩ ⟨g1, g1', g2, g3, g4⟩
    exact ⟨add_mem h1 g1, add_mem h1' g1', add_mem h2 g2, add_mem h3 g3, add_mem h4 g4⟩
  algebraMap_mem' r := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (algebraMap ℂ (SA c Λ) r).e ∈ T; rw [SA.algebraMap_e]; exact T.algebraMap_mem r
    · show (algebraMap ℂ (SA c Λ) r).e ∈ T'; rw [SA.algebraMap_e]; exact T'.algebraMap_mem r
    · show (algebraMap ℂ (SA c Λ) r).a ∈ T'; rw [SA.algebraMap_a]; exact zero_mem _
    · show (algebraMap ℂ (SA c Λ) r).b ∈ T'; rw [SA.algebraMap_b]; exact zero_mem _
    · show (algebraMap ℂ (SA c Λ) r).ab ∈ T'; rw [SA.algebraMap_ab]; exact zero_mem _

theorem LSub_mono {T T' S S' : Subalgebra ℂ (N Λ)} (h : T ≤ S) (h' : T' ≤ S') :
    (LSub T T' : Subalgebra ℂ (OE c Λ)) ≤ LSub S S' := by
  rintro F ⟨h1, h1', h2, h3, h4⟩
  exact ⟨h h1, h' h1', h' h2, h' h3, h' h4⟩

theorem mem_LSub_of_comp {T T' : Subalgebra ℂ (N Λ)} (hT : T ≤ T') {F : OE c Λ}
    (he : (F : SA c Λ).e ∈ T) (ha : (F : SA c Λ).a ∈ T') (hb : (F : SA c Λ).b ∈ T')
    (hab : (F : SA c Λ).ab ∈ T') : F ∈ (LSub T T' : Subalgebra ℂ (OE c Λ)) :=
  ⟨he, hT he, ha, hb, hab⟩

end LSub

variable {d L : ℕ} [NeZero L]

section Supp

variable {N : ℕ} {c : Case}

/-- `U^□ ∪ {a, b}`. -/
def Rab (j : ℕ) (a b : Lam d L N) (U : Finset (Lam d L N)) : Set (Lam d L N) :=
  (nbhd j U : Set (Lam d L N)) ∪ {a, b}

/-- The supports `LSub 𝒩(U^□) 𝒩(U^□ ∪ {a, b})`. -/
def SL (a b : Lam d L N) (j : ℕ) (U : Finset (Lam d L N)) : Subalgebra ℂ (OE c (Lam d L N)) :=
  LSub (NX (nbhd j U : Set (Lam d L N))) (NX (Rab j a b U))

/-- The supports on the doubled algebra. -/
def SL2 (a b : Lam d L N) (j : ℕ) (U : Finset (Lam d L N)) :
    Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)) :=
  LSub (NX2 (nbhd j U : Set (Lam d L N))) (NX2 (Rab j a b U))

/-- The support hypothesis on the activities: `K(X) ∈ SL a b j X` for connected `X`. -/
def ObsSupp (a b : Lam d L N) (j : ℕ) (K : Finset (Lam d L N) → OE c (Lam d L N)) : Prop :=
  ∀ X, IsConn j X → K X ∈ (SL a b j X : Subalgebra ℂ (OE c (Lam d L N)))

theorem nbhd_sub_Rab (j : ℕ) (a b : Lam d L N) (U : Finset (Lam d L N)) :
    NX (nbhd j U : Set (Lam d L N)) ≤ NX (Rab j a b U) :=
  NX_mono Set.subset_union_left

theorem ab_sub_Rab (j : ℕ) (a b : Lam d L N) (U : Finset (Lam d L N)) :
    NX ({a, b} : Set (Lam d L N)) ≤ NX (Rab j a b U) :=
  NX_mono Set.subset_union_right

theorem Rab_mono {j j' : ℕ} (a b : Lam d L N) {U U' : Finset (Lam d L N)}
    (h : nbhd j U ⊆ nbhd j' U') : Rab j a b U ⊆ Rab j' a b U' :=
  Set.union_subset_union_left _ (coe_subset.2 h)

theorem SL_mono {j j' : ℕ} (a b : Lam d L N) {U U' : Finset (Lam d L N)}
    (h : nbhd j U ⊆ nbhd j' U') :
    (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) ≤ SL a b j' U' :=
  LSub_mono (NX_mono (coe_subset.2 h)) (NX_mono (Rab_mono a b h))

theorem mem_SL_of_Supp {P : Prop} {a b : Lam d L N} {j : ℕ} {U : Finset (Lam d L N)}
    {F : OE c (Lam d L N)} (hF : F ∈ Supp c P a b j U) : F ∈ (SL a b j U : Subalgebra ℂ _) := by
  obtain ⟨⟨h1, h2, h3, h4, -, -⟩, -⟩ := hF
  exact mem_LSub_of_comp (nbhd_sub_Rab j a b U) h1 (nbhd_sub_Rab j a b U h2)
    (nbhd_sub_Rab j a b U h3) (nbhd_sub_Rab j a b U h4)

theorem psi_mem_ab {a b x : Lam d L N} (hx : x = a ∨ x = b) (s : ℤˣ) :
    ψ (x, s) ∈ NX ({a, b} : Set (Lam d L N)) :=
  ψ_mem_NX (by rcases hx with rfl | rfl <;> simp)

theorem halfA_mem (W : Coup c) (a b : Lam d L N) :
    (halfA c W a b).e = 0 ∧ (halfA c W a b).a ∈ NX ({a, b} : Set (Lam d L N)) ∧
      (halfA c W a b).b ∈ NX ({a, b} : Set (Lam d L N)) ∧
      (halfA c W a b).ab ∈ NX ({a, b} : Set (Lam d L N)) := by
  have pa := psi_mem_ab (a := a) (b := b) (Or.inl rfl)
  have pb := psi_mem_ab (a := a) (b := b) (Or.inr rfl)
  cases c
  · refine ⟨rfl, Subalgebra.smul_mem _ (pa _) _, zero_mem _, ?_⟩
    exact add_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem (pa _) (pa _)) _)
  · refine ⟨rfl, sub_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem (pa _) (pa _)) _), zero_mem _, ?_⟩
    exact add_mem (sub_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _
      (add_mem (mul_mem (pa _) (pb _)) (mul_mem (pb _) (pa _))) _))
      (Subalgebra.smul_mem _ (mul_mem (pa _) (pa _)) _)

theorem halfB_mem (W : Coup c) (a b : Lam d L N) :
    (halfB c W a b).e = 0 ∧ (halfB c W a b).a ∈ NX ({a, b} : Set (Lam d L N)) ∧
      (halfB c W a b).b ∈ NX ({a, b} : Set (Lam d L N)) ∧
      (halfB c W a b).ab ∈ NX ({a, b} : Set (Lam d L N)) := by
  have pa := psi_mem_ab (a := a) (b := b) (Or.inl rfl)
  have pb := psi_mem_ab (a := a) (b := b) (Or.inr rfl)
  cases c
  · refine ⟨rfl, zero_mem _, Subalgebra.smul_mem _ (pb _) _, ?_⟩
    exact add_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem (pb _) (pb _)) _)
  · refine ⟨rfl, zero_mem _, sub_mem (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ (mul_mem (pb _) (pb _)) _), ?_⟩
    exact add_mem (sub_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _
      (add_mem (mul_mem (pa _) (pb _)) (mul_mem (pb _) (pa _))) _))
      (Subalgebra.smul_mem _ (mul_mem (pb _) (pb _)) _)

theorem splitO_mem_SL (W : Coup c) (a b : Lam d L N) (j : ℕ) (U X : Finset (Lam d L N)) :
    splitO c W a b X ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) := by
  have hA : halfAO c W a b ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) := by
    obtain ⟨h1, h2, h3, h4⟩ := halfA_mem W a b
    refine mem_LSub_of_comp (nbhd_sub_Rab j a b U) ?_ (ab_sub_Rab j a b U h2)
      (ab_sub_Rab j a b U h3) (ab_sub_Rab j a b U h4)
    show (halfA c W a b).e ∈ _
    rw [h1]; exact zero_mem _
  have hB : halfBO c W a b ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) := by
    obtain ⟨h1, h2, h3, h4⟩ := halfB_mem W a b
    refine mem_LSub_of_comp (nbhd_sub_Rab j a b U) ?_ (ab_sub_Rab j a b U h2)
      (ab_sub_Rab j a b U h3) (ab_sub_Rab j a b U h4)
    show (halfB c W a b).e ∈ _
    rw [h1]; exact zero_mem _
  exact add_mem (Subalgebra.smul_mem _ hA _) (Subalgebra.smul_mem _ hB _)

theorem VfullX_mem_SL (hd : 1 ≤ d) (Vb : Vcoup) (W : Coup c) (a b : Lam d L N) {j : ℕ}
    {U : Finset (Lam d L N)} {p : Fin d → ℕ} (hp : blockSet j p ⊆ U) :
    VfullX Vb W a b (blockSet j p) ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) := by
  refine add_mem ?_ (splitO_mem_SL _ a b j U _)
  have he : (Vb.eval (blockSet j p) : Alg d L N) ∈ NX (nbhd j U : Set (Lam d L N)) :=
    NX_mono (coe_subset.2 (nbhd_mono hp)) (eval_mem_NX hd (isPolymer_blockSet j p) Vb)
  refine mem_LSub_of_comp (nbhd_sub_Rab j a b U) ?_ ?_ ?_ ?_
  · simpa using he
  all_goals simp

theorem thetaO_mem_SL2 {a b : Lam d L N} {j : ℕ} {U : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : F ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N)))) :
    thetaO F ∈ (SL2 a b j U : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) := by
  obtain ⟨h1, h1', h2, h3, h4⟩ := hF
  exact ⟨theta_mem_NX2 h1, theta_mem_NX2 h1', theta_mem_NX2 h2, theta_mem_NX2 h3,
    theta_mem_NX2 h4⟩

theorem inclO_mem_SL2 {a b : Lam d L N} {j : ℕ} {U : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : F ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N)))) :
    inclO F ∈ (SL2 a b j U : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) := by
  obtain ⟨h1, h1', h2, h3, h4⟩ := hF
  exact ⟨incl_mem_NX2 h1, incl_mem_NX2 h1', incl_mem_NX2 h2, incl_mem_NX2 h3, incl_mem_NX2 h4⟩

theorem ECO_mem_SL (C : Matrix (Lam d L N) (Lam d L N) ℝ) {a b : Lam d L N} {j : ℕ}
    {U : Finset (Lam d L N)} {F : OE c (Lam d L N ⊕ Lam d L N)}
    (hF : F ∈ (SL2 a b j U : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)))) :
    ECO C F ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) := by
  obtain ⟨h1, h1', h2, h3, h4⟩ := hF
  exact ⟨EC_mem_NX C h1, EC_mem_NX C h1', EC_mem_NX C h2, EC_mem_NX C h3, EC_mem_NX C h4⟩

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup) (Vo : Coup c)
  (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)

theorem uObsX_mem_SL (U X : Finset (Lam d L N)) :
    uObsX j C Vo K a b X ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) :=
  splitO_mem_SL _ a b j U X

/-- **The support hypotheses** of `Obs.Gen` for the supports `SL`, without conditions on the
coupling constants. -/
theorem suppHyp_SL (hd : 1 ≤ d) (hK : ObsSupp a b j K) :
    SuppHyp (obsA c C) j (obsI j C Vb Vo K a b) (SL a b j) (SL2 a b j) where
  hθ _ _ hf := thetaO_mem_SL2 hf
  hι _ _ hf := inclO_mem_SL2 hf
  hK U Y hY hYU := SL_mono a b (nbhd_mono hYU) (hK Y hY)
  hJ U p Y hp hY := mem_SL_of_Supp (JO_mem_Supp (P := True) hd (fun h => absurd trivial h)
    (hp.trans hY) Y)
  hI0 U p hp := oexp_mem _ (neg_mem (VfullX_mem_SL hd Vb _ a b hp))
    (isNilpotent_VfullX a b Vb _ _).neg
  heV U p hp := oexp_mem _ (neg_mem (VfullX_mem_SL hd _ _ a b hp))
    (isNilpotent_VfullX a b _ _ _).neg
  heum U p _ := mul_mem (Subalgebra.algebraMap_mem _ _) (oexp_mem _
    (neg_mem (uObsX_mem_SL j C Vo K a b U _))
    (isNilpotent_of_obs (by rw [map_neg, bulk_uObsX, neg_zero])))

/-- `K_{j+1}` satisfies the support hypothesis. -/
theorem obsSupp_KnextO (hd : 1 ≤ d) (hK : ObsSupp a b j K) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) :
    KnextO j C Vb Vo K a b U ∈ (SL a b j U : Subalgebra ℂ (OE c (Lam d L N))) :=
  (suppHyp_SL j C Vb Vo K a b hd hK).KnextG_mem hU (fun _ hf => ECO_mem_SL C hf)
    (fun _ _ => mul_mem (Subalgebra.algebraMap_mem _ _) (oexp_mem _
      (uObsX_mem_SL j C Vo K a b U _) (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _))))

end Supp

/-! ### Compatibility -/

variable {N M : ℕ} {c : Case}

/-- `K` on `Λ_N` and `K'` on `Λ_M` agree on connected `j`-polymers in `{|x|_∞ ≤ R}` of
diameter `≤ D`. -/
def CompatO (j R D : ℕ) (K : Finset (Lam d L N) → OE c (Lam d L N))
    (K' : Finset (Lam d L M) → OE c (Lam d L M)) : Prop :=
  ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, supNorm x ≤ R) → Flow.diam X ≤ D →
    embO N M (K X) = K' (X.image (Flow.emb N M))

theorem supNorm_sub_le' {n : ℕ} [NeZero n] (x y : Torus d n) :
    supNorm (x - y) ≤ supNorm x + supNorm y := by
  have := supNorm_add_le x (-y)
  rwa [← sub_eq_add_neg, supNorm_neg] at this

section Step

variable (hNM : N ≤ M) (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 2 ≤ N)
include hNM hd hL hj

/-- The small sets containing `emb x` are the images of those containing `x`. -/
theorem smallAt_emb {x : Lam d L N} (hx : 4 * supNorm x ≤ L ^ N) :
    smallAt j (Flow.emb N M x) = (smallAt j x).image fun X => X.image (Flow.emb N M) := by
  obtain ⟨-, -, h3, -⟩ := Flow.num_facts hd hL hj
  have hUc : ∀ y ∈ ({x} : Finset (Lam d L N)), 4 * supNorm y ≤ L ^ N := fun y hy => by
    rw [mem_singleton.1 hy]; exact hx
  have hUd : ∀ y ∈ ({x} : Finset (Lam d L N)), ∀ z ∈ ({x} : Finset (Lam d L N)),
      8 * supNorm (y - z) ≤ L ^ N := fun y hy z hz => by
    rw [mem_singleton.1 hy, mem_singleton.1 hz, sub_self, supNorm_zero]; exact Nat.zero_le _
  have H := Flow.smallSets_image hNM hd hL hj hUc hUd (M := M) (mem_singleton_self x)
  rw [Flow.bemb_blk hNM (Flow.hPj hj) h3 (by omega)] at H
  ext Y'
  have H' := congrArg (Y' ∈ ·) H
  simp only [mem_filter, mem_image, eq_iff_iff] at H'
  simp only [smallAt, mem_filter, mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨Y, ⟨hY1, hY2⟩, rfl⟩ :=
      H'.1 ⟨h1, (mem_iff_blockSet_subset (mem_smallSets.1 h1).1 (mem_blockSet_blk j _)).2 h2⟩
    exact ⟨Y, ⟨hY1, (mem_iff_blockSet_subset (mem_smallSets.1 hY1).1 (mem_blockSet_blk j _)).1 hY2⟩, rfl⟩
  · rintro ⟨Y, ⟨hY1, hY2⟩, rfl⟩
    obtain ⟨h1, h2⟩ := H'.2
      ⟨Y, ⟨hY1, (mem_iff_blockSet_subset (mem_smallSets.1 hY1).1 (mem_blockSet_blk j _)).2 hY2⟩, rfl⟩
    exact ⟨h1, (mem_iff_blockSet_subset (mem_smallSets.1 h1).1 (mem_blockSet_blk j _)).1 h2⟩

theorem compat_smallAt {R D : ℕ} {K : Finset (Lam d L N) → OE c (Lam d L N)}
    {K' : Finset (Lam d L M) → OE c (Lam d L M)} (hc : CompatO j R D K K') {x : Lam d L N}
    (hR : supNorm x + 2 ^ d * L ^ j ≤ R) (hD : 2 ^ (d + 1) * L ^ j ≤ D) :
    ∀ X ∈ smallAt j x, K' (X.image (Flow.emb N M)) = embO N M (K X) := by
  intro X hX
  obtain ⟨hX1, hX2⟩ := mem_filter.1 hX
  have hXs := mem_smallSets.1 hX1
  have e2 : 2 ^ (d + 1) * L ^ j = 2 ^ d * L ^ j + 2 ^ d * L ^ j := by ring
  refine (hc X ⟨hXs.1, hXs.2.1⟩ (fun y hy => ?_) (Flow.diam_le fun y hy z hz => ?_)).symm
  · have h1 := supNorm_le_of_isSmall hXs hy hX2
    have h2 := supNorm_add_le (y - x) x
    rw [sub_add_cancel] at h2
    omega
  · have h1 := supNorm_le_of_isSmall hXs hy hX2
    have h2 := supNorm_le_of_isSmall hXs hX2 hz
    have h3 := supNorm_add_le (y - x) (x - z)
    rw [sub_add_sub_cancel] at h3
    omega

/-! #### The ingredients -/

section Ingr

variable {a b : Lam d L N} {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
  (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N)
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {K' : Finset (Lam d L M) → OE c (Lam d L M)}
  (hloc : ObsSupp a b j K)
  (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, Flow.InB U (2 ^ d * L ^ j) x) →
    embO N M (K X) = K' (X.image (Flow.emb N M)))
include hUc hUd hloc hKK

theorem E_LocO {Y : Finset (Lam d L N)} (hY : IsSmall j Y)
    (hYU : ∀ y ∈ Y, Flow.InB U (2 ^ d * L ^ j) y)
    {B : Finset (Lam d L N)} (hB : ∀ y ∈ B, 2 * supNorm y + 2 < L ^ N) :
    embO N M (LocO a b Y B (K Y)) = LocO (Flow.emb N M a) (Flow.emb N M b) (Y.image (Flow.emb N M))
      (B.image (Flow.emb N M)) (K' (Y.image (Flow.emb N M))) := by
  have hr1 : 2 ^ d * L ^ j + 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by
    calc 2 ^ d * L ^ j + 2 ^ d * L ^ j = 2 * (2 ^ d * L ^ j) := by ring
      _ ≤ 4 * (2 ^ d * L ^ j) := by omega
      _ = 2 ^ (d + 2) * L ^ j := by ring
  have hr0 : 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by omega
  have hRn : ∀ x ∈ (nbhd j Y : Set (Lam d L N)), ∀ y ∈ (nbhd j Y : Set (Lam d L N)),
      supNorm x + supNorm y + supNorm (x - y) < L ^ N := fun x hx y hy =>
    Flow.inB_near hd hL hj hUc hUd hr1 (Flow.InB.nbhd hYU (mem_coe.1 hx))
      (Flow.InB.nbhd hYU (mem_coe.1 hy))
  rw [← hKK Y ⟨hY.1, hY.2.1⟩ hYU]
  exact embO_LocO hNM a b Y B (K Y) (Flow.LocXY_emb hNM (region_small hd hL (by omega) hY) hRn
    hY.2.1.1 (fun y hy => Flow.inB_two hd hL hj hUc hUd hr0 (hYU y hy)) B hB _
    (hloc Y ⟨hY.1, hY.2.1⟩).1)

theorem E_JO {x₀ : Lam d L N} (hx₀ : x₀ ∈ U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    embO N M (JO a b j K (blk j x₀) X) = JO (Flow.emb N M a) (Flow.emb N M b) j K'
      (Flow.bemb L N M j (blk j x₀)) (X.image (Flow.emb N M)) := by
  obtain ⟨-, -, h3, -⟩ := Flow.num_facts hd hL hj
  have hB' := Flow.blockSet_bemb' hNM hd hL hj hUc hUd (M := M) hx₀
  have hX5 : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N := fun x hx =>
    Flow.pt5_of_mem hNM hd hL hj hUc hUd (hX hx)
  have hjM : j + 1 < M := by omega
  have hjN : j + 1 < N := by omega
  have c1 : (j + 1 < M ∧ IsSmall j (X.image (Flow.emb N M)) ∧
      blockSet j (Flow.bemb L N M j (blk j x₀)) ⊆ X.image (Flow.emb N M)) ↔
      (j + 1 < N ∧ IsSmall j X ∧ blockSet (L := L) (N := N) j (blk j x₀) ⊆ X) := by
    rw [hB', Flow.image_emb_subset_iff hNM, Flow.isSmall_image_iff hNM (Flow.hPj hj) h3 hX5]
    simp only [hjM, hjN, true_and]
  have c2 : X.image (Flow.emb N M) = blockSet j (Flow.bemb L N M j (blk j x₀)) ↔
      X = blockSet (L := L) (N := N) j (blk j x₀) := by
    rw [hB']; exact (Flow.image_emb_injective hNM).eq_iff
  have hBt := Flow.block_two hNM hd hL hj hUc hUd (M := M) hx₀
  unfold JO
  by_cases hc : j + 1 < N ∧ IsSmall j X ∧ blockSet (L := L) (N := N) j (blk j x₀) ⊆ X
  · rw [if_pos hc, if_pos (c1.2 hc)]
    by_cases hx : X = blockSet (L := L) (N := N) j (blk j x₀)
    · rw [if_pos hx, if_pos (c2.2 hx), map_neg, map_sum]
      refine congrArg Neg.neg ?_
      have hS : ((smallSets j).filter fun Y' : Finset (Lam d L M) =>
          blockSet j (Flow.bemb L N M j (blk j x₀)) ⊆ Y' ∧
            Y' ≠ blockSet j (Flow.bemb L N M j (blk j x₀))) =
          ((smallSets j).filter fun Y => blockSet (L := L) (N := N) j (blk j x₀) ⊆ Y ∧
            Y ≠ blockSet (L := L) (N := N) j (blk j x₀)).image fun Y => Y.image (Flow.emb N M) := by
        rw [← filter_filter, Flow.smallSets_image hNM hd hL hj hUc hUd hx₀, filter_image,
          ← filter_filter]
        refine congrArg _ (filter_congr fun Y _ => ?_)
        rw [hB']
        exact not_congr (Flow.image_emb_injective hNM).eq_iff
      rw [hS, sum_image fun Y _ Y' _ e => Flow.image_emb_injective hNM e]
      refine sum_congr rfl fun Y hY => ?_
      obtain ⟨hY1, hY2, -⟩ := mem_filter.1 hY
      have hYs := mem_smallSets.1 hY1
      have hYU : ∀ y ∈ Y, Flow.InB U (2 ^ d * L ^ j) y := fun y hy =>
        ⟨x₀, hx₀, supNorm_le_of_isSmall hYs hy (hY2 (mem_blockSet_blk j x₀))⟩
      rw [E_LocO hNM hd hL hj hUc hUd hloc hKK hYs hYU hBt, hB']
    · rw [if_neg hx, if_neg (mt c2.1 hx)]
      have hYU : ∀ y ∈ X, Flow.InB U (2 ^ d * L ^ j) y := fun y hy => Flow.inB_of_mem (hX hy) _
      rw [E_LocO hNM hd hL hj hUc hUd hloc hKK hc.2.1 hYU hBt, hB']
  · rw [if_neg hc, if_neg (mt c1.1 hc), map_zero]

end Ingr

variable {C : Matrix (Lam d L N) (Lam d L N) ℝ} {C' : Matrix (Lam d L M) (Lam d L M) ℝ}
  (hC : ∀ x y : Lam d L N, supNorm x + supNorm y + supNorm (x - y) < L ^ N →
    C' (Flow.emb N M x) (Flow.emb N M y) = C x y)
  {a b : Lam d L N} (ha : 8 * supNorm a ≤ L ^ N) (hb : 8 * supNorm b ≤ L ^ N)
include hC ha hb

theorem C_emb_ab {x y : Lam d L N} (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) :
    C' (Flow.emb N M x) (Flow.emb N M y) = C x y := by
  refine hC x y ?_
  have h1 := supNorm_sub_le' x y
  have hP : 0 < L ^ N := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) N
  have hx8 : 8 * supNorm x ≤ L ^ N := by rcases hx with rfl | rfl <;> assumption
  have hy8 : 8 * supNorm y ≤ L ^ N := by rcases hy with rfl | rfl <;> assumption
  omega

/-- **Proposition `prop:consistency`** (observable coupling constants): activities agreeing on
the small sets containing `a` or `b` give the same observable coupling constants. -/
theorem nextObs_consist (Vo : Coup c) {K : Finset (Lam d L N) → OE c (Lam d L N)}
    {K' : Finset (Lam d L M) → OE c (Lam d L M)}
    (hKa : ∀ X ∈ smallAt j a, K' (X.image (Flow.emb N M)) = embO N M (K X))
    (hKb : ∀ X ∈ smallAt j b, K' (X.image (Flow.emb N M)) = embO N M (K X)) :
    nextObs C' j Vo K' (Flow.emb N M a) (Flow.emb N M b) = nextObs C j Vo K a b := by
  have hjN : j + 1 < N := by omega
  have hjM : j + 1 < M := by omega
  unfold nextObs Wcoup
  rw [Qcoup_emb hNM hjN hjM (smallAt_emb hNM hd hL hj (by omega))
      (smallAt_emb hNM hd hL hj (by omega)) hKa hKb,
    C_emb_ab hNM hd hL hj hC ha hb (Or.inl rfl) (Or.inr rfl),
    C_emb_ab hNM hd hL hj hC ha hb (Or.inl rfl) (Or.inl rfl),
    C_emb_ab hNM hd hL hj hC ha hb (Or.inr rfl) (Or.inr rfl)]



/-! #### The step -/

theorem C_emb_Rab {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
    (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N) :
    ∀ x ∈ Rab j a b U, ∀ y ∈ Rab j a b U, C' (Flow.emb N M x) (Flow.emb N M y) = C x y := by
  have hr : 0 + 2 ^ d * L ^ j ≤ 2 ^ (d + 2) * L ^ j := by
    rw [zero_add]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hP : 0 < L ^ N := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) N
  have hin : ∀ {x : Lam d L N}, x ∈ nbhd j U → Flow.InB U (0 + 2 ^ d * L ^ j) x := fun hx =>
    Flow.InB.nbhd (fun z hz => Flow.inB_of_mem hz 0) hx
  have hpt : ∀ x ∈ Rab j a b U, 16 * supNorm x ≤ 5 * L ^ N ∧
      (x ∈ nbhd j U ∨ 8 * supNorm x ≤ L ^ N) := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨Flow.inB_pt hd hL hj hUc hUd hr (hin (mem_coe.1 hx)), Or.inl (mem_coe.1 hx)⟩
    · have h8 : 8 * supNorm x ≤ L ^ N := by
        rcases hx with rfl | hx
        · exact ha
        · rw [Set.mem_singleton_iff.1 hx]; exact hb
      exact ⟨by omega, Or.inr h8⟩
  intro x hx y hy
  refine hC x y ?_
  obtain ⟨hx1, hx2⟩ := hpt x hx
  obtain ⟨hy1, hy2⟩ := hpt y hy
  rcases hx2 with hx2 | hx2
  · rcases hy2 with hy2 | hy2
    · exact Flow.inB_near hd hL hj hUc hUd hr (hin hx2) (hin hy2)
    · have := supNorm_sub_le' x y; omega
  · have := supNorm_sub_le' x y; omega

variable {U : Finset (Lam d L N)} (hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N)
  (hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N)
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {K' : Finset (Lam d L M) → OE c (Lam d L M)}
  (hloc : ObsSupp a b j K)
  (hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, Flow.InB U (2 ^ d * L ^ j) x) →
    embO N M (K X) = K' (X.image (Flow.emb N M)))

include hUc hUd hloc hKK in
/-- The hypotheses of `Obs.Gen.E_KnextG` for the observable map. -/
theorem obs_embHyp (hU : IsPolymer (j + 1) U) (Vb : Vcoup) (Vo : Coup c)
    (huV : uVb j C' Vb K' = uVb j C Vb K)
    (hnext : nextObs C' j Vo K' (Flow.emb N M a) (Flow.emb N M b) = nextObs C j Vo K a b) :
    EmbHyp (obsA c C) (obsA c C') (embO N M) (embO2 N M) j U (obsI j C Vb Vo K a b)
      (obsI j C' Vb Vo K' (Flow.emb N M a) (Flow.emb N M b)) where
  hθ x := embO2_thetaO hNM x
  hι x := embO2_inclO hNM x
  hI0 x hx := by
    show embO N M (oexp (-VfullX Vb Vo a b (blockSet j (blk j x)))) =
      oexp (-VfullX Vb Vo (Flow.emb N M a) (Flow.emb N M b)
        (blockSet j (Flow.bemb L N M j (blk j x))))
    rw [embO_oexp (isNilpotent_VfullX a b Vb _ _).neg, map_neg,
      embO_VfullX hNM _ _ _ _ (Flow.block_two hNM hd hL hj hUc hUd hx),
      Flow.blockSet_bemb' hNM hd hL hj hUc hUd hx]
  heV x hx := by
    show embO N M (oexp (-VfullX (uVb j C Vb K).2 (nextObs C j Vo K a b) a b
        (blockSet j (blk j x)))) =
      oexp (-VfullX (uVb j C' Vb K').2 (nextObs C' j Vo K' (Flow.emb N M a) (Flow.emb N M b))
        (Flow.emb N M a) (Flow.emb N M b) (blockSet j (Flow.bemb L N M j (blk j x))))
    rw [huV, hnext, embO_oexp (isNilpotent_VfullX a b _ _ _).neg, map_neg,
      embO_VfullX hNM _ _ _ _ (Flow.block_two hNM hd hL hj hUc hUd hx),
      Flow.blockSet_bemb' hNM hd hL hj hUc hUd hx]
  heu x hx := by
    show embO N M (algebraMap ℂ _ (Complex.exp ((uVb j C Vb K).1 *
        (blockSet (L := L) (N := N) j (blk j x)).card)) *
          oexp (uObsX j C Vo K a b (blockSet j (blk j x)))) =
      algebraMap ℂ _ (Complex.exp ((uVb j C' Vb K').1 *
        (blockSet (L := L) (N := M) j (Flow.bemb L N M j (blk j x))).card)) *
          oexp (uObsX j C' Vo K' (Flow.emb N M a) (Flow.emb N M b)
            (blockSet j (Flow.bemb L N M j (blk j x))))
    rw [huV, map_mul, AlgHom.commutes, embO_oexp (isNilpotent_of_obs (bulk_uObsX j C Vo K a b _)),
      uObsX, uObsX, hnext, embO_splitO hNM, Flow.blockSet_bemb' hNM hd hL hj hUc hUd hx,
      Flow.card_image_emb hNM]
  heum x hx := by
    show embO N M (algebraMap ℂ _ (Complex.exp (-((uVb j C Vb K).1 *
        (blockSet (L := L) (N := N) j (blk j x)).card))) *
          oexp (-uObsX j C Vo K a b (blockSet j (blk j x)))) =
      algebraMap ℂ _ (Complex.exp (-((uVb j C' Vb K').1 *
        (blockSet (L := L) (N := M) j (Flow.bemb L N M j (blk j x))).card))) *
          oexp (-uObsX j C' Vo K' (Flow.emb N M a) (Flow.emb N M b)
            (blockSet j (Flow.bemb L N M j (blk j x))))
    rw [huV, map_mul, AlgHom.commutes,
      embO_oexp (isNilpotent_of_obs (by rw [map_neg, bulk_uObsX, neg_zero])), map_neg,
      uObsX, uObsX, hnext, embO_splitO hNM, Flow.blockSet_bemb' hNM hd hL hj hUc hUd hx,
      Flow.card_image_emb hNM]
  hJ x hx X hX := E_JO hNM hd hL hj hUc hUd hloc hKK hx hX
  hK X hX hXc := hKK X hXc fun y hy => Flow.inB_of_mem (hX hy) _
  hE g hg := by
    obtain ⟨f1, f2, -, f4⟩ := Gset_facts hg
    obtain ⟨-, h1, h2, h3, h4⟩ := (suppHyp_SL j C Vb Vo K a b hd hloc).inner_mem
      (IsPolymer.of_succ hU) f1 f2 fun p hp => ⟨(f4 p hp).1, (f4 p hp).2.2.2⟩
    exact embO_ECO hNM (C_emb_Rab hNM hd hL hj hC ha hb hUc hUd) h1 h2 h3 h4

omit hUc hUd

/-- **Proposition `prop:consistency`** (observable activities): for compatible activities (and
agreeing bulk coupling constants), the next activities are compatible on a smaller region. -/
theorem KnextO_consist (Vb : Vcoup) (Vo : Coup c) (hloc : ObsSupp a b j K)
    (huV : uVb j C' Vb K' = uVb j C Vb K) {R D R' D' : ℕ} (hc : CompatO j R D K K')
    (hR : 4 * R ≤ L ^ N) (hD : 8 * D ≤ L ^ N) (hR' : R' + 2 ^ d * L ^ j ≤ R)
    (hD' : D' + 2 ^ (d + 1) * L ^ j ≤ D) (hRa : supNorm a + 2 ^ d * L ^ j ≤ R)
    (hRb : supNorm b + 2 ^ d * L ^ j ≤ R) (hDab : 2 ^ (d + 1) * L ^ j ≤ D) :
    CompatO (j + 1) R' D' (KnextO j C Vb Vo K a b)
      (KnextO j C' Vb Vo K' (Flow.emb N M a) (Flow.emb N M b)) := by
  have hnext := nextObs_consist hNM hd hL hj hC ha hb Vo
    (compat_smallAt hNM hd hL hj hc hRa hDab) (compat_smallAt hNM hd hL hj hc hRb hDab)
  have e2 : 2 ^ (d + 1) * L ^ j = 2 ^ d * L ^ j + 2 ^ d * L ^ j := by ring
  intro U hU hUR hUD
  have hUc : ∀ x ∈ U, 4 * supNorm x ≤ L ^ N := fun x hx => by have := hUR x hx; omega
  have hUd : ∀ x ∈ U, ∀ y ∈ U, 8 * supNorm (x - y) ≤ L ^ N := fun x hx y hy => by
    have := Flow.le_diam hx hy; omega
  have hKK : ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, Flow.InB U (2 ^ d * L ^ j) x) →
      embO N M (K X) = K' (X.image (Flow.emb N M)) := by
    intro X hX hXU
    refine hc X hX (fun x hx => ?_) (Flow.diam_le fun x hx y hy => ?_)
    · obtain ⟨u, hu, h⟩ := hXU x hx
      have h1 := hUR u hu
      have h2 := supNorm_add_le (x - u) u
      rw [sub_add_cancel] at h2
      omega
    · obtain ⟨u, hu, hxu⟩ := hXU x hx
      obtain ⟨v, hv, hyv⟩ := hXU y hy
      have huv := Flow.le_diam hu hv
      have e : x - y = (x - u) + ((u - v) + (v - y)) := by abel
      have h6 := supNorm_add_le (x - u) ((u - v) + (v - y))
      have h7 := supNorm_add_le (u - v) (v - y)
      rw [supNorm_sub_comm v y] at h7
      rw [← e] at h6
      omega
  exact E_KnextG hNM hd hL hj hUc hUd
    (obs_embHyp hNM hd hL hj hC ha hb hUc hUd hloc hKK hU.1 Vb Vo huV hnext)

end Step

end

end Obs
