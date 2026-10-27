import Step.StructureAux

/-!
# Proposition `prop:ZVK` (factorisation and symmetries) and Proposition `prop:consistency`

For `K ∈ 𝒦_j`, `L ≥ 2^{d+3}` and a covariance of range `≤ L^{j+1}/2` invariant under the
lattice automorphisms:

* `K_{j+1}` factorises over non-touching `(j+1)`-polymers (`Knext_union`), hence
  `K_{j+1}(U) = ∏_{Y ∈ Comp(U)} K_{j+1}(Y)` (`Knext_eq_Kext`);
* `K_{j+1} ∈ 𝒦_{j+1}` (`InK_Knext`);
* `𝔼_{C} θ Z_j = e^{-u_{j+1}|Λ|} Z_{j+1}` with `Z_{j+1}` given by `e:ZVK` at scale `j+1`
  (`ZVK'`);
* locality (`prop:consistency`, first part): `K_{j+1}(U)` and `V_{j+1}` depend on `K_j` only
  through `K_j(X)`, `X ∈ 𝒞_j`, `X ⊆ U^□` (`Knext_local`, `uVnext_local`).

The factorisation uses `L ≥ 2^{d+3}` (the text uses `L > 2^{d+2}`): the fields of the parts of
`K_{j+1}(U_1 ∪ U_2)` belonging to `U_1` and `U_2` are within `2^{d+1} L^j` of `U_1` resp. `U_2`,
and non-touching `(j+1)`-polymers are at distance `> L^{j+1}`, so the parts are at distance
`> L^{j+1} - 2^{d+2} L^j ≥ L^{j+1}/2`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- `X^□` at scale `j` is contained in `X^□` at scale `j + 1`. -/
theorem nbhd_subset_nbhd_succ {j : ℕ} (X : Finset (Lam d L N)) : nbhd j X ⊆ nbhd (j + 1) X := by
  intro y hy
  simp only [nbhd, mem_filter, mem_univ, true_and] at hy
  obtain ⟨S, hS, hyS, b, hb, hbS⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  exact subset_nbhd_succ_of_small hS (hbS (mem_blockSet_blk j x)) hx hyS

theorem Knext_empty (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N) :
    Knext j C V K ∅ = 1 :=
  Knext_empty' j C V K

/-- **Proposition `prop:ZVK`**, factorisation: `K_{j+1}(U_1 ∪ U_2) = K_{j+1}(U_1) K_{j+1}(U_2)`
for non-touching `(j+1)`-polymers. -/
theorem Knext_union (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N) {ℓ₀ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) (V : Vcoup) {K : Act d L N}
    (hK : InK j K) {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁)
    (hU₂ : IsPolymer (j + 1) U₂) (h : ¬ Touch U₁ U₂) :
    Knext j C V K (U₁ ∪ U₂) = Knext j C V K U₁ * Knext j C V K U₂ :=
  Knext_union' hd (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hL)
    (by omega : j + 1 ≤ N) hU₁ hU₂ h hC V hK

theorem Knext_eq_Kext (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N) {ℓ₀ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) (V : Vcoup) {K : Act d L N}
    (hK : InK j K) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    Knext j C V K U = Kext (j + 1) (Knext j C V K) U :=
  eq_prod_comp_of_mul (Knext j C V K) (Knext_empty j C V K)
    (fun _ _ hA hB hAB => Knext_union hd hL hj hC V hK hA hB hAB) hU

/-- **Proposition `prop:ZVK`**, locality and symmetries: `K_{j+1} ∈ 𝒦_{j+1}` (for `j + 1 < N`;
at the last scale `N` every automorphism preserves the single `N`-block, and automorphism
invariance of `K_N` does not follow from that of `K_{N-1}`). -/
theorem InK_Knext (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N) {ℓ₀ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) (V : Vcoup) {K : Act d L N}
    (hK : InK j K) : InK (j + 1) (Knext j C V K) where
  loc X hX := NX_mono (coe_subset.2 (nbhd_subset_nbhd_succ X))
    ((memHyp_loc (C := C) (V := V) (U := X) hd hK).Knext_mem hX.1 fun _ hF => EC_mem_NX C hF)
  sym X hX := (isSym_iff_mem_SymS _).2
    ((memHyp_sym (C := C) (V := V) (U := X) hK).Knext_mem hX.1 fun _ hF => EC_mem_SymS hF)
  jinv X hX := by
    have := (memHyp_jinv (C := C) (V := V) (U := X) hd hL hK).Knext_mem hX.1
      fun _ hF => EC_mem_equalizer hC.symm' hF
    exact ((AlgHom.mem_equalizer _ _ _).1 this).trans (AlgHom.id_apply _)
  aut T hT hP X _ := congrArg Subtype.val (AE_Knext hd hL hj hK hT hP hC.inv X)

/-- **Proposition `prop:ZVK`**: `𝔼_{C_{j+1}} θ Z_j = e^{-u_{j+1}|Λ|} Z_{j+1}`, where
`Z_{j+1} = ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)`. -/
theorem ZVK' (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N) {ℓ₀ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C) (V : Vcoup) {K : Act d L N}
    (hK : InK j K) :
    ECE C (thetaE (Zj j V K)) =
      Complex.exp (-((uVnext j C V K).1 * (univ : Finset (Lam d L N)).card)) •
        Zj (j + 1) (uVnext j C V K).2 (Knext j C V K) := by
  rw [ZVK C V K, Znext, Zj]
  congr 1
  refine sum_congr rfl fun U hU => ?_
  rw [Knext_eq_Kext hd hL hj hC V hK (mem_Pj.1 hU).2]

/-- **Proposition `prop:consistency`** (locality of `V_{j+1}`): `V_{j+1}` depends on `K_j` only
through the values on small sets containing one given block. -/
theorem uVnext_local (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V : Vcoup) {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hKK' : ∀ X, IsSmall j X → blockSet j b ⊆ X → K X = K' X) :
    uVnext j C V K = uVnext j C V K' :=
  uVnext_local' hd hL hj hC hCs hK hK' hb hKK'

/-- **Proposition `prop:consistency`** (locality of `K_{j+1}`): `K_{j+1}(U)` depends on `K_j`
only through `K_j(X)`, `X ∈ 𝒞_j`, `X ⊆ U^□`. -/
theorem Knext_local (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V : Vcoup) {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) (hUne : U.Nonempty)
    (hKK' : ∀ X, IsConn j X → X ⊆ nbhd (j + 1) U → K X = K' X) :
    Knext j C V K U = Knext j C V K' U :=
  Knext_local' hd hL hj hC hCs hK hK' hU hUne hKK'

end

end Step
