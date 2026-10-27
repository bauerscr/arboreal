import Loc.BlockAut

/-!
# The image of the localisation (Proposition `prop:Loc` (v))

If `G = ∑_i Loc_{X_i,B} F_i` is invariant under the automorphisms of `Λ_N` fixing the block `B`,
and the `F_i` are invariant under the symplectic symmetry `ψ ↦ ψ̄, ψ̄ ↦ -ψ`, then
`G ∈ (ℂ ⊕ 𝒱^∅)(B)` (`Loc_image`).  All coefficients (`κ`, `C`, `SymCoef`) are complex.

The symplectic invariance is an additional hypothesis compared with the text: without it the
statement fails, since `∑_{x∈B} (ψ_x (Δψ̄)_x - (Δψ)_x ψ̄_x)` is `U(1)` and lattice invariant but
not in `(ℂ ⊕ 𝒱^∅)(B)`.  The `ℍ^{0|2}` model is invariant under this symmetry.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### Identification of the symmetric monomials with `𝒱^∅` -/

theorem prj_ez (i : Fin d) : (prj (ez i) : Lam d L N) = dirVec (Sum.inl i) := by
  rw [show ez i = dirZ (Sum.inl i) from rfl, prj_dirZ]

theorem prj_neg_ez (i : Fin d) : (prj (-ez i) : Lam d L N) = dirVec (Sum.inr i) := by
  rw [show -ez i = dirZ (Sum.inr i) from rfl, prj_dirZ]

theorem dirVec_inr_eq (i : Fin d) : (dirVec (Sum.inr i) : Lam d L N) = -dirVec (Sum.inl i) := rfl

theorem monoAt_c (x : Lam d L N) : monoAt Mono.c x = psi x * psibar x := by
  simp [monoAt, stencil, tens, id1, prj_zero]

theorem sum_monoAt_m2 (x : Lam d L N) : ∑ i : Fin d, monoAt (Mono.m2 i i) x = gradSq x := by
  rw [gradSq, Fintype.sum_sum_type, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [monoAt, stencil, if_true, sc, tens, fw, grad, gradbar, prj_ez, prj_neg_ez, prj_zero,
    add_zero, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.sum_cons, List.sum_nil]
  simp only [mul_sub, sub_mul, smul_add, smul_sub, mul_one, mul_neg, neg_neg]
  module

theorem lapPsi_eq (x : Lam d L N) :
    lapPsi x = ∑ i : Fin d, (psi (x + dirVec (Sum.inl i)) + psi (x - dirVec (Sum.inl i)) -
      (2 : ℂ) • psi x) := by
  rw [lapPsi, Fintype.sum_sum_type, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [grad, dirVec_inr_eq, sub_eq_add_neg]
  simp only [neg_neg, neg_add_cancel_right, add_neg_cancel_right]
  module

theorem lapPsibar_eq (x : Lam d L N) :
    lapPsibar x = ∑ i : Fin d, (psibar (x + dirVec (Sum.inl i)) +
      psibar (x - dirVec (Sum.inl i)) - (2 : ℂ) • psibar x) := by
  rw [lapPsibar, Fintype.sum_sum_type, ← sum_add_distrib, smul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [gradbar, dirVec_inr_eq, sub_eq_add_neg]
  simp only [neg_neg, neg_add_cancel_right, add_neg_cancel_right]
  module

theorem sum_monoAt_a2 (x : Lam d L N) :
    ∑ i : Fin d, monoAt (Mono.a2 s(i, i)) x = lapPsi x * psibar x := by
  rw [lapPsi_eq, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [monoAt, show stencil (Mono.a2 s(i, i)) = tens (lap1 i) id1 by simp [stencil, Dsym, Dik]]
  simp only [tens, lap1, id1, prj_ez, prj_neg_ez, prj_zero, dirVec_inr_eq, add_zero,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.sum_cons, List.sum_nil, mul_one, sub_eq_add_neg]
  simp only [add_mul, neg_mul, smul_mul_assoc]
  module

theorem sum_monoAt_b2 (x : Lam d L N) :
    ∑ i : Fin d, monoAt (Mono.b2 s(i, i)) x = psi x * lapPsibar x := by
  rw [lapPsibar_eq, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [monoAt, show stencil (Mono.b2 s(i, i)) = tens id1 (lap1 i) by simp [stencil, Dsym, Dik]]
  simp only [tens, lap1, id1, prj_ez, prj_neg_ez, prj_zero, dirVec_inr_eq, add_zero,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.append_nil, List.sum_cons, List.sum_nil, one_mul, sub_eq_add_neg]
  simp only [mul_add, mul_neg, mul_smul_comm]
  module

/-! ### Invariance of the coefficients -/

variable {B : Finset (Lam d L N)}

/-- The coefficients of an invariant local polynomial are invariant. -/
theorem coef_aut (hB : Patch B) (hne : B.Nonempty) (T : AffAut d L N) (hT : T.img B = B)
    (κ : ℂ) (C : Mono d → ℂ)
    (hinv : autAlg T.E (κ • 1 + ∑ M, C M • monoSet M B) = κ • 1 + ∑ M, C M • monoSet M B)
    (M : Mono d) : C (T.ρ.symm M) * T.sgn (T.ρ.symm M) = C M := by
  rw [map_add, map_smul, map_one, T.autAlg_sum_monoSet, hT] at hinv
  have := coef_unique hB hne (c := fun M => C (T.ρ.symm M) * T.sgn (T.ρ.symm M)) (c' := C)
    fun β => by
      have h := congrArg (mu (base B) β) hinv
      simpa only [mu_add, mu_smul, mu_one, mul_zero, zero_add] using h
  exact congrFun this M

/-- The coefficients of a `J`-invariant local polynomial are `swapM`-invariant. -/
theorem coef_Jsym (hB : Patch B) (hne : B.Nonempty) (κ : ℂ) (C : Mono d → ℂ)
    (hinv : Jsym (κ • 1 + ∑ M, C M • monoSet M B) = κ • 1 + ∑ M, C M • monoSet M B)
    (M : Mono d) : C (swapM M) = C M := by
  rw [map_add, map_smul, map_one, Jsym_sum_monoSet] at hinv
  have := coef_unique hB hne (c := fun M => C (swapM M)) (c' := C)
    fun β => by
      have h := congrArg (mu (base B) β) hinv
      simpa only [mu_add, mu_smul, mu_one, mul_zero, zero_add] using h
  exact congrFun this M

/-! ### Symmetric coefficients -/

/-- Sum over the monomials. -/
theorem sum_mono {β : Type*} [AddCommMonoid β] (f : Mono d → β) :
    ∑ M, f M = f .c + ∑ i, f (.a1 i) + ∑ i, f (.b1 i) + ∑ s, f (.a2 s) + ∑ s, f (.b2 s) +
      ∑ i, ∑ k, f (.m2 i k) := by
  rw [← Fintype.sum_equiv Mono.equiv.symm (fun a => f (Mono.equiv.symm a)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.univ_unit, sum_singleton]
  simp only [Mono.equiv, Equiv.coe_fn_symm_mk, add_assoc]

/-- A sum over `Sym2` of a function vanishing off the diagonal. -/
theorem sum_sym2_diag {β : Type*} [AddCommMonoid β] (f : Sym2 (Fin d) → β)
    (hf : ∀ s, ¬ s.IsDiag → f s = 0) : ∑ s, f s = ∑ i, f s(i, i) := by
  rw [← sum_subset (subset_univ (univ.image Sym2.diag)), sum_image]
  · rfl
  · intro a _ b _ h; exact Sym2.diag_injective h
  · intro s _ hs
    refine hf s fun hd => hs ?_
    induction s using Sym2.ind with
    | h i k =>
      rw [Sym2.mk_isDiag_iff] at hd; subst hd
      exact mem_image_of_mem _ (mem_univ _)

theorem cnt_self (i : Fin d) {k : Fin d} (h : k ≠ i) :
    cnt i (Mono.m2 i k) = 1 ∧ cnt i (Mono.a2 s(i, k)) = 1 ∧ cnt i (Mono.b2 s(i, k)) = 1 := by
  simp [cnt, h]

/-- The symmetry conditions on the coefficients. -/
structure SymCoef (C : Mono d → ℂ) : Prop where
  refl : ∀ i M, C M * (-1) ^ cnt i M = C M
  perm : ∀ (σ : Equiv.Perm (Fin d)) M, C (permMono σ M) = C M
  swap : ∀ M, C (swapM M) = C M

theorem SymCoef.odd {C : Mono d → ℂ} (h : SymCoef C) {i : Fin d} {M : Mono d}
    (hc : cnt i M = 1) : C M = 0 := by
  have := h.refl i M; rw [hc, pow_one] at this; linear_combination (-1 / 2 : ℂ) * this

theorem SymCoef.a2 {C : Mono d → ℂ} (h : SymCoef C) (i k : Fin d) :
    C (.a2 s(i, i)) = C (.a2 s(k, k)) := by
  have := h.perm (Equiv.swap k i) (.a2 s(k, k))
  simpa [permMono] using this

theorem SymCoef.b2 {C : Mono d → ℂ} (h : SymCoef C) (i k : Fin d) :
    C (.b2 s(i, i)) = C (.a2 s(k, k)) := by
  rw [← h.a2 i k, ← h.swap (.a2 _)]; rfl

theorem SymCoef.m2 {C : Mono d → ℂ} (h : SymCoef C) (i k : Fin d) :
    C (.m2 i i) = C (.m2 k k) := by
  have := h.perm (Equiv.swap k i) (.m2 k k)
  simpa [permMono] using this

/-- A local polynomial on `B` with symmetric coefficients is in `(ℂ ⊕ 𝒱^∅)(B)`. -/
theorem mem_VXspace_of_symCoef (hd : 1 ≤ d) (hne : B.Nonempty) (κ : ℂ) {C : Mono d → ℂ}
    (hC : SymCoef C) : κ • (1 : Alg d L N) + ∑ M, C M • monoSet M B ∈ VXspace B := by
  set i₀ : Fin d := ⟨0, hd⟩
  refine ⟨κ / B.card, ⟨-2 * C (.a2 s(i₀, i₀)), C (.m2 i₀ i₀), C .c, 0⟩, ?_⟩
  have hcard : (B.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  rw [div_mul_cancel₀ _ hcard, sum_mono]
  have h1 : ∑ i, C (.a1 i) • monoSet (.a1 i) B = 0 :=
    sum_eq_zero fun i _ => by rw [hC.odd (i := i) (by simp [cnt]), zero_smul]
  have h2 : ∑ i, C (.b1 i) • monoSet (.b1 i) B = 0 :=
    sum_eq_zero fun i _ => by rw [hC.odd (i := i) (by simp [cnt]), zero_smul]
  have h3 : ∑ s, C (.a2 s) • monoSet (.a2 s) B =
      ∑ i, C (.a2 s(i₀, i₀)) • monoSet (.a2 s(i, i)) B := by
    rw [sum_sym2_diag]
    · exact sum_congr rfl fun i _ => by rw [hC.a2 i i₀]
    · intro s hs
      induction s using Sym2.ind with
      | h i k =>
        have hik : k ≠ i := fun h => hs (by simp [h])
        rw [hC.odd (cnt_self i hik).2.1, zero_smul]
  have h4 : ∑ s, C (.b2 s) • monoSet (.b2 s) B =
      ∑ i, C (.a2 s(i₀, i₀)) • monoSet (.b2 s(i, i)) B := by
    rw [sum_sym2_diag]
    · exact sum_congr rfl fun i _ => by rw [hC.b2 i i₀]
    · intro s hs
      induction s using Sym2.ind with
      | h i k =>
        have hik : k ≠ i := fun h => hs (by simp [h])
        rw [hC.odd (cnt_self i hik).2.2, zero_smul]
  have h5 : ∑ i, ∑ k, C (.m2 i k) • monoSet (.m2 i k) B =
      ∑ i, C (.m2 i₀ i₀) • monoSet (.m2 i i) B := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i, hC.m2 i i₀]
    · intro k _ hik; rw [hC.odd (cnt_self i hik).1, zero_smul]
    · simp
  rw [h1, h2, h3, h4, h5, add_zero, add_zero]
  simp only [← smul_sum, monoSet]
  rw [sum_comm (s := univ) (t := B), sum_comm (s := univ) (t := B), sum_comm (s := univ) (t := B)]
  simp only [sum_monoAt_a2, sum_monoAt_b2, sum_monoAt_m2, monoAt_c, Vcoup.eval, sum_add_distrib,
    zero_smul, add_zero, ← smul_sum]
  simp only [neg_mul, mul_neg, sum_neg_distrib]
  module

/-! ### Blocks -/

/-- Blocks are patches (for `j < N`, `L ≥ 3`). -/
theorem patch_blockSet {j : ℕ} (hj : j < N) (hL : 3 ≤ L) (b : Fin d → ℕ) :
    Patch (blockSet (L := L) (N := N) j b) := by
  intro x hx
  have hb := base_mem ⟨x, hx⟩
  have h := supNorm_lt_of_blk_eq ((mem_blockSet.1 hx).trans (mem_blockSet.1 hb).symm)
  have h3 : 3 * L ^ j ≤ L ^ N :=
    calc 3 * L ^ j ≤ L * L ^ j := Nat.mul_le_mul_right _ hL
      _ = L ^ (j + 1) := by ring
      _ ≤ L ^ N := Nat.pow_le_pow_right (by omega) hj
  have : 0 < L ^ j := pow_pos (by omega) j
  omega

theorem reflCenter_ρ (j : ℕ) (b : Fin d → ℕ) (i : Fin d) (M : Mono d) :
    (reflCenter (L := L) (N := N) j b i).ρ.symm M = M := rfl

theorem reflCenter_sgn (j : ℕ) (b : Fin d → ℕ) (i : Fin d) (M : Mono d) :
    (reflCenter (L := L) (N := N) j b i).sgn M = (-1) ^ cnt i M := by
  simp [reflCenter, AffAut.comp, AffAut.refl, AffAut.transl]

theorem permCorner_ρ (j : ℕ) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (M : Mono d) :
    (permCorner (L := L) (N := N) j b σ).ρ.symm M = permMono σ.symm M := rfl

theorem permCorner_sgn (j : ℕ) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (M : Mono d) :
    (permCorner (L := L) (N := N) j b σ).sgn M = 1 := by
  simp [permCorner, AffAut.comp, AffAut.perm, AffAut.transl]

/-- Symmetric coefficients from invariance under the automorphisms fixing a block. -/
theorem symCoef_of_inv {j : ℕ} (hj : j ≤ N) {b : Fin d → ℕ}
    (hB : Patch (blockSet (L := L) (N := N) j b)) (hne : (blockSet (L := L) (N := N) j b).Nonempty)
    (κ : ℂ) (C : Mono d → ℂ)
    (hT : ∀ T : AffAut d L N, T.img (blockSet j b) = blockSet j b →
      autAlg T.E (κ • 1 + ∑ M, C M • monoSet M (blockSet j b)) =
        κ • 1 + ∑ M, C M • monoSet M (blockSet j b))
    (hJ : Jsym (κ • 1 + ∑ M, C M • monoSet M (blockSet (L := L) (N := N) j b)) =
        κ • 1 + ∑ M, C M • monoSet M (blockSet j b)) : SymCoef C where
  refl i M := by
    have := coef_aut hB hne _ (reflCenter_img hj b i) κ C (hT _ (reflCenter_img hj b i)) M
    rwa [reflCenter_ρ, reflCenter_sgn] at this
  perm σ M := by
    have := coef_aut hB hne _ (permCorner_img hj b σ.symm) κ C
      (hT _ (permCorner_img hj b σ.symm)) M
    rwa [permCorner_ρ, permCorner_sgn, mul_one, Equiv.symm_symm] at this
  swap M := coef_Jsym hB hne κ C hJ M

/-! ### Proposition `prop:Loc` (v) -/

/-- **Proposition `prop:Loc` (v).** Let `B` be a `j`-block (`j < N`, `L ≥ 3`, `d ≥ 1`), let
`X_i` be patches (e.g. small sets, see `Region.patch`) and let the `F_i` be invariant under the
symplectic symmetry `J`. If `G = ∑_i Loc_{X_i,B} F_i` is invariant under all automorphisms
of `Λ_N` mapping `B` to itself, then `G ∈ (ℂ ⊕ 𝒱^∅)(B)`. -/
theorem Loc_image (hd : 1 ≤ d) {j : ℕ} (hj : j < N) (hL : 3 ≤ L) {b : Fin d → ℕ}
    (hne : (blockSet (L := L) (N := N) j b).Nonempty) {ι : Type*} (s : Finset ι)
    (X : ι → Finset (Lam d L N)) (F : ι → Alg d L N) (hX : ∀ i ∈ s, Patch (X i))
    (hXne : ∀ i ∈ s, (X i).Nonempty) (hFJ : ∀ i ∈ s, Jsym (F i) = F i)
    (hT : ∀ T : AffAut d L N, T.img (blockSet j b) = blockSet j b →
      autAlg T.E (∑ i ∈ s, LocXY (X i) (blockSet j b) (F i)) =
        ∑ i ∈ s, LocXY (X i) (blockSet j b) (F i)) :
    ∑ i ∈ s, LocXY (X i) (blockSet j b) (F i) ∈ VXspace (blockSet (L := L) (N := N) j b) := by
  set B := blockSet (L := L) (N := N) j b
  have hG : ∑ i ∈ s, LocXY (X i) B (F i) =
      (∑ i ∈ s, ε (F i) * B.card / (X i).card) • (1 : Alg d L N) +
        ∑ M, (∑ i ∈ s, locCoef (X i) (F i) M) • monoSet M B := by
    simp only [LocXY, sum_add_distrib, sum_smul]
    rw [sum_comm]
  have hJ : Jsym (∑ i ∈ s, LocXY (X i) B (F i)) = ∑ i ∈ s, LocXY (X i) B (F i) := by
    rw [map_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [← LocXY_Jsym (hX i hi) (hXne i hi), hFJ i hi]
  rw [hG] at hT hJ ⊢
  exact mem_VXspace_of_symCoef hd hne _
    (symCoef_of_inv hj.le (patch_blockSet hj hL b) hne _ _ hT hJ)

end

end Loc
