import Step2.Coup.CoupPast6

/-!
# The bubble coefficient: only double contractions (`h02uv-outline.tex`, `prop:C4b`)

For homogeneous quartic `A`, `B`, the quartic pairing of `F_C(A, B)` only sees the part with
exactly two cross contractions (`mu4_FC_quartic`):
`μ₄ F_C(A, B) = μ₄ c₂(A, B)`, with
`c₂ = ½𝓛²(AB) - 𝓛(𝓛A·B) - 𝓛(A·𝓛B) + ½𝓛²A·B + 𝓛A·𝓛B + ½A·𝓛²B`. By the Leibniz rules,
`c₂ = ½ X₂(A, B)` (`c2_eq_X2`), where `X₂` is the double cross contraction
`X₂(A,B) = ∑_{x,y} C_{xy} [X_C(∂_{x-}A, ∂_{y+}B) - X_C(∂_{y+}A, ∂_{x-}B)]`.

So `-𝔅(C) = q_{j,j}(e_g)_g = μ₄ X₂(V_g(B_+), V_g(Λ)) / (4|B_+|)` (`bubble_eq`): the bubble
coefficient is the quadratic form of the double contraction, with no tadpoles.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section General

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- `F` is homogeneous of degree `n`. -/
def IsHom (n : ℕ) (F : N I) : Prop := ∀ m (z : Fin m → Sf I), m ≠ n → coeff F z = 0

theorem isHom_zero (n : ℕ) : IsHom n (0 : N I) := fun m z _ => by simp

theorem IsHom.add {n : ℕ} {F G : N I} (hF : IsHom n F) (hG : IsHom n G) : IsHom n (F + G) :=
  fun m z h => by rw [coeff_add, hF m z h, hG m z h, add_zero]

theorem IsHom.smul {n : ℕ} {F : N I} (hF : IsHom n F) (c : ℂ) : IsHom n (c • F) :=
  fun m z h => by rw [coeff_smul, hF m z h, mul_zero]

theorem IsHom.neg {n : ℕ} {F : N I} (hF : IsHom n F) : IsHom n (-F) := by
  simpa using hF.smul (-1)

theorem IsHom.sub {n : ℕ} {F G : N I} (hF : IsHom n F) (hG : IsHom n G) : IsHom n (F - G) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem IsHom.sum {n : ℕ} {ι : Type*} (s : Finset ι) {F : ι → N I} (hF : ∀ i ∈ s, IsHom n (F i)) :
    IsHom n (∑ i ∈ s, F i) := fun m z h => by
  rw [coeff_sum]; exact sum_eq_zero fun i hi => hF i hi m z h

theorem isHom_psiPow {m : ℕ} (z : Fin m → Sf I) : IsHom m (psiPow z) :=
  fun _ w h => coeff_ιMulti_of_ne _ w h

theorem IsHom.mul {n n' : ℕ} {x y : N I} (hx : IsHom n x) (hy : IsHom n' y) :
    IsHom (n + n') (x * y) := by
  rw [sum_coeff x, sum_coeff y, sum_mul]
  refine IsHom.sum _ fun m _ => ?_
  rw [sum_mul]
  refine IsHom.sum _ fun z _ => ?_
  rw [mul_sum]
  refine IsHom.sum _ fun m' _ => ?_
  rw [mul_sum]
  refine IsHom.sum _ fun w _ => ?_
  rw [smul_mul_smul_comm, psiPow_mul_psiPow]
  by_cases hm : m = n
  · by_cases hm' : m' = n'
    · subst hm hm'; exact (isHom_psiPow _).smul _
    · rw [hy m' w hm', mul_zero, mul_zero, zero_smul]; exact isHom_zero _
  · rw [hx m z hm, mul_zero, zero_mul, zero_smul]; exact isHom_zero _

theorem IsHom.D {n : ℕ} {x : N I} (hx : IsHom n x) (a : Sf I) : IsHom (n - 1) (Grassmann.D a x) :=
  fun m z h => by
    rw [coeff_D]
    exact hx (m + 1) _ (by omega)

/-- On a degree-`0` element, `D` vanishes. -/
theorem IsHom.D_zero {x : N I} (hx : IsHom 0 x) (a : Sf I) : Grassmann.D a x = 0 :=
  ext_coeff fun m z => by rw [coeff_D, hx (m + 1) _ (by omega)]; simp

variable (C : Matrix I I ℂ)

theorem IsHom.lop {n : ℕ} {F : N I} (hF : IsHom n F) : IsHom (n - 2) (LopC C F) := by
  rw [LopC_apply]
  refine IsHom.sum _ fun x _ => IsHom.sum _ fun y _ => IsHom.smul ?_ _
  have := (hF.D (x, -1)).D (y, 1)
  rwa [show n - 1 - 1 = n - 2 by omega] at this

theorem IsHom.lopPow {n : ℕ} {F : N I} (hF : IsHom n F) :
    ∀ j, IsHom (n - 2 * j) ((LopC C ^ j) F)
  | 0 => by simpa using hF
  | j + 1 => by
    rw [pow_succ', Module.End.mul_apply]
    have := (hF.lopPow j).lop C
    rwa [show n - 2 * j - 2 = n - 2 * (j + 1) by omega] at this

end General

section General2

variable {I : Type*} [DecidableEq I] [Fintype I] (C : Matrix I I ℂ)

/-- `e^{𝓛_C} F = ∑_{i ≤ |I_f|} 𝓛^i F / i!`. -/
theorem expLC_eq_sum' (F : N I) :
    expLC C F = ∑ i ∈ range (Nf I + 1), ((i.factorial : ℂ)⁻¹) • (LopC C ^ i) F := by
  rw [expLC, IsNilpotent.exp_eq_sum (LopC_pow_eq_zero C), LinearMap.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ]
  simp

end General2

section Leibniz

variable {I : Type*} [DecidableEq I] [Fintype I] (C : Matrix I I ℂ)

/-- `𝓛_C` commutes with derivatives. -/
theorem LopC_D (a : Sf I) (F : N I) : LopC C (Grassmann.D a F) = Grassmann.D a (LopC C F) := by
  simp only [LopC_apply, map_sum, map_smul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [D_comm a (y, 1), D_comm a (x, -1), map_neg, neg_neg]

/-- **Leibniz rule for odd `P`**: `𝓛(PQ) = 𝓛P·Q + P·𝓛Q - X(P, Q)`. -/
theorem LopC_mul_odd {P : N I} (hP : inv' P = -P) (Q : N I) :
    LopC C (P * Q) = LopC C P * Q + P * LopC C Q - Xc C P Q := by
  simp only [LopC_apply, Xc, sum_mul, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [D_mul, map_add, D_mul, D_mul]
  have hD : inv' (Grassmann.D (x, -1) P) = Grassmann.D (x, -1) P := by
    have h := Grassmann.D_inv' (x, -1) P
    rw [hP, map_neg] at h
    exact (neg_inj.1 h).symm
  simp only [hP, hD, map_neg, neg_mul]
  simp only [smul_add, smul_sub, smul_neg, add_sub_assoc, smul_mul_assoc, mul_smul_comm]
  abel

/-- The double cross contraction. -/
def X2 (A B : N I) : N I :=
  ∑ x, ∑ y, C x y • (Xc C (Grassmann.D (x, -1) A) (Grassmann.D (y, 1) B) -
    Xc C (Grassmann.D (y, 1) A) (Grassmann.D (x, -1) B))

theorem inv'_LopC {A : N I} (hA : inv' A = A) : inv' (LopC C A) = LopC C A := by
  rw [← LopC_inv', hA]

/-- `𝓛X(A, B) - X(𝓛A, B) - X(A, 𝓛B) = X₂(A, B)` for even `A`. -/
theorem LopC_Xc {A : N I} (hA : inv' A = A) (B : N I) :
    LopC C (Xc C A B) - Xc C (LopC C A) B - Xc C A (LopC C B) = X2 C A B := by
  have hodd : ∀ a, inv' (Grassmann.D a A) = -Grassmann.D a A := fun a => inv'_D_of_even hA a
  simp only [Xc, X2, map_sum, map_smul, map_sub]
  simp only [LopC_mul_odd C (hodd _), LopC_D]
  simp only [← sum_sub_distrib, ← smul_sub]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1
  simp only [Xc, one_smul, smul_sub, smul_add, sum_sub_distrib, sum_add_distrib,
    sum_neg_distrib]
  abel

end Leibniz

variable {d L N : ℕ} [NeZero L]

theorem mu4_of_isHom {n : ℕ} {F : Alg d L N} (hF : IsHom n F) (hn : n ≠ 4) (b : Lam d L N)
    (κ κ' : Fin d) : mu4 b κ κ' F = 0 := by
  unfold mu4 cf4
  exact sum_eq_zero fun x _ => by rw [hF 4 _ (Ne.symm hn), zero_mul]

theorem mu4_lopPow_hom (C : Matrix (Lam d L N) (Lam d L N) ℂ) {n : ℕ} {F : Alg d L N}
    (hF : IsHom n F) (j : ℕ) (hj : n - 2 * j ≠ 4) (b : Lam d L N) (κ κ' : Fin d) :
    mu4 b κ κ' ((LopC C ^ j) F) = 0 :=
  mu4_of_isHom (hF.lopPow C j) hj b κ κ'

/-- `μ₄ e^{𝓛} F = μ₄ 𝓛^i F / i!` for `F` homogeneous of degree `4 + 2i`. -/
theorem mu4_expLC_hom (C : Matrix (Lam d L N) (Lam d L N) ℂ) {i : ℕ} {F : Alg d L N}
    (hF : IsHom (4 + 2 * i) F) (hi : i < Nf (Lam d L N) + 1) (b : Lam d L N) (κ κ' : Fin d) :
    mu4 b κ κ' (expLC C F) = (i.factorial : ℂ)⁻¹ * mu4 b κ κ' ((LopC C ^ i) F) := by
  rw [expLC_eq_sum', mu4_sum]
  rw [sum_eq_single i (fun j _ hj => by
      rw [mu4_smul, mu4_lopPow_hom C hF j (by omega) b κ κ', mul_zero])
    (fun h => absurd (mem_range.2 hi) h), mu4_smul]

/-- `μ₄ e^{𝓛} F = 0` for `F` homogeneous of degree `n` with `n ∉ 4 + 2ℕ`. -/
theorem mu4_expLC_hom_zero (C : Matrix (Lam d L N) (Lam d L N) ℂ) {n : ℕ} {F : Alg d L N}
    (hF : IsHom n F) (hn : ∀ i, n ≠ 4 + 2 * i) (b : Lam d L N) (κ κ' : Fin d) :
    mu4 b κ κ' (expLC C F) = 0 := by
  rw [expLC_eq_sum', mu4_sum]
  refine sum_eq_zero fun j _ => ?_
  rw [mu4_smul]
  by_cases h : n < 2 * j
  · rw [mu4_lopPow_hom C hF j (by omega) b κ κ', mul_zero]
  · rw [mu4_lopPow_hom C hF j (fun h' => hn j (by omega)) b κ κ', mul_zero]

/-- The double-contraction part `c₂(A, B)` of `F_C(A, B)`. -/
def c2 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (A B : Alg d L N) : Alg d L N :=
  (1 / 2 : ℂ) • LopC C (LopC C (A * B)) - LopC C (LopC C A * B) - LopC C (A * LopC C B) +
    (1 / 2 : ℂ) • (LopC C (LopC C A) * B) + LopC C A * LopC C B + (1 / 2 : ℂ) • (A * LopC C (LopC C B))

theorem two_le_Nf : 2 ≤ Nf (Lam d L N) := by
  unfold Nf
  rw [Fintype.card_prod]
  have h1 : 1 ≤ Fintype.card (Lam d L N) := Fintype.card_pos
  have h2 : Fintype.card ℤˣ = 2 := by decide
  rw [h2]; omega

/-- **Only double contractions contribute to the quartic content of `F_C(A, B)`.** -/
theorem mu4_FC_quartic (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : Alg d L N}
    (hA : IsHom 4 A) (hB : IsHom 4 B) (b : Lam d L N) (κ κ' : Fin d) :
    mu4 b κ κ' (FC C A B) = mu4 b κ κ' (c2 C A B) := by
  -- `e^{-𝓛} A = A - 𝓛A + ½𝓛²A`
  have hcube : ∀ {F : Alg d L N}, IsHom 4 F → ∀ C' : Matrix (Lam d L N) (Lam d L N) ℂ,
      LopC C' (LopC C' (LopC C' F)) = 0 := by
    intro F hF C'
    have h0 : IsHom 0 (LopC C' (LopC C' F)) := by
      have := (hF.lop C').lop C'
      simpa using this
    rw [LopC_apply]
    exact sum_eq_zero fun x _ => sum_eq_zero fun y _ => by
      rw [h0.D_zero, map_zero, smul_zero]
  have eA : expLC (-C) A = A - LopC C A + (1 / 2 : ℂ) • LopC C (LopC C A) := by
    rw [expLC_of_cube (-C) (hcube hA (-C)), LopC_neg]; simp [sub_eq_add_neg]
  have eB : expLC (-C) B = B - LopC C B + (1 / 2 : ℂ) • LopC C (LopC C B) := by
    rw [expLC_of_cube (-C) (hcube hB (-C)), LopC_neg]; simp [sub_eq_add_neg]
  -- homogeneous pieces
  have hLA : IsHom 2 (LopC C A) := hA.lop C
  have hLB : IsHom 2 (LopC C B) := hB.lop C
  have hLLA : IsHom 0 (LopC C (LopC C A)) := hLA.lop C
  have hLLB : IsHom 0 (LopC C (LopC C B)) := hLB.lop C
  have hm : ∀ {k n n' : ℕ} {x y : Alg d L N}, IsHom n x → IsHom n' y → n + n' = k →
      IsHom k (x * y) := fun hx hy h => h ▸ hx.mul hy
  have h8 : IsHom (4 + 2 * 2) (A * B) := hm hA hB rfl
  have h6 : IsHom (4 + 2 * 1) (-(LopC C A * B + A * LopC C B)) :=
    ((hm hLA hB rfl).add (hm hA hLB rfl)).neg
  have h4 : IsHom (4 + 2 * 0) ((1 / 2 : ℂ) • (LopC C (LopC C A) * B) + LopC C A * LopC C B +
      (1 / 2 : ℂ) • (A * LopC C (LopC C B))) :=
    (((hm hLLA hB rfl).smul _).add (hm hLA hLB rfl)).add ((hm hA hLLB rfl).smul _)
  have h2 : IsHom 2 (-((1 / 2 : ℂ) • (LopC C (LopC C A) * LopC C B) +
      (1 / 2 : ℂ) • (LopC C A * LopC C (LopC C B)))) :=
    (((hm hLLA hLB rfl).smul _).add ((hm hLA hLLB rfl).smul _)).neg
  have h0 : IsHom 0 ((1 / 4 : ℂ) • (LopC C (LopC C A) * LopC C (LopC C B))) :=
    (hm hLLA hLLB rfl).smul _
  have hP : expLC (-C) A * expLC (-C) B = A * B + -(LopC C A * B + A * LopC C B) +
      ((1 / 2 : ℂ) • (LopC C (LopC C A) * B) + LopC C A * LopC C B +
        (1 / 2 : ℂ) • (A * LopC C (LopC C B))) +
      -((1 / 2 : ℂ) • (LopC C (LopC C A) * LopC C B) +
        (1 / 2 : ℂ) • (LopC C A * LopC C (LopC C B))) +
      (1 / 4 : ℂ) • (LopC C (LopC C A) * LopC C (LopC C B)) := by
    rw [eA, eB]
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    module
  have hN := two_le_Nf (d := d) (L := L) (N := N)
  rw [FC, hP, map_add, map_add, map_add, map_add, mu4_sub, mu4_add, mu4_add, mu4_add, mu4_add,
    mu4_expLC_hom C h8 (by omega), mu4_expLC_hom C h6 (by omega), mu4_expLC_hom C h4 (by omega),
    mu4_expLC_hom_zero C h2 (by omega), mu4_expLC_hom_zero C h0 (by omega),
    mu4_of_isHom (hm hA hB rfl) (by norm_num : 4 + 4 ≠ 4)]
  simp only [c2, mu4_add, mu4_sub, mu4_smul, pow_succ, pow_zero, one_mul,
    Module.End.mul_apply, Module.End.one_apply, map_neg, map_add]
  have hneg : ∀ F : Alg d L N, mu4 b κ κ' (-F) = -mu4 b κ κ' F := fun F => by
    have := mu4_smul b κ κ' (-1) F; simpa using this
  simp only [hneg, mu4_add, mu4_smul]
  norm_num
  ring

/-- **`c₂ = ½ X₂`** for even `A`. -/
theorem c2_eq_X2 (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A : Alg d L N} (hA : inv' A = A)
    (B : Alg d L N) : c2 C A B = (1 / 2 : ℂ) • X2 C A B := by
  have h1 := LopC_mul_even C hA B
  have h2 := LopC_mul_even C (inv'_LopC C hA) B
  have h3 := LopC_mul_even C hA (LopC C B)
  have h4 : LopC C (LopC C (A * B)) =
      LopC C (LopC C A * B) + LopC C (A * LopC C B) + LopC C (Xc C A B) := by
    rw [h1, map_add, map_add]
  rw [c2, ← LopC_Xc C hA B, h4, h2, h3]
  module

theorem isHom_gmono4 (e e' : Dir d) (x : Lam d L N) : IsHom 4 (gmono4 e e' x) :=
  fun _ z h => coeff_ιMulti_of_ne _ z h

theorem isHom_mono4s (i k : Fin d) (x : Lam d L N) : IsHom 4 (mono4s i k x) := by
  unfold mono4s
  split_ifs
  · exact ((isHom_gmono4 _ _ x).add (isHom_gmono4 _ _ x)).smul _
  · exact ((((isHom_gmono4 _ _ x).sub (isHom_gmono4 _ _ x)).sub (isHom_gmono4 _ _ x)).add
      (isHom_gmono4 _ _ x)).smul _

theorem isHom_VcoupL_eg (Y : Finset (Lam d L N)) : IsHom 4 (VcoupL Y (eC 3)) := by
  rw [VcoupL_eg]
  exact IsHom.sum _ fun i _ => IsHom.sum _ fun x _ => isHom_mono4s i i x

/-- **The bubble coefficient is the double contraction**:
`-𝔅(C') = q_{j,j}(e_g)_g = μ₄ X₂(V_g(B_+), V_g(Λ)) / (4 |B_+|)`. -/
theorem FlowSeq.bubble_eq (D : FlowSeq d L N) (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) :
    D.betaQ j j b i₀ (eC 3) (eC 3) 3 = mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀
      (X2 (D.C j) (VcoupL (Bp (L := L) (N := N) j b) (eC 3)) (VcoupL univ (eC 3))) /
        (4 * (Bp (L := L) (N := N) j b).card) := by
  rw [D.betaQ_self_g_eq hL hj hb, mu4_FC_quartic _ (isHom_VcoupL_eg _) (isHom_VcoupL_eg _),
    c2_eq_X2 _ (A := VcoupL (Bp (L := L) (N := N) j b) (eC 3)) (mem_Ev.1 (unif_mem_Ev _ _ _ _)),
    mu4_smul]
  field_simp
  ring

end

end Step2
