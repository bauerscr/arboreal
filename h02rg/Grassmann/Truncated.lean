import Grassmann.GaussianC

/-!
# Truncated expectations (`h02uv-outline.tex`, Lemma `lem:F`)

For a complex covariance `Γ` let `e^{ℒ_Γ}` be `expLC Γ`; it is invertible with inverse
`e^{ℒ_{-Γ}}` (`expLC_neg_expLC`). Define
`F_Γ(A, B) = e^{ℒ_Γ}((e^{-ℒ_Γ} A)(e^{-ℒ_Γ} B)) - AB` (`FC`), so that
`F_Γ(𝔼_Γ θ A, 𝔼_Γ θ B) = 𝔼_Γ θ (AB) - (𝔼_Γ θ A)(𝔼_Γ θ B)` (`FC_expLC`).

`lem:F`:
* (i) `F_Γ` is bilinear (`FC_add_left`, …), `F_0 = 0` (`FC_zero_cov`), and `F_Γ` is symmetric
  on even elements (`FC_comm`);
* (ii) `F_{Γ₁+Γ₂}(e^{ℒ_{Γ₂}} A, e^{ℒ_{Γ₂}} B) = e^{ℒ_{Γ₂}} F_{Γ₁}(A, B) + F_{Γ₂}(e^{ℒ_{Γ₂}} A, e^{ℒ_{Γ₂}} B)`
  (`FC_add_cov`);
* (iii) `F_Γ(A, B) = 0` for `A ∈ 𝒩(X)`, `B ∈ 𝒩(Y)`, `X, Y` disjoint and `Γ` vanishing between
  them (`FC_eq_zero_of_disjoint`);
* (iv) `e^{ℒ_Γ}` preserves `𝒩(X)` (`expLC_mem_NX`).
No positivity, symmetry or reality of `Γ` is used.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-! ### Inverse and parity -/

theorem LopC_zero : LopC (0 : Matrix Λ Λ ℂ) = 0 := by
  simp [LopC]

theorem expLC_zero (F : N Λ) : expLC (0 : Matrix Λ Λ ℂ) F = F := by
  rw [expLC, LopC_zero, IsNilpotent.exp_zero]; rfl

theorem expLC_add (C₁ C₂ : Matrix Λ Λ ℂ) (F : N Λ) :
    expLC (C₁ + C₂) F = expLC C₁ (expLC C₂ F) := by
  unfold expLC
  rw [LopC_add, IsNilpotent.exp_add_of_commute (LopC_commute _ _) (LopC_isNilpotent _)
    (LopC_isNilpotent _)]
  rfl

theorem expLC_neg_expLC (C : Matrix Λ Λ ℂ) (F : N Λ) : expLC (-C) (expLC C F) = F := by
  rw [← expLC_add, neg_add_cancel, expLC_zero]

theorem expLC_expLC_neg (C : Matrix Λ Λ ℂ) (F : N Λ) : expLC C (expLC (-C) F) = F := by
  rw [← expLC_add, add_neg_cancel, expLC_zero]

theorem LopC_inv' (C : Matrix Λ Λ ℂ) (F : N Λ) : LopC C (inv' F) = inv' (LopC C F) := by
  rw [LopC_apply, LopC_apply, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [D_inv', map_neg, D_inv', neg_neg, map_smul]

theorem expLC_inv' (C : Matrix Λ Λ ℂ) (F : N Λ) : expLC C (inv' F) = inv' (expLC C F) := by
  have := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C) (LopC_isNilpotent C)
    (g := (inv' : N Λ →ₐ[ℂ] N Λ).toLinearMap) (LinearMap.ext fun G => by
      simp [LopC_inv'])
  simpa using LinearMap.congr_fun this F

/-- `e^{ℒ_Γ}` preserves even elements. -/
theorem expLC_even (C : Matrix Λ Λ ℂ) {F : N Λ} (hF : inv' F = F) :
    inv' (expLC C F) = expLC C F := by
  rw [← expLC_inv', hF]

/-! ### The truncated expectation -/

/-- `F_Γ(A, B) = e^{ℒ_Γ}((e^{-ℒ_Γ} A)(e^{-ℒ_Γ} B)) - AB`. -/
def FC (C : Matrix Λ Λ ℂ) (A B : N Λ) : N Λ :=
  expLC C (expLC (-C) A * expLC (-C) B) - A * B

/-- `F_Γ(e^{ℒ_Γ} A, e^{ℒ_Γ} B) = e^{ℒ_Γ}(AB) - (e^{ℒ_Γ} A)(e^{ℒ_Γ} B)`, the truncated
expectation `𝔼_Γ θ (AB) - (𝔼_Γ θ A)(𝔼_Γ θ B)` (by `ECC_theta`). -/
theorem FC_expLC (C : Matrix Λ Λ ℂ) (A B : N Λ) :
    FC C (expLC C A) (expLC C B) = expLC C (A * B) - expLC C A * expLC C B := by
  rw [FC, expLC_neg_expLC, expLC_neg_expLC]

theorem FC_ECC_theta (C : Matrix Λ Λ ℂ) (A B : N Λ) :
    FC C (ECC C (theta A)) (ECC C (theta B)) =
      ECC C (theta (A * B)) - ECC C (theta A) * ECC C (theta B) := by
  rw [ECC_theta, ECC_theta, ECC_theta, FC_expLC]

/-! #### (i) -/

theorem FC_add_left (C : Matrix Λ Λ ℂ) (A A' B : N Λ) :
    FC C (A + A') B = FC C A B + FC C A' B := by
  simp only [FC, map_add, add_mul]; abel

theorem FC_add_right (C : Matrix Λ Λ ℂ) (A B B' : N Λ) :
    FC C A (B + B') = FC C A B + FC C A B' := by
  simp only [FC, map_add, mul_add]; abel

theorem FC_smul_left (C : Matrix Λ Λ ℂ) (c : ℂ) (A B : N Λ) :
    FC C (c • A) B = c • FC C A B := by
  simp only [FC, map_smul, smul_mul_assoc, smul_sub]

theorem FC_smul_right (C : Matrix Λ Λ ℂ) (c : ℂ) (A B : N Λ) :
    FC C A (c • B) = c • FC C A B := by
  simp only [FC, map_smul, mul_smul_comm, smul_sub]

theorem FC_sum_left {ι : Type*} (s : Finset ι) (C : Matrix Λ Λ ℂ) (A : ι → N Λ) (B : N Λ) :
    FC C (∑ i ∈ s, A i) B = ∑ i ∈ s, FC C (A i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FC]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, FC_add_left, ih]

theorem FC_sum_right {ι : Type*} (s : Finset ι) (C : Matrix Λ Λ ℂ) (A : N Λ) (B : ι → N Λ) :
    FC C A (∑ i ∈ s, B i) = ∑ i ∈ s, FC C A (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FC]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, FC_add_right, ih]

/-- `F_Γ` is symmetric on even elements. -/
theorem FC_comm (C : Matrix Λ Λ ℂ) {A B : N Λ} (hA : inv' A = A) (hB : inv' B = B) :
    FC C A B = FC C B A := by
  rw [FC, FC, mul_comm_of_even (expLC_even (-C) hA), mul_comm_of_even hA]

/-! #### (ii) -/

/-- `lem:F`(ii). -/
theorem FC_add_cov (C₁ C₂ : Matrix Λ Λ ℂ) (A B : N Λ) :
    FC (C₁ + C₂) (expLC C₂ A) (expLC C₂ B) =
      expLC C₂ (FC C₁ A B) + FC C₂ (expLC C₂ A) (expLC C₂ B) := by
  have e1 : ∀ G, expLC (-(C₁ + C₂)) (expLC C₂ G) = expLC (-C₁) G := fun G => by
    rw [neg_add, expLC_add, expLC_neg_expLC]
  rw [FC, e1, e1, FC, FC_expLC, map_sub, add_comm C₁ C₂, expLC_add]
  abel

/-! #### (iii) and (iv) -/

/-- Multiplicativity of `e^{ℒ_Γ}` on `𝒩(X) × 𝒩(Y)` when `Γ` vanishes between `X` and `Y`. -/
theorem expLC_mul_of_disjoint (C : Matrix Λ Λ ℂ) {X Y : Set Λ} (hXY : Disjoint X Y)
    (hC : ∀ x ∈ X, ∀ y ∈ Y, C x y = 0 ∧ C y x = 0) {A B : N Λ} (hA : A ∈ NX X)
    (hB : B ∈ NX Y) : expLC C (A * B) = expLC C A * expLC C B := by
  have := ECC_theta_mul_of_disjoint C hXY hC hA hB
  rwa [ECC_theta, ECC_theta, ECC_theta] at this

/-- `lem:F`(iii): `F_Γ(A, B) = 0` if `A ∈ 𝒩(X)`, `B ∈ 𝒩(Y)` and `Γ` vanishes between the
disjoint sets `X` and `Y` (for instance `dist_∞(X, Y) > rng(Γ)`). -/
theorem FC_eq_zero_of_disjoint (C : Matrix Λ Λ ℂ) {X Y : Set Λ} (hXY : Disjoint X Y)
    (hC : ∀ x ∈ X, ∀ y ∈ Y, C x y = 0 ∧ C y x = 0) {A B : N Λ} (hA : A ∈ NX X)
    (hB : B ∈ NX Y) : FC C A B = 0 := by
  rw [FC, expLC_mul_of_disjoint C hXY hC (expLC_mem_NX _ hA) (expLC_mem_NX _ hB),
    expLC_expLC_neg, expLC_expLC_neg, sub_self]

/-- `lem:F`(iv): `F_Γ(A, B) ∈ 𝒩(X)` for `A, B ∈ 𝒩(X)`. -/
theorem FC_mem_NX (C : Matrix Λ Λ ℂ) {X : Set Λ} {A B : N Λ} (hA : A ∈ NX X) (hB : B ∈ NX X) :
    FC C A B ∈ NX X :=
  sub_mem (expLC_mem_NX _ (mul_mem (expLC_mem_NX _ hA) (expLC_mem_NX _ hB))) (mul_mem hA hB)

end

end Grassmann
