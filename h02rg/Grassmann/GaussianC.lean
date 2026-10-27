import Grassmann.Gaussian

/-!
# Gaussian integration with complex covariances

The operators of `Grassmann.Gaussian` for a *complex* covariance `C : Matrix Λ Λ ℂ`:
`LopC C = ℒ_C`, `expLC C = e^{ℒ_C}`, `ECC C = 𝔼_C`, with the same properties
(`ECC_theta` is `e:fWick`, `ECC_theta_comp` is `e:E-semigroup`,
`ECC_theta_mul_of_disjoint` is the factorisation). No positivity or symmetry of `C` is used.

The real operators of `Grassmann.Gaussian` are the special case `C.map (↑)`
(`Lop_eq_LopC`, `expL_eq_expLC`, `EC_eq_ECC`, `omega_eq`), so every statement here applies to
them. The real definitions are kept unchanged, so that existing proofs which unfold them are
not affected.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset

variable {I : Type*} [DecidableEq I]

/-! ### The operator `ℒ_C` -/

/-- `ℒ_C = ∑_{x,y} C_{xy} ∂_{ψ_y} ∂_{ψ̄_x}` (the derivative `∂_{ψ̄_x}` acts first). -/
def LopC [Fintype I] (C : Matrix I I ℂ) : Module.End ℂ (N I) :=
  ∑ x, ∑ y, C x y • (D (y, 1) ∘ₗ D (x, -1))

theorem LopC_apply [Fintype I] (C : Matrix I I ℂ) (F : N I) :
    LopC C F = ∑ x, ∑ y, C x y • D (y, 1) (D (x, -1) F) := by
  simp [LopC, LinearMap.sum_apply]

theorem LopC_add [Fintype I] (C₁ C₂ : Matrix I I ℂ) : LopC (C₁ + C₂) = LopC C₁ + LopC C₂ := by
  simp only [LopC, Matrix.add_apply, Complex.ofReal_add, add_smul, sum_add_distrib]

theorem LopC_commute [Fintype I] (C₁ C₂ : Matrix I I ℂ) : Commute (LopC C₁) (LopC C₂) :=
  Commute.sum_left _ _ _ fun x _ => Commute.sum_left _ _ _ fun y _ =>
    Commute.sum_right _ _ _ fun x' _ => Commute.sum_right _ _ _ fun y' _ =>
      ((DD_commute _ _ _ _).smul_left _).smul_right _

theorem LopC_degLe [Fintype I] (C : Matrix I I ℂ) {n : ℕ} {x : N I} (hx : DegLe (n + 1) x) :
    DegLe n (LopC C x) := by
  rw [LopC_apply]
  exact DegLe.sum _ fun a _ => DegLe.sum _ fun b _ => (DD_degLe hx _ _).smul _

theorem LopC_degLe_zero [Fintype I] (C : Matrix I I ℂ) {x : N I} (hx : DegLe 0 x) : LopC C x = 0 := by
  rw [LopC_apply]
  exact sum_eq_zero fun a _ => sum_eq_zero fun b _ => by
    rw [D_eq_zero_of_degLe_zero hx, map_zero, smul_zero]

theorem LopC_pow_eq_zero [Fintype I] (C : Matrix I I ℂ) : LopC C ^ (Nf I + 1) = 0 :=
  pow_eq_zero_of_degLe _ (fun _ _ hx => LopC_degLe C hx) fun _ hx => LopC_degLe_zero C hx

theorem LopC_isNilpotent [Fintype I] (C : Matrix I I ℂ) : IsNilpotent (LopC C) :=
  ⟨_, LopC_pow_eq_zero C⟩

/-- `e^{ℒ_C}`. -/
abbrev expLC [Fintype I] (C : Matrix I I ℂ) : Module.End ℂ (N I) := IsNilpotent.exp (LopC C)


variable {Λ : Type*} [DecidableEq Λ]

/-- `ℒ_C^ζ = ∑_{x,y} C_{xy} ∂_{ζ_y} ∂_{ζ̄_x}` on the doubled algebra. -/
def LζC [Fintype Λ] (C : Matrix Λ Λ ℂ) : Module.End ℂ (N (Λ ⊕ Λ)) :=
  ∑ x, ∑ y, C x y • (D (Sum.inr y, 1) ∘ₗ D (Sum.inr x, -1))

theorem LζC_apply [Fintype Λ] (C : Matrix Λ Λ ℂ) (F : N (Λ ⊕ Λ)) :
    LζC C F = ∑ x, ∑ y, C x y • D (Sum.inr y, 1) (D (Sum.inr x, -1) F) := by
  simp [LζC, LinearMap.sum_apply]

theorem LζC_isNilpotent [Fintype Λ] (C : Matrix Λ Λ ℂ) : IsNilpotent (LζC C) := by
  refine isNilpotent_of_degLe _ (fun n x hx => ?_) fun x hx => ?_
  · rw [LζC_apply]
    exact DegLe.sum _ fun a _ => DegLe.sum _ fun b _ => (DD_degLe hx _ _).smul _
  · rw [LζC_apply]
    exact sum_eq_zero fun a _ => sum_eq_zero fun b _ => by
      rw [D_eq_zero_of_degLe_zero hx, map_zero, smul_zero]

theorem LζC_theta [Fintype Λ] (C : Matrix Λ Λ ℂ) :
    LζC C ∘ₗ theta.toLinearMap = theta.toLinearMap ∘ₗ LopC C := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LζC_apply, LopC_apply, map_sum,
    map_smul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [show ((Sum.inr x, -1) : Sf (Λ ⊕ Λ)) = (Sum.inr (x, (-1 : ℤˣ)).1, (x, (-1 : ℤˣ)).2) from rfl,
    Dζ_theta,
    show ((Sum.inr y, 1) : Sf (Λ ⊕ Λ)) = (Sum.inr (y, (1 : ℤˣ)).1, (y, (1 : ℤˣ)).2) from rfl,
    Dζ_theta]

/-- The Gaussian expectation `𝔼_C : 𝒩(Λ ⊔ Λ) → 𝒩(Λ)`, integrating out `ζ, ζ̄`. -/
def ECC [Fintype Λ] (C : Matrix Λ Λ ℂ) : N (Λ ⊕ Λ) →ₗ[ℂ] N Λ :=
  proj.toLinearMap ∘ₗ IsNilpotent.exp (LζC C)

/-- `e:fWick`: `𝔼_C θ F = e^{ℒ_C} F`. -/
theorem ECC_theta [Fintype Λ] (C : Matrix Λ Λ ℂ) (F : N Λ) : ECC C (theta F) = expLC C F := by
  have h := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C) (LζC_isNilpotent C)
    (LζC_theta C)
  have := LinearMap.congr_fun h F
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [ECC, LinearMap.comp_apply, this, AlgHom.toLinearMap_apply, proj_theta]

/-- `e:E-semigroup`: `𝔼_{C_2} θ ∘ 𝔼_{C_1} θ = 𝔼_{C_1 + C_2} θ`. -/
theorem ECC_theta_comp [Fintype Λ] (C₁ C₂ : Matrix Λ Λ ℂ) (F : N Λ) :
    ECC C₂ (theta (ECC C₁ (theta F))) = ECC (C₁ + C₂) (theta F) := by
  rw [ECC_theta, ECC_theta, ECC_theta]
  unfold expLC
  rw [LopC_add, add_comm,
    IsNilpotent.exp_add_of_commute (LopC_commute C₂ C₁) (LopC_isNilpotent C₂) (LopC_isNilpotent C₁)]
  rfl

/-- The moment `𝔼_C θ ψ̄_x ψ_y = ψ̄_x ψ_y + C_{xy}`. -/
theorem ECC_theta_psibar_psi [Fintype Λ] (C : Matrix Λ Λ ℂ) (x y : Λ) :
    ECC C (theta (psibar x * psi y)) = psibar x * psi y + algebraMap ℂ (N Λ) (C x y) := by
  have e1 : ∀ a, D (a, -1) (psibar x * psi y) = if a = x then psi y else 0 := by
    intro a
    have hne : ((a, -1) : Sf Λ) ≠ (y, 1) := by simp [Prod.ext_iff]
    rw [D_mul, psibar, psi, D_ψ, D_ψ, if_neg hne, mul_zero, add_zero]
    by_cases h : a = x
    · subst h; simp
    · rw [if_neg (by simp [Prod.ext_iff, h]), if_neg h, zero_mul]
  have e2 : ∀ b, D (b, 1) (psi y) = if b = y then 1 else 0 := fun b => by
    simp [psi, D_ψ, Prod.ext_iff]
  have hL : LopC C (psibar x * psi y) = algebraMap ℂ (N Λ) (C x y) := by
    rw [LopC_apply]
    simp only [e1, apply_ite (D _), map_zero, e2, smul_ite, smul_zero]
    simp [Algebra.algebraMap_eq_smul_one]
  have hk : (LopC C ^ 2) • (psibar x * psi y) = 0 := by
    rw [pow_two, mul_smul, Module.End.smul_def, Module.End.smul_def, hL, LopC_apply]
    simp [D_algebraMap]
  rw [ECC_theta]
  have := IsNilpotent.exp_smul_eq_sum hk (LopC_isNilpotent C)
  rw [Module.End.smul_def] at this
  rw [this]
  simp [Finset.sum_range_succ, hL]

variable [Fintype Λ]

theorem LopC_mem_NX (C : Matrix Λ Λ ℂ) {X : Set Λ} {F : N Λ} (hF : F ∈ NX X) :
    LopC C F ∈ NX X := by
  rw [LopC_apply]
  exact Subalgebra.sum_mem _ fun x _ => Subalgebra.sum_mem _ fun y _ =>
    Subalgebra.smul_mem _ (D_mem_NX (D_mem_NX hF _) _) _

theorem LopC_pow_mem_NX (C : Matrix Λ Λ ℂ) {X : Set Λ} {F : N Λ} (hF : F ∈ NX X) (k : ℕ) :
    (LopC C ^ k) F ∈ NX X := by
  induction k with
  | zero => exact hF
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact LopC_mem_NX _ ih

theorem expLC_apply_eq_sum (C : Matrix Λ Λ ℂ) (F : N Λ) :
    expLC C F = ∑ k ∈ range (Nf Λ + 1), ((k.factorial : ℚ)⁻¹ • (LopC C ^ k)) F := by
  rw [expLC, IsNilpotent.exp_eq_sum (LopC_pow_eq_zero C), LinearMap.sum_apply]

theorem expLC_mem_NX (C : Matrix Λ Λ ℂ) {X : Set Λ} {F : N Λ} (hF : F ∈ NX X) :
    expLC C F ∈ NX X := by
  rw [expLC_apply_eq_sum]
  refine Subalgebra.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ]
  exact Subalgebra.smul_mem _ (LopC_pow_mem_NX C hF k) _

theorem expLC_eq_self (C : Matrix Λ Λ ℂ) {F : N Λ} (hF : LopC C F = 0) : expLC C F = F := by
  have h1 : (LopC C ^ 1) • F = 0 := by rw [pow_one]; exact hF
  have := IsNilpotent.exp_smul_eq_sum h1 (LopC_isNilpotent C)
  rw [Module.End.smul_def] at this
  rw [expLC, this]; simp

/-- If `ℒ` commutes with right multiplication by `G`, so does `e^{ℒ}`. -/
theorem expLC_mul_right (C : Matrix Λ Λ ℂ) (G : N Λ) (h : ∀ H, LopC C (H * G) = LopC C H * G)
    (H : N Λ) : expLC C (H * G) = expLC C H * G := by
  have := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C) (LopC_isNilpotent C)
    (g := LinearMap.mulRight ℂ G) (LinearMap.ext fun H => by simp [h])
  simpa using LinearMap.congr_fun this H

theorem expLC_mul_left (C : Matrix Λ Λ ℂ) (F : N Λ) (h : ∀ G, LopC C (F * G) = F * LopC C G)
    (G : N Λ) : expLC C (F * G) = F * expLC C G := by
  have := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C) (LopC_isNilpotent C)
    (g := LinearMap.mulLeft ℂ F) (LinearMap.ext fun G => by simp [h])
  simpa using LinearMap.congr_fun this G

open Classical in
/-- `C` restricted to `X × X`. -/
def restrC (C : Matrix Λ Λ ℂ) (X : Set Λ) : Matrix Λ Λ ℂ :=
  fun x y => if x ∈ X ∧ y ∈ X then C x y else 0

theorem LopC_restr_mul_right (C : Matrix Λ Λ ℂ) {X Y : Set Λ} (hXY : Disjoint X Y) {G : N Λ}
    (hG : G ∈ NX Y) (H : N Λ) : LopC (restrC C X) (H * G) = LopC (restrC C X) H * G := by
  rw [LopC_apply, LopC_apply, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases hxy : x ∈ X ∧ y ∈ X
  · have hx : x ∉ Y := Set.disjoint_left.1 hXY hxy.1
    have hy : y ∉ Y := Set.disjoint_left.1 hXY hxy.2
    rw [smul_mul_assoc, D_mul, D_eq_zero_of_mem_NX hG hx, mul_zero, add_zero, D_mul,
      D_eq_zero_of_mem_NX hG hy, mul_zero, add_zero]
  · simp [restrC, hxy]

theorem LopC_restr_mul_left (C : Matrix Λ Λ ℂ) {X Y : Set Λ} (hXY : Disjoint X Y) {F : N Λ}
    (hF : F ∈ NX X) (G : N Λ) : LopC (restrC C Y) (F * G) = F * LopC (restrC C Y) G := by
  rw [LopC_apply, LopC_apply, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases hxy : x ∈ Y ∧ y ∈ Y
  · have hx : x ∉ X := Set.disjoint_right.1 hXY hxy.1
    have hy : y ∉ X := Set.disjoint_right.1 hXY hxy.2
    rw [mul_smul_comm, D_mul, D_eq_zero_of_mem_NX hF hx, zero_mul, zero_add, D_mul,
      D_inv', D_eq_zero_of_mem_NX hF hy, map_zero, neg_zero, zero_mul, zero_add, inv'_inv']
  · simp [restrC, hxy]

theorem LopC_restr_eq_zero (C : Matrix Λ Λ ℂ) {X Y : Set Λ} (hXY : Disjoint X Y) {F : N Λ}
    (hF : F ∈ NX X) : LopC (restrC C Y) F = 0 := by
  have := LopC_restr_mul_left C hXY hF 1
  rw [mul_one] at this
  rw [this, LopC_apply]; simp

/-- On `𝒩(X_1 ∪ X_2)`, `ℒ_C = ℒ_{C_1} + ℒ_{C_2}` if `C` vanishes between `X_1` and `X_2`. -/
theorem LopC_eq_add_restr (C : Matrix Λ Λ ℂ) {X₁ X₂ : Set Λ} (hX : Disjoint X₁ X₂)
    (hC : ∀ x ∈ X₁, ∀ y ∈ X₂, C x y = 0 ∧ C y x = 0) {G : N Λ} (hG : G ∈ NX (X₁ ∪ X₂)) :
    LopC C G = LopC (restrC C X₁ + restrC C X₂) G := by
  rw [LopC_apply, LopC_apply]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hx : x ∈ X₁ ∪ X₂
  · by_cases hy : y ∈ X₁ ∪ X₂
    · congr 1
      simp only [Matrix.add_apply, restrC]
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · simp [hx, hy, Set.disjoint_left.1 hX hx]
      · simp [hx, hy, Set.disjoint_left.1 hX hx, Set.disjoint_right.1 hX hy, (hC x hx y hy).1]
      · simp [hx, hy, Set.disjoint_right.1 hX hx, Set.disjoint_left.1 hX hy, (hC y hy x hx).2]
      · simp [hx, hy, Set.disjoint_right.1 hX hx]
    · rw [D_eq_zero_of_mem_NX (D_mem_NX hG _) hy, smul_zero, smul_zero]
  · rw [D_eq_zero_of_mem_NX hG hx, map_zero, smul_zero, smul_zero]

/-- Factorisation of `𝔼_C θ` for `F_i ∈ 𝒩(X_i)` when `C` vanishes between the disjoint sets
`X_1` and `X_2`: `𝔼_C θ (F_1 F_2) = (𝔼_C θ F_1)(𝔼_C θ F_2)`. -/
theorem ECC_theta_mul_of_disjoint (C : Matrix Λ Λ ℂ) {X₁ X₂ : Set Λ} (hX : Disjoint X₁ X₂)
    (hC : ∀ x ∈ X₁, ∀ y ∈ X₂, C x y = 0 ∧ C y x = 0) {F₁ F₂ : N Λ} (hF₁ : F₁ ∈ NX X₁)
    (hF₂ : F₂ ∈ NX X₂) :
    ECC C (theta (F₁ * F₂)) = ECC C (theta F₁) * ECC C (theta F₂) := by
  rw [ECC_theta, ECC_theta, ECC_theta]
  set C₁ := restrC C X₁
  set C₂ := restrC C X₂
  -- `e^{ℒ_C} = e^{ℒ_{C_1 + C_2}}` on `𝒩(X_1 ∪ X_2)`
  have hsub : ∀ G ∈ NX (X₁ ∪ X₂), expLC C G = expLC (C₁ + C₂) G := by
    intro G hG
    have hk : ∀ k, (LopC C ^ k) G = (LopC (C₁ + C₂) ^ k) G := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
        exact LopC_eq_add_restr C hX hC (LopC_pow_mem_NX _ hG k)
    rw [expLC_apply_eq_sum, expLC_apply_eq_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [LinearMap.smul_apply, hk]
  have hsplit : ∀ G, expLC (C₁ + C₂) G = expLC C₁ (expLC C₂ G) := by
    intro G
    unfold expLC
    rw [LopC_add, IsNilpotent.exp_add_of_commute (LopC_commute _ _) (LopC_isNilpotent _)
      (LopC_isNilpotent _)]
    rfl
  have hsplit' : ∀ G, expLC (C₁ + C₂) G = expLC C₂ (expLC C₁ G) := by
    intro G
    unfold expLC
    rw [LopC_add, add_comm, IsNilpotent.exp_add_of_commute (LopC_commute _ _) (LopC_isNilpotent _)
      (LopC_isNilpotent _)]
    rfl
  have h12 : F₁ * F₂ ∈ NX (X₁ ∪ X₂) :=
    mul_mem (NX_mono Set.subset_union_left hF₁) (NX_mono Set.subset_union_right hF₂)
  rw [hsub _ h12, hsub _ (NX_mono Set.subset_union_left hF₁),
    hsub _ (NX_mono Set.subset_union_right hF₂), hsplit, hsplit, hsplit',
    expLC_mul_left C₂ F₁ (LopC_restr_mul_left C hX hF₁),
    expLC_eq_self C₂ (LopC_restr_eq_zero C hX hF₁),
    expLC_eq_self C₁ (LopC_restr_eq_zero C hX.symm hF₂),
    expLC_mul_right C₁ _ (LopC_restr_mul_right C hX (expLC_mem_NX C₂ hF₂))]


/-! ### The real operators as a special case -/

section Bridge

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- The complexification of a real matrix. -/
abbrev cplx {α : Type*} (C : Matrix α α ℝ) : Matrix α α ℂ := C.map (↑)

theorem EC_eq_ECC (C : Matrix I I ℝ) : EC C = ECC (cplx C) := rfl

end Bridge

end

end Grassmann
