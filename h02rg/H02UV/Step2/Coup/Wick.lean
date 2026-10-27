import Step2.Coup.JInv

/-!
# Wick contractions for `𝔼_C θ` (`h02uv-outline.tex`, Lemma `lem:first`, exact form)

For linear forms `a_r = ι u_r` (spin `+`) and `b_r = ι v_r` (spin `-`), with
`⟨u, v⟩_C = ∑_{x,y} C(x,y) u(y,+) v(x,-)` (`pairC`):

* `LopC_two`: `𝓛_C (a b) = -⟨u, v⟩`;
* `LopC_four`: `𝓛_C (a₁ b₁ a₂ b₂) = -⟨11⟩ a₂b₂ + ⟨21⟩ a₁b₂ - ⟨12⟩ b₁a₂ - ⟨22⟩ a₁b₁`;
* `expLC_of_cube`: `e^{𝓛} G = G + 𝓛G + ½ 𝓛²G` if `𝓛³ G = 0`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `⟨u, v⟩_C = ∑_{x,y} C(x,y) u(y,+) v(x,-)`. -/
def pairC (C : Matrix Λ Λ ℂ) (u v : V Λ) : ℂ := ∑ x, ∑ y, C x y * (u (y, 1) * v (x, -1))

theorem D_ι (a : Sf Λ) (u : V Λ) :
    D a (ExteriorAlgebra.ι ℂ u : N Λ) = algebraMap ℂ (N Λ) (u a) := by
  simp [D, CliffordAlgebra.contractLeft_ι]

theorem inv'_ι (u : V Λ) : inv' (ExteriorAlgebra.ι ℂ u : N Λ) = -ExteriorAlgebra.ι ℂ u := by
  simp [inv']

theorem D_ι_mul (a : Sf Λ) (u : V Λ) (X : N Λ) :
    D a ((ExteriorAlgebra.ι ℂ u : N Λ) * X) = u a • X - ExteriorAlgebra.ι ℂ u * D a X := by
  rw [D_mul, D_ι, inv'_ι, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, neg_mul,
    sub_eq_add_neg]

/-- One spin-`+` and one spin-`-` form. -/
structure PM (u v : V Λ) : Prop where
  hu : ∀ x, u (x, -1) = 0
  hv : ∀ x, v (x, 1) = 0

local notation "ι" => (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] N Λ)

theorem LopC_two (C : Matrix Λ Λ ℂ) {u v : V Λ} (h : PM u v) :
    LopC C (ι u * ι v) = (-pairC C u v) • (1 : N Λ) := by
  have e : ∀ x y, C x y • D (y, 1) (D (x, -1) (ι u * ι v)) =
      (-(C x y * (u (y, 1) * v (x, -1)))) • (1 : N Λ) := by
    intro x y
    rw [D_ι_mul, D_ι, h.hu, zero_smul, zero_sub, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one, map_neg, map_smul, D_ι, Algebra.algebraMap_eq_smul_one, smul_neg,
      smul_smul, smul_smul, ← neg_smul]
    congr 1; ring
  rw [LopC_apply]
  simp only [e, ← sum_smul, sum_neg_distrib]
  rfl

theorem DD_four {u₁ v₁ u₂ v₂ : V Λ} (h₁ : PM u₁ v₁) (h₂ : PM u₂ v₂) (x y : Λ) :
    D (y, 1) (D (x, -1) (ι u₁ * (ι v₁ * (ι u₂ * ι v₂)))) =
      (-(u₁ (y, 1) * v₁ (x, -1))) • (ι u₂ * ι v₂) + (u₂ (y, 1) * v₁ (x, -1)) • (ι u₁ * ι v₂) +
        (-(u₁ (y, 1) * v₂ (x, -1))) • (ι v₁ * ι u₂) +
        (-(u₂ (y, 1) * v₂ (x, -1))) • (ι u₁ * ι v₁) := by
  have e1 : D (x, -1) (ι u₂ * ι v₂) = (-v₂ (x, -1)) • ι u₂ := by
    rw [D_ι_mul, D_ι, h₂.hu, zero_smul, zero_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one, neg_smul]
  have e2 : D (x, -1) (ι v₁ * (ι u₂ * ι v₂)) =
      v₁ (x, -1) • (ι u₂ * ι v₂) + v₂ (x, -1) • (ι v₁ * ι u₂) := by
    rw [D_ι_mul, e1, mul_smul_comm, neg_smul, sub_neg_eq_add]
  have e3 : D (x, -1) (ι u₁ * (ι v₁ * (ι u₂ * ι v₂))) =
      (-v₁ (x, -1)) • (ι u₁ * (ι u₂ * ι v₂)) + (-v₂ (x, -1)) • (ι u₁ * (ι v₁ * ι u₂)) := by
    rw [D_ι_mul, h₁.hu, zero_smul, zero_sub, e2, mul_add, mul_smul_comm, mul_smul_comm, neg_add,
      neg_smul, neg_smul]
  have f1 : D (y, 1) (ι u₂ * ι v₂) = u₂ (y, 1) • ι v₂ := by
    rw [D_ι_mul, D_ι, h₂.hv, Algebra.algebraMap_eq_smul_one, zero_smul, mul_zero, sub_zero]
  have f2 : D (y, 1) (ι u₁ * (ι u₂ * ι v₂)) =
      u₁ (y, 1) • (ι u₂ * ι v₂) - u₂ (y, 1) • (ι u₁ * ι v₂) := by
    rw [D_ι_mul, f1, mul_smul_comm]
  have f3 : D (y, 1) (ι v₁ * ι u₂) = (-u₂ (y, 1)) • ι v₁ := by
    rw [D_ι_mul, h₁.hv, zero_smul, zero_sub, D_ι, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one, neg_smul]
  have f4 : D (y, 1) (ι u₁ * (ι v₁ * ι u₂)) =
      u₁ (y, 1) • (ι v₁ * ι u₂) + u₂ (y, 1) • (ι u₁ * ι v₁) := by
    rw [D_ι_mul, f3, mul_smul_comm, neg_smul, sub_neg_eq_add]
  rw [e3, map_add, map_smul, map_smul, f2, f4]
  module

theorem LopC_four (C : Matrix Λ Λ ℂ) {u₁ v₁ u₂ v₂ : V Λ} (h₁ : PM u₁ v₁) (h₂ : PM u₂ v₂) :
    LopC C (ι u₁ * (ι v₁ * (ι u₂ * ι v₂))) =
      (-pairC C u₁ v₁) • (ι u₂ * ι v₂) + pairC C u₂ v₁ • (ι u₁ * ι v₂) +
        (-pairC C u₁ v₂) • (ι v₁ * ι u₂) + (-pairC C u₂ v₂) • (ι u₁ * ι v₁) := by
  rw [LopC_apply]
  simp only [DD_four h₁ h₂, smul_add, smul_smul, sum_add_distrib, ← sum_smul, pairC]
  simp only [mul_neg, sum_neg_distrib]

theorem LopC_algebraMap (C : Matrix Λ Λ ℂ) (r : ℂ) : LopC C (algebraMap ℂ (N Λ) r) = 0 := by
  rw [LopC_apply]; simp [D_algebraMap]

theorem LopC_one (C : Matrix Λ Λ ℂ) : LopC C (1 : N Λ) = 0 := by
  rw [← map_one (algebraMap ℂ (N Λ))]; exact LopC_algebraMap C 1

theorem expLC_of_cube (C : Matrix Λ Λ ℂ) {G : N Λ} (hG : LopC C (LopC C (LopC C G)) = 0) :
    expLC C G = G + LopC C G + (1 / 2 : ℂ) • LopC C (LopC C G) := by
  obtain ⟨k, hk⟩ := LopC_isNilpotent C
  have hk' : LopC C ^ (max k 3) = 0 := pow_eq_zero_of_le (le_max_left _ _) hk
  rw [expLC, IsNilpotent.exp_eq_sum hk', LinearMap.sum_apply]
  have h3 : ∀ i, 3 ≤ i → (LopC C ^ i) G = 0 := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [pow_add, Module.End.mul_apply]
    have : (LopC C ^ 3) G = 0 := by
      simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply]; exact hG
    rw [this, map_zero]
  rw [← sum_range_add_sum_Ico _ (show 3 ≤ max k 3 from le_max_right _ _)]
  rw [sum_eq_zero (s := Ico 3 (max k 3)) fun i hi => by
    rw [LinearMap.smul_apply, h3 i (mem_Ico.1 hi).1, smul_zero]]
  simp [sum_range_succ, pow_succ, Module.End.mul_apply]
  rw [← Rat.cast_smul_eq_qsmul ℂ]
  norm_num

theorem expLC_two (C : Matrix Λ Λ ℂ) {u v : V Λ} (h : PM u v) :
    expLC C (ι u * ι v) = ι u * ι v + (-pairC C u v) • (1 : N Λ) := by
  rw [expLC_of_cube C (by rw [LopC_two C h, map_smul, LopC_one, smul_zero, map_zero]),
    LopC_two C h, map_smul, LopC_one, smul_zero, smul_zero, add_zero]

/-- The full contraction: `e^{𝓛}(a₁b₁a₂b₂) = a₁b₁a₂b₂ + 𝓛(a₁b₁a₂b₂) + ⟨11⟩⟨22⟩ - ⟨12⟩⟨21⟩`. -/
theorem expLC_four (C : Matrix Λ Λ ℂ) {u₁ v₁ u₂ v₂ : V Λ} (h₁ : PM u₁ v₁) (h₂ : PM u₂ v₂) :
    expLC C (ι u₁ * (ι v₁ * (ι u₂ * ι v₂))) = ι u₁ * (ι v₁ * (ι u₂ * ι v₂)) +
      LopC C (ι u₁ * (ι v₁ * (ι u₂ * ι v₂))) +
      (pairC C u₁ v₁ * pairC C u₂ v₂ - pairC C u₁ v₂ * pairC C u₂ v₁) • (1 : N Λ) := by
  have hba : ι v₁ * ι u₂ = -(ι u₂ * ι v₁) := ι_anticomm v₁ u₂
  have hPM : PM u₂ v₁ := ⟨h₂.hu, h₁.hv⟩
  have hL2 : LopC C (LopC C (ι u₁ * (ι v₁ * (ι u₂ * ι v₂)))) =
      (2 * (pairC C u₁ v₁ * pairC C u₂ v₂ - pairC C u₁ v₂ * pairC C u₂ v₁)) • (1 : N Λ) := by
    rw [LopC_four C h₁ h₂, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      LopC_two C h₂, LopC_two C ⟨h₁.hu, h₂.hv⟩, hba, map_neg, LopC_two C hPM, LopC_two C h₁]
    simp only [smul_smul, smul_neg, neg_smul]
    module
  rw [expLC_of_cube C (by rw [hL2, map_smul, LopC_one, smul_zero]), hL2, smul_smul]
  congr 1; norm_num; ring_nf

end General

end

end Step2
