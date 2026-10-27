import Grassmann.Moments

/-!
# The Gaussian expectation on the doubled algebra

`ℒ_C^ζ` is the operator `ℒ` of the covariance `C` placed on the `ζ` block (`Lζ_eq`), so the
integration by parts formulas apply:

* `EC_ψ₁_mul`: `𝔼_C (ψ_a G) = ψ_a 𝔼_C G`;
* `EC_zetabar_mul`: `𝔼_C (ζ̄_x G) = ∑_y C_{xy} 𝔼_C (∂_{ζ_y} G)`;
* `EC_zeta_mul`: `𝔼_C (ζ_y G) = -∑_x C_{xy} 𝔼_C (∂_{ζ̄_x} G)`;
* `EC_one`: `𝔼_C 1 = 1`;
* `EC_incl_mul_inclζ`: `𝔼_C (A B(ζ)) = A ⟨B⟩_C`.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The covariance `C` placed on the `ζ` block. -/
def liftζ (C : Matrix Λ Λ ℝ) : Matrix (Λ ⊕ Λ) (Λ ⊕ Λ) ℝ := Matrix.fromBlocks 0 0 0 C

theorem Lζ_eq (C : Matrix Λ Λ ℝ) : Lζ C = Lop (liftζ C) := by
  refine LinearMap.ext fun F => ?_
  rw [Lζ_apply, Lop_apply, Fintype.sum_sum_type]
  simp [liftζ, Fintype.sum_sum_type]

theorem EC_eq (C : Matrix Λ Λ ℝ) (F : N (Λ ⊕ Λ)) : EC C F = proj (expL (liftζ C) F) := by
  rw [EC, LinearMap.comp_apply, Lζ_eq]; rfl

theorem EC_ι_mul (C : Matrix Λ Λ ℝ) (w : V (Λ ⊕ Λ)) (G : N (Λ ⊕ Λ)) :
    EC C (ι ℂ w * G) = proj (ι ℂ w) * EC C G + EC C (Dφ (phiC (liftζ C) w) G) := by
  have hc := Module.End.commute_exp_left_of_commute (Lop_isNilpotent (liftζ C))
    (Lop_isNilpotent (liftζ C)) (g := Dφ (phiC (liftζ C) w))
    (LinearMap.ext fun G => Lop_Dφ (liftζ C) _ G)
  have := LinearMap.congr_fun hc G
  simp only [LinearMap.comp_apply] at this
  rw [EC_eq, EC_eq, EC_eq, expL_mul_ι, map_add, map_mul, expL, this]

theorem phiC_liftζ_inlV (C : Matrix Λ Λ ℝ) (m : V Λ) : phiC (liftζ C) (inlV m) = 0 := by
  ext w
  simp [phiC, liftζ, Fintype.sum_sum_type, inlV]

theorem EC_incl_ι_mul (C : Matrix Λ Λ ℝ) (m : V Λ) (G : N (Λ ⊕ Λ)) :
    EC C (ι ℂ (inlV m) * G) = ι ℂ m * EC C G := by
  rw [EC_ι_mul, phiC_liftζ_inlV, Dφ, map_zero, LinearMap.zero_apply, map_zero, add_zero]
  congr 1
  rw [← ExteriorAlgebra.map_apply_ι, ← incl, proj_incl]

/-- `𝔼_C (ψ_a G) = ψ_a 𝔼_C G`. -/
theorem EC_ψ₁_mul (C : Matrix Λ Λ ℝ) (a : Sf Λ) (G : N (Λ ⊕ Λ)) :
    EC C (ψ₁ a * G) = ψ a * EC C G := by
  rw [← incl_psi, incl, ψ, ExteriorAlgebra.map_apply_ι, EC_incl_ι_mul]

/-- `𝔼_C (A G) = A 𝔼_C G` for `A` in the `ψ` variables. -/
theorem EC_incl_mul (C : Matrix Λ Λ ℝ) (A : N Λ) (G : N (Λ ⊕ Λ)) :
    EC C (incl A * G) = A * EC C G := by
  induction A using CliffordAlgebra.induction generalizing G with
  | algebraMap r => simp only [AlgHom.commutes, ← Algebra.smul_def, map_smul]
  | ι m => rw [incl, ExteriorAlgebra.map_apply_ι, EC_incl_ι_mul]
  | mul a b ha hb => rw [map_mul incl a b, mul_assoc, ha, hb, ← mul_assoc]
  | add a b ha hb => rw [map_add incl a b, add_mul, map_add, ha, hb, add_mul]

theorem EC_one (C : Matrix Λ Λ ℝ) : EC C 1 = 1 := by
  rw [EC_eq, expL_eq_self, map_one]
  simp [Lop_apply]

theorem phiC_liftζ_zetabar (C : Matrix Λ Λ ℝ) (x : Λ) :
    phiC (liftζ C) (ev (Sum.inr x, -1)) = ∑ y, (C x y : ℂ) • coord (Sum.inr y, 1) := by
  ext w
  simp [phiC, liftζ, Fintype.sum_sum_type, ev, Pi.single_apply, Prod.ext_iff]

theorem phiC_liftζ_zeta (C : Matrix Λ Λ ℝ) (y : Λ) :
    phiC (liftζ C) (ev (Sum.inr y, 1)) = -∑ x, (C x y : ℂ) • coord (Sum.inr x, -1) := by
  ext w
  simp [phiC, liftζ, Fintype.sum_sum_type, ev, Pi.single_apply, Prod.ext_iff]

/-- `𝔼_C (ζ̄_x G) = ∑_y C_{xy} 𝔼_C (∂_{ζ_y} G)`. -/
theorem EC_zetabar_mul (C : Matrix Λ Λ ℝ) (x : Λ) (G : N (Λ ⊕ Λ)) :
    EC C (ζ (x, -1) * G) = ∑ y, (C x y : ℂ) • EC C (D (Sum.inr y, 1) G) := by
  rw [ζ, ψ, EC_ι_mul, ← ψ, proj_ζ, zero_mul, zero_add, phiC_liftζ_zetabar]
  simp [Dφ, map_sum, LinearMap.sum_apply, D]

/-- `𝔼_C (ζ_y G) = -∑_x C_{xy} 𝔼_C (∂_{ζ̄_x} G)`. -/
theorem EC_zeta_mul (C : Matrix Λ Λ ℝ) (y : Λ) (G : N (Λ ⊕ Λ)) :
    EC C (ζ (y, 1) * G) = -∑ x, (C x y : ℂ) • EC C (D (Sum.inr x, -1) G) := by
  rw [ζ, ψ, EC_ι_mul, ← ψ, proj_ζ, zero_mul, zero_add, phiC_liftζ_zeta]
  simp [Dφ, map_sum, LinearMap.sum_apply, D]

theorem coord_inr_inrV (x : Λ) (σ : ℤˣ) : coord (Sum.inr x, σ) ∘ₗ inrV = coord (x, σ) := by
  ext v; simp [inrV]

theorem Lop_liftζ_inclζ (C : Matrix Λ Λ ℝ) :
    Lop (liftζ C) ∘ₗ inclζ.toLinearMap = inclζ.toLinearMap ∘ₗ Lop C := by
  rw [← Lζ_eq]
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Lζ_apply, Lop_apply, map_sum,
    map_smul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1
  simp only [D, inclζ]
  rw [contractLeft_map, contractLeft_map, coord_inr_inrV, coord_inr_inrV]

/-- `𝔼_C (B(ζ)) = ⟨B⟩_C`. -/
theorem EC_inclζ (C : Matrix Λ Λ ℝ) (B : N Λ) :
    EC C (inclζ B) = algebraMap ℂ (N Λ) (omega C B) := by
  have h := Module.End.commute_exp_left_of_commute (Lop_isNilpotent C)
    (Lop_isNilpotent (liftζ C)) (Lop_liftζ_inclζ C)
  have := LinearMap.congr_fun h B
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [EC_eq, expL, this, proj_inclζ]; rfl

/-- `𝔼_C (A B(ζ)) = A ⟨B⟩_C`. -/
theorem EC_incl_mul_inclζ (C : Matrix Λ Λ ℝ) (A B : N Λ) :
    EC C (incl A * inclζ B) = omega C B • A := by
  rw [EC_incl_mul, EC_inclζ, Algebra.smul_def, Algebra.commutes]

end

end Grassmann
