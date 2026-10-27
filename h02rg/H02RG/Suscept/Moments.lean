import Suscept.Restrict

/-!
# Two-point sums by Gaussian integration by parts

For a covariance `C` with constant row and column sums `c` (for `C = (-Δ + m²)^{-1}`, `c = m^{-2}`)
and an even `G`,
`∑_{x,y} ⟨G ψ̄_x ψ_y⟩_C = c |Λ| ⟨G⟩_C + c² (𝔼_C θ G)²`, where `F² = c2 F` is the coefficient of
`ψψ̄` after restriction to constant fields (`sum_omega_psibar_psi`).
Here `⟨F⟩_C = omega C F = 𝔼_C[F]` is the Gaussian expectation (`omega_eq`).
-/

namespace Suscept

noncomputable section

open Finset Grassmann ExteriorAlgebra CliffordAlgebra

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `⟨F⟩_C = 𝔼_C[F]` is the constant term of `𝔼_C θ F`. -/
theorem omega_eq (C : Matrix Λ Λ ℝ) (F : Grassmann.N Λ) : omega C F = ε (EC C (theta F)) := by
  rw [omega, EC_theta]

/-- The vector `∑_x e_{(x,σ)}`, so that `ι (vs σ) = ∑_x ψ_{(x,σ)}`. -/
def vs (s : ℤˣ) : V Λ := ∑ x : Λ, ev ((x, s) : Sf Λ)

theorem ι_vs (s : ℤˣ) : ExteriorAlgebra.ι ℂ (vs (Λ := Λ) s) = ∑ x : Λ, ψ ((x, s) : Sf Λ) := by
  rw [vs, map_sum]; rfl

theorem vs_apply (s t : ℤˣ) (x : Λ) : vs s ((x, t) : Sf Λ) = if t = s then 1 else 0 := by
  simp only [vs, Finset.sum_apply, ev, Pi.single_apply, Prod.ext_iff]
  by_cases h : t = s
  · simp [h]
  · simp [h]

theorem δs_vs (s : ℤˣ) : δs s (vs (Λ := Λ) s) = Fintype.card Λ := by
  simp [δs, vs_apply]

theorem phiC_vs_neg (C : Matrix Λ Λ ℝ) {c : ℝ} (hcol : ∀ y, ∑ x, C x y = c) :
    phiC C (vs (-1)) = (c : ℂ) • δs 1 := by
  refine LinearMap.ext fun w => ?_
  simp [phiC, vs_apply, δs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_mul, ← Complex.ofReal_sum, hcol]

theorem phiC_vs_one (C : Matrix Λ Λ ℝ) {c : ℝ} (hrow : ∀ x, ∑ y, C x y = c) :
    phiC C (vs 1) = -((c : ℂ) • δs (-1)) := by
  refine LinearMap.ext fun w => ?_
  simp [phiC, vs_apply, δs, Finset.mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_mul, ← Complex.ofReal_sum, hrow]

theorem Dφ_δs_expL (C : Matrix Λ Λ ℝ) (s : ℤˣ) (F : Grassmann.N Λ) :
    Dφ (δs s) (expL C F) = expL C (Dφ (δs s) F) := by
  have hc : Lop C ∘ₗ Dφ (δs s) = Dφ (δs s) ∘ₗ Lop C :=
    LinearMap.ext fun G => Lop_Dφ C _ G
  have h := Module.End.commute_exp_left_of_commute (Lop_isNilpotent C) (Lop_isNilpotent C) hc
  have h2 := LinearMap.congr_fun h F
  simp only [LinearMap.comp_apply] at h2
  exact h2.symm

theorem c2_eq_ε (F : Grassmann.N Λ) : c2 F = ε (Dφ (δs (-1)) (Dφ (δs 1) F)) := by
  rw [Dφ_δs, map_sum, c2, Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [Dφ_δs, map_sum, map_sum]
  rfl

/-- **Two-point sum by integration by parts**: if `C` has constant row and column sums `c` and
`G` is even, then `∑_{x,y} ⟨G ψ̄_x ψ_y⟩_C = c |Λ| ⟨G⟩_C + c² (𝔼_C θ G)²`. -/
theorem sum_omega_psibar_psi (C : Matrix Λ Λ ℝ) {c : ℝ} (hrow : ∀ x, ∑ y, C x y = c)
    (hcol : ∀ y, ∑ x, C x y = c) {G : Grassmann.N Λ} (hG : inv' G = G) :
    ∑ x : Λ, ∑ y : Λ, omega C (G * (psibar x * psi y)) =
      (c : ℂ) * Fintype.card Λ * omega C G + (c : ℂ) ^ 2 * c2 (EC C (theta G)) := by
  have e0 : ExteriorAlgebra.ι ℂ (vs (-1)) * (ExteriorAlgebra.ι ℂ (vs 1) * G) =
      ∑ x : Λ, ∑ y : Λ, G * (psibar x * psi y) := by
    rw [ι_vs, ι_vs, ← mul_assoc, ← mul_comm_of_even hG, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    rfl
  have e1 : ∑ x : Λ, ∑ y : Λ, omega C (G * (psibar x * psi y)) =
      omega C (ExteriorAlgebra.ι ℂ (vs (-1)) * (ExteriorAlgebra.ι ℂ (vs 1) * G)) := by
    rw [e0]; simp only [omega, map_sum]
  have hsub : ∀ F F' : Grassmann.N Λ, omega C (F - F') = omega C F - omega C F' := fun F F' => by
    simp [omega]
  have hneg : ∀ F : Grassmann.N Λ, omega C (-F) = -omega C F := fun F => by simp [omega]
  rw [e1, omega_ι_mul, phiC_vs_neg C hcol, Dφ_smul, omega_smul, Dφ, contractLeft_ι_mul,
    ← Dφ, δs_vs, hsub, omega_ι_mul, phiC_vs_one C hrow]
  have e2 : Dφ (-((c : ℂ) • δs (-1))) (Dφ (δs 1) G) =
      -((c : ℂ) • Dφ (δs (-1)) (Dφ (δs 1) G)) := by simp [Dφ]
  have e3 : omega C (Dφ (δs (-1)) (Dφ (δs 1) G)) = c2 (EC C (theta G)) := by
    rw [c2_eq_ε, EC_theta, Dφ_δs_expL, Dφ_δs_expL, omega]
  rw [e2, hneg, omega_smul, omega_smul, e3]
  ring

end

end Suscept
