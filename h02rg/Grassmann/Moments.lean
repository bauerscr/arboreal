import Grassmann.IBP

/-!
# Fermionic Gaussian moments

`omega_moment`: for `ψ̄`-type vectors `b̄_i = ∑_x b_i(x) ψ̄_x` and `ψ`-type vectors
`a_j = ∑_y a_j(y) ψ_y`,
`⟨b̄_1 ⋯ b̄_n a_1 ⋯ a_n⟩_C = (-1)^{n(n-1)/2} det (b_i · C a_j)`, and moments with different
numbers of `ψ̄` and `ψ` vanish (`omega_moment_of_ne`).
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- The `ψ̄`-type vector `∑_x b(x) ψ̄_x`. -/
def vbar (b : I → ℝ) : V I := fun c => if c.2 = -1 then (b c.1 : ℂ) else 0

/-- The `ψ`-type vector `∑_y a(y) ψ_y`. -/
def vpsi (a : I → ℝ) : V I := fun c => if c.2 = 1 then (a c.1 : ℂ) else 0

theorem phiC_vbar_vbar (C : Matrix I I ℝ) (b b' : I → ℝ) : phiC C (vbar b) (vbar b') = 0 := by
  simp [phiC, vbar, LinearMap.sum_apply]

theorem phiC_vbar_vpsi (C : Matrix I I ℝ) (b a : I → ℝ) :
    phiC C (vbar b) (vpsi a) = ((b ⬝ᵥ (C *ᵥ a) : ℝ) : ℂ) := by
  simp only [phiC, vbar, vpsi, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.proj_apply, dotProduct, mulVec, mul_sum, Complex.ofReal_sum,
    Complex.ofReal_mul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp [smul_eq_mul]; ring

theorem inv'_ιMulti {n : ℕ} (u : Fin n → V I) :
    inv' (ιMulti ℂ n u : N I) = (-1 : ℂ) ^ n • ιMulti ℂ n u := by
  induction n with
  | zero => simp [ιMulti_zero_apply]
  | succ n ih => rw [ιMulti_succ_apply, map_mul, inv'_ι, ih, pow_succ']; simp

/-- A contraction passing through a product of vectors it annihilates. -/
theorem Dφ_ιMulti_mul (φ : Module.Dual ℂ (V I)) {n : ℕ} (u : Fin n → V I) (h : ∀ i, φ (u i) = 0)
    (G : N I) : Dφ φ (ιMulti ℂ n u * G) = (-1 : ℂ) ^ n • (ιMulti ℂ n u * Dφ φ G) := by
  rw [Dφ, contractLeft_mul, contractLeft_ιMulti_eq_zero φ u h, zero_mul, zero_add, inv'_ιMulti,
    smul_mul_assoc]

theorem D_vbar_free {φ : Module.Dual ℂ (V I)} {G : N I} (hG : ∀ x, D (x, -1) G = 0) (x : I) :
    D (x, -1) (Dφ φ G) = 0 := by
  rw [D, Dφ, contractLeft_comm, ← D, hG, map_zero, neg_zero]

theorem omega_smul (C : Matrix I I ℝ) (c : ℂ) (F : N I) : omega C (c • F) = c * omega C F := by
  simp [omega]

theorem omega_add (C : Matrix I I ℝ) (F G : N I) : omega C (F + G) = omega C F + omega C G := by
  simp [omega]

/-- `⟨b̄_1 ⋯ b̄_r G⟩_C = (-1)^{r(r-1)/2} (∂_{φ_{b_r}} ⋯ ∂_{φ_{b_1}} G)|_{ψ=0}` for `G` without `ψ̄`. -/
theorem omega_ιMulti_vbar_mul (C : Matrix I I ℝ) {r : ℕ} (b : Fin r → I → ℝ) {G : N I}
    (hG : ∀ x, D (x, -1) G = 0) :
    omega C (ιMulti ℂ r (fun i => vbar (b i)) * G) =
      (-1 : ℂ) ^ (r * (r - 1) / 2) * ε (contr (fun i => phiC C (vbar (b i))) G) := by
  induction r generalizing G with
  | zero => simp [ιMulti_zero_apply, omega_eq_of_Dbar C hG]
  | succ r ih =>
    rw [ιMulti_succ_apply, mul_assoc, omega_ι_mul,
      Dφ_ιMulti_mul (phiC C (vbar (b 0))) (Matrix.vecTail fun i => vbar (b i))
        (fun i => phiC_vbar_vbar _ _ _), omega_smul, contr_succ]
    have hG' : ∀ x, D (x, -1) (Dφ (phiC C (vbar (b 0))) G) = 0 := D_vbar_free hG
    have := ih (fun i => b i.succ) hG'
    simp only [Matrix.vecTail, Function.comp_def] at this ⊢
    rw [this, ← mul_assoc, ← pow_add]
    congr 2
    rcases r with _ | k
    · rfl
    · rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
        show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) by ring,
        Nat.add_mul_div_left _ _ two_pos, add_comm]

/-- The moment formula `⟨b̄_1 ⋯ b̄_n a_1 ⋯ a_n⟩_C = (-1)^{n(n-1)/2} det (b_i · C a_j)`. -/
theorem omega_moment (C : Matrix I I ℝ) {n : ℕ} (b a : Fin n → I → ℝ) :
    omega C (ιMulti ℂ n (fun i => vbar (b i)) * ιMulti ℂ n (fun j => vpsi (a j))) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * (((Matrix.of fun i j => b i ⬝ᵥ (C *ᵥ a j)).det : ℝ) : ℂ) := by
  rw [omega_ιMulti_vbar_mul C b (fun x => ?_), algebraMapInv_contr_ιMulti]
  · have hd := RingHom.map_det Complex.ofRealHom (Matrix.of fun i j => b i ⬝ᵥ (C *ᵥ a j))
    rw [Complex.ofRealHom_eq_coe] at hd
    rw [hd]
    congr 2
    ext i j
    simp [phiC_vbar_vpsi]
  · exact contractLeft_ιMulti_eq_zero _ _ fun i => by simp [vpsi]

theorem omega_moment_of_ne (C : Matrix I I ℝ) {r s : ℕ} (b : Fin r → I → ℝ) (a : Fin s → I → ℝ)
    (h : r ≠ s) :
    omega C (ιMulti ℂ r (fun i => vbar (b i)) * ιMulti ℂ s (fun j => vpsi (a j))) = 0 := by
  rw [omega_ιMulti_vbar_mul C b (fun x => ?_), algebraMapInv_contr_ιMulti_of_ne _ _ h, mul_zero]
  exact contractLeft_ιMulti_eq_zero _ _ fun i => by simp [vpsi]

end

end Grassmann
