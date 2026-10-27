import Grassmann.GaussianC
import Grassmann.Doubled

/-!
# Integration by parts, moments and the doubled algebra for complex covariances

The results of `Grassmann.IBP`, `Grassmann.Moments` and `Grassmann.Doubled` for a complex
covariance `C : Matrix Λ Λ ℂ`. The moment formula `omegaC_moment` is
`⟨b̄_1 ⋯ b̄_n a_1 ⋯ a_n⟩_C = (-1)^{n(n-1)/2} det (bil C b_i a_j)`, with the complex bilinear
form `bil C b a = ∑_{x,y} b(x) C_{xy} a(y)`.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

section IBP

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- `∑_{x,y} b(x) C_{xy} a(y)` for real profiles `b, a` and a complex matrix `C`. -/
def bil (C : Matrix I I ℂ) (b a : I → ℝ) : ℂ := ∑ x, ∑ y, (b x : ℂ) * C x y * (a y : ℂ)

/-- The functional `φ_v(w) = ∑_{x,y} C_{xy} (v_{x,-} w_{y,+} - v_{y,+} w_{x,-})`. -/
def phiCx (C : Matrix I I ℂ) (v : V I) : Module.Dual ℂ (V I) :=
  ∑ x, ∑ y, C x y • (v (x, -1) • coord (y, 1) - v (y, 1) • coord (x, -1))

theorem Dφ_phiCx_apply_sum (C : Matrix I I ℂ) (v : V I) (G : N I) :
    Dφ (phiCx C v) G = ∑ x, ∑ y, C x y • (v (x, -1) • D (y, 1) G - v (y, 1) • D (x, -1) G) := by
  simp only [phiCx, Dφ, map_sum, map_smul, map_sub, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, D]

theorem LopC_mul_ι (C : Matrix I I ℂ) (v : V I) (G : N I) :
    LopC C (ι ℂ v * G) = ι ℂ v * LopC C G + Dφ (phiCx C v) G := by
  rw [LopC_apply, LopC_apply, Dφ_phiCx_apply_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [DD_ι_mul, mul_smul_comm]
  module

/-- `∂_φ` commutes with `ℒ_C`. -/
theorem LopC_Dφ (C : Matrix I I ℂ) (φ : Module.Dual ℂ (V I)) (G : N I) :
    LopC C (Dφ φ G) = Dφ φ (LopC C G) := by
  rw [LopC_apply, LopC_apply, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [map_smul]
  congr 1
  simp only [D, Dφ]
  rw [contractLeft_comm φ, contractLeft_comm φ, map_neg, neg_neg]

theorem LopC_pow_mul_ι (C : Matrix I I ℂ) (v : V I) (G : N I) (k : ℕ) :
    (LopC C ^ (k + 1)) (ι ℂ v * G) =
      ι ℂ v * (LopC C ^ (k + 1)) G + ((k + 1 : ℕ) : ℂ) • Dφ (phiCx C v) ((LopC C ^ k) G) := by
  induction k with
  | zero => simp [LopC_mul_ι]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, LopC_mul_ι, map_smul, LopC_Dφ,
      ← Module.End.mul_apply (LopC C) (LopC C ^ (k + 1)), ← pow_succ',
      ← Module.End.mul_apply (LopC C) (LopC C ^ k), ← pow_succ']
    push_cast
    module

/-- `e^{ℒ_C} (ι v G) = ι v e^{ℒ_C} G + ∂_{φ_v} e^{ℒ_C} G`. -/
theorem expLC_mul_ι (C : Matrix I I ℂ) (v : V I) (G : N I) :
    expLC C (ι ℂ v * G) = ι ℂ v * expLC C G + Dφ (phiCx C v) (expLC C G) := by
  set K := Nf I + 1
  have hK : LopC C ^ K = 0 := LopC_pow_eq_zero C
  have h2 : LopC C ^ (K + 1) = 0 := by rw [pow_succ, hK, zero_mul]
  have eS : ∀ H, expLC C H = ∑ k ∈ range K, ((k.factorial : ℚ)⁻¹ • (LopC C ^ k)) H := fun H => by
    rw [expLC, IsNilpotent.exp_eq_sum hK, LinearMap.sum_apply]
  have eS' : ∀ H, expLC C H = ∑ k ∈ range (K + 1), ((k.factorial : ℚ)⁻¹ • (LopC C ^ k)) H :=
    fun H => by rw [expLC, IsNilpotent.exp_eq_sum h2, LinearMap.sum_apply]
  rw [show ι ℂ v * expLC C G + Dφ (phiCx C v) (expLC C G) =
      ι ℂ v * (∑ k ∈ range (K + 1), ((k.factorial : ℚ)⁻¹ • (LopC C ^ k)) G) +
        Dφ (phiCx C v) (∑ k ∈ range K, ((k.factorial : ℚ)⁻¹ • (LopC C ^ k)) G) by
      rw [← eS, ← eS'], eS']
  rw [sum_range_succ' (fun k => ((k.factorial : ℚ)⁻¹ • (LopC C ^ k)) (ι ℂ v * G)),
    sum_range_succ' (fun k => ((k.factorial : ℚ)⁻¹ • (LopC C ^ k)) G)]
  simp only [LinearMap.smul_apply, LopC_pow_mul_ι, smul_add, sum_add_distrib, mul_add, mul_sum,
    map_sum, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  have e1 : ∀ k : ℕ, ((k + 1).factorial : ℚ)⁻¹ • (ι ℂ v * (LopC C ^ (k + 1)) G) =
      ι ℂ v * (((k + 1).factorial : ℚ)⁻¹ • (LopC C ^ (k + 1)) G) := fun k => by
    rw [mul_smul_comm]
  have e2 : ∀ k : ℕ, ((k + 1).factorial : ℚ)⁻¹ • (((k + 1 : ℕ) : ℂ) • Dφ (phiCx C v) ((LopC C ^ k) G))
      = Dφ (phiCx C v) ((k.factorial : ℚ)⁻¹ • (LopC C ^ k) G) := fun k => by
    rw [← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ, smul_smul, map_smul]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    field_simp
  simp only [e1, e2]
  abel

/-- The Gaussian moment functional `⟨F⟩_C = (e^{ℒ_C} F)|_{ψ = 0}`. -/
def omegaC (C : Matrix I I ℂ) (F : N I) : ℂ := ε (expLC C F)

/-- Gaussian integration by parts: `⟨ι v G⟩_C = ⟨∂_{φ_v} G⟩_C`. -/
theorem omegaC_ι_mul (C : Matrix I I ℂ) (v : V I) (G : N I) :
    omegaC C (ι ℂ v * G) = omegaC C (Dφ (phiCx C v) G) := by
  have hc := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C) (LopC_isNilpotent C)
    (g := Dφ (phiCx C v)) (LinearMap.ext fun G => LopC_Dφ C _ G)
  have := LinearMap.congr_fun hc G
  simp only [LinearMap.comp_apply] at this
  rw [omegaC, omegaC, expLC_mul_ι, map_add, map_mul, algebraMapInv_ι, zero_mul, zero_add, expLC, this]

/-- `⟨F⟩_C = F|_{ψ=0}` if `F` contains no `ψ̄`. -/
theorem omegaC_eq_of_Dbar (C : Matrix I I ℂ) {F : N I} (hF : ∀ x, D (x, -1) F = 0) :
    omegaC C F = ε F := by
  rw [omegaC, expLC_eq_self]
  rw [LopC_apply]; simp [hF]

theorem phiCx_vbar_vbar (C : Matrix I I ℂ) (b b' : I → ℝ) : phiCx C (vbar b) (vbar b') = 0 := by
  simp [phiCx, vbar, LinearMap.sum_apply]

theorem phiCx_vbar_vpsi (C : Matrix I I ℂ) (b a : I → ℝ) :
    phiCx C (vbar b) (vpsi a) = bil C b a := by
  simp only [phiCx, bil, vbar, vpsi, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.proj_apply]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp [smul_eq_mul]; ring

theorem omegaC_smul (C : Matrix I I ℂ) (c : ℂ) (F : N I) : omegaC C (c • F) = c * omegaC C F := by
  simp [omegaC]

theorem omegaC_add (C : Matrix I I ℂ) (F G : N I) : omegaC C (F + G) = omegaC C F + omegaC C G := by
  simp [omegaC]

/-- `⟨b̄_1 ⋯ b̄_r G⟩_C = (-1)^{r(r-1)/2} (∂_{φ_{b_r}} ⋯ ∂_{φ_{b_1}} G)|_{ψ=0}` for `G` without `ψ̄`. -/
theorem omegaC_ιMulti_vbar_mul (C : Matrix I I ℂ) {r : ℕ} (b : Fin r → I → ℝ) {G : N I}
    (hG : ∀ x, D (x, -1) G = 0) :
    omegaC C (ιMulti ℂ r (fun i => vbar (b i)) * G) =
      (-1 : ℂ) ^ (r * (r - 1) / 2) * ε (contr (fun i => phiCx C (vbar (b i))) G) := by
  induction r generalizing G with
  | zero => simp [ιMulti_zero_apply, omegaC_eq_of_Dbar C hG]
  | succ r ih =>
    rw [ιMulti_succ_apply, mul_assoc, omegaC_ι_mul,
      Dφ_ιMulti_mul (phiCx C (vbar (b 0))) (Matrix.vecTail fun i => vbar (b i))
        (fun i => phiCx_vbar_vbar _ _ _), omegaC_smul, contr_succ]
    have hG' : ∀ x, D (x, -1) (Dφ (phiCx C (vbar (b 0))) G) = 0 := D_vbar_free hG
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
theorem omegaC_moment (C : Matrix I I ℂ) {n : ℕ} (b a : Fin n → I → ℝ) :
    omegaC C (ιMulti ℂ n (fun i => vbar (b i)) * ιMulti ℂ n (fun j => vpsi (a j))) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * (Matrix.of fun i j => bil C (b i) (a j)).det := by
  rw [omegaC_ιMulti_vbar_mul C b (fun x => ?_), algebraMapInv_contr_ιMulti]
  · congr 2
    ext i j
    simp [phiCx_vbar_vpsi]
  · exact contractLeft_ιMulti_eq_zero _ _ fun i => by simp [vpsi]

theorem omegaC_moment_of_ne (C : Matrix I I ℂ) {r s : ℕ} (b : Fin r → I → ℝ) (a : Fin s → I → ℝ)
    (h : r ≠ s) :
    omegaC C (ιMulti ℂ r (fun i => vbar (b i)) * ιMulti ℂ s (fun j => vpsi (a j))) = 0 := by
  rw [omegaC_ιMulti_vbar_mul C b (fun x => ?_), algebraMapInv_contr_ιMulti_of_ne _ _ h, mul_zero]
  exact contractLeft_ιMulti_eq_zero _ _ fun i => by simp [vpsi]


end IBP

section Doubled

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The covariance `C` placed on the `ζ` block. -/
def liftζC (C : Matrix Λ Λ ℂ) : Matrix (Λ ⊕ Λ) (Λ ⊕ Λ) ℂ := Matrix.fromBlocks 0 0 0 C

theorem LζC_eq (C : Matrix Λ Λ ℂ) : LζC C = LopC (liftζC C) := by
  refine LinearMap.ext fun F => ?_
  rw [LζC_apply, LopC_apply, Fintype.sum_sum_type]
  simp [liftζC, Fintype.sum_sum_type]

theorem ECC_eq (C : Matrix Λ Λ ℂ) (F : N (Λ ⊕ Λ)) : ECC C F = proj (expLC (liftζC C) F) := by
  rw [ECC, LinearMap.comp_apply, LζC_eq]; rfl

theorem ECC_ι_mul (C : Matrix Λ Λ ℂ) (w : V (Λ ⊕ Λ)) (G : N (Λ ⊕ Λ)) :
    ECC C (ι ℂ w * G) = proj (ι ℂ w) * ECC C G + ECC C (Dφ (phiCx (liftζC C) w) G) := by
  have hc := Module.End.commute_exp_left_of_commute (LopC_isNilpotent (liftζC C))
    (LopC_isNilpotent (liftζC C)) (g := Dφ (phiCx (liftζC C) w))
    (LinearMap.ext fun G => LopC_Dφ (liftζC C) _ G)
  have := LinearMap.congr_fun hc G
  simp only [LinearMap.comp_apply] at this
  rw [ECC_eq, ECC_eq, ECC_eq, expLC_mul_ι, map_add, map_mul, expLC, this]

theorem phiCx_liftζ_inlV (C : Matrix Λ Λ ℂ) (m : V Λ) : phiCx (liftζC C) (inlV m) = 0 := by
  ext w
  simp [phiCx, liftζC, Fintype.sum_sum_type, inlV]

theorem ECC_incl_ι_mul (C : Matrix Λ Λ ℂ) (m : V Λ) (G : N (Λ ⊕ Λ)) :
    ECC C (ι ℂ (inlV m) * G) = ι ℂ m * ECC C G := by
  rw [ECC_ι_mul, phiCx_liftζ_inlV, Dφ, map_zero, LinearMap.zero_apply, map_zero, add_zero]
  congr 1
  rw [← ExteriorAlgebra.map_apply_ι, ← incl, proj_incl]

/-- `𝔼_C (A G) = A 𝔼_C G` for `A` in the `ψ` variables. -/
theorem ECC_incl_mul (C : Matrix Λ Λ ℂ) (A : N Λ) (G : N (Λ ⊕ Λ)) :
    ECC C (incl A * G) = A * ECC C G := by
  induction A using CliffordAlgebra.induction generalizing G with
  | algebraMap r => simp only [AlgHom.commutes, ← Algebra.smul_def, map_smul]
  | ι m => rw [incl, ExteriorAlgebra.map_apply_ι, ECC_incl_ι_mul]
  | mul a b ha hb => rw [map_mul incl a b, mul_assoc, ha, hb, ← mul_assoc]
  | add a b ha hb => rw [map_add incl a b, add_mul, map_add, ha, hb, add_mul]

theorem ECC_one (C : Matrix Λ Λ ℂ) : ECC C 1 = 1 := by
  rw [ECC_eq, expLC_eq_self, map_one]
  simp [LopC_apply]

theorem LopC_liftζ_inclζ (C : Matrix Λ Λ ℂ) :
    LopC (liftζC C) ∘ₗ inclζ.toLinearMap = inclζ.toLinearMap ∘ₗ LopC C := by
  rw [← LζC_eq]
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LζC_apply, LopC_apply, map_sum,
    map_smul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1
  simp only [D, inclζ]
  rw [contractLeft_map, contractLeft_map, coord_inr_inrV, coord_inr_inrV]

/-- `𝔼_C (B(ζ)) = ⟨B⟩_C`. -/
theorem ECC_inclζ (C : Matrix Λ Λ ℂ) (B : N Λ) :
    ECC C (inclζ B) = algebraMap ℂ (N Λ) (omegaC C B) := by
  have h := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C)
    (LopC_isNilpotent (liftζC C)) (LopC_liftζ_inclζ C)
  have := LinearMap.congr_fun h B
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [ECC_eq, expLC, this, proj_inclζ]; rfl

/-- `𝔼_C (A B(ζ)) = A ⟨B⟩_C`. -/
theorem ECC_incl_mul_inclζ (C : Matrix Λ Λ ℂ) (A B : N Λ) :
    ECC C (incl A * inclζ B) = omegaC C B • A := by
  rw [ECC_incl_mul, ECC_inclζ, Algebra.smul_def, Algebra.commutes]


end Doubled

/-! ### The real operators as a special case -/

section Bridge

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem omega_eq_omegaC (C : Matrix I I ℝ) (F : N I) : omega C F = omegaC (cplx C) F := rfl

theorem bil_cplx (C : Matrix I I ℝ) (b a : I → ℝ) :
    bil (cplx C) b a = ((b ⬝ᵥ (C *ᵥ a) : ℝ) : ℂ) := by
  simp only [bil, dotProduct, mulVec, Matrix.map_apply, mul_sum, Complex.ofReal_sum,
    Complex.ofReal_mul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

end Bridge

end

end Grassmann
