import Grassmann.Gaussian

/-!
# Gaussian integration by parts

For a vector `v` of generators, `ℒ_C (ι v G) = ι v ℒ_C G + ∂_{φ_v} G`, where
`φ_v(w) = ∑_{x,y} C_{xy} (v_{x,-} w_{y,+} - v_{y,+} w_{x,-})` (`Lop_mul_ι`), and `∂_{φ_v}`
commutes with `ℒ_C`.  Consequently `e^{ℒ_C} (ι v G) = ι v e^{ℒ_C} G + ∂_{φ_v} e^{ℒ_C} G`
(`expL_mul_ι`), which yields the Gaussian integration by parts formulas
`⟨ι v G⟩_C = ⟨∂_{φ_v} G⟩_C` for `⟨F⟩_C = (e^{ℒ_C} F)|_{ψ=0}` (`omega_ι_mul`) and
`𝔼_C (ζ̄_x G) = ∑_y C_{xy} 𝔼_C (∂_{ζ_y} G)`, `𝔼_C (ζ_y G) = -∑_x C_{xy} 𝔼_C (∂_{ζ̄_x} G)`,
`𝔼_C (ψ_a G) = ψ_a 𝔼_C G` for the doubled algebra.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- The functional `φ_v(w) = ∑_{x,y} C_{xy} (v_{x,-} w_{y,+} - v_{y,+} w_{x,-})`. -/
def phiC (C : Matrix I I ℝ) (v : V I) : Module.Dual ℂ (V I) :=
  ∑ x, ∑ y, (C x y : ℂ) • (v (x, -1) • coord (y, 1) - v (y, 1) • coord (x, -1))

/-- `∂_φ` for a general functional. -/
abbrev Dφ (φ : Module.Dual ℂ (V I)) : N I →ₗ[ℂ] N I := contractLeft φ

theorem Dφ_smul (c : ℂ) (φ : Module.Dual ℂ (V I)) (x : N I) : Dφ (c • φ) x = c • Dφ φ x := by
  simp [Dφ]

theorem Dφ_sum {ι : Type*} (s : Finset ι) (φ : ι → Module.Dual ℂ (V I)) (x : N I) :
    Dφ (∑ i ∈ s, φ i) x = ∑ i ∈ s, Dφ (φ i) x := by
  simp [Dφ, map_sum, LinearMap.sum_apply]

theorem DD_ι_mul (a b : Sf I) (v : V I) (G : N I) :
    D b (D a (ι ℂ v * G)) = ι ℂ v * D b (D a G) + v a • D b G - v b • D a G := by
  simp only [D, contractLeft_ι_mul, map_sub, map_smul, LinearMap.proj_apply]; abel

theorem Dφ_apply_sum (C : Matrix I I ℝ) (v : V I) (G : N I) :
    Dφ (phiC C v) G = ∑ x, ∑ y, (C x y : ℂ) • (v (x, -1) • D (y, 1) G - v (y, 1) • D (x, -1) G) := by
  simp only [phiC, Dφ, map_sum, map_smul, map_sub, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, D]

theorem Lop_mul_ι (C : Matrix I I ℝ) (v : V I) (G : N I) :
    Lop C (ι ℂ v * G) = ι ℂ v * Lop C G + Dφ (phiC C v) G := by
  rw [Lop_apply, Lop_apply, Dφ_apply_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [DD_ι_mul, mul_smul_comm]
  module

/-- `∂_φ` commutes with `ℒ_C`. -/
theorem Lop_Dφ (C : Matrix I I ℝ) (φ : Module.Dual ℂ (V I)) (G : N I) :
    Lop C (Dφ φ G) = Dφ φ (Lop C G) := by
  rw [Lop_apply, Lop_apply, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [map_smul]
  congr 1
  simp only [D, Dφ]
  rw [contractLeft_comm φ, contractLeft_comm φ, map_neg, neg_neg]

theorem Lop_pow_mul_ι (C : Matrix I I ℝ) (v : V I) (G : N I) (k : ℕ) :
    (Lop C ^ (k + 1)) (ι ℂ v * G) =
      ι ℂ v * (Lop C ^ (k + 1)) G + ((k + 1 : ℕ) : ℂ) • Dφ (phiC C v) ((Lop C ^ k) G) := by
  induction k with
  | zero => simp [Lop_mul_ι]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, Lop_mul_ι, map_smul, Lop_Dφ,
      ← Module.End.mul_apply (Lop C) (Lop C ^ (k + 1)), ← pow_succ',
      ← Module.End.mul_apply (Lop C) (Lop C ^ k), ← pow_succ']
    push_cast
    module

/-- `e^{ℒ_C} (ι v G) = ι v e^{ℒ_C} G + ∂_{φ_v} e^{ℒ_C} G`. -/
theorem expL_mul_ι (C : Matrix I I ℝ) (v : V I) (G : N I) :
    expL C (ι ℂ v * G) = ι ℂ v * expL C G + Dφ (phiC C v) (expL C G) := by
  set K := Nf I + 1
  have hK : Lop C ^ K = 0 := Lop_pow_eq_zero C
  have h2 : Lop C ^ (K + 1) = 0 := by rw [pow_succ, hK, zero_mul]
  have eS : ∀ H, expL C H = ∑ k ∈ range K, ((k.factorial : ℚ)⁻¹ • (Lop C ^ k)) H := fun H => by
    rw [expL, IsNilpotent.exp_eq_sum hK, LinearMap.sum_apply]
  have eS' : ∀ H, expL C H = ∑ k ∈ range (K + 1), ((k.factorial : ℚ)⁻¹ • (Lop C ^ k)) H :=
    fun H => by rw [expL, IsNilpotent.exp_eq_sum h2, LinearMap.sum_apply]
  rw [show ι ℂ v * expL C G + Dφ (phiC C v) (expL C G) =
      ι ℂ v * (∑ k ∈ range (K + 1), ((k.factorial : ℚ)⁻¹ • (Lop C ^ k)) G) +
        Dφ (phiC C v) (∑ k ∈ range K, ((k.factorial : ℚ)⁻¹ • (Lop C ^ k)) G) by
      rw [← eS, ← eS'], eS']
  rw [sum_range_succ' (fun k => ((k.factorial : ℚ)⁻¹ • (Lop C ^ k)) (ι ℂ v * G)),
    sum_range_succ' (fun k => ((k.factorial : ℚ)⁻¹ • (Lop C ^ k)) G)]
  simp only [LinearMap.smul_apply, Lop_pow_mul_ι, smul_add, sum_add_distrib, mul_add, mul_sum,
    map_sum, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  have e1 : ∀ k : ℕ, ((k + 1).factorial : ℚ)⁻¹ • (ι ℂ v * (Lop C ^ (k + 1)) G) =
      ι ℂ v * (((k + 1).factorial : ℚ)⁻¹ • (Lop C ^ (k + 1)) G) := fun k => by
    rw [mul_smul_comm]
  have e2 : ∀ k : ℕ, ((k + 1).factorial : ℚ)⁻¹ • (((k + 1 : ℕ) : ℂ) • Dφ (phiC C v) ((Lop C ^ k) G))
      = Dφ (phiC C v) ((k.factorial : ℚ)⁻¹ • (Lop C ^ k) G) := fun k => by
    rw [← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ, smul_smul, map_smul]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    field_simp
  simp only [e1, e2]
  abel

/-- The Gaussian moment functional `⟨F⟩_C = (e^{ℒ_C} F)|_{ψ = 0}`. -/
def omega (C : Matrix I I ℝ) (F : N I) : ℂ := ε (expL C F)

/-- Gaussian integration by parts: `⟨ι v G⟩_C = ⟨∂_{φ_v} G⟩_C`. -/
theorem omega_ι_mul (C : Matrix I I ℝ) (v : V I) (G : N I) :
    omega C (ι ℂ v * G) = omega C (Dφ (phiC C v) G) := by
  have hc := Module.End.commute_exp_left_of_commute (Lop_isNilpotent C) (Lop_isNilpotent C)
    (g := Dφ (phiC C v)) (LinearMap.ext fun G => Lop_Dφ C _ G)
  have := LinearMap.congr_fun hc G
  simp only [LinearMap.comp_apply] at this
  rw [omega, omega, expL_mul_ι, map_add, map_mul, algebraMapInv_ι, zero_mul, zero_add, expL, this]

/-- `⟨F⟩_C = F|_{ψ=0}` if `F` contains no `ψ̄`. -/
theorem omega_eq_of_Dbar (C : Matrix I I ℝ) {F : N I} (hF : ∀ x, D (x, -1) F = 0) :
    omega C F = ε F := by
  rw [omega, expL_eq_self]
  rw [Lop_apply]; simp [hF]

end

end Grassmann
