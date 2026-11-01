import H04RG.Model.Defs

/-!
# Algebraic identities for `ℍ^{0|4}`

Lemma 2.1 of `h04/h04-d5-outline.tex`:
`s² = 2q`, `s q = 0`, `q² = 0`, `z² = 1 - 2s`, `z⁻¹ = 1 + s + 3q = exp(s + 2q)`,
`u_x · u_x = -1`, and the edge identity
`2 (u_x · u_y + 1) = 2 ∑_a (ξ^a_x - ξ^a_y)(η^a_x - η^a_y) + (z_x - z_y)²`.
The proofs are in the (commutative) center `H02.C (Λ × Fin 2)`.
-/

namespace H04RG

noncomputable section

open H02 (ξ η dξ dη C cv pc pc_sq cv_injective)

variable {Λ : Type*} [DecidableEq Λ]

/-- The flavour-`a` pair `ξ^a_x η^a_x` in the center. -/
abbrev P (x : Λ) (a : Fin 2) : C (Λ × Fin 2) := pc (x, a) (x, a)

theorem P_sq (x : Λ) (a : Fin 2) : P x a * P x a = 0 := pc_sq (x, a)

/-! ### Identities in the center -/

theorem sC_eq (x : Λ) : sC x = P x 0 + P x 1 := by
  simp [sC, Fin.sum_univ_two]

theorem qC_eq (x : Λ) : qC x = P x 0 * P x 1 := rfl

theorem sC_sq (x : Λ) : sC x * sC x = 2 * qC x := by
  rw [sC_eq, qC_eq]
  linear_combination P_sq x 0 + P_sq x 1

theorem sC_mul_qC (x : Λ) : sC x * qC x = 0 := by
  rw [sC_eq, qC_eq]
  linear_combination P x 1 * P_sq x 0 + P x 0 * P_sq x 1

theorem qC_sq (x : Λ) : qC x * qC x = 0 := by
  rw [qC_eq]
  linear_combination P x 1 * P x 1 * P_sq x 0

/-- `z_x² = 1 - 2 s_x`, i.e. `z_x = √(1 - 2 s_x)`. -/
theorem zC_sq (x : Λ) : zC x * zC x = 1 - 2 * sC x := by
  rw [zC]
  linear_combination sC_sq x + 2 * sC_mul_qC x + qC_sq x

/-- `z_x (1 + s_x + 3 q_x) = 1`. -/
theorem zC_mul_inv (x : Λ) : zC x * (1 + sC x + 3 * qC x) = 1 := by
  rw [zC]
  linear_combination (-1 : C (Λ × Fin 2)) * sC_sq x - 4 * sC_mul_qC x - 3 * qC_sq x

theorem isUnit_zC (x : Λ) : IsUnit (zC x) :=
  (Units.mkOfMulEqOne _ _ (zC_mul_inv x)).isUnit

/-- `z_x⁻¹ = 1 + s_x + 3 q_x`. -/
theorem inverse_zC (x : Λ) : Ring.inverse (zC x) = 1 + sC x + 3 * qC x := by
  exact (Ring.inverse_unit (Units.mkOfMulEqOne _ _ (zC_mul_inv x))).trans rfl

theorem inverse_zC_mul_zC (x : Λ) : Ring.inverse (zC x) * zC x = 1 := by
  rw [inverse_zC, mul_comm, zC_mul_inv]

/-- `z_x⁻¹ = exp(s_x + 2 q_x)`. -/
theorem exp_eq_inverse_zC (x : Λ) :
    IsNilpotent.exp (sC x + 2 * qC x) = Ring.inverse (zC x) := by
  have h2 : (sC x + 2 * qC x) ^ 2 = 2 * qC x := by
    linear_combination sC_sq x + 4 * sC_mul_qC x + 4 * qC_sq x
  have h3 : (sC x + 2 * qC x) ^ 3 = 0 := by
    rw [pow_succ, h2]
    linear_combination 2 * sC_mul_qC x + 4 * qC_sq x
  have hq : (2 : ℚ)⁻¹ • (2 * qC x) = qC x := by
    rw [show (2 : C (Λ × Fin 2)) * qC x = (2 : ℚ) • qC x by rw [two_smul, two_mul], smul_smul]
    norm_num
  rw [IsNilpotent.exp_eq_sum h3, inverse_zC]
  simp [Finset.sum_range_succ, h2, hq]
  ring

/-- The inner product in the center. -/
def dotC (x y : Λ) : C (Λ × Fin 2) :=
  -(∑ a : Fin 2, (pc (x, a) (y, a) + pc (y, a) (x, a))) - zC x * zC y

@[simp] theorem cv_dotC (x y : Λ) : cv (dotC x y) = dot x y := by simp [dotC, dot]

/-- `u_x · u_x = -1`. -/
theorem dotC_self (x : Λ) : dotC x x = -1 := by
  have : ∑ a : Fin 2, (pc (x, a) (x, a) + pc (x, a) (x, a)) = 2 * sC x := by
    rw [sC_eq]; simp [Fin.sum_univ_two]; ring
  rw [dotC, this]
  linear_combination (-1 : C (Λ × Fin 2)) * zC_sq x

/-- `(ξ^a_x - ξ^a_y)(η^a_x - η^a_y)` in the center. -/
def gradC (x y : Λ) (a : Fin 2) : C (Λ × Fin 2) :=
  pc (x, a) (x, a) - pc (x, a) (y, a) - pc (y, a) (x, a) + pc (y, a) (y, a)

theorem cv_gradC (x y : Λ) (a : Fin 2) :
    cv (gradC x y a) = (ξ (x, a) - ξ (y, a)) * (η (x, a) - η (y, a)) := by
  simp [gradC]; noncomm_ring

/-- The edge identity `2 (u_x · u_y + 1) = 2 ∑_a ∇ξ^a ∇η^a + (∇z)²`. -/
theorem dotC_edge (x y : Λ) :
    2 * (dotC x y + 1) = 2 * ∑ a : Fin 2, gradC x y a + (zC x - zC y) ^ 2 := by
  have hs : ∀ v : Λ, ∑ a : Fin 2, pc (v, a) (v, a) = sC v := fun v => rfl
  simp only [dotC, gradC, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
  linear_combination (-1 : C (Λ × Fin 2)) * zC_sq x - zC_sq y

end

end H04RG
