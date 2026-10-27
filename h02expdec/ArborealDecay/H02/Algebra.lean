module

public import ArborealDecay.H02.Defs

/-!
# Algebraic facts about the Grassmann algebra and the fermionic integral
-/

@[expose] public section

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open CliffordAlgebra

section General

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The grade involution of the exterior algebra. -/
abbrev inv' : ExteriorAlgebra ℝ M →ₐ[ℝ] ExteriorAlgebra ℝ M := CliffordAlgebra.involute

theorem inv'_ι (m : M) : inv' (ExteriorAlgebra.ι ℝ m) = -ExteriorAlgebra.ι ℝ m :=
  involute_ι m

theorem ι_anticomm (m n : M) :
    ExteriorAlgebra.ι ℝ m * ExteriorAlgebra.ι ℝ n = -(ExteriorAlgebra.ι ℝ n * ExteriorAlgebra.ι ℝ m) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m n)

theorem ι_mul_eq (m : M) (x : ExteriorAlgebra ℝ M) :
    ExteriorAlgebra.ι ℝ m * x = inv' x * ExteriorAlgebra.ι ℝ m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι n => rw [inv'_ι, neg_mul, ← ι_anticomm]
  | mul a b ha hb => rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]

/-- Even elements are central. -/
theorem mul_comm_of_even {x : ExteriorAlgebra ℝ M} (hx : inv' x = x) (y : ExteriorAlgebra ℝ M) :
    x * y = y * x := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r x).symm
  | ι n => rw [ι_mul_eq, hx]
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, add_mul]

theorem mem_center_of_even {x : ExteriorAlgebra ℝ M} (hx : inv' x = x) :
    x ∈ Subalgebra.center ℝ (ExteriorAlgebra ℝ M) :=
  Subalgebra.mem_center_iff.2 fun y => (mul_comm_of_even hx y).symm

/-- The Leibniz rule for the odd derivation `contractLeft d`. -/
theorem contractLeft_mul (d : Module.Dual ℝ M) (a b : ExteriorAlgebra ℝ M) :
    contractLeft d (a * b) = contractLeft d a * b + inv' a * contractLeft d b := by
  induction a using CliffordAlgebra.induction generalizing b with
  | algebraMap r =>
    rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, AlgHom.commutes]; simp
  | ι m =>
    rw [contractLeft_ι_mul, contractLeft_ι, inv'_ι, Algebra.smul_def]; noncomm_ring
  | mul a₁ a₂ h₁ h₂ =>
    rw [mul_assoc, h₁, h₂, h₁ a₂, map_mul]; noncomm_ring
  | add a₁ a₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, map_add]; noncomm_ring

end General

variable {Λ : Type*} [DecidableEq Λ]

local notation "A" => Grassmann Λ

/-! ### Generators -/

@[simp] theorem inv'_ξ (i : Λ) : inv' (ξ i) = -ξ i := inv'_ι _
@[simp] theorem inv'_η (i : Λ) : inv' (η i) = -η i := inv'_ι _

theorem dξ_ξ (i j : Λ) : dξ i (ξ j) = if i = j then 1 else 0 := by
  simp only [dξ, ξ, ExteriorAlgebra.ι, contractLeft_ι, LinearMap.proj_apply]
  by_cases h : i = j <;> simp [h]

theorem dξ_η (i j : Λ) : dξ i (η j) = 0 := by
  simp [dξ, η, ExteriorAlgebra.ι, contractLeft_ι]

theorem dη_ξ (i j : Λ) : dη i (ξ j) = 0 := by
  simp [dη, ξ, ExteriorAlgebra.ι, contractLeft_ι]

theorem dη_η (i j : Λ) : dη i (η j) = if i = j then 1 else 0 := by
  simp only [dη, η, ExteriorAlgebra.ι, contractLeft_ι, LinearMap.proj_apply]
  by_cases h : i = j <;> simp [h]

theorem dξ_mul (i : Λ) (a b : A) : dξ i (a * b) = dξ i a * b + inv' a * dξ i b :=
  contractLeft_mul _ a b

theorem dη_mul (i : Λ) (a b : A) : dη i (a * b) = dη i a * b + inv' a * dη i b :=
  contractLeft_mul _ a b

@[simp] theorem dξ_one (i : Λ) : dξ i (1 : A) = 0 := by simp [dξ]

theorem dξ_dξ (i : Λ) (x : A) : dξ i (dξ i x) = 0 := contractLeft_contractLeft _ _
theorem dξ_comm_dη (i j : Λ) (x : A) : dξ i (dη j x) = -dη j (dξ i x) := contractLeft_comm _ _ _
theorem dξ_comm_dξ (i j : Λ) (x : A) : dξ i (dξ j x) = -dξ j (dξ i x) := contractLeft_comm _ _ _
theorem dη_comm_dη (i j : Λ) (x : A) : dη i (dη j x) = -dη j (dη i x) := contractLeft_comm _ _ _
theorem dη_comm_dξ (i j : Λ) (x : A) : dη i (dξ j x) = -dξ j (dη i x) := contractLeft_comm _ _ _

theorem ξ_mul_ξ (i : Λ) : ξ i * ξ i = (0 : A) := ExteriorAlgebra.ι_sq_zero _
theorem η_mul_η (i : Λ) : η i * η i = (0 : A) := ExteriorAlgebra.ι_sq_zero _

theorem ξ_anticomm_η (i j : Λ) : ξ i * η j = -(η j * ξ i : A) := ι_anticomm _ _
theorem η_anticomm_ξ (i j : Λ) : η i * ξ j = -(ξ j * η i : A) := ι_anticomm _ _
theorem η_anticomm_η (i j : Λ) : η i * η j = -(η j * η i : A) := ι_anticomm _ _

/-- The product `ξ_i η_j` is even. -/
theorem inv'_ξη (i j : Λ) : inv' (ξ i * η j) = ξ i * η j := by simp

/-- The rearrangement identity `ξ_i η_j ξ_k η_l = - ξ_i η_l ξ_k η_j`. -/
theorem ξη_rel (i j k l : Λ) :
    ξ i * η j * (ξ k * η l) = -(ξ i * η l * (ξ k * η j) : A) := by
  have e1 : ξ i * η j * (ξ k * η l) = ξ i * (η j * ξ k) * η l := by noncomm_ring
  have e2 : ξ i * η l * (ξ k * η j) = ξ i * (η l * ξ k) * η j := by noncomm_ring
  rw [e1, e2, η_anticomm_ξ, η_anticomm_ξ]
  have e3 : ξ i * -(ξ k * η j) * η l = -(ξ i * ξ k * (η j * η l)) := by noncomm_ring
  have e4 : ξ i * -(ξ k * η l) * η j = -(ξ i * ξ k * (η l * η j)) := by noncomm_ring
  rw [e3, e4, η_anticomm_η j l]; noncomm_ring

end

end H02

end
