import Mathlib

/-!
# General facts about exterior algebras and their contractions

For a module `M` over a commutative ring `R`, the contraction `contractLeft φ` with a linear
functional `φ` is the odd derivation of `ExteriorAlgebra R M` with `contractLeft φ (ι v) = φ v`.

The main result is `algebraMapInv_contr_ιMulti`: the constant term of
`∂_{φ_n} ⋯ ∂_{φ_1} (ι v_1 ⋯ ι v_n)` is `det (φ_i (v_j))`.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M

/-- The grade involution. -/
abbrev inv' : E →ₐ[R] E := CliffordAlgebra.involute

theorem inv'_ι (m : M) : inv' (ι R m) = -ι R m := involute_ι m

theorem inv'_inv' (x : E) : inv' (inv' x) = x := involute_involute x

theorem ι_anticomm (m n : M) : ι R m * ι R n = -(ι R n * ι R m) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m n)

theorem ι_mul_eq (m : M) (x : E) : ι R m * x = inv' x * ι R m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι n => rw [inv'_ι, neg_mul, ← ι_anticomm]
  | mul a b ha hb => rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]

/-- Even elements are central. -/
theorem mul_comm_of_even {x : E} (hx : inv' x = x) (y : E) : x * y = y * x := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r x).symm
  | ι n => rw [ι_mul_eq, hx]
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, add_mul]

/-- The Leibniz rule for the odd derivation `contractLeft d`. -/
theorem contractLeft_mul (d : Module.Dual R M) (a b : E) :
    contractLeft d (a * b) = contractLeft d a * b + inv' a * contractLeft d b := by
  induction a using CliffordAlgebra.induction generalizing b with
  | algebraMap r =>
    rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, AlgHom.commutes]; simp
  | ι m =>
    rw [contractLeft_ι_mul, contractLeft_ι, inv'_ι, Algebra.smul_def]; noncomm_ring
  | mul a₁ a₂ h₁ h₂ =>
    rw [mul_assoc, h₁, h₂, h₁ a₂, map_mul]; noncomm_ring
  | add a₁ a₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, map_add]; noncomm_ring

/-- Contractions anticommute with the grade involution. -/
theorem contractLeft_inv' (d : Module.Dual R M) (a : E) :
    contractLeft d (inv' a) = -inv' (contractLeft d a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [contractLeft_ι]
  | mul a b ha hb =>
    rw [map_mul, contractLeft_mul, contractLeft_mul, ha, hb, map_add, map_mul, map_mul,
      inv'_inv']; noncomm_ring
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]; abel

@[simp] theorem algebraMapInv_ι (m : M) : algebraMapInv (ι R m : E) = 0 := by
  simp [algebraMapInv]

theorem algebraMapInv_inv' (x : E) : algebraMapInv (inv' x) = algebraMapInv x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-! ### Contraction of `ιMulti` -/

/-- `∂_φ (ι v_0 ⋯ ι v_n) = ∑_j (-1)^j φ(v_j) ι v_0 ⋯ \hat{ι v_j} ⋯ ι v_n`. -/
theorem contractLeft_ιMulti (φ : Module.Dual R M) {n : ℕ} (v : Fin (n + 1) → M) :
    contractLeft φ (ιMulti R (n + 1) v) =
      ∑ j : Fin (n + 1), ((-1 : R) ^ (j : ℕ) * φ (v j)) • ιMulti R n (v ∘ j.succAbove) := by
  induction n with
  | zero =>
    rw [ιMulti_succ_apply, ιMulti_zero_apply, mul_one, contractLeft_ι, Fin.sum_univ_one,
      ιMulti_zero_apply]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    rw [ιMulti_succ_apply, contractLeft_ι_mul, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hv : v ∘ j.succ.succAbove = Fin.cons (v 0) (Matrix.vecTail v ∘ j.succAbove) := by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp
        · simp [Matrix.vecTail]
      rw [hv, ιMulti_succ_apply, mul_smul_comm, ← neg_smul]
      simp only [Fin.cons_zero, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_mul]
      congr 3

/-- Iterated contraction `∂_{φ_{m-1}} ⋯ ∂_{φ_0}` (with `∂_{φ_0}` applied first). -/
def contr : {m : ℕ} → (Fin m → Module.Dual R M) → E →ₗ[R] E
  | 0, _ => LinearMap.id
  | _ + 1, φ => contr (Fin.tail φ) ∘ₗ contractLeft (φ 0)

@[simp] theorem contr_zero (φ : Fin 0 → Module.Dual R M) : contr φ = LinearMap.id := rfl

theorem contr_succ {m : ℕ} (φ : Fin (m + 1) → Module.Dual R M) (x : E) :
    contr φ x = contr (Fin.tail φ) (contractLeft (φ 0) x) := rfl

theorem algebraMapInv_ιMulti_succ {n : ℕ} (v : Fin (n + 1) → M) :
    algebraMapInv (ιMulti R (n + 1) v) = 0 := by
  rw [ιMulti_succ_apply, map_mul, algebraMapInv_ι, zero_mul]

/-- The constant term of `∂_{φ_{n-1}} ⋯ ∂_{φ_0} (ι v_0 ⋯ ι v_{n-1})` is `det (φ_i (v_j))`. -/
theorem algebraMapInv_contr_ιMulti {n : ℕ} (φ : Fin n → Module.Dual R M) (v : Fin n → M) :
    algebraMapInv (contr φ (ιMulti R n v)) = (Matrix.of fun i j => φ i (v j)).det := by
  induction n with
  | zero => simp [ιMulti_zero_apply]
  | succ n ih =>
    rw [contr_succ, contractLeft_ιMulti, map_sum, map_sum, Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, AlgHom.map_smul_of_tower, ih, smul_eq_mul]
    simp [Matrix.submatrix, Fin.tail]

/-- The constant term of `∂_{φ_{m-1}} ⋯ ∂_{φ_0} (ι v_0 ⋯ ι v_{n-1})` vanishes if `m ≠ n`. -/
theorem algebraMapInv_contr_ιMulti_of_ne {m n : ℕ} (φ : Fin m → Module.Dual R M)
    (v : Fin n → M) (h : m ≠ n) : algebraMapInv (contr φ (ιMulti R n v)) = 0 := by
  induction m generalizing n with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Ne.symm h)
    exact algebraMapInv_ιMulti_succ v
  | succ m ih =>
    cases n with
    | zero => simp [contr_succ, ιMulti_zero_apply]
    | succ n =>
      rw [contr_succ, contractLeft_ιMulti, map_sum, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [LinearMap.map_smul, AlgHom.map_smul_of_tower, ih _ _ (by omega), smul_zero]

/-- A contraction by a functional vanishing on all factors kills `ι v_0 ⋯ ι v_{n-1}`. -/
theorem contractLeft_ιMulti_eq_zero (φ : Module.Dual R M) {n : ℕ} (v : Fin n → M)
    (h : ∀ i, φ (v i) = 0) : contractLeft φ (ιMulti R n v) = 0 := by
  cases n with
  | zero => simp [ιMulti_zero_apply]
  | succ n =>
    rw [contractLeft_ιMulti]
    exact Finset.sum_eq_zero fun j _ => by rw [h, mul_zero, zero_smul]

end

end Grassmann
