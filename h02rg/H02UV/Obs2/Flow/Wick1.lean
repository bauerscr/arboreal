import Obs2.Flow.FlowMu
import Step2.Coup.BubbleX

/-!
# Exact Wick identities for the observable vertices (`h02uv-outline.tex`, Lemma `lem:second`)

**Conjugation by `e^{𝓛}`** (`exp_mul_conj`, pure algebra): if `[T, M] = D₁`, `[T, D₁] = D₂`,
`[T, D₂] = 0` with `T` nilpotent, then `e^T M = (M + D₁ + ½ D₂) e^T`.

Applied to `T = 𝓛_C` and `M` = left multiplication:
* **a linear form** `ι v` (`FC_lin`): `F_C(ι v, B) = -Xc_C(ι v, B)` for **every** `B` (a single
  line). In particular `F_C(ψ̄_a, B) = ∑_y C(a,y) ∂_{ψ_y} B` (`FC_psibar`), hence
  `m₁ F_C(ψ̄_a, B) = ∑_y C(a, y) m₁(∂_{ψ_y} B)`, and `m₁ F_C(ψ̄_a, B) = 0` for `B` homogeneous of
  degree `≠ 2` (`mass1_FC_psibar_hom`; Lemma `lem:second`(iii), first part, for the quartic);
* **a pair** `A = ι u ι w` (`FC_pair`): `F_C(A, B) = Xc_C(A, B) + ½ X₂(A, B)` for every `B`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 LocObs

/-! ### Conjugation of a nilpotent exponential -/

section Conj

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- The partial exponential sums `S n = ∑_{i<n} T^i/i!`. -/
def expSum (T : R) (n : ℕ) : R := ∑ i ∈ range n, ((i.factorial : ℚ)⁻¹) • T ^ i

theorem pow_mul_M {T M D₁ D₂ : R} (h1 : T * M = M * T + D₁) (h2 : T * D₁ = D₁ * T + D₂)
    (h3 : T * D₂ = D₂ * T) :
    ∀ n : ℕ, T ^ (n + 2) * M = M * T ^ (n + 2) + ((n : ℚ) + 2) • (D₁ * T ^ (n + 1)) +
      (((n : ℚ) + 2) * ((n : ℚ) + 1) / 2) • (D₂ * T ^ n)
  | 0 => by
    simp only [Nat.cast_zero, zero_add, pow_one, pow_zero, mul_one]
    rw [pow_two, mul_assoc, h1, mul_add, ← mul_assoc, h1, h2]
    simp only [add_mul, mul_assoc]
    module
  | n + 1 => by
    rw [pow_succ' T (n + 2), mul_assoc, pow_mul_M h1 h2 h3 n, mul_add, mul_add, ← mul_assoc, h1,
      mul_smul_comm, ← mul_assoc, h2, mul_smul_comm, ← mul_assoc, h3]
    simp only [add_mul, mul_assoc, ← pow_succ', smul_add]
    simp only [add_assoc, Nat.reduceAdd]
    push_cast
    module

theorem fact_succ_inv (n : ℕ) :
    (((n + 2).factorial : ℚ)⁻¹) * ((n : ℚ) + 2) = (((n + 1).factorial : ℚ)⁻¹) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ (n + 1)]; push_cast
  have : ((n + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

theorem fact_two_inv (n : ℕ) :
    (((n + 2).factorial : ℚ)⁻¹) * (((n : ℚ) + 2) * ((n : ℚ) + 1) / 2) =
      (1 / 2 : ℚ) * ((n.factorial : ℚ)⁻¹) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  ring

theorem expSum_succ (T : R) (n : ℕ) :
    expSum T (n + 1) = expSum T n + ((n.factorial : ℚ)⁻¹) • T ^ n := by
  simp only [expSum]; rw [sum_range_succ]

theorem expSum_mul {T M D₁ D₂ : R} (h1 : T * M = M * T + D₁) (h2 : T * D₁ = D₁ * T + D₂)
    (h3 : T * D₂ = D₂ * T) :
    ∀ n : ℕ, expSum T (n + 2) * M = M * expSum T (n + 2) + D₁ * expSum T (n + 1) +
      (1 / 2 : ℚ) • (D₂ * expSum T n)
  | 0 => by
    simp only [expSum, sum_range_succ, range_zero, sum_empty, zero_add, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_zero, pow_one, mul_zero, smul_zero,
      add_zero]
    rw [add_mul, one_mul, h1, mul_add, mul_one, mul_one]; abel
  | n + 1 => by
    have ih := expSum_mul h1 h2 h3 n
    rw [show n + 1 + 2 = (n + 2) + 1 from rfl, expSum_succ T (n + 2), add_mul, ih, smul_mul_assoc,
      pow_mul_M h1 h2 h3 n, smul_add, smul_add, smul_smul, smul_smul, fact_succ_inv,
      fact_two_inv, show n + 1 + 1 = n + 2 from rfl, expSum_succ T (n + 1), expSum_succ T n]
    simp only [mul_add, mul_smul_comm, smul_add, smul_smul]
    module

/-- **Conjugation of a nilpotent exponential.** -/
theorem exp_mul_conj {T M D₁ D₂ : R} (hT : IsNilpotent T) (h1 : T * M = M * T + D₁)
    (h2 : T * D₁ = D₁ * T + D₂) (h3 : T * D₂ = D₂ * T) :
    IsNilpotent.exp T * M = (M + D₁ + (1 / 2 : ℚ) • D₂) * IsNilpotent.exp T := by
  obtain ⟨k, hk⟩ := hT
  have hk1 : T ^ (k + 1) = 0 := pow_eq_zero_of_le (by omega) hk
  have hk2 : T ^ (k + 2) = 0 := pow_eq_zero_of_le (by omega) hk
  have hE : IsNilpotent.exp T = expSum T (k + 2) := IsNilpotent.exp_eq_sum hk2
  have e1 : expSum T (k + 2) = expSum T (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, expSum_succ, hk1, smul_zero, add_zero]
  have e2 : expSum T (k + 1) = expSum T k := by
    rw [expSum_succ, hk, smul_zero, add_zero]
  rw [hE, expSum_mul h1 h2 h3 k, ← e1, ← e2, ← e1, add_mul, add_mul, smul_mul_assoc]

end Conj

/-! ### A linear form: a single line -/

section Lin

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)

local notation "ι" => (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] Grassmann.N Λ)

/-- The single cross contraction with a linear form is a first-order derivation. -/
theorem Xc_lin (v : V Λ) (Q : Grassmann.N Λ) :
    Xc C (ι v) Q = ∑ x, ∑ y, C x y • (v (y, 1) • D (x, -1) Q - v (x, -1) • D (y, 1) Q) := by
  unfold Xc
  simp only [D_ι, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem LopC_Xc_lin (v : V Λ) (Q : Grassmann.N Λ) :
    LopC C (Xc C (ι v) Q) = Xc C (ι v) (LopC C Q) := by
  rw [Xc_lin, Xc_lin]
  simp only [map_sum, map_smul, map_sub, LopC_D]

theorem LopC_mul_lin (v : V Λ) (Q : Grassmann.N Λ) :
    LopC C (ι v * Q) = ι v * LopC C Q - Xc C (ι v) Q := by
  rw [LopC_mul_odd C (Step2.inv'_ι v) Q, LopC_lin, zero_mul, zero_add]

/-- `e^{𝓛}(ι v · Y) = ι v · e^{𝓛} Y - Xc(ι v, e^{𝓛} Y)`. -/
theorem expLC_mul_lin (v : V Λ) (Y : Grassmann.N Λ) :
    expLC C (ι v * Y) = ι v * expLC C Y - Xc C (ι v) (expLC C Y) := by
  have h1 : LopC C * LinearMap.mulLeft ℂ (ι v) =
      LinearMap.mulLeft ℂ (ι v) * LopC C + -XcL C (ι v) := by
    refine LinearMap.ext fun Q => ?_
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.add_apply,
      LinearMap.neg_apply, XcL_apply, LopC_mul_lin, sub_eq_add_neg]
  have h2 : LopC C * -XcL C (ι v) = -XcL C (ι v) * LopC C + 0 := by
    refine LinearMap.ext fun Q => ?_
    simp only [Module.End.mul_apply, LinearMap.neg_apply, XcL_apply, map_neg, LopC_Xc_lin,
      add_zero]
  have h3 : LopC C * (0 : Module.End ℂ (Grassmann.N Λ)) = 0 * LopC C := by simp
  have h := LinearMap.congr_fun (exp_mul_conj (LopC_isNilpotent C) h1 h2 h3) Y
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, smul_zero, add_zero,
    LinearMap.add_apply, LinearMap.neg_apply, XcL_apply] at h
  rw [h, sub_eq_add_neg]

/-- **`F_C` with a linear form is a single line**: `F_C(ι v, B) = -Xc_C(ι v, B)`. -/
theorem FC_lin (v : V Λ) (B : Grassmann.N Λ) : FC C (ι v) B = -Xc C (ι v) B := by
  rw [FC, expLC_lin (-C) v, expLC_mul_lin, expLC_expLC_neg]; abel

/-- `F_C(ψ̄_a, B) = ∑_y C(a, y) ∂_{ψ_y} B`. -/
theorem FC_psibar (a : Λ) (B : Grassmann.N Λ) :
    FC C (psibar a) B = ∑ y, C a y • D (y, 1) B := by
  have e : (psibar a : Grassmann.N Λ) = ι (ev (a, -1)) := rfl
  have hv1 : ∀ y : Λ, ev ((a, -1) : Sf Λ) (y, 1) = 0 := fun y => by
    simp [ev, Pi.single_apply, Prod.ext_iff]
  have hv2 : ∀ x : Λ, ev ((a, -1) : Sf Λ) (x, -1) = if x = a then 1 else 0 := fun x => by
    simp [ev, Pi.single_apply, Prod.ext_iff]
  rw [e, FC_lin, Xc_lin]
  simp only [hv1, hv2, zero_smul, zero_sub, ite_smul, one_smul, smul_neg, sum_neg_distrib,
    neg_neg, smul_ite, smul_zero]
  rw [Fintype.sum_eq_single a (fun x hx => by simp [hx])]
  simp

end Lin

/-! ### Mass coefficients -/

section Mass

variable {d L N : ℕ} [NeZero L] (C : Matrix (Lam d L N) (Lam d L N) ℂ)

theorem mass1_D (s : ℤˣ) (y : Lam d L N) (B : Alg d L N) :
    mass1 s (D (y, 1) B) = ∑ x, coeff B ![(y, 1), (x, s)] := by
  unfold mass1
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_D]
  congr 1

/-- `m₁ F_C(ψ̄_a, B) = ∑_y C(a, y) ∑_x [ψ_y ψ̄_x] B`. -/
theorem mass1_FC_psibar (a : Lam d L N) (B : Alg d L N) :
    mass1 (-1) (FC C (psibar a) B) = ∑ y, C a y * ∑ x, coeff B ![(y, 1), (x, -1)] := by
  rw [FC_psibar, mass1_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [mass1_smul, mass1_D]

/-- **Lemma `lem:second`(iii), first part**: `m₁ F_C(ψ̄_a, B) = 0` if `B` is homogeneous of a
degree `≠ 2` (e.g. the quartic monomials). -/
theorem mass1_FC_psibar_hom (a : Lam d L N) {n : ℕ} {B : Alg d L N} (hB : IsHom n B)
    (hn : n ≠ 2) : mass1 (-1) (FC C (psibar a) B) = 0 := by
  rw [mass1_FC_psibar]
  exact sum_eq_zero fun y _ => by
    rw [sum_eq_zero fun x _ => hB 2 _ (Ne.symm hn), mul_zero]

end Mass

end

end Obs2
