import Obs.Ops
import Suscept.Cov

/-!
# Coefficients after restriction to constant fields (WP1b)

* `Rc_inv'`: `Suscept.Rc` commutes with the grade involution, so it acts componentwise on the
  amended algebra: `RcO : OE c Λ →ₐ[ℂ] OE c Λ` (`coe_RcO_e`, …).
* `c1p F = ∑_y F_{(y,+)}`, `c1m F = ∑_y F_{(y,-)}` are the coefficients of `ψ` and `ψ̄` after
  restriction to constant fields: for odd `F`, `Rc F = c1p F • ψ + c1m F • ψ̄` (`Rc_odd`).
  They are linear (`c1pL`, `c1mL`), `c1p F = ε (∂_{δs +} F)` (`c1p_eq`), invariant under `Rc`
  (`c1p_Rc`), and vanish on even elements (`c1p_of_even`).
* `c1p_EC_theta`: `c1p (𝔼_C θ F) = ⟨∂_{δs +} F⟩_C` for any covariance, and for the constant
  covariance (`t_N Q_N`) and odd `F`, `c1p (𝔼_C θ F) = c1p F` (`c1p_EC_theta_const_of_odd`,
  `c1p_EC_tQ_theta_of_odd`); likewise for `c1m`.
* `RcO_ECO_thetaO_const`: `RcO` commutes with `ECO (cst c) ∘ thetaO`.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Obs ExteriorAlgebra CliffordAlgebra

set_option linter.unusedSimpArgs false

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-! ### `Rc` on the amended algebra -/

theorem Rc_inv' (x : Grassmann.N Λ) : Suscept.Rc Λ (inv' x) = inv' (Suscept.Rc Λ x) :=
  (Grassmann.inv'_map _ x).symm

variable (c Λ) in
/-- Restriction to constant fields, componentwise on even elements of the amended algebra. -/
def RcO : OE c Λ →ₐ[ℂ] OE c Λ := mapO (Suscept.Rc Λ) Rc_inv'

@[simp] theorem coe_RcO_e (F : OE c Λ) :
    ((RcO c Λ F : OE c Λ) : SA c Λ).e = Suscept.Rc Λ (F : SA c Λ).e := rfl
@[simp] theorem coe_RcO_a (F : OE c Λ) :
    ((RcO c Λ F : OE c Λ) : SA c Λ).a = Suscept.Rc Λ (F : SA c Λ).a := rfl
@[simp] theorem coe_RcO_b (F : OE c Λ) :
    ((RcO c Λ F : OE c Λ) : SA c Λ).b = Suscept.Rc Λ (F : SA c Λ).b := rfl
@[simp] theorem coe_RcO_ab (F : OE c Λ) :
    ((RcO c Λ F : OE c Λ) : SA c Λ).ab = Suscept.Rc Λ (F : SA c Λ).ab := rfl

/-! ### The coefficients of `ψ`, `ψ̄` -/

/-- `c1p F = ∑_y F_{(y,+)}`: the coefficient of `ψ` after restriction to constant fields. -/
def c1p (F : Grassmann.N Λ) : ℂ := ∑ y : Λ, coeff F ![((y, 1) : Sf Λ)]

/-- `c1m F = ∑_y F_{(y,-)}`: the coefficient of `ψ̄` after restriction to constant fields. -/
def c1m (F : Grassmann.N Λ) : ℂ := ∑ y : Λ, coeff F ![((y, -1) : Sf Λ)]

/-- The general form: `∑_y F_{(y,s)} = ε (∂_{δs s} F)`. -/
theorem sum_coeff_one_eq (s : ℤˣ) (F : Grassmann.N Λ) :
    ∑ y : Λ, coeff F ![((y, s) : Sf Λ)] = ε (Dφ (Suscept.δs s) F) := by
  rw [Suscept.Dφ_δs, map_sum]; rfl

theorem c1p_eq (F : Grassmann.N Λ) : c1p F = ε (Dφ (Suscept.δs 1) F) := sum_coeff_one_eq 1 F

theorem c1m_eq (F : Grassmann.N Λ) : c1m F = ε (Dφ (Suscept.δs (-1)) F) := sum_coeff_one_eq _ F

variable (Λ) in
/-- `c1p` as a linear functional. -/
def c1pL : Grassmann.N Λ →ₗ[ℂ] ℂ := (ε : Grassmann.N Λ →ₐ[ℂ] ℂ).toLinearMap ∘ₗ Dφ (Suscept.δs 1)

variable (Λ) in
/-- `c1m` as a linear functional. -/
def c1mL : Grassmann.N Λ →ₗ[ℂ] ℂ :=
  (ε : Grassmann.N Λ →ₐ[ℂ] ℂ).toLinearMap ∘ₗ Dφ (Suscept.δs (-1))

theorem c1pL_apply (F : Grassmann.N Λ) : c1pL Λ F = c1p F := (c1p_eq F).symm
theorem c1mL_apply (F : Grassmann.N Λ) : c1mL Λ F = c1m F := (c1m_eq F).symm

@[simp] theorem c1p_add (F G : Grassmann.N Λ) : c1p (F + G) = c1p F + c1p G := by
  simp only [← c1pL_apply, map_add]
@[simp] theorem c1m_add (F G : Grassmann.N Λ) : c1m (F + G) = c1m F + c1m G := by
  simp only [← c1mL_apply, map_add]
@[simp] theorem c1p_neg (F : Grassmann.N Λ) : c1p (-F) = -c1p F := by
  simp only [← c1pL_apply, map_neg]
@[simp] theorem c1p_smul (r : ℂ) (F : Grassmann.N Λ) : c1p (r • F) = r * c1p F := by
  simp only [← c1pL_apply, map_smul, smul_eq_mul]
@[simp] theorem c1m_smul (r : ℂ) (F : Grassmann.N Λ) : c1m (r • F) = r * c1m F := by
  simp only [← c1mL_apply, map_smul, smul_eq_mul]



theorem ε_Dφ_δs_ι (s : ℤˣ) (v : V Λ) :
    ε (Dφ (Suscept.δs s) (ExteriorAlgebra.ι ℂ v)) = ∑ x : Λ, v (x, s) := by
  simp [Dφ, Suscept.δs]

@[simp] theorem c1p_psiC [Nonempty Λ] : c1p (Suscept.psiC Λ) = 1 := by
  have hc : (Fintype.card Λ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [c1p_eq, Suscept.psiC, ε_Dφ_δs_ι]
  simp [Suscept.wv, sum_const, card_univ, hc]
@[simp] theorem c1m_psibarC [Nonempty Λ] : c1m (Suscept.psibarC Λ) = 1 := by
  have hc : (Fintype.card Λ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [c1m_eq, Suscept.psibarC, ε_Dφ_δs_ι]
  simp [Suscept.wv, sum_const, card_univ, hc]

/-- `c1p` is invariant under restriction to constant fields. -/
theorem c1p_Rc [Nonempty Λ] (F : Grassmann.N Λ) : c1p (Suscept.Rc Λ F) = c1p F := by
  rw [c1p_eq, c1p_eq, Suscept.Dφ_δs_Rc, Suscept.ε_Rc]

theorem c1m_Rc [Nonempty Λ] (F : Grassmann.N Λ) : c1m (Suscept.Rc Λ F) = c1m F := by
  rw [c1m_eq, c1m_eq, Suscept.Dφ_δs_Rc, Suscept.ε_Rc]

/-! ### Odd elements restricted to constant fields -/

theorem coeff_eq_zero_of_odd {F : Grassmann.N Λ} (hF : inv' F = -F) {n : ℕ} (hn : Even n)
    (z : Fin n → Sf Λ) : coeff F z = 0 := by
  have h := Suscept.coeff_inv' F z
  rw [hF, hn.neg_one_pow, show coeff (-F) z = -coeff F z by
    simpa using coeff_smul (-1 : ℂ) F z] at h
  have : (2 : ℂ) * coeff F z = 0 := by linear_combination -h
  simpa using this

theorem sum_fin_one {M : Type*} [AddCommMonoid M] {α : Type*} [Fintype α] (f : (Fin 1 → α) → M) :
    ∑ z, f z = ∑ a, f ![a] := by
  rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
  refine sum_congr rfl fun a _ => ?_
  congr 1
  funext i
  fin_cases i
  rfl

/-- The degree-one part of `Rc F`. -/
theorem Rc_deg_one (F : Grassmann.N Λ) :
    ∑ z : Fin 1 → Sf Λ, (((1 : ℕ).factorial : ℂ)⁻¹ * coeff F z) • Suscept.Rc Λ (psiPow z) =
      c1p F • Suscept.psiC Λ + c1m F • Suscept.psibarC Λ := by
  simp only [Suscept.Rc_psiPow]
  rw [sum_fin_one]
  simp only [Fintype.sum_prod_type, Loc.sum_units_int]
  have h1 : ∀ v : Fin 1 → V Λ, ιMulti ℂ 1 v = ExteriorAlgebra.ι ℂ (v 0) := by
    intro v
    rw [ExteriorAlgebra.ιMulti_apply]
    simp
  simp only [h1, Matrix.cons_val_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
  have hp : ExteriorAlgebra.ι ℂ (Suscept.wv Λ 1) = Suscept.psiC Λ := rfl
  have hpb : ExteriorAlgebra.ι ℂ (Suscept.wv Λ (-1)) = Suscept.psibarC Λ := rfl
  rw [hp, hpb, sum_add_distrib, ← sum_smul, ← sum_smul]
  rfl

/-- **Restriction of an odd element to constant fields**: `Rc F = c1p F • ψ + c1m F • ψ̄`. -/
theorem Rc_odd [Nonempty Λ] {F : Grassmann.N Λ} (hF : inv' F = -F) :
    Suscept.Rc Λ F = c1p F • Suscept.psiC Λ + c1m F • Suscept.psibarC Λ := by
  conv_lhs => rw [sum_coeff F]
  simp only [map_sum, map_smul]
  have hN : 2 < Nf Λ + 1 := by
    have : 0 < Fintype.card Λ := Fintype.card_pos
    simp only [Nf, Fintype.card_prod, show Fintype.card ℤˣ = 2 by decide]
    omega
  rw [← sum_range_add_sum_Ico _ (show 3 ≤ Nf Λ + 1 by omega)]
  rw [sum_eq_zero (s := Ico 3 (Nf Λ + 1)) fun n hn =>
    sum_eq_zero fun z _ => by rw [Suscept.Rc_psiPow_eq_zero (mem_Ico.1 hn).1, smul_zero]]
  rw [add_zero, sum_range_succ, sum_range_succ, sum_range_one, Rc_deg_one]
  rw [sum_eq_zero (s := (univ : Finset (Fin 2 → Sf Λ))) fun z _ => by
    rw [coeff_eq_zero_of_odd hF (by decide), mul_zero, zero_smul], add_zero]
  rw [sum_eq_zero (s := (univ : Finset (Fin 0 → Sf Λ))) fun z _ => by
    rw [coeff_eq_zero_of_odd hF (by decide), mul_zero, zero_smul], zero_add]

/-! ### Interaction with `𝔼_C θ` -/

/-- `c1p (𝔼_C θ F) = ⟨∂_{δs +} F⟩_C`. -/
theorem c1p_EC_theta (C : Matrix Λ Λ ℝ) (F : Grassmann.N Λ) :
    c1p (EC C (theta F)) = omega C (Dφ (Suscept.δs 1) F) := by
  rw [c1p_eq, EC_theta, Suscept.Dφ_δs_expL, omega]

/-- `c1m (𝔼_C θ F) = ⟨∂_{δs -} F⟩_C`. -/
theorem c1m_EC_theta (C : Matrix Λ Λ ℝ) (F : Grassmann.N Λ) :
    c1m (EC C (theta F)) = omega C (Dφ (Suscept.δs (-1)) F) := by
  rw [c1m_eq, EC_theta, Suscept.Dφ_δs_expL, omega]

theorem EC_theta_ι (C : Matrix Λ Λ ℝ) (v : V Λ) :
    EC C (theta (ExteriorAlgebra.ι ℂ v : Grassmann.N Λ)) = ExteriorAlgebra.ι ℂ v := by
  rw [EC_theta, expL_eq_self]
  simp [Lop_apply, D]

theorem EC_theta_psiC (C : Matrix Λ Λ ℝ) : EC C (theta (Suscept.psiC Λ)) = Suscept.psiC Λ :=
  EC_theta_ι C _

theorem EC_theta_psibarC (C : Matrix Λ Λ ℝ) :
    EC C (theta (Suscept.psibarC Λ)) = Suscept.psibarC Λ :=
  EC_theta_ι C _

/-- For the constant covariance and odd `F`, `Rc (𝔼_C θ F) = Rc F`. -/
theorem Rc_EC_theta_const_of_odd [Nonempty Λ] (t : ℝ) {F : Grassmann.N Λ} (hF : inv' F = -F) :
    Suscept.Rc Λ (EC (Suscept.cst Λ t) (theta F)) = Suscept.Rc Λ F := by
  rw [Suscept.Rc_EC_theta_const, Rc_odd hF, map_add, map_smul, map_smul, map_add, map_smul,
    map_smul, EC_theta_psiC, EC_theta_psibarC]

theorem c1p_EC_theta_const_of_odd [Nonempty Λ] (t : ℝ) {F : Grassmann.N Λ} (hF : inv' F = -F) :
    c1p (EC (Suscept.cst Λ t) (theta F)) = c1p F := by
  rw [← c1p_Rc, Rc_EC_theta_const_of_odd t hF, c1p_Rc]

theorem c1m_EC_theta_const_of_odd [Nonempty Λ] (t : ℝ) {F : Grassmann.N Λ} (hF : inv' F = -F) :
    c1m (EC (Suscept.cst Λ t) (theta F)) = c1m F := by
  rw [← c1m_Rc, Rc_EC_theta_const_of_odd t hF, c1m_Rc]

section Lam

open Loc

variable {d L N : ℕ} [NeZero L]

/-- `c1p (𝔼_{t Q_N} θ F) = c1p F` for odd `F`. -/
theorem c1p_EC_tQ_theta_of_odd (t : ℝ) {F : Grassmann.N (Lam d L N)} (hF : inv' F = -F) :
    c1p (EC (t • FRD.QN : Matrix (Lam d L N) (Lam d L N) ℝ) (theta F)) = c1p F := by
  rw [Suscept.tQ_eq_cst, c1p_EC_theta_const_of_odd _ hF]

theorem c1m_EC_tQ_theta_of_odd (t : ℝ) {F : Grassmann.N (Lam d L N)} (hF : inv' F = -F) :
    c1m (EC (t • FRD.QN : Matrix (Lam d L N) (Lam d L N) ℝ) (theta F)) = c1m F := by
  rw [Suscept.tQ_eq_cst, c1m_EC_theta_const_of_odd _ hF]

end Lam

end

end PtCorr
