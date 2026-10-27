import Flow.FlowDefs

/-!
# Restriction to constant fields (Section `sec:suscept`)

For a finite set `Λ`, *restriction to constant `ψ, ψ̄`* is the algebra endomorphism `Rc` of
`𝒩(Λ)` acting on the generators by `ψ_x ↦ |Λ|⁻¹ ∑_y ψ_y`, `ψ̄_x ↦ |Λ|⁻¹ ∑_y ψ̄_y`
(`Rc_psi`, `Rc_psibar`, `psiC_eq`, `psibarC_eq`).  We write `psiC`, `psibarC` for the averaged
generators (the `ψ`, `ψ̄` of the text).

* `Rc_even`: an even element `F` restricts to `F⁰ + F² ψψ̄` with `F⁰ = ε F` (the constant term)
  and `F² = c2 F = ∑_{x,y} F_{(x,+),(y,-)}` (the sum of the coefficients of `ψ_x ψ̄_y`).
* `Rc_EC_theta_const`: `Rc` commutes with `𝔼_C θ` for a constant covariance `C_{xy} = c`
  (such as `t_N Q_N`), and `EC_theta_const_P`: `𝔼_C θ (ψψ̄) = ψψ̄ - c` (the Wick formula).
-/

namespace Suscept

noncomputable section

open Finset Grassmann ExteriorAlgebra CliffordAlgebra

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-! ### The restriction homomorphism -/

variable (Λ) in
/-- The averaging map on the generators: `(avgV v)(y, σ) = |Λ|⁻¹ ∑_x v(x, σ)`. -/
def avgV : V Λ →ₗ[ℂ] V Λ where
  toFun v a := ((Fintype.card Λ : ℂ))⁻¹ * ∑ x, v (x, a.2)
  map_add' v w := by funext a; simp [sum_add_distrib, mul_add]
  map_smul' c v := by funext a; simp [mul_sum, smul_eq_mul, mul_left_comm]

variable (Λ) in
/-- **Restriction to constant fields**: the homomorphism `ψ_x ↦ |Λ|⁻¹ ∑_y ψ_y`,
`ψ̄_x ↦ |Λ|⁻¹ ∑_y ψ̄_y`. -/
def Rc : Grassmann.N Λ →ₐ[ℂ] Grassmann.N Λ := ExteriorAlgebra.map (avgV Λ)

variable (Λ) in
/-- The vector of the averaged generator of spin `σ`. -/
def wv (s : ℤˣ) : V Λ := fun a => if a.2 = s then ((Fintype.card Λ : ℂ))⁻¹ else 0

variable (Λ) in
/-- The averaged generator `ψ = |Λ|⁻¹ ∑_x ψ_x`. -/
def psiC : Grassmann.N Λ := ExteriorAlgebra.ι ℂ (wv Λ 1)

variable (Λ) in
/-- The averaged generator `ψ̄ = |Λ|⁻¹ ∑_x ψ̄_x`. -/
def psibarC : Grassmann.N Λ := ExteriorAlgebra.ι ℂ (wv Λ (-1))

theorem avgV_ev (a : Sf Λ) : avgV Λ (ev a) = wv Λ a.2 := by
  funext b
  simp only [avgV, LinearMap.coe_mk, AddHom.coe_mk, ev, wv]
  rw [Finset.sum_eq_single a.1]
  · by_cases h : b.2 = a.2
    · simp [h]
    · have : ((a.1, b.2) : Sf Λ) ≠ a := fun e => h (by rw [← e])
      simp [h, this]
  · intro x _ hx
    have : ((x, b.2) : Sf Λ) ≠ a := fun e => hx (by rw [← e])
    simp [this]
  · simp

theorem Rc_ψ (a : Sf Λ) : Rc Λ (ψ a) = ExteriorAlgebra.ι ℂ (wv Λ a.2) := by
  rw [Rc, ψ, ExteriorAlgebra.map_apply_ι, avgV_ev]

@[simp] theorem Rc_psi (x : Λ) : Rc Λ (psi x) = psiC Λ := Rc_ψ _

@[simp] theorem Rc_psibar (x : Λ) : Rc Λ (psibar x) = psibarC Λ := Rc_ψ _

theorem wv_eq (s : ℤˣ) : wv Λ s = ((Fintype.card Λ : ℂ))⁻¹ • ∑ x : Λ, ev ((x, s) : Sf Λ) := by
  funext b
  obtain ⟨b1, b2⟩ := b
  simp only [wv, Pi.smul_apply, Finset.sum_apply, ev, smul_eq_mul, Pi.single_apply]
  by_cases h : b2 = s
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single b1]
    · simp
    · intro x _ hx
      rw [if_neg]; intro e; exact hx (congrArg Prod.fst e).symm
    · simp
  · rw [if_neg h, Finset.sum_eq_zero, mul_zero]
    intro x _
    rw [if_neg]; intro e; exact h (congrArg Prod.snd e)

theorem psiC_eq : psiC Λ = ((Fintype.card Λ : ℂ))⁻¹ • ∑ x : Λ, psi x := by
  rw [psiC, wv_eq, map_smul, map_sum]; rfl

theorem psibarC_eq : psibarC Λ = ((Fintype.card Λ : ℂ))⁻¹ • ∑ x : Λ, psibar x := by
  rw [psibarC, wv_eq, map_smul, map_sum]; rfl

theorem psiC_mul_self : psiC Λ * psiC Λ = 0 := ExteriorAlgebra.ι_sq_zero _

theorem psibarC_mul_self : psibarC Λ * psibarC Λ = 0 := ExteriorAlgebra.ι_sq_zero _

theorem psibarC_mul_psiC : psibarC Λ * psiC Λ = -(psiC Λ * psibarC Λ) :=
  ι_anticomm _ _

/-- `(ψψ̄)² = 0`. -/
theorem P_mul_self : psiC Λ * psibarC Λ * (psiC Λ * psibarC Λ) = 0 := by
  rw [mul_assoc, ← mul_assoc (psibarC Λ), psibarC_mul_psiC]
  simp [neg_mul, mul_assoc, psibarC_mul_self]

/-! ### Even elements restricted to constant fields -/

/-- `F² = ∑_{x,y} F_{(x,+),(y,-)}`: the coefficient of `ψψ̄` after restriction to constant
fields. -/
def c2 (F : Grassmann.N Λ) : ℂ := ∑ x : Λ, ∑ y : Λ, coeff F ![((x, 1) : Sf Λ), (y, -1)]

theorem coeff_succ (F : Grassmann.N Λ) {n : ℕ} (z : Fin (n + 1) → Sf Λ) :
    coeff F z = coeff (D (z 0) F) (Fin.tail z) := rfl

theorem coeff_zero' (F : Grassmann.N Λ) (z : Fin 0 → Sf Λ) : coeff F z = ε F := rfl

/-- Coefficients of `inv' F`: `(inv' F)_z = (-1)^{|z|} F_z`. -/
theorem coeff_inv' (F : Grassmann.N Λ) {n : ℕ} (z : Fin n → Sf Λ) :
    coeff (inv' F) z = (-1 : ℂ) ^ n * coeff F z := by
  induction n generalizing F with
  | zero => simp [coeff_zero', algebraMapInv_inv']
  | succ n ih =>
    rw [coeff_succ, coeff_succ, Step.D_inv', show -inv' (D (z 0) F) = (-1 : ℂ) • inv' (D (z 0) F)
      by simp, coeff_smul, ih, pow_succ]
    ring

theorem coeff_eq_zero_of_even {F : Grassmann.N Λ} (hF : inv' F = F) {n : ℕ} (hn : Odd n)
    (z : Fin n → Sf Λ) : coeff F z = 0 := by
  have h := coeff_inv' F z
  rw [hF, hn.neg_one_pow] at h
  have : (2 : ℂ) * coeff F z = 0 := by linear_combination h
  simpa using this

theorem Rc_psiPow {n : ℕ} (z : Fin n → Sf Λ) :
    Rc Λ (psiPow z) = ιMulti ℂ n (fun i => wv Λ (z i).2) := by
  rw [Rc, psiPow, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  exact avgV_ev _

theorem Rc_psiPow_eq_zero {n : ℕ} (hn : 3 ≤ n) (z : Fin n → Sf Λ) : Rc Λ (psiPow z) = 0 := by
  rw [Rc_psiPow]
  refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun hinj => ?_
  have h1 : Function.Injective fun i => (z i).2 := fun i j h => hinj (by simp only [h])
  have := Fintype.card_le_of_injective _ h1
  have h2 : Fintype.card ℤˣ = 2 := by decide
  simp only [Fintype.card_fin, h2] at this
  omega

/-- The degree-two part of `Rc F`. -/
theorem Rc_deg_two (F : Grassmann.N Λ) :
    ∑ z : Fin 2 → Sf Λ, (((2 : ℕ).factorial : ℂ)⁻¹ * coeff F z) • Rc Λ (psiPow z) =
      c2 F • (psiC Λ * psibarC Λ) := by
  simp only [Rc_psiPow]
  rw [Loc.sum_fin_two]
  simp only [Fintype.sum_prod_type, Loc.sum_units_int]
  have h2 : ∀ v : Fin 2 → V Λ, ιMulti ℂ 2 v = ExteriorAlgebra.ι ℂ (v 0) * ExteriorAlgebra.ι ℂ (v 1) := by
    intro v
    rw [ExteriorAlgebra.ιMulti_apply]
    simp [List.ofFn_succ]
  simp only [h2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hp : ExteriorAlgebra.ι ℂ (wv Λ 1) = psiC Λ := rfl
  have hpb : ExteriorAlgebra.ι ℂ (wv Λ (-1)) = psibarC Λ := rfl
  simp only [hp, hpb, psiC_mul_self, psibarC_mul_self, psibarC_mul_psiC, smul_zero,
    zero_add, add_zero, smul_neg]
  have hswap : ∀ x y : Λ, coeff F ![((x, -1) : Sf Λ), (y, 1)] = -coeff F ![((y, 1) : Sf Λ), (x, -1)] := by
    intro x y
    have := coeff_perm F ![((y, 1) : Sf Λ), (x, -1)] (Equiv.swap 0 1)
    have e : (![((y, 1) : Sf Λ), (x, -1)] ∘ Equiv.swap 0 1) = ![((x, -1) : Sf Λ), (y, 1)] := by
      funext i; fin_cases i <;> rfl
    rw [e] at this
    rw [this]; simp
  simp only [hswap, mul_neg, neg_neg, neg_smul, ← sum_smul, ← add_smul]
  congr 1
  rw [c2]
  simp only [sum_add_distrib, ← mul_sum]
  rw [Finset.sum_comm (f := fun x y => coeff F ![((y, 1) : Sf Λ), (x, -1)])]
  norm_num
  ring

/-- **Restriction of an even element to constant fields**: `Rc F = F⁰ + F² ψψ̄` with
`F⁰ = ε F` and `F² = c2 F`. -/
theorem Rc_even [Nonempty Λ] {F : Grassmann.N Λ} (hF : inv' F = F) :
    Rc Λ F = algebraMap ℂ (Grassmann.N Λ) (ε F) + c2 F • (psiC Λ * psibarC Λ) := by
  conv_lhs => rw [sum_coeff F]
  simp only [map_sum, map_smul]
  have hN : 2 < Nf Λ + 1 := by
    have : 0 < Fintype.card Λ := Fintype.card_pos
    simp only [Nf, Fintype.card_prod, show Fintype.card ℤˣ = 2 by decide]
    omega
  rw [← sum_range_add_sum_Ico _ (show 3 ≤ Nf Λ + 1 by omega)]
  rw [sum_eq_zero (s := Ico 3 (Nf Λ + 1)) fun n hn =>
    sum_eq_zero fun z _ => by rw [Rc_psiPow_eq_zero (mem_Ico.1 hn).1, smul_zero]]
  rw [add_zero, sum_range_succ, sum_range_succ, sum_range_one, Rc_deg_two]
  rw [sum_eq_zero (s := (univ : Finset (Fin 1 → Sf Λ))) fun z _ => by
    rw [coeff_eq_zero_of_even hF (by decide), mul_zero, zero_smul], add_zero]
  congr 1
  rw [Fintype.sum_unique]
  rw [Rc_psiPow, coeff_zero', ExteriorAlgebra.ιMulti_zero_apply]
  simp [Algebra.algebraMap_eq_smul_one]

theorem c2_P [Nonempty Λ] : c2 (psiC Λ * psibarC Λ) = 1 := by
  have h2 : psiC Λ * psibarC Λ = ιMulti ℂ 2 ![wv Λ 1, wv Λ (-1)] := by
    rw [ExteriorAlgebra.ιMulti_apply]
    simp [List.ofFn_succ, psiC, psibarC]
  have _hc : (Fintype.card Λ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [c2, h2, coeff_ιMulti, Matrix.det_fin_two, Matrix.of_apply]
  simp [wv, sum_const, card_univ]

theorem c2_algebraMap (c : ℂ) : c2 (algebraMap ℂ (Grassmann.N Λ) c) = 0 := by
  simp [c2, coeff_succ, D_algebraMap]

theorem c2_add (F G : Grassmann.N Λ) : c2 (F + G) = c2 F + c2 G := by
  simp [c2, sum_add_distrib]

theorem c2_smul (r : ℂ) (F : Grassmann.N Λ) : c2 (r • F) = r * c2 F := by
  simp [c2, mul_sum]

/-- `c2` recovers `F²` from the restriction: `c2 (Rc F) = c2 F` for even `F`. -/
theorem c2_Rc [Nonempty Λ] {F : Grassmann.N Λ} (hF : inv' F = F) : c2 (Rc Λ F) = c2 F := by
  rw [Rc_even hF, c2_add, c2_algebraMap, c2_smul, c2_P]; ring

theorem ε_Rc (F : Grassmann.N Λ) : ε (Rc Λ F) = ε F := by
  have : (ε : Grassmann.N Λ →ₐ[ℂ] ℂ).comp (Rc Λ) = ε := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [Rc, ExteriorAlgebra.map_apply_ι]
  exact congrArg (fun f : Grassmann.N Λ →ₐ[ℂ] ℂ => f F) this

/-! ### Constant covariances -/

variable (Λ) in
/-- The constant covariance `C_{xy} = c` (e.g. `t_N Q_N` with `c = t_N/|Λ|`). -/
def cst (c : ℝ) : Matrix Λ Λ ℝ := fun _ _ => c

/-- The functional `v ↦ ∑_x v(x, σ)`, so that `∂_{δs σ} = ∑_x ∂_{ψ_{(x,σ)}}`. -/
def δs (s : ℤˣ) : Module.Dual ℂ (V Λ) := ∑ x : Λ, coord ((x, s) : Sf Λ)

theorem Dφ_δs (s : ℤˣ) (F : Grassmann.N Λ) : Dφ (δs s) F = ∑ x : Λ, D ((x, s) : Sf Λ) F := by
  rw [δs, Dφ_sum]; rfl

theorem Lop_cst (c : ℝ) (F : Grassmann.N Λ) :
    Lop (cst Λ c) F = (c : ℂ) • Dφ (δs 1) (Dφ (δs (-1)) F) := by
  rw [Lop_apply, Dφ_δs, Dφ_δs]
  simp only [map_sum, smul_sum, cst]
  rw [Finset.sum_comm]

theorem δs_comp_avgV [Nonempty Λ] (s : ℤˣ) : δs s ∘ₗ avgV Λ = δs (Λ := Λ) s := by
  have hc : (Fintype.card Λ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, δs, LinearMap.coe_sum, Finset.sum_apply, LinearMap.proj_apply]
  simp only [avgV, LinearMap.coe_mk, AddHom.coe_mk, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem Dφ_δs_Rc [Nonempty Λ] (s : ℤˣ) (F : Grassmann.N Λ) :
    Dφ (δs s) (Rc Λ F) = Rc Λ (Dφ (δs s) F) := by
  rw [Dφ, Rc, contractLeft_map, δs_comp_avgV]

theorem Lop_cst_Rc [Nonempty Λ] (c : ℝ) (F : Grassmann.N Λ) :
    Lop (cst Λ c) (Rc Λ F) = Rc Λ (Lop (cst Λ c) F) := by
  rw [Lop_cst, Lop_cst, Dφ_δs_Rc, Dφ_δs_Rc, map_smul]

theorem expL_cst_Rc [Nonempty Λ] (c : ℝ) (F : Grassmann.N Λ) :
    expL (cst Λ c) (Rc Λ F) = Rc Λ (expL (cst Λ c) F) := by
  have hc : Lop (cst Λ c) ∘ₗ (Rc Λ).toLinearMap = (Rc Λ).toLinearMap ∘ₗ Lop (cst Λ c) :=
    LinearMap.ext fun G => Lop_cst_Rc c G
  have h := Module.End.commute_exp_left_of_commute (Lop_isNilpotent (cst Λ c))
    (Lop_isNilpotent (cst Λ c)) hc
  have h2 := LinearMap.congr_fun h F
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h2
  exact h2

/-- Restriction to constant fields commutes with `𝔼_C θ` for a constant covariance. -/
theorem Rc_EC_theta_const [Nonempty Λ] (c : ℝ) (F : Grassmann.N Λ) :
    Rc Λ (EC (cst Λ c) (theta F)) = EC (cst Λ c) (theta (Rc Λ F)) := by
  rw [EC_theta, EC_theta, expL_cst_Rc]

/-- The fermionic Wick formula for the zero mode: `𝔼_C θ (ψψ̄) = ψψ̄ - c` for `C_{xy} = c`. -/
theorem EC_theta_const_P [Nonempty Λ] (c : ℝ) :
    EC (cst Λ c) (theta (psiC Λ * psibarC Λ)) =
      psiC Λ * psibarC Λ - algebraMap ℂ (Grassmann.N Λ) (c : ℂ) := by
  have hc : (Fintype.card Λ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h1 : ∀ x y : Λ, EC (cst Λ c) (theta (psi x * psibar y)) =
      psi x * psibar y - algebraMap ℂ (Grassmann.N Λ) (c : ℂ) := by
    intro x y
    have e : psi x * psibar y = -(psibar y * psi x) := ι_anticomm _ _
    rw [e, map_neg, map_neg, EC_theta_psibar_psi]
    simp [cst]; abel
  have hP : psiC Λ * psibarC Λ =
      ((Fintype.card Λ : ℂ) ^ 2)⁻¹ • ∑ x : Λ, ∑ y : Λ, psi x * psibar y := by
    rw [psiC_eq, psibarC_eq, smul_mul_smul_comm, sum_mul_sum, pow_two, mul_inv]
  rw [hP, map_smul, map_smul, map_sum]
  simp only [map_sum, h1, sum_sub_distrib, sum_const, card_univ, smul_sub]
  congr 1
  simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [show ((Fintype.card Λ : ℂ) ^ 2)⁻¹ * ((Fintype.card Λ : ℂ) * (Fintype.card Λ : ℂ)) = 1 by
    field_simp, one_smul]

end

end Suscept
