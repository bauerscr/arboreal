import Suscept.Bounds
import Grassmann.GaussianC

/-!
# Restriction to constant fields with a complex constant covariance (`PtCorr2`)

The zero mode of the last scale is a *complex* constant covariance `C_{xy} = c`
(`c = Γ^int_N(0)/|Λ|`, the raw zero mode of the dressed decomposition). This file extends the
real computations of `Suscept.Restrict` to complex `c`:

* `cstC c`: the constant complex covariance;
* `Rc_ECC_theta_cstC`: restriction to constant fields commutes with `𝔼_{cQ} θ`;
* `ECC_theta_cstC_P`: `𝔼_{cQ} θ (ψψ̄) = ψψ̄ - c`;
* **`Rc_ECC_cstC_even`**: for even `F`, `Rc 𝔼_{cQ} θ F = (ε F - c F²) + F² ψψ̄`, `F² = c2 F`;
* on the even subalgebra (commutative): `RE = Rc|_{EvR}`, `PPE = ψψ̄ ∈ EvR`,
  the product rule `prod_add_smul_nil` for elements `α + β P` with `P² = 0`, and
  `eps_c2_of_RE` (reading `ε F`, `c2 F` from `Rc F`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Suscept Step

section General

set_option linter.unusedSectionVars false

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

variable (Λ) in
/-- The constant complex covariance `C_{xy} = c`. -/
def cstC (c : ℂ) : Matrix Λ Λ ℂ := fun _ _ => c

theorem LopC_cstC (c : ℂ) (F : Grassmann.N Λ) :
    LopC (cstC Λ c) F = c • Dφ (δs 1) (Dφ (δs (-1)) F) := by
  rw [LopC_apply, Dφ_δs, Dφ_δs]
  simp only [map_sum, smul_sum, cstC]
  rw [Finset.sum_comm]

theorem ECC_theta_one (C : Matrix Λ Λ ℂ) : ECC C (theta (1 : Grassmann.N Λ)) = 1 := by
  rw [ECC_theta, expLC_eq_self]
  simp [LopC_apply, D]

theorem ECC_theta_algebraMap (C : Matrix Λ Λ ℂ) (a : ℂ) :
    ECC C (theta (algebraMap ℂ (Grassmann.N Λ) a)) = algebraMap ℂ (Grassmann.N Λ) a := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, ECC_theta_one]

variable [Nonempty Λ]

theorem LopC_cstC_Rc (c : ℂ) (F : Grassmann.N Λ) :
    LopC (cstC Λ c) (Rc Λ F) = Rc Λ (LopC (cstC Λ c) F) := by
  rw [LopC_cstC, LopC_cstC, Dφ_δs_Rc, Dφ_δs_Rc, map_smul]

theorem expLC_cstC_Rc (c : ℂ) (F : Grassmann.N Λ) :
    expLC (cstC Λ c) (Rc Λ F) = Rc Λ (expLC (cstC Λ c) F) := by
  have hc : LopC (cstC Λ c) ∘ₗ (Rc Λ).toLinearMap = (Rc Λ).toLinearMap ∘ₗ LopC (cstC Λ c) :=
    LinearMap.ext fun G => LopC_cstC_Rc c G
  have h := Module.End.commute_exp_left_of_commute (LopC_isNilpotent (cstC Λ c))
    (LopC_isNilpotent (cstC Λ c)) hc
  have h2 := LinearMap.congr_fun h F
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h2
  exact h2

/-- Restriction to constant fields commutes with `𝔼_{cQ} θ` (complex `c`). -/
theorem Rc_ECC_theta_cstC (c : ℂ) (F : Grassmann.N Λ) :
    Rc Λ (ECC (cstC Λ c) (theta F)) = ECC (cstC Λ c) (theta (Rc Λ F)) := by
  rw [ECC_theta, ECC_theta, expLC_cstC_Rc]

/-- The fermionic Wick formula for a complex zero mode: `𝔼_{cQ} θ (ψψ̄) = ψψ̄ - c`. -/
theorem ECC_theta_cstC_P (c : ℂ) :
    ECC (cstC Λ c) (theta (psiC Λ * psibarC Λ)) =
      psiC Λ * psibarC Λ - algebraMap ℂ (Grassmann.N Λ) c := by
  have h1 : ∀ x y : Λ, ECC (cstC Λ c) (theta (psi x * psibar y)) =
      psi x * psibar y - algebraMap ℂ (Grassmann.N Λ) c := by
    intro x y
    have e : psi x * psibar y = -(psibar y * psi x) := ι_anticomm _ _
    rw [e, map_neg, map_neg, ECC_theta_psibar_psi]
    simp [cstC]; abel
  have hP : psiC Λ * psibarC Λ =
      ((Fintype.card Λ : ℂ) ^ 2)⁻¹ • ∑ x : Λ, ∑ y : Λ, psi x * psibar y := by
    rw [psiC_eq, psibarC_eq, smul_mul_smul_comm, sum_mul_sum, pow_two, mul_inv]
  rw [hP, map_smul, map_smul, map_sum]
  simp only [map_sum, h1, sum_sub_distrib, sum_const, card_univ, smul_sub]
  congr 1
  simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [show ((Fintype.card Λ : ℂ) ^ 2)⁻¹ * ((Fintype.card Λ : ℂ) * (Fintype.card Λ : ℂ)) = 1 by
    field_simp, one_smul]

/-- **Zero-mode integration restricted to constant fields**: for even `F` and the complex
constant covariance `cQ`, `Rc 𝔼_{cQ} θ F = (ε F - c F²) + F² ψψ̄` with `F² = c2 F`. -/
theorem Rc_ECC_cstC_even (c : ℂ) {F : Grassmann.N Λ} (hF : inv' F = F) :
    Rc Λ (ECC (cstC Λ c) (theta F)) =
      algebraMap ℂ (Grassmann.N Λ) (ε F - c * c2 F) + c2 F • (psiC Λ * psibarC Λ) := by
  rw [Rc_ECC_theta_cstC, Rc_even hF, map_add, map_add, map_smul, map_smul, ECC_theta_algebraMap,
    ECC_theta_cstC_P, smul_sub, Algebra.smul_def (c2 F) (algebraMap ℂ _ c), ← map_mul, map_sub,
    mul_comm (c2 F) c]
  abel

/-! ### The even subalgebra -/

theorem inv'_PP : inv' (psiC Λ * psibarC Λ) = psiC Λ * psibarC Λ := by
  rw [map_mul, psiC, psibarC, inv'_ι, inv'_ι, neg_mul_neg]

variable (Λ) in
/-- `ψψ̄` (constant fields) as an even element. -/
def PPE : EvR Λ := ⟨psiC Λ * psibarC Λ, mem_Ev.2 inv'_PP⟩

variable (Λ) in
/-- Restriction to constant fields on the even subalgebra. -/
abbrev RE : EvR Λ →ₐ[ℂ] EvR Λ := mapE (avgV Λ)

theorem coe_RE (x : EvR Λ) : (RE Λ x : Grassmann.N Λ) = Rc Λ x := rfl

@[simp] theorem coe_PPE : (PPE Λ : Grassmann.N Λ) = psiC Λ * psibarC Λ := rfl

theorem PPE_mul_self : PPE Λ * PPE Λ = 0 := Subtype.ext P_mul_self

/-- `Rc F = ε F + F² ψψ̄` on the even subalgebra. -/
theorem RE_eq (x : EvR Λ) :
    RE Λ x = algebraMap ℂ (EvR Λ) (ε (x : Grassmann.N Λ)) + c2 (x : Grassmann.N Λ) • PPE Λ :=
  Subtype.ext (by rw [coe_RE, Rc_even (mem_Ev.1 x.2)]; rfl)

theorem ε_PP : ε (psiC Λ * psibarC Λ) = 0 := by
  rw [map_mul, psiC, algebraMapInv_ι, zero_mul]

/-- Reading `ε F` and `F²` off `Rc F`. -/
theorem eps_c2_of_RE {x : EvR Λ} {a b : ℂ}
    (h : RE Λ x = algebraMap ℂ (EvR Λ) a + b • PPE Λ) :
    ε (x : Grassmann.N Λ) = a ∧ c2 (x : Grassmann.N Λ) = b := by
  have h' := congrArg (fun y : EvR Λ => (y : Grassmann.N Λ)) h
  simp only [coe_RE, Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_algebraMap,
    coe_PPE] at h'
  constructor
  · have := congrArg ε h'
    rwa [ε_Rc, map_add, map_smul, ε_PP, smul_zero, add_zero, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] at this
  · have := congrArg c2 h'
    rwa [c2_Rc (mem_Ev.1 x.2), c2_add, c2_smul, c2_algebraMap, c2_P, mul_one, zero_add] at this

end General

/-! ### Products of elements `α + β P` with `P² = 0` -/

theorem prod_add_smul_nil {R : Type*} [CommRing R] [Algebra ℂ R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α β : ι → ℂ) {P : R} (hP : P * P = 0) :
    ∏ i ∈ s, (algebraMap ℂ R (α i) + β i • P) =
      algebraMap ℂ R (∏ i ∈ s, α i) + (∑ i ∈ s, β i * ∏ k ∈ s.erase i, α k) • P := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, ih, prod_insert ha, sum_insert ha, erase_insert ha]
    have hs : ∑ i ∈ s, β i * ∏ k ∈ (insert a s).erase i, α k =
        α a * ∑ i ∈ s, β i * ∏ k ∈ s.erase i, α k := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      rw [erase_insert_of_ne hne, prod_insert (fun h => ha (mem_of_mem_erase h))]
      ring
    rw [hs]
    simp only [Algebra.smul_def, map_mul, map_add]
    linear_combination (algebraMap ℂ R (β a) *
      algebraMap ℂ R (∑ i ∈ s, β i * ∏ k ∈ s.erase i, α k)) * hP

end

end PtCorr2
