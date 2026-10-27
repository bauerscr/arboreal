import Obs.Ops
import Step2.Map.Defs

/-!
# Operations on the algebra with source fields, complex covariance (new route)

The new route (`Step2`) uses complex covariances (`ECC`, `expLC`, `F_C = FC`). This file lifts
these operations to the algebra with source fields `OE c Λ` (`Obs.Algebra`), componentwise,
exactly as `Obs.Ops` does for the real covariance of the old route:

* `ECCO C : OE c (Λ ⊕ Λ) →ₗ OE c Λ` (`𝔼_C`, componentwise `ECC C`), `expO C` (`e^{ℒ_C}`,
  componentwise `expLC C`); `𝔼_C θ = e^{ℒ_C}` (`EthO_eq_expO`);
* `EthO C F = 𝔼_C θ F`, `FCO C A B = e^{ℒ_C}((e^{-ℒ_C} A)(e^{-ℒ_C} B)) - AB`, the truncated
  expectation: `F_C(𝔼θA, 𝔼θB) = 𝔼θ(AB) - 𝔼θA 𝔼θB` (`FCO_EthO`);
* the bulk component commutes with all of them (`bulk_ECCO`, `bulk_expO`, `bulk_EthO`,
  `bulk_FCO`), and with the exponential **without hypotheses** (`bulk_oexp'`: both sides are the
  junk value `0` for non-nilpotent arguments).

The source fields are constants for `θ`, the inclusion and `𝔼_C` (`ℒ_C` is even), so all maps
act componentwise on `F_∅, F_a, F_b, F_ab`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-! ### `𝔼_C` and `e^{ℒ_C}` -/

/-- `𝔼_C` on the amended algebra (componentwise), complex covariance. -/
def ECCS (C : Matrix Λ Λ ℂ) : SA c (Λ ⊕ Λ) →ₗ[ℂ] SA c Λ := mapL (ECC C)

@[simp] theorem ECCS_e (C : Matrix Λ Λ ℂ) (F : SA c (Λ ⊕ Λ)) : (ECCS C F).e = ECC C F.e := rfl
@[simp] theorem ECCS_a (C : Matrix Λ Λ ℂ) (F : SA c (Λ ⊕ Λ)) : (ECCS C F).a = ECC C F.a := rfl
@[simp] theorem ECCS_b (C : Matrix Λ Λ ℂ) (F : SA c (Λ ⊕ Λ)) : (ECCS C F).b = ECC C F.b := rfl
@[simp] theorem ECCS_ab (C : Matrix Λ Λ ℂ) (F : SA c (Λ ⊕ Λ)) : (ECCS C F).ab = ECC C F.ab :=
  rfl

/-- `𝔼_C` on even elements, complex covariance. -/
def ECCO (C : Matrix Λ Λ ℂ) : OE c (Λ ⊕ Λ) →ₗ[ℂ] OE c Λ :=
  (((ECCS C).comp (OEv c (Λ ⊕ Λ)).val.toLinearMap).codRestrict (OEv c Λ).toSubmodule fun F => by
    obtain ⟨h1, h2, h3, h4⟩ := mem_OEv.1 F.2
    refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val, ECCS_e,
        ECCS_a, ECCS_b, ECCS_ab, ← Step2.ECC_inv', h1, h2, h3, h4, map_smul])

@[simp] theorem coe_ECCO (C : Matrix Λ Λ ℂ) (F : OE c (Λ ⊕ Λ)) :
    (ECCO C F : SA c Λ) = ECCS C (F : SA c (Λ ⊕ Λ)) := rfl

theorem bulk_ECCO (C : Matrix Λ Λ ℂ) (F : OE c (Λ ⊕ Λ)) :
    bulk (ECCO C F) = Step2.ECCE C (bulk F) := rfl

theorem ECCO_emb (C : Matrix Λ Λ ℂ) (x : Step.EvR (Λ ⊕ Λ)) :
    ECCO C (emb x : OE c (Λ ⊕ Λ)) = emb (Step2.ECCE C x) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

/-- `𝔼_C (ι a · g) = a 𝔼_C g`. -/
theorem ECCS_inclS_mul (C : Matrix Λ Λ ℂ) (F : SA c Λ) (G : SA c (Λ ⊕ Λ)) :
    ECCS C (inclS F * G) = F * ECCS C G := by
  ext <;> simp only [ECCS_e, ECCS_a, ECCS_b, ECCS_ab, mul_e, mul_a, mul_b, mul_ab, inclS_e,
    inclS_a, inclS_b, inclS_ab, map_add, map_smul, Obs.Case.tau_comm c incl incl_inv',
    ECC_incl_mul]

theorem ECCO_inclO_mul (C : Matrix Λ Λ ℂ) (F : OE c Λ) (G : OE c (Λ ⊕ Λ)) :
    ECCO C (inclO F * G) = F * ECCO C G :=
  Subtype.ext (ECCS_inclS_mul C (F : SA c Λ) (G : SA c (Λ ⊕ Λ)))

theorem ECCO_one (C : Matrix Λ Λ ℂ) : ECCO C (1 : OE c (Λ ⊕ Λ)) = 1 := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [ECC_one]

theorem ECCO_inclO (C : Matrix Λ Λ ℂ) (F : OE c Λ) : ECCO C (inclO F) = F := by
  have := ECCO_inclO_mul C F 1
  rwa [mul_one, ECCO_one, mul_one] at this

/-- `e^{ℒ_C}` on the amended algebra (componentwise). -/
def expS (C : Matrix Λ Λ ℂ) : SA c Λ →ₗ[ℂ] SA c Λ := mapL (expLC C)

@[simp] theorem expS_e (C : Matrix Λ Λ ℂ) (F : SA c Λ) : (expS C F).e = expLC C F.e := rfl
@[simp] theorem expS_a (C : Matrix Λ Λ ℂ) (F : SA c Λ) : (expS C F).a = expLC C F.a := rfl
@[simp] theorem expS_b (C : Matrix Λ Λ ℂ) (F : SA c Λ) : (expS C F).b = expLC C F.b := rfl
@[simp] theorem expS_ab (C : Matrix Λ Λ ℂ) (F : SA c Λ) : (expS C F).ab = expLC C F.ab := rfl

/-- `e^{ℒ_C}` on even elements. -/
def expO (C : Matrix Λ Λ ℂ) : OE c Λ →ₗ[ℂ] OE c Λ :=
  (((expS C).comp (OEv c Λ).val.toLinearMap).codRestrict (OEv c Λ).toSubmodule fun F => by
    obtain ⟨h1, h2, h3, h4⟩ := mem_OEv.1 F.2
    refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val, expS_e,
        expS_a, expS_b, expS_ab, ← expLC_inv', h1, h2, h3, h4, map_smul])

@[simp] theorem coe_expO (C : Matrix Λ Λ ℂ) (F : OE c Λ) :
    (expO C F : SA c Λ) = expS C (F : SA c Λ) := rfl

theorem expO_neg_expO (C : Matrix Λ Λ ℂ) (F : OE c Λ) : expO (-C) (expO C F) = F := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [expLC_neg_expLC]

/-! ### `𝔼_C θ` and `F_C` -/

/-- `𝔼_C θ` on even elements with sources. -/
def EthO (C : Matrix Λ Λ ℂ) (F : OE c Λ) : OE c Λ := ECCO C (thetaO F)

theorem EthO_eq_expO (C : Matrix Λ Λ ℂ) (F : OE c Λ) : EthO C F = expO C F := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [EthO, ECC_theta]

theorem EthO_add (C : Matrix Λ Λ ℂ) (F G : OE c Λ) : EthO C (F + G) = EthO C F + EthO C G := by
  simp [EthO, map_add]

theorem EthO_smul (C : Matrix Λ Λ ℂ) (r : ℂ) (F : OE c Λ) : EthO C (r • F) = r • EthO C F := by
  simp [EthO, map_smul]

theorem EthO_sub (C : Matrix Λ Λ ℂ) (F G : OE c Λ) : EthO C (F - G) = EthO C F - EthO C G := by
  simp [EthO, map_sub]

/-- `𝔼_C θ` as a linear map. -/
def EthOL (C : Matrix Λ Λ ℂ) : OE c Λ →ₗ[ℂ] OE c Λ := (ECCO C).comp thetaO.toLinearMap

theorem bulk_EthO (C : Matrix Λ Λ ℂ) (F : OE c Λ) : bulk (EthO C F) = Step2.EthE C (bulk F) :=
  rfl

theorem EthO_emb (C : Matrix Λ Λ ℂ) (x : Step.EvR Λ) :
    EthO C (emb x : OE c Λ) = emb (Step2.EthE C x) := by
  rw [EthO, thetaO_emb, ECCO_emb]; rfl

/-- `F_C(A, B) = e^{ℒ_C}((e^{-ℒ_C} A)(e^{-ℒ_C} B)) - AB` on even elements with sources. -/
def FCO (C : Matrix Λ Λ ℂ) (A B : OE c Λ) : OE c Λ :=
  expO C (expO (-C) A * expO (-C) B) - A * B

theorem bulk_FCO (C : Matrix Λ Λ ℂ) (A B : OE c Λ) :
    bulk (FCO C A B) = Step2.FCE C (bulk A) (bulk B) := rfl

theorem FCO_comm (C : Matrix Λ Λ ℂ) (A B : OE c Λ) : FCO C A B = FCO C B A := by
  rw [FCO, FCO, mul_comm (expO (-C) A), mul_comm A]

/-- **The truncated expectation**: `F_C(𝔼θA, 𝔼θB) = 𝔼θ(AB) - 𝔼θA 𝔼θB`. -/
theorem FCO_EthO (C : Matrix Λ Λ ℂ) (A B : OE c Λ) :
    FCO C (EthO C A) (EthO C B) = EthO C (A * B) - EthO C A * EthO C B := by
  rw [EthO_eq_expO, EthO_eq_expO, EthO_eq_expO, FCO, expO_neg_expO, expO_neg_expO]

/-- `𝔼θ(AB) = 𝔼θA 𝔼θB + F(𝔼θA, 𝔼θB)`. -/
theorem EthO_mul (C : Matrix Λ Λ ℂ) (A B : OE c Λ) :
    EthO C (A * B) = EthO C A * EthO C B + FCO C (EthO C A) (EthO C B) := by
  rw [FCO_EthO]; abel

theorem FCO_add_left (C : Matrix Λ Λ ℂ) (A A' B : OE c Λ) :
    FCO C (A + A') B = FCO C A B + FCO C A' B := by
  simp only [FCO, map_add, add_mul]; abel

theorem FCO_add_right (C : Matrix Λ Λ ℂ) (A B B' : OE c Λ) :
    FCO C A (B + B') = FCO C A B + FCO C A B' := by
  rw [FCO_comm, FCO_add_left, FCO_comm C B, FCO_comm C B']

theorem FCO_smul_left (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : OE c Λ) :
    FCO C (r • A) B = r • FCO C A B := by
  simp only [FCO, map_smul, smul_mul_assoc, smul_sub]

theorem FCO_smul_right (C : Matrix Λ Λ ℂ) (r : ℂ) (A B : OE c Λ) :
    FCO C A (r • B) = r • FCO C A B := by
  rw [FCO_comm, FCO_smul_left, FCO_comm]

theorem FCO_sum_left {ι : Type*} (s : Finset ι) (C : Matrix Λ Λ ℂ) (A : ι → OE c Λ)
    (B : OE c Λ) : FCO C (∑ i ∈ s, A i) B = ∑ i ∈ s, FCO C (A i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FCO]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, FCO_add_left, ih]

theorem FCO_sum_right {ι : Type*} (s : Finset ι) (C : Matrix Λ Λ ℂ) (A : OE c Λ)
    (B : ι → OE c Λ) : FCO C A (∑ i ∈ s, B i) = ∑ i ∈ s, FCO C A (B i) := by
  rw [FCO_comm, FCO_sum_left]; simp only [FCO_comm C A]

theorem FCO_emb (C : Matrix Λ Λ ℂ) (x y : Step.EvR Λ) :
    FCO C (emb x : OE c Λ) (emb y) = emb (Step2.FCE C x y) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;>
    simp [FCO, Step2.FCE, FC, Case.tau_of_even c (expLC_even (-C) (Step.mem_Ev.1 x.2))]

/-! ### The exponential -/

theorem nilExp_of_not {A : Type*} [Ring A] [Module ℚ A] {a : A} (h : ¬ IsNilpotent a) :
    IsNilpotent.exp a = 0 := by
  have : nilpotencyClass a = 0 := by
    rw [nilpotencyClass]
    have : {k | a ^ k = 0} = (∅ : Set ℕ) :=
      Set.eq_empty_of_forall_notMem fun k hk => h ⟨k, hk⟩
    rw [this, Nat.sInf_empty]
  rw [IsNilpotent.exp, this, range_zero, sum_empty]

theorem isNilpotent_of_bulk {F : OE c Λ} (h : IsNilpotent (bulk F)) : IsNilpotent F := by
  rw [eq_emb_add_πobs F]
  exact (Commute.all _ _).isNilpotent_add (h.map emb) (isNilpotent_of_obs (bulk_πobs F))

/-- `bulk (e^F) = e^{bulk F}` for every even `F` (both are `0` unless `F` is nilpotent). -/
theorem bulk_oexp' (F : OE c Λ) : bulk (oexp F) = Step.gexp (bulk F) := by
  by_cases h : IsNilpotent (bulk F)
  · exact IsNilpotent.map_exp (isNilpotent_of_bulk h) bulk
  · have h' : ¬ IsNilpotent F := fun hF => h (hF.map bulk)
    rw [oexp, Step.gexp, nilExp_of_not h, nilExp_of_not h', map_zero]

theorem bulk_oexp_of_obs {F : OE c Λ} (hF : bulk F = 0) : bulk (oexp F) = 1 := by
  rw [bulk_oexp', hF, Step.gexp, IsNilpotent.exp_zero]

/-- `e^{x} • e^{F}` for a bulk constant `x` and an even element `F` (the extended `e^{u}`). -/
def expU (x : ℂ) (F : OE c Λ) : OE c Λ := Complex.exp x • oexp F

theorem bulk_expU_obs (x : ℂ) {F : OE c Λ} (hF : bulk F = 0) :
    bulk (expU x F) = algebraMap ℂ (Step.EvR Λ) (Complex.exp x) := by
  rw [expU, map_smul, bulk_oexp_of_obs hF, Algebra.algebraMap_eq_smul_one]

/-! ### Families -/

/-- The bulk components of a family. -/
def bulkF {ι : Type*} (F : ι → OE c Λ) : ι → Step.EvR Λ := fun i => bulk (F i)

@[simp] theorem bulkF_apply {ι : Type*} (F : ι → OE c Λ) (i : ι) : bulkF F i = bulk (F i) := rfl

/-- The embedding of a bulk family. -/
def embF {ι : Type*} (F : ι → Step.EvR Λ) : ι → OE c Λ := fun i => emb (F i)

@[simp] theorem bulkF_embF {ι : Type*} (F : ι → Step.EvR Λ) : bulkF (embF F : ι → OE c Λ) = F :=
  rfl

end

end Obs2
