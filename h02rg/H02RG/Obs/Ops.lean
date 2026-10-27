import Obs.Algebra
import Step.ExpNorm
import Step.SymAlg

/-!
# Operations on the algebra with source fields

* `thetaS`, `inclS` (on `SA`) and `thetaO`, `inclO` (on even elements `OE`) are the doubling
  map `θ` and the inclusion `𝒩(Λ) ⊆ 𝒩(Λ ⊔ Λ)`, applied componentwise (the source fields are
  constants: `θ σ = σ`).  They are algebra homs.
* `ECS C`, `ECO C` are `𝔼_C`, applied componentwise (`𝔼_C` is an even operator in `ζ` and
  commutes with the source fields); `ECO_inclO_mul : 𝔼_C (ι a · g) = a 𝔼_C g`.
* `bulk` commutes with `θ`, `ι`, `𝔼_C` (`bulk_thetaO`, `bulk_inclO`, `bulk_ECO`), and
  `θ`, `ι`, `𝔼_C` commute with the embedding of bulk elements (`thetaO_emb`, …).
* `oexp` is the (nilpotent) exponential on even elements; an even element with `ε(F_∅) = 0` is
  nilpotent (`isNilpotent_of_ε`, indeed `F ^ (Nf Λ + 3) = 0`), `bulk (e^F) = e^{F_∅}`
  (`bulk_oexp`), `θ e^F = e^{θ F}`, and for observable `F` (`bulk F = 0`)
  `e^F = 1 + F + F²/2` (`oexp_of_obs`); in general
  `e^F = e^{F_∅} (1 + F^obs + (F^obs)²/2)` (`oexp_eq_mul`), so
  `π_obs e^F = e^{F_∅} (F^obs + (F^obs)²/2)` (`πobs_oexp`).
* `scalS t` is the `U(1)` action (`ψ ↦ tψ`, `ψ̄ ↦ t⁻¹ψ̄`, and in Case (1) `σ_a ↦ tσ_a`,
  `σ̄_b ↦ t⁻¹σ̄_b`; in Case (2) `σ_x = ϑ̄_xϑ_x` is invariant); `IsSymS F` (`F` is `U(1)`
  invariant) is `scalS 2 F = F` as in `Step.SymAlg`.  `isSymS_iff_one`/`isSymS_iff_two` give the
  component description of the text: in Case (1) `F_∅, F_ab` invariant, `F_a` has one more
  barred factor (eigenvalue `2⁻¹` of `scal 2`) and `F_b` one more unbarred factor (eigenvalue
  `2`); in Case (2) all components are invariant.
* `epsS`/`epsO` set `ψ = 0` componentwise; `omS C F = epsS (𝔼_C θ F)` is the full Gaussian
  expectation, componentwise `⟨F_x⟩_C` (`omS_e` etc.).
* `logObs G ginv` is the logarithm `log(G / G_∅)` of an even element with invertible bulk
  component (`ginv * bulk G = 1`): `G = G_∅ e^{logObs G ginv}` (`eq_mul_oexp_logObs`), it is
  the unique observable element with this property (`logObs_unique`), and
  `(log)_a = G_a/G_∅`, `(log)_b = G_b/G_∅`, `(log)_ab = G_ab/G_∅ - s G_a G_b / G_∅²`
  (`logObs_a`, `logObs_ab`), i.e. `+ G_a G_b/G_∅²` in Case (1) and `- G_a G_b/G_∅²` in Case (2).
  The derivatives `∂_{σ̄_b} ∂_{σ_a}` (Case (1)), `∂_{σ_b} ∂_{σ_a}` (Case (2)) at `σ = 0` of an
  element are its `ab` component, and `∂_{σ_a}` at `σ = 0` its `a` component (with the order of
  the derivatives as in `e:s5cora`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA

variable {c : Case} {Λ Λ' : Type*}

/-! ### `θ`, the inclusion and `𝔼_C` -/

section Maps

variable [DecidableEq Λ]

theorem theta_inv' (x : N Λ) : theta (inv' x) = inv' (theta x) := (Grassmann.inv'_map thetaV x).symm

theorem incl_inv' (x : N Λ) : incl (inv' x) = inv' (incl x) := (Grassmann.inv'_map inlV x).symm

/-- `θ` on the amended algebra. -/
def thetaS : SA c Λ →ₐ[ℂ] SA c (Λ ⊕ Λ) := mapS theta theta_inv'

/-- The inclusion `𝒩(Λ) ⊆ 𝒩(Λ ⊔ Λ)` on the amended algebra. -/
def inclS : SA c Λ →ₐ[ℂ] SA c (Λ ⊕ Λ) := mapS incl incl_inv'

/-- `θ` on even elements. -/
def thetaO : OE c Λ →ₐ[ℂ] OE c (Λ ⊕ Λ) := mapO theta theta_inv'

/-- The inclusion on even elements. -/
def inclO : OE c Λ →ₐ[ℂ] OE c (Λ ⊕ Λ) := mapO incl incl_inv'

@[simp] theorem coe_thetaO (F : OE c Λ) : (thetaO F : SA c (Λ ⊕ Λ)) = thetaS (F : SA c Λ) := rfl
@[simp] theorem coe_inclO (F : OE c Λ) : (inclO F : SA c (Λ ⊕ Λ)) = inclS (F : SA c Λ) := rfl

@[simp] theorem thetaS_e (F : SA c Λ) : (thetaS F).e = theta F.e := rfl
@[simp] theorem thetaS_a (F : SA c Λ) : (thetaS F).a = theta F.a := rfl
@[simp] theorem thetaS_b (F : SA c Λ) : (thetaS F).b = theta F.b := rfl
@[simp] theorem thetaS_ab (F : SA c Λ) : (thetaS F).ab = theta F.ab := rfl
@[simp] theorem inclS_e (F : SA c Λ) : (inclS F).e = incl F.e := rfl
@[simp] theorem inclS_a (F : SA c Λ) : (inclS F).a = incl F.a := rfl
@[simp] theorem inclS_b (F : SA c Λ) : (inclS F).b = incl F.b := rfl
@[simp] theorem inclS_ab (F : SA c Λ) : (inclS F).ab = incl F.ab := rfl

theorem bulk_thetaO (F : OE c Λ) : bulk (thetaO F) = Step.thetaE (bulk F) := rfl
theorem bulk_inclO (F : OE c Λ) : bulk (inclO F) = Step.inclE (bulk F) := rfl

theorem thetaO_emb (x : Step.EvR Λ) : thetaO (emb x : OE c Λ) = emb (Step.thetaE x) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

variable [Fintype Λ]

/-- `𝔼_C` on the amended algebra (componentwise). -/
def ECS (C : Matrix Λ Λ ℝ) : SA c (Λ ⊕ Λ) →ₗ[ℂ] SA c Λ := mapL (EC C)

@[simp] theorem ECS_e (C : Matrix Λ Λ ℝ) (F : SA c (Λ ⊕ Λ)) : (ECS C F).e = EC C F.e := rfl
@[simp] theorem ECS_a (C : Matrix Λ Λ ℝ) (F : SA c (Λ ⊕ Λ)) : (ECS C F).a = EC C F.a := rfl
@[simp] theorem ECS_b (C : Matrix Λ Λ ℝ) (F : SA c (Λ ⊕ Λ)) : (ECS C F).b = EC C F.b := rfl
@[simp] theorem ECS_ab (C : Matrix Λ Λ ℝ) (F : SA c (Λ ⊕ Λ)) : (ECS C F).ab = EC C F.ab := rfl

/-- `𝔼_C` on even elements. -/
def ECO (C : Matrix Λ Λ ℝ) : OE c (Λ ⊕ Λ) →ₗ[ℂ] OE c Λ :=
  (((ECS C).comp (OEv c (Λ ⊕ Λ)).val.toLinearMap).codRestrict (OEv c Λ).toSubmodule fun F => by
    obtain ⟨h1, h2, h3, h4⟩ := mem_OEv.1 F.2
    refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val, ECS_e,
        ECS_a, ECS_b, ECS_ab, ← Step.EC_inv', h1, h2, h3, h4, map_smul])

@[simp] theorem coe_ECO (C : Matrix Λ Λ ℝ) (F : OE c (Λ ⊕ Λ)) :
    (ECO C F : SA c Λ) = ECS C (F : SA c (Λ ⊕ Λ)) := rfl

theorem bulk_ECO (C : Matrix Λ Λ ℝ) (F : OE c (Λ ⊕ Λ)) : bulk (ECO C F) = Step.ECE C (bulk F) :=
  rfl

/-- `𝔼_C (ι a · g) = a 𝔼_C g`. -/
theorem ECS_inclS_mul (C : Matrix Λ Λ ℝ) (F : SA c Λ) (G : SA c (Λ ⊕ Λ)) :
    ECS C (inclS F * G) = F * ECS C G := by
  ext <;> simp only [ECS_e, ECS_a, ECS_b, ECS_ab, mul_e, mul_a, mul_b, mul_ab, inclS_e, inclS_a,
    inclS_b, inclS_ab, map_add, map_smul, Case.tau_comm c incl incl_inv', EC_incl_mul]

theorem ECO_inclO_mul (C : Matrix Λ Λ ℝ) (F : OE c Λ) (G : OE c (Λ ⊕ Λ)) :
    ECO C (inclO F * G) = F * ECO C G :=
  Subtype.ext (ECS_inclS_mul C (F : SA c Λ) (G : SA c (Λ ⊕ Λ)))

theorem ECO_one (C : Matrix Λ Λ ℝ) : ECO C (1 : OE c (Λ ⊕ Λ)) = 1 := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [EC_one]

theorem ECO_inclO (C : Matrix Λ Λ ℝ) (F : OE c Λ) : ECO C (inclO F) = F := by
  have := ECO_inclO_mul C F 1
  rw [mul_one, ECO_one, mul_one] at this
  exact this

/-- `𝔼_{C_2} θ ∘ 𝔼_{C_1} θ = 𝔼_{C_1 + C_2} θ` (`e:E-semigroup`). -/
theorem ECO_thetaO_comp (C₁ C₂ : Matrix Λ Λ ℝ) (F : OE c Λ) :
    ECO C₂ (thetaO (ECO C₁ (thetaO F))) = ECO (C₁ + C₂) (thetaO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [EC_theta_comp]

/-- `𝔼_C θ` is `e^{ℒ_C}` componentwise (`e:fWick`). -/
theorem ECS_thetaS (C : Matrix Λ Λ ℝ) (F : SA c Λ) :
    ECS C (thetaS F) = ⟨expL C F.e, expL C F.a, expL C F.b, expL C F.ab⟩ := by
  ext <;> simp [EC_theta]

end Maps

/-! ### The exponential -/

section Exp

variable [DecidableEq Λ] [Fintype Λ]

/-- The exponential of an even element (meaningful for nilpotent elements). -/
def oexp (F : OE c Λ) : OE c Λ := IsNilpotent.exp F

theorem emb_pow_eq_zero {x : Step.EvR Λ} (hx : ε (x : N Λ) = 0) :
    (emb x : OE c Λ) ^ (Nf Λ + 1) = 0 := by
  rw [← map_pow, Step.pow_eq_zero_of_ε' hx (Nat.lt_succ_self _), map_zero]

/-- An even element with `ε(F_∅) = 0` is nilpotent: `F ^ (Nf Λ + 3) = 0`. -/
theorem pow_eq_zero_of_ε {F : OE c Λ} (hF : ε ((F : SA c Λ).e) = 0) : F ^ (Nf Λ + 3) = 0 := by
  rw [eq_emb_add_πobs F]
  exact (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (emb_pow_eq_zero hF)
    (OE.pow_three_eq_zero (bulk_πobs F)) (by omega)

theorem isNilpotent_of_ε {F : OE c Λ} (hF : ε ((F : SA c Λ).e) = 0) : IsNilpotent F :=
  ⟨_, pow_eq_zero_of_ε hF⟩

theorem isNilpotent_of_obs {F : OE c Λ} (hF : bulk F = 0) : IsNilpotent F :=
  ⟨3, OE.pow_three_eq_zero hF⟩

theorem ε_bulk_eq_zero_of_obs {F : OE c Λ} (hF : bulk F = 0) : ε ((F : SA c Λ).e) = 0 := by
  rw [← coe_bulk, hF]; simp

theorem coe_oexp {F : OE c Λ} {k : ℕ} (hk : F ^ k = 0) :
    oexp F = ∑ i ∈ range k, ((i.factorial : ℂ)⁻¹) • F ^ i := by
  rw [oexp, IsNilpotent.exp_eq_sum hk]
  refine sum_congr rfl fun i _ => ?_
  rw [OE.qsmul_eq]; push_cast; rfl

/-- For observable `F`: `e^F = 1 + F + F²/2`. -/
theorem oexp_of_obs {F : OE c Λ} (hF : bulk F = 0) :
    oexp F = 1 + F + (1 / 2 : ℂ) • F ^ 2 := by
  rw [coe_oexp (OE.pow_three_eq_zero hF)]
  simp [sum_range_succ]

theorem bulk_oexp {F : OE c Λ} (hF : ε ((F : SA c Λ).e) = 0) :
    bulk (oexp F) = Step.gexp (bulk F) :=
  IsNilpotent.map_exp (isNilpotent_of_ε hF) bulk

theorem oexp_emb {x : Step.EvR Λ} (hx : ε (x : N Λ) = 0) :
    oexp (emb x : OE c Λ) = emb (Step.gexp x) :=
  (IsNilpotent.map_exp (Step.isNilpotent_of_ε' hx) emb).symm

theorem oexp_add {F G : OE c Λ} (hF : IsNilpotent F) (hG : IsNilpotent G) :
    oexp (F + G) = oexp F * oexp G :=
  IsNilpotent.exp_add_of_commute (Commute.all _ _) hF hG

theorem oexp_zero : oexp (0 : OE c Λ) = 1 := IsNilpotent.exp_zero

/-- `e^F = e^{F_∅} (1 + F^obs + (F^obs)²/2)`. -/
theorem oexp_eq_mul {F : OE c Λ} (hF : ε ((F : SA c Λ).e) = 0) :
    oexp F = emb (Step.gexp (bulk F)) * (1 + πobs F + (1 / 2 : ℂ) • πobs F ^ 2) := by
  conv_lhs => rw [eq_emb_add_πobs F]
  rw [oexp_add (isNilpotent_of_ε (F := emb (bulk F)) hF) (isNilpotent_of_obs (bulk_πobs F)),
    oexp_emb hF, oexp_of_obs (bulk_πobs F)]

theorem πobs_emb_mul {x : Step.EvR Λ} {G : OE c Λ} (hG : bulk G = 0) :
    πobs ((emb x : OE c Λ) * G) = emb x * G := by
  have h := eq_emb_add_πobs ((emb x : OE c Λ) * G)
  rw [map_mul, hG, mul_zero, map_zero, zero_add] at h
  exact h.symm

theorem πobs_emb (x : Step.EvR Λ) : πobs (emb x : OE c Λ) = 0 := by
  have h := eq_emb_add_πobs (emb x : OE c Λ)
  rw [bulk_emb] at h
  exact add_eq_left.1 h.symm

theorem thetaO_oexp {F : OE c Λ} (hF : ε ((F : SA c Λ).e) = 0) :
    thetaO (oexp F) = oexp (thetaO F) :=
  IsNilpotent.map_exp (isNilpotent_of_ε hF) thetaO

theorem inclO_oexp {F : OE c Λ} (hF : ε ((F : SA c Λ).e) = 0) :
    inclO (oexp F) = oexp (inclO F) :=
  IsNilpotent.map_exp (isNilpotent_of_ε hF) inclO

end Exp

/-! ### `U(1)` invariance -/

section Sym

variable [DecidableEq Λ]

/-- The scaling factor of `σ_a`. -/
def Case.ca (c : Case) (t : ℂ) : ℂ := match c with
  | .one => t
  | .two => 1

/-- The scaling factor of `σ̄_b` (Case (1)) resp. `σ_b` (Case (2)). -/
def Case.cb (c : Case) (t : ℂ) : ℂ := match c with
  | .one => t⁻¹
  | .two => 1

theorem scal_inv' (t : ℂ) (x : N Λ) : Step.scal Λ t (inv' x) = inv' (Step.scal Λ t x) :=
  (Grassmann.inv'_map (Step.scalV Λ t) x).symm

/-- The `U(1)` action on the amended algebra. -/
def scalS (t : ℂ) : SA c Λ →ₐ[ℂ] SA c Λ where
  toFun F := ⟨Step.scal Λ t F.e, c.ca t • Step.scal Λ t F.a, c.cb t • Step.scal Λ t F.b,
    (c.ca t * c.cb t) • Step.scal Λ t F.ab⟩
  map_one' := by ext <;> simp
  map_mul' F G := by
    ext <;> simp only [mul_e, mul_a, mul_b, mul_ab, map_add, map_mul, map_smul,
      Case.tau_comm c (Step.scal Λ t) (scal_inv' t), smul_add, mul_smul_comm, smul_mul_assoc,
      smul_smul] <;> ring_nf
  map_zero' := by ext <;> simp
  map_add' F G := by ext <;> simp [smul_add]
  commutes' r := by ext <;> simp

/-- `U(1)` invariance. -/
def IsSymS (F : SA c Λ) : Prop := scalS 2 F = F

/-- The `U(1)`-invariant elements. -/
def SymSA (c : Case) (Λ : Type*) [DecidableEq Λ] : Subalgebra ℂ (SA c Λ) :=
  AlgHom.equalizer (scalS 2) (AlgHom.id ℂ _)

theorem mem_SymSA {F : SA c Λ} : F ∈ SymSA c Λ ↔ IsSymS F := by
  simp [SymSA, AlgHom.mem_equalizer, IsSymS]

/-- Case (1): `F_∅, F_ab` are invariant, `F_a` has one more barred factor, `F_b` one more
unbarred factor. -/
theorem isSymS_iff_one (F : SA .one Λ) :
    IsSymS F ↔ Step.scal Λ 2 F.e = F.e ∧ Step.scal Λ 2 F.a = (2⁻¹ : ℂ) • F.a ∧
      Step.scal Λ 2 F.b = (2 : ℂ) • F.b ∧ Step.scal Λ 2 F.ab = F.ab := by
  have h2 : (2 : ℂ) * 2⁻¹ = 1 := by norm_num
  simp only [IsSymS, scalS, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    SA.ext_iff, Case.ca, Case.cb, h2, one_smul]
  constructor
  · rintro ⟨h1, h2', h3, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · have := congrArg ((2⁻¹ : ℂ) • ·) h2'
      simpa [smul_smul] using this
    · have := congrArg ((2 : ℂ) • ·) h3
      simpa [smul_smul] using this
  · rintro ⟨h1, h2', h3, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · rw [h2', smul_smul]; norm_num
    · rw [h3, smul_smul]; norm_num

/-- Case (2): all components are invariant. -/
theorem isSymS_iff_two (F : SA .two Λ) :
    IsSymS F ↔ Step.scal Λ 2 F.e = F.e ∧ Step.scal Λ 2 F.a = F.a ∧
      Step.scal Λ 2 F.b = F.b ∧ Step.scal Λ 2 F.ab = F.ab := by
  simp [IsSymS, scalS, SA.ext_iff, Case.ca, Case.cb]

end Sym

/-! ### Setting `ψ = 0` and the full Gaussian expectation -/

section Eps

/-- `x ↦ ε(x) 1`, setting `ψ = 0`. -/
def epsN : N Λ →ₐ[ℂ] N Λ := (Algebra.ofId ℂ (N Λ)).comp ε

theorem epsN_inv' (x : N Λ) : epsN (inv' x) = inv' (epsN x) := by
  simp [epsN, algebraMapInv_inv']

/-- Setting `ψ = 0` componentwise. -/
def epsS : SA c Λ →ₐ[ℂ] SA c Λ := mapS epsN epsN_inv'

/-- Setting `ψ = 0` on even elements. -/
def epsO : OE c Λ →ₐ[ℂ] OE c Λ := mapO epsN epsN_inv'

@[simp] theorem epsS_e (F : SA c Λ) : (epsS F).e = algebraMap ℂ (N Λ) (ε F.e) := rfl
@[simp] theorem epsS_a (F : SA c Λ) : (epsS F).a = algebraMap ℂ (N Λ) (ε F.a) := rfl
@[simp] theorem epsS_b (F : SA c Λ) : (epsS F).b = algebraMap ℂ (N Λ) (ε F.b) := rfl
@[simp] theorem epsS_ab (F : SA c Λ) : (epsS F).ab = algebraMap ℂ (N Λ) (ε F.ab) := rfl
@[simp] theorem coe_epsO (F : OE c Λ) : (epsO F : SA c Λ) = epsS (F : SA c Λ) := rfl

theorem ε_eq_zero_of_isOdd {x : N Λ} (hx : Step.IsOdd x) : ε x = 0 := by
  have h := algebraMapInv_inv' (R := ℂ) (M := V Λ) x
  rw [show inv' x = -x from hx, map_neg] at h
  have : (2 : ℂ) * ε x = 0 := by
    have : ε x = -ε x := h.symm
    linear_combination this
  simpa using this

/-- In Case (1), `ε(F_a) = ε(F_b) = 0` for even `F`. -/
theorem ε_a_one (F : OE .one Λ) : ε ((F : SA .one Λ).a) = 0 := ε_eq_zero_of_isOdd F.isOdd_a

variable [DecidableEq Λ] [Fintype Λ]

/-- The full Gaussian expectation `ψ ↦ 0` of `𝔼_C θ F`, componentwise `⟨F_x⟩_C`. -/
def omS (C : Matrix Λ Λ ℝ) (F : SA c Λ) : SA c Λ := epsS (ECS C (thetaS F))

theorem omega_eq' (C : Matrix Λ Λ ℝ) (x : N Λ) : omega C x = ε (EC C (theta x)) := by
  rw [omega, EC_theta]

@[simp] theorem omS_e (C : Matrix Λ Λ ℝ) (F : SA c Λ) :
    (omS C F).e = algebraMap ℂ (N Λ) (omega C F.e) := by simp [omS, omega_eq']
@[simp] theorem omS_a (C : Matrix Λ Λ ℝ) (F : SA c Λ) :
    (omS C F).a = algebraMap ℂ (N Λ) (omega C F.a) := by simp [omS, omega_eq']
@[simp] theorem omS_b (C : Matrix Λ Λ ℝ) (F : SA c Λ) :
    (omS C F).b = algebraMap ℂ (N Λ) (omega C F.b) := by simp [omS, omega_eq']
@[simp] theorem omS_ab (C : Matrix Λ Λ ℝ) (F : SA c Λ) :
    (omS C F).ab = algebraMap ℂ (N Λ) (omega C F.ab) := by simp [omS, omega_eq']

end Eps

/-! ### The logarithm -/

section Log

variable [Fintype Λ]

/-- `log(G / G_∅) = X - X²/2` with `X = G_∅⁻¹ G^obs`, for `ginv = G_∅⁻¹`. -/
def logObs (G : OE c Λ) (ginv : Step.EvR Λ) : OE c Λ :=
  emb ginv * πobs G - (1 / 2 : ℂ) • (emb ginv * πobs G) ^ 2

variable [DecidableEq Λ]

section Comp

variable (G : OE c Λ) (ginv : Step.EvR Λ)

private theorem logObs_eq : (logObs G ginv : SA c Λ) = ((emb ginv * πobs G : OE c Λ) : SA c Λ) -
    (1 / 2 : ℂ) • (((emb ginv * πobs G) * (emb ginv * πobs G) : OE c Λ) : SA c Λ) := by
  rw [logObs, sq]; rfl

private theorem X_e : ((emb ginv * πobs G : OE c Λ) : SA c Λ).e = 0 := by
  rw [OE.mul_e]; simp [piobs_apply]

private theorem X_a : ((emb ginv * πobs G : OE c Λ) : SA c Λ).a = (ginv : N Λ) * (G : SA c Λ).a := by
  rw [OE.mul_a]; simp [piobs_apply]

private theorem X_b : ((emb ginv * πobs G : OE c Λ) : SA c Λ).b = (ginv : N Λ) * (G : SA c Λ).b := by
  rw [OE.mul_b]; simp [piobs_apply]

private theorem X_ab :
    ((emb ginv * πobs G : OE c Λ) : SA c Λ).ab = (ginv : N Λ) * (G : SA c Λ).ab := by
  rw [OE.mul_ab]; simp [piobs_apply]

/-- `(log G)_a = G_a / G_∅`. -/
theorem logObs_a : (logObs G ginv : SA c Λ).a = (ginv : N Λ) * (G : SA c Λ).a := by
  rw [logObs_eq, sub_a, smul_a, X_a, OE.mul_a (emb ginv * πobs G), X_e, X_a]; simp

/-- `(log G)_ab = G_ab / G_∅ - s G_a G_b / G_∅²`. -/
theorem logObs_ab : (logObs G ginv : SA c Λ).ab = (ginv : N Λ) * (G : SA c Λ).ab -
    c.s • ((ginv : N Λ) * ginv * ((G : SA c Λ).a * (G : SA c Λ).b)) := by
  rw [logObs_eq, sub_ab, smul_ab]
  have hg := Step.mem_Ev.1 ginv.2
  have pa : inv' ((ginv : N Λ) * (G : SA c Λ).a) = c.s • ((ginv : N Λ) * (G : SA c Λ).a) := by
    rw [map_mul, hg, G.par_a, mul_smul_comm]
  have pb : inv' ((ginv : N Λ) * (G : SA c Λ).b) = c.s • ((ginv : N Λ) * (G : SA c Λ).b) := by
    rw [map_mul, hg, G.par_b, mul_smul_comm]
  rw [X_ab, OE.mul_ab (emb ginv * πobs G), X_e, X_a, X_b, X_ab, mul_of_par c pb pa, zero_mul, mul_zero, zero_add, add_zero]
  have hc : (ginv : N Λ) * (G : SA c Λ).a * ((ginv : N Λ) * (G : SA c Λ).b) =
      (ginv : N Λ) * ginv * ((G : SA c Λ).a * (G : SA c Λ).b) := by
    rw [mul_assoc, ← mul_assoc (G : SA c Λ).a, ← mul_comm_of_even hg, mul_assoc, mul_assoc]
  rw [hc]
  module

end Comp

end Log

end

end Obs
