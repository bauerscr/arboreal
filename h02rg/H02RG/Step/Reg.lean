import Step.Continuity
import Step.DerivAux

/-!
# Regularity in a parameter: a generic framework

`Step/Continuity.lean` proves continuity in `m²` of `(u, V)_{j+1}` and `K_{j+1}` for fixed
`(V_j, K_j)`, coefficient-wise (`CC`, `CCE`).  For the flows we need continuity along families
`m ↦ (C(m), V(m), K(m))`, and in `sec:ward` also holomorphy in `b₀` (at fixed `m²`).  Both are
instances of a class of scalar functions `T → ℂ` closed under constants, `+`, `·`, `exp` and
modification off a domain `D` (`Reg`):

* `Reg.cont S` (`T` a topological space): `ContinuousOn · S`;
* `Reg.hol U` (`T = ℂ`): `DifferentiableOn ℂ · U`.

This file develops the coefficient-wise calculus for such a class (`RegN`, `RegE`: the analogues
of `CC`, `CCE`; `RegV`, `RegK`: of the continuous families `CV`, `CK`) and proves the
regularity of one step, `uVnext_reg` and `Knext_reg`.  For `Reg.cont S` all notions are
*definitionally* the continuity notions (`regN_cont_iff`, `regE_cont_iff`, `RegV.of_CV`,
`RegV.toCV`, `regK_cont_iff`).  The iteration along the bulk flow is in `Flow/Continuity.lean`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD Coup

/-! ### Continuous families of coupling constants and activities -/

section CVCK

variable {d L : ℕ} [NeZero L] {N : ℕ}

/-- A continuous family of coupling constants. -/
structure CV (S : Set ℝ) (W : ℝ → Vcoup) : Prop where
  z : ContinuousOn (fun m => (W m).z) S
  y : ContinuousOn (fun m => (W m).y) S
  a : ContinuousOn (fun m => (W m).a) S
  b : ContinuousOn (fun m => (W m).b) S

/-- A (coefficient-wise) continuous family of polymer activities. -/
def CK (S : Set ℝ) (K : ℝ → Act d L N) : Prop := ∀ X, CCE S (fun m => K m X)

end CVCK

/-! ### Regular scalar functions -/

/-- A class of "regular" scalar functions on a parameter space `T`: closed under constants,
sums, products, `exp`, and modification outside the domain `D`. -/
structure Reg (T : Type*) where
  /-- The domain. -/
  D : Set T
  /-- The regular functions. -/
  P : (T → ℂ) → Prop
  const : ∀ c : ℂ, P (fun _ => c)
  add : ∀ {f g : T → ℂ}, P f → P g → P (fun t => f t + g t)
  mul : ∀ {f g : T → ℂ}, P f → P g → P (fun t => f t * g t)
  exp : ∀ {f : T → ℂ}, P f → P (fun t => Complex.exp (f t))
  congr : ∀ {f g : T → ℂ}, P f → (∀ t ∈ D, g t = f t) → P g

namespace Reg

/-- Continuity on `S`. -/
def cont {T : Type*} [TopologicalSpace T] (S : Set T) : Reg T where
  D := S
  P f := ContinuousOn f S
  const _ := continuousOn_const
  add hf hg := hf.add hg
  mul hf hg := hf.mul hg
  exp hf := Complex.continuous_exp.comp_continuousOn hf
  congr hf h := hf.congr h

variable {T : Type*} {R : Reg T}

theorem of_eq {f g : T → ℂ} (hf : R.P f) (h : ∀ t, g t = f t) : R.P g := by
  rwa [show g = f from funext h]

theorem neg {f : T → ℂ} (hf : R.P f) : R.P (fun t => -f t) :=
  of_eq (R.mul (R.const (-1)) hf) fun t => by ring

theorem sub {f g : T → ℂ} (hf : R.P f) (hg : R.P g) : R.P (fun t => f t - g t) :=
  of_eq (R.add hf (neg hg)) fun t => by ring

theorem const_mul (c : ℂ) {f : T → ℂ} (hf : R.P f) : R.P (fun t => c * f t) :=
  R.mul (R.const c) hf

theorem mul_const {f : T → ℂ} (hf : R.P f) (c : ℂ) : R.P (fun t => f t * c) :=
  R.mul hf (R.const c)

theorem div_const {f : T → ℂ} (hf : R.P f) (c : ℂ) : R.P (fun t => f t / c) :=
  of_eq (R.mul hf (R.const c⁻¹)) fun t => by rw [div_eq_mul_inv]

theorem sum {ι : Type*} (s : Finset ι) {f : ι → T → ℂ} (hf : ∀ i ∈ s, R.P (f i)) :
    R.P (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact of_eq (R.const 0) fun t => by simp
  | insert a s ha ih =>
    exact of_eq (R.add (hf a (mem_insert_self a s)) (ih fun i hi => hf i (mem_insert_of_mem hi)))
      fun t => by rw [sum_insert ha]

theorem pow {f : T → ℂ} (hf : R.P f) (k : ℕ) : R.P (fun t => f t ^ k) := by
  induction k with
  | zero => exact of_eq (R.const 1) fun t => by simp
  | succ k ih => exact of_eq (R.mul ih hf) fun t => by rw [pow_succ]

/-- A real-valued continuous function, as a continuous complex-valued function. -/
theorem cont_ofReal {T : Type*} [TopologicalSpace T] {S : Set T} {f : T → ℝ}
    (hf : ContinuousOn f S) : (cont S).P (fun t => ((f t : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp_continuousOn hf

end Reg

/-! ### Coefficient-wise regularity of Grassmann-valued maps -/

section RegN

variable {T : Type*} {R : Reg T}
variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]

/-- Coefficient-wise regularity (for `Reg.cont S` this is `Step.CC S`). -/
def RegN (R : Reg T) (f : T → Grassmann.N I) : Prop :=
  ∀ n (z : Fin n → Sf I), R.P (fun t => coeff (f t) z)

theorem RegN.lin {f : T → Grassmann.N I} (hf : RegN R f) (ℓ : Grassmann.N I →ₗ[ℂ] ℂ) :
    R.P (fun t => ℓ (f t)) := by
  refine Reg.of_eq ?_ (fun t => expand ℓ (f t))
  refine Reg.sum _ fun n _ => Reg.sum _ fun z _ => ?_
  simp only [smul_eq_mul]
  exact R.mul (R.mul (R.const _) (hf n z)) (R.const _)

theorem RegN.bilin {f : T → Grassmann.N I} {g : T → Grassmann.N J} (hf : RegN R f)
    (hg : RegN R g) (B : Grassmann.N I →ₗ[ℂ] Grassmann.N J →ₗ[ℂ] ℂ) :
    R.P (fun t => B (f t) (g t)) := by
  refine Reg.of_eq ?_ (fun t => by rw [expand B (f t)])
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Reg.sum _ fun n _ => Reg.sum _ fun z _ => ?_
  exact R.mul (R.mul (R.const _) (hf n z)) (hg.lin _)

theorem RegN.map {f : T → Grassmann.N I} (hf : RegN R f)
    (T' : Grassmann.N I →ₗ[ℂ] Grassmann.N J) : RegN R (fun t => T' (f t)) := fun _ z =>
  hf.lin ((coeffL z).comp T')

theorem RegN.const (F : Grassmann.N I) : RegN R (fun _ => F) := fun _ _ => R.const _

theorem RegN.mul {f g : T → Grassmann.N I} (hf : RegN R f) (hg : RegN R g) :
    RegN R (fun t => f t * g t) := fun _ z =>
  hf.bilin hg ((LinearMap.mul ℂ (Grassmann.N I)).compr₂ (coeffL z))

theorem RegN.add {f g : T → Grassmann.N I} (hf : RegN R f) (hg : RegN R g) :
    RegN R (fun t => f t + g t) := fun n z =>
  Reg.of_eq (R.add (hf n z) (hg n z)) fun _ => coeff_add _ _ _

theorem RegN.smul {c : T → ℂ} {f : T → Grassmann.N I} (hc : R.P c) (hf : RegN R f) :
    RegN R (fun t => c t • f t) := fun n z =>
  Reg.of_eq (R.mul hc (hf n z)) fun _ => coeff_smul _ _ _

theorem RegN.neg {f : T → Grassmann.N I} (hf : RegN R f) : RegN R (fun t => -f t) := fun n z =>
  Reg.of_eq (Reg.neg (hf n z)) fun t => by
    show coeff (-f t) z = -coeff (f t) z
    rw [show -f t = (-1 : ℂ) • f t by simp, coeff_smul]; ring

theorem RegN.sub {f g : T → Grassmann.N I} (hf : RegN R f) (hg : RegN R g) :
    RegN R (fun t => f t - g t) := fun n z =>
  Reg.of_eq ((hf.add hg.neg) n z) fun t => by
    show coeff (f t - g t) z = coeff (f t + -g t) z
    rw [sub_eq_add_neg]

theorem RegN.sum {ι : Type*} (s : Finset ι) {f : ι → T → Grassmann.N I}
    (hf : ∀ i ∈ s, RegN R (f i)) : RegN R (fun t => ∑ i ∈ s, f i t) := fun n z =>
  Reg.of_eq (Reg.sum s fun i hi => hf i hi n z) fun _ => coeff_sum _ _ _

theorem RegN.pow {f : T → Grassmann.N I} (hf : RegN R f) (k : ℕ) :
    RegN R (fun t => f t ^ k) := by
  induction k with
  | zero => simpa using RegN.const (R := R) (1 : Grassmann.N I)
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem RegN.congr {f g : T → Grassmann.N I} (hf : RegN R f) (h : ∀ t ∈ R.D, g t = f t) :
    RegN R g := fun n z => R.congr (hf n z) fun t ht => by simp only [h t ht]

theorem RegN.of_eq {f g : T → Grassmann.N I} (hf : RegN R f) (h : ∀ t, g t = f t) :
    RegN R g := by
  rwa [show g = f from funext h]

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem RegN.lzeta {C : T → Matrix Λ Λ ℝ} (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ)))
    {f : T → Grassmann.N (Λ ⊕ Λ)} (hf : RegN R f) :
    RegN R (fun t => Grassmann.Lζ (C t) (f t)) := by
  simp only [Lζ_apply]
  exact RegN.sum _ fun x _ => RegN.sum _ fun y _ => RegN.smul (hC x y) ((hf.map _).map _)

theorem RegN.lzeta_pow {C : T → Matrix Λ Λ ℝ} (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ)))
    {f : T → Grassmann.N (Λ ⊕ Λ)} (hf : RegN R f) (k : ℕ) :
    RegN R (fun t => (Grassmann.Lζ (C t) ^ k) (f t)) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => simpa [pow_succ', Module.End.mul_apply] using RegN.lzeta hC ih

theorem RegN.EC {C : T → Matrix Λ Λ ℝ} (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ)))
    {f : T → Grassmann.N (Λ ⊕ Λ)} (hf : RegN R f) : RegN R (fun t => EC (C t) (f t)) := by
  simp only [EC_eq_sum]
  exact RegN.sum _ fun i _ => RegN.smul (R.const _) ((RegN.lzeta_pow hC hf i).map proj.toLinearMap)

end RegN

/-! ### Even elements -/

section RegE

variable {T : Type*} {R : Reg T}
variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]

/-- Coefficient-wise regularity of maps into the even subalgebra (`CCE` for `Reg.cont S`). -/
def RegE (R : Reg T) (f : T → EvR I) : Prop := RegN R (fun t => (f t : Grassmann.N I))

theorem RegE.const (F : EvR I) : RegE R (fun _ => F) := RegN.const _

theorem RegE.mul {f g : T → EvR I} (hf : RegE R f) (hg : RegE R g) :
    RegE R (fun t => f t * g t) := RegN.mul hf hg

theorem RegE.sub {f g : T → EvR I} (hf : RegE R f) (hg : RegE R g) :
    RegE R (fun t => f t - g t) := RegN.sub hf hg

theorem RegE.neg {f : T → EvR I} (hf : RegE R f) : RegE R (fun t => -f t) := RegN.neg hf

theorem RegE.smul {c : T → ℂ} {f : T → EvR I} (hc : R.P c) (hf : RegE R f) :
    RegE R (fun t => c t • f t) := RegN.smul hc hf

theorem RegE.sum {ι : Type*} (s : Finset ι) {f : ι → T → EvR I} (hf : ∀ i ∈ s, RegE R (f i)) :
    RegE R (fun t => ∑ i ∈ s, f i t) := by
  unfold RegE
  simp only [AddSubmonoidClass.coe_finsetSum]
  exact RegN.sum s hf

theorem RegE.prod {ι : Type*} (s : Finset ι) {f : ι → T → EvR I} (hf : ∀ i ∈ s, RegE R (f i)) :
    RegE R (fun t => ∏ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RegE.const (R := R) (1 : EvR I)
  | insert a s ha ih =>
    simp only [prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem RegE.thetaE {f : T → EvR Λ} (hf : RegE R f) : RegE R (fun t => thetaE (f t)) :=
  RegN.map hf theta.toLinearMap

theorem RegE.inclE {f : T → EvR Λ} (hf : RegE R f) : RegE R (fun t => inclE (f t)) :=
  RegN.map hf incl.toLinearMap

theorem RegE.ECE {C : T → Matrix Λ Λ ℝ} (hC : ∀ x y, R.P (fun t => ((C t x y : ℝ) : ℂ)))
    {f : T → EvR (Λ ⊕ Λ)} (hf : RegE R f) : RegE R (fun t => ECE (C t) (f t)) :=
  RegN.EC hC hf

theorem RegE.gexp {f : T → EvR I} (hf : RegE R f) (h0 : ∀ t ∈ R.D, ε (f t : Grassmann.N I) = 0) :
    RegE R (fun t => gexp (f t)) := by
  refine RegN.congr (f := fun t => ∑ i ∈ range (Nf I + 1),
    ((i.factorial : ℂ)⁻¹) • (f t : Grassmann.N I) ^ i) ?_ fun t ht => ?_
  · exact RegN.sum _ fun i _ => RegN.smul (R.const _) (RegN.pow hf i)
  · exact coe_gexp (pow_eq_zero_of_ε' (h0 t ht) (Nat.lt_succ_self _))

/-- The coefficients of the value of an even element under a linear functional. -/
theorem RegE.lin {f : T → EvR I} (hf : RegE R f) (ℓ : EvR I →ₗ[ℂ] ℂ) :
    R.P (fun t => ℓ (f t)) := by
  obtain ⟨P, hP⟩ : ∃ P : Grassmann.N I →ₗ[ℂ] EvR I, ∀ x : EvR I, P x = x := by
    obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (Ev I).val.toLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    exact ⟨P, fun x => LinearMap.congr_fun hP x⟩
  exact Reg.of_eq (RegN.lin hf (ℓ.comp P)) fun t => by simp [hP]

theorem RegE.map' {f : T → EvR I} (hf : RegE R f) (T' : EvR I →ₗ[ℂ] EvR J) :
    RegE R (fun t => T' (f t)) := fun _ z =>
  hf.lin ((coeffL z).comp ((Ev J).val.toLinearMap.comp T'))

end RegE

/-! ### Coupling constants and activities -/

section Bulk

variable {T : Type*} {R : Reg T} {d L : ℕ} [NeZero L] {N : ℕ}

/-- A regular family of bulk coupling constants (`CV` for `Reg.cont S`). -/
structure RegV (R : Reg T) (W : T → Vcoup) : Prop where
  z : R.P (fun t => (W t).z)
  y : R.P (fun t => (W t).y)
  a : R.P (fun t => (W t).a)
  b : R.P (fun t => (W t).b)

/-- A (coefficient-wise) regular family of polymer activities (`CK` for `Reg.cont S`). -/
def RegK (R : Reg T) (K : T → Act d L N) : Prop := ∀ X, RegE R (fun t => K t X)

theorem RegV.of_CV {S : Set ℝ} {W : ℝ → Vcoup} (h : CV S W) : RegV (Reg.cont S) W :=
  ⟨h.z, h.y, h.a, h.b⟩

theorem RegV.toCV {S : Set ℝ} {W : ℝ → Vcoup} (h : RegV (Reg.cont S) W) : CV S W :=
  ⟨h.z, h.y, h.a, h.b⟩

theorem regK_cont_iff {S : Set ℝ} {K : ℝ → Act d L N} :
    RegK (Reg.cont S) K ↔ CK S K := Iff.rfl

theorem RegV.eval {W : T → Vcoup} (hW : RegV R W) (X : Finset (Lam d L N)) :
    RegN R (fun t => (W t).eval X) := by
  simp only [eval_eq_sum, Vsum]
  exact RegN.sum _ fun x _ => (((RegN.smul hW.y (RegN.const _)).add
    (RegN.smul (Reg.div_const hW.z 2) (RegN.const _))).add (RegN.smul hW.a (RegN.const _))).add
    (RegN.smul hW.b (RegN.const _))

theorem RegV.VE {W : T → Vcoup} (hW : RegV R W) (X : Finset (Lam d L N)) :
    RegE R (fun t => VE (W t) X) := hW.eval X

theorem RegK.LocE {K : T → Act d L N} (hK : RegK R K) (X Y Z : Finset (Lam d L N)) :
    RegE R (fun t => LocE Y Z (K t X)) := RegE.map' (hK X) (LocEL Y Z)

theorem RegK.Qb {K : T → Act d L N} (hK : RegK R K) (j : ℕ) (b : Fin d → ℕ) :
    RegE R (fun t => Qb j (K t) b) := by
  classical
  unfold Step.Qb
  split_ifs
  · exact RegE.sum _ fun X _ => hK.LocE _ _ _
  · exact RegE.const _

theorem RegK.Jb {K : T → Act d L N} (hK : RegK R K) (j : ℕ) (b : Fin d → ℕ)
    (X : Finset (Lam d L N)) : RegE R (fun t => Jb j (K t) b X) := by
  classical
  unfold Step.Jb
  split_ifs
  · exact (RegE.sum _ fun Y _ => hK.LocE _ _ _).neg
  · exact hK.LocE _ _ _
  · exact RegE.const _

theorem RegK.Kext {K : T → Act d L N} (hK : RegK R K) (j : ℕ) (X : Finset (Lam d L N)) :
    RegE R (fun t => Kext j (K t) X) := by
  unfold Step.Kext
  exact RegE.prod _ fun Y _ => hK Y

/-- Regularity of the coupling constants along regular families `(C(t), V(t), K(t))`. -/
theorem uVnext_reg (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {Cm : T → Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, R.P (fun t => ((Cm t x y : ℝ) : ℂ)))
    (hinv : ∀ t ∈ R.D, CovInv (Cm t)) (hsym : ∀ t ∈ R.D, ∀ x y, Cm t x y = Cm t y x)
    {W : T → Vcoup} {K : T → Act d L N} (hW : RegV R W) (hK : RegK R K)
    (hKj : ∀ t ∈ R.D, InK j (K t)) :
    R.P (fun t => (uVnext j (Cm t) (W t) (K t)).1) ∧
      RegV R (fun t => (uVnext j (Cm t) (W t) (K t)).2) := by
  have hLN : 3 ≤ L ^ N := (three_le_L hd hL).trans (Nat.le_self_pow (by omega) L)
  obtain ⟨Ψ, hΨ⟩ := exists_coupInv hd hLN (mem_blockIdx.1 (zero_mem_blockIdx j))
    (patch_blockSet hj (three_le_L hd hL) 0)
  have hG : RegN R (fun t => EC (Cm t) (theta ((W t).eval (blockSet j 0) -
      (Qb j (K t) 0 : Alg d L N)))) :=
    RegN.EC hC (((hW.eval _).sub (hK.Qb j 0)).map theta.toLinearMap)
  have key : ∀ i : Fin 5, R.P (fun t => cvec (uVnext j (Cm t) (W t) (K t)) i) :=
    fun i => R.congr (hG.lin ((LinearMap.proj i).comp Ψ)) fun t ht => by
      have hmem := EC_theta_VXspace (hinv t ht) (hsym t ht)
        (VXspace_sub (eval_mem_VXspace (W t) _) (Qb_mem hd hL (hKj t ht) (zero_mem_blockIdx j)))
      show _ = LinearMap.proj (R := ℂ) i (Ψ _)
      rw [hΨ _ hmem]
      rfl
  exact ⟨key 0, ⟨key 1, key 2, key 3, key 4⟩⟩

/-- Regularity of `K_{j+1}` along regular families `(C(t), V(t), K(t))`. -/
theorem Knext_reg (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {Cm : T → Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, R.P (fun t => ((Cm t x y : ℝ) : ℂ)))
    (hinv : ∀ t ∈ R.D, CovInv (Cm t)) (hsym : ∀ t ∈ R.D, ∀ x y, Cm t x y = Cm t y x)
    {W : T → Vcoup} {K : T → Act d L N} (hW : RegV R W) (hK : RegK R K)
    (hKj : ∀ t ∈ R.D, InK j (K t)) (U : Finset (Lam d L N)) :
    RegE R (fun t => Knext j (Cm t) (W t) (K t) U) := by
  obtain ⟨hu, hU⟩ := uVnext_reg hd hL hj hC hinv hsym hW hK hKj
  have hI : ∀ b, RegE R (fun t => Inext j (Cm t) (W t) (K t) b) := fun b => by
    unfold Inext
    exact RegE.smul (R.exp (Reg.neg (Reg.mul_const hu _)))
      (RegE.gexp (hU.VE _).neg fun t _ => by simp [eval_ε0])
  have hIP : ∀ X, RegE R (fun t => InextPow j (Cm t) (W t) (K t) X) := fun X => by
    unfold InextPow
    exact RegE.prod _ fun b _ => hI b
  have hdI : ∀ X, RegE R (fun t => dIPow j (Cm t) (W t) (K t) X) := fun X => by
    unfold dIPow dI
    exact RegE.prod _ fun b _ =>
      (RegE.gexp (hW.VE _).neg fun t _ => by simp [eval_ε0]).thetaE.sub (hI b).inclE
  have hKt : ∀ Z, RegE R (fun t => Ktil j (Cm t) (W t) (K t) Z) := fun Z => by
    unfold Ktil
    exact RegE.sum _ fun Y _ => (hK.Kext j _).thetaE.mul (hdI Y)
  have hKc : ∀ X, RegE R (fun t => Kchk j (Cm t) (W t) (K t) X) := fun X => by
    unfold Kchk KchkC
    exact RegE.prod _ fun Z _ => (hKt Z).sub (RegE.sum _ fun b _ => (hK.Jb j b Z).thetaE)
  unfold Knext
  exact RegE.smul (R.exp (Reg.mul_const hu _))
    (RegE.sum _ fun g _ => (hIP _).mul (RegE.ECE hC ((hKc g.2).mul
      (RegE.prod _ fun p _ => (hK.Jb j p.1 p.2).thetaE))))

end Bulk

end

end Step
