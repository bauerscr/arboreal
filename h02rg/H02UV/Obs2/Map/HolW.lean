import Obs2.Map.Ops
import Step.Hol
import Flow.Spaces

/-!
# Weak holomorphy in a finite-dimensional algebra

`HolW f`: every linear functional of `f` is differentiable. In a finite-dimensional algebra this is
closed under linear maps, products and polynomials (`HolW.map`, `HolW.mul`, `HolW.prod`), and agrees
with the coefficient-wise holomorphy of `Step.Hol`/`Step.HolE` (`HolW.of_hol`, `HolW.hol`,
`HolW.of_holE`). The algebra with sources `OE c Λ` is finite-dimensional (`finiteDimensional_OE`),
and `oexp` preserves `HolW` (`HolW.oexp`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Step

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [AddCommGroup M] [Module ℂ M] {M' : Type*} [AddCommGroup M'] [Module ℂ M']

/-- **Weak holomorphy**: all linear functionals of `f` are differentiable. -/
def HolW (f : E → M) : Prop := ∀ ℓ : M →ₗ[ℂ] ℂ, Differentiable ℂ (fun e => ℓ (f e))

theorem HolW.map {f : E → M} (hf : HolW f) (T : M →ₗ[ℂ] M') : HolW (fun e => T (f e)) :=
  fun ℓ => hf (ℓ.comp T)

theorem HolW.const (x : M) : HolW (fun _ : E => x) := fun _ => differentiable_const _

theorem HolW.add {f g : E → M} (hf : HolW f) (hg : HolW g) : HolW (fun e => f e + g e) :=
  fun ℓ => by simp only [map_add]; exact (hf ℓ).add (hg ℓ)

theorem HolW.neg {f : E → M} (hf : HolW f) : HolW (fun e => -f e) :=
  fun ℓ => by simp only [map_neg]; exact (hf ℓ).neg

theorem HolW.sub {f g : E → M} (hf : HolW f) (hg : HolW g) : HolW (fun e => f e - g e) :=
  fun ℓ => by simp only [map_sub]; exact (hf ℓ).sub (hg ℓ)

theorem HolW.smul {c : E → ℂ} {f : E → M} (hc : Differentiable ℂ c) (hf : HolW f) :
    HolW (fun e => c e • f e) :=
  fun ℓ => by simp only [map_smul, smul_eq_mul]; exact hc.mul (hf ℓ)

theorem HolW.sum {ι : Type*} (s : Finset ι) {f : ι → E → M} (hf : ∀ i ∈ s, HolW (f i)) :
    HolW (fun e => ∑ i ∈ s, f i e) :=
  fun ℓ => by simp only [map_sum]; exact Differentiable.fun_sum fun i hi => hf i hi ℓ

theorem HolW.congr {f g : E → M} (hf : HolW f) (h : ∀ e, g e = f e) : HolW g := by
  have : g = f := funext h
  rwa [this]

section Fin

variable [FiniteDimensional ℂ M]

theorem HolW.bilin {f : E → M} {g : E → M'} (hf : HolW f) (hg : HolW g)
    (B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ) : Differentiable ℂ (fun e => B (f e) (g e)) := by
  set b := Module.finBasis ℂ M
  have h : (fun e => B (f e) (g e)) = fun e => ∑ i, b.coord i (f e) * B (b i) (g e) :=
    funext fun e => by
      conv_lhs => rw [← b.sum_repr (f e)]
      simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Module.Basis.coord_apply]
  rw [h]
  exact Differentiable.fun_sum fun i _ => (hf (b.coord i)).mul (hg (B (b i)))

variable {R : Type*} [CommRing R] [Algebra ℂ R] [FiniteDimensional ℂ R]

theorem HolW.mul {f g : E → R} (hf : HolW f) (hg : HolW g) : HolW (fun e => f e * g e) :=
  fun ℓ => hf.bilin hg ((LinearMap.mul ℂ R).compr₂ ℓ)

theorem HolW.pow {f : E → R} (hf : HolW f) (k : ℕ) : HolW (fun e => f e ^ k) := by
  induction k with
  | zero => simpa using HolW.const (E := E) (1 : R)
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem HolW.prod {ι : Type*} (s : Finset ι) {f : ι → E → R} (hf : ∀ i ∈ s, HolW (f i)) :
    HolW (fun e => ∏ i ∈ s, f i e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HolW.const (E := E) (1 : R)
  | insert a s ha ih =>
    simp only [prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem HolW.algMap {c : E → ℂ} (hc : Differentiable ℂ c) :
    HolW (fun e => algebraMap ℂ R (c e)) :=
  (HolW.smul hc (HolW.const (1 : R))).congr fun e => by
    simp only [Algebra.algebraMap_eq_smul_one]

end Fin

end Gen

/-! ### Grassmann algebras -/

section Grass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {I : Type*} [DecidableEq I] [Fintype I]

theorem HolW.hol {f : E → Grassmann.N I} (hf : HolW f) : Hol f := fun _ z => hf (coeffL z)

end Grass

/-! ### The algebra with sources -/

section SA

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The four components as a linear map. -/
def toTL : SA c Λ →ₗ[ℂ] N Λ × N Λ × N Λ × N Λ where
  toFun F := (F.e, F.a, F.b, F.ab)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The component `F_∅` as a linear map. -/
def eL : SA c Λ →ₗ[ℂ] N Λ := (LinearMap.fst ℂ _ _).comp toTL
/-- The component `F_a` as a linear map. -/
def aL : SA c Λ →ₗ[ℂ] N Λ := (LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp toTL)
/-- The component `F_b` as a linear map. -/
def bL : SA c Λ →ₗ[ℂ] N Λ :=
  (LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp toTL))
/-- The component `F_ab` as a linear map. -/
def abL : SA c Λ →ₗ[ℂ] N Λ :=
  (LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp toTL))

@[simp] theorem eL_apply (F : SA c Λ) : eL F = F.e := rfl
@[simp] theorem aL_apply (F : SA c Λ) : aL F = F.a := rfl
@[simp] theorem bL_apply (F : SA c Λ) : bL F = F.b := rfl
@[simp] theorem abL_apply (F : SA c Λ) : abL F = F.ab := rfl

instance finiteDimensional_SA : FiniteDimensional ℂ (SA c Λ) :=
  Module.Finite.of_injective (toTL (c := c) (Λ := Λ)) fun F G h => by
    simp only [toTL, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact SA.ext h1 h2 h3 h4

instance finiteDimensional_OE : FiniteDimensional ℂ (OE c Λ) :=
  Module.Finite.of_injective (OEv c Λ).val.toLinearMap Subtype.val_injective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function into `OE` is weakly holomorphic iff its image in `SA` is. -/
theorem HolW.coe {f : E → OE c Λ} (hf : HolW f) : HolW (fun e => (f e : SA c Λ)) :=
  hf.map (OEv c Λ).val.toLinearMap

theorem HolW.e {f : E → OE c Λ} (hf : HolW f) : Hol (fun e => (f e : SA c Λ).e) :=
  (hf.coe.map eL).hol

/-- The bulk constant `ε(F_∅)` is differentiable. -/
theorem HolW.eps_e {f : E → OE c Λ} (hf : HolW f) :
    Differentiable ℂ (fun e => ε ((f e : SA c Λ).e)) :=
  hf.e.lin (Grassmann.ε (Λ := Λ)).toLinearMap

/-- **`oexp` preserves weak holomorphy** (for `ε(F_∅) = 0`). -/
theorem HolW.oexp {f : E → OE c Λ} (hf : HolW f) (h0 : ∀ e, ε ((f e : SA c Λ).e) = 0) :
    HolW (fun e => Obs.oexp (f e)) :=
  (HolW.sum _ fun i _ => HolW.smul (differentiable_const _) (hf.pow i)).congr fun e =>
    coe_oexp (pow_eq_zero_of_ε (h0 e))

theorem HolW.expU {x : E → ℂ} (hx : Differentiable ℂ x) {f : E → OE c Λ} (hf : HolW f)
    (h0 : ∀ e, ε ((f e : SA c Λ).e) = 0) : HolW (fun e => expU (x e) (f e)) :=
  HolW.smul hx.cexp (hf.oexp h0)

end SA

end

end Obs2
