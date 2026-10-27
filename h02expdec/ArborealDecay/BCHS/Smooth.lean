module

public import ArborealDecay.Horo.SuperChange
public import ArborealDecay.Super.ComposeComp
public import ArborealDecay.Super.H24

/-!
# Smooth superfunctions

`SSmooth F`: every coordinate `ℓ ∘ F` of a `Gr O`-valued function is `C^∞`.  The class is closed
under the algebra operations, partial derivatives, and composition `g(S)` with functions `g` that
are smooth on an open set containing the bodies.  It is the regularity class in which the nilpotent
Taylor shifts of `ArborealDecay.Horo` are algebra homomorphisms (`ShiftAlg.lean`).
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset ArborealDecay.Super
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Every coordinate of `F` is smooth. -/
def SSmooth (F : Y → Gr O) : Prop := ∀ ℓ : Module.Dual ℝ (Gr O), ContDiff ℝ ∞ fun x => ℓ (F x)

theorem SSmooth.sdiff {F : Y → Gr O} (hF : SSmooth F) : SDiff F := fun ℓ =>
  (hF ℓ).differentiable (by simp)

theorem SSmooth.const (c : Gr O) : SSmooth fun _ : Y => c := fun _ => contDiff_const

theorem SSmooth.add {F G : Y → Gr O} (hF : SSmooth F) (hG : SSmooth G) :
    SSmooth fun x => F x + G x := fun ℓ => by
  simp only [map_add]; exact (hF ℓ).add (hG ℓ)

theorem SSmooth.neg {F : Y → Gr O} (hF : SSmooth F) : SSmooth fun x => -F x := fun ℓ => by
  simp only [map_neg]; exact (hF ℓ).neg

theorem SSmooth.sub {F G : Y → Gr O} (hF : SSmooth F) (hG : SSmooth G) :
    SSmooth fun x => F x - G x := fun ℓ => by
  simp only [map_sub]; exact (hF ℓ).sub (hG ℓ)

theorem SSmooth.smul {g : Y → ℝ} {F : Y → Gr O} (hg : ContDiff ℝ ∞ g) (hF : SSmooth F) :
    SSmooth fun x => g x • F x := fun ℓ => by
  simp only [map_smul, smul_eq_mul]; exact hg.mul (hF ℓ)

theorem SSmooth.smul_const {g : Y → ℝ} (hg : ContDiff ℝ ∞ g) (c : Gr O) :
    SSmooth fun x => g x • c := (SSmooth.const c).smul hg

theorem SSmooth.sum {ι : Type*} (s : Finset ι) {F : ι → Y → Gr O}
    (hF : ∀ i ∈ s, SSmooth (F i)) : SSmooth fun x => ∑ i ∈ s, F i x := fun ℓ => by
  simp only [map_sum]; exact ContDiff.sum fun i hi => hF i hi ℓ

theorem SSmooth.map {F : Y → Gr O} (hF : SSmooth F) (L : Gr O →ₗ[ℝ] Gr O) :
    SSmooth fun x => L (F x) := fun ℓ => hF (ℓ ∘ₗ L)

theorem SSmooth.mul {F G : Y → Gr O} (hF : SSmooth F) (hG : SSmooth G) :
    SSmooth fun x => F x * G x := fun ℓ => by
  have e : (fun x => ℓ (F x * G x)) =
      fun x => ∑ m, crd m (F x) * (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb (Gr O) m)) (G x) := by
    funext x; rw [dual_mul_eq_sum]; rfl
  rw [e]
  exact ContDiff.sum fun m _ => (hF (crd m)).mul (hG _)

theorem SSmooth.pow {F : Y → Gr O} (hF : SSmooth F) (k : ℕ) : SSmooth fun x => F x ^ k := by
  induction k with
  | zero => simpa using SSmooth.const (Y := Y) (1 : Gr O)
  | succ k ih => simpa [pow_succ] using ih.mul hF

theorem SSmooth.list_prod {ι : Type*} (l : List ι) {F : ι → Y → Gr O}
    (hF : ∀ i ∈ l, SSmooth (F i)) : SSmooth fun x => (l.map fun i => F i x).prod := by
  induction l with
  | nil => simpa using SSmooth.const (Y := Y) (1 : Gr O)
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF i List.mem_cons_self).mul (ih fun j hj => hF j (List.mem_cons_of_mem _ hj))

theorem contDiff_fderiv_apply {f : Y → ℝ} (hf : ContDiff ℝ ∞ f) (v : Y) :
    ContDiff ℝ ∞ fun x => fderiv ℝ f x v :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem SSmooth.deriv {F : Y → Gr O} (hF : SSmooth F) (v : Y) : SSmooth (pd v F) := fun ℓ => by
  have e : (fun x => ℓ (pd v F x)) = fun x => fderiv ℝ (fun y => ℓ (F y)) x v :=
    funext fun x => dual_pd hF.sdiff ℓ v x
  rw [e]; exact contDiff_fderiv_apply (hF ℓ) v

theorem SSmooth.contDiff_body {F : Y → Gr O} (hF : SSmooth F) : ContDiff ℝ ∞ fun x => body (F x) :=
  hF (body : Gr O →ₐ[ℝ] ℝ).toLinearMap

theorem SSmooth.soulF {F : Y → Gr O} (hF : SSmooth F) : SSmooth (soulF F) :=
  hF.sub (SSmooth.smul_const hF.contDiff_body 1)

/-- Composition with a function smooth on an open set containing the bodies. -/
theorem SSmooth.scomp {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {S : Y → Gr O} (hS : SSmooth S) (hE : ∀ p, IsEven (S p)) (hb : ∀ p, body (S p) ∈ U) :
    SSmooth fun p => scomp g (S p) := by
  rw [scomp_fun_eq hE le_rfl]
  refine SSmooth.sum _ fun k _ => SSmooth.smul ?_ (hS.soulF.pow k)
  have h1 := (contDiffOn_iteratedDeriv hU hg k).comp_contDiff hS.contDiff_body hb
  exact h1.div_const _

theorem SSmooth.sinv {S : Y → Gr O} (hS : SSmooth S) (hE : ∀ p, IsEven (S p))
    (hb : ∀ p, 0 < body (S p)) : SSmooth fun p => Ring.inverse (S p) := by
  have e : (fun p => Ring.inverse (S p)) = fun p => Super.scomp (fun t : ℝ => t⁻¹) (S p) :=
    funext fun p => inverse_eq_scomp_inv (isNilpotent_soul (hE p)) (hb p).ne'
  rw [e]
  exact hS.scomp isOpen_Ioi H24.contDiffOn_inv hE hb

end

end ArborealDecay.BCHS

end
