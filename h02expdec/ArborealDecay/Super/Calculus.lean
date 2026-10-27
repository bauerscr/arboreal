module

public import Mathlib

/-!
# Calculus for functions with values in a finite-dimensional real vector space

Let `A` be a finite-dimensional real vector space (in applications, a Grassmann algebra).  We do
not put a topology on `A`; instead a function `F : X → A` is treated through the scalar functions
`x ↦ ℓ (F x)`, `ℓ : Module.Dual ℝ A`.  We fix the basis `fb A := Module.finBasis ℝ A` with
coordinate functionals `crd m`.

* `SDiff F`: every `ℓ ∘ F` is differentiable.
* `pd v F x`: the partial derivative of `F` at `x` in direction `v`, defined coordinatewise;
  `dual_pd` says `ℓ (pd v F x) = fderiv ℝ (ℓ ∘ F) x v` for differentiable `F`.
* `pd_mul`: the product rule when `A` is an `ℝ`-algebra.
* `sint F`: the integral of `F`, defined coordinatewise; `dual_sint` says
  `ℓ (sint F) = ∫ ℓ (F x)` when every `ℓ ∘ F` is integrable.
* Decay classes on `E → ℝ` (`E` a finite type, sup norm, Lebesgue measure):
  `RDec f` (continuous, `(1 + ‖x‖)^k |f x|` bounded for every `k`),
  `Decay f` (`C¹`, with `f` and all its partial derivatives in `RDec`),
  `Temp g` (`C¹` multipliers with `g` and its partial derivatives polynomially bounded), and
  `SDecay F` (every `ℓ ∘ F` is in `Decay`).
* `Decay.integral_fderiv_eq_zero`: `∫ ∂_v f = 0` for `f` in `Decay`.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory

set_option linter.unusedSectionVars false

/-! ### Coordinates -/

section Coord

variable (A : Type*) [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]

/-- The fixed basis of `A`. -/
abbrev fb : Module.Basis (Fin (Module.finrank ℝ A)) ℝ A := Module.finBasis ℝ A

variable {A}

/-- The coordinate functionals of the fixed basis. -/
def crd (m : Fin (Module.finrank ℝ A)) : Module.Dual ℝ A := (fb A).coord m

theorem sum_crd_smul (x : A) : ∑ m, crd m x • fb A m = x := (fb A).sum_repr x

theorem dual_eq_sum (ℓ : Module.Dual ℝ A) (x : A) : ℓ x = ∑ m, crd m x * ℓ (fb A m) := by
  conv_lhs => rw [← sum_crd_smul x]
  simp [map_sum, smul_eq_mul]

theorem ext_crd {x y : A} (h : ∀ m, crd m x = crd m y) : x = y := (fb A).ext_elem h

theorem ext_dual {x y : A} (h : ∀ ℓ : Module.Dual ℝ A, ℓ x = ℓ y) : x = y :=
  ext_crd fun _ => h _

/-- An `ℓ¹`-type size of an element of `A`. -/
def anorm (x : A) : ℝ := ∑ m, |crd m x|

theorem anorm_nonneg (x : A) : 0 ≤ anorm x := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_crd_le_anorm (x : A) (m) : |crd m x| ≤ anorm x :=
  Finset.single_le_sum (f := fun m => |crd m x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m)

theorem abs_dual_le (ℓ : Module.Dual ℝ A) (x : A) :
    |ℓ x| ≤ (∑ m, |ℓ (fb A m)|) * anorm x := by
  rw [dual_eq_sum ℓ x, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_crd_le_anorm x m) (abs_nonneg _)

theorem abs_bilin_le (Φ : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) (x y : A) :
    |Φ x y| ≤ (∑ m, ∑ n, |Φ (fb A m) (fb A n)|) * anorm x * anorm y := by
  have e : Φ x y = ∑ m, crd m x * ∑ n, crd n y * Φ (fb A m) (fb A n) := by
    conv_lhs => rw [← sum_crd_smul x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [dual_eq_sum (Φ (fb A m)) y]
  rw [e, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [abs_mul]
  refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [abs_mul]
  have h1 := abs_crd_le_anorm x m
  have h2 := abs_crd_le_anorm y n
  have h3 := anorm_nonneg x
  calc |crd m x| * (|crd n y| * |Φ (fb A m) (fb A n)|)
      ≤ anorm x * (anorm y * |Φ (fb A m) (fb A n)|) := by gcongr
    _ = |Φ (fb A m) (fb A n)| * anorm x * anorm y := by ring

theorem continuous_anorm_comp {T : Type*} [TopologicalSpace T] {f : T → A}
    (hf : ∀ m, Continuous fun t => crd m (f t)) : Continuous fun t => anorm (f t) :=
  continuous_finsetSum _ fun m _ => (hf m).abs

end Coord

/-! ### Differentiation -/

section Deriv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {A : Type*} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
variable {B : Type*} [AddCommGroup B] [Module ℝ B] [FiniteDimensional ℝ B]

/-- `F` is differentiable: every `ℓ ∘ F` is differentiable. -/
def SDiff (F : X → A) : Prop := ∀ ℓ : Module.Dual ℝ A, Differentiable ℝ (fun x => ℓ (F x))

/-- The partial derivative of `F` at `x` in direction `v`. -/
def pd (v : X) (F : X → A) (x : X) : A :=
  ∑ m, fderiv ℝ (fun y => crd m (F y)) x v • fb A m

theorem hasFDerivAt_dual {F : X → A} (hF : SDiff F) (ℓ : Module.Dual ℝ A) (x : X) :
    HasFDerivAt (fun y => ℓ (F y))
      (∑ m, ℓ (fb A m) • fderiv ℝ (fun y => crd m (F y)) x) x := by
  have e : (fun y => ℓ (F y)) = fun y => ∑ m, ℓ (fb A m) * crd m (F y) := by
    funext y; rw [dual_eq_sum ℓ (F y)]; simp [mul_comm]
  rw [e]
  exact HasFDerivAt.fun_sum fun m _ => ((hF (crd m) x).hasFDerivAt).const_mul _

theorem dual_pd {F : X → A} (hF : SDiff F) (ℓ : Module.Dual ℝ A) (v x : X) :
    ℓ (pd v F x) = fderiv ℝ (fun y => ℓ (F y)) x v := by
  rw [(hasFDerivAt_dual hF ℓ x).fderiv, pd, map_sum]
  simp [smul_eq_mul, mul_comm]

theorem SDiff.map {F : X → A} (hF : SDiff F) (L : A →ₗ[ℝ] B) : SDiff fun x => L (F x) :=
  fun ℓ => hF (ℓ ∘ₗ L)

theorem pd_map {F : X → A} (hF : SDiff F) (L : A →ₗ[ℝ] B) (v x : X) :
    pd v (fun y => L (F y)) x = L (pd v F x) := by
  refine ext_dual fun ℓ => ?_
  rw [dual_pd (hF.map L), ← LinearMap.comp_apply ℓ L, dual_pd hF]; rfl

theorem SDiff.const (c : A) : SDiff fun _ : X => c := fun _ => differentiable_const _

@[simp] theorem pd_const (c : A) (v x : X) : pd v (fun _ => c) x = 0 := by
  simp [pd]

theorem SDiff.add {F G : X → A} (hF : SDiff F) (hG : SDiff G) : SDiff fun x => F x + G x :=
  fun ℓ => by simp only [map_add]; exact (hF ℓ).fun_add (hG ℓ)

theorem SDiff.neg {F : X → A} (hF : SDiff F) : SDiff fun x => -F x :=
  fun ℓ => by simp only [map_neg]; exact (hF ℓ).fun_neg

theorem SDiff.sub {F G : X → A} (hF : SDiff F) (hG : SDiff G) : SDiff fun x => F x - G x :=
  fun ℓ => by simp only [map_sub]; exact (hF ℓ).fun_sub (hG ℓ)

theorem SDiff.sum {ι : Type*} (s : Finset ι) {F : ι → X → A} (hF : ∀ i ∈ s, SDiff (F i)) :
    SDiff fun x => ∑ i ∈ s, F i x := fun ℓ => by
  simp only [map_sum]; exact Differentiable.fun_sum (fun i hi => hF i hi ℓ)

theorem SDiff.smul {g : X → ℝ} {F : X → A} (hg : Differentiable ℝ g) (hF : SDiff F) :
    SDiff fun x => g x • F x := fun ℓ => by
  simp only [map_smul, smul_eq_mul]; exact hg.fun_mul (hF ℓ)

theorem pd_add {F G : X → A} (hF : SDiff F) (hG : SDiff G) (v x : X) :
    pd v (fun y => F y + G y) x = pd v F x + pd v G x := by
  refine ext_dual fun ℓ => ?_
  rw [dual_pd (hF.add hG), map_add, dual_pd hF, dual_pd hG]
  simp only [map_add]
  rw [fderiv_fun_add ((hF ℓ) x) ((hG ℓ) x)]; rfl

theorem pd_neg {F : X → A} (hF : SDiff F) (v x : X) :
    pd v (fun y => -F y) x = -pd v F x := by
  refine ext_dual fun ℓ => ?_
  rw [dual_pd hF.neg, map_neg, dual_pd hF]
  simp only [map_neg]
  rw [fderiv_fun_neg]; rfl

theorem pd_sub {F G : X → A} (hF : SDiff F) (hG : SDiff G) (v x : X) :
    pd v (fun y => F y - G y) x = pd v F x - pd v G x := by
  simp only [sub_eq_add_neg]
  rw [pd_add hF hG.neg, pd_neg hG]

theorem pd_sum {ι : Type*} (s : Finset ι) {F : ι → X → A} (hF : ∀ i ∈ s, SDiff (F i))
    (v x : X) : pd v (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, pd v (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [pd_add (hF a (Finset.mem_insert_self a s))
      (SDiff.sum s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem pd_smul {g : X → ℝ} {F : X → A} (hg : Differentiable ℝ g) (hF : SDiff F) (v x : X) :
    pd v (fun y => g y • F y) x = fderiv ℝ g x v • F x + g x • pd v F x := by
  refine ext_dual fun ℓ => ?_
  rw [dual_pd (hF.smul hg), map_add, map_smul, map_smul, dual_pd hF]
  simp only [map_smul, smul_eq_mul]
  rw [fderiv_fun_mul (hg x) (hF ℓ x)]
  simp [smul_eq_mul]; ring

theorem pd_smul_const {g : X → ℝ} (hg : Differentiable ℝ g) (c : A) (v x : X) :
    pd v (fun y => g y • c) x = fderiv ℝ g x v • c := by
  rw [pd_smul hg (SDiff.const c)]; simp

end Deriv

section Product

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

theorem dual_mul_eq_sum (ℓ : Module.Dual ℝ A) (a b : A) :
    ℓ (a * b) = ∑ m, crd m a * ℓ (fb A m * b) := by
  conv_lhs => rw [← sum_crd_smul a]
  simp [Finset.sum_mul, map_sum, smul_eq_mul]

theorem SDiff.mul {F G : X → A} (hF : SDiff F) (hG : SDiff G) : SDiff fun x => F x * G x :=
  fun ℓ => by
    have e : (fun x => ℓ (F x * G x)) =
        fun x => ∑ m, crd m (F x) * (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G x) := by
      funext x; rw [dual_mul_eq_sum]; rfl
    rw [e]
    exact Differentiable.fun_sum fun m _ => (hF (crd m)).mul (hG _)

/-- The product rule. -/
theorem pd_mul {F G : X → A} (hF : SDiff F) (hG : SDiff G) (v x : X) :
    pd v (fun y => F y * G y) x = pd v F x * G x + F x * pd v G x := by
  refine ext_dual fun ℓ => ?_
  rw [dual_pd (hF.mul hG)]
  have e : (fun x => ℓ (F x * G x)) =
      fun x => ∑ m, crd m (F x) * (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G x) := by
    funext x; rw [dual_mul_eq_sum]; rfl
  have hd : HasFDerivAt (fun x => ∑ m, crd m (F x) * (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G x))
      (∑ m, (crd m (F x) • fderiv ℝ (fun y => (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G y)) x +
        (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G x) • fderiv ℝ (fun y => crd m (F y)) x)) x :=
    HasFDerivAt.fun_sum fun m _ => ((hF (crd m) x).hasFDerivAt).mul ((hG _ x).hasFDerivAt)
  rw [e, hd.fderiv]
  rw [map_add, dual_mul_eq_sum ℓ (pd v F x), dual_mul_eq_sum ℓ (F x), ← Finset.sum_add_distrib]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 := dual_pd hF (crd m) v x
  have h2 := dual_pd hG (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) v x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply] at h2
  simp only [add_apply, smul_apply, smul_eq_mul,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
  rw [h1, ← h2]; ring

end Product

/-! ### Integration -/

section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {A : Type*} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]

/-- `F` is integrable: every `ℓ ∘ F` is integrable. -/
def SInt (F : X → A) (μ : Measure X) : Prop :=
  ∀ ℓ : Module.Dual ℝ A, Integrable (fun x => ℓ (F x)) μ

/-- The integral of an `A`-valued function, computed coordinatewise. -/
def sint (F : X → A) (μ : Measure X) : A := ∑ m, (∫ x, crd m (F x) ∂μ) • fb A m

theorem dual_sint {F : X → A} (hF : SInt F μ) (ℓ : Module.Dual ℝ A) :
    ℓ (sint F μ) = ∫ x, ℓ (F x) ∂μ := by
  simp only [sint, map_sum, map_smul, smul_eq_mul]
  have e : (fun x => ℓ (F x)) = fun x => ∑ m, crd m (F x) * ℓ (fb A m) := by
    funext x; exact dual_eq_sum ℓ (F x)
  rw [e, integral_finsetSum _ fun m _ => (hF (crd m)).mul_const _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const]

end Integral

/-! ### Decay classes on `E → ℝ` -/

section Decay

variable {E : Type*} [Fintype E]

local notation "X" => E → ℝ

/-- Polynomially bounded scalar functions. -/
def PolyBd (g : X → ℝ) : Prop := ∃ C : ℝ, ∃ k : ℕ, ∀ x, |g x| ≤ C * (1 + ‖x‖) ^ k

/-- Rapidly decreasing continuous scalar functions. -/
def RDec (f : X → ℝ) : Prop :=
  Continuous f ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ k * |f x| ≤ C

/-- `C¹` functions which, together with all their partial derivatives, decrease rapidly. -/
def Decay (f : X → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ RDec f ∧ ∀ v : X, RDec fun x => fderiv ℝ f x v

/-- `C¹` multipliers which, together with all their partial derivatives, grow at most
polynomially. -/
def Temp (g : X → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ PolyBd g ∧ ∀ v : X, PolyBd fun x => fderiv ℝ g x v

theorem PolyBd.const (c : ℝ) : PolyBd fun _ : X => c := ⟨|c|, 0, fun x => by simp⟩

theorem PolyBd.mul {f g : X → ℝ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd fun x => f x * g x := by
  obtain ⟨C, k, hC⟩ := hf
  obtain ⟨D, l, hD⟩ := hg
  refine ⟨C * D, k + l, fun x => ?_⟩
  rw [abs_mul, pow_add]
  have h1 := hC x; have h2 := hD x
  have : 0 ≤ C * (1 + ‖x‖) ^ k := (abs_nonneg _).trans h1
  calc |f x| * |g x| ≤ (C * (1 + ‖x‖) ^ k) * (D * (1 + ‖x‖) ^ l) :=
        mul_le_mul h1 h2 (abs_nonneg _) this
    _ = C * D * ((1 + ‖x‖) ^ k * (1 + ‖x‖) ^ l) := by ring

theorem PolyBd.add {f g : X → ℝ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd fun x => f x + g x := by
  obtain ⟨C, k, hC⟩ := hf
  obtain ⟨D, l, hD⟩ := hg
  refine ⟨|C| + |D|, k + l, fun x => ?_⟩
  have hx : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have hk : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ (k + l) := pow_le_pow_right₀ hx (by omega)
  have hl : (1 + ‖x‖) ^ l ≤ (1 + ‖x‖) ^ (k + l) := pow_le_pow_right₀ hx (by omega)
  have p0 : 0 ≤ (1 + ‖x‖) ^ k := by positivity
  have p1 : 0 ≤ (1 + ‖x‖) ^ l := by positivity
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C * (1 + ‖x‖) ^ k + D * (1 + ‖x‖) ^ l := add_le_add (hC x) (hD x)
    _ ≤ |C| * (1 + ‖x‖) ^ (k + l) + |D| * (1 + ‖x‖) ^ (k + l) := by
        exact add_le_add
          ((mul_le_mul_of_nonneg_right (le_abs_self C) p0).trans
            (mul_le_mul_of_nonneg_left hk (abs_nonneg C)))
          ((mul_le_mul_of_nonneg_right (le_abs_self D) p1).trans
            (mul_le_mul_of_nonneg_left hl (abs_nonneg D)))
    _ = (|C| + |D|) * (1 + ‖x‖) ^ (k + l) := by ring

theorem PolyBd.neg {f : X → ℝ} (hf : PolyBd f) : PolyBd fun x => -f x := by
  obtain ⟨C, k, hC⟩ := hf; exact ⟨C, k, fun x => by simpa using hC x⟩

theorem PolyBd.of_le {f g : X → ℝ} (hg : PolyBd g) (h : ∀ x, |f x| ≤ |g x|) : PolyBd f := by
  obtain ⟨C, k, hC⟩ := hg; exact ⟨C, k, fun x => (h x).trans (hC x)⟩

theorem RDec.mul {f g : X → ℝ} (hf : RDec f) (hgc : Continuous g) (hg : PolyBd g) :
    RDec fun x => g x * f x := by
  refine ⟨hgc.mul hf.1, fun k => ?_⟩
  obtain ⟨C, l, hC⟩ := hg
  obtain ⟨D, hD⟩ := hf.2 (k + l)
  refine ⟨|C| * D, fun x => ?_⟩
  have h1 : |g x| ≤ |C| * (1 + ‖x‖) ^ l :=
    (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [abs_mul]
  calc (1 + ‖x‖) ^ k * (|g x| * |f x|)
      ≤ (1 + ‖x‖) ^ k * ((|C| * (1 + ‖x‖) ^ l) * |f x|) := by gcongr
    _ = |C| * ((1 + ‖x‖) ^ (k + l) * |f x|) := by rw [pow_add]; ring
    _ ≤ |C| * D := mul_le_mul_of_nonneg_left (hD x) (abs_nonneg C)

theorem RDec.add {f g : X → ℝ} (hf : RDec f) (hg : RDec g) : RDec fun x => f x + g x := by
  refine ⟨hf.1.add hg.1, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 k
  obtain ⟨D, hD⟩ := hg.2 k
  refine ⟨C + D, fun x => ?_⟩
  calc (1 + ‖x‖) ^ k * |f x + g x| ≤ (1 + ‖x‖) ^ k * (|f x| + |g x|) := by
        gcongr; exact abs_add_le _ _
    _ ≤ C + D := by rw [mul_add]; exact add_le_add (hC x) (hD x)

theorem RDec.const_mul {f : X → ℝ} (hf : RDec f) (c : ℝ) : RDec fun x => c * f x :=
  hf.mul continuous_const (PolyBd.const c)

theorem RDec.neg {f : X → ℝ} (hf : RDec f) : RDec fun x => -f x := by
  simpa using hf.const_mul (-1)

theorem RDec.abs {f : X → ℝ} (hf : RDec f) : RDec fun x => |f x| :=
  ⟨hf.1.abs, fun k => by simpa using hf.2 k⟩

theorem RDec.zero : RDec fun _ : X => (0 : ℝ) := ⟨continuous_const, fun _ => ⟨0, by simp⟩⟩

theorem RDec.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ} (hf : ∀ i ∈ s, RDec (f i)) :
    RDec fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RDec.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem RDec.bounded {f : X → ℝ} (hf : RDec f) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.2 0
  exact ⟨C, fun x => by simpa using hC x⟩

theorem RDec.integrable {f : X → ℝ} (hf : RDec f) : Integrable f := by
  have hm : AEStronglyMeasurable f volume := hf.1.aestronglyMeasurable
  obtain ⟨C₁, hC₁⟩ := hf.bounded
  obtain ⟨C₂, hC₂⟩ := hf.2 (0 + (volume : Measure X).integrablePower)
  have := integrable_of_le_of_pow_mul_le (μ := (volume : Measure X)) (f := f) (k := 0)
    (C₁ := C₁) (C₂ := C₂) (fun x => by simpa using hC₁ x) (fun x => ?_) hm
  · simpa using this.norm.congr (Filter.Eventually.of_forall fun x => rfl) |>.mono'
      hm (Filter.Eventually.of_forall fun x => by simp)
  · refine le_trans ?_ (hC₂ x)
    rw [Real.norm_eq_abs]
    gcongr
    linarith [norm_nonneg x]

theorem Temp.continuous {g : X → ℝ} (hg : Temp g) : Continuous g := hg.1.continuous

theorem Temp.differentiable {g : X → ℝ} (hg : Temp g) : Differentiable ℝ g :=
  hg.1.differentiable one_ne_zero

theorem Temp.continuous_fderiv {g : X → ℝ} (hg : Temp g) (v : X) :
    Continuous fun x => fderiv ℝ g x v :=
  (hg.1.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem Temp.const (c : ℝ) : Temp fun _ : X => c :=
  ⟨contDiff_const, PolyBd.const c, fun v => by simpa using PolyBd.const 0⟩

theorem Temp.mul {f g : X → ℝ} (hf : Temp f) (hg : Temp g) : Temp fun x => f x * g x := by
  refine ⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, fun v => ?_⟩
  have e : (fun x => fderiv ℝ (fun y => f y * g y) x v) =
      fun x => f x * fderiv ℝ g x v + g x * fderiv ℝ f x v := by
    funext x
    rw [fderiv_fun_mul (hf.differentiable x) (hg.differentiable x)]
    simp [smul_eq_mul]
  rw [e]
  exact (hf.2.1.mul (hg.2.2 v)).add (hg.2.1.mul (hf.2.2 v))

theorem Temp.add {f g : X → ℝ} (hf : Temp f) (hg : Temp g) : Temp fun x => f x + g x := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, fun v => ?_⟩
  have e : (fun x => fderiv ℝ (fun y => f y + g y) x v) =
      fun x => fderiv ℝ f x v + fderiv ℝ g x v := by
    funext x
    rw [fderiv_fun_add (hf.differentiable x) (hg.differentiable x)]; rfl
  rw [e]; exact (hf.2.2 v).add (hg.2.2 v)

theorem Temp.const_mul {g : X → ℝ} (hg : Temp g) (c : ℝ) : Temp fun x => c * g x :=
  (Temp.const c).mul hg

/-- A continuous linear functional is a `Temp` multiplier. -/
theorem Temp.clm (L : X →L[ℝ] ℝ) : Temp fun x => L x := by
  refine ⟨L.contDiff, ⟨‖L‖, 1, fun x => ?_⟩, fun v => ?_⟩
  · rw [← Real.norm_eq_abs, pow_one]
    refine (L.le_opNorm x).trans ?_
    gcongr; linarith
  · simp only [ContinuousLinearMap.fderiv]
    exact PolyBd.const _

/-- The coordinate `x ↦ x k`. -/
theorem Temp.coord [DecidableEq E] (k : E) : Temp fun x : X => x k :=
  Temp.clm (ContinuousLinearMap.proj k)

theorem Decay.differentiable {f : X → ℝ} (hf : Decay f) : Differentiable ℝ f :=
  hf.1.differentiable one_ne_zero

theorem Decay.continuous {f : X → ℝ} (hf : Decay f) : Continuous f := hf.2.1.1

theorem Decay.integrable {f : X → ℝ} (hf : Decay f) : Integrable f := hf.2.1.integrable

theorem Decay.integrable_fderiv {f : X → ℝ} (hf : Decay f) (v : X) :
    Integrable fun x => fderiv ℝ f x v := (hf.2.2 v).integrable

theorem Decay.mul_temp {f g : X → ℝ} (hf : Decay f) (hg : Temp g) : Decay fun x => g x * f x := by
  refine ⟨hg.1.mul hf.1, hf.2.1.mul hg.continuous hg.2.1, fun v => ?_⟩
  have e : (fun x => fderiv ℝ (fun y => g y * f y) x v) =
      fun x => g x * fderiv ℝ f x v + fderiv ℝ g x v * f x := by
    funext x
    rw [fderiv_fun_mul (hg.differentiable x) (hf.differentiable x)]
    simp [smul_eq_mul]; ring
  rw [e]
  exact ((hf.2.2 v).mul hg.continuous hg.2.1).add
    (hf.2.1.mul (hg.continuous_fderiv v) (hg.2.2 v))

theorem Decay.add {f g : X → ℝ} (hf : Decay f) (hg : Decay g) : Decay fun x => f x + g x := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, fun v => ?_⟩
  have e : (fun x => fderiv ℝ (fun y => f y + g y) x v) =
      fun x => fderiv ℝ f x v + fderiv ℝ g x v := by
    funext x
    rw [fderiv_fun_add (hf.differentiable x) (hg.differentiable x)]; rfl
  rw [e]; exact (hf.2.2 v).add (hg.2.2 v)

theorem Decay.const_mul {f : X → ℝ} (hf : Decay f) (c : ℝ) : Decay fun x => c * f x :=
  hf.mul_temp (Temp.const c)

theorem Decay.zero : Decay fun _ : X => (0 : ℝ) :=
  ⟨contDiff_const, RDec.zero, fun v => by simpa using RDec.zero⟩

theorem Decay.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ} (hf : ∀ i ∈ s, Decay (f i)) :
    Decay fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Decay.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The integral of a partial derivative of a function in `Decay` vanishes. -/
theorem Decay.integral_fderiv_eq_zero {f : X → ℝ} (hf : Decay f) (v : X) :
    ∫ x, fderiv ℝ f x v = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : X => (1 : ℝ)) (g := f) (v := v) (by simp)
    (by simpa using hf.integrable_fderiv v) (by simpa using hf.integrable)
    (fun x _ => differentiableAt_const _) (fun x _ => hf.differentiable x)
  simpa using h

end Decay

/-! ### Superfunctions with decay -/

section SDecay

variable {E : Type*} [Fintype E]
variable {A : Type*} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
variable {B : Type*} [AddCommGroup B] [Module ℝ B] [FiniteDimensional ℝ B]

local notation "X" => E → ℝ

/-- An `A`-valued function on `E → ℝ` all of whose coordinates are in `Decay`. -/
def SDecay (F : X → A) : Prop := ∀ ℓ : Module.Dual ℝ A, Decay fun x => ℓ (F x)

theorem SDecay.sdiff {F : X → A} (hF : SDecay F) : SDiff F := fun ℓ => (hF ℓ).differentiable

theorem SDecay.continuous {F : X → A} (hF : SDecay F) (ℓ : Module.Dual ℝ A) :
    Continuous fun x => ℓ (F x) := (hF ℓ).continuous

theorem SDecay.sint {F : X → A} (hF : SDecay F) : SInt F volume := fun ℓ => (hF ℓ).integrable

theorem SDecay.sint_pd {F : X → A} (hF : SDecay F) (v : X) : SInt (pd v F) volume := fun ℓ => by
  simp_rw [dual_pd hF.sdiff ℓ]
  exact (hF ℓ).integrable_fderiv v

theorem SDecay.map {F : X → A} (hF : SDecay F) (L : A →ₗ[ℝ] B) : SDecay fun x => L (F x) :=
  fun ℓ => hF (ℓ ∘ₗ L)

theorem SDecay.smul {F : X → A} (hF : SDecay F) {g : X → ℝ} (hg : Temp g) :
    SDecay fun x => g x • F x := fun ℓ => by simpa using (hF ℓ).mul_temp hg

theorem SDecay.add {F G : X → A} (hF : SDecay F) (hG : SDecay G) : SDecay fun x => F x + G x :=
  fun ℓ => by simpa using (hF ℓ).add (hG ℓ)

theorem SDecay.neg {F : X → A} (hF : SDecay F) : SDecay fun x => -F x :=
  fun ℓ => by simpa using (hF ℓ).const_mul (-1)

theorem SDecay.sub {F G : X → A} (hF : SDecay F) (hG : SDecay G) : SDecay fun x => F x - G x := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem SDecay.sum {ι : Type*} (s : Finset ι) {F : ι → X → A} (hF : ∀ i ∈ s, SDecay (F i)) :
    SDecay fun x => ∑ i ∈ s, F i x := fun ℓ => by
  simpa using Decay.sum s fun i hi => hF i hi ℓ

/-- The coordinates of a function in `SDecay` are bounded. -/
theorem SDecay.anorm_bounded {F : X → A} (hF : SDecay F) : ∃ C, ∀ x, anorm (F x) ≤ C := by
  choose C hC using fun m => (hF (crd m)).2.1.bounded
  exact ⟨∑ m, C m, fun x => Finset.sum_le_sum fun m _ => hC m x⟩

/-- `x ↦ anorm (F x)` is in `RDec`. -/
theorem SDecay.rdec_anorm {F : X → A} (hF : SDecay F) : RDec fun x => anorm (F x) := by
  unfold anorm
  exact RDec.sum _ fun m _ => (hF (crd m)).2.1.abs

/-! ### Schwartz functions -/

theorem rdec_of_schwartzMap {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : SchwartzMap X W) (g : W → ℝ) (hg : Continuous g) {c : ℝ} (hc : 0 ≤ c)
    (hgf : ∀ w, |g w| ≤ c * ‖w‖) : RDec fun x => g (f x) := by
  refine ⟨hg.comp f.continuous, fun k => ⟨c * (2 ^ k *
    (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f), fun x => ?_⟩⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero] at h
  calc (1 + ‖x‖) ^ k * |g (f x)| ≤ (1 + ‖x‖) ^ k * (c * ‖f x‖) :=
        mul_le_mul_of_nonneg_left (hgf _) (by positivity)
    _ = c * ((1 + ‖x‖) ^ k * ‖f x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc

/-- A Schwartz function is in `Decay`. -/
theorem decay_of_schwartzMap (f : SchwartzMap X ℝ) : Decay fun x => f x := by
  refine ⟨f.smooth 1, rdec_of_schwartzMap f id continuous_id zero_le_one
    fun w => by simp [Real.norm_eq_abs], fun v => ?_⟩
  have h := rdec_of_schwartzMap (SchwartzMap.fderivCLM ℝ X ℝ f) (fun L => L v)
    (continuous_id.clm_apply continuous_const) (norm_nonneg v) fun L => by
      rw [← Real.norm_eq_abs, mul_comm]
      exact L.le_opNorm v
  simpa [SchwartzMap.fderivCLM_apply] using h

/-- An `A`-valued function whose coordinates are Schwartz functions is in `SDecay`. -/
theorem SDecay.of_schwartz {F : X → A}
    (h : ∀ m, ∃ f : SchwartzMap X ℝ, ∀ x, crd m (F x) = f x) : SDecay F := fun ℓ => by
  choose f hf using h
  have e : (fun x => ℓ (F x)) = fun x => ∑ m, ℓ (fb A m) * f m x := by
    funext x; rw [dual_eq_sum]; simp [hf, mul_comm]
  rw [e]
  exact Decay.sum _ fun m _ => (decay_of_schwartzMap (f m)).const_mul _

end SDecay

end

end ArborealDecay.Super

end
