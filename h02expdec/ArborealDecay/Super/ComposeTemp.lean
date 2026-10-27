module

public import ArborealDecay.Super.ComposeDiff

/-!
# Tempered superfunctions and decay of composed integrands

* `STemp F`: every coordinate `ℓ ∘ F` of `F : (E → ℝ) → A` is a `Temp` multiplier (`C¹`, with
  itself and its first partial derivatives polynomially bounded).  `STemp` is closed under sums,
  products, multiplication by `Temp` scalars and composition with smooth `g` whose derivatives
  are polynomially bounded on the range of the body (`STemp.scomp`).
* `SDecay.of_decay_smul`: `f • F` is in `SDecay` if `f` is in `Decay` and `F` is in `STemp`.
* `decay_exp_neg`: `e^{-Φ}` is in `Decay` if `Φ ≥ 0` is `Temp` and `1 + ‖p‖ ≤ C (1 + Φ p)^M`.
* `temp_iteratedDeriv_comp`: `p ↦ φ^{(k)}(s p)` is `Temp` if `s` is `Temp` with values in a set
  `V` on which every derivative of `φ` is polynomially bounded.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory Finset
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {E : Type*} [Fintype E]

local notation "X" => E → ℝ

/-! ### Scalar lemmas -/

theorem Temp.neg {g : X → ℝ} (hg : Temp g) : Temp fun x => -g x := by
  simpa using hg.const_mul (-1)

theorem Temp.sub {f g : X → ℝ} (hf : Temp f) (hg : Temp g) : Temp fun x => f x - g x := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem Temp.mul_const {g : X → ℝ} (hg : Temp g) (c : ℝ) : Temp fun x => g x * c := by
  simpa [mul_comm] using hg.const_mul c

theorem Temp.div_const {g : X → ℝ} (hg : Temp g) (c : ℝ) : Temp fun x => g x / c := by
  simpa [div_eq_mul_inv] using hg.mul_const c⁻¹

theorem Temp.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ} (hf : ∀ i ∈ s, Temp (f i)) :
    Temp fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Temp.const (E := E) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem Temp.pow {g : X → ℝ} (hg : Temp g) (k : ℕ) : Temp fun x => g x ^ k := by
  induction k with
  | zero => simpa using Temp.const (E := E) 1
  | succ k ih => simpa [pow_succ] using ih.mul hg

theorem PolyBd.comp {s : X → ℝ} (hs : PolyBd s) {f : ℝ → ℝ} {V : Set ℝ} (hsV : ∀ x, s x ∈ V)
    (hf : ∃ C : ℝ, ∃ m : ℕ, ∀ t ∈ V, |f t| ≤ C * (1 + |t|) ^ m) : PolyBd fun x => f (s x) := by
  obtain ⟨C, k, hC⟩ := hs
  obtain ⟨D, m, hD⟩ := hf
  refine ⟨|D| * (1 + |C|) ^ m, k * m, fun x => ?_⟩
  have h1 : (1 : ℝ) ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg x])
  have h2 : 1 + |s x| ≤ (1 + |C|) * (1 + ‖x‖) ^ k := by
    have := hC x
    have hc : C * (1 + ‖x‖) ^ k ≤ |C| * (1 + ‖x‖) ^ k :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    nlinarith [abs_nonneg C]
  calc |f (s x)| ≤ D * (1 + |s x|) ^ m := hD _ (hsV x)
    _ ≤ |D| * ((1 + |C|) * (1 + ‖x‖) ^ k) ^ m := by
        gcongr
        · exact le_abs_self D
    _ = |D| * (1 + |C|) ^ m * (1 + ‖x‖) ^ (k * m) := by rw [mul_pow, ← pow_mul]; ring

/-- `p ↦ φ^{(k)}(s p)` is a `Temp` multiplier. -/
theorem temp_iteratedDeriv_comp {φ : ℝ → ℝ} {U V : Set ℝ} (hU : IsOpen U) (hVU : V ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U)
    (hbd : ∀ k, ∃ C : ℝ, ∃ m : ℕ, ∀ t ∈ V, |iteratedDeriv k φ t| ≤ C * (1 + |t|) ^ m)
    {s : X → ℝ} (hs : Temp s) (hsV : ∀ x, s x ∈ V) (k : ℕ) :
    Temp fun x => iteratedDeriv k φ (s x) := by
  refine ⟨?_, hs.2.1.comp hsV (hbd k), fun v => ?_⟩
  · exact ((contDiffOn_iteratedDeriv hU hφ k).of_le (by exact_mod_cast le_top)).comp_contDiff
      hs.1 (fun x => hVU (hsV x))
  · have e : (fun x => fderiv ℝ (fun y => iteratedDeriv k φ (s y)) x v) =
        fun x => iteratedDeriv (k + 1) φ (s x) * fderiv ℝ s x v := by
      funext x
      have h := (hasDerivAt_iteratedDeriv hU hφ k (hVU (hsV x))).comp_hasFDerivAt x
        (hs.differentiable x).hasFDerivAt
      rw [show (fun y => iteratedDeriv k φ (s y)) = iteratedDeriv k φ ∘ s from rfl, h.fderiv]
      simp
    rw [e]
    exact (hs.2.1.comp hsV (hbd (k + 1))).mul (hs.2.2 v)

/-- `e^{-Φ}` decays rapidly if `Φ ≥ 0` is tempered and `1 + ‖x‖` is dominated by a power of
`1 + Φ x`. -/
theorem decay_exp_neg {Φ : X → ℝ} (hΦ : Temp Φ) (h0 : ∀ x, 0 ≤ Φ x) {C : ℝ} {M : ℕ}
    (hdom : ∀ x, 1 + ‖x‖ ≤ C * (1 + Φ x) ^ M) : Decay fun x => Real.exp (-Φ x) := by
  have hcont : Continuous fun x => Real.exp (-Φ x) := (hΦ.continuous.neg).rexp
  have hC : 0 ≤ C := by
    have h := hdom 0
    have : 0 < (1 + Φ 0) ^ M := pow_pos (by linarith [h0 0]) M
    by_contra hneg
    have hneg' : C < 0 := not_le.mp hneg
    nlinarith [norm_nonneg (0 : X)]
  have hR : RDec fun x => Real.exp (-Φ x) := by
    refine ⟨hcont, fun k => ⟨C ^ k * ((M * k).factorial * Real.exp 1), fun x => ?_⟩⟩
    have hΦx := h0 x
    have hf : (0 : ℝ) < (M * k).factorial := by exact_mod_cast Nat.factorial_pos _
    have h1 : (1 + Φ x) ^ (M * k) / (M * k).factorial ≤ Real.exp (1 + Φ x) :=
      Real.pow_div_factorial_le_exp _ (by linarith) _
    rw [div_le_iff₀ hf] at h1
    have h2 : (1 + ‖x‖) ^ k ≤ C ^ k * (1 + Φ x) ^ (M * k) := by
      calc (1 + ‖x‖) ^ k ≤ (C * (1 + Φ x) ^ M) ^ k :=
            pow_le_pow_left₀ (by positivity) (hdom x) k
        _ = C ^ k * (1 + Φ x) ^ (M * k) := by rw [mul_pow, ← pow_mul]
    rw [abs_of_pos (Real.exp_pos _)]
    calc (1 + ‖x‖) ^ k * Real.exp (-Φ x)
        ≤ (C ^ k * (1 + Φ x) ^ (M * k)) * Real.exp (-Φ x) := by gcongr
      _ ≤ (C ^ k * (Real.exp (1 + Φ x) * (M * k).factorial)) * Real.exp (-Φ x) := by
          gcongr
      _ = C ^ k * ((M * k).factorial * Real.exp 1) := by
          rw [show Real.exp (1 + Φ x) = Real.exp 1 * Real.exp (Φ x) from Real.exp_add _ _]
          have := Real.exp_neg (Φ x)
          field_simp
          rw [this]; field_simp
  refine ⟨Real.contDiff_exp.comp hΦ.1.neg, hR, fun v => ?_⟩
  have e : (fun x => fderiv ℝ (fun y => Real.exp (-Φ y)) x v) =
      fun x => -fderiv ℝ Φ x v * Real.exp (-Φ x) := by
    funext x
    have h : HasFDerivAt (fun y => Real.exp (-Φ y)) _ x :=
      ((hΦ.differentiable x).hasFDerivAt.neg).exp
    rw [h.fderiv]
    simp [mul_comm]
  rw [e]
  exact hR.mul (hΦ.continuous_fderiv v).neg (hΦ.2.2 v).neg

/-! ### Tempered superfunctions -/

section STemp

variable {A : Type*} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]

/-- Every coordinate of `F` is a `Temp` multiplier. -/
def STemp (F : X → A) : Prop := ∀ ℓ : Module.Dual ℝ A, Temp fun x => ℓ (F x)

theorem STemp.const (c : A) : STemp fun _ : X => c := fun _ => Temp.const _

theorem STemp.add {F G : X → A} (hF : STemp F) (hG : STemp G) : STemp fun x => F x + G x :=
  fun ℓ => by simpa using (hF ℓ).add (hG ℓ)

theorem STemp.neg {F : X → A} (hF : STemp F) : STemp fun x => -F x :=
  fun ℓ => by simpa using (hF ℓ).neg

theorem STemp.sub {F G : X → A} (hF : STemp F) (hG : STemp G) : STemp fun x => F x - G x :=
  fun ℓ => by simpa using (hF ℓ).sub (hG ℓ)

theorem STemp.smul {F : X → A} (hF : STemp F) {g : X → ℝ} (hg : Temp g) :
    STemp fun x => g x • F x := fun ℓ => by simpa using hg.mul (hF ℓ)

theorem STemp.const_smul {F : X → A} (hF : STemp F) (c : ℝ) : STemp fun x => c • F x :=
  hF.smul (Temp.const c)

theorem STemp.sum {ι : Type*} (s : Finset ι) {F : ι → X → A} (hF : ∀ i ∈ s, STemp (F i)) :
    STemp fun x => ∑ i ∈ s, F i x := fun ℓ => by
  simpa using Temp.sum s fun i hi => hF i hi ℓ

theorem STemp.map {B : Type*} [AddCommGroup B] [Module ℝ B] [FiniteDimensional ℝ B] {F : X → A}
    (hF : STemp F) (L : A →ₗ[ℝ] B) : STemp fun x => L (F x) := fun ℓ => hF (ℓ ∘ₗ L)

/-- `f • F` decays if `f` decays and `F` is tempered. -/
theorem SDecay.of_decay_smul {f : X → ℝ} (hf : Decay f) {F : X → A} (hF : STemp F) :
    SDecay fun x => f x • F x := fun ℓ => by
  simpa [mul_comm] using hf.mul_temp (hF ℓ)

end STemp

section STempAlg

variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

theorem STemp.mul {F G : X → A} (hF : STemp F) (hG : STemp G) : STemp fun x => F x * G x :=
  fun ℓ => by
    have e : (fun x => ℓ (F x * G x)) =
        fun x => ∑ m, crd m (F x) * (ℓ ∘ₗ LinearMap.mulLeft ℝ (fb A m)) (G x) := by
      funext x; rw [dual_mul_eq_sum]; rfl
    rw [e]
    exact Temp.sum _ fun m _ => (hF (crd m)).mul (hG _)

theorem STemp.pow {F : X → A} (hF : STemp F) (k : ℕ) : STemp fun x => F x ^ k := by
  induction k with
  | zero => simpa using STemp.const (E := E) (1 : A)
  | succ k ih => simpa [pow_succ] using ih.mul hF

theorem STemp.list_prod {ι : Type*} (l : List ι) {F : ι → X → A} (hF : ∀ i ∈ l, STemp (F i)) :
    STemp fun x => (l.map fun i => F i x).prod := by
  induction l with
  | nil => simpa using STemp.const (E := E) (1 : A)
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF i List.mem_cons_self).mul (ih fun j hj => hF j (List.mem_cons_of_mem _ hj))

end STempAlg

/-! ### Composition -/

section Comp

variable {O : Type*} [Fintype O] [DecidableEq O]

theorem STemp.temp_body {S : X → Gr O} (hS : STemp S) : Temp fun x => body (S x) :=
  hS body.toLinearMap

theorem STemp.stemp_soulF {S : X → Gr O} (hS : STemp S) : STemp (soulF S) :=
  hS.sub ((STemp.const 1).smul hS.temp_body)

/-- Composition preserves `STemp`, given `Temp` bounds on the Taylor coefficients. -/
theorem STemp.scomp {g : ℝ → ℝ} {S : X → Gr O} (hS : STemp S) (hE : ∀ x, IsEven (S x))
    (hg : ∀ k, Temp fun x => iteratedDeriv k g (body (S x))) :
    STemp fun x => Super.scomp g (S x) := by
  rw [scomp_fun_eq hE le_rfl]
  exact STemp.sum _ fun k _ => (hS.stemp_soulF.pow k).smul ((hg k).div_const _)

/-- `exp(a) = e^{body a} · exp(soul a)`. -/
theorem scomp_exp_eq_smul {a : Gr O} (ha : IsEven a) :
    Super.scomp Real.exp a = Real.exp (Super.body a) • Super.scomp Real.exp (soul a) := by
  rw [scomp_exp (isNilpotent_soul ha), scomp_exp_of_body_eq_zero ?_ (body_soul a)]
  rw [← soul_of_body_eq_zero (body_soul a)]
  exact isNilpotent_soul ha.soul

/-- `p ↦ exp(soul (S p))` is tempered when `S` is. -/
theorem STemp.scomp_exp_soul {S : X → Gr O} (hS : STemp S) (hE : ∀ x, IsEven (S x)) :
    STemp fun x => Super.scomp Real.exp (soul (S x)) := by
  have e : (fun x => soul (S x)) = soulF S := funext fun x => (soulF_eq S x).symm
  rw [show (fun x => Super.scomp Real.exp (soul (S x))) =
    fun x => Super.scomp Real.exp (soulF S x) from by rw [← e]]
  refine hS.stemp_soulF.scomp (fun x => by rw [soulF_eq]; exact (hE x).soul) fun k => ?_
  simp only [soulF_eq, body_soul, iteratedDeriv_exp, Real.exp_zero]
  exact Temp.const 1

end Comp

end

end ArborealDecay.Super

end
