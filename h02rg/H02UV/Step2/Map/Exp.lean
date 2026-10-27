import Step2.Map.Ord
import Step.ExpNorm

/-!
# Second-order expansions at `t = 0`

`ExpE2 f F₀ F₁ F₂`: `f(t) = F₀ + t F₁ + t² F₂ + O(t³)` (with `O(t³)` in the sense of `OrdE 3`),
and `ExpS2 φ a₀ a₁ a₂` for scalars. These are closed under sums, products (Cauchy product of
the truncated series), scalar multiplication, fixed linear maps, `gexp` (for nilpotent `f`
with `F₀ = 0`: `e^f = 1 + t F₁ + t² (F₂ + F₁²/2) + O(t³)`) and `Complex.exp`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann

/-! ### Scalars -/

/-- `φ(t) = a₀ + t a₁ + t² a₂ + O(t³)`. -/
def ExpS2 (φ : ℂ → ℂ) (a₀ a₁ a₂ : ℂ) : Prop := OrdS 3 (fun t => φ t - (a₀ + t * a₁ + t ^ 2 * a₂))

theorem ExpS2.congr {φ ψ : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} (h : ExpS2 φ a₀ a₁ a₂) (e : ∀ t, ψ t = φ t) :
    ExpS2 ψ a₀ a₁ a₂ := OrdS.congr h fun t => by rw [e]

theorem ExpS2.const (a : ℂ) : ExpS2 (fun _ => a) a 0 0 :=
  (OrdS.zero 3).congr fun t => by ring

theorem ExpS2.lin (a : ℂ) : ExpS2 (fun t => t * a) 0 a 0 :=
  (OrdS.zero 3).congr fun t => by ring

theorem ExpS2.add {φ ψ : ℂ → ℂ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℂ} (h1 : ExpS2 φ a₀ a₁ a₂)
    (h2 : ExpS2 ψ b₀ b₁ b₂) : ExpS2 (fun t => φ t + ψ t) (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) :=
  OrdS.congr (OrdS.add h1 h2) fun t => by ring

theorem ExpS2.sum {ι : Type*} (s : Finset ι) {φ : ι → ℂ → ℂ} {a₀ a₁ a₂ : ι → ℂ}
    (h : ∀ i ∈ s, ExpS2 (φ i) (a₀ i) (a₁ i) (a₂ i)) :
    ExpS2 (fun t => ∑ i ∈ s, φ i t) (∑ i ∈ s, a₀ i) (∑ i ∈ s, a₁ i) (∑ i ∈ s, a₂ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (ExpS2.const 0).congr fun t => by simp
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- `e^{q} = 1 + t a₁ + t² (a₂ + a₁²/2) + O(t³)` for `q = t a₁ + t² a₂ + O(t³)`. -/
theorem ExpS2.exp {q : ℂ → ℂ} {a₁ a₂ : ℂ} (h : ExpS2 q 0 a₁ a₂) :
    ExpS2 (fun t => Complex.exp (q t)) 1 a₁ (a₂ + a₁ ^ 2 / 2) := by
  have hq : OrdS 1 q := by
    have e : OrdS 1 (fun t => q t - (0 + t * a₁ + t ^ 2 * a₂)) := OrdS.mono (by norm_num) h
    have e' : OrdS 1 (fun t => t * (a₁ + t * a₂)) :=
      ⟨fun t => a₁ + t * a₂, by fun_prop, fun t => by ring⟩
    exact (e.add e').congr fun t => by ring
  have hx := OrdS.exp_taylor hq
  -- `q - t a₁ = O(t²)`, `q + t a₁ = O(t)`
  have hm : OrdS 2 (fun t => q t - t * a₁) := by
    have e : OrdS 2 (fun t => q t - (0 + t * a₁ + t ^ 2 * a₂)) := OrdS.mono (by norm_num) h
    exact (e.add (OrdS.pow_mul (n := 2) (h := fun _ => a₂) (differentiable_const _))).congr
      fun t => by ring
  have hp : OrdS 1 (fun t => q t + t * a₁) :=
    hq.add ⟨fun _ => a₁, differentiable_const _, fun t => by ring⟩
  have hsq : OrdS 3 (fun t => (q t - t * a₁) * (q t + t * a₁)) := hm.mul hp
  have e2 : OrdS 3 (fun t => q t - (0 + t * a₁ + t ^ 2 * a₂)) := h
  have := (hx.add e2).add (hsq.congr (ψ := fun t => (q t ^ 2 - t ^ 2 * a₁ ^ 2) / 2 * 2)
    (fun t => by ring))
  refine OrdS.congr (φ := fun t => (Complex.exp (q t) - (1 + q t + q t ^ 2 / 2) +
    (q t - (0 + t * a₁ + t ^ 2 * a₂))) + (1 / 2) * ((q t - t * a₁) * (q t + t * a₁))) ?_ ?_
  · exact (hx.add e2).add (OrdS.mul (m := 0) (OrdS.of_differentiable (differentiable_const _))
      hsq |>.congr fun t => rfl)
  · intro t; ring

/-! ### Even elements -/

section Elements

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- `f(t) = F₀ + t F₁ + t² F₂ + O(t³)`. -/
def ExpE2 (f : ℂ → EvR I) (F₀ F₁ F₂ : EvR I) : Prop :=
  OrdE 3 (fun t => f t - (F₀ + t • F₁ + t ^ 2 • F₂))

theorem poly_hol (F₀ F₁ F₂ : EvR I) : HolE (fun t : ℂ => F₀ + t • F₁ + t ^ 2 • F₂) :=
  ((HolE.const _).add (HolE.smul differentiable_id (HolE.const _))).add
    (HolE.smul (differentiable_id.pow 2) (HolE.const _))

theorem ExpE2.hol {f : ℂ → EvR I} {F₀ F₁ F₂ : EvR I} (h : ExpE2 f F₀ F₁ F₂) : HolE f :=
  HolE.congr ((OrdE.hol h).add (poly_hol F₀ F₁ F₂)) fun t => by simp

theorem ExpE2.congr {f g : ℂ → EvR I} {F₀ F₁ F₂ : EvR I} (h : ExpE2 f F₀ F₁ F₂)
    (e : ∀ t, g t = f t) : ExpE2 g F₀ F₁ F₂ := OrdE.congr h fun t => by rw [e]

theorem ExpE2.coeffs {f : ℂ → EvR I} {F₀ F₁ F₂ G₀ G₁ G₂ : EvR I} (h : ExpE2 f F₀ F₁ F₂)
    (e₀ : G₀ = F₀) (e₁ : G₁ = F₁) (e₂ : G₂ = F₂) : ExpE2 f G₀ G₁ G₂ := by
  subst e₀ e₁ e₂; exact h

theorem ExpE2.of_ord3 {f : ℂ → EvR I} (h : OrdE 3 f) : ExpE2 f 0 0 0 :=
  OrdE.congr h fun t => by simp

theorem ExpE2.const (F : EvR I) : ExpE2 (fun _ => F) F 0 0 :=
  (OrdE.zero 3).congr fun t => by simp

theorem ExpE2.lin (F : EvR I) : ExpE2 (fun t => t • F) 0 F 0 :=
  (OrdE.zero 3).congr fun t => by simp

theorem ExpE2.quad (F : EvR I) : ExpE2 (fun t => t ^ 2 • F) 0 0 F :=
  (OrdE.zero 3).congr fun t => by simp

theorem ExpE2.add {f g : ℂ → EvR I} {F₀ F₁ F₂ G₀ G₁ G₂ : EvR I} (h1 : ExpE2 f F₀ F₁ F₂)
    (h2 : ExpE2 g G₀ G₁ G₂) : ExpE2 (fun t => f t + g t) (F₀ + G₀) (F₁ + G₁) (F₂ + G₂) :=
  OrdE.congr (OrdE.add h1 h2) fun t => by simp only [smul_add]; abel

theorem ExpE2.sub {f g : ℂ → EvR I} {F₀ F₁ F₂ G₀ G₁ G₂ : EvR I} (h1 : ExpE2 f F₀ F₁ F₂)
    (h2 : ExpE2 g G₀ G₁ G₂) : ExpE2 (fun t => f t - g t) (F₀ - G₀) (F₁ - G₁) (F₂ - G₂) :=
  OrdE.congr (OrdE.sub h1 h2) fun t => by simp only [smul_sub]; abel

theorem ExpE2.smul_const (c : ℂ) {f : ℂ → EvR I} {F₀ F₁ F₂ : EvR I} (h : ExpE2 f F₀ F₁ F₂) :
    ExpE2 (fun t => c • f t) (c • F₀) (c • F₁) (c • F₂) :=
  OrdE.congr (OrdE.smul_const c h) fun t => by
    simp only [smul_sub, smul_add, smul_comm c t, smul_comm c]

theorem ExpE2.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → EvR I} {F₀ F₁ F₂ : ι → EvR I}
    (h : ∀ i ∈ s, ExpE2 (f i) (F₀ i) (F₁ i) (F₂ i)) :
    ExpE2 (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, F₀ i) (∑ i ∈ s, F₁ i) (∑ i ∈ s, F₂ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (ExpE2.const 0).congr fun t => by simp
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem ExpE2.map {J : Type*} [DecidableEq J] [Fintype J] {f : ℂ → EvR I} {F₀ F₁ F₂ : EvR I}
    (h : ExpE2 f F₀ F₁ F₂) (T : EvR I →ₗ[ℂ] EvR J) :
    ExpE2 (fun t => T (f t)) (T F₀) (T F₁) (T F₂) :=
  OrdE.congr (OrdE.map h T) fun t => by simp only [map_sub, map_add, map_smul]

theorem ExpE2.mapA {J : Type*} [DecidableEq J] [Fintype J] {f : ℂ → EvR I} {F₀ F₁ F₂ : EvR I}
    (h : ExpE2 f F₀ F₁ F₂) (T : EvR I →ₐ[ℂ] EvR J) :
    ExpE2 (fun t => T (f t)) (T F₀) (T F₁) (T F₂) :=
  h.map T.toLinearMap

theorem smul_eq_alg (t : ℂ) (F : EvR I) : t • F = algebraMap ℂ (EvR I) t * F :=
  Algebra.smul_def t F

theorem ExpE2.mul {f g : ℂ → EvR I} {F₀ F₁ F₂ G₀ G₁ G₂ : EvR I} (h1 : ExpE2 f F₀ F₁ F₂)
    (h2 : ExpE2 g G₀ G₁ G₂) :
    ExpE2 (fun t => f t * g t) (F₀ * G₀) (F₀ * G₁ + F₁ * G₀) (F₀ * G₂ + F₁ * G₁ + F₂ * G₀) := by
  have hg := h2.hol
  have e1 : OrdE 3 (fun t => (f t - (F₀ + t • F₁ + t ^ 2 • F₂)) * g t) := by
    simpa using OrdE.mul h1 (OrdE.of_hol hg)
  have e2 : OrdE 3 (fun t => (F₀ + t • F₁ + t ^ 2 • F₂) * (g t - (G₀ + t • G₁ + t ^ 2 • G₂))) := by
    simpa using (OrdE.of_hol (poly_hol F₀ F₁ F₂)).mul (h2 : OrdE 3 _)
  have e3 : OrdE 3 (fun t => t ^ 3 • (F₁ * G₂ + F₂ * G₁ + t • (F₂ * G₂))) :=
    ⟨_, (HolE.const _).add (HolE.smul differentiable_id (HolE.const _)), fun _ => rfl⟩
  refine OrdE.congr ((e1.add e2).add e3) fun t => ?_
  simp only [smul_eq_alg, map_pow]
  ring

theorem ExpE2.ofS {φ : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} (h : ExpS2 φ a₀ a₁ a₂) :
    ExpE2 (fun t => algebraMap ℂ (EvR I) (φ t)) (algebraMap ℂ _ a₀) (algebraMap ℂ _ a₁)
      (algebraMap ℂ _ a₂) := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun t => g t • (1 : EvR I), HolE.smul hg (HolE.const _), fun t => ?_⟩
  have h1 : φ t = (a₀ + t * a₁ + t ^ 2 * a₂) + t ^ 3 * g t := by
    have := e t
    simp only at this
    linear_combination this
  beta_reduce
  rw [h1]
  simp only [smul_eq_alg, map_add, map_mul, map_pow, mul_one]
  ring

theorem ExpE2.smulS {φ : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} {f : ℂ → EvR I} {F₀ F₁ F₂ : EvR I}
    (hφ : ExpS2 φ a₀ a₁ a₂) (h : ExpE2 f F₀ F₁ F₂) :
    ExpE2 (fun t => φ t • f t) (a₀ • F₀) (a₀ • F₁ + a₁ • F₀) (a₀ • F₂ + a₁ • F₁ + a₂ • F₀) := by
  have := (ExpE2.ofS (I := I) hφ).mul h
  refine (this.congr fun t => by rw [smul_eq_alg]).coeffs ?_ ?_ ?_ <;> simp [smul_eq_alg]

theorem OrdE.pow {f : ℂ → EvR I} (h : OrdE 1 f) (k : ℕ) : OrdE k (fun t => f t ^ k) := by
  induction k with
  | zero => simpa using OrdE.of_hol (HolE.const (1 : EvR I))
  | succ k ih =>
    rw [add_comm]
    exact OrdE.congr (h.mul ih) fun t => by rw [add_comm, pow_succ']

theorem ExpE2.ord1 {f : ℂ → EvR I} {F₁ F₂ : EvR I} (h : ExpE2 f 0 F₁ F₂) : OrdE 1 f := by
  have e : OrdE 1 (fun t => f t - (0 + t • F₁ + t ^ 2 • F₂)) := OrdE.mono (by norm_num) h
  have e' : OrdE 1 (fun t => t • (F₁ + t • F₂)) :=
    ⟨fun t => F₁ + t • F₂, (HolE.const _).add (HolE.smul differentiable_id (HolE.const _)),
      fun t => by simp⟩
  exact (e.add e').congr fun t => by simp only [smul_add, smul_smul, ← pow_two]; abel

/-- `e^f = 1 + t F₁ + t² (F₂ + F₁²/2) + O(t³)` for nilpotent `f = t F₁ + t² F₂ + O(t³)`. -/
theorem ExpE2.gexp {f : ℂ → EvR I} {F₁ F₂ : EvR I} (h : ExpE2 f 0 F₁ F₂)
    (h0 : ∀ t, ε (f t : Grassmann.N I) = 0) :
    ExpE2 (fun t => Step.gexp (f t)) 1 F₁ (F₂ + (1 / 2 : ℂ) • F₁ ^ 2) := by
  have h1 := h.ord1
  set M := Nf I + 3
  -- `e^f - (1 + f + f²/2) = ∑_{3 ≤ k < M} f^k / k!`
  have hrep : ∀ t, Step.gexp (f t) - (1 + f t + (1 / 2 : ℂ) • f t ^ 2) =
      ∑ k ∈ (range M).filter (fun k => 3 ≤ k), ((k.factorial : ℂ)⁻¹) • f t ^ k := by
    intro t
    have hk : f t ^ M = 0 := pow_eq_zero_of_ε' (h0 t) (by omega)
    refine Subtype.ext ?_
    rw [Subalgebra.coe_sub, coe_gexp hk, ← sum_filter_add_sum_filter_not (range M)
      (fun k => 3 ≤ k)]
    have e3 : (range M).filter (fun k => ¬ 3 ≤ k) = range 3 := by
      ext k; simp only [mem_filter, mem_range, not_le]; omega
    rw [e3]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, SubmonoidClass.coe_pow, Subalgebra.coe_add, Subalgebra.coe_one,
      Subalgebra.coe_smul]
    norm_num
  have hS : OrdE 3 (fun t => ∑ k ∈ (range M).filter (fun k => 3 ≤ k),
      ((k.factorial : ℂ)⁻¹) • f t ^ k) :=
    OrdE.sum _ fun k hk => OrdE.mono (mem_filter.1 hk).2 ((h1.pow k).smul_const _)
  have hsq : ExpE2 (fun t => f t ^ 2) 0 0 (F₁ ^ 2) := by
    have := h.mul h
    exact (this.congr fun t => by rw [pow_two]).coeffs (by simp) (by simp)
      (by simp [pow_two])
  have := ((ExpE2.const (1 : EvR I)).add h).add (hsq.smul_const (1 / 2 : ℂ))
  have := (ExpE2.of_ord3 hS).add this
  refine (this.congr fun t => ?_).coeffs (by simp) (by simp) (by simp)
  rw [← hrep t]; abel

/-! ### First-order expansions -/

/-- `f(t) = F₀ + t F₁ + O(t²)`. -/
def ExpE1 (f : ℂ → EvR I) (F₀ F₁ : EvR I) : Prop := OrdE 2 (fun t => f t - (F₀ + t • F₁))

theorem ExpE1.hol {f : ℂ → EvR I} {F₀ F₁ : EvR I} (h : ExpE1 f F₀ F₁) : HolE f :=
  HolE.congr ((OrdE.hol h).add ((HolE.const F₀).add (HolE.smul differentiable_id
    (HolE.const F₁)))) fun t => by simp

theorem ExpE1.congr {f g : ℂ → EvR I} {F₀ F₁ : EvR I} (h : ExpE1 f F₀ F₁)
    (e : ∀ t, g t = f t) : ExpE1 g F₀ F₁ := OrdE.congr h fun t => by rw [e]

theorem ExpE1.coeffs {f : ℂ → EvR I} {F₀ F₁ G₀ G₁ : EvR I} (h : ExpE1 f F₀ F₁)
    (e₀ : G₀ = F₀) (e₁ : G₁ = F₁) : ExpE1 f G₀ G₁ := by subst e₀ e₁; exact h

theorem ExpE1.of_ord2 {f : ℂ → EvR I} (h : OrdE 2 f) : ExpE1 f 0 0 :=
  OrdE.congr h fun t => by simp

theorem ExpE1.of_exp2 {f : ℂ → EvR I} {F₀ F₁ F₂ : EvR I} (h : ExpE2 f F₀ F₁ F₂) :
    ExpE1 f F₀ F₁ := by
  have h1 : OrdE 2 (fun t => f t - (F₀ + t • F₁ + t ^ 2 • F₂)) := OrdE.mono (by norm_num) h
  exact OrdE.congr (h1.add (OrdE.const_pow 2 F₂)) fun t => by abel

theorem ExpE1.const (F : EvR I) : ExpE1 (fun _ => F) F 0 :=
  (OrdE.zero 2).congr fun t => by simp

theorem ExpE1.lin (F : EvR I) : ExpE1 (fun t => t • F) 0 F :=
  (OrdE.zero 2).congr fun t => by simp

theorem ExpE1.add {f g : ℂ → EvR I} {F₀ F₁ G₀ G₁ : EvR I} (h1 : ExpE1 f F₀ F₁)
    (h2 : ExpE1 g G₀ G₁) : ExpE1 (fun t => f t + g t) (F₀ + G₀) (F₁ + G₁) :=
  OrdE.congr (OrdE.add h1 h2) fun t => by simp only [smul_add]; abel

theorem ExpE1.sub {f g : ℂ → EvR I} {F₀ F₁ G₀ G₁ : EvR I} (h1 : ExpE1 f F₀ F₁)
    (h2 : ExpE1 g G₀ G₁) : ExpE1 (fun t => f t - g t) (F₀ - G₀) (F₁ - G₁) :=
  OrdE.congr (OrdE.sub h1 h2) fun t => by simp only [smul_sub]; abel

theorem ExpE1.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → EvR I} {F₀ F₁ : ι → EvR I}
    (h : ∀ i ∈ s, ExpE1 (f i) (F₀ i) (F₁ i)) :
    ExpE1 (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, F₀ i) (∑ i ∈ s, F₁ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (ExpE1.const 0).congr fun t => by simp
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem ExpE1.map {J : Type*} [DecidableEq J] [Fintype J] {f : ℂ → EvR I} {F₀ F₁ : EvR I}
    (h : ExpE1 f F₀ F₁) (T : EvR I →ₗ[ℂ] EvR J) :
    ExpE1 (fun t => T (f t)) (T F₀) (T F₁) :=
  OrdE.congr (OrdE.map h T) fun t => by simp only [map_sub, map_add, map_smul]

theorem ExpE1.mapA {J : Type*} [DecidableEq J] [Fintype J] {f : ℂ → EvR I} {F₀ F₁ : EvR I}
    (h : ExpE1 f F₀ F₁) (T : EvR I →ₐ[ℂ] EvR J) :
    ExpE1 (fun t => T (f t)) (T F₀) (T F₁) :=
  h.map T.toLinearMap

theorem ExpE1.mul {f g : ℂ → EvR I} {F₀ F₁ G₀ G₁ : EvR I} (h1 : ExpE1 f F₀ F₁)
    (h2 : ExpE1 g G₀ G₁) :
    ExpE1 (fun t => f t * g t) (F₀ * G₀) (F₀ * G₁ + F₁ * G₀) := by
  have hg := h2.hol
  have e1 : OrdE 2 (fun t => (f t - (F₀ + t • F₁)) * g t) := by
    simpa using OrdE.mul h1 (OrdE.of_hol hg)
  have hp : HolE (fun t : ℂ => F₀ + t • F₁) :=
    (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
  have e2 : OrdE 2 (fun t => (F₀ + t • F₁) * (g t - (G₀ + t • G₁))) := by
    simpa using (OrdE.of_hol hp).mul (h2 : OrdE 2 _)
  have e3 : OrdE 2 (fun t => t ^ 2 • (F₁ * G₁)) := OrdE.const_pow 2 _
  refine OrdE.congr ((e1.add e2).add e3) fun t => ?_
  simp only [smul_eq_alg, map_pow]
  ring

theorem ExpE1.ord1 {f : ℂ → EvR I} {F₁ : EvR I} (h : ExpE1 f 0 F₁) : OrdE 1 f := by
  have e : OrdE 1 (fun t => f t - (0 + t • F₁)) := OrdE.mono (by norm_num) h
  exact OrdE.congr (e.add (⟨fun _ => F₁, HolE.const _, fun t => by simp⟩ :
    OrdE 1 (fun t => t • F₁))) fun t => by abel

theorem ExpE1.smulS {φ : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} {f : ℂ → EvR I} {F₀ F₁ : EvR I}
    (hφ : ExpS2 φ a₀ a₁ a₂) (h : ExpE1 f F₀ F₁) :
    ExpE1 (fun t => φ t • f t) (a₀ • F₀) (a₀ • F₁ + a₁ • F₀) := by
  have := (ExpE1.of_exp2 (ExpE2.ofS (I := I) hφ)).mul h
  refine (this.congr fun t => by rw [smul_eq_alg]).coeffs ?_ ?_ <;> simp [smul_eq_alg]

/-- Products: if every factor is `1 + O(t)`, so is the product. -/
theorem ExpE1.prod_one {ι : Type*} (s : Finset ι) {f : ι → ℂ → EvR I}
    (h : ∀ i ∈ s, ∃ F₁, ExpE1 (f i) 1 F₁) :
    ∃ F₁, ExpE1 (fun t => ∏ i ∈ s, f i t) 1 F₁ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, (ExpE1.const 1).congr fun t => by simp⟩
  | insert a s ha ih =>
    obtain ⟨F₁, hF⟩ := h a (mem_insert_self _ _)
    obtain ⟨G₁, hG⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    exact ⟨_, ((hF.mul hG).congr fun t => by rw [prod_insert ha]).coeffs (by simp) rfl⟩

end Elements

end

end Step2
