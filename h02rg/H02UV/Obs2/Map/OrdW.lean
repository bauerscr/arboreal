import Obs2.Map.HolW
import Step2.Map.Exp

/-!
# Order of vanishing and expansions in a finite-dimensional algebra

The calculus `Step2.OrdE`, `Step2.ExpE2`, `Step2.ExpE1` of `Step2.Map.Ord`/`Step2.Map.Exp`, for functions
`ℂ → R` with values in a finite-dimensional commutative `ℂ`-algebra `R` and the weak holomorphy
`HolW` (`OrdW`, `ExpW2`, `ExpW1`). Same statements and proofs. The exponential of a nilpotent
element with sources is `ExpW2.oexp` (in `OE c Λ`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Step Step2

section Gen

variable {R : Type*} [CommRing R] [Algebra ℂ R] [FiniteDimensional ℂ R]

/-- `f(t) = t^n • g(t)` with `g` weakly holomorphic. -/
def OrdW (n : ℕ) (f : ℂ → R) : Prop := ∃ g : ℂ → R, HolW g ∧ ∀ t, f t = t ^ n • g t

theorem OrdW.hol {n : ℕ} {f : ℂ → R} (h : OrdW n f) : HolW f := by
  obtain ⟨g, hg, e⟩ := h
  exact (HolW.smul (differentiable_id.pow n) hg).congr e

theorem OrdW.of_hol {f : ℂ → R} (h : HolW f) : OrdW 0 f := ⟨f, h, fun t => by simp⟩

theorem OrdW.zero (n : ℕ) : OrdW n (fun _ => (0 : R)) := ⟨fun _ => 0, HolW.const _, by simp⟩

theorem OrdW.congr {n : ℕ} {f g : ℂ → R} (h : OrdW n f) (e : ∀ t, g t = f t) : OrdW n g := by
  obtain ⟨g', hg, e'⟩ := h
  exact ⟨g', hg, fun t => by beta_reduce; rw [e, e']⟩

theorem OrdW.add {n : ℕ} {f g : ℂ → R} (h1 : OrdW n f) (h2 : OrdW n g) :
    OrdW n (fun t => f t + g t) := by
  obtain ⟨g1, hg1, e1⟩ := h1
  obtain ⟨g2, hg2, e2⟩ := h2
  exact ⟨fun t => g1 t + g2 t, hg1.add hg2, fun t => by beta_reduce; rw [e1, e2, smul_add]⟩

theorem OrdW.neg {n : ℕ} {f : ℂ → R} (h : OrdW n f) : OrdW n (fun t => -f t) := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun t => -g t, hg.neg, fun t => by beta_reduce; rw [e, smul_neg]⟩

theorem OrdW.sub {n : ℕ} {f g : ℂ → R} (h1 : OrdW n f) (h2 : OrdW n g) :
    OrdW n (fun t => f t - g t) := by
  simpa [sub_eq_add_neg] using h1.add h2.neg

theorem OrdW.mul {m n : ℕ} {f g : ℂ → R} (h1 : OrdW m f) (h2 : OrdW n g) :
    OrdW (m + n) (fun t => f t * g t) := by
  obtain ⟨g1, hg1, e1⟩ := h1
  obtain ⟨g2, hg2, e2⟩ := h2
  exact ⟨fun t => g1 t * g2 t, hg1.mul hg2, fun t => by
    beta_reduce; rw [e1, e2, smul_mul_smul_comm, pow_add]⟩

theorem OrdW.smul {m n : ℕ} {c : ℂ → ℂ} {f : ℂ → R} (hc : OrdS m c) (h : OrdW n f) :
    OrdW (m + n) (fun t => c t • f t) := by
  obtain ⟨h1, hh1, e1⟩ := hc
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun t => h1 t • g t, HolW.smul hh1 hg, fun t => by
    beta_reduce; rw [e1, e, smul_smul, smul_smul, pow_add]; ring_nf⟩

theorem OrdW.smul_const {n : ℕ} (c : ℂ) {f : ℂ → R} (h : OrdW n f) : OrdW n (fun t => c • f t) := by
  simpa using OrdW.smul (OrdS.of_differentiable (differentiable_const c)) h

theorem OrdW.mono {m n : ℕ} (hmn : m ≤ n) {f : ℂ → R} (h : OrdW n f) : OrdW m f := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun t => t ^ (n - m) • g t, HolW.smul (differentiable_id.pow _) hg, fun t => ?_⟩
  rw [e, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]

theorem OrdW.map {R' : Type*} [CommRing R'] [Algebra ℂ R'] [FiniteDimensional ℂ R'] {n : ℕ}
    {f : ℂ → R} (h : OrdW n f) (T : R →ₗ[ℂ] R') : OrdW n (fun t => T (f t)) := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun t => T (g t), hg.map T, fun t => by beta_reduce; rw [e, map_smul]⟩

theorem OrdW.sum {ι : Type*} (s : Finset ι) {n : ℕ} {f : ι → ℂ → R}
    (h : ∀ i ∈ s, OrdW n (f i)) : OrdW n (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OrdW.zero (R := R) n
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem OrdW.prod {ι : Type*} (s : Finset ι) {f : ι → ℂ → R}
    (h : ∀ i ∈ s, OrdW 1 (f i)) : OrdW s.card (fun t => ∏ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OrdW.of_hol (HolW.const (E := ℂ) (1 : R))
  | insert a s ha ih =>
    simp only [prod_insert ha, card_insert_of_notMem ha]
    rw [add_comm]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem OrdW.const_pow (n : ℕ) (F : R) : OrdW n (fun t => t ^ n • F) :=
  ⟨fun _ => F, HolW.const _, fun _ => rfl⟩

theorem OrdW.pow {f : ℂ → R} (h : OrdW 1 f) (k : ℕ) : OrdW k (fun t => f t ^ k) := by
  induction k with
  | zero => simpa using OrdW.of_hol (HolW.const (E := ℂ) (1 : R))
  | succ k ih =>
    rw [add_comm]
    exact OrdW.congr (h.mul ih) fun t => by rw [add_comm, pow_succ']

/-! ### Second-order expansions -/

/-- `f(t) = F₀ + t F₁ + t² F₂ + O(t³)`. -/
def ExpW2 (f : ℂ → R) (F₀ F₁ F₂ : R) : Prop := OrdW 3 (fun t => f t - (F₀ + t • F₁ + t ^ 2 • F₂))

theorem polyW_hol (F₀ F₁ F₂ : R) : HolW (fun t : ℂ => F₀ + t • F₁ + t ^ 2 • F₂) :=
  ((HolW.const _).add (HolW.smul differentiable_id (HolW.const _))).add
    (HolW.smul (differentiable_id.pow 2) (HolW.const _))

theorem ExpW2.hol {f : ℂ → R} {F₀ F₁ F₂ : R} (h : ExpW2 f F₀ F₁ F₂) : HolW f :=
  ((OrdW.hol h).add (polyW_hol F₀ F₁ F₂)).congr fun t => by simp

theorem ExpW2.congr {f g : ℂ → R} {F₀ F₁ F₂ : R} (h : ExpW2 f F₀ F₁ F₂)
    (e : ∀ t, g t = f t) : ExpW2 g F₀ F₁ F₂ := OrdW.congr h fun t => by rw [e]

theorem ExpW2.coeffs {f : ℂ → R} {F₀ F₁ F₂ G₀ G₁ G₂ : R} (h : ExpW2 f F₀ F₁ F₂)
    (e₀ : G₀ = F₀) (e₁ : G₁ = F₁) (e₂ : G₂ = F₂) : ExpW2 f G₀ G₁ G₂ := by
  subst e₀ e₁ e₂; exact h

theorem ExpW2.of_ord3 {f : ℂ → R} (h : OrdW 3 f) : ExpW2 f 0 0 0 := OrdW.congr h fun t => by simp

theorem ExpW2.const (F : R) : ExpW2 (fun _ => F) F 0 0 := (OrdW.zero 3).congr fun t => by simp

theorem ExpW2.lin (F : R) : ExpW2 (fun t => t • F) 0 F 0 := (OrdW.zero 3).congr fun t => by simp

theorem ExpW2.quad (F : R) : ExpW2 (fun t => t ^ 2 • F) 0 0 F :=
  (OrdW.zero 3).congr fun t => by simp

theorem ExpW2.add {f g : ℂ → R} {F₀ F₁ F₂ G₀ G₁ G₂ : R} (h1 : ExpW2 f F₀ F₁ F₂)
    (h2 : ExpW2 g G₀ G₁ G₂) : ExpW2 (fun t => f t + g t) (F₀ + G₀) (F₁ + G₁) (F₂ + G₂) :=
  OrdW.congr (OrdW.add h1 h2) fun t => by simp only [smul_add]; abel

theorem ExpW2.sub {f g : ℂ → R} {F₀ F₁ F₂ G₀ G₁ G₂ : R} (h1 : ExpW2 f F₀ F₁ F₂)
    (h2 : ExpW2 g G₀ G₁ G₂) : ExpW2 (fun t => f t - g t) (F₀ - G₀) (F₁ - G₁) (F₂ - G₂) :=
  OrdW.congr (OrdW.sub h1 h2) fun t => by simp only [smul_sub]; abel

theorem ExpW2.smul_const (c : ℂ) {f : ℂ → R} {F₀ F₁ F₂ : R} (h : ExpW2 f F₀ F₁ F₂) :
    ExpW2 (fun t => c • f t) (c • F₀) (c • F₁) (c • F₂) :=
  OrdW.congr (OrdW.smul_const c h) fun t => by
    simp only [smul_sub, smul_add, smul_comm c t, smul_comm c]

theorem ExpW2.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → R} {F₀ F₁ F₂ : ι → R}
    (h : ∀ i ∈ s, ExpW2 (f i) (F₀ i) (F₁ i) (F₂ i)) :
    ExpW2 (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, F₀ i) (∑ i ∈ s, F₁ i) (∑ i ∈ s, F₂ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (ExpW2.const (0 : R)).congr fun t => by simp
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem ExpW2.map {R' : Type*} [CommRing R'] [Algebra ℂ R'] [FiniteDimensional ℂ R']
    {f : ℂ → R} {F₀ F₁ F₂ : R} (h : ExpW2 f F₀ F₁ F₂) (T : R →ₗ[ℂ] R') :
    ExpW2 (fun t => T (f t)) (T F₀) (T F₁) (T F₂) :=
  OrdW.congr (OrdW.map h T) fun t => by simp only [map_sub, map_add, map_smul]

theorem smul_eq_algW (t : ℂ) (F : R) : t • F = algebraMap ℂ R t * F := Algebra.smul_def t F

theorem ExpW2.mul {f g : ℂ → R} {F₀ F₁ F₂ G₀ G₁ G₂ : R} (h1 : ExpW2 f F₀ F₁ F₂)
    (h2 : ExpW2 g G₀ G₁ G₂) :
    ExpW2 (fun t => f t * g t) (F₀ * G₀) (F₀ * G₁ + F₁ * G₀) (F₀ * G₂ + F₁ * G₁ + F₂ * G₀) := by
  have hg := h2.hol
  have e1 : OrdW 3 (fun t => (f t - (F₀ + t • F₁ + t ^ 2 • F₂)) * g t) := by
    simpa using OrdW.mul h1 (OrdW.of_hol hg)
  have e2 : OrdW 3 (fun t => (F₀ + t • F₁ + t ^ 2 • F₂) * (g t - (G₀ + t • G₁ + t ^ 2 • G₂))) := by
    simpa using (OrdW.of_hol (polyW_hol F₀ F₁ F₂)).mul (h2 : OrdW 3 _)
  have e3 : OrdW 3 (fun t => t ^ 3 • (F₁ * G₂ + F₂ * G₁ + t • (F₂ * G₂))) :=
    ⟨_, (HolW.const _).add (HolW.smul differentiable_id (HolW.const _)), fun _ => rfl⟩
  refine OrdW.congr ((e1.add e2).add e3) fun t => ?_
  simp only [smul_eq_algW, map_pow]
  ring

theorem ExpW2.ofS {φ : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} (h : ExpS2 φ a₀ a₁ a₂) :
    ExpW2 (fun t => algebraMap ℂ R (φ t)) (algebraMap ℂ _ a₀) (algebraMap ℂ _ a₁)
      (algebraMap ℂ _ a₂) := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun t => g t • (1 : R), HolW.smul hg (HolW.const _), fun t => ?_⟩
  have h1 : φ t = (a₀ + t * a₁ + t ^ 2 * a₂) + t ^ 3 * g t := by
    have := e t
    simp only at this
    linear_combination this
  beta_reduce
  rw [h1]
  simp only [smul_eq_algW, map_add, map_mul, map_pow, mul_one]
  ring

theorem ExpW2.smulS {φ : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} {f : ℂ → R} {F₀ F₁ F₂ : R}
    (hφ : ExpS2 φ a₀ a₁ a₂) (h : ExpW2 f F₀ F₁ F₂) :
    ExpW2 (fun t => φ t • f t) (a₀ • F₀) (a₀ • F₁ + a₁ • F₀) (a₀ • F₂ + a₁ • F₁ + a₂ • F₀) := by
  have := (ExpW2.ofS (R := R) hφ).mul h
  refine (this.congr fun t => by rw [smul_eq_algW]).coeffs ?_ ?_ ?_ <;> simp [smul_eq_algW]

theorem ExpW2.ord1 {f : ℂ → R} {F₁ F₂ : R} (h : ExpW2 f 0 F₁ F₂) : OrdW 1 f := by
  have e : OrdW 1 (fun t => f t - (0 + t • F₁ + t ^ 2 • F₂)) := OrdW.mono (by norm_num) h
  have e' : OrdW 1 (fun t => t • (F₁ + t • F₂)) :=
    ⟨fun t => F₁ + t • F₂, (HolW.const _).add (HolW.smul differentiable_id (HolW.const _)),
      fun t => by simp⟩
  exact (e.add e').congr fun t => by simp only [smul_add, smul_smul, ← pow_two]; abel

/-- The exponential of a nilpotent `f = t F₁ + t² F₂ + O(t³)` with a uniform nilpotency order. -/
theorem ExpW2.expN {f : ℂ → R} {F₁ F₂ : R} (h : ExpW2 f 0 F₁ F₂) {M : ℕ} (hM : 3 ≤ M)
    (E : ℂ → R) (hE : ∀ t, E t = ∑ k ∈ range M, ((k.factorial : ℂ)⁻¹) • f t ^ k) :
    ExpW2 E 1 F₁ (F₂ + (1 / 2 : ℂ) • F₁ ^ 2) := by
  have h1 := h.ord1
  have hrep : ∀ t, E t - (1 + f t + (1 / 2 : ℂ) • f t ^ 2) =
      ∑ k ∈ (range M).filter (fun k => 3 ≤ k), ((k.factorial : ℂ)⁻¹) • f t ^ k := by
    intro t
    rw [hE, ← sum_filter_add_sum_filter_not (range M) (fun k => 3 ≤ k)]
    have e3 : (range M).filter (fun k => ¬ 3 ≤ k) = range 3 := by
      ext k; simp only [mem_filter, mem_range, not_le]; omega
    rw [e3]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have hS : OrdW 3 (fun t => ∑ k ∈ (range M).filter (fun k => 3 ≤ k),
      ((k.factorial : ℂ)⁻¹) • f t ^ k) :=
    OrdW.sum _ fun k hk => OrdW.mono (mem_filter.1 hk).2 ((h1.pow k).smul_const _)
  have hsq : ExpW2 (fun t => f t ^ 2) 0 0 (F₁ ^ 2) := by
    have := h.mul h
    exact (this.congr fun t => by rw [pow_two]).coeffs (by simp) (by simp) (by simp [pow_two])
  have := ((ExpW2.const (1 : R)).add h).add (hsq.smul_const (1 / 2 : ℂ))
  have := (ExpW2.of_ord3 hS).add this
  refine (this.congr fun t => ?_).coeffs (by simp) (by simp) (by simp)
  rw [← hrep t]; abel

/-! ### First-order expansions -/

/-- `f(t) = F₀ + t F₁ + O(t²)`. -/
def ExpW1 (f : ℂ → R) (F₀ F₁ : R) : Prop := OrdW 2 (fun t => f t - (F₀ + t • F₁))

theorem ExpW1.hol {f : ℂ → R} {F₀ F₁ : R} (h : ExpW1 f F₀ F₁) : HolW f :=
  ((OrdW.hol h).add ((HolW.const F₀).add (HolW.smul differentiable_id
    (HolW.const F₁)))).congr fun t => by simp

theorem ExpW1.congr {f g : ℂ → R} {F₀ F₁ : R} (h : ExpW1 f F₀ F₁)
    (e : ∀ t, g t = f t) : ExpW1 g F₀ F₁ := OrdW.congr h fun t => by rw [e]

theorem ExpW1.coeffs {f : ℂ → R} {F₀ F₁ G₀ G₁ : R} (h : ExpW1 f F₀ F₁)
    (e₀ : G₀ = F₀) (e₁ : G₁ = F₁) : ExpW1 f G₀ G₁ := by subst e₀ e₁; exact h

theorem ExpW1.of_ord2 {f : ℂ → R} (h : OrdW 2 f) : ExpW1 f 0 0 := OrdW.congr h fun t => by simp

theorem ExpW1.of_exp2 {f : ℂ → R} {F₀ F₁ F₂ : R} (h : ExpW2 f F₀ F₁ F₂) : ExpW1 f F₀ F₁ := by
  have h1 : OrdW 2 (fun t => f t - (F₀ + t • F₁ + t ^ 2 • F₂)) := OrdW.mono (by norm_num) h
  exact OrdW.congr (h1.add (OrdW.const_pow 2 F₂)) fun t => by abel

theorem ExpW1.const (F : R) : ExpW1 (fun _ => F) F 0 := (OrdW.zero 2).congr fun t => by simp

theorem ExpW1.lin (F : R) : ExpW1 (fun t => t • F) 0 F := (OrdW.zero 2).congr fun t => by simp

theorem ExpW1.add {f g : ℂ → R} {F₀ F₁ G₀ G₁ : R} (h1 : ExpW1 f F₀ F₁)
    (h2 : ExpW1 g G₀ G₁) : ExpW1 (fun t => f t + g t) (F₀ + G₀) (F₁ + G₁) :=
  OrdW.congr (OrdW.add h1 h2) fun t => by simp only [smul_add]; abel

theorem ExpW1.sub {f g : ℂ → R} {F₀ F₁ G₀ G₁ : R} (h1 : ExpW1 f F₀ F₁)
    (h2 : ExpW1 g G₀ G₁) : ExpW1 (fun t => f t - g t) (F₀ - G₀) (F₁ - G₁) :=
  OrdW.congr (OrdW.sub h1 h2) fun t => by simp only [smul_sub]; abel

theorem ExpW1.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → R} {F₀ F₁ : ι → R}
    (h : ∀ i ∈ s, ExpW1 (f i) (F₀ i) (F₁ i)) :
    ExpW1 (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, F₀ i) (∑ i ∈ s, F₁ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (ExpW1.const (0 : R)).congr fun t => by simp
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem ExpW1.map {R' : Type*} [CommRing R'] [Algebra ℂ R'] [FiniteDimensional ℂ R']
    {f : ℂ → R} {F₀ F₁ : R} (h : ExpW1 f F₀ F₁) (T : R →ₗ[ℂ] R') :
    ExpW1 (fun t => T (f t)) (T F₀) (T F₁) :=
  OrdW.congr (OrdW.map h T) fun t => by simp only [map_sub, map_add, map_smul]

theorem ExpW1.mul {f g : ℂ → R} {F₀ F₁ G₀ G₁ : R} (h1 : ExpW1 f F₀ F₁)
    (h2 : ExpW1 g G₀ G₁) :
    ExpW1 (fun t => f t * g t) (F₀ * G₀) (F₀ * G₁ + F₁ * G₀) := by
  have hg := h2.hol
  have e1 : OrdW 2 (fun t => (f t - (F₀ + t • F₁)) * g t) := by
    simpa using OrdW.mul h1 (OrdW.of_hol hg)
  have hp : HolW (fun t : ℂ => F₀ + t • F₁) :=
    (HolW.const _).add (HolW.smul differentiable_id (HolW.const _))
  have e2 : OrdW 2 (fun t => (F₀ + t • F₁) * (g t - (G₀ + t • G₁))) := by
    simpa using (OrdW.of_hol hp).mul (h2 : OrdW 2 _)
  have e3 : OrdW 2 (fun t => t ^ 2 • (F₁ * G₁)) := OrdW.const_pow 2 _
  refine OrdW.congr ((e1.add e2).add e3) fun t => ?_
  simp only [smul_eq_algW, map_pow]
  ring

theorem ExpW1.ord1 {f : ℂ → R} {F₁ : R} (h : ExpW1 f 0 F₁) : OrdW 1 f := by
  have e : OrdW 1 (fun t => f t - (0 + t • F₁)) := OrdW.mono (by norm_num) h
  exact OrdW.congr (e.add (⟨fun _ => F₁, HolW.const _, fun t => by simp⟩ :
    OrdW 1 (fun t => t • F₁))) fun t => by abel

theorem ExpW1.smulS {φ : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} {f : ℂ → R} {F₀ F₁ : R}
    (hφ : ExpS2 φ a₀ a₁ a₂) (h : ExpW1 f F₀ F₁) :
    ExpW1 (fun t => φ t • f t) (a₀ • F₀) (a₀ • F₁ + a₁ • F₀) := by
  have := (ExpW1.of_exp2 (ExpW2.ofS (R := R) hφ)).mul h
  refine (this.congr fun t => by rw [smul_eq_algW]).coeffs ?_ ?_ <;> simp [smul_eq_algW]

/-- Products: if every factor is `1 + O(t)`, so is the product. -/
theorem ExpW1.prod_one {ι : Type*} (s : Finset ι) {f : ι → ℂ → R}
    (h : ∀ i ∈ s, ∃ F₁, ExpW1 (f i) 1 F₁) :
    ∃ F₁, ExpW1 (fun t => ∏ i ∈ s, f i t) 1 F₁ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, (ExpW1.const (1 : R)).congr fun t => by simp⟩
  | insert a s ha ih =>
    obtain ⟨F₁, hF⟩ := h a (mem_insert_self _ _)
    obtain ⟨G₁, hG⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    exact ⟨_, ((hF.mul hG).congr fun t => by rw [prod_insert ha]).coeffs (by simp) rfl⟩

/-- Products: if every factor is `1 + t F₁ + t² F₂ + O(t³)`, so is the product. -/
theorem ExpW2.prod_one {ι : Type*} (s : Finset ι) {f : ι → ℂ → R}
    (h : ∀ i ∈ s, ∃ F₁ F₂, ExpW2 (f i) 1 F₁ F₂) :
    ∃ F₁ F₂, ExpW2 (fun t => ∏ i ∈ s, f i t) 1 F₁ F₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, (ExpW2.const (1 : R)).congr fun t => by simp⟩
  | insert a s ha ih =>
    obtain ⟨F₁, F₂, hF⟩ := h a (mem_insert_self _ _)
    obtain ⟨G₁, G₂, hG⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    exact ⟨_, _, ((hF.mul hG).congr fun t => by rw [prod_insert ha]).coeffs (by simp) rfl rfl⟩

end Gen

/-! ### The exponential with sources -/

section OE

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `e^f = 1 + t F₁ + t² (F₂ + F₁²/2) + O(t³)` for `f = t F₁ + t² F₂ + O(t³)` with `ε(f_∅) = 0`. -/
theorem ExpW2.oexp {f : ℂ → OE c Λ} {F₁ F₂ : OE c Λ} (h : ExpW2 f 0 F₁ F₂)
    (h0 : ∀ t, ε ((f t : SA c Λ).e) = 0) :
    ExpW2 (fun t => Obs.oexp (f t)) 1 F₁ (F₂ + (1 / 2 : ℂ) • F₁ ^ 2) :=
  h.expN (M := Nf Λ + 3) (by omega) _ fun t => coe_oexp (pow_eq_zero_of_ε (h0 t))

end OE

end

end Obs2
