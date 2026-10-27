import Step.Hol
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Functions vanishing to order `n` at `t = 0`

For the exact second-order computation of `h02uv-outline.tex` (`e:K2`) we use a calculus of
entire functions of `t ∈ ℂ` vanishing to a given order at `0`:

* `OrdS n φ` (scalar): `φ(t) = t^n h(t)` with `h` entire;
* `OrdE n f` (even Grassmann elements): `f(t) = t^n • g(t)` with `g` coefficient-wise entire.

Both are closed under sums, products (orders add), entire scalar factors, and fixed linear
maps. The scalar exponential satisfies `e^z = 1 + z + z²/2 + z³ E₃(z)` with `E₃` entire
(`exp_eq_taylor3`), and the exponential of a nilpotent `t A + t² B` is
`1 + t A + t² (A²/2 + B) + O(t³)` (`OrdE.gexp_quad`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Filter Topology

/-! ### Scalars -/

/-- `φ(t) = t^n h(t)` with `h` entire. -/
def OrdS (n : ℕ) (φ : ℂ → ℂ) : Prop := ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ t, φ t = t ^ n * h t

theorem OrdS.differentiable {n : ℕ} {φ : ℂ → ℂ} (h : OrdS n φ) : Differentiable ℂ φ := by
  obtain ⟨g, hg, e⟩ := h
  have : φ = fun t => t ^ n * g t := funext e
  rw [this]; exact (differentiable_id.pow n).mul hg

theorem OrdS.of_differentiable {φ : ℂ → ℂ} (h : Differentiable ℂ φ) : OrdS 0 φ :=
  ⟨φ, h, fun t => by simp⟩

theorem OrdS.zero (n : ℕ) : OrdS n (fun _ => 0) := ⟨fun _ => 0, differentiable_const _, by simp⟩

theorem OrdS.add {n : ℕ} {φ ψ : ℂ → ℂ} (h1 : OrdS n φ) (h2 : OrdS n ψ) :
    OrdS n (fun t => φ t + ψ t) := by
  obtain ⟨g1, hg1, e1⟩ := h1
  obtain ⟨g2, hg2, e2⟩ := h2
  exact ⟨fun t => g1 t + g2 t, hg1.add hg2, fun t => by beta_reduce; rw [e1, e2]; ring⟩

theorem OrdS.mul {m n : ℕ} {φ ψ : ℂ → ℂ} (h1 : OrdS m φ) (h2 : OrdS n ψ) :
    OrdS (m + n) (fun t => φ t * ψ t) := by
  obtain ⟨g1, hg1, e1⟩ := h1
  obtain ⟨g2, hg2, e2⟩ := h2
  exact ⟨fun t => g1 t * g2 t, hg1.mul hg2, fun t => by beta_reduce; rw [e1, e2, pow_add]; ring⟩

theorem OrdS.mono {m n : ℕ} (hmn : m ≤ n) {φ : ℂ → ℂ} (h : OrdS n φ) : OrdS m φ := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun t => t ^ (n - m) * g t, (differentiable_id.pow _).mul hg, fun t => ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]

theorem OrdS.congr {n : ℕ} {φ ψ : ℂ → ℂ} (h : OrdS n φ) (e : ∀ t, ψ t = φ t) : OrdS n ψ := by
  obtain ⟨g, hg, e'⟩ := h
  exact ⟨g, hg, fun t => by beta_reduce; rw [e, e']⟩

theorem OrdS.pow_mul {n : ℕ} {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    OrdS n (fun t => t ^ n * h t) := ⟨h, hh, fun _ => rfl⟩

/-- An entire function vanishing at `0` is `t h(t)` with `h` entire. -/
theorem OrdS.one_of_zero {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (h0 : φ 0 = 0) : OrdS 1 φ := by
  refine ⟨dslope φ 0, ?_, fun t => ?_⟩
  · have := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).2
      hφ.differentiableOn
    exact fun t => (this t (Set.mem_univ t)).differentiableAt Filter.univ_mem
  · have := sub_smul_dslope φ 0 t
    rw [h0, sub_zero, sub_zero, smul_eq_mul] at this
    rw [pow_one, this]

/-- `e^z - 1 - z - z²/2 = z³ E₃(z)` with `E₃` entire. -/
theorem exp_eq_taylor3 : ∃ E₃ : ℂ → ℂ, Differentiable ℂ E₃ ∧
    ∀ z, Complex.exp z = 1 + z + z ^ 2 / 2 + z ^ 3 * E₃ z := by
  set f : ℂ → ℂ := fun z => Complex.exp z - 1 - z - z ^ 2 / 2 with hf
  have hfd : Differentiable ℂ f := by
    refine ((Complex.differentiable_exp.sub (differentiable_const _)).sub differentiable_id).sub ?_
    exact (differentiable_id.pow 2).div_const 2
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ ‖z‖ ^ 3 := by
    intro z hz
    have := Complex.exp_bound hz (n := 3) (by norm_num)
    have e : ∑ m ∈ range 3, z ^ m / (m.factorial : ℂ) = 1 + z + z ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [e] at this
    have e2 : f z = Complex.exp z - (1 + z + z ^ 2 / 2) := by simp only [hf]; ring
    rw [e2]
    refine this.trans ?_
    have : ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * 3)⁻¹) ≤ 1 := by norm_num [Nat.factorial]
    calc ‖z‖ ^ 3 * ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * 3)⁻¹) ≤ ‖z‖ ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ‖z‖ ^ 3 := mul_one _
  have hf0 : f 0 = 0 := by simp [hf]
  obtain ⟨g1, hg1, e1⟩ := OrdS.one_of_zero hfd hf0
  -- `g1 (0) = 0` and `g1` has derivative `0` at `0`
  have hg1z : ∀ z, z ≠ 0 → g1 z = f z / z := fun z hz => by
    rw [e1 z, pow_one, mul_div_cancel_left₀ _ hz]
  have hg10 : g1 0 = 0 := by
    have hc : ContinuousAt g1 0 := (hg1 0).continuousAt
    have hlim : Tendsto g1 (𝓝[≠] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro δ hδ
      refine ⟨min δ 1, lt_min hδ one_pos, fun z hz hzd => ?_⟩
      have hz0 : z ≠ 0 := hz
      rw [dist_zero_right] at hzd ⊢
      have hz1 : ‖z‖ ≤ 1 := (lt_min_iff.1 hzd).2.le
      rw [hg1z z hz0, norm_div]
      have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz0
      calc ‖f z‖ / ‖z‖ ≤ ‖z‖ ^ 3 / ‖z‖ := div_le_div_of_nonneg_right (hbound z hz1) hzp.le
        _ = ‖z‖ ^ 2 := by field_simp
        _ ≤ ‖z‖ := by nlinarith [norm_nonneg z]
        _ < δ := (lt_min_iff.1 hzd).1
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  obtain ⟨g2, hg2, e2⟩ := OrdS.one_of_zero hg1 hg10
  have hg2z : ∀ z, z ≠ 0 → g2 z = f z / z ^ 2 := fun z hz => by
    have := e2 z
    rw [hg1z z hz, pow_one] at this
    have h2 : f z = z ^ 2 * g2 z := by
      have hz' : (z : ℂ) ≠ 0 := hz
      field_simp at this
      linear_combination this
    rw [h2]; field_simp
  have hg20 : g2 0 = 0 := by
    have hc : ContinuousAt g2 0 := (hg2 0).continuousAt
    have hlim : Tendsto g2 (𝓝[≠] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro δ hδ
      refine ⟨min δ 1, lt_min hδ one_pos, fun z hz hzd => ?_⟩
      have hz0 : z ≠ 0 := hz
      rw [dist_zero_right] at hzd ⊢
      have hz1 : ‖z‖ ≤ 1 := (lt_min_iff.1 hzd).2.le
      rw [hg2z z hz0, norm_div, norm_pow]
      have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz0
      calc ‖f z‖ / ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 / ‖z‖ ^ 2 :=
            div_le_div_of_nonneg_right (hbound z hz1) (by positivity)
        _ = ‖z‖ := by field_simp
        _ < δ := (lt_min_iff.1 hzd).1
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  obtain ⟨g3, hg3, e3⟩ := OrdS.one_of_zero hg2 hg20
  refine ⟨g3, hg3, fun z => ?_⟩
  have h1 := e1 z
  have h2 := e2 z
  have h3 := e3 z
  have : f z = z ^ 3 * g3 z := by
    rw [h1, h2, h3]; ring
  simp only [hf] at this
  linear_combination this

/-- `e^{q(t)} = 1 + q + q²/2 + O(t³)` for an entire `q` vanishing at `0`. -/
theorem OrdS.exp_taylor {q : ℂ → ℂ} (hq : OrdS 1 q) :
    OrdS 3 (fun t => Complex.exp (q t) - (1 + q t + q t ^ 2 / 2)) := by
  obtain ⟨E₃, hE, he⟩ := exp_eq_taylor3
  have hqd := hq.differentiable
  obtain ⟨g, hg, e⟩ := hq
  refine ⟨fun t => g t ^ 3 * E₃ (q t), (hg.pow 3).mul (hE.comp hqd), fun t => ?_⟩
  beta_reduce
  rw [he, e t]
  ring

/-! ### Even Grassmann elements -/

section Elements

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- `f(t) = t^n • g(t)` with `g` coefficient-wise entire. -/
def OrdE (n : ℕ) (f : ℂ → EvR I) : Prop := ∃ g : ℂ → EvR I, HolE g ∧ ∀ t, f t = t ^ n • g t

theorem HolE.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → EvR I}
    (hf : HolE f) (h : ∀ e, g e = f e) : HolE g :=
  Hol.congr hf fun e => congrArg _ (h e)

theorem OrdE.hol {n : ℕ} {f : ℂ → EvR I} (h : OrdE n f) : HolE f := by
  obtain ⟨g, hg, e⟩ := h
  exact HolE.congr (HolE.smul (differentiable_id.pow n) hg) e

theorem OrdE.of_hol {f : ℂ → EvR I} (h : HolE f) : OrdE 0 f := ⟨f, h, fun t => by simp⟩

theorem OrdE.zero (n : ℕ) : OrdE n (fun _ => (0 : EvR I)) :=
  ⟨fun _ => 0, HolE.const _, by simp⟩

theorem OrdE.congr {n : ℕ} {f g : ℂ → EvR I} (h : OrdE n f) (e : ∀ t, g t = f t) : OrdE n g := by
  obtain ⟨g', hg, e'⟩ := h
  exact ⟨g', hg, fun t => by beta_reduce; rw [e, e']⟩

theorem OrdE.add {n : ℕ} {f g : ℂ → EvR I} (h1 : OrdE n f) (h2 : OrdE n g) :
    OrdE n (fun t => f t + g t) := by
  obtain ⟨g1, hg1, e1⟩ := h1
  obtain ⟨g2, hg2, e2⟩ := h2
  exact ⟨fun t => g1 t + g2 t, hg1.add hg2, fun t => by beta_reduce; rw [e1, e2, smul_add]⟩

theorem OrdE.neg {n : ℕ} {f : ℂ → EvR I} (h : OrdE n f) : OrdE n (fun t => -f t) := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun t => -g t, hg.neg, fun t => by beta_reduce; rw [e, smul_neg]⟩

theorem OrdE.sub {n : ℕ} {f g : ℂ → EvR I} (h1 : OrdE n f) (h2 : OrdE n g) :
    OrdE n (fun t => f t - g t) := by
  simpa [sub_eq_add_neg] using h1.add h2.neg

theorem OrdE.mul {m n : ℕ} {f g : ℂ → EvR I} (h1 : OrdE m f) (h2 : OrdE n g) :
    OrdE (m + n) (fun t => f t * g t) := by
  obtain ⟨g1, hg1, e1⟩ := h1
  obtain ⟨g2, hg2, e2⟩ := h2
  exact ⟨fun t => g1 t * g2 t, hg1.mul hg2, fun t => by
    beta_reduce; rw [e1, e2, smul_mul_smul_comm, pow_add]⟩

theorem OrdE.smul {m n : ℕ} {c : ℂ → ℂ} {f : ℂ → EvR I} (hc : OrdS m c) (h : OrdE n f) :
    OrdE (m + n) (fun t => c t • f t) := by
  obtain ⟨h1, hh1, e1⟩ := hc
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun t => h1 t • g t, HolE.smul hh1 hg, fun t => by
    beta_reduce; rw [e1, e, smul_smul, smul_smul, pow_add]; ring_nf⟩

theorem OrdE.smul_const {n : ℕ} (c : ℂ) {f : ℂ → EvR I} (h : OrdE n f) :
    OrdE n (fun t => c • f t) := by
  simpa using OrdE.smul (OrdS.of_differentiable (differentiable_const c)) h

theorem OrdE.mono {m n : ℕ} (hmn : m ≤ n) {f : ℂ → EvR I} (h : OrdE n f) : OrdE m f := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun t => t ^ (n - m) • g t, HolE.smul (differentiable_id.pow _) hg, fun t => ?_⟩
  rw [e, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]

theorem OrdE.map {J : Type*} [DecidableEq J] [Fintype J] {n : ℕ} {f : ℂ → EvR I} (h : OrdE n f)
    (T : EvR I →ₗ[ℂ] EvR J) : OrdE n (fun t => T (f t)) := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun t => T (g t), hg.map T, fun t => by beta_reduce; rw [e, map_smul]⟩

theorem OrdE.sum {ι : Type*} (s : Finset ι) {n : ℕ} {f : ι → ℂ → EvR I}
    (h : ∀ i ∈ s, OrdE n (f i)) : OrdE n (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OrdE.zero n
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem OrdE.prod {ι : Type*} (s : Finset ι) {f : ι → ℂ → EvR I}
    (h : ∀ i ∈ s, OrdE 1 (f i)) : OrdE s.card (fun t => ∏ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OrdE.of_hol (HolE.const (1 : EvR I))
  | insert a s ha ih =>
    simp only [prod_insert ha, card_insert_of_notMem ha]
    rw [add_comm]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem OrdE.const_pow (n : ℕ) (F : EvR I) : OrdE n (fun t => t ^ n • F) :=
  ⟨fun _ => F, HolE.const _, fun _ => rfl⟩

end Elements

end

end Step2
