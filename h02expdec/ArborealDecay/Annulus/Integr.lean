module

public import ArborealDecay.Annulus.RootChange

/-!
# Integrability and linearity of the pinned expectation

* `integrable_exp_lin`: `e^{∑_v λ_v t_v}` is integrable against the density
  (connected `w`, `a ≥ 0`).
* `expect_add`, `expect_sum`, `expect_const_mul`, `expect_const`, `expect_mono`: the elementary
  properties of `TLaw.expect`.
-/

open Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem continuous_ext_apply (ρ v : V) : Continuous fun τ : {i // i ≠ ρ} → ℝ => TLaw.ext ρ τ v :=
  (continuous_apply v).comp (continuous_ext ρ)

/-- Exponential moments: `e^{∑_v λ_v t_v} · density` is integrable. -/
theorem integrable_exp_lin {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) {a : ℝ} (ha : 0 ≤ a) (lam : V → ℝ) :
    Integrable (fun τ => exp (∑ v, lam v * TLaw.ext ρ τ v) * density w ρ a τ) := by
  have e : ∀ τ : {i // i ≠ ρ} → ℝ, ∑ v, lam v * TLaw.ext ρ τ v =
      ∑ i : {i // i ≠ ρ}, lam i * τ i := fun τ => by
    rw [← sum_ne_eq_of_root ρ (fun v => lam v * TLaw.ext ρ τ v) (by simp)]
    simp
  simp_rw [e]
  have hfin := lintegral_exp_mul_density_lt_top hW hconn ρ ha (fun i => lam i)
  have hc : Continuous fun τ : {i // i ≠ ρ} → ℝ =>
      exp (∑ i : {i // i ≠ ρ}, lam i * τ i) * density w ρ a τ :=
    (continuous_exp.comp (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_apply i))).mul (continuous_density hW hconn ρ a)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun τ =>
    mul_nonneg (exp_pos _).le (density_pos hW hconn ρ a τ).le)]
  exact hfin

theorem integrable_density {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) {a : ℝ} (ha : 0 ≤ a) : Integrable (density w ρ a) := by
  have := integrable_exp_lin hW hconn ρ ha 0
  simpa using this

/-- `e^{c t_q}` (in particular `U_q^2 = e^{2 t_q}`). -/
theorem integrable_exp_single {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) (q : V) :
    Integrable (fun τ => exp (c * TLaw.ext ρ τ q) * density w ρ a τ) := by
  have := integrable_exp_lin hW hconn ρ ha (Pi.single q c)
  simpa [Pi.single_apply] using this

/-- `e^{t_p + t_q}` (i.e. `U_p U_q`). -/
theorem integrable_exp_pair {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) {a : ℝ} (ha : 0 ≤ a) (p q : V) :
    Integrable (fun τ => exp (TLaw.ext ρ τ p + TLaw.ext ρ τ q) * density w ρ a τ) := by
  have := integrable_exp_lin hW hconn ρ ha (Pi.single p 1 + Pi.single q 1)
  simpa [Pi.single_apply, add_mul, Finset.sum_add_distrib] using this

/-! ### Linearity of `expect` -/

theorem expect_add {w : V → V → ℝ} {ρ : V} {a : ℝ} {f g : ({i // i ≠ ρ} → ℝ) → ℝ}
    (hf : Integrable (fun τ => f τ * density w ρ a τ))
    (hg : Integrable (fun τ => g τ * density w ρ a τ)) :
    expect w ρ a (fun τ => f τ + g τ) = expect w ρ a f + expect w ρ a g := by
  unfold expect
  simp_rw [add_mul]
  rw [integral_add hf hg]; ring

theorem expect_sum {ι : Type*} (s : Finset ι) {w : V → V → ℝ} {ρ : V} {a : ℝ}
    {f : ι → ({i // i ≠ ρ} → ℝ) → ℝ}
    (hf : ∀ i ∈ s, Integrable (fun τ => f i τ * density w ρ a τ)) :
    expect w ρ a (fun τ => ∑ i ∈ s, f i τ) = ∑ i ∈ s, expect w ρ a (f i) := by
  unfold expect
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum s hf, Finset.mul_sum]

theorem expect_const_mul (w : V → V → ℝ) (ρ : V) (a c : ℝ) (f : ({i // i ≠ ρ} → ℝ) → ℝ) :
    expect w ρ a (fun τ => c * f τ) = c * expect w ρ a f := by
  unfold expect
  simp_rw [mul_assoc]
  rw [integral_const_mul]; ring

theorem expect_const {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) : expect w ρ a (fun _ => c) = c := by
  have h1 : expect w ρ a (fun _ => (1 : ℝ)) = 1 := by
    have := expect_exp_root_change hW hconn ρ ρ a
    simp only [TLaw.ext_root, mul_zero, exp_zero] at this
    rw [this]
    exact div_self (ENNReal.toReal_pos (Z_pos hW hconn ρ _).ne' (Z_lt_top hW hconn ρ ha).ne).ne'
  have := expect_const_mul w ρ a c (fun _ => (1 : ℝ))
  simp only [mul_one] at this
  rw [this, h1, mul_one]

theorem expect_mono {w : V → V → ℝ} {ρ : V} {a : ℝ} {f g : ({i // i ≠ ρ} → ℝ) → ℝ}
    (hd : ∀ τ, 0 ≤ density w ρ a τ)
    (hf : Integrable (fun τ => f τ * density w ρ a τ))
    (hg : Integrable (fun τ => g τ * density w ρ a τ)) (hfg : ∀ τ, f τ ≤ g τ) :
    expect w ρ a f ≤ expect w ρ a g := by
  unfold expect
  refine mul_le_mul_of_nonneg_left (integral_mono hf hg fun τ => ?_)
    (inv_nonneg.2 ENNReal.toReal_nonneg)
  exact mul_le_mul_of_nonneg_right (hfg τ) (hd τ)

/-- Domination: a measurable `0 ≤ f ≤ g` with `g · density` integrable is integrable. -/
theorem integrable_of_le {w : V → V → ℝ} {ρ : V} {a : ℝ} {f g : ({i // i ≠ ρ} → ℝ) → ℝ}
    (hd : ∀ τ, 0 ≤ density w ρ a τ) (hfm : Measurable f)
    (hg : Integrable (fun τ => g τ * density w ρ a τ)) (hf0 : ∀ τ, 0 ≤ f τ)
    (hfg : ∀ τ, f τ ≤ g τ) :
    Integrable (fun τ => f τ * density w ρ a τ) := by
  refine hg.mono (hfm.mul (measurable_density w ρ a)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 τ) (hd τ)),
    abs_of_nonneg (mul_nonneg ((hf0 τ).trans (hfg τ)) (hd τ))]
  exact mul_le_mul_of_nonneg_right (hfg τ) (hd τ)

end ArborealDecay.Annulus
