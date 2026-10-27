module

public import Mathlib

/-!
# The standard Gaussian on `ι → ℝ`

One-dimensional moments of `exp (-x²/2)` and their product versions over `ι → ℝ`.
-/

open MeasureTheory Real

namespace ArborealDecay.Gaussian

public section

/-- The one-dimensional standard Gaussian weight. -/
@[expose] noncomputable def w1 (x : ℝ) : ℝ := Real.exp (-(1 / 2) * x ^ 2)

theorem w1_pos (x : ℝ) : 0 < w1 x := Real.exp_pos _

theorem integrable_w1 : Integrable w1 := integrable_exp_neg_mul_sq (by norm_num)

theorem integrable_pow_mul_w1 {n : ℕ} (hn : n ≤ 2) :
    Integrable fun x : ℝ => x ^ n * w1 x := by
  interval_cases n
  · simpa using integrable_w1
  · simpa [w1] using integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  · have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2) (by norm_num)
    simpa [w1, Real.rpow_two] using this

theorem integral_w1 : ∫ x, w1 x = Real.sqrt (2 * π) := by
  have := integral_gaussian (1 / 2)
  simp only [w1]
  rw [this]
  congr 1
  field_simp

theorem integral_id_mul_w1 : ∫ x, x * w1 x = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => x * w1 x) (volume : Measure ℝ)
  have h2 : ∫ x : ℝ, (-x) * w1 (-x) = -∫ x, x * w1 x := by
    rw [← integral_neg]
    congr 1; ext x; simp [w1]
  linarith

theorem integral_sq_mul_w1 : ∫ x, x ^ 2 * w1 x = Real.sqrt (2 * π) := by
  have hv : ∀ x ∈ tsupport (fun x : ℝ => x), HasDerivAt (fun x : ℝ => -w1 x) (x * w1 x) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(1 / 2) * x ^ 2) (-(1 / 2) * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-(1 / 2) : ℝ))
    have h2 : HasDerivAt (fun x : ℝ => -w1 x) _ x := h1.exp.neg
    exact h2.congr_deriv (by simp [w1]; ring)
  have i1 : Integrable ((fun x : ℝ => x) * fun x => x * w1 x) := by
    convert integrable_pow_mul_w1 (n := 2) le_rfl using 1; ext x; simp; ring
  have i2 : Integrable ((fun _ : ℝ => (1 : ℝ)) * fun x => -w1 x) := by
    convert integrable_w1.neg using 1; ext x; simp
  have i3 : Integrable ((fun x : ℝ => x) * fun x => -w1 x) := by
    convert (integrable_pow_mul_w1 (n := 1) (by norm_num)).neg using 1; ext x; simp
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x : ℝ => x)
    (v := fun x : ℝ => -w1 x) (u' := fun _ => (1 : ℝ)) (v' := fun x => x * w1 x)
    (fun x _ => hasDerivAt_id x) hv i1 i2 i3
  simp only [one_mul, integral_neg, neg_neg] at key
  rw [← integral_w1, ← key]
  congr 1; ext x; ring

/-- Integrability of a monomial times the standard Gaussian on `ι → ℝ`, product form. -/
theorem integrable_prod_pow_w1 {ι : Type*} [Fintype ι] {n : ι → ℕ} (hn : ∀ i, n i ≤ 2) :
    Integrable fun u : ι → ℝ => ∏ i, (u i ^ n i * w1 (u i)) :=
  Integrable.fintype_prod (f := fun i (x : ℝ) => x ^ n i * w1 x) fun i => integrable_pow_mul_w1 (hn i)

theorem integral_prod_pow_w1 {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    ∫ u : ι → ℝ, ∏ i, (u i ^ n i * w1 (u i)) = ∏ i, ∫ x : ℝ, x ^ n i * w1 x :=
  integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ))
    (fun i (x : ℝ) => x ^ n i * w1 x)

/-- The standard Gaussian weight on `ι → ℝ`. -/
@[expose] noncomputable def stdWeight {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * ∑ i, u i ^ 2)

theorem stdWeight_eq_prod {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    stdWeight u = ∏ i, w1 (u i) := by
  simp only [stdWeight, w1, ← Real.exp_sum, Finset.mul_sum]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem mono_eq (k l : ι) (u : ι → ℝ) :
    u k * u l * stdWeight u
      = ∏ i, (u i ^ (Pi.single k 1 + Pi.single l 1 : ι → ℕ) i * w1 (u i)) := by
  rw [stdWeight_eq_prod, Finset.prod_mul_distrib]
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, Pi.single_apply, pow_ite]
  simp [Finset.prod_ite_eq']

omit [Fintype ι] in
private theorem single_le (k l : ι) (i : ι) :
    (Pi.single k 1 + Pi.single l 1 : ι → ℕ) i ≤ 2 := by
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> norm_num

omit [DecidableEq ι] in
theorem integrable_stdWeight : Integrable (stdWeight : (ι → ℝ) → ℝ) := by
  have := integrable_prod_pow_w1 (ι := ι) (n := fun _ => 0) (fun _ => by norm_num)
  simp only [pow_zero, one_mul] at this
  have e : (stdWeight : (ι → ℝ) → ℝ) = fun u => ∏ i, w1 (u i) := funext stdWeight_eq_prod
  rw [e]; exact this

theorem integrable_coord_mul_stdWeight (k : ι) :
    Integrable fun u : ι → ℝ => u k * stdWeight u := by
  have := integrable_prod_pow_w1 (ι := ι) (n := Pi.single k 1) (fun i => by
    simp only [Pi.single_apply]; split_ifs <;> norm_num)
  convert this using 1
  ext u
  rw [stdWeight_eq_prod, Finset.prod_mul_distrib]
  congr 1
  simp [Pi.single_apply, pow_ite, Finset.prod_ite_eq']

theorem integrable_coord_mul_coord_mul_stdWeight (k l : ι) :
    Integrable fun u : ι → ℝ => u k * u l * stdWeight u := by
  have := integrable_prod_pow_w1 (ι := ι) (n := Pi.single k 1 + Pi.single l 1) (single_le k l)
  simpa only [mono_eq] using this

omit [DecidableEq ι] in
theorem integral_stdWeight :
    ∫ u : ι → ℝ, stdWeight u = Real.sqrt (2 * π) ^ Fintype.card ι := by
  have := integral_prod_pow_w1 (ι := ι) (fun _ => 0)
  simpa [stdWeight_eq_prod, integral_w1] using this

theorem integral_coord_mul_coord_mul_stdWeight (k l : ι) :
    ∫ u : ι → ℝ, u k * u l * stdWeight u
      = if k = l then Real.sqrt (2 * π) ^ Fintype.card ι else 0 := by
  simp only [mono_eq]
  rw [integral_prod_pow_w1]
  by_cases h : k = l
  · subst h
    simp only [ite_true]
    have : ∀ i, ∫ x : ℝ, x ^ (Pi.single k 1 + Pi.single k 1 : ι → ℕ) i * w1 x
        = Real.sqrt (2 * π) := by
      intro i
      by_cases hi : i = k
      · subst hi; simpa [Pi.single_apply] using integral_sq_mul_w1
      · simpa [Pi.single_apply, hi] using integral_w1
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const, Finset.card_univ]
  · simp only [h, ite_false]
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    simp [h, integral_id_mul_w1]

end

end ArborealDecay.Gaussian
