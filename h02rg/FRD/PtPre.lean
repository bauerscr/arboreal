import FRD.PtFourier
import FRD.PtCot
import FRD.PtAverage

/-!
# The pre-family `P⁰_t`

`Q_t(u) = ∑_{|n| ≤ ⌊t⌋} f(-n/t) T_n(1 - u)`, so that `Q_t(1 - cos 2πx) = ∑_k t ψ(t(x + k))` by
Poisson summation, and `P⁰_t = Q_t / (c t) + A 1_{[1,2]}(t)` for `t ≥ 1`, `P⁰_t = 0` for `t < 1`.
-/

namespace FRD.PtF

open MeasureTheory Set Filter Topology Real Polynomial

/-- The polynomial `Q_t`. -/
noncomputable def Q (t : ℝ) : ℝ[X] :=
  ∑ n ∈ Finset.Icc (-(⌊t⌋₊ : ℤ)) ⌊t⌋₊, C (f (-(n / t))) * (Chebyshev.T ℝ n).comp (1 - X)

lemma eval_Q (t v : ℝ) :
    (Q t).eval v = ∑ n ∈ Finset.Icc (-(⌊t⌋₊ : ℤ)) ⌊t⌋₊,
      f (-(n / t)) * (Chebyshev.T ℝ n).eval (1 - v) := by
  simp [Q, eval_finsetSum, eval_comp]

lemma natDegree_Q (t : ℝ) : (Q t).natDegree ≤ ⌊t⌋₊ := by
  unfold Q
  apply natDegree_sum_le_of_forall_le
  intro n hn
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_comp_le.trans ?_
  have h1 : (1 - X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    simp
  rw [Chebyshev.natDegree_T]
  rw [Finset.mem_Icc] at hn
  calc n.natAbs * (1 - X : ℝ[X]).natDegree ≤ n.natAbs * 1 := Nat.mul_le_mul_left _ h1
    _ ≤ ⌊t⌋₊ := by rw [mul_one]; omega

lemma eval_Q_cos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (Q t).eval (1 - Real.cos (2 * π * x)) = ∑' k : ℤ, t * ψ (t * (x + k)) := by
  rw [poisson ht, eval_Q]
  apply Finset.sum_congr rfl
  intro n _
  rw [sub_sub_cancel, Chebyshev.T_real_cos]
  congr 2
  ring

lemma eval_Q_of_lt_one {t : ℝ} (ht : t < 1) (v : ℝ) : (Q t).eval v = f 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  rw [eval_Q, this]
  simp

/-- The angle variable `x = arccos(1 - u) / 2π ∈ [0, 1/2]`. -/
noncomputable def xu (u : ℝ) : ℝ := Real.arccos (1 - u) / (2 * π)

lemma cos_xu {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) : 1 - Real.cos (2 * π * xu u) = u := by
  have : 2 * π * xu u = Real.arccos (1 - u) := by
    rw [xu]; field_simp
  rw [this, Real.cos_arccos (by linarith [hu.2]) (by linarith [hu.1])]
  ring

lemma xu_nonneg (u : ℝ) : 0 ≤ xu u := by
  unfold xu; have := Real.arccos_nonneg (1 - u); positivity

lemma xu_le (u : ℝ) : xu u ≤ 1 / 2 := by
  unfold xu
  rw [div_le_iff₀ (by positivity)]
  have := Real.arccos_le_pi (1 - u)
  linarith

lemma xu_pos {u : ℝ} (hu : 0 < u) : 0 < xu u := by
  unfold xu
  have : 0 < Real.arccos (1 - u) := Real.arccos_pos.mpr (by linarith)
  positivity

lemma eval_Q_eq {t : ℝ} (ht : 0 < t) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) :
    (Q t).eval u = ∑' k : ℤ, t * ψ (t * (xu u + k)) := by
  conv_lhs => rw [← cos_xu hu]
  exact eval_Q_cos ht _

lemma eval_Q_nonneg {t : ℝ} (ht : 0 < t) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) :
    0 ≤ (Q t).eval u := by
  rw [eval_Q_eq ht hu]
  exact tsum_nonneg fun k => mul_nonneg ht.le (ψ_nonneg _)

/-- Auxiliary: the finite sum with a given cutoff `N`. -/
noncomputable def QN (u : ℝ) (p : ℝ × ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (-(p.2 : ℤ)) p.2, f (-(n / p.1)) * (Chebyshev.T ℝ n).eval (1 - u)

lemma measurable_QN (u : ℝ) : Measurable (QN u) := by
  apply measurable_from_prod_countable_left
  intro N
  unfold QN
  simp only
  refine Finset.measurable_sum (M := ℝ) _ (fun n _ => ?_)
  refine Measurable.mul_const ?_ _
  exact f_continuous.measurable.comp (measurable_const.div measurable_id).neg

lemma measurable_eval_Q (u : ℝ) : Measurable fun t => (Q t).eval u := by
  have : (fun t => (Q t).eval u) = QN u ∘ fun t => (t, ⌊t⌋₊) := by
    funext t; simp only [Function.comp, QN, eval_Q]
  rw [this]
  exact (measurable_QN u).comp (measurable_id.prodMk Nat.measurable_floor)

/-! ### The integral `∫_0^∞ Q_t(u) dt` -/

/-- `c₀ = ∫_0^∞ s ψ(s) ds`. -/
noncomputable def c0 : ℝ := ∫ s in Ioi 0, s * ψ s

lemma integrableOn_c0 : IntegrableOn (fun s => s * ψ s) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := ψ_decay' 3
  have hg : Integrable fun s : ℝ => C * (1 + ‖s‖) ^ (-(2 : ℝ)) :=
    (integrable_one_add_norm (by simp)).const_mul C
  refine (hg.mono' ?_ ?_).integrableOn
  · exact (continuous_id.mul ψ_continuous).aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ψ_nonneg s), Real.norm_eq_abs,
      Real.rpow_neg (by positivity), Real.rpow_two]
    have h1 := hC s
    have hs : 0 < 1 + |s| := by positivity
    calc |s| * ψ s ≤ (1 + |s|) * (C / (1 + |s|) ^ 3) := by
          gcongr
          · exact ψ_nonneg s
          · linarith
      _ = C * ((1 + |s|) ^ 2)⁻¹ := by field_simp

lemma c0_pos : 0 < c0 := by
  have hev : ∀ᶠ ξ in 𝓝 (0 : ℝ), 0 < ψ ξ :=
    ψ_continuous.continuousAt.eventually (lt_mem_nhds ψ_zero_pos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  unfold c0
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ integrableOn_c0]
  · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo 0 ε) ?_)
    · simp [hε]
    · intro s hs
      refine ⟨?_, hs.1⟩
      rw [Function.mem_support]
      apply (mul_pos hs.1 (hball _)).ne'
      rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
      exact hs.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (le_of_lt hs) (ψ_nonneg s)

lemma integral_scale {y : ℝ} (hy : y ≠ 0) : ∫ t in Ioi 0, t * ψ (t * y) = c0 / y ^ 2 := by
  have hya : 0 < |y| := abs_pos.mpr hy
  have e : ∀ t ∈ Ioi (0 : ℝ), t * ψ (t * y) = |y|⁻¹ * ((|y| * t) * ψ (|y| * t)) := by
    intro t ht
    rw [← ψ_abs (t * y), abs_mul, abs_of_pos (show (0 : ℝ) < t from ht), mul_comm t |y|]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_comp_mul_left_Ioi (fun s => s * ψ s) 0 hya, mul_zero, smul_eq_mul, ← c0,
    ← sq_abs y]
  field_simp

lemma int_add_ne_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (k : ℤ) : x + k ≠ 0 := by
  intro h
  have hk : (k : ℝ) = -x := by linarith
  have h1 : (k : ℝ) < 0 := by linarith
  have h2 : k < 0 := by exact_mod_cast h1
  have h3 : k ≤ -1 := by omega
  have h4 : (k : ℝ) ≤ -1 := by exact_mod_cast h3
  linarith

lemma integral_tsum_scale {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    ∫ t in Ioi 0, ∑' k : ℤ, t * ψ (t * (x + k)) = c0 * (π ^ 2 / Real.sin (π * x) ^ 2) := by
  have hS := hasSum_inv_add_int_sq hx0 (by linarith)
  have hint : ∀ k : ℤ, IntegrableOn (fun t => t * ψ (t * (x + k))) (Ioi 0) := by
    intro k
    apply Integrable.of_integral_ne_zero
    rw [integral_scale (int_add_ne_zero hx0 hx1 k)]
    have := int_add_ne_zero hx0 hx1 k
    have := c0_pos
    positivity
  rw [integral_tsum (fun k => (hint k).aestronglyMeasurable)]
  · simp_rw [integral_scale (int_add_ne_zero hx0 hx1 _), div_eq_mul_inv]
    rw [tsum_mul_left, hS.tsum_eq, div_eq_mul_inv]
  · have : ∀ k : ℤ, ∫⁻ t in Ioi 0, ‖t * ψ (t * (x + k))‖ₑ =
        ENNReal.ofReal (c0 / (x + k) ^ 2) := by
      intro k
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hint k),
        ← integral_scale (int_add_ne_zero hx0 hx1 k)]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg (le_of_lt ht) (ψ_nonneg _))
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro k; have := c0_pos; positivity
    · simpa [div_eq_mul_inv] using hS.summable.mul_left c0

lemma two_sin_sq (x : ℝ) : 2 * Real.sin (π * x) ^ 2 = 1 - Real.cos (2 * π * x) := by
  have h1 := Real.sin_sq (π * x)
  have h2 := Real.cos_sq (π * x)
  rw [h1, h2]
  have : 2 * (π * x) = 2 * π * x := by ring
  rw [this]
  ring

/-- The normalizing constant `c = 2 π² c₀`. -/
noncomputable def cc : ℝ := 2 * π ^ 2 * c0

lemma cc_pos : 0 < cc := by unfold cc; have := c0_pos; positivity

lemma integral_Q {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) :
    ∫ t in Ioi 0, (Q t).eval u = cc / u := by
  have hu' : u ∈ Icc (0 : ℝ) 2 := ⟨hu.1.le, hu.2⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => eval_Q_eq ht hu'),
    integral_tsum_scale (xu_pos hu.1) (xu_le u)]
  have h := two_sin_sq (xu u)
  rw [cos_xu hu'] at h
  have hsin : Real.sin (π * xu u) ^ 2 = u / 2 := by linarith
  rw [hsin, cc]
  have := hu.1
  field_simp

lemma integrableOn_Q {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) :
    IntegrableOn (fun t => (Q t).eval u) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_Q hu]
  have := cc_pos; have := hu.1
  positivity

/-! ### Decay estimates -/

lemma summable_b : Summable fun k : ℤ => ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually
    ((summable_one_div_int_pow.mpr one_lt_two).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hpos : 0 < (k : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [show 4 * (1 / (k : ℝ) ^ 2) = ((k : ℝ) ^ 2 / 4)⁻¹ by field_simp]
  apply inv_anti₀ (by positivity)
  have : (k : ℝ) ^ 2 / 4 = (|(k : ℝ)| / 2) ^ 2 := by rw [div_pow, sq_abs]; norm_num
  rw [this]
  have : 0 ≤ |(k : ℝ)| / 2 := by positivity
  nlinarith

lemma abs_add_int_ge {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (k : ℤ) :
    x ≤ |x + k| ∧ |(k : ℝ)| / 2 ≤ |x + k| := by
  rcases le_or_gt 0 k with hk | hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg hk']
    constructor <;> linarith [hx.1]
  · have hk1 : k ≤ -1 := by omega
    have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
    rw [abs_of_neg (by linarith [hx.2]), abs_of_neg (by linarith)]
    constructor <;> linarith [hx.2]

lemma sum_bound (M : ℕ) : ∃ D, 0 ≤ D ∧ ∀ t, 1 ≤ t → ∀ x ∈ Icc (0 : ℝ) (1 / 2),
    Summable (fun k : ℤ => ψ (t * (x + k))) ∧
    ∑' k : ℤ, ψ (t * (x + k)) ≤ D / (1 + t * x) ^ M := by
  obtain ⟨C, hC0, hC⟩ := ψ_decay' (M + 2)
  set B := ∑' k : ℤ, ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹
  have hB : 0 ≤ B := tsum_nonneg fun k => by positivity
  refine ⟨C * B, mul_nonneg hC0 hB, fun t ht x hx => ?_⟩
  have hx0 := hx.1
  have hterm : ∀ k : ℤ, ψ (t * (x + k)) ≤
      C / (1 + t * x) ^ M * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
    intro k
    refine (hC _).trans ?_
    obtain ⟨h1, h2⟩ := abs_add_int_ge hx k
    have ha : |t * (x + k)| = t * |x + k| := by rw [abs_mul, abs_of_pos (by linarith)]
    have e1 : 1 + t * x ≤ 1 + |t * (x + k)| := by
      rw [ha]; gcongr
    have e2 : 1 + |(k : ℝ)| / 2 ≤ 1 + |t * (x + k)| := by
      rw [ha]; nlinarith [abs_nonneg (x + k)]
    have hp : 0 < 1 + t * x := by positivity
    have key : (1 + t * x) ^ M * (1 + |(k : ℝ)| / 2) ^ 2 ≤ (1 + |t * (x + k)|) ^ (M + 2) := by
      calc (1 + t * x) ^ M * (1 + |(k : ℝ)| / 2) ^ 2
          ≤ (1 + |t * (x + k)|) ^ M * (1 + |t * (x + k)|) ^ 2 := by gcongr
        _ = (1 + |t * (x + k)|) ^ (M + 2) := by rw [pow_add]
    calc C / (1 + |t * (x + k)|) ^ (M + 2)
        ≤ C / ((1 + t * x) ^ M * (1 + |(k : ℝ)| / 2) ^ 2) :=
          div_le_div_of_nonneg_left hC0 (by positivity) key
      _ = C / (1 + t * x) ^ M * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv (C / _)]
  have hsb : Summable fun k : ℤ => C / (1 + t * x) ^ M * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ :=
    summable_b.mul_left _
  have hsum : Summable fun k : ℤ => ψ (t * (x + k)) :=
    hsb.of_nonneg_of_le (fun k => ψ_nonneg _) hterm
  refine ⟨hsum, (hsum.tsum_le_tsum hterm hsb).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left]
  ring

lemma one_add_le {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    1 + t ^ 2 * (1 - Real.cos (2 * π * x)) ≤ 2 * π ^ 2 * (1 + t * x) ^ 2 := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * π * x)
  have h2 : t ^ 2 * (1 - Real.cos (2 * π * x)) ≤ t ^ 2 * (2 * π ^ 2 * x ^ 2) := by
    gcongr; nlinarith
  have h3 := Real.pi_gt_three
  have htx : 0 ≤ t * x := mul_nonneg ht hx
  nlinarith

/-! ### The pre-family -/

/-- The constant on `[1, 2]`, compensating for `∫_0^1 Q_t dt = f(0)`. -/
noncomputable def AA : ℝ := 2 / 3 * f 0 / cc

lemma AA_pos : 0 < AA := by unfold AA; have := f_zero_pos; have := cc_pos; positivity

/-- The pre-family `P⁰_t`. -/
noncomputable def P0 (t : ℝ) : ℝ[X] :=
  if t < 1 then 0 else C (1 / (cc * t)) * Q t + (if t ≤ 2 then C AA else 0)

lemma eval_P0 {t : ℝ} (ht : 1 ≤ t) (u : ℝ) :
    (P0 t).eval u = (Q t).eval u / (cc * t) + (if t ≤ 2 then AA else 0) := by
  rw [P0, if_neg (not_lt.mpr ht)]
  split_ifs <;> simp [div_eq_inv_mul]

lemma eval_P0_lt {t : ℝ} (ht : t < 1) (u : ℝ) : (P0 t).eval u = 0 := by
  rw [P0, if_pos ht, eval_zero]

lemma natDegree_P0 (t : ℝ) (ht : 0 < t) : ((P0 t).natDegree : ℝ) ≤ t := by
  unfold P0
  split_ifs with h1 h2
  · simp [ht.le]
  · refine le_trans ?_ (Nat.floor_le ht.le)
    norm_cast
    refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (natDegree_C_mul_le _ _).trans (natDegree_Q t)
  · refine le_trans ?_ (Nat.floor_le ht.le)
    norm_cast
    rw [add_zero]
    exact (natDegree_C_mul_le _ _).trans (natDegree_Q t)

lemma nonneg_P0 (t : ℝ) (ht : 0 < t) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2) :
    0 ≤ (P0 t).eval u := by
  rcases lt_or_ge t 1 with h | h
  · rw [eval_P0_lt h]
  · rw [eval_P0 h]
    have := eval_Q_nonneg ht hu
    have := cc_pos
    have := AA_pos
    have : 0 ≤ (if t ≤ 2 then AA else 0) := by split_ifs <;> linarith
    positivity

lemma ge_AA_P0 (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2) :
    AA ≤ (P0 t).eval u := by
  rw [eval_P0 ht.1, if_pos ht.2]
  have := eval_Q_nonneg (by linarith [ht.1]) hu
  have := cc_pos
  have : 0 ≤ (Q t).eval u / (cc * t) := by have := ht.1; positivity
  linarith

lemma measurable_P0 (u : ℝ) : Measurable fun t => (P0 t).eval u := by
  have : (fun t => (P0 t).eval u) = fun t => if t < 1 then 0 else
      (Q t).eval u / (cc * t) + (if t ≤ 2 then AA else 0) := by
    funext t
    by_cases h : t < 1
    · rw [if_pos h]; exact eval_P0_lt h u
    · rw [if_neg h]; exact eval_P0 (not_lt.mp h) u
  rw [this]
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  refine Measurable.add ?_ (Measurable.ite measurableSet_Iic measurable_const measurable_const)
  exact (measurable_eval_Q u).div (measurable_const.mul measurable_id)

lemma bound_P0 (s : ℝ) (hs : 0 ≤ s) : ∃ K : ℝ, ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2,
    (P0 t).eval u ≤ K * (1 + t ^ 2 * u) ^ (-s) := by
  set m := ⌈s⌉₊
  obtain ⟨D, hD0, hD⟩ := sum_bound (2 * m)
  have hcc := cc_pos
  have hAA := AA_pos
  refine ⟨D / cc * (2 * π ^ 2) ^ m + AA * 9 ^ s, fun t ht u hu => ?_⟩
  have hK : 0 ≤ D / cc * (2 * π ^ 2) ^ m + AA * 9 ^ s := by positivity
  have hpos : 0 < 1 + t ^ 2 * u := by have := hu.1; positivity
  have hrpow : 0 ≤ (1 + t ^ 2 * u) ^ (-s) := Real.rpow_nonneg hpos.le _
  rcases lt_or_ge t 1 with h1 | h1
  · rw [eval_P0_lt h1]; positivity
  rw [eval_P0 h1]
  set x := xu u
  have hx : x ∈ Icc (0 : ℝ) (1 / 2) := ⟨xu_nonneg u, xu_le u⟩
  obtain ⟨hsum, hle⟩ := hD t h1 x hx
  have hux : 1 - Real.cos (2 * π * x) = u := cos_xu hu
  -- the main term
  have hmain : (Q t).eval u / (cc * t) ≤ D / cc * (2 * π ^ 2) ^ m * (1 + t ^ 2 * u) ^ (-s) := by
    rw [eval_Q_eq ht hu, tsum_mul_left]
    have e : (t * ∑' k : ℤ, ψ (t * (x + k))) / (cc * t) = (∑' k : ℤ, ψ (t * (x + k))) / cc := by
      rw [mul_comm cc t, mul_div_mul_left _ _ ht.ne']
    rw [e]
    have hp : 0 < 1 + t * x := by have := hx.1; positivity
    have h2 : 1 + t ^ 2 * u ≤ 2 * π ^ 2 * (1 + t * x) ^ 2 := by
      rw [← hux]; exact one_add_le ht.le hx.1
    have h3 : ((1 + t * x) ^ (2 * m))⁻¹ ≤ (2 * π ^ 2) ^ m * ((1 + t ^ 2 * u) ^ m)⁻¹ := by
      have h3' : (1 + t ^ 2 * u) ^ m ≤ ((2 * π ^ 2) * (1 + t * x) ^ 2) ^ m :=
        pow_le_pow_left₀ hpos.le h2 m
      rw [pow_mul, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
        inv_mul_le_iff₀ (by positivity), ← mul_pow]
      exact h3'.trans (le_of_eq (by ring))
    have h4 : ((1 + t ^ 2 * u) ^ m)⁻¹ ≤ (1 + t ^ 2 * u) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hpos.le]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [mul_nonneg (sq_nonneg t) hu.1])
      simp only [neg_le_neg_iff, m]
      exact Nat.le_ceil s
    calc (∑' k : ℤ, ψ (t * (x + k))) / cc ≤ D / (1 + t * x) ^ (2 * m) / cc := by gcongr
      _ = D / cc * ((1 + t * x) ^ (2 * m))⁻¹ := by field_simp
      _ ≤ D / cc * ((2 * π ^ 2) ^ m * ((1 + t ^ 2 * u) ^ m)⁻¹) := by gcongr
      _ ≤ D / cc * ((2 * π ^ 2) ^ m * (1 + t ^ 2 * u) ^ (-s)) := by gcongr
      _ = D / cc * (2 * π ^ 2) ^ m * (1 + t ^ 2 * u) ^ (-s) := by ring
  have hA : (if t ≤ 2 then AA else 0) ≤ AA * 9 ^ s * (1 + t ^ 2 * u) ^ (-s) := by
    split_ifs with h2
    · have h9 : 1 + t ^ 2 * u ≤ 9 := by
        have : t ^ 2 ≤ 4 := by nlinarith
        nlinarith [hu.1, hu.2]
      have := Real.rpow_le_rpow_of_nonpos hpos h9 (by linarith : -s ≤ 0)
      have h99 : (9 : ℝ) ^ s * (9 : ℝ) ^ (-s) = 1 := by
        rw [Real.rpow_neg (by norm_num), mul_inv_cancel₀ (by positivity)]
      have h9s : 0 ≤ (9 : ℝ) ^ s := by positivity
      calc AA = AA * ((9 : ℝ) ^ s * (9 : ℝ) ^ (-s)) := by rw [h99, mul_one]
        _ ≤ AA * ((9 : ℝ) ^ s * (1 + t ^ 2 * u) ^ (-s)) := by gcongr
        _ = AA * 9 ^ s * (1 + t ^ 2 * u) ^ (-s) := by ring
    · positivity
  calc (Q t).eval u / (cc * t) + (if t ≤ 2 then AA else 0)
      ≤ D / cc * (2 * π ^ 2) ^ m * (1 + t ^ 2 * u) ^ (-s) + AA * 9 ^ s * (1 + t ^ 2 * u) ^ (-s) :=
        add_le_add hmain hA
    _ = (D / cc * (2 * π ^ 2) ^ m + AA * 9 ^ s) * (1 + t ^ 2 * u) ^ (-s) := by ring

lemma integral_P0 {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) :
    ∫ t in Ioi 0, t * (P0 t).eval u = 1 / u := by
  have hcc := cc_pos
  have e : ∀ t ∈ Ioi (0 : ℝ), t * (P0 t).eval u = (Q t).eval u / cc -
      (Ioo (0 : ℝ) 1).indicator (fun _ => f 0 / cc) t +
      (Icc (1 : ℝ) 2).indicator (fun t => t * AA) t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rcases lt_or_ge t 1 with h1 | h1
    · rw [eval_P0_lt h1, eval_Q_of_lt_one h1, indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht', h1⟩),
        indicator_of_notMem (fun h => by linarith [h.1])]
      ring
    · rw [eval_P0 h1, indicator_of_notMem (fun h => by linarith [h.2])]
      split_ifs with h2
      · rw [indicator_of_mem (show t ∈ Icc (1 : ℝ) 2 from ⟨h1, h2⟩)]; field_simp; ring
      · rw [indicator_of_notMem (fun h => h2 h.2)]; field_simp; ring
  have i1 : IntegrableOn (fun t => (Q t).eval u / cc) (Ioi 0) := (integrableOn_Q hu).div_const _
  have i2 : IntegrableOn ((Ioo (0 : ℝ) 1).indicator (fun _ => f 0 / cc)) (Ioi 0) := by
    apply Integrable.integrableOn
    apply (integrable_indicator_iff measurableSet_Ioo).mpr
    exact integrableOn_const (by simp)
  have i3 : IntegrableOn ((Icc (1 : ℝ) 2).indicator (fun t => t * AA)) (Ioi 0) := by
    apply Integrable.integrableOn
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (continuous_id.mul continuous_const).integrableOn_Icc
  have i12 : IntegrableOn (fun t => (Q t).eval u / cc -
      (Ioo (0 : ℝ) 1).indicator (fun _ => f 0 / cc) t) (Ioi 0) := i1.sub i2
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add i12 i3,
    integral_sub i1 i2, integral_div, integral_Q hu,
    setIntegral_indicator measurableSet_Ioo, setIntegral_indicator measurableSet_Icc,
    inter_eq_right.mpr Ioo_subset_Ioi_self,
    inter_eq_right.mpr (show Icc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) from
      fun t ht => lt_of_lt_of_le one_pos ht.1),
    setIntegral_const, integral_mul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), integral_id]
  simp only [Measure.real, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal zero_le_one,
    smul_eq_mul, one_mul, AA]
  have := hu.1
  field_simp
  ring

/-- The pre-family. -/
noncomputable def prePt : PrePtFamily where
  P := P0
  eq_zero t ht := by rw [P0, if_pos ht]
  natDegree_le := natDegree_P0
  nonneg := nonneg_P0
  A := AA
  A_pos := AA_pos
  ge_A := ge_AA_P0
  bound := bound_P0
  measurable := measurable_P0
  integral_eq _ hu := integral_P0 hu

end FRD.PtF
