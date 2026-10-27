import Step2.D2.D2Profile

/-!
# The symbol `ê_T` of the concrete decomposition (`prop:d2`, (R1))

For `P = FRD.PtF.prePt.toPtFamily` (`Pc`), `u = û(p) ∈ (0, 2]` and `x = arccos(1 - u)/2π`:

* `tail_Pc`: `∫_T^∞ t P_t(u) dt = ∑_i ω_i G⁰(T/2^i, u)`, `G⁰(τ, u) = ∫_τ^∞ s P⁰_s(u) ds`;
* `abs_Gc_le`: `G⁰(τ, u) = c⁻¹ ∫_τ^∞ Q_s(u) ds + O(τ^{-2})` (the corrections from `s ≤ 2`);
* `integral_Q_Ioi`: `∫_τ^∞ Q_s(u) ds = ∑_k Ψ₁(τ|x + k|)/(x + k)²` (Poisson);
* `ehat_repr`: **the exact form of `ê_T`**:
  `|ê_T(p) - (1 - sinc²(πx) (1 - H(T x)))| ≤ C_rem u / T²`,
  with the profile `H` of `D2Profile` and `sinc(πx) = sin(πx)/(πx)`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF
open scoped Nat

/-- The concrete family `P_t` (not `FRD.stdPt`, which is a choice). -/
abbrev Pc : PtFamily := PtF.prePt.toPtFamily

theorem Pc_eval (t u : ℝ) :
    (Pc.P t).eval u = ∑' i, PrePtFamily.a i * (P0 (t / 2 ^ i)).eval u :=
  PtF.prePt.eval_avgP_eq_tsum t u

/-- `G⁰(τ, u) = ∫_τ^∞ s P⁰_s(u) ds`. -/
def G0 (τ u : ℝ) : ℝ := ∫ s in Ioi τ, s * (P0 s).eval u

theorem a_mul_four_pow (i : ℕ) : PrePtFamily.a i * 4 ^ i = om i := by
  simp only [PrePtFamily.a, om]
  have := PrePtFamily.W_pos
  field_simp

theorem integral_scaled_Ioi {u : ℝ} (T : ℝ) (i : ℕ) :
    ∫ t in Ioi T, t * (PrePtFamily.a i * (P0 (t / 2 ^ i)).eval u) = om i * G0 (T / 2 ^ i) u := by
  have h2 : (0 : ℝ) < (2 ^ i)⁻¹ := by positivity
  have := integral_comp_mul_left_Ioi (fun s => s * (P0 s).eval u) T h2
  have e : ∀ t : ℝ, t * (PrePtFamily.a i * (P0 (t / 2 ^ i)).eval u) =
      (PrePtFamily.a i * 2 ^ i) * ((2 ^ i)⁻¹ * t * (P0 ((2 ^ i)⁻¹ * t)).eval u) := by
    intro t
    rw [inv_mul_eq_div]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, this, smul_eq_mul, inv_inv, G0, inv_mul_eq_div, ← a_mul_four_pow]
  have h4 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
  rw [h4]; ring

theorem integrableOn_scaled {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) (i : ℕ) :
    IntegrableOn (fun t => t * (PrePtFamily.a i * (P0 (t / 2 ^ i)).eval u)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  have := PtF.prePt.integral_scaled hu i
  simp only [PtF.prePt] at this ⊢
  rw [this]
  have := PrePtFamily.w_pos i; have := PrePtFamily.W_pos; have := hu.1
  positivity

/-- **The tail of `∫ t P_t`.** `∫_T^∞ t P_t(u) dt = ∑_i ω_i G⁰(T/2^i, u)`. -/
theorem tail_Pc {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Ioi T, t * (Pc.P t).eval u = ∑' i, om i * G0 (T / 2 ^ i) u := by
  have hu' : u ∈ Icc (0 : ℝ) 2 := ⟨hu.1.le, hu.2⟩
  simp_rw [Pc_eval, ← tsum_mul_left]
  have hmeas : ∀ i : ℕ, Measurable fun t => t * (PrePtFamily.a i * (P0 (t / 2 ^ i)).eval u) :=
    fun i => measurable_id.mul (((measurable_P0 u).comp (measurable_id.div_const _)).const_mul _)
  have hnn : ∀ i t, 0 ≤ t → 0 ≤ t * (PrePtFamily.a i * (P0 (t / 2 ^ i)).eval u) := by
    intro i t ht
    exact mul_nonneg ht (mul_nonneg (PrePtFamily.a_pos i).le (PtF.prePt.eval_nonneg hu'))
  rw [integral_tsum (fun i => (hmeas i).aestronglyMeasurable)]
  · simp_rw [integral_scaled_Ioi]
  · have hle : ∀ i : ℕ, ∫⁻ t in Ioi T, ‖t * (PrePtFamily.a i * (P0 (t / 2 ^ i)).eval u)‖ₑ ≤
        ENNReal.ofReal (PrePtFamily.w i / PrePtFamily.W * (1 / u)) := by
      intro i
      refine (lintegral_mono_set (Ioi_subset_Ioi hT)).trans (le_of_eq ?_)
      rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_scaled hu i)]
      have := PtF.prePt.integral_scaled hu i
      simp only [PtF.prePt] at this
      rw [← this]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn i t (le_of_lt ht))]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro i; have := PrePtFamily.w_pos i; have := PrePtFamily.W_pos; have := hu.1; positivity
    · exact (PrePtFamily.summable_w.div_const _).mul_right _

/-! ### `G⁰` and the Poisson representation -/

/-- `B₀ = f(0)/c + 2A`. -/
def B0 : ℝ := f 0 / cc + 2 * AA

theorem B0_nonneg : 0 ≤ B0 := by
  have := f_zero_pos; have := cc_pos; have := AA_pos; unfold B0; positivity

/-- The pointwise correction `s P⁰_s(u) - Q_s(u)/c`. -/
theorem abs_P0_sub_Q_le {s : ℝ} (hs : 0 < s) (u : ℝ) :
    |s * (P0 s).eval u - (Q s).eval u / cc| ≤ B0 * (Ioc (0 : ℝ) 2).indicator 1 s := by
  have hcc := cc_pos
  have hf := f_zero_pos
  have hA := AA_pos
  rcases lt_or_ge s 1 with h1 | h1
  · rw [eval_P0_lt h1, eval_Q_of_lt_one h1, indicator_of_mem (show s ∈ Ioc (0 : ℝ) 2 from
      ⟨hs, by linarith⟩), Pi.one_apply, mul_zero, zero_sub, abs_neg, abs_of_pos (by positivity),
      mul_one, B0]
    linarith
  · rw [eval_P0 h1]
    rcases le_or_gt s 2 with h2 | h2
    · rw [if_pos h2, indicator_of_mem (show s ∈ Ioc (0 : ℝ) 2 from ⟨hs, h2⟩), Pi.one_apply,
        mul_one]
      have e : s * ((Q s).eval u / (cc * s) + AA) - (Q s).eval u / cc = AA * s := by
        field_simp; ring
      rw [e, abs_of_pos (by positivity), B0]
      have : 0 ≤ f 0 / cc := by positivity
      nlinarith
    · rw [if_neg (not_le.2 h2), indicator_of_notMem (fun h => by linarith [h.2])]
      have e : s * ((Q s).eval u / (cc * s) + 0) - (Q s).eval u / cc = 0 := by
        field_simp; ring
      rw [e]; simp

/-- `G⁰(τ, u) - c⁻¹ ∫_τ^∞ Q_s(u) ds`. -/
def Gc (τ u : ℝ) : ℝ := G0 τ u - (∫ s in Ioi τ, (Q s).eval u) / cc

theorem Gc_eq_integral {τ u : ℝ} (hτ : 0 ≤ τ) (hu : u ∈ Ioc (0 : ℝ) 2) :
    Gc τ u = ∫ s in Ioi τ, (s * (P0 s).eval u - (Q s).eval u / cc) := by
  have i1 : IntegrableOn (fun s => s * (P0 s).eval u) (Ioi τ) :=
    (PtF.prePt.integrable_P hu).mono_set (Ioi_subset_Ioi hτ)
  have i2 : IntegrableOn (fun s => (Q s).eval u / cc) (Ioi τ) :=
    IntegrableOn.mono_set (by exact (integrableOn_Q hu).div_const cc) (Ioi_subset_Ioi hτ)
  rw [integral_sub i1 i2, integral_div, Gc, G0]

theorem abs_Gc_le_const {τ u : ℝ} (hτ : 0 ≤ τ) (hu : u ∈ Ioc (0 : ℝ) 2) :
    |Gc τ u| ≤ 2 * B0 := by
  rw [Gc_eq_integral hτ hu]
  set g : ℝ → ℝ := fun s => B0 * (Ioc (0 : ℝ) 2).indicator 1 s
  have hg : Integrable g := by
    have : Integrable ((Ioc (0 : ℝ) 2).indicator (1 : ℝ → ℝ)) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
    exact this.const_mul B0
  have hb : ∀ᵐ s ∂(volume.restrict (Ioi τ)), ‖s * (P0 s).eval u - (Q s).eval u / cc‖ ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs]
    exact abs_P0_sub_Q_le (lt_of_le_of_lt hτ hs) u
  have h1 := norm_integral_le_of_norm_le hg.integrableOn hb
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ((setIntegral_le_integral hg (Eventually.of_forall fun s => ?_)).trans
    (le_of_eq ?_))
  · simp only [g]; have := B0_nonneg
    exact mul_nonneg this (indicator_nonneg (fun _ _ => zero_le_one) _)
  · simp only [g]
    rw [integral_const_mul, integral_indicator_one measurableSet_Ioc]
    simp [Measure.real, Real.volume_Ioc]
    ring

theorem Gc_eq_zero {τ u : ℝ} (hτ : 2 ≤ τ) (hu : u ∈ Ioc (0 : ℝ) 2) : Gc τ u = 0 := by
  rw [Gc_eq_integral (by linarith) hu]
  have h0 : ∀ s ∈ Ioi τ, s * (P0 s).eval u - (Q s).eval u / cc = 0 := by
    intro s hs
    have hs' : τ < s := hs
    have := abs_P0_sub_Q_le (show 0 < s by linarith) u
    rw [indicator_of_notMem (fun h => by linarith [h.2]), mul_zero] at this
    exact abs_nonpos_iff.1 this
  rw [setIntegral_congr_fun measurableSet_Ioi h0]
  simp

/-- `|G⁰(τ, u) - c⁻¹ ∫_τ^∞ Q_s(u) ds| ≤ 8 B₀ τ⁻²`. -/
theorem abs_Gc_le {τ u : ℝ} (hτ : 0 < τ) (hu : u ∈ Ioc (0 : ℝ) 2) :
    |Gc τ u| ≤ 8 * B0 / τ ^ 2 := by
  have hB := B0_nonneg
  rcases le_or_gt 2 τ with h | h
  · rw [Gc_eq_zero h hu, abs_zero]; positivity
  · refine (abs_Gc_le_const hτ.le hu).trans ?_
    rw [le_div_iff₀ (by positivity)]
    have : τ ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hB]

/-- `∫_τ^∞ s ψ(s y) ds = Ψ₁(τ|y|)/y²` for `y ≠ 0`, `τ ≥ 0`. -/
theorem integral_Ioi_scale {y τ : ℝ} (hy : y ≠ 0) (hτ : 0 ≤ τ) :
    ∫ s in Ioi τ, s * ψ (s * y) = Psi1 (τ * |y|) / y ^ 2 := by
  have hya : 0 < |y| := abs_pos.mpr hy
  have e : ∀ s ∈ Ioi τ, s * ψ (s * y) = |y|⁻¹ * ((|y| * s) * ψ (|y| * s)) := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hτ hs
    rw [← ψ_abs (s * y), abs_mul, abs_of_pos hs0, mul_comm s |y|]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_comp_mul_left_Ioi (fun s => s * ψ s) τ hya, smul_eq_mul,
    ← Psi1_eq_integral (by positivity), ← sq_abs y, mul_comm |y| τ]
  field_simp

theorem integrableOn_Ioi_scale {y τ : ℝ} (hy : y ≠ 0) (hτ : 0 ≤ τ) :
    IntegrableOn (fun s => s * ψ (s * y)) (Ioi τ) := by
  have hya : 0 < |y| := abs_pos.mpr hy
  have h1 : IntegrableOn (fun s => s * ψ (s * y)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_scale hy]
    have := c0_pos
    positivity
  exact h1.mono_set (Ioi_subset_Ioi hτ)

/-- **Poisson representation of the tail.** For `τ ≥ 0` and `x = x(u)`,
`∫_τ^∞ Q_s(u) ds = ∑_k Ψ₁(τ|x+k|)/(x+k)²`. -/
theorem integral_Q_Ioi {u τ : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) (hτ : 0 ≤ τ) :
    ∫ s in Ioi τ, (Q s).eval u = ∑' k : ℤ, Psi1 (τ * |xu u + k|) / (xu u + k) ^ 2 := by
  have hu' : u ∈ Icc (0 : ℝ) 2 := ⟨hu.1.le, hu.2⟩
  set x := xu u
  have hx0 : 0 < x := xu_pos hu.1
  have hx1 : x ≤ 1 / 2 := xu_le u
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => eval_Q_eq (lt_of_le_of_lt hτ hs) hu')]
  have hne : ∀ k : ℤ, x + k ≠ 0 := int_add_ne_zero hx0 hx1
  have hS := hasSum_inv_add_int_sq hx0 (by linarith)
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable (fun s => s * ψ (s * (x + k)))
      (volume.restrict (Ioi τ)) := fun k =>
    (continuous_id.mul (ψ_continuous.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
  rw [integral_tsum hmeas]
  · simp_rw [integral_Ioi_scale (hne _) hτ]
  · have hle : ∀ k : ℤ, ∫⁻ s in Ioi τ, ‖s * ψ (s * (x + k))‖ₑ ≤
        ENNReal.ofReal (c0 * ((x + k) ^ 2)⁻¹) := by
      intro k
      rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_Ioi_scale (hne k) hτ)]
      refine ENNReal.ofReal_le_ofReal ?_
      have e : (∫ s in Ioi τ, ‖s * ψ (s * (x + k))‖) = ∫ s in Ioi τ, s * ψ (s * (x + k)) :=
        setIntegral_congr_fun measurableSet_Ioi fun s hs => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hτ.trans (le_of_lt hs)) (ψ_nonneg _))]
      rw [e, integral_Ioi_scale (hne k) hτ, div_eq_mul_inv]
      have : 0 < (x + k) ^ 2 := by have := hne k; positivity
      gcongr
      exact Psi1_le_c0 (by positivity)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro k; have := c0_pos; positivity
    · exact hS.summable.mul_left c0

/-! ### The terms `k ≠ 0` -/

/-- `B_ℤ = ∑_k (1 + |k|/2)^{-2}`. -/
def Bz : ℝ := ∑' k : ℤ, ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹

theorem Bz_nonneg : 0 ≤ Bz := tsum_nonneg fun k => by positivity

/-- The constant of the `k ≠ 0` terms. -/
def Ck : ℝ := 36 * CΨ * Bz

theorem Ck_nonneg : 0 ≤ Ck := by have := CΨ_nonneg; have := Bz_nonneg; unfold Ck; positivity

theorem Psi1_term_le {x τ : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (hτ : 0 < τ) {k : ℤ} (hk : k ≠ 0) :
    Psi1 (τ * |x + k|) / (x + k) ^ 2 ≤ Ck / τ ^ 2 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := FRD.PtF.abs_add_int_ge hx k
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have hy : 1 / 2 ≤ |x + k| := by linarith
  have hy0 : 0 < |x + k| := by linarith
  have hsq : (x + k) ^ 2 = |x + k| ^ 2 := (sq_abs _).symm
  have hP := Psi1_le (show 0 ≤ τ * |x + k| by positivity)
  -- `(1 + τ|y|)^{-3} ≤ (τ |y|)^{-2}`
  have e1 : ((1 + τ * |x + k|) ^ 3)⁻¹ ≤ ((τ * |x + k|) ^ 2)⁻¹ := by
    have hz : 0 < τ * |x + k| := by positivity
    apply inv_anti₀ (by positivity)
    nlinarith [pow_pos hz 2, pow_pos hz 3, sq_nonneg (τ * |x + k|)]
  -- `|y|^{-4} ≤ 36 (1 + |k|/2)^{-2}` (with `1 + |k|/2 ≤ 3|y|` and `|y| ≥ 1/2`)
  have e2 : (|x + k| ^ 4)⁻¹ ≤ 36 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
    have h3 : 1 + |(k : ℝ)| / 2 ≤ 3 * |x + k| := by linarith
    have h4 : (1 + |(k : ℝ)| / 2) ^ 2 ≤ 9 * |x + k| ^ 2 := by nlinarith
    have h5 : (1 : ℝ) / 4 ≤ |x + k| ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hC := CΨ_nonneg
  calc Psi1 (τ * |x + k|) / (x + k) ^ 2
      ≤ CΨ * ((1 + τ * |x + k|) ^ 3)⁻¹ / (x + k) ^ 2 := by
        gcongr
    _ ≤ CΨ * ((τ * |x + k|) ^ 2)⁻¹ / |x + k| ^ 2 := by rw [hsq]; gcongr
    _ = CΨ / τ ^ 2 * (|x + k| ^ 4)⁻¹ := by field_simp
    _ ≤ CΨ / τ ^ 2 * (36 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹) := by gcongr
    _ ≤ Ck / τ ^ 2 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
        rw [Ck]
        have hB : 1 ≤ Bz := by
          have := FRD.PtF.summable_b.le_tsum 0 (fun k _ => by positivity)
          simpa [Bz] using this
        have hb0 : 0 ≤ ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by positivity
        have : 0 < τ ^ 2 := by positivity
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right this]
        have := mul_le_mul_of_nonneg_left hB (mul_nonneg hC hb0)
        nlinarith

/-- The `k ≠ 0` part of the Poisson sum. -/
def Rk (τ x : ℝ) : ℝ := ∑' k : ℤ, if k = 0 then 0 else Psi1 (τ * |x + k|) / (x + k) ^ 2

theorem summable_Psi1_terms {x τ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hτ : 0 ≤ τ) :
    Summable fun k : ℤ => Psi1 (τ * |x + k|) / (x + k) ^ 2 := by
  have hS := (hasSum_inv_add_int_sq hx0 (by linarith)).summable.mul_left c0
  refine hS.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
  · exact div_nonneg (Psi1_nonneg (by positivity)) (sq_nonneg _)
  · rw [div_eq_mul_inv]
    gcongr
    exact Psi1_le_c0 (by positivity)

theorem tsum_split {x τ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hτ : 0 ≤ τ) :
    ∑' k : ℤ, Psi1 (τ * |x + k|) / (x + k) ^ 2 = Psi1 (τ * x) / x ^ 2 + Rk τ x := by
  rw [(summable_Psi1_terms hx0 hx1 hτ).tsum_eq_add_tsum_ite 0, Rk]
  simp [abs_of_pos hx0]

theorem Rk_bound {x τ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hτ : 0 < τ) :
    0 ≤ Rk τ x ∧ Rk τ x ≤ Ck * Bz / τ ^ 2 := by
  have hx : x ∈ Icc (0 : ℝ) (1 / 2) := ⟨hx0.le, hx1⟩
  have hnn : ∀ k : ℤ, 0 ≤ (if k = 0 then 0 else Psi1 (τ * |x + k|) / (x + k) ^ 2) := by
    intro k; split_ifs
    · exact le_rfl
    · exact div_nonneg (Psi1_nonneg (by positivity)) (sq_nonneg _)
  have hle : ∀ k : ℤ, (if k = 0 then 0 else Psi1 (τ * |x + k|) / (x + k) ^ 2) ≤
      Ck / τ ^ 2 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
    intro k; split_ifs with hk
    · have := Ck_nonneg; positivity
    · exact Psi1_term_le hx hτ hk
  have hs2 : Summable fun k : ℤ => Ck / τ ^ 2 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ :=
    FRD.PtF.summable_b.mul_left _
  have hs1 := hs2.of_nonneg_of_le hnn hle
  refine ⟨tsum_nonneg hnn, (hs1.tsum_le_tsum hle hs2).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left, Bz]; ring

/-! ### The exact form of `ê_T` -/

/-- `sinc²(πx) = sin²(πx)/(πx)²`. -/
def sinc2 (x : ℝ) : ℝ := Real.sin (π * x) ^ 2 / (π * x) ^ 2

theorem u_eq_two_sin_sq {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) : u = 2 * Real.sin (π * xu u) ^ 2 := by
  rw [two_sin_sq, cos_xu hu]

/-- `u Ψ₁(τx)/(c x²) = sinc²(πx) Ψ₁(τx)/c₀`. -/
theorem u_main {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) (z : ℝ) :
    u * (z / xu u ^ 2 / cc) = sinc2 (xu u) * (z / c0) := by
  have hx := xu_pos hu.1
  have := c0_pos
  calc u * (z / xu u ^ 2 / cc) = (2 * Real.sin (π * xu u) ^ 2) * (z / xu u ^ 2 / cc) := by
        rw [← u_eq_two_sin_sq ⟨hu.1.le, hu.2⟩]
    _ = sinc2 (xu u) * (z / c0) := by
        rw [sinc2, cc]
        field_simp

/-- The remainder constant of `ehat_repr`. -/
def Crem : ℝ := (Ck * Bz / cc + 8 * B0) * Som 4

theorem Crem_nonneg : 0 ≤ Crem := by
  have := Ck_nonneg; have := Bz_nonneg; have := cc_pos; have := B0_nonneg
  have := Som_nonneg (r := 4) (by norm_num)
  unfold Crem; positivity

/-- **The exact form of `ê_T` for the concrete family.** For `u = û(p) ∈ (0, 2]` and
`x = x(u) = arccos(1 - u)/2π`, `T > 0`:
`|ê_T(p) - (1 - sinc²(πx) (1 - H(T x)))| ≤ C_rem u / T²`. -/
theorem ehat_repr {msq T : ℝ} (hmsq : 0 ≤ msq) (hT : 0 < T) {p : ℂ} (hu0 : 0 < uhatC msq p) :
    |ehat Pc msq T p - (1 - sinc2 (xu (uhatC msq p)) * (1 - Hp (T * xu (uhatC msq p))))| ≤
      Crem * uhatC msq p / T ^ 2 := by
  set u := uhatC msq p
  have hu : u ∈ Ioc (0 : ℝ) 2 := ⟨hu0, (uhatC_mem hmsq p).2⟩
  set x := xu u
  have hx0 : 0 < x := xu_pos hu.1
  have hx1 : x ≤ 1 / 2 := xu_le u
  have hcc := cc_pos
  have hc0 := c0_pos
  -- the decomposition of each `G⁰(T/2^i)`
  have hG : ∀ i : ℕ, G0 (T / 2 ^ i) u =
      Psi1 (T * x / 2 ^ i) / x ^ 2 / cc + (Rk (T / 2 ^ i) x / cc + Gc (T / 2 ^ i) u) := by
    intro i
    have hτ : 0 ≤ T / 2 ^ i := by positivity
    have h1 : G0 (T / 2 ^ i) u = (∫ s in Ioi (T / 2 ^ i), (Q s).eval u) / cc + Gc (T / 2 ^ i) u := by
      rw [Gc]; ring
    rw [h1, integral_Q_Ioi hu hτ, tsum_split hx0 hx1 hτ, div_mul_eq_mul_div]
    ring
  -- the remainder
  set R : ℕ → ℝ := fun i => Rk (T / 2 ^ i) x / cc + Gc (T / 2 ^ i) u
  have hR : ∀ i, |R i| ≤ (Ck * Bz / cc + 8 * B0) / T ^ 2 * 4 ^ i := by
    intro i
    have hτ : 0 < T / 2 ^ i := by positivity
    obtain ⟨r0, r1⟩ := Rk_bound hx0 hx1 hτ
    have g1 := abs_Gc_le hτ hu
    have e : (T / 2 ^ i) ^ 2 = T ^ 2 / 4 ^ i := by
      rw [div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e] at r1 g1
    have h4 : (0 : ℝ) < 4 ^ i := by positivity
    calc |R i| ≤ |Rk (T / 2 ^ i) x / cc| + |Gc (T / 2 ^ i) u| := abs_add_le _ _
      _ ≤ Ck * Bz / (T ^ 2 / 4 ^ i) / cc + 8 * B0 / (T ^ 2 / 4 ^ i) := by
          rw [abs_div, abs_of_nonneg r0, abs_of_pos hcc]; gcongr
      _ = (Ck * Bz / cc + 8 * B0) / T ^ 2 * 4 ^ i := by field_simp
  obtain ⟨hRs, hRb⟩ := tsum_om_le (r := 4) (by norm_num) hR
  have hM : Summable fun i => om i * (Psi1 (T * x / 2 ^ i) / c0) :=
    summable_om_Psi1 (by positivity)
  have hM' : Summable fun i => om i * (Psi1 (T * x / 2 ^ i) / x ^ 2 / cc) := by
    have := hM.mul_left (c0 / x ^ 2 / cc)
    convert this using 1; funext i; field_simp
  -- assemble
  have key : ehat Pc msq T p = 1 - sinc2 x * (1 - Hp (T * x)) - u * ∑' i, om i * R i := by
    rw [ehat, tail_Pc hu hT.le]
    have hG' : ∀ i, om i * G0 (T / 2 ^ i) u =
        om i * (Psi1 (T * x / 2 ^ i) / x ^ 2 / cc) + om i * R i := by
      intro i; rw [hG]; ring
    simp_rw [hG']
    rw [Summable.tsum_add hM' hRs, mul_add, one_sub_Hp]
    have e2 : u * ∑' i, om i * (Psi1 (T * x / 2 ^ i) / x ^ 2 / cc) =
        sinc2 x * ∑' i, om i * (Psi1 (T * x / 2 ^ i) / c0) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      congr 1; funext i
      rw [mul_left_comm, u_main hu, mul_left_comm]
    rw [e2]
    ring
  rw [key]
  have hu0' : 0 ≤ u := hu0.le
  calc |1 - sinc2 x * (1 - Hp (T * x)) - u * ∑' i, om i * R i -
        (1 - sinc2 x * (1 - Hp (T * x)))| = u * |∑' i, om i * R i| := by
        rw [show 1 - sinc2 x * (1 - Hp (T * x)) - u * ∑' i, om i * R i -
          (1 - sinc2 x * (1 - Hp (T * x))) = -(u * ∑' i, om i * R i) by ring, abs_neg, abs_mul,
          abs_of_nonneg hu0']
    _ ≤ u * ((Ck * Bz / cc + 8 * B0) / T ^ 2 * Som 4) := by gcongr
    _ = Crem * u / T ^ 2 := by rw [Crem]; ring

end

end Step2.D2
