import Step2.D2.D2Sh2

/-!
# Sharp line 3, part 3: the representation of `∫_T^∞ τ D_τ(x) dτ`

* `integral_fP'`: `∫_z^∞ r² ψ'(r) dr = -f(z)`;
* `integral_tP`: `∫_T^∞ τ t_i(τ) dτ = -ω_i f(Tx/2^i)/(c x³)`;
* `integral_D0`: `∫_T^∞ τ D⁰_τ(x) dτ = -(2c₀/(c x³)) (1 - Φ_H(Tx))`;
* `tail_repr`: `|∫_T^∞ τ D_τ(x) dτ + (2c₀/(c x³))(1 - Φ_H(Tx))| ≤ C₁ S₈/(3T³)`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

theorem continuous_fP' : Continuous fP' := by
  unfold fP'; exact (continuous_pow 2).mul continuous_ψd

theorem abs_fP'_le {r : ℝ} (hr : 0 ≤ r) : |fP' r| ≤ Cd * ((1 + r) ^ 4)⁻¹ := by
  rw [fP', abs_mul, abs_of_nonneg (sq_nonneg r)]
  have h := ψd_le r
  rw [abs_of_nonneg hr] at h
  have hCd := Cd_nonneg
  have h1 : r ^ 2 ≤ (1 + r) ^ 4 := by
    calc r ^ 2 ≤ (1 + r) ^ 2 := pow_le_pow_left₀ hr (by linarith) 2
      _ ≤ (1 + r) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  calc r ^ 2 * |ψd r| ≤ (1 + r) ^ 4 * (Cd / (1 + r) ^ 8) :=
        mul_le_mul h1 h (abs_nonneg _) (by positivity)
    _ = Cd * ((1 + r) ^ 4)⁻¹ := by field_simp

theorem integrableOn_fP' {z : ℝ} (hz : 0 ≤ z) : IntegrableOn fP' (Ioi z) := by
  refine ((integrableOn_Ioi_one_add_pow z hz).const_mul Cd).mono'
    continuous_fP'.aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
  rw [Real.norm_eq_abs]
  exact abs_fP'_le (le_of_lt (lt_of_le_of_lt hz hr))

theorem tendsto_fP : Tendsto fP atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => Cfp * ((1 + r) ^ 3)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun r : ℝ => ((1 + r) ^ 3)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp
        (tendsto_atTop_add_const_left _ 1 tendsto_id))
    simpa using this.const_mul Cfp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with r hr; exact fP_nonneg hr
  · filter_upwards [eventually_ge_atTop 0] with r hr; exact fP_le hr

theorem integral_fP' {z : ℝ} (hz : 0 ≤ z) : ∫ r in Ioi z, fP' r = -fP z := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hasDerivAt_fP z).continuousAt.continuousWithinAt
    (fun r _ => hasDerivAt_fP r) (integrableOn_fP' hz) tendsto_fP]
  ring

/-- `τ t_i(τ) = (a_i/(2^i c c_x²)) f'(c_x τ)`, `c_x = x/2^i`. -/
theorem tau_tP_eq {x : ℝ} (hx : 0 < x) (i : ℕ) (τ : ℝ) :
    τ * tP x τ i = PrePtFamily.a i / (2 ^ i * cc * (x / 2 ^ i) ^ 2) * fP' (x / 2 ^ i * τ) := by
  have hcc := cc_pos
  unfold tP fP'
  have : (2 : ℝ) ^ i ≠ 0 := by positivity
  rw [show τ * x / 2 ^ i = x / 2 ^ i * τ by ring]
  field_simp

theorem integrableOn_tau_tP {x : ℝ} (hx : 0 < x) (i : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun τ => τ * tP x τ i) (Ioi T) := by
  have hc : 0 < x / 2 ^ i := by positivity
  simp_rw [tau_tP_eq hx i]
  refine Integrable.const_mul ?_ _
  exact (integrableOn_Ioi_comp_mul_left_iff fP' T hc).2 (integrableOn_fP' (by positivity))

theorem integral_tau_tP {x : ℝ} (hx : 0 < x) (i : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in Ioi T, τ * tP x τ i = -(om i / (cc * x ^ 3)) * fP (T * x / 2 ^ i) := by
  have hc : 0 < x / 2 ^ i := by positivity
  have hcc := cc_pos
  simp_rw [tau_tP_eq hx i]
  rw [integral_const_mul, integral_comp_mul_left_Ioi fP' T hc, integral_fP' (by positivity),
    smul_eq_mul, ← a_mul_four_pow, show T * x / 2 ^ i = x / 2 ^ i * T by ring]
  have : (2 : ℝ) ^ i ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
  rw [h4]
  field_simp

theorem integral_norm_tau_tP_le {x : ℝ} (hx : 0 < x) (i : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in Ioi T, ‖τ * tP x τ i‖ ≤ om i * ((∫ r in Ioi 0, |fP' r|) / (cc * x ^ 3)) := by
  have hc : 0 < x / 2 ^ i := by positivity
  have hcc := cc_pos
  have hpos : 0 < PrePtFamily.a i / (2 ^ i * cc * (x / 2 ^ i) ^ 2) := by
    have := PrePtFamily.a_pos i; positivity
  simp_rw [tau_tP_eq hx i, norm_mul, Real.norm_of_nonneg hpos.le, Real.norm_eq_abs]
  rw [integral_const_mul]
  have h1 := integral_comp_mul_left_Ioi (fun r => |fP' r|) T hc
  rw [h1, smul_eq_mul]
  have hI : ∫ r in Ioi (x / 2 ^ i * T), |fP' r| ≤ ∫ r in Ioi 0, |fP' r| :=
    setIntegral_mono_set (integrableOn_fP' le_rfl).abs
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r _ => abs_nonneg _)
      (Eventually.of_forall (Ioi_subset_Ioi (by positivity)))
  have hI0 : 0 ≤ ∫ r in Ioi (x / 2 ^ i * T), |fP' r| :=
    setIntegral_nonneg measurableSet_Ioi fun r _ => abs_nonneg _
  have e : PrePtFamily.a i / (2 ^ i * cc * (x / 2 ^ i) ^ 2) * (x / 2 ^ i)⁻¹ =
      om i / (cc * x ^ 3) := by
    rw [← a_mul_four_pow]
    have : (2 : ℝ) ^ i ≠ 0 := by positivity
    have h4 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
    rw [h4]; field_simp
  calc PrePtFamily.a i / (2 ^ i * cc * (x / 2 ^ i) ^ 2) *
        ((x / 2 ^ i)⁻¹ * ∫ r in Ioi (x / 2 ^ i * T), |fP' r|)
      = om i / (cc * x ^ 3) * ∫ r in Ioi (x / 2 ^ i * T), |fP' r| := by rw [← e]; ring
    _ ≤ om i / (cc * x ^ 3) * ∫ r in Ioi 0, |fP' r| := by
        gcongr; have := om_pos i; positivity
    _ = _ := by ring

/-- **`∫_T^∞ τ D⁰_τ(x) dτ`.** -/
theorem integral_D0 {x : ℝ} (hx : 0 < x) {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in Ioi T, ∑' i, τ * tP x τ i = -(2 * c0 / (cc * x ^ 3)) * (1 - PhiH (T * x)) := by
  have hcc := cc_pos
  have hc0 := c0_pos
  rw [← integral_tsum_of_summable_integral_norm (fun i => integrableOn_tau_tP hx i hT)
    ((summable_om.mul_right _).of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => integral_norm_tau_tP_le hx i hT))]
  simp_rw [integral_tau_tP hx _ hT]
  have hs := summable_om_fP (z := T * x) (by positivity)
  have e : (fun i => -(om i / (cc * x ^ 3)) * fP (T * x / 2 ^ i)) =
      fun i => -(cc * x ^ 3)⁻¹ * (om i * fP (T * x / 2 ^ i)) := by
    funext i; field_simp
  rw [e, tsum_mul_left]
  have h1 : 1 - PhiH (T * x) = (2 * c0)⁻¹ * ∑' i, om i * fP (T * x / 2 ^ i) := by
    unfold PhiH; ring
  rw [h1]
  field_simp

theorem continuous_tP (x : ℝ) (i : ℕ) : Continuous fun τ => tP x τ i := by
  unfold tP
  exact (((continuous_const.mul (continuous_id.div_const _))).mul
    (continuous_ψd.comp ((continuous_id.mul continuous_const).div_const _))).div_const _

theorem measurable_Dp (x : ℝ) : Measurable fun τ => Dp τ x := by
  have : (fun τ => Dp τ x) = fun τ => Pd τ (1 - Real.cos (2 * π * x)) *
      (2 * π * Real.sin (2 * π * x)) := rfl
  rw [this]
  exact (measurable_Pd _).mul_const _

theorem integrable_rpow_tail {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun τ : ℝ => (τ ^ 4)⁻¹) (Ioi T) ∧
      ∫ τ in Ioi T, (τ ^ 4)⁻¹ = (T ^ 3)⁻¹ / 3 := by
  have e : EqOn (fun τ : ℝ => (τ ^ 4)⁻¹) (fun τ => τ ^ (-(4 : ℝ))) (Ioi T) := by
    intro τ hτ
    have : 0 < τ := lt_trans hT hτ
    simp only
    rw [Real.rpow_neg this.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hi := integrableOn_Ioi_rpow_of_lt (show (-(4 : ℝ)) < -1 by norm_num) hT
  refine ⟨hi.congr_fun e.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_rpow_of_lt (by norm_num) hT]
  rw [show (-(4 : ℝ)) + 1 = -3 by norm_num, Real.rpow_neg hT.le,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- **The tail of `∫ τ D_τ`.** For `x ∈ (0, 1/2]`, `T > 0`. -/
theorem tail_repr {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun τ => τ * Dp τ x) (Ioi T) ∧
    |(∫ τ in Ioi T, τ * Dp τ x) + 2 * c0 / (cc * x ^ 3) * (1 - PhiH (T * x))| ≤
      C1d * Som 8 * (T ^ 3)⁻¹ / 3 := by
  have hx0 := hx.1
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2) := ⟨hx0.le, hx.2⟩
  set C := C1d * Som 8
  have hC : 0 ≤ C := mul_nonneg C1d_nonneg (Som_nonneg (by norm_num))
  obtain ⟨hint4, hval4⟩ := integrable_rpow_tail hT
  -- `τ D_τ` is integrable
  have hDp : IntegrableOn (fun τ => τ * Dp τ x) (Ioi T) := by
    have hb : IntegrableOn (fun τ : ℝ => CD * (τ ^ 2 / (1 + τ * x) ^ 6)) (Ioi 0) :=
      (integrableOn_sq_decay (a := x) hx0).const_mul CD
    refine (IntegrableOn.mono_set hb (Ioi_subset_Ioi hT.le)).mono'
      ((measurable_id.mul (measurable_Dp x)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
    have hτ0 : 0 < τ := lt_trans hT hτ
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hτ0]
    have := abs_Dp_le hτ0 hxI
    calc τ * |Dp τ x| ≤ τ * (CD * τ / (1 + τ * x) ^ 6) := by gcongr
      _ = CD * (τ ^ 2 / (1 + τ * x) ^ 6) := by ring
  -- `τ D⁰_τ` is measurable and integrable
  have hmeas : AEStronglyMeasurable (fun τ => ∑' i, τ * tP x τ i) (volume.restrict (Ioi T)) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun n τ => ∑ i ∈ Finset.range n, τ * tP x τ i) (fun n => ?_) ?_
    · exact (continuous_finsetSum _ fun i _ =>
        continuous_id.mul (continuous_tP x i)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
      have hτ0 : 0 < τ := lt_trans hT hτ
      exact ((summable_tP hxI hτ0).mul_left τ).hasSum.tendsto_sum_nat
  have hdiff : ∀ τ ∈ Ioi T, |τ * Dp τ x - ∑' i, τ * tP x τ i| ≤ C * (τ ^ 4)⁻¹ := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_trans hT hτ
    rw [tsum_mul_left, ← mul_sub, abs_mul, abs_of_pos hτ0]
    have h := abs_Dp_sub_D0_le hxI hτ0
    unfold D0 at h
    calc τ * |Dp τ x - ∑' i, tP x τ i| ≤ τ * (C * (τ ^ 5)⁻¹) := by gcongr
      _ = C * (τ ^ 4)⁻¹ := by field_simp
  have hD0 : IntegrableOn (fun τ => ∑' i, τ * tP x τ i) (Ioi T) := by
    refine (hDp.norm.add (hint4.const_mul C)).mono' hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
    have := hdiff τ hτ
    rw [Real.norm_eq_abs]
    have h2 := abs_sub_abs_le_abs_sub (∑' i, τ * tP x τ i) (τ * Dp τ x)
    rw [abs_sub_comm] at this
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith
  refine ⟨hDp, ?_⟩
  have hsplit : ∫ τ in Ioi T, τ * Dp τ x = (∫ τ in Ioi T, ∑' i, τ * tP x τ i) +
      ∫ τ in Ioi T, (τ * Dp τ x - ∑' i, τ * tP x τ i) := by
    rw [integral_sub hDp hD0]; ring
  rw [hsplit, integral_D0 hx0 hT.le]
  have hE : |∫ τ in Ioi T, (τ * Dp τ x - ∑' i, τ * tP x τ i)| ≤ C * ((T ^ 3)⁻¹ / 3) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hint4.const_mul C)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hdiff τ hτ
    · rw [integral_const_mul, hval4]
  set I := ∫ τ in Ioi T, (τ * Dp τ x - ∑' i, τ * tP x τ i)
  have key : -(2 * c0 / (cc * x ^ 3)) * (1 - PhiH (T * x)) + I +
      2 * c0 / (cc * x ^ 3) * (1 - PhiH (T * x)) = I := by ring
  rw [key]
  calc |I| ≤ C * ((T ^ 3)⁻¹ / 3) := hE
    _ = C * (T ^ 3)⁻¹ / 3 := by ring

end

end Step2.D2