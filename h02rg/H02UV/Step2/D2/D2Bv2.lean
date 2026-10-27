import Step2.D2.D2Bv1

/-!
# Differentiation of `∫ t P_t(u) dt` in `u` (`prop:d2`, line 3)

For the concrete family and `u ∈ (0, 2)`, `x = x(u)`:

* `measurable_Pd`: `τ ↦ P_τ'(u)` is measurable;
* `Pd_eq`: `P_τ'(u) = D_τ(x) / (2π sin 2πx)`;
* `hasDerivAt_integral_P`: `d/du ∫_S τ P_τ(u) dτ = ∫_S τ P_τ'(u) dτ` (`S ⊆ (0, ∞)` measurable);
* `integral_Pd_Ioi`: `∫_0^∞ τ P_τ'(u) dτ = -1/u²`;
* `tail_Pd_le`: `|∫_T^∞ τ P_τ'(u) dτ| · 2π sin 2πx ≤ C_D x^{-6} T^{-3}/3`;
* `head_Pd_le`: `|∫_0^T τ P_τ'(u) dτ| · 2π sin 2πx ≤ C_D T³/3`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- `P_τ'(u)`. -/
def Pd (τ u : ℝ) : ℝ := ((Pc.P τ).derivative).eval u

theorem measurable_Pd (u : ℝ) : Measurable fun τ => Pd τ u := by
  have hlim : Tendsto (fun (n : ℕ) (τ : ℝ) => ((1 : ℝ) / (n + 1))⁻¹ *
      ((Pc.P τ).eval (u + 1 / (n + 1)) - (Pc.P τ).eval u)) atTop (𝓝 fun τ => Pd τ u) := by
    rw [tendsto_pi_nhds]
    intro τ
    have h := ((Pc.P τ).hasDerivAt u).tendsto_slope_zero_right
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_one_div_add_atTop_nhds_zero_nat
        (Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity)
    have := h.comp h2
    simpa only [Function.comp_def, smul_eq_mul, Pd] using this
  refine measurable_of_tendsto_metrizable (fun n => ?_) hlim
  exact ((Pc.measurable _).sub (Pc.measurable _)).const_mul _

theorem xu_lt_half {u : ℝ} (hu : u < 2) : xu u < 1 / 2 := by
  unfold xu
  rw [div_lt_iff₀ (by positivity)]
  have : Real.arccos (1 - u) < π := Real.arccos_lt_pi.2 (by linarith)
  linarith

theorem sin_xu_sq {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) :
    Real.sin (2 * π * xu u) ^ 2 = u * (2 - u) := by
  have h := cos_xu hu
  have := Real.sin_sq_add_cos_sq (2 * π * xu u)
  have hc : Real.cos (2 * π * xu u) = 1 - u := by linarith
  rw [hc] at this; nlinarith

theorem sin_xu_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) : 0 < Real.sin (2 * π * xu u) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have := xu_pos hu.1; positivity
  · have := xu_lt_half hu.2; nlinarith [pi_pos]

theorem Pd_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) (τ : ℝ) :
    Pd τ u = Dp τ (xu u) / (2 * π * Real.sin (2 * π * xu u)) := by
  have hs := sin_xu_pos hu
  have hne : 2 * π * Real.sin (2 * π * xu u) ≠ 0 := by have := pi_pos; positivity
  rw [eq_div_iff hne, Dp, cos_xu ⟨hu.1.le, hu.2.le⟩, Pd]

theorem xu_mono {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 2) : xu a ≤ xu b := by
  unfold xu
  gcongr

/-- `τ² (1 + aτ)^{-6}` is integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_sq_decay {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun τ : ℝ => τ ^ 2 / (1 + τ * a) ^ 6) (Ioi 0) := by
  have h1 : IntegrableOn (fun τ : ℝ => ((1 + τ * a) ^ 4)⁻¹) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun r : ℝ => ((1 + r) ^ 4)⁻¹) 0 ha).2
      (by rw [mul_zero]; exact integrableOn_Ioi_one_add_pow 0 le_rfl)
    simpa [mul_comm] using this
  refine (h1.const_mul (a⁻¹ ^ 2)).mono' ?_ ?_
  · exact ((measurable_id.pow_const 2).div (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ => ?_)
    have hτ0 : 0 < τ := hτ
    have hp : 0 < 1 + τ * a := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : τ ^ 2 ≤ a⁻¹ ^ 2 * (1 + τ * a) ^ 2 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ hτ0.le
      rw [mul_add, mul_one, mul_comm τ a, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      have : 0 < a⁻¹ := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)]
    calc τ ^ 2 ≤ a⁻¹ ^ 2 * (1 + τ * a) ^ 2 := h2
      _ = a⁻¹ ^ 2 * ((1 + τ * a) ^ 4)⁻¹ * (1 + τ * a) ^ 6 := by field_simp

/-- **Differentiation under the integral.** For `u₀ ∈ (0, 2)` and measurable `S ⊆ (0, ∞)`. -/
theorem hasDerivAt_integral_P {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0) {u₀ : ℝ}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) 2) (hint : IntegrableOn (fun τ => τ * (Pc.P τ).eval u₀) S) :
    IntegrableOn (fun τ => τ * Pd τ u₀) S ∧
      HasDerivAt (fun u => ∫ τ in S, τ * (Pc.P τ).eval u) (∫ τ in S, τ * Pd τ u₀) u₀ := by
  set a := u₀ / 2
  set b := (u₀ + 2) / 2
  have ha : 0 < a := by simp only [a]; linarith [hu₀.1]
  have hab : a < u₀ ∧ u₀ < b := ⟨by simp only [a]; linarith [hu₀.1],
    by simp only [b]; linarith [hu₀.2]⟩
  have hb : b < 2 := by simp only [b]; linarith [hu₀.2]
  set xa := xu a
  have hxa : 0 < xa := xu_pos ha
  set δ := min (a * (2 - a)) (b * (2 - b))
  have hδ : 0 < δ := lt_min (by nlinarith) (by nlinarith)
  have hsin : ∀ u ∈ Icc a b, √δ ≤ Real.sin (2 * π * xu u) := by
    intro u hu
    have hu2 : u ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h1 : δ ≤ u * (2 - u) := by
      rcases le_total u 1 with h | h
      · exact (min_le_left _ _).trans (by nlinarith [hu.1])
      · exact (min_le_right _ _).trans (by nlinarith [hu.2])
    rw [Real.sqrt_le_left (sin_xu_pos ⟨by linarith [hu.1], by linarith [hu.2]⟩).le]
    rw [sin_xu_sq hu2]; exact h1
  set bound : ℝ → ℝ := fun τ => CD / (2 * π * √δ) * (τ ^ 2 / (1 + τ * xa) ^ 6)
  have hbound : ∀ τ ∈ S, ∀ u ∈ Icc a b, ‖τ * Pd τ u‖ ≤ bound τ := by
    intro τ hτ u hu
    have hτ0 : 0 < τ := hS0 hτ
    have hu' : u ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hx := xu_mono hu.1 ha.le (by linarith [hu.2])
    have hxu : xu u ∈ Icc (0 : ℝ) (1 / 2) := ⟨xu_nonneg u, xu_le u⟩
    have hD := abs_Dp_le hτ0 hxu
    have hs := hsin u hu
    have hsq : 0 < √δ := Real.sqrt_pos.2 hδ
    have hpos : (0 : ℝ) < 2 * π * Real.sin (2 * π * xu u) := by
      have := sin_xu_pos hu'; have := pi_pos; positivity
    rw [Pd_eq hu', Real.norm_eq_abs, abs_mul, abs_of_pos hτ0, abs_div, abs_of_pos hpos]
    have hC := CD_nonneg
    have e1 : (1 + τ * xa) ^ 6 ≤ (1 + τ * xu u) ^ 6 := by gcongr
    calc τ * (|Dp τ (xu u)| / (2 * π * Real.sin (2 * π * xu u)))
        ≤ τ * (CD * τ / (1 + τ * xu u) ^ 6 / (2 * π * √δ)) := by gcongr
      _ ≤ τ * (CD * τ / (1 + τ * xa) ^ 6 / (2 * π * √δ)) := by gcongr
      _ = bound τ := by simp only [bound]; field_simp
  have hbi : IntegrableOn bound S :=
    IntegrableOn.mono_set (by exact (integrableOn_sq_decay hxa).const_mul _) hS0
  have hderiv : ∀ τ, ∀ u, HasDerivAt (fun u => τ * (Pc.P τ).eval u) (τ * Pd τ u) u :=
    fun τ u => ((Pc.P τ).hasDerivAt u).const_mul τ
  have hnhds : Icc a b ∈ 𝓝 u₀ := Icc_mem_nhds hab.1 hab.2
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun u τ => τ * (Pc.P τ).eval u) (F' := fun u τ => τ * Pd τ u) (x₀ := u₀)
    (bound := bound) hnhds
    (Eventually.of_forall fun u => (measurable_id.mul (Pc.measurable u)).aestronglyMeasurable)
    hint ((measurable_id.mul (measurable_Pd u₀)).aestronglyMeasurable)
    ((ae_restrict_iff' hS).2 (Eventually.of_forall fun τ hτ u hu => hbound τ hτ u hu)) hbi
    (Eventually.of_forall fun τ u _ => hderiv τ u)
  exact this

theorem integrableOn_P_Ioi {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun τ => τ * (Pc.P τ).eval u) (Ioi T) :=
  FRD.integrableOn_Ioi Pc hu hT

/-- **`∫_0^∞ τ P_τ'(u) dτ = -1/u²`** for `u ∈ (0, 2)`. -/
theorem integral_Pd_Ioi {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) :
    IntegrableOn (fun τ => τ * Pd τ u) (Ioi 0) ∧ ∫ τ in Ioi 0, τ * Pd τ u = -1 / u ^ 2 := by
  obtain ⟨hi, hd⟩ := hasDerivAt_integral_P measurableSet_Ioi le_rfl hu
    (integrableOn_P_Ioi ⟨hu.1, hu.2.le⟩ le_rfl)
  refine ⟨hi, ?_⟩
  have h2 : HasDerivAt (fun u : ℝ => 1 / u) (-1 / u ^ 2) u := by
    have := (hasDerivAt_inv hu.1.ne')
    convert this using 1
    · funext v; rw [one_div]
    · field_simp
  have heq : (fun u => ∫ τ in Ioi 0, τ * (Pc.P τ).eval u) =ᶠ[𝓝 u] fun u : ℝ => 1 / u := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    exact Pc.integral_eq v ⟨hv.1, hv.2.le⟩
  exact hd.unique (h2.congr_of_eventuallyEq heq)

theorem integral_tail_le {x : ℝ} (hx : 0 < x) {T : ℝ} (hT : 0 < T) :
    ∫ τ in Ioi T, CD * τ ^ 2 / (1 + τ * x) ^ 6 ≤ CD / (3 * x ^ 6 * T ^ 3) := by
  have hC := CD_nonneg
  have hi : IntegrableOn (fun τ : ℝ => CD * τ ^ (-(4 : ℝ)) / x ^ 6) (Ioi T) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul CD).div_const _
  have hle : ∀ τ ∈ Ioi T, CD * τ ^ 2 / (1 + τ * x) ^ 6 ≤ CD * τ ^ (-(4 : ℝ)) / x ^ 6 := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_trans hT hτ
    have e : τ ^ (-(4 : ℝ)) = (τ ^ 4)⁻¹ := by
      rw [Real.rpow_neg hτ0.le]; norm_cast
    rw [e]
    have h1 : (τ * x) ^ 6 ≤ (1 + τ * x) ^ 6 := by gcongr; linarith
    have h2 : CD * τ ^ 2 / (1 + τ * x) ^ 6 ≤ CD * τ ^ 2 / (τ * x) ^ 6 := by gcongr
    refine h2.trans (le_of_eq ?_)
    field_simp
  have hi2 : IntegrableOn (fun τ : ℝ => CD * τ ^ 2 / (1 + τ * x) ^ 6) (Ioi T) := by
    refine (hi.mono' ?_ ?_)
    · exact ((by fun_prop : Measurable fun τ : ℝ => CD * τ ^ 2).div
        (by fun_prop : Measurable fun τ : ℝ => (1 + τ * x) ^ 6)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ0 : 0 < τ := lt_trans hT hτ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hle τ hτ
  refine (setIntegral_mono_on hi2 hi measurableSet_Ioi hle).trans (le_of_eq ?_)
  rw [integral_div, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
  rw [show (-(4 : ℝ)) + 1 = -3 by norm_num, Real.rpow_neg hT.le,
    show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- The angular factor `2π sin 2πx(u)`. -/
def snx (u : ℝ) : ℝ := 2 * π * Real.sin (2 * π * xu u)

theorem snx_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) : 0 < snx u := by
  have := sin_xu_pos hu; have := pi_pos; unfold snx; positivity

theorem abs_tau_Pd_le {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) {τ : ℝ} (hτ : 0 < τ) :
    |τ * Pd τ u| * snx u ≤ CD * τ ^ 2 / (1 + τ * xu u) ^ 6 := by
  have hs := snx_pos hu
  have e : Pd τ u = Dp τ (xu u) / snx u := Pd_eq hu τ
  rw [e, abs_mul, abs_of_pos hτ, abs_div, abs_of_pos hs]
  have hD := abs_Dp_le hτ ⟨xu_nonneg u, xu_le u⟩
  rw [mul_assoc, div_mul_cancel₀ _ hs.ne']
  calc τ * |Dp τ (xu u)| ≤ τ * (CD * τ / (1 + τ * xu u) ^ 6) := by gcongr
    _ = CD * τ ^ 2 / (1 + τ * xu u) ^ 6 := by ring

/-- **The head and the tail.** For `u ∈ (0, 2)`, `T > 0`:
`∫_0^T τ P_τ' = -1/u² - ∫_T^∞ τ P_τ'`, `|∫_T^∞ τ P_τ'| snx ≤ C_D/(3 x⁶ T³)`,
`|∫_0^T τ P_τ'| snx ≤ C_D T³/3`. -/
theorem head_tail_Pd {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) {T : ℝ} (hT : 0 < T) :
    (∫ τ in Ioc 0 T, τ * Pd τ u) = -1 / u ^ 2 - ∫ τ in Ioi T, τ * Pd τ u ∧
      |∫ τ in Ioi T, τ * Pd τ u| * snx u ≤ CD / (3 * xu u ^ 6 * T ^ 3) ∧
      |∫ τ in Ioc 0 T, τ * Pd τ u| * snx u ≤ CD * T ^ 3 / 3 := by
  obtain ⟨hi, hval⟩ := integral_Pd_Ioi hu
  have hs := snx_pos hu
  have hx := xu_pos hu.1
  have hC := CD_nonneg
  have hiT : IntegrableOn (fun τ => τ * Pd τ u) (Ioi T) := hi.mono_set (Ioi_subset_Ioi hT.le)
  have hiH : IntegrableOn (fun τ => τ * Pd τ u) (Ioc 0 T) := hi.mono_set Ioc_subset_Ioi_self
  refine ⟨?_, ?_, ?_⟩
  · have h := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hiH hiT
    rw [Ioc_union_Ioi_eq_Ioi hT.le, hval] at h
    linarith
  · have h1 := norm_integral_le_integral_norm (μ := volume.restrict (Ioi T))
      (fun τ => τ * Pd τ u)
    rw [Real.norm_eq_abs] at h1
    have h2 : (∫ τ in Ioi T, ‖τ * Pd τ u‖) * snx u ≤
        ∫ τ in Ioi T, CD * τ ^ 2 / (1 + τ * xu u) ^ 6 := by
      rw [← integral_mul_const]
      refine setIntegral_mono_on (hiT.norm.mul_const _) ?_ measurableSet_Ioi fun τ hτ => ?_
      · refine IntegrableOn.mono_set (by exact (integrableOn_sq_decay hx).const_mul CD)
          (Ioi_subset_Ioi hT.le) |>.congr_fun (fun τ _ => by ring) measurableSet_Ioi
      · rw [Real.norm_eq_abs]; exact abs_tau_Pd_le hu (lt_trans hT hτ)
    calc _ ≤ (∫ τ in Ioi T, ‖τ * Pd τ u‖) * snx u := by gcongr
      _ ≤ _ := h2.trans (integral_tail_le hx hT)
  · have h1 := norm_integral_le_integral_norm (μ := volume.restrict (Ioc 0 T))
      (fun τ => τ * Pd τ u)
    rw [Real.norm_eq_abs] at h1
    have h2 : (∫ τ in Ioc 0 T, ‖τ * Pd τ u‖) * snx u ≤ ∫ τ in Ioc 0 T, CD * τ ^ 2 := by
      rw [← integral_mul_const]
      refine setIntegral_mono_on (hiH.norm.mul_const _)
        ((continuous_const.mul (continuous_id.pow 2)).integrableOn_Ioc) measurableSet_Ioc
        fun τ hτ => ?_
      rw [Real.norm_eq_abs]
      refine (abs_tau_Pd_le hu hτ.1).trans ?_
      have : 1 ≤ (1 + τ * xu u) ^ 6 := one_le_pow₀ (by have := hτ.1.le; nlinarith)
      exact div_le_self (by positivity) this
    have h3 : ∫ τ in Ioc 0 T, CD * τ ^ 2 = CD * T ^ 3 / 3 := by
      rw [← intervalIntegral.integral_of_le hT.le,
        intervalIntegral.integral_const_mul, integral_pow]
      ring
    calc _ ≤ (∫ τ in Ioc 0 T, ‖τ * Pd τ u‖) * snx u := by gcongr
      _ ≤ _ := h2.trans h3.le

end

end Step2.D2
