import Cont.TorusHeat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The logarithmic integral `∫₀¹ e^{-π r²/s} ds/s = -log r² + c₀ + o(1)` (B1)
-/

open Real Set Filter Topology MeasureTheory

noncomputable section

namespace Cont

/-- `k(u) = e^{-π/u}/u`. -/
def b1k (u : ℝ) : ℝ := rexp (-π / u) / u

/-- `φ(u) = k(u) - 1/u`, integrable at `∞`. -/
def b1phi (u : ℝ) : ℝ := b1k u - u⁻¹

lemma b1k_continuousOn : ContinuousOn b1k (Ioi 0) := by
  intro u hu
  have hu' : u ≠ 0 := (ne_of_gt hu)
  exact ((continuousAt_const.div continuousAt_id hu').rexp.div continuousAt_id hu').continuousWithinAt

lemma b1phi_continuousOn : ContinuousOn b1phi (Ioi 0) :=
  b1k_continuousOn.sub (continuousOn_inv₀.mono fun _ hu ↦ ne_of_gt hu)

lemma b1_integrableOn_Ioc_of_bdd {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) (B : ℝ)
    (hB : ∀ s ∈ Ioc (0 : ℝ) 1, |f s| ≤ B) : IntegrableOn f (Ioc 0 1) := by
  refine Integrable.mono' (integrable_const B)
    ((hf.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs ↦ by
    simpa [Real.norm_eq_abs] using hB s hs)

lemma b1k_intervalIntegrable_zero_one : IntervalIntegrable b1k volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine b1_integrableOn_Ioc_of_bdd b1k_continuousOn (1 / π) fun s hs ↦ ?_
  have : 0 ≤ b1k s := div_nonneg (exp_pos _).le hs.1.le
  rw [abs_of_nonneg this]
  exact b1_exp_div_le pi_pos hs.1

lemma b1k_intervalIntegrable_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable b1k volume a b :=
  (b1k_continuousOn.mono fun x hx ↦ by
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1).intervalIntegrable

lemma b1phi_integrableOn : IntegrableOn b1phi (Ioi 1) := by
  have hint : IntegrableOn (fun u : ℝ ↦ π * u ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul π
  refine Integrable.mono' hint
    ((b1phi_continuousOn.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu ↦ ?_)
  have hu0 : 0 < u := lt_trans one_pos hu
  have hpi : -π / u = -(π / u) := by ring
  have he : 1 - rexp (-π / u) ≤ π / u := by have := add_one_le_exp (-π / u); linarith
  have he' : rexp (-π / u) ≤ 1 := exp_le_one_iff.mpr (by rw [hpi]; have := div_pos pi_pos hu0; linarith)
  have heq : b1phi u = -((1 - rexp (-π / u)) / u) := by unfold b1phi b1k; field_simp; ring
  rw [Real.norm_eq_abs, heq, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hu0.le)]
  have : π * u ^ (-2 : ℝ) = (π / u) / u := by
    rw [Real.rpow_neg hu0.le, Real.rpow_two]; field_simp
  rw [this]
  exact div_le_div_of_nonneg_right he hu0.le

/-- Scaling identity `∫₀¹ e^{-π r²/s} ds/s = ∫₀^{1/r²} k`. -/
lemma b1_sing_scale {r2 : ℝ} (hr : 0 < r2) :
    ∫ s in Ioc (0 : ℝ) 1, rexp (-π * r2 / s) / s = ∫ u in (0 : ℝ)..r2⁻¹, b1k u := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := r2⁻¹)
    (fun s ↦ rexp (-π * r2 / s) / s) hr.ne'
  simp only [mul_zero, mul_inv_cancel₀ hr.ne', smul_eq_mul] at h
  have hc : (fun u ↦ rexp (-π * r2 / (r2 * u)) / (r2 * u)) = fun u ↦ r2⁻¹ * b1k u := by
    funext u
    rcases eq_or_ne u 0 with rfl | hu
    · simp [b1k]
    · simp only [b1k]
      have : -π * r2 / (r2 * u) = -π / u := by field_simp
      rw [this]; field_simp
  rw [hc, intervalIntegral.integral_const_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero hr.ne') h).symm

/-- `∫₀¹ e^{-π r²/s} ds/s + log r² = ∫₀¹ k + ∫₁^{1/r²} φ`. -/
lemma b1_sing_add_log {r2 : ℝ} (hr : 0 < r2) :
    (∫ s in Ioc (0 : ℝ) 1, rexp (-π * r2 / s) / s) + Real.log r2 =
      (∫ u in (0 : ℝ)..1, b1k u) + ∫ u in (1 : ℝ)..r2⁻¹, b1phi u := by
  have hR : 0 < r2⁻¹ := inv_pos.mpr hr
  rw [b1_sing_scale hr, ← intervalIntegral.integral_add_adjacent_intervals
    b1k_intervalIntegrable_zero_one (b1k_intervalIntegrable_pos one_pos hR)]
  have hinv : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 1 r2⁻¹ :=
    intervalIntegral.intervalIntegrable_inv (fun x hx ↦ by
      rcases le_total 1 r2⁻¹ with h | h
      · rw [uIcc_of_le h] at hx; exact ne_of_gt (lt_of_lt_of_le one_pos hx.1)
      · rw [uIcc_of_ge h] at hx; exact ne_of_gt (lt_of_lt_of_le hR hx.1)) continuousOn_id
  have hphi : ∫ u in (1 : ℝ)..r2⁻¹, b1phi u =
      (∫ u in (1 : ℝ)..r2⁻¹, b1k u) - ∫ u in (1 : ℝ)..r2⁻¹, u⁻¹ :=
    intervalIntegral.integral_sub (b1k_intervalIntegrable_pos one_pos hR) hinv
  rw [hphi, integral_inv_of_pos one_pos hR, div_one, Real.log_inv]
  ring

/-- The constant `c₀ = ∫₀¹ k + ∫₁^∞ φ`. -/
def b1c0 : ℝ := (∫ u in (0 : ℝ)..1, b1k u) + ∫ u in Ioi (1 : ℝ), b1phi u

/-- Logarithmic asymptotics: `∫₀¹ e^{-π r²/s} ds/s + log r² → c₀` as `r² → 0⁺`. -/
theorem b1_tendsto_sing_add_log :
    Tendsto (fun r2 : ℝ ↦ (∫ s in Ioc (0 : ℝ) 1, rexp (-π * r2 / s) / s) + Real.log r2)
      (𝓝[>] 0) (𝓝 b1c0) := by
  have h := (intervalIntegral_tendsto_integral_Ioi 1 b1phi_integrableOn tendsto_id).comp
    tendsto_inv_nhdsGT_zero
  refine Tendsto.congr' ?_ (h.const_add (∫ u in (0 : ℝ)..1, b1k u))
  filter_upwards [self_mem_nhdsWithin] with r2 hr
  rw [b1_sing_add_log hr]
  rfl

end Cont
