import Step2.D2.D2Sh8

/-!
# Sharp line 3, part 9: `J(T)` versus `J_Φ(T) = ∫ λ³ Φ(2T√ν)²/ν⁴`

* `continuousOn_PhiE`: `Φ` is continuous on `[0, ∞)`, `Φ(0) = 0`;
* `intBZ_dec3`: `∫_{BZ} (1 + T√λ)^{-3} ≤ π² Ia(3)/(4T²)`;
* `JT_sub_JPhi`: `|J(T) - J_Φ(T)| ≤ C_J/T²`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

variable {msq T : ℝ}

theorem PhiE_zero : PhiE 0 = 0 := by
  have := abs_PhiE_le (y := 0) le_rfl
  simpa using this

theorem continuousOn_PhiE : ContinuousOn PhiE (Ici 0) := by
  intro y hy
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ y from hy) with h0 | h0
  · subst h0
    rw [ContinuousWithinAt, PhiE_zero]
    set c := (2 * c0)⁻¹ * M2
    have h1 : Tendsto (fun y : ℝ => c * y ^ 4) (𝓝[Ici 0] 0) (𝓝 0) := by
      have : Tendsto (fun y : ℝ => c * y ^ 4) (𝓝 0) (𝓝 (c * 0 ^ 4)) :=
        ((continuous_const.mul (continuous_pow 4)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun y : ℝ => -(c * y ^ 4)) (𝓝[Ici 0] 0) (𝓝 0) := by
      simpa using h1.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have := abs_PhiE_le (y := z) hz
      linarith [neg_abs_le (PhiE z)]
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have := abs_PhiE_le (y := z) hz
      linarith [le_abs_self (PhiE z)]
  · exact (hasDerivAt_PhiE h0).continuousAt.continuousWithinAt

theorem continuous_PhiE_comp {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ p, 0 ≤ f p) :
    Continuous fun p => PhiE (f p) :=
  continuousOn_PhiE.comp_continuous hf hf0

theorem abs_PhiE_le' {y : ℝ} (hy : 0 ≤ y) : |PhiE y| ≤ 1 + KPhiE := by
  rcases eq_or_lt_of_le hy with h0 | h0
  · rw [← h0, PhiE_zero]; have := KPhiE_nonneg; simp; linarith
  · exact abs_PhiE_bound h0

/-- `∫_{BZ} (1 + T√λ)^{-3} ≤ π² Ia(3)/(4T²)`. -/
theorem intBZ_dec3 (hT : 0 < T) :
    ∫ p in BZ, ((1 + T * √(lamC p)) ^ 3)⁻¹ ≤ π ^ 2 * Ia 3 / (4 * T ^ 2) := by
  have hpi := pi_pos
  have ha : 0 < 2 * T / π := by positivity
  have hint := (integrable_decay_scale (α := 3) (by norm_num) ha).integrableOn (s := BZ)
  have hle : ∀ p ∈ BZ, ((1 + T * √(lamC p)) ^ 3)⁻¹ ≤ (1 + 2 * T / π * ‖p‖) ^ (-(3 : ℝ)) := by
    intro p hp
    rw [one_add_rpow_neg_three (by positivity)]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have := sqrt_lamC_ge hp
    have : 2 * T / π * ‖p‖ ≤ T * √(lamC p) := by
      calc 2 * T / π * ‖p‖ = T * (2 / π * ‖p‖) := by ring
        _ ≤ T * √(lamC p) := by gcongr
    linarith
  have hmeas : Continuous fun p : ℂ => ((1 + T * √(lamC p)) ^ 3)⁻¹ := by
    have hl := continuous_lamC
    refine Continuous.inv₀ (by fun_prop) (fun p => by positivity)
  calc ∫ p in BZ, ((1 + T * √(lamC p)) ^ 3)⁻¹ ≤ ∫ p in BZ, (1 + 2 * T / π * ‖p‖) ^ (-(3 : ℝ)) :=
        setIntegral_mono_on (hmeas.continuousOn.integrableOn_compact isCompact_BZ) hint
          measurableSet_BZ hle
    _ ≤ Ia 3 / (2 * T / π) ^ 2 := integral_BZ_decay_le (by norm_num) ha
    _ = π ^ 2 * Ia 3 / (4 * T ^ 2) := by field_simp; ring

theorem intBZ_const (c : ℝ) : ∫ _p in BZ, c = (2 * π) ^ 2 * c := by
  rw [setIntegral_const, volume_real_BZ, smul_eq_mul]

/-- `J_Φ(T) = ∫ λ³ Φ(2T√ν)²/ν⁴`. -/
def JPhi (msq T : ℝ) : ℝ := ∫ p in BZ, lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 /
  (lamC p + msq) ^ 4

theorem bdd_PhiE_nu (hm : 0 < msq) (T : ℝ) (hT : 0 ≤ T) :
    Bdd fun p => PhiE (2 * T * √(lamC p + msq)) :=
  ⟨(continuous_PhiE_comp (by have := continuous_lamC; fun_prop)
      (fun p => by positivity)).measurable,
    1 + KPhiE, fun p => abs_PhiE_le' (by positivity)⟩

/-- The constant `C_J`. -/
def CJ : ℝ := Ca * (A0 + 1 + KPhiE) * (π ^ 2 * Ia 3 / 4 + (2 * π) ^ 2)

/-- **`|J(T) - J_Φ(T)| ≤ C_J/T²`.** -/
theorem JT_sub_JPhi (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T) :
    |JT msq T - JPhi msq T| ≤ CJ / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hpi := pi_pos
  have ha := bdd_aT hm hm1 hT
  have hP := bdd_PhiE_nu hm T hT0.le
  have hνi := bdd_nu_inv hm
  have hCa := Ca_nonneg
  have hA0 := A0_nonneg
  have hK := KPhiE_nonneg
  have hJ1 : Bdd fun p => lamC p ^ 3 * aT msq T p ^ 2 / (lamC p + msq) ^ 4 :=
    ((bdd_lamC.pow 3).mul (ha.pow 2)).mul (hνi.pow 4) |>.congr fun p => by
      rw [inv_pow, ← div_eq_mul_inv]
  have hJ2 : Bdd fun p => lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4 :=
    ((bdd_lamC.pow 3).mul (hP.pow 2)).mul (hνi.pow 4) |>.congr fun p => by
      rw [inv_pow, ← div_eq_mul_inv]
  set B : ℂ → ℝ := fun p => Ca * (A0 + 1 + KPhiE) * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹)
  have hBc : Continuous B := by
    have := continuous_lamC
    refine continuous_const.mul ((Continuous.inv₀ (by fun_prop) (fun p => by positivity)).add
      continuous_const)
  have hpt : ∀ p, |lamC p ^ 3 * aT msq T p ^ 2 / (lamC p + msq) ^ 4 -
      lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4| ≤ B p := by
    intro p
    have hl := lamC_nonneg p
    have hν : 0 < lamC p + msq := by linarith
    have hP' := abs_PhiE_le' (y := 2 * T * √(lamC p + msq)) (by positivity)
    have hd := aT_vs_PhiE hm hm1 hT p
    have hab := abs_aT_le hm hm1 hT p
    have e : lamC p ^ 3 * aT msq T p ^ 2 / (lamC p + msq) ^ 4 -
        lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4 =
        lamC p ^ 3 / (lamC p + msq) ^ 4 * ((aT msq T p - PhiE (2 * T * √(lamC p + msq))) *
          (aT msq T p + PhiE (2 * T * √(lamC p + msq)))) := by ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg (by positivity)]
    have hl3 : lamC p ^ 3 / (lamC p + msq) ^ 4 ≤ (lamC p + msq)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      calc lamC p ^ 3 ≤ (lamC p + msq) ^ 3 := pow_le_pow_left₀ hl (by linarith) 3
        _ = (lamC p + msq)⁻¹ * (lamC p + msq) ^ 4 := by field_simp
    have hsum : |aT msq T p + PhiE (2 * T * √(lamC p + msq))| ≤ A0 + 1 + KPhiE :=
      (abs_add_le _ _).trans (by linarith)
    calc lamC p ^ 3 / (lamC p + msq) ^ 4 * (|aT msq T p - PhiE (2 * T * √(lamC p + msq))| *
          |aT msq T p + PhiE (2 * T * √(lamC p + msq))|)
        ≤ (lamC p + msq)⁻¹ * (Ca * (lamC p + msq) *
            (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) * (A0 + 1 + KPhiE)) := by gcongr
      _ = B p := by simp only [B]; field_simp
  unfold JT JPhi
  rw [← integral_sub hJ1.integrableOn hJ2.integrableOn, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hBc.continuousOn.integrableOn_compact isCompact_BZ)
    (ae_restrict_of_forall_mem measurableSet_BZ fun p _ => by
      rw [Real.norm_eq_abs]; exact hpt p)).trans ?_
  simp only [B]
  rw [integral_const_mul, integral_add ((Continuous.inv₀ (by have := continuous_lamC; fun_prop)
    (fun p => by positivity)).continuousOn.integrableOn_compact isCompact_BZ)
    (continuous_const.continuousOn.integrableOn_compact isCompact_BZ), intBZ_const]
  have h3 := intBZ_dec3 hT0
  unfold CJ
  have hc : 0 ≤ Ca * (A0 + 1 + KPhiE) := by positivity
  calc Ca * (A0 + 1 + KPhiE) * ((∫ p in BZ, ((1 + T * √(lamC p)) ^ 3)⁻¹) + (2 * π) ^ 2 * (T ^ 2)⁻¹)
      ≤ Ca * (A0 + 1 + KPhiE) * (π ^ 2 * Ia 3 / (4 * T ^ 2) + (2 * π) ^ 2 * (T ^ 2)⁻¹) := by gcongr
    _ = _ := by field_simp

end

end Step2.D2
