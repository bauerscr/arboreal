import Step2.D2.D2Bv7

/-!
# Integral estimates for `𝔅(w_T)` (`prop:d2`, line 3): the main term

* `ptM`: `|χ λ³/ν⁴ - 1_{T^{-1} < |p| < π} |p|^{-2}| ≤ 1 + C_M T² (1 + T|p|)^{-4}` on `[-π,π]²`
  (for `m² ≤ T^{-2}`);
* `integral_gA`: `∫_{[-π,π]²} 1_{T^{-1} < |p| < π} |p|^{-2} = 2π (log π + log T)`;
* `Bdd`: bounded measurable functions (integrable on `[-π,π]²`).
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real

theorem rpow_four_eq (c : ℝ) : c ^ (4 : ℝ) = c ^ 4 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The annulus profile `1_{T^{-1} < y < π} y^{-2}`. -/
def gR (T y : ℝ) : ℝ := if T⁻¹ < y ∧ y < π then (y ^ 2)⁻¹ else 0

/-- The constant `C_M`. -/
def CM : ℝ := 64 * (π ^ 2 / 4) ^ 2 + (1 + π) ^ 4

theorem CM_nonneg : 0 ≤ CM := by have := pi_pos; unfold CM; positivity

theorem quartic_gap {l m : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) :
    l * (l + m) ^ 4 - l ^ 5 ≤ 4 * m * (l + m) ^ 4 := by
  have h1 : (l + m) ^ 4 - l ^ 4 ≤ 4 * m * (l + m) ^ 3 := by
    nlinarith [mul_nonneg hl hm, mul_nonneg (mul_nonneg hl hm) hm, mul_nonneg (mul_nonneg hl hl) hm,
      pow_nonneg hm 4, mul_nonneg (mul_nonneg hl hm) (mul_nonneg hl hm),
      mul_nonneg (mul_nonneg (mul_nonneg hl hl) hl) hm, mul_nonneg (mul_nonneg (mul_nonneg hl hm) hm) hm,
      mul_nonneg (mul_nonneg (mul_nonneg hl hl) hm) hm]
  have h2 : l * ((l + m) ^ 4 - l ^ 4) ≤ l * (4 * m * (l + m) ^ 3) := mul_le_mul_of_nonneg_left h1 hl
  have h3 : l * (4 * m * (l + m) ^ 3) ≤ (l + m) * (4 * m * (l + m) ^ 3) := by
    have : 0 ≤ 4 * m * (l + m) ^ 3 := by positivity
    nlinarith
  nlinarith

/-- **The main-term comparison**, real-variable form. -/
theorem ptM {T lam msq np : ℝ} (hT : 1 ≤ T) (hm : 0 < msq) (hmT : msq ≤ (T ^ 2)⁻¹)
    (hnp : 0 ≤ np) (hlp : 4 / π ^ 2 * np ^ 2 ≤ lam) (hlu : lam ≤ np ^ 2)
    (hgap : np ^ 2 - lam ≤ (np ^ 2) ^ 2 / 4) :
    |chiT T (lam + msq) * lam ^ 3 / (lam + msq) ^ 4 - gR T np| ≤
      1 + CM * (T ^ 2 * (1 + T * np) ^ (-(4 : ℝ))) := by
  have hpi := pi_pos
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ lam := le_trans (by positivity) hlp
  set ν := lam + msq with hνdef
  have hν : 0 < ν := by linarith
  have hlν : lam ≤ ν := by linarith
  set D := T ^ 2 * (1 + T * np) ^ (-(4 : ℝ)) with hD
  have hD0 : 0 ≤ D := by positivity
  have hCM := CM_nonneg
  -- `0 ≤ f ≤ 1/ν`
  have hf0 : 0 ≤ chiT T ν * lam ^ 3 / ν ^ 4 := by unfold chiT; split_ifs <;> positivity
  have hfν : ∀ hχ : (T ^ 2)⁻¹ < ν, chiT T ν * lam ^ 3 / ν ^ 4 = lam ^ 3 / ν ^ 4 := by
    intro hχ; unfold chiT; rw [if_pos hχ, one_mul]
  have hl3 : lam ^ 3 / ν ^ 4 ≤ ν⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    calc lam ^ 3 ≤ ν ^ 3 := pow_le_pow_left₀ hl0 hlν 3
      _ = ν⁻¹ * ν ^ 4 := by field_simp
  rcases le_or_gt (T * np) π with hs | hs
  · -- `T|p| ≤ π`: both terms in `[0, T²]`
    have hfT : chiT T ν * lam ^ 3 / ν ^ 4 ≤ T ^ 2 := by
      unfold chiT; split_ifs with hχ
      · rw [one_mul]
        refine hl3.trans (le_of_lt ?_)
        rwa [inv_lt_comm₀ hν (by positivity)]
      · simp; positivity
    have hg0 : 0 ≤ gR T np := by unfold gR; split_ifs <;> positivity
    have hgT : gR T np ≤ T ^ 2 := by
      unfold gR; split_ifs with h
      · have h1 : T⁻¹ ^ 2 < np ^ 2 := pow_lt_pow_left₀ h.1 (by positivity) two_ne_zero
        rw [inv_le_comm₀ (by nlinarith [inv_pos.2 hT0]) (by positivity), ← inv_pow]; exact h1.le
      · positivity
    have h2 := one_le_decay (α := 4) (c := π) (x := T * np) (by norm_num) (by positivity) hs
    rw [rpow_four_eq] at h2
    have hT2 : T ^ 2 ≤ CM * D := by
      rw [hD]
      calc T ^ 2 = T ^ 2 * 1 := by ring
        _ ≤ T ^ 2 * ((1 + π) ^ 4 * (1 + T * np) ^ (-(4 : ℝ))) := by gcongr
        _ ≤ T ^ 2 * (CM * (1 + T * np) ^ (-(4 : ℝ))) := by
            gcongr; unfold CM; have : 0 ≤ 64 * (π ^ 2 / 4) ^ 2 := by positivity
            linarith
        _ = CM * (T ^ 2 * (1 + T * np) ^ (-(4 : ℝ))) := by ring
    rw [abs_le]; constructor <;> linarith
  · -- `T|p| > π`
    have hnp0 : 0 < np := by
      by_contra h; push Not at h
      have : T * np ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hT0.le h
      linarith
    have hpi3 := pi_gt_three
    have hTp1 : 1 ≤ T * np := by linarith
    have hl0' : 0 < lam := lt_of_lt_of_le (by positivity) hlp
    -- `χ = 1`
    have hχ : (T ^ 2)⁻¹ < ν := by
      have h1 : π ^ 2 < (T * np) ^ 2 := pow_lt_pow_left₀ hs hpi.le two_ne_zero
      have h2 : 4 < 4 / π ^ 2 * (T * np) ^ 2 := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]; nlinarith
      have h3 : (T ^ 2)⁻¹ < lam := by
        rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
        calc (1 : ℝ) < 4 / π ^ 2 * (T * np) ^ 2 := by linarith
          _ = T ^ 2 * (4 / π ^ 2 * np ^ 2) := by ring
          _ ≤ lam * T ^ 2 := by rw [mul_comm lam]; gcongr
      linarith
    rw [hfν hχ]
    have hq : 1 / lam ≤ π ^ 2 / 4 * (np ^ 2)⁻¹ := by
      rw [one_div]; exact nu_inv_le hlp le_rfl hnp0
    have hfl : 0 ≤ 1 / lam - lam ^ 3 / ν ^ 4 := by
      have : lam ^ 3 / ν ^ 4 ≤ 1 / lam := by
        rw [div_le_div_iff₀ (by positivity) hl0']
        have : lam ^ 4 ≤ ν ^ 4 := pow_le_pow_left₀ hl0 hlν 4
        nlinarith
      linarith
    have hpi4 : π ^ 2 / 4 / 4 ≤ 1 := by
      have := pi_lt_four; nlinarith
    unfold gR
    split_ifs with hg
    · -- inside the disc
      have hdiff1 : 1 / lam - lam ^ 3 / ν ^ 4 ≤ 64 * (π ^ 2 / 4) ^ 2 * D := by
        have e : 1 / lam - lam ^ 3 / ν ^ 4 = (lam * ν ^ 4 - lam ^ 5) / (lam ^ 2 * ν ^ 4) := by
          field_simp
        have hk := quartic_gap hl0 hm.le
        rw [← hνdef] at hk
        have h1 : 1 / lam - lam ^ 3 / ν ^ 4 ≤ 4 * msq * (1 / lam) ^ 2 := by
          rw [e, div_le_iff₀ (by positivity)]
          calc lam * ν ^ 4 - lam ^ 5 ≤ 4 * msq * ν ^ 4 := hk
            _ = 4 * msq * (1 / lam) ^ 2 * (lam ^ 2 * ν ^ 4) := by field_simp
        have h2 : 4 * msq * (1 / lam) ^ 2 ≤ 4 * (T ^ 2)⁻¹ * (π ^ 2 / 4 * (np ^ 2)⁻¹) ^ 2 := by
          gcongr
        have h3 : 4 * (T ^ 2)⁻¹ * (π ^ 2 / 4 * (np ^ 2)⁻¹) ^ 2 =
            4 * (π ^ 2 / 4) ^ 2 * (T ^ 2 * ((T * np) ^ 4)⁻¹) := by field_simp
        have h4 := inv_pow_le_decay (k := 4) (α := 4) (by norm_num) (by norm_num) hTp1
        rw [rpow_four_eq, show (2 : ℝ) ^ 4 = 16 by norm_num] at h4
        have h5 : T ^ 2 * ((T * np) ^ 4)⁻¹ ≤ 16 * D := by
          have : T ^ 2 * ((T * np) ^ 4)⁻¹ ≤ T ^ 2 * (16 * (1 + T * np) ^ (-(4 : ℝ))) := by
            gcongr
          rw [hD]; linarith
        have h6 : 4 * (π ^ 2 / 4) ^ 2 * (T ^ 2 * ((T * np) ^ 4)⁻¹) ≤
            4 * (π ^ 2 / 4) ^ 2 * (16 * D) := by gcongr
        linarith
      have hdiff2 : 0 ≤ 1 / lam - (np ^ 2)⁻¹ ∧ 1 / lam - (np ^ 2)⁻¹ ≤ π ^ 2 / 4 / 4 := by
        have e : 1 / lam - (np ^ 2)⁻¹ = (np ^ 2 - lam) * (1 / lam) * (np ^ 2)⁻¹ := by
          field_simp
        rw [e]
        constructor
        · have : 0 ≤ np ^ 2 - lam := by linarith
          positivity
        · calc (np ^ 2 - lam) * (1 / lam) * (np ^ 2)⁻¹ ≤ (np ^ 2) ^ 2 / 4 *
                (π ^ 2 / 4 * (np ^ 2)⁻¹) * (np ^ 2)⁻¹ := by
                have : 0 ≤ np ^ 2 - lam := by linarith
                gcongr
            _ = π ^ 2 / 4 / 4 := by field_simp
      have hmd : 64 * (π ^ 2 / 4) ^ 2 * D ≤ CM * D := by
        gcongr; unfold CM; have : 0 ≤ (1 + π) ^ 4 := by positivity
        linarith
      rw [abs_le]; constructor <;> linarith [hdiff2.1, hdiff2.2]
    · -- outside the disc: `|p| ≥ π`
      have hnpi : π ≤ np := by
        by_contra h; push Not at h
        refine hg ⟨?_, h⟩
        rw [inv_lt_iff_one_lt_mul₀ hT0]; linarith
      have hf1 : lam ^ 3 / ν ^ 4 ≤ 1 / 4 := by
        have h1 : 1 / lam ≤ 1 / 4 := by
          refine hq.trans ?_
          have : (np ^ 2)⁻¹ ≤ (π ^ 2)⁻¹ := by
            apply inv_anti₀ (by positivity); exact pow_le_pow_left₀ hpi.le hnpi 2
          calc π ^ 2 / 4 * (np ^ 2)⁻¹ ≤ π ^ 2 / 4 * (π ^ 2)⁻¹ := by gcongr
            _ = 1 / 4 := by field_simp
        linarith
      have : 0 ≤ lam ^ 3 / ν ^ 4 := by positivity
      rw [sub_zero, abs_of_nonneg this]
      have : 0 ≤ CM * D := by positivity
      linarith

/-! ### The annulus integral -/

theorem gR_nonneg (T y : ℝ) : 0 ≤ gR T y := by unfold gR; split_ifs <;> positivity

theorem measurable_gR (T : ℝ) : Measurable (gR T) := by
  unfold gR
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt measurable_id measurable_const)

theorem gR_le (hT : 0 < T) (y : ℝ) : gR T y ≤ T ^ 2 := by
  unfold gR; split_ifs with h
  · have h1 : T⁻¹ ^ 2 < y ^ 2 := pow_lt_pow_left₀ h.1 (by positivity) two_ne_zero
    rw [inv_le_comm₀ (by nlinarith [inv_pos.2 hT]) (by positivity), ← inv_pow]; exact h1.le
  · positivity

/-- **The annulus integral.** -/
theorem integral_gR (hT : 1 ≤ T) :
    ∫ p in BZ, gR T ‖p‖ = 2 * π * (Real.log π + Real.log T) := by
  have hpi := pi_pos
  have hT0 : 0 < T := by linarith
  have hTi : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have hpi3 := pi_gt_three
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)]
  swap
  · unfold gR
    rw [if_neg]
    rintro ⟨-, h⟩
    refine hp ⟨?_, ?_⟩
    · exact (Complex.abs_re_le_norm p).trans h.le
    · exact (Complex.abs_im_le_norm p).trans h.le
  rw [integral_radial (gR T)]
  have e : ∫ y in Ioi (0 : ℝ), y * gR T y = ∫ y in Ioo T⁻¹ π, y⁻¹ := by
    have e1 : (fun y => y * gR T y) = (Ioo T⁻¹ π).indicator (fun y => y⁻¹) := by
      funext y
      unfold gR
      by_cases h : T⁻¹ < y ∧ y < π
      · rw [if_pos h, indicator_of_mem (show y ∈ Ioo T⁻¹ π from h)]
        have : y ≠ 0 := (lt_trans (inv_pos.2 hT0) h.1).ne'
        field_simp
      · rw [if_neg h, indicator_of_notMem (show y ∉ Ioo T⁻¹ π from h), mul_zero]
    rw [e1, setIntegral_indicator measurableSet_Ioo]
    rw [inter_eq_right.2 (fun y hy => mem_Ioi.2 (lt_trans (inv_pos.2 hT0) hy.1))]
  rw [e, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    integral_inv_of_pos (inv_pos.2 hT0) hpi, div_inv_eq_mul, Real.log_mul hpi.ne' hT0.ne']

/-! ### Bounded measurable functions -/

/-- Bounded measurable functions on `ℂ`. -/
def Bdd (f : ℂ → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ p, |f p| ≤ C

theorem Bdd.integrableOn {f : ℂ → ℝ} (hf : Bdd f) : IntegrableOn f BZ := by
  obtain ⟨hm, C, hC⟩ := hf
  refine Measure.integrableOn_of_bounded (M := C) isCompact_BZ.measure_lt_top.ne
    hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]; exact hC p

theorem Bdd.const (c : ℝ) : Bdd fun _ => c := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem Bdd.mul {f g : ℂ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun p => f p * g p := by
  obtain ⟨hf, Cf, hCf⟩ := hf
  obtain ⟨hg, Cg, hCg⟩ := hg
  refine ⟨hf.mul hg, Cf * Cg, fun p => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hCf p) (hCg p) (abs_nonneg _) ((abs_nonneg _).trans (hCf p))

theorem Bdd.add {f g : ℂ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun p => f p + g p := by
  obtain ⟨hf, Cf, hCf⟩ := hf
  obtain ⟨hg, Cg, hCg⟩ := hg
  exact ⟨hf.add hg, Cf + Cg, fun p => (abs_add_le _ _).trans (add_le_add (hCf p) (hCg p))⟩

theorem Bdd.neg {f : ℂ → ℝ} (hf : Bdd f) : Bdd fun p => -f p := by
  obtain ⟨hf, Cf, hCf⟩ := hf
  exact ⟨hf.neg, Cf, fun p => by rw [abs_neg]; exact hCf p⟩

theorem Bdd.sub {f g : ℂ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun p => f p - g p := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem Bdd.pow {f : ℂ → ℝ} (hf : Bdd f) (n : ℕ) : Bdd fun p => f p ^ n := by
  induction n with
  | zero => simpa using Bdd.const 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem Bdd.congr {f g : ℂ → ℝ} (hf : Bdd f) (h : ∀ p, f p = g p) : Bdd g := by
  have : f = g := funext h
  rwa [← this]

theorem bdd_lamC : Bdd lamC :=
  ⟨continuous_lamC.measurable, 8, fun p => by
    rw [abs_of_nonneg (lamC_nonneg p)]; exact lamC_le_eight p⟩

theorem bdd_sin_re : Bdd fun p : ℂ => Real.sin p.re :=
  ⟨by fun_prop, 1, fun p => abs_sin_le_one _⟩

theorem bdd_sin_im : Bdd fun p : ℂ => Real.sin p.im :=
  ⟨by fun_prop, 1, fun p => abs_sin_le_one _⟩

theorem bdd_cos_re : Bdd fun p : ℂ => Real.cos p.re :=
  ⟨by fun_prop, 1, fun p => abs_cos_le_one _⟩

theorem bdd_cos_im : Bdd fun p : ℂ => Real.cos p.im :=
  ⟨by fun_prop, 1, fun p => abs_cos_le_one _⟩

theorem bdd_nu_inv {msq : ℝ} (hm : 0 < msq) : Bdd fun p => (lamC p + msq)⁻¹ := by
  refine ⟨(continuous_lamC.measurable.add_const _).inv, msq⁻¹, fun p => ?_⟩
  have := lamC_nonneg p
  rw [abs_of_pos (inv_pos.2 (by linarith))]
  exact inv_anti₀ hm (by linarith)

theorem bdd_chiT (T msq : ℝ) : Bdd fun p => chiT T (lamC p + msq) := by
  refine ⟨?_, 1, fun p => ?_⟩
  · unfold chiT
    exact Measurable.ite (measurableSet_lt measurable_const
      (continuous_lamC.measurable.add_const _)) measurable_const measurable_const
  · show |chiT T (lamC p + msq)| ≤ 1
    unfold chiT; split_ifs <;> simp

theorem bdd_gR {T : ℝ} (hT : 0 < T) : Bdd fun p : ℂ => gR T ‖p‖ :=
  ⟨(measurable_gR T).comp measurable_norm, T ^ 2, fun p => by
    rw [abs_of_nonneg (gR_nonneg _ _)]; exact gR_le hT _⟩

end

end Step2.D2
