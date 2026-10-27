import Step2.D2.D2Sh7
import Step2.D2.D2Bv9

/-!
# Sharp line 3, part 8: `𝔅(w_T) = (2π)^{-2} (J(T) + S(T))`

* `J(T) = ∫ λ³ a_T²/ν⁴`, `S(T) = ∫ R (ĉ_T²/2 - λ² a_T²/(4ν⁴))`, `R = (2-2cos p₀)² + (2-2cos p₁)²`;
* `frakBT_JS`: `frakBT = (2π)^{-2} (J + S)`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

variable {msq T : ℝ}

theorem measurable_tl (msq T : ℝ) : Measurable (tl msq T) := by
  have hu := measurable_uncurry_of_continuous_of_measurable
    (u := fun (p : ℂ) (τ : ℝ) => τ * Pd τ (uhatC msq p))
    (fun τ => continuous_const.mul ((Polynomial.continuous _).comp (continuous_uhatC msq)))
    (fun p => measurable_id.mul (measurable_Pd _))
  exact (hu.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi T))).measurable

theorem measurable_aT (msq T : ℝ) : Measurable (aT msq T) := by
  unfold aT
  exact measurable_const.add (((continuous_uhatC msq).measurable.pow_const 2).mul (measurable_tl msq T))

/-- The uniform bound of `a_T`. -/
def A0 : ℝ := 1 + KPhiE + 18 * Ca

theorem A0_nonneg : 0 ≤ A0 := by have := KPhiE_nonneg; have := Ca_nonneg; unfold A0; positivity

theorem abs_aT_le (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T) (p : ℂ) : |aT msq T p| ≤ A0 := by
  have h := aT_vs_PhiE hm hm1 hT p
  have hl := lamC_nonneg p
  have hl8 := lamC_le_eight p
  have hν : lamC p + msq ≤ 9 := by linarith
  have hT0 : 0 < T := by linarith
  have hy : 0 ≤ 2 * T * √(lamC p + msq) := by positivity
  have hP : |PhiE (2 * T * √(lamC p + msq))| ≤ 1 + KPhiE := by
    rcases eq_or_lt_of_le hy with h0 | h0
    · rw [← h0]
      have := abs_PhiE_le (y := 0) le_rfl
      have := KPhiE_nonneg
      simp at this ⊢; linarith
    · exact abs_PhiE_bound h0
  have hI1 : ((1 + T * √(lamC p)) ^ 3)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by
      have : 0 ≤ T * √(lamC p) := mul_nonneg hT0.le (Real.sqrt_nonneg _)
      linarith))
  have hI2 : (T ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  have hCa := Ca_nonneg
  have hE : Ca * (lamC p + msq) * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) ≤ 18 * Ca := by
    have h1 : ((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹ ≤ 2 := by linarith
    have h2 : 0 ≤ ((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹ := by positivity
    calc Ca * (lamC p + msq) * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) ≤ Ca * 9 * 2 := by
          gcongr
      _ = 18 * Ca := by ring
  have := abs_sub_abs_le_abs_sub (aT msq T p) (PhiE (2 * T * √(lamC p + msq)))
  unfold A0; linarith

theorem bdd_aT (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T) : Bdd (aT msq T) :=
  ⟨measurable_aT msq T, A0, abs_aT_le hm hm1 hT⟩

/-- `R = (2 - 2cos p₀)² + (2 - 2cos p₁)²`. -/
def Rq (p : ℂ) : ℝ := (2 - 2 * Real.cos p.re) ^ 2 + (2 - 2 * Real.cos p.im) ^ 2

theorem bdd_Rq : Bdd Rq := ((((Bdd.const 2).sub ((Bdd.const 2).mul bdd_cos_re)).pow 2).add
    (((Bdd.const 2).sub ((Bdd.const 2).mul bdd_cos_im)).pow 2))

/-- `J(T) = ∫ λ³ a_T²/ν⁴`. -/
def JT (msq T : ℝ) : ℝ := ∫ p in BZ, lamC p ^ 3 * aT msq T p ^ 2 / (lamC p + msq) ^ 4

/-- `S(T) = ∫ R (ĉ_T²/2 - λ² a_T²/(4ν⁴))`. -/
def ST (msq T : ℝ) : ℝ := ∫ p in BZ, Rq p * (chat Pc msq (Ioc 0 T) p ^ 2 / 2 -
  lamC p ^ 2 * aT msq T p ^ 2 / (4 * (lamC p + msq) ^ 4))

theorem aT_swapC (p : ℂ) : aT msq T (swapC p) = aT msq T p := by
  simp [aT, tl, uhatC, lamC_swapC]

/-- **The exact representation.** -/
theorem frakBT_JS {L N : ℕ} [NeZero L] (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T)
    (hn : 2 * (⌊T⌋₊ + 4) < L ^ N) :
    frakBT L N msq T = ((((2 * π) ^ 2)⁻¹ * (JT msq T + ST msq T) : ℝ) : ℂ) := by
  have hT0 : 0 < T := by linarith
  rw [frakBT_eq hm hT0 hn]
  congr 2
  set c := chat Pc msq (Ioc 0 T)
  have hc := bdd_chat hm hT0.le
  have ha := bdd_aT hm hm1 hT
  have hνi := bdd_nu_inv hm
  -- `I₁ = ∫ R/2 ĉ²`
  have hsym1 := integral_sin_sq_sym (g := fun p => 4 * c p ^ 2)
    (fun p => by simp [c, chat_swapC])
    (((Bdd.const 4).mul (hc.pow 2)).mul (bdd_sin_re.pow 2)).integrableOn
    (((Bdd.const 4).mul (hc.pow 2)).mul (bdd_sin_im.pow 2)).integrableOn
  have hI1 : ∫ p in BZ, (2 * lamC p - 4 * Real.sin p.re ^ 2) * c p ^ 2 =
      ∫ p in BZ, Rq p / 2 * c p ^ 2 := by
    have e1 : (fun p => (2 * lamC p - 4 * Real.sin p.re ^ 2) * c p ^ 2) =
        fun p => 2 * lamC p * c p ^ 2 - 4 * c p ^ 2 * Real.sin p.re ^ 2 := by funext p; ring
    have hX : Bdd fun p => 4 * c p ^ 2 * ((Real.sin p.re ^ 2 + Real.sin p.im ^ 2) / 2) :=
      (((Bdd.const 4).mul (hc.pow 2)).mul ((bdd_sin_re.pow 2).add (bdd_sin_im.pow 2))).mul
        (Bdd.const (1 / 2)) |>.congr fun p => by ring
    have hY : Bdd fun p => 2 * lamC p * c p ^ 2 := (((Bdd.const 2).mul bdd_lamC).mul (hc.pow 2))
    have hZ : Bdd fun p => 4 * c p ^ 2 * Real.sin p.re ^ 2 :=
      (((Bdd.const 4).mul (hc.pow 2)).mul (bdd_sin_re.pow 2))
    rw [e1, integral_sub hY.integrableOn hZ.integrableOn, hsym1,
      ← integral_sub hY.integrableOn hX.integrableOn]
    refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
    simp only [Rq]
    rw [sin_sq_add_sin_sq]; ring
  -- `I₂ = ∫ λ² a_T²/ν⁴ (λ - R/4)`
  set G : ℂ → ℝ := fun p => 2 * lamC p ^ 2 * aT msq T p ^ 2 * ((lamC p + msq)⁻¹) ^ 4
  have hG : Bdd G := (((Bdd.const 2).mul (bdd_lamC.pow 2)).mul (ha.pow 2)).mul (hνi.pow 4)
  have hsym2 := integral_sin_sq_sym (g := G) (fun p => by simp [G, lamC_swapC, aT_swapC])
    (hG.mul (bdd_sin_re.pow 2)).integrableOn (hG.mul (bdd_sin_im.pow 2)).integrableOn
  have hI2 : ∫ p in BZ, lamC p ^ 2 / 2 * dchat msq T p ^ 2 =
      ∫ p in BZ, G p * ((Real.sin p.re ^ 2 + Real.sin p.im ^ 2) / 2) := by
    rw [← hsym2]
    refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
    have hl := lamC_nonneg p
    have hν : lamC p + msq ≠ 0 := by linarith
    simp only [G]
    rw [dchat_eq_aT hm hT0 p]
    field_simp
  rw [hI1, hI2]
  -- regroup
  have hJ : Bdd fun p => lamC p ^ 3 * aT msq T p ^ 2 / (lamC p + msq) ^ 4 :=
    ((bdd_lamC.pow 3).mul (ha.pow 2)).mul (hνi.pow 4) |>.congr fun p => by
      rw [inv_pow, ← div_eq_mul_inv]
  have hS : Bdd fun p => Rq p * (c p ^ 2 / 2 -
      lamC p ^ 2 * aT msq T p ^ 2 / (4 * (lamC p + msq) ^ 4)) :=
    bdd_Rq.mul (((hc.pow 2).mul (Bdd.const (1 / 2))).sub
      ((((bdd_lamC.pow 2).mul (ha.pow 2)).mul (hνi.pow 4)).mul (Bdd.const (1 / 4))))
      |>.congr fun p => by
        have hl := lamC_nonneg p
        have hν : lamC p + msq ≠ 0 := by linarith
        simp only [c]
        field_simp
  have hR2 : Bdd fun p => Rq p / 2 * c p ^ 2 := (bdd_Rq.mul (Bdd.const (1 / 2))).mul (hc.pow 2)
    |>.congr fun p => by ring
  have hGs : Bdd fun p => G p * ((Real.sin p.re ^ 2 + Real.sin p.im ^ 2) / 2) :=
    (hG.mul ((bdd_sin_re.pow 2).add (bdd_sin_im.pow 2))).mul (Bdd.const (1 / 2))
      |>.congr fun p => by ring
  unfold JT ST
  rw [← integral_add hR2.integrableOn hGs.integrableOn,
    ← integral_add hJ.integrableOn hS.integrableOn]
  refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
  have hl := lamC_nonneg p
  have hν : lamC p + msq ≠ 0 := by linarith
  simp only [G, Rq]
  rw [sin_sq_add_sin_sq]
  field_simp
  ring

end

end Step2.D2
