import Step2.D2.D2Bv5

/-!
# Integral estimates for `𝔅(w_T)` (`prop:d2`, line 3): tools

* `swapC`, `setIntegral_BZ_swap`: the reflection `p₀ ↔ p₁` preserves `∫_{[-π,π]²}`;
* `chat_nonneg`, `lam_chat_le_one`: `0 ≤ ĉ_T`, `λ ĉ_T ≤ 1`;
* `measurable_dchat`;
* `integral_BZ_decay_T`: `∫_{[-π,π]²} T²(1 + T|p|)^{-α} ≤ Ia(α)`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- The reflection `(p₀, p₁) ↦ (p₁, p₀)`. -/
def swapC (p : ℂ) : ℂ := ⟨p.im, p.re⟩

theorem measurePreserving_swapC : MeasurePreserving swapC volume volume := by
  have h1 := Complex.volume_preserving_equiv_real_prod
  have h2 : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap
  have := (h1.symm).comp (h2.comp h1)
  convert this using 1

theorem measurableEmbedding_swapC : MeasurableEmbedding swapC := by
  have : swapC = Complex.measurableEquivRealProd.symm ∘ Prod.swap ∘
      Complex.measurableEquivRealProd := by
    funext p; rfl
  rw [this]
  exact (Complex.measurableEquivRealProd.symm.measurableEmbedding).comp
    ((MeasurableEquiv.prodComm.measurableEmbedding).comp
      Complex.measurableEquivRealProd.measurableEmbedding)

theorem swapC_preimage_BZ : swapC ⁻¹' BZ = BZ := by
  ext p; simp [BZ, swapC, and_comm]

theorem setIntegral_BZ_swap (g : ℂ → ℝ) : ∫ p in BZ, g (swapC p) = ∫ p in BZ, g p := by
  have := measurePreserving_swapC.setIntegral_preimage_emb measurableEmbedding_swapC g BZ
  rwa [swapC_preimage_BZ] at this

theorem lamC_swapC (p : ℂ) : lamC (swapC p) = lamC p := by
  simp [lamC, swapC]; ring

theorem chat_swapC (msq : ℝ) (S : Set ℝ) (p : ℂ) : chat Pc msq S (swapC p) = chat Pc msq S p := by
  simp [chat, uhatC, lamC_swapC]

/-- **Symmetrization.** For `g` invariant under `p₀ ↔ p₁`:
`∫ g sin² p₀ = ∫ g (sin² p₀ + sin² p₁)/2`. -/
theorem integral_sin_sq_sym {g : ℂ → ℝ} (hg : ∀ p, g (swapC p) = g p)
    (hi : IntegrableOn (fun p => g p * Real.sin p.re ^ 2) BZ)
    (hi' : IntegrableOn (fun p => g p * Real.sin p.im ^ 2) BZ) :
    ∫ p in BZ, g p * Real.sin p.re ^ 2 =
      ∫ p in BZ, g p * ((Real.sin p.re ^ 2 + Real.sin p.im ^ 2) / 2) := by
  have h1 : ∫ p in BZ, g p * Real.sin p.im ^ 2 = ∫ p in BZ, g p * Real.sin p.re ^ 2 := by
    rw [← setIntegral_BZ_swap]
    refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
    rw [hg]; rfl
  have e : (fun p => g p * ((Real.sin p.re ^ 2 + Real.sin p.im ^ 2) / 2)) =
      fun p => (g p * Real.sin p.re ^ 2 + g p * Real.sin p.im ^ 2) / 2 := by funext p; ring
  rw [e, integral_div, integral_add hi hi', h1]; ring

/-- `sin² p₀ + sin² p₁ = λ - (λ₀² + λ₁²)/4`. -/
theorem sin_sq_add_sin_sq (p : ℂ) :
    Real.sin p.re ^ 2 + Real.sin p.im ^ 2 = lamC p -
      ((2 - 2 * Real.cos p.re) ^ 2 + (2 - 2 * Real.cos p.im) ^ 2) / 4 := by
  have h1 := Real.sin_sq_add_cos_sq p.re
  have h2 := Real.sin_sq_add_cos_sq p.im
  simp only [lamC]; nlinarith

theorem lamC_parts_le (p : ℂ) :
    0 ≤ (2 - 2 * Real.cos p.re) ^ 2 + (2 - 2 * Real.cos p.im) ^ 2 ∧
      (2 - 2 * Real.cos p.re) ^ 2 + (2 - 2 * Real.cos p.im) ^ 2 ≤ lamC p ^ 2 := by
  have h1 := two_sub_two_cos_nonneg p.re
  have h2 := two_sub_two_cos_nonneg p.im
  constructor
  · positivity
  · simp only [lamC]; nlinarith

/-! ### `ĉ_T` -/

variable {msq T : ℝ}

theorem chat_bounds (hm : 0 < msq) (hT : 0 ≤ T) (p : ℂ) :
    0 ≤ chat Pc msq (Ioc 0 T) p ∧ chat Pc msq (Ioc 0 T) p * (lamC p + msq) ≤ 1 := by
  have hν : 0 < lamC p + msq := by have := lamC_nonneg p; linarith
  have hu : 0 < uhatC msq p := (uhatC_mem_Ioo hm p).1
  obtain ⟨h0, h1⟩ := ehat_mem Pc hm.le hT hu
  rw [chat_zero_eq hm.le hT hν]
  refine ⟨div_nonneg h0 hν.le, ?_⟩
  rw [div_mul_cancel₀ _ hν.ne']; exact h1

theorem measurable_dchat (msq T : ℝ) : Measurable (dchat msq T) := by
  have hu := measurable_uncurry_of_continuous_of_measurable
    (u := fun (p : ℂ) (τ : ℝ) => τ * Pd τ (uhatC msq p))
    (fun τ => continuous_const.mul ((Polynomial.continuous _).comp (continuous_uhatC msq)))
    (fun p => measurable_id.mul (measurable_Pd _))
  have h2 := hu.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc 0 T))
  unfold dchat
  exact (measurable_const.mul h2.measurable).mul
    ((measurable_const.mul (Real.measurable_sin.comp Complex.measurable_re)).div_const _)

theorem measurable_chat' (msq T : ℝ) : Measurable (chat Pc msq (Ioc 0 T)) :=
  measurable_chat Pc msq _

/-- `∫_{[-π,π]²} T² (1 + T|p|)^{-α} ≤ Ia(α)`. -/
theorem integral_BZ_decay_T {α : ℝ} (hα : 2 < α) {T : ℝ} (hT : 0 < T) :
    ∫ p in BZ, T ^ 2 * (1 + T * ‖p‖) ^ (-α) ≤ Ia α := by
  rw [integral_const_mul]
  have := integral_BZ_decay_le hα hT
  calc T ^ 2 * ∫ p in BZ, (1 + T * ‖p‖) ^ (-α) ≤ T ^ 2 * (Ia α / T ^ 2) := by gcongr
    _ = Ia α := by field_simp

theorem integrableOn_decay_T {α : ℝ} (hα : 2 < α) {T : ℝ} (hT : 0 < T) (C : ℝ) :
    IntegrableOn (fun p : ℂ => C * (T ^ 2 * (1 + T * ‖p‖) ^ (-α))) BZ :=
  (((integrable_decay_scale hα hT).const_mul (T ^ 2)).const_mul C).integrableOn

/-- `1 ≤ (1 + a)^α (1 + a·b)^{-α}`-type bound: if `T|p| ≤ c` then
`1 ≤ (1 + c)^α (1 + T|p|)^{-α}`. -/
theorem one_le_decay {α c x : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ x) (hxc : x ≤ c) :
    1 ≤ (1 + c) ^ α * (1 + x) ^ (-α) := by
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
  exact Real.rpow_le_rpow (by linarith) (by linarith) hα

/-- If `1 ≤ x` then `x^{-k} ≤ 2^α (1 + x)^{-α}` for `α ≤ k`. -/
theorem inv_pow_le_decay {k : ℕ} {α x : ℝ} (hα : 0 ≤ α) (hαk : α ≤ k) (hx : 1 ≤ x) :
    (x ^ k)⁻¹ ≤ 2 ^ α * (1 + x) ^ (-α) := by
  have hx0 : 0 < x := by linarith
  have h1 : (x ^ k)⁻¹ ≤ x ^ (-α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2 : x ^ (-α) ≤ 2 ^ α * (1 + x) ^ (-α) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_neg (by linarith), ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity),
      ← Real.mul_rpow (by norm_num) hx0.le]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hα
  exact h1.trans h2

end

end Step2.D2
