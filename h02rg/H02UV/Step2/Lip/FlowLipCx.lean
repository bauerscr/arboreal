import Step2.Lip.FlowLipHist

/-!
# Elementary complex estimates for the normalisation (Lipschitz bounds, part 10)

The principal square root has nonnegative real part (`re_csq_nonneg`); hence for `|ζ| ≤ 1/8`,
`r = (1 + ζ)^{1/2}` satisfies `|r - 1| ≤ |ζ|`, and `ζ ↦ r`, `ζ ↦ 1/r`, `ζ ↦ r/|r|` are Lipschitz
(`csq_lip`, `inv_csq_lip`, `phase_csq_lip`).
-/

namespace Step2

noncomputable section

theorem re_csq_nonneg (w : ℂ) : 0 ≤ (csq w).re := by
  unfold csq
  rw [Complex.cpow_def]
  split_ifs with h0 h1
  · simp
  · simp
  · rw [Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
    · have : (Complex.log w * 2⁻¹).im = Complex.arg w / 2 := by
        simp [Complex.log_im]; ring
      rw [this]; linarith [Complex.neg_pi_lt_arg w]
    · have : (Complex.log w * 2⁻¹).im = Complex.arg w / 2 := by
        simp [Complex.log_im]; ring
      rw [this]; linarith [Complex.arg_le_pi w]

theorem norm_add_one_ge_one_of_re {r : ℂ} (hr : 0 ≤ r.re) : 1 ≤ ‖r + 1‖ := by
  have h := Complex.abs_re_le_norm (r + 1)
  have : (r + 1).re = r.re + 1 := by simp
  rw [this, abs_of_nonneg (by linarith)] at h
  linarith

/-- `|(1 + ζ)^{1/2} - 1| ≤ |ζ|`. -/
theorem norm_csq_sub_one_le (ζ : ℂ) : ‖csq (1 + ζ) - 1‖ ≤ ‖ζ‖ := by
  have h1 : (csq (1 + ζ) - 1) * (csq (1 + ζ) + 1) = ζ := by
    have := csq_sq (1 + ζ); linear_combination this
  have h2 := norm_add_one_ge_one_of_re (re_csq_nonneg (1 + ζ))
  calc ‖csq (1 + ζ) - 1‖ ≤ ‖csq (1 + ζ) - 1‖ * ‖csq (1 + ζ) + 1‖ :=
        le_mul_of_one_le_right (norm_nonneg _) h2
    _ = ‖ζ‖ := by rw [← norm_mul, h1]

theorem re_csq_ge {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 8) : 7 / 8 ≤ (csq (1 + ζ)).re := by
  have h1 := norm_csq_sub_one_le ζ
  have h2 := Complex.abs_re_le_norm (csq (1 + ζ) - 1)
  have : (csq (1 + ζ) - 1).re = (csq (1 + ζ)).re - 1 := by simp
  rw [this] at h2
  have := (abs_le.1 (h2.trans h1)).1
  linarith

theorem norm_csq_ge {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 8) : 7 / 8 ≤ ‖csq (1 + ζ)‖ :=
  (re_csq_ge h).trans (Complex.re_le_norm _)

/-- **Lipschitz bound for the square root.** -/
theorem csq_lip {ζ ζ' : ℂ} (h : ‖ζ‖ ≤ 1 / 8) (h' : ‖ζ'‖ ≤ 1 / 8) :
    ‖csq (1 + ζ) - csq (1 + ζ')‖ ≤ ‖ζ - ζ'‖ := by
  have e : (csq (1 + ζ) - csq (1 + ζ')) * (csq (1 + ζ) + csq (1 + ζ')) = ζ - ζ' := by
    have h1 := csq_sq (1 + ζ); have h2 := csq_sq (1 + ζ'); linear_combination h1 - h2
  have hr : 1 ≤ ‖csq (1 + ζ) + csq (1 + ζ')‖ := by
    have h1 := re_csq_ge h; have h2 := re_csq_ge h'
    have h3 := Complex.re_le_norm (csq (1 + ζ) + csq (1 + ζ'))
    simp only [Complex.add_re] at h3
    linarith
  calc ‖csq (1 + ζ) - csq (1 + ζ')‖ ≤ ‖csq (1 + ζ) - csq (1 + ζ')‖ *
        ‖csq (1 + ζ) + csq (1 + ζ')‖ := le_mul_of_one_le_right (norm_nonneg _) hr
    _ = ‖ζ - ζ'‖ := by rw [← norm_mul, e]

theorem csq_ne_zero {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 8) : csq (1 + ζ) ≠ 0 := by
  intro h0; have := norm_csq_ge h; rw [h0, norm_zero] at this; linarith

/-- **Lipschitz bound for the inverse square root.** -/
theorem inv_csq_lip {ζ ζ' : ℂ} (h : ‖ζ‖ ≤ 1 / 8) (h' : ‖ζ'‖ ≤ 1 / 8) :
    ‖(csq (1 + ζ))⁻¹ - (csq (1 + ζ'))⁻¹‖ ≤ 2 * ‖ζ - ζ'‖ := by
  have hr := csq_ne_zero h
  have hr' := csq_ne_zero h'
  have e : (csq (1 + ζ))⁻¹ - (csq (1 + ζ'))⁻¹ =
      (csq (1 + ζ') - csq (1 + ζ)) / (csq (1 + ζ) * csq (1 + ζ')) := by
    field_simp
  rw [e, norm_div, norm_mul, norm_sub_rev]
  have h1 := norm_csq_ge h
  have h2 := norm_csq_ge h'
  have h3 := csq_lip h h'
  rw [div_le_iff₀ (by positivity)]
  have : (49 / 64 : ℝ) ≤ ‖csq (1 + ζ)‖ * ‖csq (1 + ζ')‖ := by nlinarith
  nlinarith [norm_nonneg (ζ - ζ')]

end

end Step2
