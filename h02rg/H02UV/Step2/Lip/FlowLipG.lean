import Step2.Lip.FlowLipFin

/-!
# The marginal and relevant couplings: elementary estimates (Lipschitz bounds, part 25)

* `G_lip`: `|a'(1+n')/(1+ζ')² - a(1+n)/(1+ζ)²| ≤ (1 + 4s)|δa| + |a|(2|δn| + 5|δζ|)` for
  `|ζ|, |ζ'|, |n|, |n'| ≤ s ≤ 1/16`;
* `P_lip`: `|P'/(1+ζ') - P/(1+ζ)| ≤ 2|δP| + 2|P||δζ|` for `|ζ|, |ζ'| ≤ 1/8`;
* `ghat_sub_le'`: `|δĝ| ≤ (1 + 2|n'|)|δg| + 2|g||δn|`;
* `nCor_sub_le'`: the Lipschitz bound of `n = 4νw` on the domain.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

theorem norm_inv_one_add_le' {z : ℂ} {s : ℝ} (hz : ‖z‖ ≤ s) (hs : s ≤ 1 / 2) :
    ‖(1 + z)⁻¹‖ ≤ 1 + 2 * s := by
  have h1 : 1 - s ≤ ‖1 + z‖ := le_trans (by linarith) (norm_one_add_ge (ζ := z))
  have hs0 : 0 ≤ s := (norm_nonneg z).trans hz
  rw [norm_inv, inv_le_iff_one_le_mul₀ (by linarith)]
  have : (1 + 2 * s) * (1 - s) ≤ (1 + 2 * s) * ‖1 + z‖ :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

/-- **The marginal coupling map is Lipschitz.** -/
theorem G_lip {a a' ζ ζ' n n' : ℂ} {s : ℝ} (hs : s ≤ 1 / 16) (hζ : ‖ζ‖ ≤ s) (hζ' : ‖ζ'‖ ≤ s)
    (hn : ‖n‖ ≤ s) (hn' : ‖n'‖ ≤ s) :
    ‖a' / (1 + ζ') ^ 2 * (1 + n') - a / (1 + ζ) ^ 2 * (1 + n)‖ ≤
      (1 + 4 * s) * ‖a' - a‖ + ‖a‖ * (2 * ‖n' - n‖ + 5 * ‖ζ' - ζ‖) := by
  have hs0 : 0 ≤ s := (norm_nonneg ζ).trans hζ
  have h1 : 1 - s ≤ ‖1 + ζ‖ := le_trans (by linarith) (norm_one_add_ge (ζ := ζ))
  have h1' : 1 - s ≤ ‖1 + ζ'‖ := le_trans (by linarith) (norm_one_add_ge (ζ := ζ'))
  have hne : 1 + ζ ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  have hne' : 1 + ζ' ≠ 0 := fun h => by rw [h, norm_zero] at h1'; linarith
  set Φ := (1 + n) / (1 + ζ) ^ 2
  set Φ' := (1 + n') / (1 + ζ') ^ 2
  have e1 : a' / (1 + ζ') ^ 2 * (1 + n') - a / (1 + ζ) ^ 2 * (1 + n) = (a' - a) * Φ' + a * (Φ' - Φ) := by
    simp only [Φ, Φ']; field_simp; ring
  rw [e1]
  have hq : (15 / 16 : ℝ) ^ 2 ≤ ‖1 + ζ'‖ ^ 2 := by
    have : 15 / 16 ≤ ‖1 + ζ'‖ := by linarith
    gcongr
  have hq0 : (15 / 16 : ℝ) ^ 2 ≤ ‖1 + ζ‖ ^ 2 := by
    have : 15 / 16 ≤ ‖1 + ζ‖ := by linarith
    gcongr
  have hΦ' : ‖Φ'‖ ≤ 1 + 4 * s := by
    simp only [Φ']
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have hn1 : ‖1 + n'‖ ≤ 1 + s := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    have : (1 - s) ^ 2 ≤ ‖1 + ζ'‖ ^ 2 := by
      have : 0 ≤ 1 - s := by linarith
      gcongr
    nlinarith
  have hΔ : ‖Φ' - Φ‖ ≤ 2 * ‖n' - n‖ + 5 * ‖ζ' - ζ‖ := by
    have e2 : Φ' - Φ = (n' - n) / (1 + ζ') ^ 2 +
        (1 + n) * ((ζ - ζ') * (2 + ζ + ζ')) / ((1 + ζ) ^ 2 * (1 + ζ') ^ 2) := by
      simp only [Φ, Φ']; field_simp; ring
    rw [e2]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (n' - n)]
    · rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_sub_rev ζ,
        div_le_iff₀ (by positivity)]
      have hn1 : ‖1 + n‖ ≤ 17 / 16 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
      have h2 : ‖2 + ζ + ζ'‖ ≤ 17 / 8 :=
        (norm_add_le _ _).trans (by
          have := norm_add_le (2 : ℂ) ζ
          rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at this
          linarith)
      have hd := norm_nonneg (ζ' - ζ)
      have hp : (15 / 16 : ℝ) ^ 2 * (15 / 16) ^ 2 ≤ ‖1 + ζ‖ ^ 2 * ‖1 + ζ'‖ ^ 2 :=
        mul_le_mul hq0 hq (by positivity) (by positivity)
      have h3 : ‖1 + n‖ * (‖ζ' - ζ‖ * ‖2 + ζ + ζ'‖) ≤ 17 / 16 * (‖ζ' - ζ‖ * (17 / 8)) :=
        mul_le_mul hn1 (mul_le_mul_of_nonneg_left h2 hd) (by positivity) (by norm_num)
      nlinarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_left hΦ' (norm_nonneg (a' - a))
  have := mul_le_mul_of_nonneg_left hΔ (norm_nonneg a)
  nlinarith

/-- **The relevant coupling map is Lipschitz.** -/
theorem P_lip {P P' ζ ζ' : ℂ} (hζ : ‖ζ‖ ≤ 1 / 8) (hζ' : ‖ζ'‖ ≤ 1 / 8) :
    ‖P' / (1 + ζ') - P / (1 + ζ)‖ ≤ 2 * ‖P' - P‖ + 2 * ‖P‖ * ‖ζ' - ζ‖ := by
  have h1 : 7 / 8 ≤ ‖1 + ζ‖ := le_trans (by linarith) (norm_one_add_ge (ζ := ζ))
  have h1' : 7 / 8 ≤ ‖1 + ζ'‖ := le_trans (by linarith) (norm_one_add_ge (ζ := ζ'))
  have hne : 1 + ζ ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  have hne' : 1 + ζ' ≠ 0 := fun h => by rw [h, norm_zero] at h1'; linarith
  have e1 : P' / (1 + ζ') - P / (1 + ζ) = (P' - P) / (1 + ζ') + P * (ζ - ζ') / ((1 + ζ) * (1 + ζ')) := by
    field_simp; ring
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg (P' - P)]
  · rw [norm_div, norm_mul, norm_mul, norm_sub_rev ζ, div_le_iff₀ (by positivity)]
    have : (7 / 8 : ℝ) * (7 / 8) ≤ ‖1 + ζ‖ * ‖1 + ζ'‖ := mul_le_mul h1 h1' (by norm_num) (by positivity)
    nlinarith [mul_nonneg (norm_nonneg P) (norm_nonneg (ζ' - ζ))]

/-- The sharp difference of `ĝ = g/(1+n)`. -/
theorem ghat_sub_le' (s s' : SD L N) {τ : ℝ} (hτ : ‖nCor (s'.μ : ℂ) s'.w‖ ≤ τ) (hτ2 : τ ≤ 1 / 2) :
    ‖ghat s' - ghat s‖ ≤
      (1 + 2 * τ) * |s'.g - s.g| + 2 * |s.g| * ‖nCor (s'.μ : ℂ) s'.w - nCor (s.μ : ℂ) s.w‖ := by
  have e : ghat s' - ghat s = ((s'.g - s.g : ℝ) : ℂ) * (1 + nCor (s'.μ : ℂ) s'.w)⁻¹ +
      (s.g : ℂ) * ((1 + nCor (s'.μ : ℂ) s'.w)⁻¹ - (1 + nCor (s.μ : ℂ) s.w)⁻¹) := by
    simp only [ghat]; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have a1 := norm_inv_one_add_le' hτ hτ2
  have a2 := norm_inv_one_add_sub_le (norm_nCor_le (s'.μ : ℂ) s'.w) (norm_nCor_le (s.μ : ℂ) s.w)
  have := mul_le_mul_of_nonneg_left a1 (abs_nonneg (s'.g - s.g))
  have := mul_le_mul_of_nonneg_left a2 (abs_nonneg s.g)
  nlinarith

/-- `n = 4νw` on the domain: the Lipschitz bound for complex `ν`. -/
theorem nCor_sub_le' {a a' w w' : ℂ} {Ba Bw : ℝ} (ha' : ‖a'‖ ≤ Ba) (hw : ‖w‖ ≤ Bw)
    (hd : ‖4 * a * w‖ ≤ 1 / 8) (hd' : ‖4 * a' * w'‖ ≤ 1 / 8) :
    ‖nCor a' w' - nCor a w‖ ≤ 4 * (Bw * ‖a' - a‖ + Ba * ‖w' - w‖) := by
  rw [nCor_dom hd, nCor_dom hd']
  have e : 4 * a' * w' - 4 * a * w = 4 * ((a' - a) * w + a' * (w' - w)) := by ring
  rw [e, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by norm_num)
  rw [norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_left hw (norm_nonneg (a' - a))
  have := mul_le_mul_of_nonneg_right ha' (norm_nonneg (w' - w))
  nlinarith [mul_comm ‖a' - a‖ ‖w‖]

end

end Step2
