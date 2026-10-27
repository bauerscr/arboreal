import Step2.D2.D2Bv6

/-!
# Pointwise estimates for `𝔅(w_T)` (`prop:d2`, line 3)

Real-variable inequalities used in the integral estimate:

* `ptE2`: the error `(λ²/2)(∂₀ĉ)² - χ (λ²/2) A²` is `≤ C_E T² (1 + T|p|)^{-5}`;
* `ptM`: `|χ λ³/ν⁴ - 1_{λ > T^{-2}}/λ| ≤ C_M T² (1 + T|p|)^{-4}` (needs `m² T² ≤ 1`);
* `ptZ`: `|1_{λ > T^{-2}}/λ - 1_{T^{-2} < |p|² < π²}/|p|²| ≤ 1 + 81 T² (1 + T|p|)^{-4}`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real

/-- The cut-off `χ = 1_{ν > T^{-2}}`. -/
def chiT (T ν : ℝ) : ℝ := if (T ^ 2)⁻¹ < ν then 1 else 0

theorem rpow_five_eq (c : ℝ) : c ^ (5 : ℝ) = c ^ 5 := by
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem small_of_le {T lam np : ℝ} (hT : 0 < T) (hlp : 4 / π ^ 2 * np ^ 2 ≤ lam)
    (hnp : 0 ≤ np) (hl : lam ≤ (T ^ 2)⁻¹) : T * np ≤ π / 2 := by
  have hpi := pi_pos
  have hT2 : 0 < T ^ 2 := by positivity
  have h2 : T ^ 2 * lam ≤ 1 := by
    calc T ^ 2 * lam ≤ T ^ 2 * (T ^ 2)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hT2.ne'
  have h3 : np ^ 2 ≤ π ^ 2 / 4 * lam := by
    have : π ^ 2 / 4 * (4 / π ^ 2 * np ^ 2) = np ^ 2 := by field_simp
    rw [← this]; gcongr
  have h1 : (T * np) ^ 2 ≤ (π / 2) ^ 2 := by
    calc (T * np) ^ 2 = T ^ 2 * np ^ 2 := by ring
      _ ≤ T ^ 2 * (π ^ 2 / 4 * lam) := by gcongr
      _ = π ^ 2 / 4 * (T ^ 2 * lam) := by ring
      _ ≤ π ^ 2 / 4 * 1 := by gcongr
      _ = (π / 2) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1

theorem nu_inv_le {lam ν np : ℝ} (hlp : 4 / π ^ 2 * np ^ 2 ≤ lam) (hlν : lam ≤ ν) (hnp : 0 < np) :
    ν⁻¹ ≤ π ^ 2 / 4 * (np ^ 2)⁻¹ := by
  have hpi := pi_pos
  have h : 4 / π ^ 2 * np ^ 2 ≤ ν := hlp.trans hlν
  have hpos : 0 < 4 / π ^ 2 * np ^ 2 := by positivity
  calc ν⁻¹ ≤ (4 / π ^ 2 * np ^ 2)⁻¹ := inv_anti₀ hpos h
    _ = π ^ 2 / 4 * (np ^ 2)⁻¹ := by field_simp

theorem pi_sq_div_four_ge_one : 1 ≤ π ^ 2 / 4 := by
  have := pi_gt_three; nlinarith

/-- `x^{-8}, x^{-5} ≤ 32 (1+x)^{-5}` for `x ≥ 1`. -/
theorem inv_pow_le_32 {k : ℕ} (hk : 5 ≤ k) {x : ℝ} (hx : 1 ≤ x) :
    (x ^ k)⁻¹ ≤ 32 * (1 + x) ^ (-(5 : ℝ)) := by
  have := inv_pow_le_decay (k := k) (α := 5) (by norm_num) (by exact_mod_cast hk) hx
  rwa [rpow_five_eq, show (2 : ℝ) ^ 5 = 32 by norm_num] at this

/-- The far-from-cut-off case. -/
theorem chi1_bound {T ν np b q : ℝ} (hT : 0 < T) (hν : 0 < ν) (hu : ν⁻¹ < T ^ 2) (hq : 1 ≤ q)
    (hb : 0 ≤ b) (hnp : 0 ≤ np) (hfar : 0 < np → ν⁻¹ ≤ q * (np ^ 2)⁻¹) :
    b ^ 2 / 2 * (T ^ 6)⁻¹ * (ν⁻¹) ^ 4 + 2 * b * np * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 ≤
      32 * q ^ 4 * (b ^ 2 / 2 + 2 * b) * (T ^ 2 * (1 + T * np) ^ (-(5 : ℝ))) := by
  set D := T ^ 2 * (1 + T * np) ^ (-(5 : ℝ)) with hD
  have hD0 : 0 ≤ D := by positivity
  have hui : 0 < ν⁻¹ := inv_pos.2 hν
  have hq0 : 0 < q := by linarith
  have hq4 : 1 ≤ q ^ 4 := one_le_pow₀ hq
  have hq34 : q ^ 3 ≤ q ^ 4 := pow_le_pow_right₀ hq (by norm_num)
  rcases le_or_gt (T * np) 1 with hs | hs
  · have hd5 : 1 ≤ 32 * (1 + T * np) ^ (-(5 : ℝ)) := by
      have := one_le_decay (α := 5) (c := 1) (x := T * np) (by norm_num) (by positivity) hs
      rwa [rpow_five_eq, show ((1 : ℝ) + 1) ^ 5 = 32 by norm_num] at this
    have hT2D : T ^ 2 ≤ 32 * D := by
      rw [hD]
      calc T ^ 2 = T ^ 2 * 1 := by ring
        _ ≤ T ^ 2 * (32 * (1 + T * np) ^ (-(5 : ℝ))) := by gcongr
        _ = 32 * (T ^ 2 * (1 + T * np) ^ (-(5 : ℝ))) := by ring
    have e1 : b ^ 2 / 2 * (T ^ 6)⁻¹ * (ν⁻¹) ^ 4 ≤ b ^ 2 / 2 * T ^ 2 := by
      calc b ^ 2 / 2 * (T ^ 6)⁻¹ * (ν⁻¹) ^ 4 ≤ b ^ 2 / 2 * (T ^ 6)⁻¹ * (T ^ 2) ^ 4 := by
            gcongr
        _ = b ^ 2 / 2 * T ^ 2 := by field_simp
    have hnpT : np ≤ T⁻¹ := by
      rw [← one_div, le_div_iff₀ hT]; linarith [mul_comm T np]
    have e2 : 2 * b * np * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 ≤ 2 * b * T ^ 2 := by
      calc 2 * b * np * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 ≤ 2 * b * T⁻¹ * (T ^ 3)⁻¹ * (T ^ 2) ^ 3 := by
            gcongr
        _ = 2 * b * T ^ 2 := by field_simp
    have f : (b ^ 2 / 2 + 2 * b) * T ^ 2 ≤ (b ^ 2 / 2 + 2 * b) * (32 * D) := by gcongr
    have g : (b ^ 2 / 2 + 2 * b) * (32 * D) ≤ q ^ 4 * ((b ^ 2 / 2 + 2 * b) * (32 * D)) := by
      have : 0 ≤ (b ^ 2 / 2 + 2 * b) * (32 * D) := by positivity
      nlinarith
    calc _ ≤ b ^ 2 / 2 * T ^ 2 + 2 * b * T ^ 2 := add_le_add e1 e2
      _ = (b ^ 2 / 2 + 2 * b) * T ^ 2 := by ring
      _ ≤ q ^ 4 * ((b ^ 2 / 2 + 2 * b) * (32 * D)) := f.trans g
      _ = _ := by ring
  · have hnp0 : 0 < np := by
      by_contra h; push Not at h
      have : T * np ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hT.le h
      linarith
    have hν' := hfar hnp0
    have d8 := inv_pow_le_32 (k := 8) (by norm_num) hs.le
    have d5 := inv_pow_le_32 (k := 5) (by norm_num) hs.le
    have e1 : b ^ 2 / 2 * (T ^ 6)⁻¹ * (ν⁻¹) ^ 4 ≤ b ^ 2 / 2 * q ^ 4 * (T ^ 2 * ((T * np) ^ 8)⁻¹) := by
      calc b ^ 2 / 2 * (T ^ 6)⁻¹ * (ν⁻¹) ^ 4 ≤ b ^ 2 / 2 * (T ^ 6)⁻¹ * (q * (np ^ 2)⁻¹) ^ 4 := by
            gcongr
        _ = b ^ 2 / 2 * q ^ 4 * (T ^ 2 * ((T * np) ^ 8)⁻¹) := by field_simp
    have e2 : 2 * b * np * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 ≤ 2 * b * q ^ 3 * (T ^ 2 * ((T * np) ^ 5)⁻¹) := by
      calc 2 * b * np * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 ≤ 2 * b * np * (T ^ 3)⁻¹ * (q * (np ^ 2)⁻¹) ^ 3 := by
            gcongr
        _ = 2 * b * q ^ 3 * (T ^ 2 * ((T * np) ^ 5)⁻¹) := by field_simp
    have g8 : T ^ 2 * ((T * np) ^ 8)⁻¹ ≤ 32 * D := by
      rw [hD]; calc T ^ 2 * ((T * np) ^ 8)⁻¹ ≤ T ^ 2 * (32 * (1 + T * np) ^ (-(5 : ℝ))) := by gcongr
        _ = _ := by ring
    have g5 : T ^ 2 * ((T * np) ^ 5)⁻¹ ≤ 32 * D := by
      rw [hD]; calc T ^ 2 * ((T * np) ^ 5)⁻¹ ≤ T ^ 2 * (32 * (1 + T * np) ^ (-(5 : ℝ))) := by gcongr
        _ = _ := by ring
    have h1 : b ^ 2 / 2 * q ^ 4 * (T ^ 2 * ((T * np) ^ 8)⁻¹) ≤ b ^ 2 / 2 * q ^ 4 * (32 * D) := by
      gcongr
    have h2 : 2 * b * q ^ 3 * (T ^ 2 * ((T * np) ^ 5)⁻¹) ≤ 2 * b * q ^ 4 * (32 * D) := by
      gcongr
    calc _ ≤ b ^ 2 / 2 * q ^ 4 * (32 * D) + 2 * b * q ^ 4 * (32 * D) :=
          add_le_add (e1.trans h1) (e2.trans h2)
      _ = _ := by ring

/-- The near-zero case `ν ≤ T^{-2}`. -/
theorem chi0_bound {T lam ν d np a : ℝ} (hT : 0 < T) (hlν : lam ≤ ν) (hl0 : 0 ≤ lam)
    (hnp : 0 ≤ np) (hlp : 4 / π ^ 2 * np ^ 2 ≤ lam) (hχ : ν ≤ (T ^ 2)⁻¹)
    (hd : |d| ≤ a * T ^ 3) :
    |lam ^ 2 / 2 * d ^ 2| ≤ a ^ 2 / 2 * (1 + π / 2) ^ 5 * (T ^ 2 * (1 + T * np) ^ (-(5 : ℝ))) := by
  have hpi := pi_pos
  have hs := small_of_le hT hlp hnp (hlν.trans hχ)
  have hd2 : d ^ 2 ≤ (a * T ^ 3) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hl1 : lam ≤ (T ^ 2)⁻¹ := hlν.trans hχ
  have hl2 : lam ^ 2 ≤ ((T ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
  have h1 : |lam ^ 2 / 2 * d ^ 2| ≤ a ^ 2 / 2 * T ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    calc lam ^ 2 / 2 * d ^ 2 ≤ ((T ^ 2)⁻¹) ^ 2 / 2 * (a * T ^ 3) ^ 2 := by gcongr
      _ = a ^ 2 / 2 * T ^ 2 := by field_simp
  have h2 := one_le_decay (α := 5) (c := π / 2) (x := T * np) (by norm_num) (by positivity) hs
  rw [rpow_five_eq] at h2
  calc _ ≤ a ^ 2 / 2 * T ^ 2 := h1
    _ = a ^ 2 / 2 * T ^ 2 * 1 := by ring
    _ ≤ a ^ 2 / 2 * T ^ 2 * ((1 + π / 2) ^ 5 * (1 + T * np) ^ (-(5 : ℝ))) := by gcongr
    _ = _ := by ring

/-- The constant `C_E(a, b)`. -/
def CE (a b : ℝ) : ℝ := 32 * (π ^ 2 / 4) ^ 4 * (b ^ 2 / 2 + 2 * b) + a ^ 2 / 2 * (1 + π / 2) ^ 5

/-- **The error of the main term in `(λ²/2)(∂₀ĉ)²`.** -/
theorem ptE2 {T lam ν d A np a b : ℝ} (hT : 0 < T) (hν : 0 < ν) (hlν : lam ≤ ν) (hl0 : 0 ≤ lam)
    (hnp : 0 ≤ np) (hlp : 4 / π ^ 2 * np ^ 2 ≤ lam) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : |d| ≤ a * T ^ 3) (hdA : |d - A| ≤ b / (T ^ 3 * ν ^ 3)) (hA : |A| ≤ 2 * np / ν ^ 2) :
    |lam ^ 2 / 2 * d ^ 2 - chiT T ν * (lam ^ 2 / 2 * A ^ 2)| ≤
      CE a b * (T ^ 2 * (1 + T * np) ^ (-(5 : ℝ))) := by
  have hpi := pi_pos
  have hq := pi_sq_div_four_ge_one
  have hdec : 0 ≤ T ^ 2 * (1 + T * np) ^ (-(5 : ℝ)) := by positivity
  have hCE1 : 0 ≤ 32 * (π ^ 2 / 4) ^ 4 * (b ^ 2 / 2 + 2 * b) := by positivity
  have hCE2 : 0 ≤ a ^ 2 / 2 * (1 + π / 2) ^ 5 := by positivity
  unfold chiT CE
  split_ifs with hχ
  · rw [one_mul]
    set B := d - A
    have hdB : d = A + B := by simp [B]
    have e : lam ^ 2 / 2 * d ^ 2 - lam ^ 2 / 2 * A ^ 2 = lam ^ 2 / 2 * (B * (B + 2 * A)) := by
      rw [hdB]; ring
    rw [e]
    have hl2 : lam ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ hl0 hlν 2
    have hνinv : ν⁻¹ < T ^ 2 := by
      rw [inv_lt_comm₀ hν (by positivity)]; exact hχ
    have hA' : |A| ≤ 2 * np * (ν⁻¹) ^ 2 := by rw [inv_pow, ← div_eq_mul_inv]; exact hA
    have hB' : |B| ≤ b * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 := by
      rw [inv_pow, mul_assoc, ← mul_inv, ← div_eq_mul_inv]; exact hdA
    have h1 : |B + 2 * A| ≤ |B| + 2 * |A| := by
      calc |B + 2 * A| ≤ |B| + |2 * A| := abs_add_le _ _
        _ = |B| + 2 * |A| := by rw [abs_mul, abs_two]
    have key : |lam ^ 2 / 2 * (B * (B + 2 * A))| ≤
        b ^ 2 / 2 * (T ^ 6)⁻¹ * (ν⁻¹) ^ 4 + 2 * b * np * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
      calc lam ^ 2 / 2 * (|B| * |B + 2 * A|) ≤ ν ^ 2 / 2 * (|B| * (|B| + 2 * |A|)) := by gcongr
        _ ≤ ν ^ 2 / 2 * ((b * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3) * ((b * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3) +
            2 * (2 * np * (ν⁻¹) ^ 2))) := by gcongr
        _ = b ^ 2 / 2 * (T ^ 6)⁻¹ * (ν⁻¹) ^ 4 + 2 * b * np * (T ^ 3)⁻¹ * (ν⁻¹) ^ 3 := by
            field_simp
    refine key.trans ((chi1_bound hT hν hνinv hq hb hnp
      (fun h => nu_inv_le hlp hlν h)).trans ?_)
    nlinarith
  · rw [zero_mul, sub_zero]
    push Not at hχ
    refine (chi0_bound hT hlν hl0 hnp hlp hχ hd).trans ?_
    nlinarith

end

end Step2.D2
