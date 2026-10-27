import Step2.D2.D2Bv4

/-!
# Pointwise bounds for `∂_{p₀} ĉ_T` (`prop:d2`, line 3)

With `K = 4 + m²`, `ν = λ + m²`, `A = -2 sin p₀/ν²`:

* `abs_sin_re_le`: `|sin p₀| ≤ (K/2) sin(2π x(u))`;
* `abs_dchat_le`: `|∂₀ ĉ_T| ≤ C_D T³/(6πK)`;
* `abs_dchat_sub_le`: `|∂₀ ĉ_T - A| ≤ C_D (2π²K)³/(6πK) · T^{-3} ν^{-3}`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

variable {msq T : ℝ}

theorem abs_sin_re_le (hm : 0 ≤ msq) (p : ℂ) :
    |Real.sin p.re| ≤ (2 * 2 + msq) / 2 * Real.sin (2 * π * xu (uhatC msq p)) := by
  set u := uhatC msq p
  have hu := uhatC_mem hm p
  have hs2 := sin_xu_sq hu
  have hs0 : 0 ≤ Real.sin (2 * π * xu u) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · have := xu_nonneg u; positivity
    · have := xu_le u; nlinarith [pi_pos]
  have hK : (0 : ℝ) < 2 * 2 + msq := by linarith
  have hu' : u * (2 * 2 + msq) = lamC p + msq := by
    simp only [u, uhatC]; field_simp
  have hc0 := Real.neg_one_le_cos p.re
  have hc1 := Real.cos_le_one p.re
  have hd0 := Real.neg_one_le_cos p.im
  have hd1 := Real.cos_le_one p.im
  have hsq : Real.sin p.re ^ 2 = (1 - Real.cos p.re) * (1 + Real.cos p.re) := by
    have := Real.sin_sq_add_cos_sq p.re; nlinarith
  have hl : lamC p = (2 - 2 * Real.cos p.re) + (2 - 2 * Real.cos p.im) := rfl
  -- `K u ≥ 2 - 2 cos p₀` and `K (2 - u) ≥ 2 + 2 cos p₀`
  have a1 : 2 - 2 * Real.cos p.re ≤ u * (2 * 2 + msq) := by rw [hu', hl]; nlinarith
  have a2 : 2 + 2 * Real.cos p.re ≤ (2 - u) * (2 * 2 + msq) := by
    have : (2 - u) * (2 * 2 + msq) = 2 * (2 * 2 + msq) - (lamC p + msq) := by rw [← hu']; ring
    rw [this, hl]; nlinarith
  have key : Real.sin p.re ^ 2 ≤ ((2 * 2 + msq) / 2 * Real.sin (2 * π * xu u)) ^ 2 := by
    rw [mul_pow, hs2, hsq]
    have h1 : 0 ≤ 2 - 2 * Real.cos p.re := by linarith
    have h2 : 0 ≤ 2 + 2 * Real.cos p.re := by linarith
    have := mul_le_mul a1 a2 h2 (by nlinarith)
    nlinarith
  exact abs_le_of_sq_le_sq' key (by positivity) |>.2 |> fun h => abs_le.2 ⟨by
    have := abs_le_of_sq_le_sq' key (by positivity); linarith [this.1], h⟩

/-- `x(u)⁶ ≥ (u/(2π²))³`. -/
theorem xu_pow_six_ge {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) : (u / (2 * π ^ 2)) ^ 3 ≤ xu u ^ 6 := by
  have h := cos_xu hu
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * π * xu u)
  have hu2 : u ≤ 2 * π ^ 2 * xu u ^ 2 := by nlinarith
  have hpi := pi_pos
  have h0 : 0 ≤ u / (2 * π ^ 2) := div_nonneg hu.1 (by positivity)
  have h1 : u / (2 * π ^ 2) ≤ xu u ^ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  calc (u / (2 * π ^ 2)) ^ 3 ≤ (xu u ^ 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
    _ = xu u ^ 6 := by ring

/-- **The crude bound** `|∂₀ĉ_T| ≤ C_D T³/(6πK)`. -/
theorem abs_dchat_le (hm : 0 < msq) (hT : 0 < T) (p : ℂ) :
    |dchat msq T p| ≤ CD * T ^ 3 / (6 * π * (2 * 2 + msq)) := by
  have hu := uhatC_mem_Ioo hm p
  obtain ⟨-, -, hH⟩ := head_tail_Pd hu hT
  have hs := abs_sin_re_le hm.le p
  have hK : (0 : ℝ) < 2 * 2 + msq := by linarith
  have hpi := pi_pos
  unfold dchat
  set H := ∫ τ in Ioc 0 T, τ * Pd τ (uhatC msq p)
  have hsn : snx (uhatC msq p) = 2 * π * Real.sin (2 * π * xu (uhatC msq p)) := rfl
  rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * 2 + msq)⁻¹),
    abs_of_pos hK, abs_two]
  rw [hsn] at hH
  have hC := CD_nonneg
  calc (2 * 2 + msq)⁻¹ * |H| * (2 * |Real.sin p.re| / (2 * 2 + msq))
      ≤ (2 * 2 + msq)⁻¹ * |H| * (2 * ((2 * 2 + msq) / 2 * Real.sin (2 * π * xu (uhatC msq p))) /
          (2 * 2 + msq)) := by gcongr
    _ = (|H| * (2 * π * Real.sin (2 * π * xu (uhatC msq p)))) / (2 * π * (2 * 2 + msq)) := by
        field_simp
    _ ≤ (CD * T ^ 3 / 3) / (2 * π * (2 * 2 + msq)) := by gcongr
    _ = CD * T ^ 3 / (6 * π * (2 * 2 + msq)) := by field_simp; ring

/-- `A = -2 sin p₀ / ν²`. -/
def Amain (msq : ℝ) (p : ℂ) : ℝ := -2 * Real.sin p.re / (lamC p + msq) ^ 2

/-- The constant of `abs_dchat_sub_le`. -/
def CBd (msq : ℝ) : ℝ := CD * (2 * π ^ 2 * (2 * 2 + msq)) ^ 3 / (6 * π * (2 * 2 + msq))

/-- **`|∂₀ĉ_T - A| ≤ C T^{-3} ν^{-3}`.** -/
theorem abs_dchat_sub_le (hm : 0 < msq) (hT : 0 < T) (p : ℂ) :
    |dchat msq T p - Amain msq p| ≤ CBd msq / (T ^ 3 * (lamC p + msq) ^ 3) := by
  have hu := uhatC_mem_Ioo hm p
  obtain ⟨hsplit, htail, -⟩ := head_tail_Pd hu hT
  have hs := abs_sin_re_le hm.le p
  have hK : (0 : ℝ) < 2 * 2 + msq := by linarith
  have hpi := pi_pos
  have hν : 0 < lamC p + msq := by have := lamC_nonneg p; linarith
  set u := uhatC msq p
  have huK : u * (2 * 2 + msq) = lamC p + msq := by simp only [u, uhatC]; field_simp
  set tail := ∫ τ in Ioi T, τ * Pd τ u
  have hsn : snx u = 2 * π * Real.sin (2 * π * xu u) := rfl
  rw [hsn] at htail
  have hx6 := xu_pow_six_ge (u := u) ⟨hu.1.le, hu.2.le⟩
  have hx0 : 0 < xu u := xu_pos hu.1
  have e : dchat msq T p - Amain msq p =
      -((2 * 2 + msq)⁻¹ * tail * (2 * Real.sin p.re / (2 * 2 + msq))) := by
    unfold dchat Amain
    rw [hsplit, ← huK]
    have : u ≠ 0 := hu.1.ne'
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * 2 + msq)⁻¹),
    abs_of_pos hK, abs_two]
  have hC := CD_nonneg
  calc (2 * 2 + msq)⁻¹ * |tail| * (2 * |Real.sin p.re| / (2 * 2 + msq))
      ≤ (2 * 2 + msq)⁻¹ * |tail| * (2 * ((2 * 2 + msq) / 2 * Real.sin (2 * π * xu u)) /
          (2 * 2 + msq)) := by gcongr
    _ = (|tail| * (2 * π * Real.sin (2 * π * xu u))) / (2 * π * (2 * 2 + msq)) := by
        field_simp
    _ ≤ (CD / (3 * xu u ^ 6 * T ^ 3)) / (2 * π * (2 * 2 + msq)) := by gcongr
    _ ≤ (CD / (3 * (u / (2 * π ^ 2)) ^ 3 * T ^ 3)) / (2 * π * (2 * 2 + msq)) := by
        have := hu.1
        gcongr
    _ = CBd msq / (T ^ 3 * (lamC p + msq) ^ 3) := by
        rw [CBd, ← huK]
        have : u ≠ 0 := hu.1.ne'
        field_simp
        ring

end

end Step2.D2
