import Step2.D2.D2Sh5

/-!
# Sharp line 3, part 6: `a_T = -(λ+m²)² ∂_λ ĉ_T` versus the profile `Φ(2T√(λ+m²))`

* `aT msq T p = 1 + u² ∫_T^∞ τ P_τ'(u) dτ`, `u = û(p)`;
* `dchat_eq_aT`: `∂₀ĉ_T = -(a_T/ν²) · 2 sin p₀`, `ν = λ + m²`;
* `aT_vs_PhiE`: `|a_T - Φ(2T√ν)| ≤ C_a ν ((1 + T√λ)^{-3} + T^{-2})` for `0 < m² ≤ 1`, `T ≥ 1`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- `∫_T^∞ τ P_τ'(û(p)) dτ`. -/
def tl (msq T : ℝ) (p : ℂ) : ℝ := ∫ τ in Ioi T, τ * Pd τ (uhatC msq p)

/-- `a_T = 1 + u² ∫_T^∞ τ P_τ'(u) dτ = -(λ + m²)² ∂_λ ĉ_T`. -/
def aT (msq T : ℝ) (p : ℂ) : ℝ := 1 + uhatC msq p ^ 2 * tl msq T p

variable {msq T : ℝ}

theorem uhatC_eq' (msq : ℝ) (p : ℂ) : uhatC msq p = (lamC p + msq) / (2 * 2 + msq) := rfl

/-- **`∂₀ĉ_T = -(a_T/ν²) · 2 sin p₀`.** -/
theorem dchat_eq_aT (hm : 0 < msq) (hT : 0 < T) (p : ℂ) :
    dchat msq T p = -(aT msq T p / (lamC p + msq) ^ 2) * (2 * Real.sin p.re) := by
  have hu := uhatC_mem_Ioo hm p
  obtain ⟨hsplit, -, -⟩ := head_tail_Pd hu hT
  unfold dchat aT tl
  rw [hsplit]
  set u := uhatC msq p
  have hK : (0 : ℝ) < 2 * 2 + msq := by linarith
  have hnu : lamC p + msq = (2 * 2 + msq) * u := by
    simp only [u, uhatC_eq']; field_simp
  rw [hnu]
  have hu0 : u ≠ 0 := hu.1.ne'
  field_simp
  ring

/-! ### The angle variable `x = xu u` versus `y = 2√ν/κ` -/

theorem sqrt_four_add_le {m : ℝ} (hm : 0 ≤ m) : √(4 + m) ≤ 2 + m / 4 := by
  rw [Real.sqrt_le_left (by positivity)]; nlinarith

theorem two_le_sqrt_four_add {m : ℝ} (hm : 0 ≤ m) : 2 ≤ √(4 + m) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith

/-- `y = 2√ν/κ = √(4+m²) sin(πx)/(2π)`. -/
theorem ymom_eq (hm : 0 ≤ msq) (p : ℂ) :
    2 * √(lamC p + msq) / kap =
      √(4 + msq) * Real.sin (π * xu (uhatC msq p)) / (2 * π) := by
  have hpi := pi_pos
  set u := uhatC msq p
  have hu2 : u = 2 * Real.sin (π * xu u) ^ 2 := u_eq_two_sin_sq (uhatC_mem hm p)
  have hnu : lamC p + msq = (4 + msq) * u := by
    simp only [u, uhatC_eq']; have : (0 : ℝ) < 2 * 2 + msq := by linarith
    field_simp; ring
  have hs0 : 0 ≤ Real.sin (π * xu u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by have := xu_nonneg u; positivity)
      (by have := xu_le u; nlinarith)
  set x := xu u
  have hu3 : u = (√2 * Real.sin (π * x)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; exact hu2
  have hsq : √(lamC p + msq) = √(4 + msq) * (√2 * Real.sin (π * x)) := by
    rw [hnu, Real.sqrt_mul (by positivity)]
    congr 1
    rw [hu3, Real.sqrt_sq (by positivity)]
  rw [hsq, kap]
  have : √2 ≠ 0 := by positivity
  field_simp
  ring

/-- `x/2 ≤ y` and `|x - y| ≤ x (m²/8 + π²x²/4)` for `x ≤ 1/4`. -/
theorem ymom_bounds (hm : 0 ≤ msq) (p : ℂ) (hx0 : 0 < xu (uhatC msq p))
    (hx : xu (uhatC msq p) ≤ 1 / 4) :
    xu (uhatC msq p) / 2 ≤ 2 * √(lamC p + msq) / kap ∧
      |xu (uhatC msq p) - 2 * √(lamC p + msq) / kap| ≤
        xu (uhatC msq p) * (msq / 8 + π ^ 2 * xu (uhatC msq p) ^ 2 / 4) := by
  have hpi := pi_pos
  rw [ymom_eq hm p]
  set x := xu (uhatC msq p)
  set y := π * x
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := pi_mul_le_quarter ⟨hx0, hx⟩
  have hs1 : Real.sin y ≤ y := Real.sin_le hy0.le
  have hs2 : y - y ^ 3 / 4 < Real.sin y := Real.sin_gt_sub_cube hy0 hy1
  have hK1 := two_le_sqrt_four_add hm
  have hK2 := sqrt_four_add_le hm
  have e1 : Real.sin y / π ≤ x := by rw [div_le_iff₀ hpi]; simp only [y] at hs1; linarith
  have e2 : x - π ^ 2 * x ^ 3 / 4 ≤ Real.sin y / π := by
    rw [le_div_iff₀ hpi]
    have : y - y ^ 3 / 4 = (x - π ^ 2 * x ^ 3 / 4) * π := by simp only [y]; ring
    linarith
  have hsp : 0 ≤ Real.sin y / π := by
    have : 0 ≤ x - π ^ 2 * x ^ 3 / 4 := by
      have : π ^ 2 * x ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith
  have e : √(4 + msq) * Real.sin y / (2 * π) = √(4 + msq) / 2 * (Real.sin y / π) := by
    field_simp
  rw [e]
  have hyl : x - π ^ 2 * x ^ 3 / 4 ≤ √(4 + msq) / 2 * (Real.sin y / π) := by
    calc x - π ^ 2 * x ^ 3 / 4 ≤ Real.sin y / π := e2
      _ = 1 * (Real.sin y / π) := (one_mul _).symm
      _ ≤ √(4 + msq) / 2 * (Real.sin y / π) := by gcongr; linarith
  have hyu : √(4 + msq) / 2 * (Real.sin y / π) ≤ (1 + msq / 8) * x := by
    calc √(4 + msq) / 2 * (Real.sin y / π) ≤ (1 + msq / 8) * (Real.sin y / π) := by
          gcongr; linarith
      _ ≤ (1 + msq / 8) * x := by gcongr
  have hq : π ^ 2 * x ^ 2 ≤ 1 := by nlinarith
  constructor
  · nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- `x² ≤ ν/32` and `√λ/10 ≤ x` (for `m² ≤ 1`). -/
theorem xu_vs_nu (hm : 0 ≤ msq) (hm1 : msq ≤ 1) (p : ℂ) :
    xu (uhatC msq p) ^ 2 ≤ (lamC p + msq) / 32 ∧ √(lamC p) / 10 ≤ xu (uhatC msq p) := by
  have hpi := pi_pos
  set u := uhatC msq p
  set x := xu u
  have hx0 : 0 ≤ x := xu_nonneg u
  have hx1 : x ≤ 1 / 2 := xu_le u
  have hu2 : u = 2 * Real.sin (π * x) ^ 2 := u_eq_two_sin_sq (uhatC_mem hm p)
  have hnu : lamC p + msq = (4 + msq) * u := by
    simp only [u, uhatC_eq']; have : (0 : ℝ) < 2 * 2 + msq := by linarith
    field_simp; ring
  have hl := lamC_nonneg p
  constructor
  · -- `sin(πx) ≥ 2x`
    have hs : 2 * x ≤ Real.sin (π * x) := by
      have := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
      have e : 2 / π * (π * x) = 2 * x := by field_simp
      linarith
    have : 8 * x ^ 2 ≤ u := by rw [hu2]; nlinarith
    rw [hnu]; nlinarith
  · have hs : Real.sin (π * x) ≤ π * x := Real.sin_le (by positivity)
    have hs0 : 0 ≤ Real.sin (π * x) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    have h1 : lamC p ≤ 10 * Real.sin (π * x) ^ 2 := by
      have : lamC p ≤ (4 + msq) * u := by rw [← hnu]; linarith
      rw [hu2] at this; nlinarith
    have h2 : √(lamC p) ≤ √10 * Real.sin (π * x) := by
      rw [show √10 * Real.sin (π * x) = √(10 * Real.sin (π * x) ^ 2) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hs0]]
      exact Real.sqrt_le_sqrt h1
    have h3 : √10 * π ≤ 10 := by
      have hp := pi_lt_d2
      have : √10 ≤ 10 / π := by
        rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
        nlinarith
      rw [le_div_iff₀ hpi] at this; linarith
    have h4 : √(lamC p) ≤ √10 * π * x := by nlinarith [Real.sqrt_nonneg 10]
    rw [div_le_iff₀ (by norm_num)]
    nlinarith

end

end Step2.D2
