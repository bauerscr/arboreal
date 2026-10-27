import Step2.D2.D2Sh4

/-!
# Sharp line 3, part 5: elementary bounds in the angle variable

For `x ∈ (0, 1/4]`:

* `rhoS x = sin³(πx)/((πx)³ cos(πx))`, `|ρ - 1| ≤ π² x²`;
* `u²/snx ≤ 2π² x³` (`u = 2 sin²(πx)`);
* `abs_PhiH_sub_le`: `|Φ_H(a) - Φ_H(b)| ≤ (2c₀)⁻¹ C_d S₈ |a - b|/m (1+m)^{-3}`, `m ≤ a, b`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- `ρ(x) = sin³(πx)/((πx)³ cos(πx))`. -/
def rhoS (x : ℝ) : ℝ := Real.sin (π * x) ^ 3 / ((π * x) ^ 3 * Real.cos (π * x))

theorem pi_mul_le_quarter {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 4)) : π * x ≤ 1 := by
  have := pi_lt_four
  nlinarith [hx.1, hx.2]

theorem cos_pos_quarter {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 4)) : 0 < Real.cos (π * x) := by
  apply Real.cos_pos_of_mem_Ioo
  have := pi_pos
  constructor <;> nlinarith [hx.1, hx.2]

theorem abs_rhoS_sub_le {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 4)) : |rhoS x - 1| ≤ π ^ 2 * x ^ 2 := by
  have hpi := pi_pos
  set y := π * x with hy
  have hy0 : 0 < y := mul_pos hpi hx.1
  have hy1 : y ≤ 1 := pi_mul_le_quarter hx
  have hc := cos_pos_quarter hx
  rw [← hy] at hc
  have hs1 : Real.sin y ≤ y := Real.sin_le hy0.le
  have hs2 : y - y ^ 3 / 4 < Real.sin y := Real.sin_gt_sub_cube hy0 hy1
  have hc1 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hc2 : Real.cos y ≤ 1 := Real.cos_le_one y
  have hsp : 0 < Real.sin y := by nlinarith
  have hx2 : π ^ 2 * x ^ 2 = y ^ 2 := by rw [hy]; ring
  rw [hx2]
  unfold rhoS
  rw [← hy, abs_le]
  have hden : 0 < y ^ 3 * Real.cos y := by positivity
  constructor
  · -- `ρ ≥ 1 - y²`
    rw [le_sub_iff_add_le, le_div_iff₀ hden]
    have h1 : (y - y ^ 3 / 4) ^ 3 ≤ Real.sin y ^ 3 := pow_le_pow_left₀ (by nlinarith) hs2.le 3
    have h2 : (-y ^ 2 + 1) * (y ^ 3 * Real.cos y) ≤ (1 - 3 * y ^ 2 / 4) * y ^ 3 := by
      have : 0 ≤ 1 - y ^ 2 := by nlinarith
      nlinarith [mul_nonneg (pow_pos hy0 3).le this]
    have h3 : (1 - 3 * y ^ 2 / 4) * y ^ 3 ≤ (y - y ^ 3 / 4) ^ 3 := by
      have e : (y - y ^ 3 / 4) ^ 3 = y ^ 3 * (1 - y ^ 2 / 4) ^ 3 := by ring
      rw [e]
      have : 1 - 3 * y ^ 2 / 4 ≤ (1 - y ^ 2 / 4) ^ 3 := by
        have ha : 0 ≤ y ^ 2 / 4 := by positivity
        have ha1 : y ^ 2 / 4 ≤ 1 := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg ha ha) (sub_nonneg.2 ha1)]
      nlinarith [pow_pos hy0 3]
    linarith
  · -- `ρ ≤ 1 + y²`
    rw [sub_le_iff_le_add, div_le_iff₀ hden]
    have h1 : Real.sin y ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hsp.le hs1 3
    have h2 : y ^ 3 ≤ (y ^ 2 + 1) * (y ^ 3 * Real.cos y) := by
      have : 1 ≤ (y ^ 2 + 1) * Real.cos y := by nlinarith
      nlinarith [pow_pos hy0 3]
    linarith

/-- `u²/(2π sin 2πx) = sin³(πx)/(π cos πx)` with `u = 2 sin²(πx)`. -/
theorem u_sq_div_snx {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) :
    u ^ 2 / snx u = Real.sin (π * xu u) ^ 3 / (π * Real.cos (π * xu u)) := by
  have hpi := pi_pos
  have hu2 : u = 2 * Real.sin (π * xu u) ^ 2 := u_eq_two_sin_sq ⟨hu.1.le, hu.2.le⟩
  have hs := snx_pos hu
  have e : snx u = 4 * π * Real.sin (π * xu u) * Real.cos (π * xu u) := by
    unfold snx
    rw [show 2 * π * xu u = 2 * (π * xu u) by ring, Real.sin_two_mul]; ring
  rw [e] at hs ⊢
  set x := xu u
  have hsin : Real.sin (π * x) ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hcos : Real.cos (π * x) ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hu2' : u ^ 2 = 4 * Real.sin (π * x) ^ 4 := by
    have : u ^ 2 = (2 * Real.sin (π * x) ^ 2) ^ 2 := by
      conv_lhs => rw [hu2]
    rw [this]; ring
  rw [hu2']
  field_simp

/-- `u²/snx ≤ 2π² x³` for `x ≤ 1/4`. -/
theorem u_sq_div_snx_le {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 2) (hx : xu u ≤ 1 / 4) :
    u ^ 2 / snx u ≤ 2 * π ^ 2 * xu u ^ 3 := by
  have hpi := pi_pos
  have hx0 := xu_pos hu.1
  rw [u_sq_div_snx hu]
  have hc := cos_pos_quarter ⟨hx0, hx⟩
  set y := π * xu u
  have hy0 : 0 < y := by positivity
  have hs1 : Real.sin y ≤ y := Real.sin_le hy0.le
  have hsp : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy0 (by nlinarith [pi_gt_three])
  have hy1 : y ≤ 1 := pi_mul_le_quarter ⟨hx0, hx⟩
  have hc1 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hc2 : 1 / 2 ≤ Real.cos y := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : Real.sin y ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hsp.le hs1 3
  have e : y ^ 3 = π ^ 3 * xu u ^ 3 := by simp only [y]; ring
  have h2 : y ^ 3 ≤ 2 * π ^ 2 * xu u ^ 3 * (π * Real.cos y) := by
    rw [e]
    have : 0 ≤ π ^ 3 * xu u ^ 3 := by positivity
    nlinarith
  linarith

/-! ### The Lipschitz bound for `Φ_H` -/

theorem abs_fP'_le_div {w : ℝ} (hw : 0 < w) : |fP' w| ≤ Cd / (w * (1 + w) ^ 3) := by
  have h := abs_w3_ψd_le hw.le
  rw [fP', abs_mul, abs_of_nonneg (sq_nonneg w), le_div_iff₀ (by positivity)]
  calc w ^ 2 * |ψd w| * (w * (1 + w) ^ 3) = (w ^ 3 * |ψd w|) * (1 + w) ^ 3 := by ring
    _ ≤ (Cd * ((1 + w) ^ 3)⁻¹) * (1 + w) ^ 3 := by gcongr
    _ = Cd := by field_simp

theorem abs_fP_sub_le' {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |fP a - fP b| ≤ |a - b| * (Cd / (m * (1 + m) ^ 3)) := by
  have hCd := Cd_nonneg
  have key : ∀ {a b : ℝ}, m ≤ a → a ≤ b → |fP a - fP b| ≤ |a - b| * (Cd / (m * (1 + m) ^ 3)) := by
    intro a b ha hab
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fP) (f' := fP')
      (s := Icc a b) (C := Cd / (m * (1 + m) ^ 3))
      (fun t _ => (hasDerivAt_fP t).hasDerivWithinAt)
      (fun t ht => by
        have ht0 : 0 < t := lt_of_lt_of_le hm (ha.trans ht.1)
        rw [Real.norm_eq_abs]
        refine (abs_fP'_le_div ht0).trans ?_
        apply div_le_div_of_nonneg_left hCd (by positivity)
        have hmt : m ≤ t := ha.trans ht.1
        gcongr)
      (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (fP b), abs_sub_comm b] at h
    linarith [mul_comm (Cd / (m * (1 + m) ^ 3)) |a - b|]
  rcases le_total a b with hab | hab
  · exact key ha hab
  · rw [abs_sub_comm, abs_sub_comm a]; exact key hb hab

/-- **`|Φ_H(a) - Φ_H(b)| ≤ (2c₀)⁻¹ C_d S₈ |a - b| / (m (1+m)³)`** for `0 < m ≤ a, b`. -/
theorem abs_PhiH_sub_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |PhiH a - PhiH b| ≤ (2 * c0)⁻¹ * Cd * Som 8 * (|a - b| / (m * (1 + m) ^ 3)) := by
  have hc0 := c0_pos
  have hCd := Cd_nonneg
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have e : PhiH a - PhiH b = -((2 * c0)⁻¹ * ∑' i, om i * (fP (a / 2 ^ i) - fP (b / 2 ^ i))) := by
    unfold PhiH
    have h1 : ∑' i, om i * (fP (a / 2 ^ i) - fP (b / 2 ^ i)) =
        ∑' i, om i * fP (a / 2 ^ i) - ∑' i, om i * fP (b / 2 ^ i) := by
      rw [← Summable.tsum_sub (summable_om_fP ha0) (summable_om_fP hb0)]
      congr 1; funext i; ring
    rw [h1]; ring
  rw [e, abs_neg, abs_mul, abs_of_pos (by positivity)]
  have hterm : ∀ i : ℕ, |fP (a / 2 ^ i) - fP (b / 2 ^ i)| ≤
      Cd * (|a - b| / (m * (1 + m) ^ 3)) * 8 ^ i := by
    intro i
    have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have hmi : 0 < m / 2 ^ i := by positivity
    refine (abs_fP_sub_le' hmi (div_le_div_of_nonneg_right ha h2.le)
      (div_le_div_of_nonneg_right hb h2.le)).trans ?_
    have e1 : |a / 2 ^ i - b / 2 ^ i| = |a - b| / 2 ^ i := by
      rw [← sub_div, abs_div, abs_of_pos h2]
    rw [e1]
    have h3 := inv_one_add_div_pow_le hm.le i 3
    norm_num at h3
    have hab := abs_nonneg (a - b)
    calc |a - b| / 2 ^ i * (Cd / (m / 2 ^ i * (1 + m / 2 ^ i) ^ 3))
        = Cd * (|a - b| / m) * ((1 + m / 2 ^ i) ^ 3)⁻¹ := by field_simp
      _ ≤ Cd * (|a - b| / m) * (8 ^ i * ((1 + m) ^ 3)⁻¹) := by gcongr
      _ = Cd * (|a - b| / (m * (1 + m) ^ 3)) * 8 ^ i := by field_simp
  have h := (tsum_om_le (r := 8) (by norm_num) hterm).2
  calc (2 * c0)⁻¹ * |∑' i, om i * (fP (a / 2 ^ i) - fP (b / 2 ^ i))| ≤
      (2 * c0)⁻¹ * (Cd * (|a - b| / (m * (1 + m) ^ 3)) * Som 8) := by gcongr
    _ = _ := by ring

end

end Step2.D2
