import Step2.D2.D2Sh1
import Step2.D2.D2Bv2

/-!
# Sharp line 3, part 2: the `k = 0` part of `D_τ`

`D⁰_τ(x) = ∑_i a_i (τ/2^i) ψ'(τx/2^i)/c` (all `i`, image `k = 0`):

* `abs_Dp_sub_D0_le`: `|D_τ(x) - D⁰_τ(x)| ≤ C₁ S₈ τ^{-5}` for `x ∈ [0, 1/2]`, `τ > 0`;
* `integral_D0`: `∫_T^∞ τ D⁰_τ(x) dτ = -(c x³)⁻¹ ∑_i ω_i f(Tx/2^i) = -(2c₀/(c x³))(1 - Φ_H(Tx))`;
* `tail_repr`: `|∫_T^∞ τ D_τ(x) dτ + (2c₀/(c x³))(1 - Φ_H(Tx))| ≤ C₁ S₈/(3T³)`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

theorem two_pow_pow (i n : ℕ) : ((2 : ℝ) ^ i) ^ n = ((2 : ℝ) ^ n) ^ i := by
  rw [← pow_mul, ← pow_mul, mul_comm]

theorem continuous_ψd : Continuous ψd := by
  have h : ψd = fun r => (SchwartzMap.derivCLM ℝ ℂ ΨS r).re := by
    funext r; unfold ψd; rw [deriv_ΨS_eq]
  rw [h]
  exact Complex.continuous_re.comp (SchwartzMap.derivCLM ℝ ℂ ΨS).continuous

theorem abs_ψd_le_Cd (r : ℝ) : |ψd r| ≤ Cd := by
  refine (ψd_le r).trans ?_
  have := Cd_nonneg
  exact div_le_self this (one_le_pow₀ (by linarith [abs_nonneg r]))

/-- The terms of `D⁰`. -/
def tP (x τ : ℝ) (i : ℕ) : ℝ := PrePtFamily.a i * (τ / 2 ^ i) * ψd (τ * x / 2 ^ i) / cc

/-- `D⁰_τ(x) = ∑_i a_i (τ/2^i) ψ'(τx/2^i)/c`. -/
def D0 (τ x : ℝ) : ℝ := ∑' i, tP x τ i

/-- The constant `C₁ = (64 C_d B_ℤ + M₂/2)/c`. -/
def C1d : ℝ := (64 * Cd * Bz + M2 / 2) / cc

theorem C1d_nonneg : 0 ≤ C1d := by
  have := Cd_nonneg; have := Bz_nonneg; have := M2_nonneg; have := cc_pos
  unfold C1d; positivity

theorem a_eq_om (i : ℕ) : PrePtFamily.a i = om i / 4 ^ i := by
  rw [← a_mul_four_pow]; field_simp

/-- The small-`s` terms. -/
theorem abs_tP_small {x τ : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (hτ : 0 < τ) {i : ℕ}
    (hs : τ / 2 ^ i < 1) : |tP x τ i| ≤ C1d * (om i * 8 ^ i) * (τ ^ 5)⁻¹ := by
  have hcc := cc_pos
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  have hτ2 : τ < 2 ^ i := by rwa [div_lt_one h2] at hs
  have hψ : |ψd (τ * x / 2 ^ i)| ≤ M2 * (τ / 2 ^ i) / 2 := by
    refine (abs_ψd_le _).trans ?_
    rw [abs_of_nonneg (by have := hx.1; positivity)]
    have := M2_nonneg
    calc M2 * (τ * x / 2 ^ i) = M2 * (τ / 2 ^ i) * x := by ring
      _ ≤ M2 * (τ / 2 ^ i) * (1 / 2) := by gcongr; exact hx.2
      _ = M2 * (τ / 2 ^ i) / 2 := by ring
  have hM := M2_nonneg
  have hom := om_pos i
  -- `τ² 16^{-i} ≤ 8^i τ^{-5}`
  have key : τ ^ 2 / 16 ^ i ≤ 8 ^ i * (τ ^ 5)⁻¹ := by
    have h7 : τ ^ 7 ≤ (2 ^ i) ^ 7 := pow_le_pow_left₀ hτ.le hτ2.le 7
    rw [div_le_iff₀ (by positivity), ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc τ ^ 2 * τ ^ 5 = τ ^ 7 := by ring
      _ ≤ (2 ^ i) ^ 7 := h7
      _ = 8 ^ i * 16 ^ i := by rw [two_pow_pow, ← mul_pow]; norm_num
  unfold tP
  rw [abs_div, abs_of_pos hcc, abs_mul, abs_mul, abs_of_pos (PrePtFamily.a_pos i),
    abs_of_pos (by positivity : 0 < τ / 2 ^ i), a_eq_om]
  calc om i / 4 ^ i * (τ / 2 ^ i) * |ψd (τ * x / 2 ^ i)| / cc
      ≤ om i / 4 ^ i * (τ / 2 ^ i) * (M2 * (τ / 2 ^ i) / 2) / cc := by gcongr
    _ = M2 / 2 / cc * om i * (τ ^ 2 / 16 ^ i) := by
        rw [show (16 : ℝ) ^ i = 4 ^ i * (2 ^ i) ^ 2 by rw [two_pow_pow, ← mul_pow]; norm_num]
        field_simp
    _ ≤ M2 / 2 / cc * om i * (8 ^ i * (τ ^ 5)⁻¹) := by gcongr
    _ ≤ C1d * (om i * 8 ^ i) * (τ ^ 5)⁻¹ := by
        have h1 : M2 / 2 / cc ≤ C1d := by
          unfold C1d
          have : 0 ≤ 64 * Cd * Bz := by have := Cd_nonneg; have := Bz_nonneg; positivity
          gcongr; linarith
        have : 0 ≤ om i * (8 ^ i * (τ ^ 5)⁻¹) := by positivity
        calc M2 / 2 / cc * om i * (8 ^ i * (τ ^ 5)⁻¹) = M2 / 2 / cc * (om i * (8 ^ i * (τ ^ 5)⁻¹)) := by
              ring
          _ ≤ C1d * (om i * (8 ^ i * (τ ^ 5)⁻¹)) := by gcongr
          _ = _ := by ring

/-- The images `k ≠ 0` for `s ≥ 1`. -/
theorem abs_images_le {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (hs : 1 ≤ s) :
    Summable (fun k : ℤ => if k = 0 then 0 else ψd (s * (x + k))) ∧
      |∑' k : ℤ, (if k = 0 then 0 else ψd (s * (x + k)))| ≤ 64 * Cd * Bz * (s ^ 6)⁻¹ := by
  have hCd := Cd_nonneg
  have hs0 : 0 < s := by linarith
  have hterm : ∀ k : ℤ, |if k = 0 then 0 else ψd (s * (x + k))| ≤
      64 * Cd * (s ^ 6)⁻¹ * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
    intro k
    split_ifs with hk
    · simp; positivity
    · refine (ψd_le _).trans ?_
      obtain ⟨-, h2⟩ := FRD.PtF.abs_add_int_ge hx k
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
      have ha : |s * (x + k)| = s * |x + k| := by rw [abs_mul, abs_of_pos hs0]
      have e1 : s / 2 ≤ |s * (x + k)| := by rw [ha]; nlinarith
      have e2 : 1 + |(k : ℝ)| / 2 ≤ 1 + |s * (x + k)| := by rw [ha]; nlinarith
      have e3 : s ^ 6 ≤ 64 * (1 + |s * (x + k)|) ^ 6 := by
        have : s ≤ 2 * (1 + |s * (x + k)|) := by linarith
        calc s ^ 6 ≤ (2 * (1 + |s * (x + k)|)) ^ 6 := pow_le_pow_left₀ hs0.le this 6
          _ = 64 * (1 + |s * (x + k)|) ^ 6 := by ring
      have key : s ^ 6 * (1 + |(k : ℝ)| / 2) ^ 2 ≤ 64 * (1 + |s * (x + k)|) ^ 8 := by
        calc s ^ 6 * (1 + |(k : ℝ)| / 2) ^ 2 ≤ (64 * (1 + |s * (x + k)|) ^ 6) *
              (1 + |s * (x + k)|) ^ 2 := by gcongr
          _ = 64 * (1 + |s * (x + k)|) ^ 8 := by ring
      rw [div_le_iff₀ (by positivity)]
      have hp : 0 < s ^ 6 * (1 + |(k : ℝ)| / 2) ^ 2 := by positivity
      calc Cd = 64 * Cd * (s ^ 6)⁻¹ * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ *
            (s ^ 6 * (1 + |(k : ℝ)| / 2) ^ 2) / 64 := by field_simp
        _ ≤ 64 * Cd * (s ^ 6)⁻¹ * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ *
            (64 * (1 + |s * (x + k)|) ^ 8) / 64 := by gcongr
        _ = _ := by ring
  have hsb : Summable fun k : ℤ => 64 * Cd * (s ^ 6)⁻¹ * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ :=
    FRD.PtF.summable_b.mul_left _
  have hsum : Summable fun k : ℤ => |if k = 0 then 0 else ψd (s * (x + k))| :=
    hsb.of_nonneg_of_le (fun k => abs_nonneg _) hterm
  refine ⟨hsum.of_abs, ?_⟩
  calc |∑' k : ℤ, (if k = 0 then 0 else ψd (s * (x + k)))|
      ≤ ∑' k : ℤ, |if k = 0 then 0 else ψd (s * (x + k))| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun k : ℤ =>
          if k = 0 then 0 else ψd (s * (x + k))) (by simpa only [Real.norm_eq_abs] using hsum)
    _ ≤ ∑' k : ℤ, 64 * Cd * (s ^ 6)⁻¹ * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ :=
        hsum.tsum_le_tsum hterm hsb
    _ = 64 * Cd * Bz * (s ^ 6)⁻¹ := by rw [tsum_mul_left, Bz]; ring

/-- The large-`s` terms of `D` minus those of `D⁰`. -/
theorem abs_term_large {x τ : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (hτ : 0 < τ) {i : ℕ}
    (hs : 1 ≤ τ / 2 ^ i) :
    |PrePtFamily.a i * (1 / (cc * (τ / 2 ^ i)) *
        (((Polynomial.derivative (Q (τ / 2 ^ i)))).eval (1 - Real.cos (2 * π * x)) *
          (2 * π * Real.sin (2 * π * x)))) - tP x τ i| ≤ C1d * (om i * 8 ^ i) * (τ ^ 5)⁻¹ := by
  set s := τ / 2 ^ i with hsdef
  have hs0 : 0 < s := by linarith
  have hcc := cc_pos
  have hxI : x ∈ Ioo (-1 / 4 : ℝ) (3 / 4) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨hsumI, hbI⟩ := abs_images_le hx hs
  obtain ⟨hsum, -⟩ := exists_sum_ψd_bound.choose_spec.2 s hs x hx
  have hsum' : Summable fun k : ℤ => s ^ 2 * ψd (s * (x + k)) :=
    (hsum.mul_left (s ^ 2)).of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)])
  rw [Qderiv_eq hs hxI, hsum'.tsum_eq_add_tsum_ite 0]
  have e : (∑' k : ℤ, if k = 0 then 0 else s ^ 2 * ψd (s * (x + k))) =
      s ^ 2 * ∑' k : ℤ, (if k = 0 then 0 else ψd (s * (x + k))) := by
    rw [← tsum_mul_left]; congr 1; funext k; split_ifs <;> simp
  rw [e]
  have e2 : PrePtFamily.a i * (1 / (cc * s) * (s ^ 2 * ψd (s * (x + ((0 : ℤ) : ℝ))) +
      s ^ 2 * ∑' k : ℤ, (if k = 0 then 0 else ψd (s * (x + k))))) - tP x τ i =
      PrePtFamily.a i * (s / cc) * ∑' k : ℤ, (if k = 0 then 0 else ψd (s * (x + k))) := by
    unfold tP
    rw [← hsdef]
    simp only [Int.cast_zero, add_zero]
    rw [show τ * x / 2 ^ i = s * x by rw [hsdef]; ring]
    field_simp
    ring
  rw [e2, abs_mul, abs_mul, abs_of_pos (PrePtFamily.a_pos i), abs_of_pos (by positivity : 0 < s / cc),
    a_eq_om]
  have hom := om_pos i
  have key : s ^ 5 = τ ^ 5 / 32 ^ i := by
    rw [hsdef, div_pow, two_pow_pow]; norm_num
  calc om i / 4 ^ i * (s / cc) * |∑' k : ℤ, (if k = 0 then 0 else ψd (s * (x + k)))|
      ≤ om i / 4 ^ i * (s / cc) * (64 * Cd * Bz * (s ^ 6)⁻¹) := by gcongr
    _ = 64 * Cd * Bz / cc * om i / (4 ^ i * s ^ 5) := by field_simp
    _ = 64 * Cd * Bz / cc * (om i * 8 ^ i) * (τ ^ 5)⁻¹ := by
        rw [key]
        have : (32 : ℝ) ^ i = 4 ^ i * 8 ^ i := by rw [← mul_pow]; norm_num
        rw [this]; field_simp
    _ ≤ C1d * (om i * 8 ^ i) * (τ ^ 5)⁻¹ := by
        have h1 : 64 * Cd * Bz / cc ≤ C1d := by
          unfold C1d
          have := M2_nonneg
          gcongr; linarith
        have : 0 ≤ (om i * 8 ^ i) * (τ ^ 5)⁻¹ := by positivity
        nlinarith

theorem summable_tP {x τ : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (hτ : 0 < τ) :
    Summable (tP x τ) := by
  have hcc := cc_pos
  refine (summable_om.mul_right (τ * Cd / cc)).of_norm_bounded (fun i => ?_)
  rw [Real.norm_eq_abs]
  unfold tP
  rw [abs_div, abs_of_pos hcc, abs_mul, abs_mul, abs_of_pos (PrePtFamily.a_pos i),
    abs_of_pos (by positivity : 0 < τ / 2 ^ i), a_eq_om]
  have h1 : τ / 2 ^ i ≤ τ := div_le_self hτ.le (one_le_pow₀ (by norm_num))
  have h2 : om i / 4 ^ i ≤ om i := div_le_self (om_pos i).le (one_le_pow₀ (by norm_num))
  have h3 := abs_ψd_le_Cd (τ * x / 2 ^ i)
  have := Cd_nonneg
  calc om i / 4 ^ i * (τ / 2 ^ i) * |ψd (τ * x / 2 ^ i)| / cc ≤ om i * τ * Cd / cc := by
        gcongr
        · exact mul_nonneg (om_pos i).le hτ.le
        · exact (om_pos i).le
    _ = om i * (τ * Cd / cc) := by ring

/-- **`|D_τ(x) - D⁰_τ(x)| ≤ C₁ S₈ τ^{-5}`.** -/
theorem abs_Dp_sub_D0_le {x τ : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) (hτ : 0 < τ) :
    |Dp τ x - D0 τ x| ≤ C1d * Som 8 * (τ ^ 5)⁻¹ := by
  set R := Finset.range (⌊τ⌋₊ + 1)
  set g : ℕ → ℝ := fun i => PrePtFamily.a i *
      (if τ / 2 ^ i < 1 then 0 else 1 / (cc * (τ / 2 ^ i)) *
        (((Polynomial.derivative (Q (τ / 2 ^ i)))).eval (1 - Real.cos (2 * π * x)) *
          (2 * π * Real.sin (2 * π * x))))
  have hDp : Dp τ x = ∑' i, (if i ∈ R then g i else 0) := by
    rw [Dp_eq, tsum_eq_sum (s := R) (fun i hi => by simp [hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [hi, g]
  have hsg : Summable fun i => (if i ∈ R then g i else 0) :=
    summable_of_ne_finset_zero (s := R) (fun i hi => by simp [hi])
  have hst := summable_tP hx hτ
  have hdiff : Dp τ x - D0 τ x = ∑' i, ((if i ∈ R then g i else 0) - tP x τ i) := by
    rw [hDp, D0, Summable.tsum_sub hsg hst]
  have hb : ∀ i, |(if i ∈ R then g i else 0) - tP x τ i| ≤ C1d * (τ ^ 5)⁻¹ * (om i * 8 ^ i) := by
    intro i
    have hsmall : τ / 2 ^ i < 1 → |tP x τ i| ≤ C1d * (τ ^ 5)⁻¹ * (om i * 8 ^ i) := fun h => by
      have := abs_tP_small hx hτ h; linarith
    by_cases hi : i ∈ R
    · rw [if_pos hi]
      simp only [g]
      split_ifs with h
      · rw [mul_zero, zero_sub, abs_neg]; exact hsmall h
      · push Not at h
        have := abs_term_large hx hτ h; linarith
    · rw [if_neg hi, zero_sub, abs_neg]
      apply hsmall
      simp only [R, Finset.mem_range, not_lt] at hi
      have h1 : τ < (⌊τ⌋₊ + 1 : ℕ) := by push_cast; exact Nat.lt_floor_add_one τ
      have h2 : ((⌊τ⌋₊ + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi
      have h3 : (i : ℝ) < 2 ^ i := by exact_mod_cast Nat.lt_two_pow_self
      rw [div_lt_one (by positivity)]; linarith
  have hf : ∀ i, |((if i ∈ R then g i else 0) - tP x τ i) / om i| ≤ C1d * (τ ^ 5)⁻¹ * 8 ^ i := by
    intro i
    rw [abs_div, abs_of_pos (om_pos i), div_le_iff₀ (om_pos i)]
    calc _ ≤ C1d * (τ ^ 5)⁻¹ * (om i * 8 ^ i) := hb i
      _ = _ := by ring
  have := (tsum_om_le (r := 8) (by norm_num) hf).2
  have e : (fun i => om i * (((if i ∈ R then g i else 0) - tP x τ i) / om i)) =
      fun i => (if i ∈ R then g i else 0) - tP x τ i := by
    funext i; field_simp [(om_pos i).ne']
  rw [e] at this
  rw [hdiff]
  calc _ ≤ C1d * (τ ^ 5)⁻¹ * Som 8 := this
    _ = _ := by ring

end

end Step2.D2
