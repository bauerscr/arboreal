import Step2.D2.D2Sh6

/-!
# Sharp line 3, part 7: `|a_T - Φ(2T√ν)| ≤ C_a ν ((1 + T√λ)^{-3} + T^{-2})`
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

variable {msq T : ℝ}

/-- The constants of the comparison. -/
def Aa : ℝ := (2 * c0)⁻¹ * Som 8 * (π ^ 2 * Cfp + 4 * π ^ 2 * Cd)

def Ba : ℝ := 2 * π ^ 2 * (C1d * Som 8) / 3

def Ca : ℝ := 2000 * Aa + Ba + (2 * Kc + KPhiE)

theorem Aa_nonneg : 0 ≤ Aa := by
  have := c0_pos; have := Cfp_nonneg; have := Cd_nonneg; have := Som_nonneg (r := 8) (by norm_num)
  unfold Aa; positivity

theorem Ba_nonneg : 0 ≤ Ba := by
  have := C1d_nonneg; have := Som_nonneg (r := 8) (by norm_num)
  unfold Ba; positivity

theorem Ca_nonneg : 0 ≤ Ca := by
  have := Aa_nonneg; have := Ba_nonneg; have := Kc_nonneg; have := KPhiE_nonneg
  unfold Ca; positivity

set_option maxHeartbeats 1000000 in
/-- **The angle region `x ≤ 1/4`.** -/
theorem aT_vs_PhiE_small (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T) (p : ℂ)
    (hx : xu (uhatC msq p) ≤ 1 / 4) :
    |aT msq T p - PhiE (2 * T * √(lamC p + msq))| ≤
      Aa * (xu (uhatC msq p) ^ 2 + msq) * ((1 + T * xu (uhatC msq p)) ^ 3)⁻¹ +
        Ba * xu (uhatC msq p) ^ 3 / T ^ 3 := by
  have hpi := pi_pos
  have hc0 := c0_pos
  have hcc := cc_pos
  have hT0 : 0 < T := by linarith
  have hu := uhatC_mem_Ioo hm p
  set u := uhatC msq p
  set x := xu u
  have hx0 : 0 < x := xu_pos hu.1
  have hxI : x ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hx0, by linarith⟩
  -- the representation
  obtain ⟨hint, hrep⟩ := tail_repr hxI hT0
  set E := (∫ τ in Ioi T, τ * Dp τ x) + 2 * c0 / (cc * x ^ 3) * (1 - PhiH (T * x))
  have hsnx := snx_pos hu
  have htl : tl msq T p = (∫ τ in Ioi T, τ * Dp τ x) / snx u := by
    unfold tl
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    rw [Pd_eq hu τ]
    unfold snx; ring
  have hrho : u ^ 2 / snx u * (2 * c0 / (cc * x ^ 3)) = rhoS x := by
    rw [u_sq_div_snx hu]
    show Real.sin (π * x) ^ 3 / (π * Real.cos (π * x)) * (2 * c0 / (cc * x ^ 3)) = rhoS x
    have hc := cos_pos_quarter ⟨hx0, hx⟩
    rw [rhoS, cc]
    field_simp
  have hEq : aT msq T p = 1 - rhoS x * (1 - PhiH (T * x)) + u ^ 2 / snx u * E := by
    unfold aT
    rw [htl, ← hrho]
    simp only [E]
    field_simp
    ring
  -- the momentum variable
  obtain ⟨hy1, hy2⟩ := ymom_bounds hm.le p hx0 hx
  set y := 2 * √(lamC p + msq) / kap
  have hPhiE : PhiE (2 * T * √(lamC p + msq)) = PhiH (T * y) := by
    unfold PhiE; congr 1; simp only [y]; ring
  rw [hPhiE, hEq]
  have hdecomp : 1 - rhoS x * (1 - PhiH (T * x)) + u ^ 2 / snx u * E - PhiH (T * y) =
      (1 - rhoS x) * (1 - PhiH (T * x)) + (PhiH (T * x) - PhiH (T * y)) + u ^ 2 / snx u * E := by
    ring
  rw [hdecomp]
  -- the three bounds
  have b1 : |(1 - rhoS x) * (1 - PhiH (T * x))| ≤
      π ^ 2 * x ^ 2 * ((2 * c0)⁻¹ * Cfp * Som 8 * ((1 + T * x) ^ 3)⁻¹) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul (abs_rhoS_sub_le ⟨hx0, hx⟩) (one_sub_PhiH_le (by positivity))
      (abs_nonneg _) (by positivity)
  have b2 : |PhiH (T * x) - PhiH (T * y)| ≤
      (2 * c0)⁻¹ * Cd * Som 8 * (2 * (msq / 8 + π ^ 2 * x ^ 2 / 4) * (8 * ((1 + T * x) ^ 3)⁻¹)) := by
    have hm0 : 0 < T * x / 2 := by positivity
    refine (abs_PhiH_sub_le hm0 (by linarith [mul_pos hT0 hx0]) (by nlinarith [hy1, hT0])).trans ?_
    have hCd := Cd_nonneg
    have hS := Som_nonneg (r := 8) (by norm_num)
    gcongr
    rw [← mul_sub, abs_mul, abs_of_pos hT0]
    have h3 : ((1 + T * x / 2) ^ 3)⁻¹ ≤ 8 * ((1 + T * x) ^ 3)⁻¹ := by
      have := inv_one_add_div_pow_le (z := T * x) (by positivity) 1 3
      norm_num at this ⊢; linarith
    calc T * |x - y| / (T * x / 2 * (1 + T * x / 2) ^ 3)
        = 2 * (|x - y| / x) * ((1 + T * x / 2) ^ 3)⁻¹ := by field_simp
      _ ≤ 2 * (msq / 8 + π ^ 2 * x ^ 2 / 4) * (8 * ((1 + T * x) ^ 3)⁻¹) := by
          gcongr
          rw [div_le_iff₀ hx0]; linarith
  have b3 : |u ^ 2 / snx u * E| ≤ 2 * π ^ 2 * x ^ 3 * (C1d * Som 8 * (T ^ 3)⁻¹ / 3) := by
    rw [abs_mul, abs_of_pos (div_pos (pow_pos hu.1 2) hsnx)]
    exact mul_le_mul (u_sq_div_snx_le hu hx) hrep (abs_nonneg _) (by positivity)
  have hq : msq / 8 ≤ π ^ 2 * msq / 4 := by
    have := pi_gt_three
    have : 1 ≤ π ^ 2 := by nlinarith
    nlinarith [hm.le]
  calc |(1 - rhoS x) * (1 - PhiH (T * x)) + (PhiH (T * x) - PhiH (T * y)) + u ^ 2 / snx u * E|
      ≤ |(1 - rhoS x) * (1 - PhiH (T * x))| + |PhiH (T * x) - PhiH (T * y)| + |u ^ 2 / snx u * E| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ π ^ 2 * x ^ 2 * ((2 * c0)⁻¹ * Cfp * Som 8 * ((1 + T * x) ^ 3)⁻¹) +
        (2 * c0)⁻¹ * Cd * Som 8 * (2 * (msq / 8 + π ^ 2 * x ^ 2 / 4) * (8 * ((1 + T * x) ^ 3)⁻¹)) +
        2 * π ^ 2 * x ^ 3 * (C1d * Som 8 * (T ^ 3)⁻¹ / 3) := add_le_add (add_le_add b1 b2) b3
    _ ≤ Aa * (x ^ 2 + msq) * ((1 + T * x) ^ 3)⁻¹ + Ba * x ^ 3 / T ^ 3 := by
        unfold Aa Ba
        have hS := Som_nonneg (r := 8) (by norm_num)
        have hCfp := Cfp_nonneg
        have hCd := Cd_nonneg
        have hI : 0 ≤ ((1 + T * x) ^ 3)⁻¹ := by positivity
        have hm8 : 2 * (msq / 8 + π ^ 2 * x ^ 2 / 4) * 8 ≤ 4 * π ^ 2 * (x ^ 2 + msq) := by nlinarith
        have k1 : (2 * c0)⁻¹ * Cd * Som 8 * (2 * (msq / 8 + π ^ 2 * x ^ 2 / 4) * (8 * ((1 + T * x) ^ 3)⁻¹))
            ≤ (2 * c0)⁻¹ * Som 8 * (4 * π ^ 2 * Cd) * (x ^ 2 + msq) * ((1 + T * x) ^ 3)⁻¹ := by
          have : (2 * c0)⁻¹ * Cd * Som 8 * (2 * (msq / 8 + π ^ 2 * x ^ 2 / 4) * (8 * ((1 + T * x) ^ 3)⁻¹)) =
              (2 * c0)⁻¹ * Som 8 * Cd * ((1 + T * x) ^ 3)⁻¹ * (2 * (msq / 8 + π ^ 2 * x ^ 2 / 4) * 8) := by
            ring
          rw [this]
          have h0 : 0 ≤ (2 * c0)⁻¹ * Som 8 * Cd * ((1 + T * x) ^ 3)⁻¹ := by positivity
          calc _ ≤ (2 * c0)⁻¹ * Som 8 * Cd * ((1 + T * x) ^ 3)⁻¹ * (4 * π ^ 2 * (x ^ 2 + msq)) := by
                gcongr
            _ = _ := by ring
        have k2 : π ^ 2 * x ^ 2 * ((2 * c0)⁻¹ * Cfp * Som 8 * ((1 + T * x) ^ 3)⁻¹) ≤
            (2 * c0)⁻¹ * Som 8 * (π ^ 2 * Cfp) * (x ^ 2 + msq) * ((1 + T * x) ^ 3)⁻¹ := by
          have : π ^ 2 * x ^ 2 * ((2 * c0)⁻¹ * Cfp * Som 8 * ((1 + T * x) ^ 3)⁻¹) =
              (2 * c0)⁻¹ * Som 8 * (π ^ 2 * Cfp) * x ^ 2 * ((1 + T * x) ^ 3)⁻¹ := by ring
          rw [this]
          have h0 : 0 ≤ (2 * c0)⁻¹ * Som 8 * (π ^ 2 * Cfp) := by positivity
          gcongr; linarith
        have k3 : 2 * π ^ 2 * x ^ 3 * (C1d * Som 8 * (T ^ 3)⁻¹ / 3) =
            2 * π ^ 2 * (C1d * Som 8) / 3 * x ^ 3 / T ^ 3 := by field_simp
        rw [k3]
        have kA : (2 * c0)⁻¹ * Som 8 * (π ^ 2 * Cfp + 4 * π ^ 2 * Cd) * (x ^ 2 + msq) * ((1 + T * x) ^ 3)⁻¹ =
            (2 * c0)⁻¹ * Som 8 * (π ^ 2 * Cfp) * (x ^ 2 + msq) * ((1 + T * x) ^ 3)⁻¹ +
            (2 * c0)⁻¹ * Som 8 * (4 * π ^ 2 * Cd) * (x ^ 2 + msq) * ((1 + T * x) ^ 3)⁻¹ := by ring
        linarith

theorem lt_quarter_of_u {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : xu u ≤ 1 / 4 := by
  rw [← xu_one]; exact xu_mono hu1 hu (by norm_num)

/-- **`|a_T - Φ(2T√ν)| ≤ C_a ν ((1+T√λ)^{-3} + T^{-2})`.** -/
theorem aT_vs_PhiE (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T) (p : ℂ) :
    |aT msq T p - PhiE (2 * T * √(lamC p + msq))| ≤
      Ca * (lamC p + msq) * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
  have hT0 : 0 < T := by linarith
  have hl := lamC_nonneg p
  have hu := uhatC_mem_Ioo hm p
  set u := uhatC msq p
  set ν := lamC p + msq
  have hν : 0 < ν := by simp only [ν]; linarith
  have hCa := Ca_nonneg
  have hI1 : 0 ≤ ((1 + T * √(lamC p)) ^ 3)⁻¹ := by positivity
  have hI2 : 0 < (T ^ 2)⁻¹ := by positivity
  by_cases hx : xu u ≤ 1 / 4
  · have h := aT_vs_PhiE_small hm hm1 hT p hx
    obtain ⟨hx2, hxl⟩ := xu_vs_nu hm.le hm1 p
    set x := xu u
    have hx0 : 0 < x := xu_pos hu.1
    have hx1 : x ≤ 1 := by linarith
    -- `(1 + Tx)^{-3} ≤ 1000 (1 + T√λ)^{-3}`
    have hdec : ((1 + T * x) ^ 3)⁻¹ ≤ 1000 * ((1 + T * √(lamC p)) ^ 3)⁻¹ := by
      have h1 : 1 + T * √(lamC p) ≤ 10 * (1 + T * x) := by nlinarith
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
        div_le_iff₀ (by positivity)]
      calc (1 + T * √(lamC p)) ^ 3 ≤ (10 * (1 + T * x)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h1 3
        _ = 1000 * (1 + T * x) ^ 3 := by ring
    have hA := Aa_nonneg
    have hB := Ba_nonneg
    have e1 : x ^ 2 + msq ≤ 2 * ν := by simp only [ν]; linarith
    have e2 : x ^ 3 / T ^ 3 ≤ ν * (T ^ 2)⁻¹ := by
      have h3 : x ^ 3 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
      have h4 : T ^ 2 ≤ T ^ 3 := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      calc x ^ 3 ≤ ν := by simp only [ν] at hx2 ⊢; linarith
        _ = ν * (T ^ 2)⁻¹ * T ^ 2 := by field_simp
        _ ≤ ν * (T ^ 2)⁻¹ * T ^ 3 := by gcongr
    calc _ ≤ Aa * (x ^ 2 + msq) * ((1 + T * x) ^ 3)⁻¹ + Ba * x ^ 3 / T ^ 3 := h
      _ ≤ Aa * (2 * ν) * (1000 * ((1 + T * √(lamC p)) ^ 3)⁻¹) + Ba * (ν * (T ^ 2)⁻¹) := by
          rw [mul_div_assoc]; gcongr
      _ ≤ Ca * ν * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
          unfold Ca
          have hK := Kc_nonneg; have hKP := KPhiE_nonneg
          have : 0 ≤ ν * ((1 + T * √(lamC p)) ^ 3)⁻¹ := by positivity
          have : 0 ≤ ν * (T ^ 2)⁻¹ := by positivity
          nlinarith
  · push Not at hx
    have hu1 : 1 ≤ u := by
      by_contra h; push Not at h
      exact absurd (lt_quarter_of_u hu.1.le h.le) (not_le.2 hx)
    have hK : (0 : ℝ) < 2 * 2 + msq := by linarith
    have hν4 : 4 ≤ ν := by
      have : ν = (2 * 2 + msq) * u := by
        simp only [ν, u, uhatC_eq']; field_simp
      rw [this]; nlinarith
    have h1 : |aT msq T p - 1| ≤ 2 * Kc * (T ^ 2)⁻¹ := by
      unfold aT
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have ht := abs_tail_corner ⟨hu1, hu.2⟩ hT0
      have hu4 : u ^ 2 ≤ 4 := by nlinarith [hu.2]
      have := Kc_nonneg
      calc u ^ 2 * |tl msq T p| ≤ 4 * (Kc * (T ^ 2)⁻¹ / 2) := by
            unfold tl; exact mul_le_mul hu4 ht (abs_nonneg _) (by norm_num)
        _ = 2 * Kc * (T ^ 2)⁻¹ := by ring
    have h2 : |1 - PhiE (2 * T * √ν)| ≤ KPhiE * (T ^ 2)⁻¹ := by
      have hs : 0 < 2 * T * √ν := by positivity
      have hd := PhiE_decay (2 * T * √ν) hs
      have hy : T ≤ 2 * T * √ν := by
        have : 1 ≤ √ν := by rw [Real.le_sqrt (by norm_num) hν.le]; linarith
        nlinarith
      have hr : (1 + 2 * T * √ν) ^ (-(3 : ℝ)) ≤ (T ^ 2)⁻¹ := by
        rw [one_add_rpow_neg_three hs.le]
        apply inv_anti₀ (by positivity)
        nlinarith [sq_nonneg T, sq_nonneg (2 * T * √ν)]
      have := KPhiE_nonneg
      have h3 : |1 - PhiE (2 * T * √ν)| ≤ KPhiE * (1 + 2 * T * √ν) ^ (-(3 : ℝ)) := by
        linarith [abs_nonneg (2 * T * √ν * PhiE' (2 * T * √ν))]
      exact h3.trans (by gcongr)
    calc |aT msq T p - PhiE (2 * T * √ν)| ≤ |aT msq T p - 1| + |1 - PhiE (2 * T * √ν)| := by
          rw [show aT msq T p - PhiE (2 * T * √ν) = (aT msq T p - 1) + (1 - PhiE (2 * T * √ν)) by
            ring]
          exact abs_add_le _ _
      _ ≤ (2 * Kc + KPhiE) * (T ^ 2)⁻¹ := by linarith
      _ ≤ Ca * ν * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
          unfold Ca
          have hA := Aa_nonneg; have hB := Ba_nonneg
          have hK := Kc_nonneg; have hKP := KPhiE_nonneg
          have : 0 ≤ ν * ((1 + T * √(lamC p)) ^ 3)⁻¹ := by positivity
          have h5 : (2 * Kc + KPhiE) * (T ^ 2)⁻¹ ≤ (2 * Kc + KPhiE) * (ν * (T ^ 2)⁻¹) := by
            gcongr; nlinarith
          have h6 : 2 * Kc + KPhiE ≤ 2000 * Aa + Ba + (2 * Kc + KPhiE) := by linarith
          calc (2 * Kc + KPhiE) * (T ^ 2)⁻¹ ≤ (2 * Kc + KPhiE) * (ν * (T ^ 2)⁻¹) := h5
            _ ≤ (2000 * Aa + Ba + (2 * Kc + KPhiE)) * (ν * (T ^ 2)⁻¹) := by gcongr
            _ ≤ (2000 * Aa + Ba + (2 * Kc + KPhiE)) * ν *
                (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
                have : 0 ≤ (2000 * Aa + Ba + (2 * Kc + KPhiE)) * ν := by positivity
                nlinarith

end

end Step2.D2