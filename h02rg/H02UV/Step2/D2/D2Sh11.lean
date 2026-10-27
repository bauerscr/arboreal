import Step2.D2.D2Sh10

/-!
# Sharp line 3, part 11: `|S(T') - S(T)| ≤ C_S/T²` for `1 ≤ T ≤ T'`
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

variable {msq T T' : ℝ}

theorem ehat_mono (hm : 0 < msq) (hT : 0 ≤ T) (hTT : T ≤ T') (p : ℂ) :
    ehat Pc msq T p ≤ ehat Pc msq T' p := by
  have hu := uhatC_mem_Ioo hm p
  have hu' : uhatC msq p ∈ Ioc (0 : ℝ) 2 := ⟨hu.1, hu.2.le⟩
  unfold ehat
  have h : ∫ t in Ioi T', t * (Pc.P t).eval (uhatC msq p) ≤ ∫ t in Ioi T, t * (Pc.P t).eval (uhatC msq p) :=
    setIntegral_mono_set (FRD.integrableOn_Ioi Pc hu' hT)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (le_of_lt (lt_of_le_of_lt hT ht))
          (Pc.nonneg t (lt_of_le_of_lt hT ht) _ (uhatC_mem hm.le p)))
      (Eventually.of_forall (Ioi_subset_Ioi hTT))
  have := hu.1
  nlinarith

theorem sinc2_le_one {x : ℝ} (hx : 0 < x) : sinc2 x ≤ 1 := by
  have hpi := pi_pos
  unfold sinc2
  rw [div_le_one (pow_pos (mul_pos hpi hx) 2)]
  have h1 := Real.abs_sin_le_abs (x := π * x)
  rw [abs_of_pos (mul_pos hpi hx)] at h1
  rw [← sq_abs (Real.sin (π * x))]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

def CE1 : ℝ := 1000 * (CΨ / c0 * Som 8) + 2 * Crem

theorem CE1_nonneg : 0 ≤ CE1 := by
  have := CΨ_nonneg; have := c0_pos; have := Som_nonneg (r := 8) (by norm_num); have := Crem_nonneg
  unfold CE1; positivity

/-- `1 - ê_T ≤ C_{E1} ((1 + T√λ)^{-3} + T^{-2})`. -/
theorem one_sub_ehat_le (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 0 < T) (p : ℂ) :
    1 - ehat Pc msq T p ≤ CE1 * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
  have hu := uhatC_mem_Ioo hm p
  have hr := ehat_repr hm.le hT hu.1
  set u := uhatC msq p
  set x := xu u
  have hx0 : 0 < x := xu_pos hu.1
  have hxl := (xu_vs_nu hm.le hm1 p).2
  have hs := sinc2_le_one hx0
  have hs0 : 0 ≤ sinc2 x := by unfold sinc2; positivity
  have hH := one_sub_Hp_le (z := T * x) (by positivity)
  have hdec : ((1 + T * x) ^ 3)⁻¹ ≤ 1000 * ((1 + T * √(lamC p)) ^ 3)⁻¹ := by
    have h1 : 1 + T * √(lamC p) ≤ 10 * (1 + T * x) := by nlinarith
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
      div_le_iff₀ (by positivity)]
    calc (1 + T * √(lamC p)) ^ 3 ≤ (10 * (1 + T * x)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h1 3
      _ = 1000 * (1 + T * x) ^ 3 := by ring
  have hC := CΨ_nonneg; have hc0 := c0_pos; have hS8 := Som_nonneg (r := 8) (by norm_num)
  have hCr := Crem_nonneg
  have e1 : 1 - ehat Pc msq T p ≤ sinc2 x * |1 - Hp (T * x)| + Crem * u / T ^ 2 := by
    have := abs_le.1 hr
    have h2 : sinc2 x * (1 - Hp (T * x)) ≤ sinc2 x * |1 - Hp (T * x)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hs0
    linarith
  have e2 : sinc2 x * |1 - Hp (T * x)| ≤ CΨ / c0 * Som 8 * ((1 + T * x) ^ 3)⁻¹ := by
    calc sinc2 x * |1 - Hp (T * x)| ≤ 1 * |1 - Hp (T * x)| := by gcongr
      _ ≤ _ := by rw [one_mul]; exact hH
  have e3 : Crem * u / T ^ 2 ≤ 2 * Crem * (T ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    have h2 : Crem * u ≤ 2 * Crem := by nlinarith [hu.2]
    have : 0 ≤ (T ^ 2)⁻¹ := by positivity
    nlinarith
  have hI1 : 0 ≤ ((1 + T * √(lamC p)) ^ 3)⁻¹ := by positivity
  calc 1 - ehat Pc msq T p ≤ CΨ / c0 * Som 8 * ((1 + T * x) ^ 3)⁻¹ + 2 * Crem * (T ^ 2)⁻¹ := by
        linarith
    _ ≤ CΨ / c0 * Som 8 * (1000 * ((1 + T * √(lamC p)) ^ 3)⁻¹) + 2 * Crem * (T ^ 2)⁻¹ := by
        gcongr
    _ ≤ CE1 * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
        unfold CE1
        have hI2 : 0 ≤ (T ^ 2)⁻¹ := by positivity
        have hA : 0 ≤ CΨ / c0 * Som 8 := by positivity
        nlinarith [mul_nonneg hA hI2, mul_nonneg hCr hI1]

/-- `|a_{T'} - a_T| ≤ C ((1 + T√λ)^{-3} + T^{-2})`. -/
theorem abs_aT_sub_le (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T) (hTT : T ≤ T') (p : ℂ) :
    |aT msq T' p - aT msq T p| ≤ (18 * Ca + 2 * KPhiE) *
      (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
  have hT0 : 0 < T := by linarith
  have hT' : 1 ≤ T' := le_trans hT hTT
  have hl := lamC_nonneg p
  have hl8 := lamC_le_eight p
  have hν9 : lamC p + msq ≤ 9 := by linarith
  have hCa := Ca_nonneg
  have hK := KPhiE_nonneg
  set I1 := ((1 + T * √(lamC p)) ^ 3)⁻¹
  set I2 := (T ^ 2)⁻¹
  have hI1 : 0 ≤ I1 := by positivity
  have hI2 : 0 ≤ I2 := by positivity
  -- the errors at `T` and `T'`
  have h1 := aT_vs_PhiE hm hm1 hT p
  have h2 := aT_vs_PhiE hm hm1 hT' p
  have hmono1 : ((1 + T' * √(lamC p)) ^ 3)⁻¹ ≤ I1 := by
    apply inv_anti₀ (by positivity)
    have : T * √(lamC p) ≤ T' * √(lamC p) := by gcongr
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hmono2 : (T' ^ 2)⁻¹ ≤ I2 := inv_anti₀ (by positivity) (pow_le_pow_left₀ hT0.le hTT 2)
  have hE1 : Ca * (lamC p + msq) * (I1 + I2) ≤ 9 * Ca * (I1 + I2) := by
    have h0 : 0 ≤ Ca * (I1 + I2) := by positivity
    calc Ca * (lamC p + msq) * (I1 + I2) = (Ca * (I1 + I2)) * (lamC p + msq) := by ring
      _ ≤ (Ca * (I1 + I2)) * 9 := mul_le_mul_of_nonneg_left hν9 h0
      _ = 9 * Ca * (I1 + I2) := by ring
  have hE2 : Ca * (lamC p + msq) * (((1 + T' * √(lamC p)) ^ 3)⁻¹ + (T' ^ 2)⁻¹) ≤
      9 * Ca * (I1 + I2) := by
    have h0 : 0 ≤ ((1 + T' * √(lamC p)) ^ 3)⁻¹ + (T' ^ 2)⁻¹ := by positivity
    calc Ca * (lamC p + msq) * (((1 + T' * √(lamC p)) ^ 3)⁻¹ + (T' ^ 2)⁻¹) ≤
        Ca * 9 * (((1 + T' * √(lamC p)) ^ 3)⁻¹ + (T' ^ 2)⁻¹) := by gcongr
      _ ≤ Ca * 9 * (I1 + I2) := by gcongr <;> assumption
      _ = 9 * Ca * (I1 + I2) := by ring
  -- the profile at `T` and `T'`
  have hΦ : ∀ S, T ≤ S → |1 - PhiE (2 * S * √(lamC p + msq))| ≤ KPhiE * I1 := by
    intro S hS
    have hS0 : 0 < S := by linarith
    have hy : 0 < 2 * S * √(lamC p + msq) := by
      have : 0 < lamC p + msq := by linarith
      positivity
    have hd := PhiE_decay _ hy
    rw [one_add_rpow_neg_three hy.le] at hd
    have h3 : |1 - PhiE (2 * S * √(lamC p + msq))| ≤ KPhiE * ((1 + 2 * S * √(lamC p + msq)) ^ 3)⁻¹ := by
      linarith [abs_nonneg (2 * S * √(lamC p + msq) * PhiE' (2 * S * √(lamC p + msq)))]
    refine h3.trans ?_
    simp only [I1]
    apply mul_le_mul_of_nonneg_left _ hK
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have : √(lamC p) ≤ √(lamC p + msq) := Real.sqrt_le_sqrt (by linarith)
    have : T * √(lamC p) ≤ 2 * S * √(lamC p + msq) := by
      have h0 : 0 ≤ √(lamC p) := Real.sqrt_nonneg _
      calc T * √(lamC p) ≤ S * √(lamC p + msq) := by gcongr
        _ ≤ 2 * S * √(lamC p + msq) := by nlinarith [Real.sqrt_nonneg (lamC p + msq)]
    linarith
  have hΦ1 := hΦ T le_rfl
  have hΦ2 := hΦ T' hTT
  calc |aT msq T' p - aT msq T p| ≤ |aT msq T' p - PhiE (2 * T' * √(lamC p + msq))| +
        |1 - PhiE (2 * T' * √(lamC p + msq))| + |1 - PhiE (2 * T * √(lamC p + msq))| +
        |aT msq T p - PhiE (2 * T * √(lamC p + msq))| := by
        have e : aT msq T' p - aT msq T p = (aT msq T' p - PhiE (2 * T' * √(lamC p + msq))) -
            (1 - PhiE (2 * T' * √(lamC p + msq))) + (1 - PhiE (2 * T * √(lamC p + msq))) -
            (aT msq T p - PhiE (2 * T * √(lamC p + msq))) := by ring
        rw [e]
        refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ 9 * Ca * (I1 + I2) + KPhiE * I1 + KPhiE * I1 + 9 * Ca * (I1 + I2) := by
        gcongr
        · exact h2.trans hE2
        · exact h1.trans hE1
    _ ≤ (18 * Ca + 2 * KPhiE) * (I1 + I2) := by nlinarith

def CS : ℝ := (CE1 + A0 * (18 * Ca + 2 * KPhiE) / 2) * (π ^ 2 * Ia 3 / 4 + (2 * π) ^ 2)

/-- **`|S(T') - S(T)| ≤ C_S/T²`.** -/
theorem ST_sub_le (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 1 ≤ T) (hTT : T ≤ T') :
    |ST msq T' - ST msq T| ≤ CS / T ^ 2 := by
  have hpi := pi_pos
  have hT0 : 0 < T := by linarith
  have hT' : 1 ≤ T' := le_trans hT hTT
  have hl := continuous_lamC
  have hA := A0_nonneg
  have hCa := Ca_nonneg
  have hK := KPhiE_nonneg
  have hCE := CE1_nonneg
  have hS : ∀ S, 1 ≤ S → Bdd fun p => Rq p * (chat Pc msq (Ioc 0 S) p ^ 2 / 2 -
      lamC p ^ 2 * aT msq S p ^ 2 / (4 * (lamC p + msq) ^ 4)) := by
    intro S hS1
    have hc := bdd_chat hm (show 0 ≤ S by linarith)
    have ha := bdd_aT hm hm1 hS1
    have hνi := bdd_nu_inv hm
    exact bdd_Rq.mul (((hc.pow 2).mul (Bdd.const (1 / 2))).sub
      ((((bdd_lamC.pow 2).mul (ha.pow 2)).mul (hνi.pow 4)).mul (Bdd.const (1 / 4))))
      |>.congr fun p => by
        have hl := lamC_nonneg p
        have hν : lamC p + msq ≠ 0 := by linarith
        field_simp
  set Cp := CE1 + A0 * (18 * Ca + 2 * KPhiE) / 2
  have hCp : 0 ≤ Cp := by positivity
  have hpt : ∀ p, |Rq p * (chat Pc msq (Ioc 0 T') p ^ 2 / 2 -
        lamC p ^ 2 * aT msq T' p ^ 2 / (4 * (lamC p + msq) ^ 4)) -
      Rq p * (chat Pc msq (Ioc 0 T) p ^ 2 / 2 -
        lamC p ^ 2 * aT msq T p ^ 2 / (4 * (lamC p + msq) ^ 4))| ≤
      Cp * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by
    intro p
    have h0 := lamC_nonneg p
    have hν : 0 < lamC p + msq := by linarith
    obtain ⟨hR0, hR1⟩ := lamC_parts_le p
    have hRq : Rq p ≤ lamC p ^ 2 := hR1
    have hRq0 : 0 ≤ Rq p := hR0
    -- the `ĉ` part
    have hc1 : chat Pc msq (Ioc 0 T) p = ehat Pc msq T p / (lamC p + msq) :=
      chat_zero_eq hm.le hT0.le hν
    have hc2 : chat Pc msq (Ioc 0 T') p = ehat Pc msq T' p / (lamC p + msq) :=
      chat_zero_eq hm.le (by linarith) hν
    have hu := uhatC_mem_Ioo hm p
    obtain ⟨e0, e1⟩ := ehat_mem Pc hm.le hT0.le hu.1
    obtain ⟨e0', e1'⟩ := ehat_mem Pc hm.le (show 0 ≤ T' by linarith) hu.1
    have hmono := ehat_mono hm hT0.le hTT p
    have hE := one_sub_ehat_le hm hm1 hT0 p
    have hpart1 : |Rq p * (chat Pc msq (Ioc 0 T') p ^ 2 / 2 - chat Pc msq (Ioc 0 T) p ^ 2 / 2)| ≤
        1 - ehat Pc msq T p := by
      rw [hc1, hc2]
      have e : Rq p * ((ehat Pc msq T' p / (lamC p + msq)) ^ 2 / 2 -
          (ehat Pc msq T p / (lamC p + msq)) ^ 2 / 2) =
          Rq p / (lamC p + msq) ^ 2 * ((ehat Pc msq T' p - ehat Pc msq T p) *
            (ehat Pc msq T' p + ehat Pc msq T p) / 2) := by field_simp; ring
      have hd0 : 0 ≤ ehat Pc msq T' p - ehat Pc msq T p := by linarith
      rw [e, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg
        (div_nonneg (mul_nonneg hd0 (by linarith)) (by norm_num))]
      have hq : Rq p / (lamC p + msq) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        calc Rq p ≤ lamC p ^ 2 := hRq
          _ ≤ (lamC p + msq) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
      calc Rq p / (lamC p + msq) ^ 2 * ((ehat Pc msq T' p - ehat Pc msq T p) *
            (ehat Pc msq T' p + ehat Pc msq T p) / 2) ≤
          1 * ((1 - ehat Pc msq T p) * 2 / 2) := by
            have hB : (ehat Pc msq T' p - ehat Pc msq T p) * (ehat Pc msq T' p + ehat Pc msq T p) / 2
                ≤ (1 - ehat Pc msq T p) * 2 / 2 := by
              have h1 : ehat Pc msq T' p - ehat Pc msq T p ≤ 1 - ehat Pc msq T p := by linarith
              have h2 : ehat Pc msq T' p + ehat Pc msq T p ≤ 2 := by linarith
              have h3 : 0 ≤ ehat Pc msq T' p + ehat Pc msq T p := by linarith
              have := mul_le_mul h1 h2 h3 (by linarith)
              linarith
            exact mul_le_mul hq hB (div_nonneg (mul_nonneg hd0 (by linarith)) (by norm_num))
              zero_le_one
        _ = 1 - ehat Pc msq T p := by ring
    -- the `a` part
    have hab := abs_aT_le hm hm1 hT p
    have hab' := abs_aT_le hm hm1 hT' p
    have hd := abs_aT_sub_le hm hm1 hT hTT p
    have hpart2 : |Rq p * (lamC p ^ 2 * aT msq T' p ^ 2 / (4 * (lamC p + msq) ^ 4)) -
        Rq p * (lamC p ^ 2 * aT msq T p ^ 2 / (4 * (lamC p + msq) ^ 4))| ≤
        A0 / 2 * ((18 * Ca + 2 * KPhiE) * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹)) := by
      have e : Rq p * (lamC p ^ 2 * aT msq T' p ^ 2 / (4 * (lamC p + msq) ^ 4)) -
          Rq p * (lamC p ^ 2 * aT msq T p ^ 2 / (4 * (lamC p + msq) ^ 4)) =
          Rq p * lamC p ^ 2 / (4 * (lamC p + msq) ^ 4) *
            ((aT msq T' p - aT msq T p) * (aT msq T' p + aT msq T p)) := by
        field_simp; ring
      rw [e, abs_mul, abs_mul, abs_of_nonneg (by positivity)]
      have hq : Rq p * lamC p ^ 2 / (4 * (lamC p + msq) ^ 4) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]
        have h4 : lamC p ^ 4 ≤ (lamC p + msq) ^ 4 := pow_le_pow_left₀ h0 (by linarith) 4
        nlinarith [mul_le_mul_of_nonneg_right hRq (sq_nonneg (lamC p))]
      have hs : |aT msq T' p + aT msq T p| ≤ 2 * A0 := (abs_add_le _ _).trans (by linarith)
      calc Rq p * lamC p ^ 2 / (4 * (lamC p + msq) ^ 4) * (|aT msq T' p - aT msq T p| *
            |aT msq T' p + aT msq T p|) ≤ 1 / 4 * (((18 * Ca + 2 * KPhiE) *
            (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹)) * (2 * A0)) := by gcongr
        _ = _ := by ring
    have e : Rq p * (chat Pc msq (Ioc 0 T') p ^ 2 / 2 -
          lamC p ^ 2 * aT msq T' p ^ 2 / (4 * (lamC p + msq) ^ 4)) -
        Rq p * (chat Pc msq (Ioc 0 T) p ^ 2 / 2 -
          lamC p ^ 2 * aT msq T p ^ 2 / (4 * (lamC p + msq) ^ 4)) =
        Rq p * (chat Pc msq (Ioc 0 T') p ^ 2 / 2 - chat Pc msq (Ioc 0 T) p ^ 2 / 2) -
        (Rq p * (lamC p ^ 2 * aT msq T' p ^ 2 / (4 * (lamC p + msq) ^ 4)) -
          Rq p * (lamC p ^ 2 * aT msq T p ^ 2 / (4 * (lamC p + msq) ^ 4))) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have hI : 0 ≤ ((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹ := by positivity
    calc _ ≤ CE1 * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) +
          A0 / 2 * ((18 * Ca + 2 * KPhiE) * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹)) :=
          add_le_add (hpart1.trans hE) hpart2
      _ = Cp * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) := by simp only [Cp]; ring
  have hDc : Continuous fun p : ℂ => Cp * (((1 + T * √(lamC p)) ^ 3)⁻¹ + (T ^ 2)⁻¹) :=
    continuous_const.mul ((Continuous.inv₀ (by fun_prop) (fun p => by positivity)).add
      continuous_const)
  unfold ST
  rw [← integral_sub (hS T' hT').integrableOn (hS T hT).integrableOn, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hDc.continuousOn.integrableOn_compact isCompact_BZ)
    (ae_restrict_of_forall_mem measurableSet_BZ fun p _ => by
      rw [Real.norm_eq_abs]; exact hpt p)).trans ?_
  rw [integral_const_mul, integral_add ((Continuous.inv₀ (by fun_prop)
    (fun p => by positivity)).continuousOn.integrableOn_compact isCompact_BZ)
    (continuous_const.continuousOn.integrableOn_compact isCompact_BZ), intBZ_const]
  have h3 := intBZ_dec3 hT0
  unfold CS
  calc Cp * ((∫ p in BZ, ((1 + T * √(lamC p)) ^ 3)⁻¹) + (2 * π) ^ 2 * (T ^ 2)⁻¹)
      ≤ Cp * (π ^ 2 * Ia 3 / (4 * T ^ 2) + (2 * π) ^ 2 * (T ^ 2)⁻¹) := by gcongr
    _ = _ := by simp only [Cp]; field_simp

end

end Step2.D2
