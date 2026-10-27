import Step2.D2.D2Sh9

/-!
# Sharp line 3, part 10: removing the mass, `|J_Φ(T) - J₀(T)| ≤ C_m m² T²`

`J₀(T) = ∫ Φ(2T√λ)²/λ` (`fc (Φ²) (2T)`).
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

variable {msq T : ℝ}

/-- `h = Φ²`. -/
def hPhi (y : ℝ) : ℝ := PhiE y * PhiE y

def hPhi' (y : ℝ) : ℝ := 2 * PhiE y * PhiE' y

theorem hasDerivAt_hPhi {y : ℝ} (hy : 0 < y) : HasDerivAt hPhi (hPhi' y) y := by
  have := (hasDerivAt_PhiE hy).mul (hasDerivAt_PhiE hy)
  convert this using 1; unfold hPhi'; ring

/-- `J₀(T) = ∫ Φ(2T√λ)²/λ`. -/
def J0 (T : ℝ) : ℝ := ∫ p in BZ, fc hPhi (2 * T) (lamC p)

def c4 : ℝ := (2 * c0)⁻¹ * M2

theorem c4_nonneg : 0 ≤ c4 := by have := c0_pos; have := M2_nonneg; unfold c4; positivity

/-- The constant of the mass hypothesis. -/
def Mh : ℝ := 16 * (1 + KPhiE + KPhiE) * (c4 + (1 + KPhiE))

theorem Mh_nonneg : 0 ≤ Mh := by
  have := KPhiE_nonneg; have := c4_nonneg; unfold Mh; positivity

theorem one_add_rpow_neg_four {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ (-(4 : ℝ)) = ((1 + y) ^ 4)⁻¹ := by
  rw [Real.rpow_neg (by linarith)]; norm_cast

theorem Phi_hPhi_le {y : ℝ} (hy : 0 < y) :
    |Phi hPhi hPhi' y| ≤ Mh * y ^ 4 * (1 + y) ^ (-(4 : ℝ)) := by
  have hK := KPhiE_nonneg
  have hc := c4_nonneg
  set B := 1 + KPhiE
  have hB := abs_PhiE_bound hy
  have hs := abs_PhiE_le hy.le
  have hd := PhiE_decay y hy
  have hyd : |y * PhiE' y| ≤ KPhiE := by
    have h1 : (1 + y) ^ (-(3 : ℝ)) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have : KPhiE * (1 + y) ^ (-(3 : ℝ)) ≤ KPhiE := mul_le_of_le_one_right hK h1
    linarith [abs_nonneg (1 - PhiE y)]
  have e : Phi hPhi hPhi' y = PhiE y * (PhiE y - y * PhiE' y) := by
    unfold Phi hPhi hPhi'; ring
  rw [e, abs_mul, one_add_rpow_neg_four hy.le]
  have h2 : |PhiE y - y * PhiE' y| ≤ B + KPhiE := (abs_sub _ _).trans (by linarith)
  have h2' : 0 ≤ B + KPhiE := by positivity
  rcases le_total y 1 with hy1 | hy1
  · have h16 : (1 : ℝ) ≤ 16 * ((1 + y) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      calc (1 + y) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
        _ = 16 := by norm_num
    calc |PhiE y| * |PhiE y - y * PhiE' y| ≤ c4 * y ^ 4 * (B + KPhiE) := by
          unfold c4; gcongr
      _ = c4 * (B + KPhiE) * y ^ 4 * 1 := by ring
      _ ≤ c4 * (B + KPhiE) * y ^ 4 * (16 * ((1 + y) ^ 4)⁻¹) := by gcongr
      _ = 16 * (B + KPhiE) * c4 * (y ^ 4 * ((1 + y) ^ 4)⁻¹) := by ring
      _ ≤ 16 * (B + KPhiE) * (c4 + B) * (y ^ 4 * ((1 + y) ^ 4)⁻¹) := by
          gcongr; simp only [B]; linarith
      _ = Mh * y ^ 4 * ((1 + y) ^ 4)⁻¹ := by unfold Mh; simp only [B]; ring
  · have h16 : (1 : ℝ) ≤ 16 * y ^ 4 * ((1 + y) ^ 4)⁻¹ := by
      rw [mul_assoc, ← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ (by positivity), one_mul]
      calc (1 + y) ^ 4 ≤ (2 * y) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
        _ = 16 * y ^ 4 := by ring
    calc |PhiE y| * |PhiE y - y * PhiE' y| ≤ B * (B + KPhiE) := by gcongr
      _ = B * (B + KPhiE) * 1 := by ring
      _ ≤ B * (B + KPhiE) * (16 * y ^ 4 * ((1 + y) ^ 4)⁻¹) := by gcongr
      _ = 16 * (B + KPhiE) * B * (y ^ 4 * ((1 + y) ^ 4)⁻¹) := by ring
      _ ≤ 16 * (B + KPhiE) * (c4 + B) * (y ^ 4 * ((1 + y) ^ 4)⁻¹) := by
          gcongr; linarith
      _ = Mh * y ^ 4 * ((1 + y) ^ 4)⁻¹ := by unfold Mh; simp only [B]; ring

/-- `∫_{BZ} (1 + T√λ)^{-4} ≤ π² Ia(4)/(4T²)`. -/
theorem intBZ_dec4 (hT : 0 < T) :
    ∫ p in BZ, ((1 + T * √(lamC p)) ^ 4)⁻¹ ≤ π ^ 2 * Ia 4 / (4 * T ^ 2) := by
  have hpi := pi_pos
  have ha : 0 < 2 * T / π := by positivity
  have hint := (integrable_decay_scale (α := 4) (by norm_num) ha).integrableOn (s := BZ)
  have hle : ∀ p ∈ BZ, ((1 + T * √(lamC p)) ^ 4)⁻¹ ≤ (1 + 2 * T / π * ‖p‖) ^ (-(4 : ℝ)) := by
    intro p hp
    rw [one_add_rpow_neg_four (by positivity)]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have := sqrt_lamC_ge hp
    have : 2 * T / π * ‖p‖ ≤ T * √(lamC p) := by
      calc 2 * T / π * ‖p‖ = T * (2 / π * ‖p‖) := by ring
        _ ≤ T * √(lamC p) := by gcongr
    linarith
  have hmeas : Continuous fun p : ℂ => ((1 + T * √(lamC p)) ^ 4)⁻¹ := by
    have hl := continuous_lamC
    refine Continuous.inv₀ (by fun_prop) (fun p => by positivity)
  calc ∫ p in BZ, ((1 + T * √(lamC p)) ^ 4)⁻¹ ≤ ∫ p in BZ, (1 + 2 * T / π * ‖p‖) ^ (-(4 : ℝ)) :=
        setIntegral_mono_on (hmeas.continuousOn.integrableOn_compact isCompact_BZ) hint
          measurableSet_BZ hle
    _ ≤ Ia 4 / (2 * T / π) ^ 2 := integral_BZ_decay_le (by norm_num) ha
    _ = π ^ 2 * Ia 4 / (4 * T ^ 2) := by field_simp; ring

/-- `X ≤ a T⁴`, `X ≤ b/λ²` give `X ≤ 16 (a + b) T⁴ (1 + T√λ)^{-4}`. -/
theorem min_decay_le {X a b l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (hT : 0 < T)
    (h1 : X ≤ a * T ^ 4) (h2 : 0 < l → X ≤ b / l ^ 2) :
    X ≤ 16 * (a + b) * T ^ 4 * ((1 + T * √l) ^ 4)⁻¹ := by
  have hs := Real.sqrt_nonneg l
  rcases le_total (T * √l) 1 with hy | hy
  · have h16 : (1 : ℝ) ≤ 16 * ((1 + T * √l) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      calc (1 + T * √l) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
        _ = 16 := by norm_num
    calc X ≤ a * T ^ 4 * 1 := by linarith
      _ ≤ a * T ^ 4 * (16 * ((1 + T * √l) ^ 4)⁻¹) := by gcongr
      _ ≤ 16 * (a + b) * T ^ 4 * ((1 + T * √l) ^ 4)⁻¹ := by
          have : 0 ≤ T ^ 4 * ((1 + T * √l) ^ 4)⁻¹ := by positivity
          nlinarith
  · have hl0 : 0 < l := by
      by_contra h; push Not at h
      have : l = 0 := le_antisymm h hl
      rw [this, Real.sqrt_zero, mul_zero] at hy; linarith
    have hsl : √l ^ 2 = l := Real.sq_sqrt hl
    have key : b / l ^ 2 ≤ 16 * b * T ^ 4 * ((1 + T * √l) ^ 4)⁻¹ := by
      have h4 : (1 + T * √l) ^ 4 ≤ 16 * (T * √l) ^ 4 := by
        calc (1 + T * √l) ^ 4 ≤ (2 * (T * √l)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
          _ = 16 * (T * √l) ^ 4 := by ring
      have e : (T * √l) ^ 4 = T ^ 4 * l ^ 2 := by rw [mul_pow, show √l ^ 4 = (√l ^ 2) ^ 2 by ring, hsl]
      rw [e] at h4
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      calc b * (1 + T * √l) ^ 4 ≤ b * (16 * (T ^ 4 * l ^ 2)) := by gcongr
        _ = 16 * b * T ^ 4 * l ^ 2 := by ring
    calc X ≤ b / l ^ 2 := h2 hl0
      _ ≤ 16 * b * T ^ 4 * ((1 + T * √l) ^ 4)⁻¹ := key
      _ ≤ 16 * (a + b) * T ^ 4 * ((1 + T * √l) ^ 4)⁻¹ := by
          have : 0 ≤ T ^ 4 * ((1 + T * √l) ^ 4)⁻¹ := by positivity
          nlinarith

def Qm : ℝ := 16 * (1 + KPhiE) * c4 + (1 + KPhiE) ^ 2

theorem Qm_nonneg : 0 ≤ Qm := by have := KPhiE_nonneg; have := c4_nonneg; unfold Qm; positivity

def Cms : ℝ := 12 * π ^ 2 * Qm * Ia 4 + π ^ 2 * Ia 4 * Mh

/-- **Removing the mass**: `|J_Φ(T) - J₀(T)| ≤ C_m m² T²`. -/
theorem JPhi_sub_J0 (hm : 0 < msq) (hT : 1 ≤ T) :
    |JPhi msq T - J0 T| ≤ Cms * msq * T ^ 2 := by
  have hpi := pi_pos
  have hT0 : 0 < T := by linarith
  have hK := KPhiE_nonneg
  have hc4 := c4_nonneg
  have hQ := Qm_nonneg
  have hI4 := Ia_nonneg 4
  have hνi := bdd_nu_inv hm
  have hP := bdd_PhiE_nu hm T hT0.le
  have hl := continuous_lamC
  set B := 1 + KPhiE
  -- the functions
  set g : ℝ → ℝ := fc hPhi (2 * T)
  have hJ2 : Bdd fun p => lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4 :=
    ((bdd_lamC.pow 3).mul (hP.pow 2)).mul (hνi.pow 4) |>.congr fun p => by
      rw [inv_pow, ← div_eq_mul_inv]
  have hgν : Bdd fun p => g (lamC p + msq) :=
    (hP.mul hP).mul hνi |>.congr fun p => by
      simp only [g, fc, hPhi]
      rw [show 2 * T * √(lamC p + msq) = 2 * T * √(lamC p + msq) by ring, div_eq_mul_inv]
  have hgl : Bdd fun p => g (lamC p) := by
    refine ⟨?_, c4 ^ 2 * (2 * T) ^ 8 * 8 ^ 3, fun p => ?_⟩
    · have hc : Continuous fun p => PhiE (2 * T * √(lamC p)) :=
        continuous_PhiE_comp (by fun_prop) (fun p => by positivity)
      simp only [g, fc, hPhi]
      exact (hc.measurable.mul hc.measurable).div hl.measurable
    · simp only [g, fc, hPhi]
      have h0 := lamC_nonneg p
      have h8 := lamC_le_eight p
      rcases eq_or_lt_of_le h0 with h | h
      · rw [← h]; simp; positivity
      · have hb := abs_PhiE_le (y := 2 * T * √(lamC p)) (by positivity)
        rw [abs_div, abs_mul, abs_of_pos h]
        have e : (2 * T * √(lamC p)) ^ 4 = (2 * T) ^ 4 * lamC p ^ 2 := by
          rw [mul_pow, show √(lamC p) ^ 4 = (√(lamC p) ^ 2) ^ 2 by ring, Real.sq_sqrt h0]
        rw [e] at hb
        rw [div_le_iff₀ h]
        calc |PhiE (2 * T * √(lamC p))| * |PhiE (2 * T * √(lamC p))| ≤
            (c4 * ((2 * T) ^ 4 * lamC p ^ 2)) * (c4 * ((2 * T) ^ 4 * lamC p ^ 2)) := by
              unfold c4; gcongr
          _ = c4 ^ 2 * (2 * T) ^ 8 * lamC p ^ 3 * lamC p := by ring
          _ ≤ c4 ^ 2 * (2 * T) ^ 8 * 8 ^ 3 * lamC p := by gcongr
  -- (a) `λ³Φ²/ν⁴` versus `Φ²/ν`
  have hpta : ∀ p, |lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4 -
      g (lamC p + msq)| ≤ 3 * msq * (16 * Qm * T ^ 4 * ((1 + T * √(lamC p)) ^ 4)⁻¹) := by
    intro p
    have h0 := lamC_nonneg p
    set ν := lamC p + msq
    have hν : 0 < ν := by simp only [ν]; linarith
    set Φ := PhiE (2 * T * √ν)
    have hb1 : |Φ| ≤ B := abs_PhiE_le' (by positivity)
    have hb2 : |Φ| ≤ c4 * (16 * T ^ 4 * ν ^ 2) := by
      have := abs_PhiE_le (y := 2 * T * √ν) (by positivity)
      have e : (2 * T * √ν) ^ 4 = 16 * T ^ 4 * ν ^ 2 := by
        rw [mul_pow, show √ν ^ 4 = (√ν ^ 2) ^ 2 by ring, Real.sq_sqrt hν.le]; ring
      rw [e] at this; unfold c4; exact this
    have e : lamC p ^ 3 * Φ ^ 2 / ν ^ 4 - g ν = -(Φ ^ 2 * (ν ^ 3 - lamC p ^ 3) / ν ^ 4) := by
      simp only [g, fc, hPhi]; field_simp; ring
    rw [e, abs_neg]
    have hd : 0 ≤ ν ^ 3 - lamC p ^ 3 := by
      have := pow_le_pow_left₀ h0 (show lamC p ≤ ν by simp only [ν]; linarith) 3; linarith
    have hd2 : ν ^ 3 - lamC p ^ 3 ≤ 3 * msq * ν ^ 2 := by
      have hlν : lamC p ≤ ν := by simp only [ν]; linarith
      have : ν ^ 3 - lamC p ^ 3 = msq * (ν ^ 2 + ν * lamC p + lamC p ^ 2) := by simp only [ν]; ring
      rw [this]
      have : ν ^ 2 + ν * lamC p + lamC p ^ 2 ≤ 3 * ν ^ 2 := by nlinarith
      nlinarith
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg Φ), abs_of_nonneg hd, abs_of_pos (by positivity)]
    have hX : Φ ^ 2 / ν ^ 2 ≤ 16 * Qm * T ^ 4 * ((1 + T * √(lamC p)) ^ 4)⁻¹ := by
      have := min_decay_le (X := Φ ^ 2 / ν ^ 2) (a := 16 * B * c4) (b := B ^ 2)
        (l := lamC p) (by positivity) (by positivity) h0 hT0 ?_ ?_
      · calc Φ ^ 2 / ν ^ 2 ≤ 16 * (16 * B * c4 + B ^ 2) * T ^ 4 * ((1 + T * √(lamC p)) ^ 4)⁻¹ := this
          _ = _ := by unfold Qm; simp only [B]
      · rw [div_le_iff₀ (by positivity)]
        calc Φ ^ 2 = |Φ| * |Φ| := by rw [abs_mul_abs_self, sq]
          _ ≤ B * (c4 * (16 * T ^ 4 * ν ^ 2)) := by gcongr
          _ = 16 * B * c4 * T ^ 4 * ν ^ 2 := by ring
      · intro hl0
        have hle : lamC p ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ h0 (by simp only [ν]; linarith) 2
        have hΦ2 : Φ ^ 2 ≤ B ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
        calc Φ ^ 2 / ν ^ 2 ≤ B ^ 2 / ν ^ 2 := by gcongr
          _ ≤ B ^ 2 / lamC p ^ 2 := by gcongr
    calc Φ ^ 2 * (ν ^ 3 - lamC p ^ 3) / ν ^ 4 ≤ Φ ^ 2 * (3 * msq * ν ^ 2) / ν ^ 4 := by gcongr
      _ = 3 * msq * (Φ ^ 2 / ν ^ 2) := by field_simp
      _ ≤ 3 * msq * (16 * Qm * T ^ 4 * ((1 + T * √(lamC p)) ^ 4)⁻¹) := by gcongr
  have hDc : Continuous fun p : ℂ => 3 * msq * (16 * Qm * T ^ 4 * ((1 + T * √(lamC p)) ^ 4)⁻¹) :=
    continuous_const.mul (continuous_const.mul (Continuous.inv₀ (by fun_prop)
      (fun p => by positivity)))
  have ha : |(∫ p in BZ, lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4) -
      ∫ p in BZ, g (lamC p + msq)| ≤ 12 * π ^ 2 * Qm * Ia 4 * msq * T ^ 2 := by
    rw [← integral_sub hJ2.integrableOn hgν.integrableOn, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hDc.continuousOn.integrableOn_compact isCompact_BZ)
      (ae_restrict_of_forall_mem measurableSet_BZ fun p _ => by
        rw [Real.norm_eq_abs]; exact hpta p)).trans ?_
    rw [integral_const_mul, integral_const_mul]
    have := intBZ_dec4 hT0
    calc 3 * msq * (16 * Qm * T ^ 4 * ∫ p in BZ, ((1 + T * √(lamC p)) ^ 4)⁻¹)
        ≤ 3 * msq * (16 * Qm * T ^ 4 * (π ^ 2 * Ia 4 / (4 * T ^ 2))) := by gcongr
      _ = 12 * π ^ 2 * Qm * Ia 4 * msq * T ^ 2 := by field_simp; ring
  -- (b) `lattice_mass`
  have hb : |∫ p in BZ, (g (lamC p + msq) - g (lamC p))| ≤
      π ^ 2 / 4 * Ia 4 * Mh * msq * (2 * T) ^ 2 :=
    lattice_mass (c := 2 * T) (g := g)
      (g' := fun t => -Phi hPhi hPhi' (2 * T * √t) / t ^ 2)
      (fun t ht => hasDerivAt_fc (fun y hy => hasDerivAt_hPhi hy) (by positivity) ht)
      (fun t ht => fc_deriv_bound_mass (fun y hy => Phi_hPhi_le hy) (by positivity) ht)
      (by norm_num) (by positivity) hm.le
  rw [integral_sub hgν.integrableOn hgl.integrableOn] at hb
  unfold JPhi J0
  calc |(∫ p in BZ, lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4) -
        ∫ p in BZ, fc hPhi (2 * T) (lamC p)|
      ≤ |(∫ p in BZ, lamC p ^ 3 * PhiE (2 * T * √(lamC p + msq)) ^ 2 / (lamC p + msq) ^ 4) -
          ∫ p in BZ, g (lamC p + msq)| +
        |(∫ p in BZ, g (lamC p + msq)) - ∫ p in BZ, g (lamC p)| := abs_sub_le _ _ _
    _ ≤ 12 * π ^ 2 * Qm * Ia 4 * msq * T ^ 2 + π ^ 2 / 4 * Ia 4 * Mh * msq * (2 * T) ^ 2 :=
        add_le_add ha hb
    _ = Cms * msq * T ^ 2 := by unfold Cms; ring

end

end Step2.D2