import Step2.D2.D2Bv8

/-!
# `|𝔅(w_T) - log T/(2π)| ≤ C_{B,0}` (`prop:d2`, line 3, fallback form)

For the concrete FRD family, `0 < m²`, `1 ≤ T`, `m² T² ≤ 1` and a torus large enough
(`2(⌊T⌋ + 4) < L^N`):

  `‖𝔅(w_T) - log T/(2π)‖ ≤ CB0`

with an absolute constant `CB0` (`frakBT_bound`).
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

variable {msq T : ℝ}

/-! ### Constants -/

/-- `C_{∂,b}`: `CBd` at `m² = 1`. -/
def bB : ℝ := CBd 1

/-- `C_{∂,a}`. -/
def aB : ℝ := CD / (24 * π)

theorem aB_nonneg : 0 ≤ aB := by have := CD_nonneg; have := pi_pos; unfold aB; positivity

theorem CBd_eq (hm : 0 ≤ msq) : CBd msq = CD * (2 * π ^ 2) ^ 3 / (6 * π) * (2 * 2 + msq) ^ 2 := by
  have := pi_pos
  have : (0 : ℝ) < 2 * 2 + msq := by linarith
  unfold CBd; field_simp

theorem CBd_mono (hm : 0 ≤ msq) (hm1 : msq ≤ 1) : CBd msq ≤ bB := by
  have := CD_nonneg; have := pi_pos
  unfold bB; rw [CBd_eq hm, CBd_eq zero_le_one]; gcongr

theorem bB_nonneg : 0 ≤ bB := by
  have := CD_nonneg; have := pi_pos
  unfold bB; rw [CBd_eq zero_le_one]; positivity

/-- The absolute constant `C_{B,0}`. -/
def CB0 : ℝ := (7 * π ^ 2 + CE aB bB * Ia 5 + CM * Ia 4 + 2 * π * Real.log π) / (2 * π) ^ 2

/-! ### Pointwise inputs -/

theorem abs_dchat_le' (hm : 0 < msq) (hT : 0 < T) (p : ℂ) : |dchat msq T p| ≤ aB * T ^ 3 := by
  refine (abs_dchat_le hm hT p).trans ?_
  have := CD_nonneg; have := pi_pos
  unfold aB
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

theorem abs_dchat_sub_le' (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 0 < T) (p : ℂ) :
    |dchat msq T p - Amain msq p| ≤ bB / (T ^ 3 * (lamC p + msq) ^ 3) := by
  refine (abs_dchat_sub_le hm hT p).trans ?_
  have := lamC_nonneg p
  have : 0 < lamC p + msq := by linarith
  gcongr
  exact CBd_mono hm.le hm1

theorem abs_Amain_le (hm : 0 < msq) (p : ℂ) : |Amain msq p| ≤ 2 * ‖p‖ / (lamC p + msq) ^ 2 := by
  have := lamC_nonneg p
  have hν : 0 < lamC p + msq := by linarith
  unfold Amain
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (lamC p + msq) ^ 2)]
  rw [show |(-2 : ℝ)| = 2 by norm_num]
  gcongr
  exact (Real.abs_sin_le_abs).trans (Complex.abs_re_le_norm p)

theorem chat_le (hm : 0 < msq) (hT : 0 ≤ T) (p : ℂ) : chat Pc msq (Ioc 0 T) p ≤ msq⁻¹ := by
  obtain ⟨h0, h1⟩ := chat_bounds hm hT p
  have := lamC_nonneg p
  have h2 : chat Pc msq (Ioc 0 T) p * msq ≤ 1 := by
    calc chat Pc msq (Ioc 0 T) p * msq ≤ chat Pc msq (Ioc 0 T) p * (lamC p + msq) := by
          gcongr; linarith
      _ ≤ 1 := h1
  calc chat Pc msq (Ioc 0 T) p = chat Pc msq (Ioc 0 T) p * msq * msq⁻¹ := by field_simp
    _ ≤ 1 * msq⁻¹ := by gcongr
    _ = msq⁻¹ := one_mul _

theorem bdd_chat (hm : 0 < msq) (hT : 0 ≤ T) : Bdd (chat Pc msq (Ioc 0 T)) :=
  ⟨measurable_chat' msq T, msq⁻¹, fun p => by
    rw [abs_of_nonneg (chat_bounds hm hT p).1]; exact chat_le hm hT p⟩

theorem bdd_dchat (hm : 0 < msq) (hT : 0 < T) : Bdd (dchat msq T) :=
  ⟨measurable_dchat msq T, aB * T ^ 3, abs_dchat_le' hm hT⟩

theorem bdd_Amain (hm : 0 < msq) : Bdd (Amain msq) := by
  have h := ((Bdd.const (-2)).mul bdd_sin_re).mul ((bdd_nu_inv hm).pow 2)
  exact h.congr fun p => by unfold Amain; field_simp

/-! ### The `ĉ²` term -/

/-- `0 ≤ ∫ (2λ - 4 sin² p₀) ĉ_T² ≤ 2π²`. -/
theorem I1_bounds (hm : 0 < msq) (hT : 0 ≤ T) :
    0 ≤ ∫ p in BZ, (2 * lamC p - 4 * Real.sin p.re ^ 2) * chat Pc msq (Ioc 0 T) p ^ 2 ∧
      ∫ p in BZ, (2 * lamC p - 4 * Real.sin p.re ^ 2) * chat Pc msq (Ioc 0 T) p ^ 2 ≤ 2 * π ^ 2 := by
  set c := chat Pc msq (Ioc 0 T)
  have hc := bdd_chat hm hT
  have hpi := pi_pos
  have hsym := integral_sin_sq_sym (g := fun p => 4 * c p ^ 2)
    (fun p => by simp [c, chat_swapC])
    (((Bdd.const 4).mul (hc.pow 2)).mul (bdd_sin_re.pow 2)).integrableOn
    (((Bdd.const 4).mul (hc.pow 2)).mul (bdd_sin_im.pow 2)).integrableOn
  set R : ℂ → ℝ := fun p => (2 - 2 * Real.cos p.re) ^ 2 + (2 - 2 * Real.cos p.im) ^ 2
  have hR : Bdd R := ((((Bdd.const 2).sub ((Bdd.const 2).mul bdd_cos_re)).pow 2).add
    (((Bdd.const 2).sub ((Bdd.const 2).mul bdd_cos_im)).pow 2))
  have e : ∫ p in BZ, (2 * lamC p - 4 * Real.sin p.re ^ 2) * c p ^ 2 =
      ∫ p in BZ, R p / 2 * c p ^ 2 := by
    have e1 : (fun p => (2 * lamC p - 4 * Real.sin p.re ^ 2) * c p ^ 2) =
        fun p => 2 * lamC p * c p ^ 2 - 4 * c p ^ 2 * Real.sin p.re ^ 2 := by funext p; ring
    have hX : Bdd fun p => 4 * c p ^ 2 * ((Real.sin p.re ^ 2 + Real.sin p.im ^ 2) / 2) :=
      (((Bdd.const 4).mul (hc.pow 2)).mul ((bdd_sin_re.pow 2).add (bdd_sin_im.pow 2))).mul
        (Bdd.const (1 / 2)) |>.congr fun p => by ring
    have hY : Bdd fun p => 2 * lamC p * c p ^ 2 :=
      (((Bdd.const 2).mul bdd_lamC).mul (hc.pow 2))
    have hZ : Bdd fun p => 4 * c p ^ 2 * Real.sin p.re ^ 2 :=
      (((Bdd.const 4).mul (hc.pow 2)).mul (bdd_sin_re.pow 2))
    rw [e1, integral_sub hY.integrableOn hZ.integrableOn, hsym,
      ← integral_sub hY.integrableOn hX.integrableOn]
    refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
    simp only [R]
    rw [sin_sq_add_sin_sq]; ring
  rw [e]
  have hpt : ∀ p, 0 ≤ R p / 2 * c p ^ 2 ∧ R p / 2 * c p ^ 2 ≤ 1 / 2 := by
    intro p
    obtain ⟨hR0, hR1⟩ := lamC_parts_le p
    obtain ⟨hc0, hc1⟩ := chat_bounds hm hT p
    have hl := lamC_nonneg p
    have hlc : lamC p * c p ≤ 1 := by
      calc lamC p * c p ≤ (lamC p + msq) * c p := by gcongr; linarith
        _ ≤ 1 := by rw [mul_comm]; exact hc1
    have hlc0 : 0 ≤ lamC p * c p := by positivity
    constructor
    · exact mul_nonneg (div_nonneg hR0 (by norm_num)) (sq_nonneg _)
    · calc R p / 2 * c p ^ 2 ≤ lamC p ^ 2 / 2 * c p ^ 2 := by gcongr
        _ = (lamC p * c p) ^ 2 / 2 := by ring
        _ ≤ 1 ^ 2 / 2 := by gcongr
        _ = 1 / 2 := by norm_num
  have hint : IntegrableOn (fun p => R p / 2 * c p ^ 2) BZ :=
    ((hR.mul (Bdd.const (1 / 2))).mul (hc.pow 2) |>.congr fun p => by ring).integrableOn
  constructor
  · exact setIntegral_nonneg measurableSet_BZ fun p _ => (hpt p).1
  · calc ∫ p in BZ, R p / 2 * c p ^ 2 ≤ ∫ p in BZ, (1 / 2 : ℝ) :=
          setIntegral_mono_on hint (Bdd.const (1 / 2 : ℝ)).integrableOn
            measurableSet_BZ fun p _ => (hpt p).2
      _ = 2 * π ^ 2 := by rw [setIntegral_const, volume_real_BZ]; simp; ring

/-! ### The `(∂₀ĉ)²` term -/

/-- The main part `M₂ = χ (λ²/2) A²`. -/
def M2b (msq T : ℝ) (p : ℂ) : ℝ := chiT T (lamC p + msq) * (lamC p ^ 2 / 2 * Amain msq p ^ 2)

theorem bdd_M2b (hm : 0 < msq) : Bdd (M2b msq T) :=
  ((bdd_chiT T msq).mul (((bdd_lamC.pow 2).mul (Bdd.const (1 / 2))).mul ((bdd_Amain hm).pow 2))
    |>.congr fun p => by unfold M2b; ring)

theorem I2_sub_M2b (hm : 0 < msq) (hm1 : msq ≤ 1) (hT : 0 < T) :
    |(∫ p in BZ, lamC p ^ 2 / 2 * dchat msq T p ^ 2) - ∫ p in BZ, M2b msq T p| ≤ CE aB bB * Ia 5 := by
  have hf2 : Bdd fun p => lamC p ^ 2 / 2 * dchat msq T p ^ 2 :=
    ((bdd_lamC.pow 2).mul (Bdd.const (1 / 2))).mul ((bdd_dchat hm hT).pow 2) |>.congr
      fun p => by ring
  rw [← integral_sub hf2.integrableOn (bdd_M2b hm).integrableOn]
  have hCE : 0 ≤ CE aB bB := by
    have := aB_nonneg; have := bB_nonneg; have := pi_pos; unfold CE; positivity
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrableOn_decay_T (α := 5) (by norm_num) hT (CE aB bB))
    (ae_restrict_of_forall_mem measurableSet_BZ fun p hp => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    have hl := lamC_nonneg p
    exact ptE2 hT (by linarith) (by linarith) hl (norm_nonneg p) (lamC_ge hp) aB_nonneg bB_nonneg
      (abs_dchat_le' hm hT p) (abs_dchat_sub_le' hm hm1 hT p) (abs_Amain_le hm p)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_BZ_decay_T (by norm_num) hT) hCE

/-- The symmetrized main part: `∫ M₂ = ∫ χ λ³/ν⁴ - ∫ W` with `0 ≤ W ≤ 1/4`. -/
theorem integral_M2b (hm : 0 < msq) :
    ∃ w, 0 ≤ w ∧ w ≤ π ^ 2 ∧ ∫ p in BZ, M2b msq T p =
      (∫ p in BZ, chiT T (lamC p + msq) * lamC p ^ 3 / (lamC p + msq) ^ 4) - w := by
  have hpi := pi_pos
  set G : ℂ → ℝ := fun p => chiT T (lamC p + msq) * 2 * lamC p ^ 2 / (lamC p + msq) ^ 4
  have hG : Bdd G := (((bdd_chiT T msq).mul (Bdd.const 2)).mul (bdd_lamC.pow 2)).mul
    ((bdd_nu_inv hm).pow 4) |>.congr fun p => by simp only [G]; field_simp
  set R : ℂ → ℝ := fun p => (2 - 2 * Real.cos p.re) ^ 2 + (2 - 2 * Real.cos p.im) ^ 2
  have hR : Bdd R := ((((Bdd.const 2).sub ((Bdd.const 2).mul bdd_cos_re)).pow 2).add
    (((Bdd.const 2).sub ((Bdd.const 2).mul bdd_cos_im)).pow 2))
  set W : ℂ → ℝ := fun p => chiT T (lamC p + msq) * lamC p ^ 2 * R p / (4 * (lamC p + msq) ^ 4)
  have hW : Bdd W := ((((bdd_chiT T msq).mul (bdd_lamC.pow 2)).mul hR).mul
    (((bdd_nu_inv hm).pow 4).mul (Bdd.const (1 / 4)))) |>.congr fun p => by simp only [W]; field_simp
  have hfM : Bdd fun p => chiT T (lamC p + msq) * lamC p ^ 3 / (lamC p + msq) ^ 4 :=
    (((bdd_chiT T msq).mul (bdd_lamC.pow 3)).mul ((bdd_nu_inv hm).pow 4)) |>.congr
      fun p => by field_simp
  have hsym := integral_sin_sq_sym (g := G) (fun p => by simp [G, lamC_swapC])
    (hG.mul (bdd_sin_re.pow 2)).integrableOn (hG.mul (bdd_sin_im.pow 2)).integrableOn
  have e1 : ∫ p in BZ, M2b msq T p = ∫ p in BZ, G p * Real.sin p.re ^ 2 := by
    refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
    have := lamC_nonneg p
    have : lamC p + msq ≠ 0 := by linarith
    simp only [M2b, G, Amain]; field_simp
  have e2 : ∫ p in BZ, G p * ((Real.sin p.re ^ 2 + Real.sin p.im ^ 2) / 2) =
      ∫ p in BZ, ((chiT T (lamC p + msq) * lamC p ^ 3 / (lamC p + msq) ^ 4) - W p) := by
    refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
    have := lamC_nonneg p
    have : lamC p + msq ≠ 0 := by linarith
    simp only [G, W, R]; rw [sin_sq_add_sin_sq]; field_simp
  refine ⟨∫ p in BZ, W p, setIntegral_nonneg measurableSet_BZ fun p _ => ?_, ?_, ?_⟩
  · have := lamC_nonneg p
    have := (lamC_parts_le p).1
    have : 0 ≤ chiT T (lamC p + msq) := by unfold chiT; split_ifs <;> norm_num
    simp only [W, R]; positivity
  · have hpt : ∀ p, W p ≤ 1 / 4 := by
      intro p
      have hl := lamC_nonneg p
      have hν : 0 < lamC p + msq := by linarith
      have hR1 := (lamC_parts_le p).2
      have hR0 := (lamC_parts_le p).1
      have hχ : 0 ≤ chiT T (lamC p + msq) ∧ chiT T (lamC p + msq) ≤ 1 := by
        unfold chiT; split_ifs <;> norm_num
      simp only [W, R]
      rw [div_le_iff₀ (by positivity)]
      have h4 : lamC p ^ 4 ≤ (lamC p + msq) ^ 4 := pow_le_pow_left₀ hl (by linarith) 4
      calc chiT T (lamC p + msq) * lamC p ^ 2 * ((2 - 2 * Real.cos p.re) ^ 2 +
            (2 - 2 * Real.cos p.im) ^ 2) ≤ 1 * lamC p ^ 2 * lamC p ^ 2 := by
            gcongr; exact hχ.2
        _ ≤ 1 / 4 * (4 * (lamC p + msq) ^ 4) := by nlinarith
    calc ∫ p in BZ, W p ≤ ∫ p in BZ, (1 / 4 : ℝ) :=
          setIntegral_mono_on hW.integrableOn (Bdd.const (1 / 4 : ℝ)).integrableOn
            measurableSet_BZ fun p _ => hpt p
      _ = π ^ 2 := by rw [setIntegral_const, volume_real_BZ]; simp; ring
  · rw [e1, hsym, e2, integral_sub hfM.integrableOn hW.integrableOn]

/-- `|∫ χ λ³/ν⁴ - 2π(log π + log T)| ≤ 4π² + C_M Ia(4)`. -/
theorem fM_bound (hm : 0 < msq) (hT : 1 ≤ T) (hmT : msq * T ^ 2 ≤ 1) :
    |(∫ p in BZ, chiT T (lamC p + msq) * lamC p ^ 3 / (lamC p + msq) ^ 4) -
      2 * π * (Real.log π + Real.log T)| ≤ 4 * π ^ 2 + CM * Ia 4 := by
  have hT0 : 0 < T := by linarith
  have hfM : Bdd fun p => chiT T (lamC p + msq) * lamC p ^ 3 / (lamC p + msq) ^ 4 :=
    (((bdd_chiT T msq).mul (bdd_lamC.pow 3)).mul ((bdd_nu_inv hm).pow 4)) |>.congr
      fun p => by field_simp
  have hmT' : msq ≤ (T ^ 2)⁻¹ := by
    rw [le_inv_comm₀ hm (by positivity), inv_eq_one_div, le_div_iff₀ hm]; linarith
  rw [← integral_gR hT, ← integral_sub hfM.integrableOn (bdd_gR hT0).integrableOn,
    ← Real.norm_eq_abs]
  have hint : IntegrableOn (fun p : ℂ => 1 + CM * (T ^ 2 * (1 + T * ‖p‖) ^ (-(4 : ℝ)))) BZ :=
    (Bdd.const (1 : ℝ)).integrableOn.add
      (integrableOn_decay_T (α := 4) (by norm_num) hT0 CM)
  refine (norm_integral_le_of_norm_le hint
    (ae_restrict_of_forall_mem measurableSet_BZ fun p hp => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    exact ptM hT hm hmT' (norm_nonneg p) (lamC_ge hp) (lamC_le p) (normSq_sub_lamC_le p)
  · rw [integral_add (Bdd.const (1 : ℝ)).integrableOn
      (integrableOn_decay_T (α := 4) (by norm_num) hT0 CM), setIntegral_const, volume_real_BZ,
      integral_const_mul]
    have := integral_BZ_decay_T (α := 4) (by norm_num) hT0
    have := CM_nonneg
    have : CM * ∫ p in BZ, T ^ 2 * (1 + T * ‖p‖) ^ (-(4 : ℝ)) ≤ CM * Ia 4 := by gcongr
    simp only [smul_eq_mul, mul_one]
    nlinarith

/-! ### Assembly -/

/-- **Line 3 of `prop:d2` at a single scale (fallback form).**
`‖𝔅(w_T) - log T/(2π)‖ ≤ CB0` with an absolute constant `CB0`. -/
theorem frakBT_bound {L N : ℕ} [NeZero L] (hm : 0 < msq) (hT : 1 ≤ T) (hmT : msq * T ^ 2 ≤ 1)
    (hn : 2 * (⌊T⌋₊ + 4) < L ^ N) :
    ‖frakBT L N msq T - ((Real.log T / (2 * π) : ℝ) : ℂ)‖ ≤ CB0 := by
  have hpi := pi_pos
  have hT0 : 0 < T := by linarith
  have hm1 : msq ≤ 1 := by have := one_le_pow₀ (n := 2) hT; nlinarith
  rw [frakBT_eq hm hT0 hn, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨h1a, h1b⟩ := I1_bounds hm hT0.le
  have h2 := I2_sub_M2b hm hm1 hT0
  obtain ⟨w, hw0, hw1, hM⟩ := integral_M2b (T := T) hm
  have h3 := fM_bound hm hT hmT
  have hlogpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [pi_gt_three])
  set I1 := ∫ p in BZ, (2 * lamC p - 4 * Real.sin p.re ^ 2) * chat Pc msq (Ioc 0 T) p ^ 2
  set I2 := ∫ p in BZ, lamC p ^ 2 / 2 * dchat msq T p ^ 2
  set FM := ∫ p in BZ, chiT T (lamC p + msq) * lamC p ^ 3 / (lamC p + msq) ^ 4
  have hk : |I1 + I2 - 2 * π * Real.log T| ≤
      7 * π ^ 2 + CE aB bB * Ia 5 + CM * Ia 4 + 2 * π * Real.log π := by
    rw [hM] at h2
    rw [abs_le] at h2 h3 ⊢
    constructor <;> nlinarith
  have e : ((2 * π) ^ 2)⁻¹ * (I1 + I2) - Real.log T / (2 * π) =
      (I1 + I2 - 2 * π * Real.log T) / (2 * π) ^ 2 := by
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ 2)]
  unfold CB0
  gcongr

/-- **Line 3 of `prop:d2` (fallback form):** for `T' = L T`,
`‖𝔅(w_{T'}) - 𝔅(w_T) - log L/(2π)‖ ≤ 2 CB0`. -/
theorem frakBT_diff_bound {L N : ℕ} [NeZero L] (hL : 1 ≤ L) (hm : 0 < msq) (hT : 1 ≤ T)
    (hmT : msq * (L * T) ^ 2 ≤ 1) (hn : 2 * (⌊(L : ℝ) * T⌋₊ + 4) < L ^ N) :
    ‖frakBT L N msq (L * T) - frakBT L N msq T - ((Real.log L / (2 * π) : ℝ) : ℂ)‖ ≤ 2 * CB0 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hT0 : 0 < T := by linarith
  have hLT : 1 ≤ (L : ℝ) * T := by nlinarith
  have hfl : ⌊T⌋₊ ≤ ⌊(L : ℝ) * T⌋₊ := Nat.floor_le_floor (by nlinarith)
  have hmT' : msq * T ^ 2 ≤ 1 := by
    have : T ^ 2 ≤ (L * T) ^ 2 := pow_le_pow_left₀ hT0.le (by nlinarith) 2
    nlinarith
  have h1 := frakBT_bound (L := L) (N := N) hm hLT hmT hn
  have h2 := frakBT_bound (L := L) (N := N) hm hT hmT' (by omega)
  have e : frakBT L N msq (L * T) - frakBT L N msq T - ((Real.log L / (2 * π) : ℝ) : ℂ) =
      (frakBT L N msq (L * T) - ((Real.log (L * T) / (2 * π) : ℝ) : ℂ)) -
        (frakBT L N msq T - ((Real.log T / (2 * π) : ℝ) : ℂ)) := by
    rw [Real.log_mul (by positivity) hT0.ne']; push_cast; ring
  rw [e]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ CB0 + CB0 := add_le_add h1 h2
    _ = 2 * CB0 := by ring

end

end Step2.D2
