import Mathlib

/-!
# Fourier-analytic input for the construction of `P_t`

We fix a smooth even bump `g₀ ≥ 0` supported in `[-1/2, 1/2]`, the (complex) Schwartz function
`g`, and its autoconvolution `F = g ⋆ g`, a real continuous function supported in `[-1, 1]`
(`FRD.PtF.f`). Its Fourier transform `Ψ = 𝓕 F = (𝓕 g)^2` is real, nonnegative, even and
rapidly decreasing (`FRD.PtF.ψ`). Poisson summation then gives, for `t > 0`,
`∑_k t ψ(t (x + k)) = ∑_{|n| ≤ ⌊t⌋} f(-n/t) cos(2π n x)`.
-/

namespace FRD.PtF

open MeasureTheory Set Filter Topology Real
open scoped FourierTransform SchwartzMap ComplexConjugate ContDiff

/-- The bump function `g₀(x) = exp(-1/(1/4 - x²))` for `|x| < 1/2`, and `0` otherwise. -/
noncomputable def g0 (x : ℝ) : ℝ := expNegInvGlue (1 / 4 - x ^ 2)

lemma g0_nonneg (x : ℝ) : 0 ≤ g0 x := expNegInvGlue.nonneg _

lemma g0_neg (x : ℝ) : g0 (-x) = g0 x := by simp [g0]

lemma g0_eq_zero {x : ℝ} (h : 1 / 2 ≤ |x|) : g0 x = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  have : (1 / 2) ^ 2 ≤ |x| ^ 2 := by gcongr
  rw [sq_abs] at this
  linarith

lemma g0_pos {x : ℝ} (h : |x| < 1 / 2) : 0 < g0 x := by
  apply expNegInvGlue.pos_of_pos
  have : |x| ^ 2 < (1 / 2) ^ 2 := by gcongr
  rw [sq_abs] at this
  linarith

lemma g0_contDiff : ContDiff ℝ ∞ g0 :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

lemma g0_continuous : Continuous g0 := g0_contDiff.continuous

lemma g0_hasCompactSupport : HasCompactSupport g0 := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (1 / 2))
  intro x hx
  apply g0_eq_zero
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  exact hx.le

lemma g0_integrable : Integrable g0 := g0_continuous.integrable_of_hasCompactSupport
  g0_hasCompactSupport

lemma integral_pos_of_pos_on {φ : ℝ → ℝ} (_hc : Continuous φ) (hi : Integrable φ)
    (h0 : ∀ x, 0 ≤ φ x) {a b : ℝ} (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < φ x) :
    0 < ∫ x, φ x := by
  rw [integral_pos_iff_support_of_nonneg h0 hi]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo a b) fun x hx => (hpos x hx).ne')
  simp [hab]

lemma integral_g0_pos : 0 < ∫ x, g0 x := by
  refine integral_pos_of_pos_on g0_continuous g0_integrable g0_nonneg
    (a := -1 / 2) (b := 1 / 2) (by norm_num) ?_
  intro x hx
  apply g0_pos
  rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]

/-- The complex-valued bump. -/
noncomputable def gC (x : ℝ) : ℂ := (g0 x : ℂ)

lemma gC_contDiff : ContDiff ℝ ∞ gC := Complex.ofRealCLM.contDiff.comp g0_contDiff

lemma gC_hasCompactSupport : HasCompactSupport gC :=
  g0_hasCompactSupport.comp_left Complex.ofReal_zero

/-- The bump as a Schwartz function. -/
noncomputable def gS : 𝓢(ℝ, ℂ) := gC_hasCompactSupport.toSchwartzMap gC_contDiff

/-- The autoconvolution `F = g ⋆ g`. -/
noncomputable def FS : 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) gS gS

/-- `Ψ = 𝓕 F`. -/
noncomputable def ΨS : 𝓢(ℝ, ℂ) := 𝓕 FS

lemma ΨS_apply (ξ : ℝ) : ΨS ξ = 𝓕 gC ξ * 𝓕 gC ξ := by
  rw [ΨS, FS, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', SchwartzMap.fourier_coe]
  rfl

lemma fourier_gC_neg (ξ : ℝ) : 𝓕 gC (-ξ) = 𝓕 gC ξ := by
  rw [← fourierInv_eq_fourier_neg, fourierInv_eq_fourier_comp_neg]
  have : (fun x => gC (-x)) = gC := by funext x; simp [gC, g0_neg]
  rw [this]

lemma fourier_gC_conj (ξ : ℝ) : conj (𝓕 gC ξ) = 𝓕 gC (-ξ) := by
  rw [fourier_real_eq, fourier_real_eq, ← integral_conj]
  congr 1
  funext v
  simp only [Circle.smul_def, smul_eq_mul, map_mul, gC, Complex.conj_ofReal]
  congr 1
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
  congr 2
  ring

lemma fourier_gC_im (ξ : ℝ) : (𝓕 gC ξ).im = 0 := by
  rw [← Complex.conj_eq_iff_im, fourier_gC_conj, fourier_gC_neg]

lemma fourier_gC_eq (ξ : ℝ) : 𝓕 gC ξ = ((𝓕 gC ξ).re : ℂ) :=
  (Complex.ext rfl (by simp [fourier_gC_im]))

/-- `ψ = Ψ`, as a real function. -/
noncomputable def ψ (ξ : ℝ) : ℝ := (ΨS ξ).re

lemma ψ_eq (ξ : ℝ) : ψ ξ = (𝓕 gC ξ).re ^ 2 := by
  rw [ψ, ΨS_apply, fourier_gC_eq]
  norm_cast
  ring

lemma ΨS_eq (ξ : ℝ) : ΨS ξ = (ψ ξ : ℂ) := by
  rw [ψ_eq, ΨS_apply, fourier_gC_eq]
  norm_cast
  ring

lemma ψ_nonneg (ξ : ℝ) : 0 ≤ ψ ξ := by rw [ψ_eq]; positivity

lemma ψ_neg (ξ : ℝ) : ψ (-ξ) = ψ ξ := by rw [ψ_eq, ψ_eq, fourier_gC_neg]

lemma ψ_abs (ξ : ℝ) : ψ |ξ| = ψ ξ := by
  rcases abs_choice ξ with h | h <;> rw [h]
  exact ψ_neg ξ

lemma ψ_continuous : Continuous ψ :=
  Complex.continuous_re.comp ΨS.continuous

lemma ψ_zero_pos : 0 < ψ 0 := by
  rw [ψ_eq]
  have : 𝓕 gC 0 = ((∫ x, g0 x : ℝ) : ℂ) := by
    rw [fourier_real_eq, ← integral_complex_ofReal]
    congr 1; funext v; simp [gC]
  rw [this, Complex.ofReal_re]
  have := integral_g0_pos
  positivity

/-- Rapid decay of `ψ`. -/
lemma ψ_decay (M : ℕ) : ∃ C, ∀ ξ, (1 + |ξ|) ^ M * ψ ξ ≤ C := by
  refine ⟨2 ^ M * (Finset.Iic (M, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ΨS,
    fun ξ => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, 0)) (k := M) (n := 0)
    le_rfl le_rfl ΨS ξ
  rw [norm_iteratedFDeriv_zero, ΨS_eq, Complex.norm_real] at this
  simp only [Real.norm_eq_abs] at this
  rwa [abs_of_nonneg (ψ_nonneg ξ)] at this

lemma ψ_decay' (M : ℕ) : ∃ C, 0 ≤ C ∧ ∀ ξ, ψ ξ ≤ C / (1 + |ξ|) ^ M := by
  obtain ⟨C, hC⟩ := ψ_decay M
  refine ⟨max C 0, le_max_right _ _, fun ξ => ?_⟩
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (hC ξ).trans (le_max_left _ _)

/-- The real function `f = F`. -/
noncomputable def f (y : ℝ) : ℝ := (FS y).re

lemma FS_apply (y : ℝ) : FS y = ∫ t, gC t * gC (y - t) := by
  rw [FS, SchwartzMap.convolution_apply, convolution_def]
  rfl

lemma f_eq (y : ℝ) : f y = ∫ t, g0 t * g0 (y - t) := by
  rw [f, FS_apply]
  have : (∫ t, gC t * gC (y - t)) = ((∫ t, g0 t * g0 (y - t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; congr 1; funext t; simp [gC]
  rw [this, Complex.ofReal_re]

lemma FS_eq (y : ℝ) : FS y = (f y : ℂ) := by
  rw [f_eq, FS_apply, ← integral_complex_ofReal]; congr 1; funext t; simp [gC]

lemma f_continuous : Continuous f := Complex.continuous_re.comp FS.continuous

lemma f_eq_zero {y : ℝ} (hy : 1 ≤ |y|) : f y = 0 := by
  rw [f_eq]
  have : ∀ t, g0 t * g0 (y - t) = 0 := by
    intro t
    rcases le_or_gt (1 / 2) |t| with h | h
    · rw [g0_eq_zero h, zero_mul]
    · have : 1 / 2 ≤ |y - t| := by
        have := abs_sub_abs_le_abs_sub y t
        linarith
      rw [g0_eq_zero this, mul_zero]
  simp [this]

lemma f_zero_pos : 0 < f 0 := by
  rw [f_eq]
  have hc : Continuous fun t => g0 t * g0 (0 - t) :=
    g0_continuous.mul (g0_continuous.comp (continuous_const.sub continuous_id))
  refine integral_pos_of_pos_on hc ?_ (fun t => mul_nonneg (g0_nonneg _) (g0_nonneg _))
    (a := -1 / 2) (b := 1 / 2) (by norm_num) ?_
  · exact hc.integrable_of_hasCompactSupport (g0_hasCompactSupport.mul_right)
  · intro t ht
    have h1 : |t| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have h2 : |0 - t| < 1 / 2 := by rwa [zero_sub, abs_neg]
    exact mul_pos (g0_pos h1) (g0_pos h2)

lemma fourier_ΨS (η : ℝ) : 𝓕 (ΨS : ℝ → ℂ) η = FS (-η) := by
  have h1 : 𝓕 (ΨS : ℝ → ℂ) η = 𝓕⁻ (ΨS : ℝ → ℂ) (-η) := by
    rw [fourierInv_eq_fourier_neg, neg_neg]
  rw [h1, ← SchwartzMap.fourierInv_coe, ΨS, FourierPair.fourierInv_fourier_eq]

/-- The scaled function `h_t(y) = t Ψ(t y)`. -/
noncomputable def hS (t : ℝ) (y : ℝ) : ℂ := (t : ℂ) * ΨS (t * y)

lemma fourier_hS {t : ℝ} (ht : 0 < t) (ξ : ℝ) : 𝓕 (hS t) ξ = FS (-(ξ / t)) := by
  rw [← fourier_ΨS, fourier_real_eq, fourier_real_eq]
  have := Measure.integral_comp_mul_left
    (fun z : ℝ => (t : ℂ) * (𝐞 (-(z * (ξ / t))) • ΨS z)) t
  have e : ∀ v : ℝ, 𝐞 (-(v * ξ)) • hS t v =
      (t : ℂ) * (𝐞 (-((t * v) * (ξ / t))) • ΨS (t * v)) := by
    intro v
    rw [hS, mul_smul_comm]
    congr 3
    field_simp
  simp_rw [e]
  rw [this, abs_inv, abs_of_pos ht, integral_const_mul, Complex.real_smul]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ htc, one_mul]


lemma hS_continuous (t : ℝ) : Continuous (hS t) :=
  continuous_const.mul (ΨS.continuous.comp (continuous_const.mul continuous_id))

lemma hS_eq (t y : ℝ) : hS t y = ((t * ψ (t * y) : ℝ) : ℂ) := by
  rw [hS, ΨS_eq]; push_cast; rfl

lemma hS_isBigO {t : ℝ} (ht : 0 < t) : hS t =O[cocompact ℝ] fun x => |x| ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := ψ_decay' 2
  refine Asymptotics.IsBigO.of_bound (C / t) ?_
  filter_upwards [(isCompact_singleton : IsCompact ({0} : Set ℝ)).compl_mem_cocompact] with y hy
  have hy0 : y ≠ 0 := hy
  have hya : 0 < |y| := abs_pos.mpr hy0
  rw [hS_eq, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ht.le (ψ_nonneg _)),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), Real.rpow_neg (abs_nonneg _),
    Real.rpow_two]
  have h1 := hC (t * y)
  have h2 : t * |y| ≤ 1 + |t * y| := by rw [abs_mul, abs_of_pos ht]; linarith
  have h3 : C / (1 + |t * y|) ^ 2 ≤ C / (t * |y|) ^ 2 := by gcongr
  calc t * ψ (t * y) ≤ t * (C / (t * |y|) ^ 2) := by gcongr; exact h1.trans h3
    _ = C / t * (|y| ^ 2)⁻¹ := by field_simp

lemma f_eq_zero_of_not_mem {t : ℝ} (ht : 0 < t) {n : ℤ}
    (hn : n ∉ Finset.Icc (-(⌊t⌋₊ : ℤ)) ⌊t⌋₊) : f (-(n / t)) = 0 := by
  apply f_eq_zero
  rw [abs_neg, abs_div, abs_of_pos ht, le_div_iff₀ ht, one_mul]
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  have h1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have h2 : (⌊t⌋₊ : ℤ) + 1 ≤ |n| := by
    rcases hn with h | h
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  have h3 : ((⌊t⌋₊ : ℤ) + 1 : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith

lemma summable_fourier_hS {t : ℝ} (ht : 0 < t) : Summable fun n : ℤ => 𝓕 (hS t) n := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (-(⌊t⌋₊ : ℤ)) ⌊t⌋₊)
  intro n hn
  rw [fourier_hS ht, FS_eq, f_eq_zero_of_not_mem ht hn, Complex.ofReal_zero]

/-- **Poisson summation** for the scaled function `t ψ(t ·)`. -/
theorem poisson {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∑' k : ℤ, t * ψ (t * (x + k)) =
      ∑ n ∈ Finset.Icc (-(⌊t⌋₊ : ℤ)) ⌊t⌋₊, f (-(n / t)) * Real.cos (2 * π * n * x) := by
  have P := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (hS_continuous t) one_lt_two
    (hS_isBigO ht) (summable_fourier_hS ht) x
  have hR : ∑' n : ℤ, 𝓕 (hS t) n * fourier n (x : UnitAddCircle) =
      ∑ n ∈ Finset.Icc (-(⌊t⌋₊ : ℤ)) ⌊t⌋₊, 𝓕 (hS t) n * fourier n (x : UnitAddCircle) := by
    apply tsum_eq_sum
    intro n hn
    rw [fourier_hS ht, FS_eq, f_eq_zero_of_not_mem ht hn, Complex.ofReal_zero, zero_mul]
  rw [hR] at P
  · simp_rw [hS_eq] at P
    rw [← Complex.ofReal_tsum] at P
    have := congrArg Complex.re P
    rw [Complex.ofReal_re, Complex.re_sum] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro n _
    rw [fourier_hS ht, FS_eq, fourier_coe_apply, Complex.re_ofReal_mul]
    congr 1
    have : 2 * (π : ℂ) * Complex.I * n * x / ((1 : ℝ) : ℂ) = ((2 * π * n * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_re]

end FRD.PtF
