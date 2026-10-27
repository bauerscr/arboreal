import Cont.LatHeat
import Cont.TorusGreen

/-!
# Fourier series of the torus heat kernel and the large-time part of `G_𝕋` (B1, scaling limit)

* `b1c_hasSum_heat` : `Θ_s(y) = ∑_{k ∈ ℤ²} e^{-π|k|² s} cos(2π k·y)`;
* `b1c_integral_large` : `∫_ε^∞ (Θ_s(y) - 1) ds = ∑_{k ≠ 0} e^{-επ|k|²} cos(2πk·y)/(π|k|²)`;
* `b1c_torusGreen_split` : `4π G_𝕋(x) = ∫_0^ε (Θ_s(x) - 1) ds + ∫_ε^∞ (Θ_s(x) - 1) ds`;
* `b1c_abs_small_cont_le` : `|∫_0^ε (Θ_s(x) - 1) ds| ≤ ε (1/(π δ²) + M + 1)` for `|x| ≥ δ`.
-/

namespace Cont

noncomputable section

open Real Set Filter Topology MeasureTheory HurwitzZeta

/-- `b(k) = π|k|²`. -/
def b1c_bk (k : ℤ × ℤ) : ℝ := π * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2)

/-- The phase `2π k·y`. -/
def b1c_phase (k : ℤ × ℤ) (y : Fin 2 → ℝ) : ℝ := 2 * π * (k.1 * y 0 + k.2 * y 1)

lemma b1c_sq_sum_ge_one {k : ℤ × ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2 := by
  have : (1 : ℤ) ≤ k.1 ^ 2 + k.2 ^ 2 := by
    rcases k with ⟨a, b⟩
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb ↦ hk (by simp [ha, hb])
      have := Int.one_le_abs hb
      nlinarith [sq_abs b, sq_nonneg a, abs_nonneg b]
    · have := Int.one_le_abs ha
      nlinarith [sq_abs a, sq_nonneg b, abs_nonneg a]
  exact_mod_cast this

lemma b1c_bk_ge {k : ℤ × ℤ} (hk : k ≠ 0) : π ≤ b1c_bk k := by
  have := b1c_sq_sum_ge_one hk
  unfold b1c_bk; nlinarith [pi_pos]

lemma b1c_bk_pos {k : ℤ × ℤ} (hk : k ≠ 0) : 0 < b1c_bk k := lt_of_lt_of_le pi_pos (b1c_bk_ge hk)

lemma b1c_exp_bk (k : ℤ × ℤ) (u : ℝ) :
    Real.exp (-(b1c_bk k) * u) =
      Real.exp (-π * (k.1 : ℝ) ^ 2 * u) * Real.exp (-π * (k.2 : ℝ) ^ 2 * u) := by
  rw [← Real.exp_add]; unfold b1c_bk; ring_nf

/-- Summability of the two-dimensional Gaussian `e^{-π|k|²u}`. -/
lemma b1c_summable_gauss2 {u : ℝ} (hu : 0 < u) :
    Summable fun k : ℤ × ℤ ↦ Real.exp (-π * (k.1 : ℝ) ^ 2 * u) * Real.exp (-π * (k.2 : ℝ) ^ 2 * u) :=
  (b1c_hasSum_theta hu).summable.mul_of_nonneg (b1c_hasSum_theta hu).summable
    (fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ (Real.exp_pos _).le)

lemma b1c_term_eq (a b s : ℝ) (k : ℤ × ℤ) :
    Complex.exp (2 * π * Complex.I * a * k.1) * (Real.exp (-π * (k.1 : ℝ) ^ 2 * s) : ℂ) *
      (Complex.exp (2 * π * Complex.I * b * k.2) * (Real.exp (-π * (k.2 : ℝ) ^ 2 * s) : ℂ)) =
      (Real.exp (-(b1c_bk k) * s) : ℂ) *
        Complex.exp ((b1c_phase k (fun i ↦ if i = 0 then a else b) : ℂ) * Complex.I) := by
  simp only [Complex.ofReal_exp, ← Complex.exp_add, b1c_bk, b1c_phase]
  congr 1
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  push_cast; ring

/-- Fourier series of the torus heat kernel. -/
theorem b1c_hasSum_heat {s : ℝ} (hs : 0 < s) (y : Fin 2 → ℝ) :
    HasSum (fun k : ℤ × ℤ ↦ Real.exp (-(b1c_bk k) * s) * Real.cos (b1c_phase k y))
      (torusHeat s (torusProj y)) := by
  have h0 := hasSum_int_cosKernel (y 0) hs
  have h1 := hasSum_int_cosKernel (y 1) hs
  have hy : (fun i : Fin 2 ↦ if i = 0 then y 0 else y 1) = y := by
    funext i; fin_cases i <;> rfl
  have hsum : Summable fun k : ℤ × ℤ ↦
      (Complex.exp (2 * π * Complex.I * y 0 * k.1) * (Real.exp (-π * (k.1 : ℝ) ^ 2 * s) : ℂ)) *
      (Complex.exp (2 * π * Complex.I * y 1 * k.2) * (Real.exp (-π * (k.2 : ℝ) ^ 2 * s) : ℂ)) := by
    refine Summable.of_norm_bounded (b1c_summable_gauss2 hs) fun k ↦ le_of_eq ?_
    rw [b1c_term_eq, hy, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), b1c_exp_bk]
  have h := Complex.hasSum_re (h0.mul h1 hsum)
  rw [b1_torusHeat_proj]
  convert h using 1
  · funext k
    rw [b1c_term_eq, hy, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · rw [← Complex.ofReal_mul, Complex.ofReal_re]

lemma b1c_bk_zero : b1c_bk 0 = 0 := by simp [b1c_bk]

lemma b1c_phase_zero (y : Fin 2 → ℝ) : b1c_phase 0 y = 0 := by simp [b1c_phase]

/-- The zero-mode-free series. -/
theorem b1c_hasSum_heat0 {s : ℝ} (hs : 0 < s) (y : Fin 2 → ℝ) :
    HasSum (fun k : ℤ × ℤ ↦ if k = 0 then 0 else
      Real.exp (-(b1c_bk k) * s) * Real.cos (b1c_phase k y)) (torusHeat s (torusProj y) - 1) := by
  have := hasSum_ite_sub_hasSum (b1c_hasSum_heat hs y) 0
  simpa [b1c_bk_zero, b1c_phase_zero] using this

/-- `∫_ε^∞ e^{-bs} ds = e^{-bε}/b`. -/
lemma b1c_int_Ioi_exp {b : ℝ} (hb : 0 < b) (ε : ℝ) :
    ∫ s in Ioi ε, Real.exp (-b * s) = Real.exp (-b * ε) / b := by
  rw [integral_exp_mul_Ioi (neg_lt_zero.2 hb), neg_div_neg_eq]

/-- Termwise large-time coefficient. -/
def b1c_Fc (ε : ℝ) (y : Fin 2 → ℝ) (k : ℤ × ℤ) : ℝ :=
  if k = 0 then 0 else Real.exp (-(b1c_bk k) * ε) / b1c_bk k * Real.cos (b1c_phase k y)

/-- The large-time part of `4π G_𝕋` as a Fourier series. -/
theorem b1c_integral_large {ε : ℝ} (hε : 0 < ε) (y : Fin 2 → ℝ) :
    ∫ s in Ioi ε, (torusHeat s (torusProj y) - 1) = ∑' k, b1c_Fc ε y k := by
  set G : ℤ × ℤ → ℝ → ℝ := fun k s ↦ if k = 0 then 0 else
    Real.exp (-(b1c_bk k) * s) * Real.cos (b1c_phase k y)
  have hpt : ∀ s ∈ Ioi ε, torusHeat s (torusProj y) - 1 = ∑' k, G k s := fun s hs ↦
    ((b1c_hasSum_heat0 (lt_trans hε hs) y).tsum_eq).symm
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : ∀ k, Integrable (G k) (volume.restrict (Ioi ε)) := fun k ↦ by
    by_cases hk : k = 0
    · simp only [G, hk, if_true]; exact integrable_zero _ _ _
    · simp only [G, hk, if_false]
      exact (exp_neg_integrableOn_Ioi ε (b1c_bk_pos hk)).mul_const _
  have hle : ∀ k, ∫ s in Ioi ε, ‖G k s‖ ≤
      π⁻¹ * (Real.exp (-π * (k.1 : ℝ) ^ 2 * ε) * Real.exp (-π * (k.2 : ℝ) ^ 2 * ε)) := fun k ↦ by
    by_cases hk : k = 0
    · simp only [G, hk, if_true, norm_zero, integral_zero]; positivity
    · have hb := b1c_bk_pos hk
      calc ∫ s in Ioi ε, ‖G k s‖ ≤ ∫ s in Ioi ε, Real.exp (-(b1c_bk k) * s) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun s ↦ norm_nonneg _)
              (exp_neg_integrableOn_Ioi ε hb) (Eventually.of_forall fun s ↦ ?_)
            simp only [G, hk, if_false, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_cos_le_one _)
        _ = Real.exp (-(b1c_bk k) * ε) / b1c_bk k := b1c_int_Ioi_exp hb ε
        _ ≤ Real.exp (-(b1c_bk k) * ε) / π := by
            gcongr; exact b1c_bk_ge hk
        _ = _ := by rw [b1c_exp_bk]; ring
  have hsum : Summable fun k ↦ ∫ s in Ioi ε, ‖G k s‖ :=
    Summable.of_nonneg_of_le (fun k ↦ integral_nonneg fun s ↦ norm_nonneg _) hle
      ((b1c_summable_gauss2 hε).mul_left _)
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun k ↦ ?_
  by_cases hk : k = 0
  · simp [G, b1c_Fc, hk]
  · simp only [G, b1c_Fc, hk, if_false]
    rw [integral_mul_const, b1c_int_Ioi_exp (b1c_bk_pos hk)]

/-- Splitting `4π G_𝕋(x)` at time `ε`. -/
theorem b1c_torusGreen_split {x : UnitAddTorus (Fin 2)} (hx : x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    4 * π * torusGreen x = (∫ s in (0 : ℝ)..ε, (torusHeat s x - 1)) +
      ∫ s in Ioi ε, (torusHeat s x - 1) := by
  have h := torusGreen_integrableOn hx
  rw [intervalIntegral.integral_of_le hε.le, torusGreen, ← mul_assoc,
    mul_inv_cancel₀ (by positivity : (4 * π : ℝ) ≠ 0), one_mul,
    ← Ioc_union_Ioi_eq_Ioi hε.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (h.mono_set Ioc_subset_Ioi_self) (h.mono_set (Ioi_subset_Ioi hε.le))]

/-- `‖x i‖ = |torusRep x i|`. -/
lemma b1c_norm_eq_rep (x : UnitAddTorus (Fin 2)) (i : Fin 2) : ‖x i‖ = |torusRep x i| := by
  have hx : x i = ((torusRep x i : ℝ) : UnitAddCircle) := (congrFun (torusProj_torusRep x) i).symm
  rw [hx, AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero]
  rw [abs_one]; exact abs_torusRep_le x i

lemma b1c_torusNorm_eq (x : UnitAddTorus (Fin 2)) :
    torusNorm x = Real.sqrt (torusRep x 0 ^ 2 + torusRep x 1 ^ 2) := by
  rw [torusNorm, b1c_norm_eq_rep, b1c_norm_eq_rep, sq_abs, sq_abs]

lemma b1c_r2_ge {x : UnitAddTorus (Fin 2)} {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ torusNorm x) :
    δ ^ 2 ≤ torusRep x 0 ^ 2 + torusRep x 1 ^ 2 := by
  rw [b1c_torusNorm_eq] at h
  have := pow_le_pow_left₀ hδ.le h 2
  rwa [Real.sq_sqrt (by positivity)] at this

lemma b1c_torusNorm_zero : torusNorm (0 : UnitAddTorus (Fin 2)) = 0 := by
  simp [torusNorm]

lemma b1c_ne_zero_of_norm {x : UnitAddTorus (Fin 2)} {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ torusNorm x) :
    x ≠ 0 := by
  rintro rfl; rw [b1c_torusNorm_zero] at h; linarith

/-- Short-time part of the continuum Green function at distance `≥ δ`. -/
theorem b1c_abs_small_cont_le {x : UnitAddTorus (Fin 2)} {δ : ℝ} (hδ : 0 < δ)
    (h : δ ≤ torusNorm x) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ s in (0 : ℝ)..ε, (torusHeat s x - 1)| ≤ ε * (1 / (π * δ ^ 2) + b1M + 1) := by
  have hr := b1c_r2_ge hδ h
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := ε) (f := fun s ↦ torusHeat s x - 1) (C := 1 / (π * δ ^ 2) + b1M + 1)
    (fun s hs ↦ by
      rw [uIoc_of_le hε.le] at hs
      have h1 := b1_abs_heat_sub_one_le (b1_box_of_rep x) (by positivity) hr
        (s := s) ⟨hs.1, hs.2.trans hε1⟩
      rw [torusProj_torusRep] at h1
      rwa [Real.norm_eq_abs])
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hε] at this
  linarith

end

end Cont
