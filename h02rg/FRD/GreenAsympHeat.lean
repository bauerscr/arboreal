import FRD.Green
import FRD.GreenAsymp1D
import FRD.GreenAsympGauss

/-!
# Heat-kernel representation of the `ℤ^d` Green function (for eq:LapZd)

* `greenZd_eq_integral_P`: `G(z) = ∫_0^∞ P z t dt`, where `P z t = Re ∏_i Q t (z_i)`
  is the heat kernel of `ℤ^d`;
* `abs_P_le_Q`: `|P z t| ≤ ‖Q t (z_i)‖`;
* `abs_P_sub_pbar_le`: local CLT on `ℤ^d`,
  `|P z t - pbar d |z|² t| ≤ K / (t · √t^d)`.
-/

namespace FRD.GreenAsymp

noncomputable section

open MeasureTheory Set Complex FRD

variable {d : ℕ}

/-- The heat kernel of `ℤ^d`: `P z t = Re ∏_i Q t (z_i)`. -/
def P (z : Zd d) (t : ℝ) : ℝ := (∏ i, Q t (z i)).re

theorem prod_fC (t : ℝ) (z : Zd d) (k : Fin d → ℝ) :
    ∏ i, fC t (z i) (k i) =
      cexp (((∑ i, k i * z i : ℝ) : ℂ) * I) * ((Real.exp (-t * lamR k) : ℝ) : ℂ) := by
  simp_rw [fC_ofReal, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.ofReal_prod,
    ← Real.exp_sum]
  congr 2
  · push_cast; rw [Finset.sum_mul]
  · unfold lamR; rw [Finset.mul_sum]; rfl

theorem re_prod_fC (t : ℝ) (z : Zd d) (k : Fin d → ℝ) :
    (∏ i, fC t (z i) (k i)).re = Real.cos (∑ i, k i * z i) * Real.exp (-t * lamR k) := by
  rw [prod_fC, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]

theorem continuous_prod_fC (t : ℝ) (z : Zd d) :
    Continuous fun k : Fin d → ℝ => ∏ i, fC t (z i) (k i) :=
  continuous_finsetProd _ fun i _ => (continuous_fC_ofReal t (z i)).comp (continuous_apply i)

theorem integral_Icc_fC (t : ℝ) (n : ℤ) :
    ∫ k in Icc (-Real.pi) Real.pi, fC t n k = (2 * Real.pi : ℂ) * Q t n := by
  have hpi := Real.pi_pos
  rw [Q, ← mul_assoc, mul_inv_cancel₀, one_mul, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc]
  rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
  exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)

theorem integral_cube_heat (t : ℝ) (z : Zd d) :
    ∫ k in cube d, Real.cos (∑ i, k i * z i) * Real.exp (-t * lamR k) =
      (2 * Real.pi) ^ d * P z t := by
  have hint : Integrable (fun k : Fin d → ℝ => ∏ i, fC t (z i) (k i))
      (volume.restrict (cube d)) :=
    (continuous_prod_fC t z).continuousOn.integrableOn_compact isCompact_cube
  simp_rw [← re_prod_fC]
  have hre : ∫ k in cube d, (∏ i, fC t (z i) (k i)).re =
      (∫ k in cube d, ∏ i, fC t (z i) (k i)).re := integral_re hint
  rw [hre]
  rw [volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (f := fun i (k : ℝ) => fC t (z i) k)]
  simp_rw [integral_Icc_fC, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [P, show (2 : ℂ) ^ d * (Real.pi : ℂ) ^ d = (((2 * Real.pi) ^ d : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-! ### Fubini -/

/-- The integrand `(k, t) ↦ cos(k·z) e^{-tλ(k)}`. -/
def heatF (z : Zd d) (q : (Fin d → ℝ) × ℝ) : ℝ :=
  Real.cos (∑ i, q.1 i * z i) * Real.exp (-q.2 * lamR q.1)

theorem continuous_heatF (z : Zd d) : Continuous (heatF z) := by
  unfold heatF lamR; fun_prop

theorem integral_exp_neg_mul_lam {l : ℝ} (hl : 0 < l) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t * l) = l⁻¹ := by
  have := integral_exp_mul_Ioi (a := -l) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at this
  rw [show (fun t : ℝ => Real.exp (-t * l)) = fun t => Real.exp (-l * t) by
    funext t; ring_nf, this]
  field_simp

theorem integrableOn_exp_neg_mul_lam {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun t : ℝ => Real.exp (-t * l)) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 hl
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only; ring_nf

theorem integrable_heatF (hd : 3 ≤ d) (z : Zd d) :
    Integrable (heatF z) ((volume.restrict (cube d)).prod (volume.restrict (Ioi 0))) := by
  have hd1 : 0 < d := by omega
  rw [integrable_prod_iff (continuous_heatF z).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_cube_ne_zero] with k ⟨hk, hk0⟩
    have hl := lamR_pos hk (hk0 ⟨0, hd1⟩)
    refine (integrableOn_exp_neg_mul_lam hl).mono'
      ((continuous_heatF z).comp (Continuous.prodMk_right k)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [heatF, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)
  · have hg : Integrable (fun k : Fin d → ℝ => |Real.cos (∑ i, k i * z i)| * (lamR k)⁻¹)
        (volume.restrict (cube d)) := by
      refine (integrable_inv_lamR hd).mono'
        (by exact ((continuous_abs.comp (Real.continuous_cos.comp (continuous_dotZ z))).measurable.mul
          continuous_lamR.measurable.inv).aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (inv_nonneg.2 (lamR_nonneg k))]
      exact mul_le_of_le_one_left (inv_nonneg.2 (lamR_nonneg k)) (Real.abs_cos_le_one _)
    refine hg.congr ?_
    filter_upwards [ae_cube_ne_zero] with k ⟨hk, hk0⟩
    have hl := lamR_pos hk (hk0 ⟨0, hd1⟩)
    simp only [heatF, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [integral_const_mul, integral_exp_neg_mul_lam hl]

/-- Heat-kernel representation: `G(z) = ∫_0^∞ P z t dt`. -/
theorem greenZd_eq_integral_P (hd : 3 ≤ d) (z : Zd d) :
    IntegrableOn (P z) (Ioi 0) ∧ greenZd d z = ∫ t in Ioi 0, P z t := by
  have hd1 : 0 < d := by omega
  have hpi := Real.pi_pos
  have hF := integrable_heatF hd z
  have hc : (0 : ℝ) < (2 * Real.pi) ^ d := by positivity
  have hPeq : (fun t => ∫ k in cube d, heatF z (k, t)) = fun t => (2 * Real.pi) ^ d * P z t := by
    funext t; exact integral_cube_heat t z
  have hPint : IntegrableOn (P z) (Ioi 0) := by
    have h1 := hF.integral_prod_right
    rw [hPeq] at h1
    have h2 := h1.const_mul ((2 * Real.pi) ^ d)⁻¹
    refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
    change ((2 * Real.pi) ^ d)⁻¹ * ((2 * Real.pi) ^ d * P z t) = P z t
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  refine ⟨hPint, ?_⟩
  have hstep : ∫ k in cube d, Real.cos (∑ i, k i * z i) / lamR k =
      ∫ k in cube d, ∫ t in Ioi 0, heatF z (k, t) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cube_ne_zero] with k ⟨hk, hk0⟩
    have hl := lamR_pos hk (hk0 ⟨0, hd1⟩)
    simp only [heatF]
    rw [integral_const_mul, integral_exp_neg_mul_lam hl, div_eq_mul_inv]
  have hswap := integral_integral_swap (f := fun k t => heatF z (k, t)) hF
  rw [greenZd, hstep, hswap,
    congrArg (fun f : ℝ → ℝ => ∫ t in Ioi (0 : ℝ), f t) hPeq]
  rw [integral_const_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow,
    one_mul]

/-! ### Pointwise bounds on `P` -/

theorem abs_P_le_Q {t : ℝ} (ht : 0 ≤ t) (z : Zd d) (i : Fin d) : |P z t| ≤ ‖Q t (z i)‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one (fun j _ => norm_nonneg _) fun j _ => norm_Q_le_one ht _)

theorem norm_prod_sub_prod_le {n : ℕ} (a b : Fin (n + 1) → ℂ) {M ε : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ M) (hb : ∀ i, ‖b i‖ ≤ M) (hab : ∀ i, ‖a i - b i‖ ≤ ε) :
    ‖∏ i, a i - ∏ i, b i‖ ≤ (n + 1) * ε * M ^ n := by
  induction n with
  | zero => simpa using hab 0
  | succ n ih =>
    rw [Fin.prod_univ_succ a, Fin.prod_univ_succ b]
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hab 0)
    have h1 := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => ha _) (fun i => hb _)
      (fun i => hab _)
    have h2 : ‖∏ i : Fin (n + 1), b i.succ‖ ≤ M ^ (n + 1) := by
      rw [norm_prod]
      calc ∏ i : Fin (n + 1), ‖b i.succ‖ ≤ ∏ _i : Fin (n + 1), M :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hb _
        _ = M ^ (n + 1) := by simp
    have e : a 0 * ∏ i : Fin (n + 1), a i.succ - b 0 * ∏ i : Fin (n + 1), b i.succ =
        a 0 * (∏ i : Fin (n + 1), a i.succ - ∏ i : Fin (n + 1), b i.succ) +
          (a 0 - b 0) * ∏ i : Fin (n + 1), b i.succ := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc ‖a 0‖ * ‖∏ i : Fin (n + 1), a i.succ - ∏ i : Fin (n + 1), b i.succ‖ +
          ‖a 0 - b 0‖ * ‖∏ i : Fin (n + 1), b i.succ‖
        ≤ M * ((n + 1) * ε * M ^ n) + ε * M ^ (n + 1) := by
          gcongr
          · exact ha 0
          · exact hab 0
      _ = ((n + 1 : ℕ) + 1 : ℝ) * ε * M ^ (n + 1) := by push_cast; ring

theorem prod_g (t : ℝ) (z : Zd d) :
    ∏ i, g t (z i) = pbar d (∑ i, ((z i : ℤ) : ℝ) ^ 2) t := by
  unfold g pbar
  rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 2
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The LCLT constant on `ℤ^d`. -/
def Kd (d : ℕ) : ℝ := d * Clclt * (Real.sqrt Real.pi / 4) ^ (d - 1)

theorem Kd_nonneg (d : ℕ) : 0 ≤ Kd d := by
  unfold Kd; have := Clclt_nonneg; positivity

/-- Local CLT on `ℤ^d`: `|P z t - pbar d |z|² t| ≤ K_d / (t √t^d)`. -/
theorem abs_P_sub_pbar_le (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (z : Zd d) :
    |P z t - pbar d (∑ i, ((z i : ℤ) : ℝ) ^ 2) t| ≤ Kd d / (t * Real.sqrt t ^ d) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hst := Real.sqrt_pos.2 ht
  rw [← prod_g]
  have e : P z t - ∏ i, g t (z i) = (∏ i, Q t (z i) - ∏ i, ((g t (z i) : ℝ) : ℂ)).re := by
    rw [P, Complex.sub_re, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hM : 0 ≤ Real.sqrt Real.pi / (4 * Real.sqrt t) := by positivity
  refine (norm_prod_sub_prod_le _ _ hM (fun i => norm_Q_le_sqrt ht _) (fun i => ?_)
    (fun i => norm_Q_sub_g_le ht _)).trans (le_of_eq ?_)
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (g_nonneg _ _)]
    exact g_le_sqrt ht _
  · unfold Kd
    simp only [Nat.add_sub_cancel]
    rw [div_pow, mul_pow]
    push_cast
    have h4 : (1 / 4 : ℝ) ^ n * 4 ^ n = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination (-(Clclt * Real.sqrt Real.pi ^ n * Real.sqrt t * Real.sqrt t ^ n)) * h4

end

end FRD.GreenAsymp
