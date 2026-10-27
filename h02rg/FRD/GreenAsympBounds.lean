import FRD.GreenAsymp1D
import FRD.GreenAsympGauss

/-!
# Scalar estimates for eq:LapZd

* `norm_Q_le_small`: `‖Q t n‖ ≤ exp(-n²/(8T))` for `0 ≤ t ≤ T`, `|n| ≤ 4T`;
* `pbar_le_small`: `pbar d R t ≤ Cpb d · exp(-R/(8T))` for `R ≥ 1`, `0 < t ≤ T`;
* `tail_integral`: `∫_T^∞ K/(t √t^d) dt = K (2/d) T^{-d/2}`;
* `rpow_mul_exp_le`: `n^{2-2/d} exp(-n^{2/d}/(8d)) ≤ Cpe d · n^{1-d}` for `n ≥ 1`.
-/

namespace FRD.GreenAsymp

noncomputable section

open MeasureTheory Set

theorem norm_Q_le_small {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hT : 0 < T) (n : ℤ)
    (hn : |(n : ℝ)| ≤ 4 * T) : ‖Q t n‖ ≤ Real.exp (-(n : ℝ) ^ 2 / (8 * T)) := by
  set a := |(n : ℝ)| / (4 * T) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one (by positivity)]; exact hn
  refine (norm_Q_le_chernoff ht n ha0 ha1).trans (Real.exp_le_exp.2 ?_)
  have h1 : 2 * t * a ^ 2 ≤ 2 * T * a ^ 2 := by nlinarith [sq_nonneg a]
  have h2 : -a * |(n : ℝ)| + 2 * T * a ^ 2 = -(n : ℝ) ^ 2 / (8 * T) := by
    rw [ha, ← sq_abs (n : ℝ)]; field_simp; ring
  linarith

/-- The constant in `pbar_le_small`. -/
def Cpb (d : ℕ) : ℝ := 2 ^ d * d.factorial * Real.exp (1 / 2)

theorem Cpb_nonneg (d : ℕ) : 0 ≤ Cpb d := by unfold Cpb; positivity

theorem pbar_le_small (d : ℕ) {R t T : ℝ} (hR : 1 ≤ R) (ht : 0 < t) (htT : t ≤ T) :
    pbar d R t ≤ Cpb d * Real.exp (-R / (8 * T)) := by
  have hpi := Real.pi_pos
  have hpi2 := Real.two_le_pi
  set u := R / (4 * t) with hu
  have hu0 : 0 < u := by positivity
  have h1 : (Real.sqrt (4 * Real.pi * t))⁻¹ ≤ 1 + u := by
    rw [← Real.sqrt_inv, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (4 * Real.pi * t)⁻¹ ≤ u := by
      rw [hu, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1R : 1 ≤ R * Real.pi := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1R (by positivity : (0 : ℝ) ≤ 4 * t)]
    nlinarith
  have h2 : pbar d R t ≤ Real.exp (-u) * (1 + u) ^ d := by
    unfold pbar
    rw [div_eq_mul_inv, ← inv_pow, show -R / (4 * t) = -u by rw [hu]; ring]
    gcongr
  have h3 : (1 + u) ^ d ≤ 2 ^ d * d.factorial * (Real.exp (1 / 2) * Real.exp (u / 2)) := by
    have := Real.pow_div_factorial_le_exp (x := (1 + u) / 2) (by positivity) d
    rw [← Real.exp_add, show 1 / 2 + u / 2 = (1 + u) / 2 by ring]
    rw [div_le_iff₀ (by positivity), div_pow] at this
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    calc (1 + u) ^ d = 2 ^ d * ((1 + u) ^ d / 2 ^ d) := by field_simp
      _ ≤ 2 ^ d * (Real.exp ((1 + u) / 2) * d.factorial) := by gcongr
      _ = _ := by ring
  have h4 : Real.exp (-u) * Real.exp (u / 2) ≤ Real.exp (-R / (8 * T)) := by
    rw [← Real.exp_add, Real.exp_le_exp, hu]
    have : R / (8 * T) ≤ R / (8 * t) := by gcongr
    have e : -(R / (4 * t)) + R / (4 * t) / 2 = -(R / (8 * t)) := by field_simp; ring
    rw [e, neg_div]; linarith
  calc pbar d R t ≤ Real.exp (-u) * (1 + u) ^ d := h2
    _ ≤ Real.exp (-u) * (2 ^ d * d.factorial * (Real.exp (1 / 2) * Real.exp (u / 2))) := by gcongr
    _ = Cpb d * (Real.exp (-u) * Real.exp (u / 2)) := by unfold Cpb; ring
    _ ≤ Cpb d * Real.exp (-R / (8 * T)) := by gcongr; exact Cpb_nonneg d

theorem inv_mul_sqrt_pow_eq {t : ℝ} (ht : 0 < t) (d : ℕ) (K : ℝ) :
    K / (t * Real.sqrt t ^ d) = K * t ^ (-((d : ℝ) / 2 + 1)) := by
  rw [sqrt_pow_eq_rpow ht.le, Real.rpow_neg ht.le, Real.rpow_add_one ht.ne', div_eq_mul_inv,
    mul_comm t]

theorem tail_integral {d : ℕ} (hd : 1 ≤ d) (K : ℝ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t => K / (t * Real.sqrt t ^ d)) (Ioi T) ∧
      ∫ t in Ioi T, K / (t * Real.sqrt t ^ d) = K * (2 / d) * T ^ (-((d : ℝ) / 2)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : -((d : ℝ) / 2 + 1) < -1 := by linarith
  have hcongr : EqOn (fun t => K / (t * Real.sqrt t ^ d))
      (fun t => K * t ^ (-((d : ℝ) / 2 + 1))) (Ioi T) :=
    fun t ht => inv_mul_sqrt_pow_eq (hT.trans ht) d K
  refine ⟨IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt ha hT).const_mul K) hcongr.symm
    measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_Ioi_rpow_of_lt ha hT, show -((d : ℝ) / 2 + 1) + 1 = -((d : ℝ) / 2) by ring]
  field_simp

/-- The constant in `rpow_mul_exp_le`. -/
def Cpe (d : ℕ) : ℝ := (8 * d) ^ (d * (d + 1)) * (d * (d + 1)).factorial

theorem Cpe_nonneg (d : ℕ) : 0 ≤ Cpe d := by unfold Cpe; positivity

theorem rpow_mul_exp_le {d : ℕ} (hd : 3 ≤ d) {n : ℝ} (hn : 1 ≤ n) :
    n ^ (2 - 2 / (d : ℝ)) * Real.exp (-(n ^ (2 / (d : ℝ)) / (8 * d))) ≤
      Cpe d * n ^ (1 - (d : ℝ)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : 0 < n := by linarith
  set N := d * (d + 1) with hN
  set s := n ^ (2 / (d : ℝ)) with hs
  set v := s / (8 * d) with hv
  have hv0 : 0 ≤ v := by positivity
  have key : n ^ (2 - 2 / (d : ℝ)) * n ^ ((d : ℝ) - 1) ≤ s ^ N := by
    rw [← Real.rpow_add hn0, hs, ← Real.rpow_mul_natCast hn0.le]
    refine Real.rpow_le_rpow_of_exponent_le hn ?_
    rw [hN]; push_cast
    have : 2 / (d : ℝ) * (d * (d + 1)) = 2 * (d + 1) := by field_simp
    rw [this]
    have : 0 < 2 / (d : ℝ) := by positivity
    linarith
  have hsN : s ^ N = (8 * d) ^ N * v ^ N := by
    rw [← mul_pow, hv]; congr 1; field_simp
  have hvN : v ^ N ≤ N.factorial * Real.exp v := by
    have := Real.pow_div_factorial_le_exp v hv0 N
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hk2 : n ^ (2 - 2 / (d : ℝ)) * n ^ ((d : ℝ) - 1) * Real.exp (-v) ≤ Cpe d := by
    calc n ^ (2 - 2 / (d : ℝ)) * n ^ ((d : ℝ) - 1) * Real.exp (-v)
        ≤ (8 * d) ^ N * (N.factorial * Real.exp v) * Real.exp (-v) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact key.trans (hsN.le.trans (mul_le_mul_of_nonneg_left hvN (by positivity)))
      _ = Cpe d := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
          unfold Cpe; rw [hN]
  have hinv : n ^ ((d : ℝ) - 1) * n ^ (1 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add hn0]; simp
  calc n ^ (2 - 2 / (d : ℝ)) * Real.exp (-(n ^ (2 / (d : ℝ)) / (8 * d)))
      = (n ^ (2 - 2 / (d : ℝ)) * n ^ ((d : ℝ) - 1) * Real.exp (-v)) * n ^ (1 - (d : ℝ)) := by
        rw [hv, hs]
        linear_combination (n ^ (2 - 2 / (d : ℝ)) *
          Real.exp (-(n ^ (2 / (d : ℝ)) / (8 * d)))) * hinv.symm
    _ ≤ Cpe d * n ^ (1 - (d : ℝ)) := by gcongr

end

end FRD.GreenAsymp
