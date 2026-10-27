import FRD.GreenAsympHeat
import FRD.GreenAsympBounds
import FRD.GreenBd

/-!
# Asymptotics of the `ℤ^d` Green function (eq:LapZd)

`greenZd_asymp`: for `d ≥ 3` there is `C` such that for all `z ≠ 0`
`|G(z) - c_d |z|^{2-d}| ≤ C |z|^{1-d}`, with `c_d = Γ(d/2-1)/(4π^{d/2})` (`cd`)
and `|z|` the Euclidean norm (`eNorm`).

Proof: `G(z) = ∫_0^∞ P z t dt` (heat kernel), `∫_0^∞ pbar = c_d |z|^{2-d}`; split at
`T = |z|^{2-2/d}`: LCLT for `t > T` (error `T^{-d/2} = |z|^{1-d}`), Chernoff bounds for `t ≤ T`.
-/

namespace FRD.GreenAsymp

noncomputable section

open MeasureTheory Set FRD

variable {d : ℕ}

/-- The constant of `greenZd_asymp`. -/
def Casymp (d : ℕ) : ℝ := Kd d * (2 / d) + (1 + Cpb d) * Cpe d

theorem Casymp_nonneg (d : ℕ) : 0 ≤ Casymp d := by
  unfold Casymp
  have := Kd_nonneg d; have := Cpb_nonneg d; have := Cpe_nonneg d
  positivity

theorem sum_sq_eq_eNorm_sq (z : Zd d) : ∑ i, ((z i : ℤ) : ℝ) ^ 2 = eNorm z ^ 2 := by
  rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- **eq:LapZd**: `|G(z) - c_d |z|^{2-d}| ≤ C |z|^{1-d}` for `z ≠ 0`. -/
theorem greenZd_asymp_explicit (hd : 3 ≤ d) (z : Zd d) (hz : z ≠ 0) :
    |greenZd d z - cd d * eNorm z ^ (2 - (d : ℝ))| ≤ Casymp d * eNorm z ^ (1 - (d : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set n := eNorm z with hn
  have hn1 : 1 ≤ n := by
    have := one_le_supNormZ hz
    exact le_trans (by exact_mod_cast this) (supNormZ_le_eNorm z)
  have hn0 : 0 < n := by linarith
  set R := ∑ i, ((z i : ℤ) : ℝ) ^ 2 with hR
  have hRn : R = n ^ 2 := sum_sq_eq_eNorm_sq z
  have hR1 : 1 ≤ R := by rw [hRn]; nlinarith
  set T := n ^ (2 - 2 / (d : ℝ)) with hT
  have hexp1 : 1 ≤ 2 - 2 / (d : ℝ) := by
    have : 2 / (d : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hnT : n ≤ T := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 hexp1
    rwa [Real.rpow_one] at this
  have hT0 : 0 < T := by linarith
  obtain ⟨hPi, hG⟩ := greenZd_eq_integral_P hd z
  obtain ⟨hpbI, hpbV⟩ := integral_pbar hd (by linarith : 0 < R)
  have hcd : cd d * n ^ (2 - (d : ℝ)) = ∫ t in Ioi 0, pbar d R t := by
    rw [hpbV, hRn, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 2; push_cast; ring
  set D := fun t => P z t - pbar d R t with hD
  have hDi : IntegrableOn D (Ioi 0) := hPi.sub hpbI
  have hE : greenZd d z - cd d * n ^ (2 - (d : ℝ)) =
      (∫ t in Ioc 0 T, D t) + ∫ t in Ioi T, D t := by
    rw [hG, hcd, ← integral_sub hPi hpbI, ← Ioc_union_Ioi_eq_Ioi hT0.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hDi.mono_set Ioc_subset_Ioi_self) (hDi.mono_set (Ioi_subset_Ioi hT0.le))]
  -- a coordinate with `|z_i| = |z|_∞`
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun i => (z i).natAbs
  have hzi : |((z i : ℤ) : ℝ)| = (supNormZ z : ℝ) := by
    rw [supNormZ, hi, Nat.cast_natAbs, Int.cast_abs]
  have hzin : |((z i : ℤ) : ℝ)| ≤ n := by rw [hzi]; exact supNormZ_le_eNorm z
  have hnzi : n ^ 2 ≤ d * ((z i : ℤ) : ℝ) ^ 2 := by
    have h := eNorm_le_supNormZ z
    rw [← hzi] at h
    have hs : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
    calc n ^ 2 ≤ (Real.sqrt d * |((z i : ℤ) : ℝ)|) ^ 2 := pow_le_pow_left₀ hn0.le h 2
      _ = d * ((z i : ℤ) : ℝ) ^ 2 := by rw [mul_pow, hs, sq_abs]
  set ε := Real.exp (-(n ^ (2 / (d : ℝ)) / (8 * d))) with hε
  have hn2T : n ^ 2 / T = n ^ (2 / (d : ℝ)) := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_sub hn0]; congr 1; push_cast; ring
  have hsmall : ∀ t ∈ Ioc 0 T, ‖D t‖ ≤ (1 + Cpb d) * ε := by
    intro t ⟨ht0, htT⟩
    have hdpos : (0 : ℝ) < d := by linarith
    have hkey : -(n ^ 2) / (8 * T) ≤ 0 := by
      have : 0 ≤ n ^ 2 / (8 * T) := by positivity
      rw [neg_div]; linarith
    have hεeq : ε = Real.exp (-(n ^ 2) / (8 * d * T)) := by
      rw [hε]; congr 1
      rw [neg_div, ← hn2T]; field_simp
    have h1 : |P z t| ≤ ε := by
      refine (abs_P_le_Q ht0.le z i).trans ((norm_Q_le_small ht0.le htT hT0 _
        (by linarith)).trans ?_)
      rw [hεeq, Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hnzi, hT0]
    have h2 : pbar d R t ≤ Cpb d * ε := by
      refine (pbar_le_small d hR1 ht0 htT).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Cpb_nonneg d)
      rw [hεeq, Real.exp_le_exp, hRn, neg_div, neg_div, neg_le_neg_iff,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ n ^ 2 * (8 * T) := by positivity
      nlinarith
    rw [Real.norm_eq_abs, hD]
    simp only
    calc |P z t - pbar d R t| ≤ |P z t| + |pbar d R t| := abs_sub _ _
      _ ≤ ε + Cpb d * ε := by rw [abs_of_nonneg (pbar_nonneg _ _ _)]; linarith
      _ = (1 + Cpb d) * ε := by ring
  have hbound1 : ‖∫ t in Ioc 0 T, D t‖ ≤ (1 + Cpb d) * Cpe d * n ^ (1 - (d : ℝ)) := by
    refine (norm_setIntegral_le_of_norm_le_const (by simp) hsmall).trans ?_
    rw [Real.volume_real_Ioc_of_le hT0.le, sub_zero, mul_assoc (1 + Cpb d) ε,
      mul_assoc (1 + Cpb d) (Cpe d)]
    have hC1 : 0 ≤ 1 + Cpb d := by have := Cpb_nonneg d; linarith
    refine mul_le_mul_of_nonneg_left ?_ hC1
    rw [mul_comm, hε, hT]
    exact rpow_mul_exp_le hd hn1
  obtain ⟨htI, htV⟩ := tail_integral hd1 (Kd d) hT0
  have hbound2 : ‖∫ t in Ioi T, D t‖ ≤ Kd d * (2 / d) * n ^ (1 - (d : ℝ)) := by
    refine (norm_integral_le_of_norm_le htI ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
    · have ht0 : 0 < t := hT0.trans ht
      rw [Real.norm_eq_abs]
      exact abs_P_sub_pbar_le hd1 ht0 z
    · rw [htV, hT, ← Real.rpow_mul hn0.le]
      congr 2
      field_simp; ring
  rw [hE]
  calc |(∫ t in Ioc 0 T, D t) + ∫ t in Ioi T, D t|
      ≤ ‖∫ t in Ioc 0 T, D t‖ + ‖∫ t in Ioi T, D t‖ := abs_add_le _ _
    _ ≤ (1 + Cpb d) * Cpe d * n ^ (1 - (d : ℝ)) + Kd d * (2 / d) * n ^ (1 - (d : ℝ)) :=
        add_le_add hbound1 hbound2
    _ = Casymp d * n ^ (1 - (d : ℝ)) := by unfold Casymp; ring

/-- **eq:LapZd** (`h02rg.tex`): `(-Δ^{ℤ^d})^{-1}(0,z) = c_d |z|^{-(d-2)} + O(|z|^{-(d-2)-1})`. -/
theorem greenZd_asymp (hd : 3 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Zd d, z ≠ 0 →
    |greenZd d z - cd d * eNorm z ^ (2 - (d : ℝ))| ≤ C * eNorm z ^ (1 - (d : ℝ)) :=
  ⟨Casymp d, Casymp_nonneg d, fun z hz => greenZd_asymp_explicit hd z hz⟩

/-- The weaker form `|G(z) - c_d |z|^{2-d}| ≤ C |z|^{2-d-κ'}` for any `κ' ∈ [0, 1]`. -/
theorem greenZd_asymp_kappa (hd : 3 ≤ d) {κ : ℝ} (hκ : κ ≤ 1) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : Zd d, z ≠ 0 →
      |greenZd d z - cd d * eNorm z ^ (2 - (d : ℝ))| ≤ C * eNorm z ^ (2 - (d : ℝ) - κ) := by
  refine ⟨Casymp d, Casymp_nonneg d, fun z hz => (greenZd_asymp_explicit hd z hz).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (Casymp_nonneg d)
  have hn1 : 1 ≤ eNorm z :=
    le_trans (by exact_mod_cast one_le_supNormZ hz) (supNormZ_le_eNorm z)
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

end

end FRD.GreenAsymp
