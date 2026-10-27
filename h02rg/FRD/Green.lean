import FRD.Lift

/-!
# The Green's function of the lattice Laplacian on `ℤ^d`

With `λ(k) = ∑_i (2 - 2 cos k_i)`, the Green's function of `-Δ` on `ℤ^d`, `d ≥ 3`, is
`(-Δ)^{-1}(0, z) = (2π)^{-d} ∫_{[-π,π]^d} cos(k·z)/λ(k) dk` (`greenZd`).

* `aeval_Ainf_fourier`: the Fourier representation
  `(p(A_∞) δ_0)(z) = (2π)^{-d} ∫ p(û(k)) cos(k·z) dk`, `û = (λ + m²)/(2d + m²)`;
* `integrable_inv_lamR`: `1/λ` is integrable on `[-π,π]^d` for `d ≥ 3`;
* `hasSum_covZ_green`: `(-Δ^{ℤ^d})^{-1} = ∑_{j ≥ 1} c_j` at `m² = 0`, with
  `c_j = covZ P d 0 (L^{j-1}/2, L^j/2]` (`(0, L/2]` for `j = 1`).
-/

namespace FRD

noncomputable section

open Finset MeasureTheory Set Grassmann

variable {d : ℕ}

/-- `λ(k) = ∑_i (2 - 2 cos k_i)`. -/
def lamR (k : Fin d → ℝ) : ℝ := ∑ i, (2 - 2 * Real.cos (k i))

/-- The cube `[-π, π]^d`. -/
abbrev cube (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-Real.pi) Real.pi

/-- `k · z`. -/
def dotZ (k : Fin d → ℝ) (z : Zd d) : ℝ := ∑ i, k i * z i

theorem continuous_lamR : Continuous (lamR : (Fin d → ℝ) → ℝ) := by
  unfold lamR; fun_prop

theorem continuous_dotZ (z : Zd d) : Continuous fun k : Fin d → ℝ => dotZ k z := by
  unfold dotZ; fun_prop

theorem isCompact_cube : IsCompact (cube d) := isCompact_univ_pi fun _ => isCompact_Icc

theorem integrableOn_cube {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) : IntegrableOn f (cube d) :=
  hf.continuousOn.integrableOn_compact isCompact_cube

/-! ### Orthogonality -/

theorem integral_cexp_int (m : ℤ) :
    ∫ x in Icc (-Real.pi) Real.pi, Complex.exp (((x * m : ℝ) : ℂ) * Complex.I) =
      if m = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  split_ifs with hm
  · subst hm; simp; ring
  · have hc : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Complex.I_ne_zero
    have h1 : ∀ x : ℝ, Complex.exp (((x * m : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((m : ℂ) * Complex.I * x) := fun x => by push_cast; ring_nf
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((m : ℂ) * Complex.I * (Real.pi : ℝ)) =
        Complex.exp ((m : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
      rw [show (m : ℂ) * Complex.I * (Real.pi : ℝ) =
          (m : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) + m * (2 * Real.pi * Complex.I) by
            push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h2, sub_self, zero_div]

theorem integral_cos_dotZ (z : Zd d) :
    ∫ k in cube d, Real.cos (dotZ k z) = if z = 0 then (2 * Real.pi) ^ d else 0 := by
  have h1 : ∀ k : Fin d → ℝ, Real.cos (dotZ k z) =
      RCLike.re (∏ i, Complex.exp (((k i * z i : ℝ) : ℂ) * Complex.I)) := by
    intro k
    rw [← Complex.exp_sum, ← Finset.sum_mul, dotZ]
    rw [show (∑ i, ((k i * z i : ℝ) : ℂ)) = ((∑ i, k i * z i : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.exp_ofReal_mul_I_re _).symm
  simp_rw [h1]
  have hμ : (volume : Measure (Fin d → ℝ)).restrict (cube d) =
      Measure.pi fun _ => volume.restrict (Icc (-Real.pi) Real.pi) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  rw [hμ]
  have hint : Integrable (fun k : Fin d → ℝ => ∏ i, Complex.exp (((k i * z i : ℝ) : ℂ) * Complex.I))
      (Measure.pi fun _ => volume.restrict (Icc (-Real.pi) Real.pi)) := by
    refine Integrable.fintype_prod (f := fun i x => Complex.exp (((x * z i : ℝ) : ℂ) * Complex.I))
      fun i => ?_
    exact Continuous.integrableOn_Icc (by fun_prop)
  rw [integral_re hint]
  rw [integral_fintype_prod_eq_prod (f := fun i x => Complex.exp (((x * z i : ℝ) : ℂ) * Complex.I))]
  simp_rw [integral_cexp_int]
  split_ifs with hz
  · subst hz
    simp only [Pi.zero_apply, if_true, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [show ((((2 * Real.pi : ℝ)) : ℂ)) ^ d = (((2 * Real.pi) ^ d : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h; push Not at h; exact hz (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp

/-! ### The eigenvalue relation -/

theorem dotZ_add_dirZ (k : Fin d → ℝ) (z : Zd d) (i : Fin d) :
    dotZ k (z + dirZ (Sum.inl i)) = dotZ k z + k i ∧
      dotZ k (z + dirZ (Sum.inr i)) = dotZ k z - k i := by
  constructor
  · simp only [dotZ, dirZ, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply]
  · simp only [dotZ, dirZ, Pi.add_apply, Pi.neg_apply, Pi.single_apply]
    push_cast
    simp_rw [mul_add, Finset.sum_add_distrib, mul_neg, mul_ite, mul_one, mul_zero,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← sub_eq_add_neg]

theorem sum_cos_dirZ (k : Fin d → ℝ) (z : Zd d) :
    ∑ e : Dir d, Real.cos (dotZ k (z + dirZ e)) = 2 * Real.cos (dotZ k z) * ∑ i, Real.cos (k i) := by
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(dotZ_add_dirZ k z i).1, (dotZ_add_dirZ k z i).2, Real.cos_add, Real.cos_sub]
  ring

theorem lamR_eq (k : Fin d → ℝ) : lamR k = 2 * d - 2 * ∑ i, Real.cos (k i) := by
  simp [lamR, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]

theorem uhat_mul_cos {msq : ℝ} (hmsq : 2 * (d : ℝ) + msq ≠ 0) (k : Fin d → ℝ) (z : Zd d) :
    (lamR k + msq) / (2 * d + msq) * Real.cos (dotZ k z) =
      Real.cos (dotZ k z) - (2 * d + msq)⁻¹ * ∑ e : Dir d, Real.cos (dotZ k (z + dirZ e)) := by
  rw [sum_cos_dirZ, lamR_eq]
  field_simp
  ring

/-! ### The Fourier representation of the kernels on `ℤ^d` -/

theorem pow_Ainf_fourier {msq : ℝ} (hmsq : 2 * (d : ℝ) + msq ≠ 0) (n : ℕ) (z : Zd d) :
    (Ainf d msq ^ n) (Finsupp.single 0 1) z =
      (2 * Real.pi)⁻¹ ^ d * ∫ k in cube d,
        ((lamR k + msq) / (2 * d + msq)) ^ n * Real.cos (dotZ k z) := by
  induction n generalizing z with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, one_mul, integral_cos_dotZ, Finsupp.single_apply]
    by_cases hz : z = 0
    · subst hz; simp only [if_true]
      rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
    · rw [if_neg (Ne.symm hz), if_neg hz, mul_zero]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Ainf_apply, ih]
    simp_rw [ih]
    have h1 : ∀ k : Fin d → ℝ, ((lamR k + msq) / (2 * d + msq)) ^ (n + 1) * Real.cos (dotZ k z) =
        ((lamR k + msq) / (2 * d + msq)) ^ n * Real.cos (dotZ k z) - (2 * d + msq)⁻¹ *
          ∑ e : Dir d, ((lamR k + msq) / (2 * d + msq)) ^ n * Real.cos (dotZ k (z + dirZ e)) := by
      intro k
      rw [pow_succ, mul_assoc, uhat_mul_cos hmsq, ← Finset.mul_sum]
      ring
    simp_rw [h1]
    have hc : ∀ w : Zd d, Continuous fun k : Fin d → ℝ =>
        ((lamR k + msq) / (2 * d + msq)) ^ n * Real.cos (dotZ k w) := fun w =>
      ((continuous_lamR.add continuous_const).div_const _).pow n |>.mul
        (Real.continuous_cos.comp (continuous_dotZ w))
    rw [integral_sub (integrableOn_cube (hc z)), integral_const_mul,
      integral_finsetSum _ fun e _ => integrableOn_cube (hc _), Finset.mul_sum, Finset.mul_sum,
      mul_sub, Finset.mul_sum]
    · congr 1
      refine Finset.sum_congr rfl fun e _ => by ring
    · exact (integrable_finsetSum _ fun e _ => integrableOn_cube (hc _)).const_mul _

/-- The Fourier representation of the `ℤ^d` kernels. -/
theorem aeval_Ainf_fourier {msq : ℝ} (hmsq : 2 * (d : ℝ) + msq ≠ 0) (p : Polynomial ℝ) (z : Zd d) :
    Polynomial.aeval (Ainf d msq) p (Finsupp.single 0 1) z =
      (2 * Real.pi)⁻¹ ^ d * ∫ k in Set.pi Set.univ (fun _ => Set.Icc (-Real.pi) Real.pi),
        p.eval ((lamR k + msq) / (2 * d + msq)) * Real.cos (∑ i, k i * z i) := by
  have hc : ∀ q : Polynomial ℝ, Continuous fun k : Fin d → ℝ =>
      q.eval ((lamR k + msq) / (2 * d + msq)) * Real.cos (dotZ k z) := fun q =>
    (q.continuous.comp ((continuous_lamR.add continuous_const).div_const _)).mul
      (Real.continuous_cos.comp (continuous_dotZ z))
  change _ = (2 * Real.pi)⁻¹ ^ d * ∫ k in cube d,
    p.eval ((lamR k + msq) / (2 * d + msq)) * Real.cos (dotZ k z)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, Finsupp.coe_add, Pi.add_apply, Polynomial.eval_add,
      add_mul, hp, hq]
    rw [integral_add (integrableOn_cube (hc p)) (integrableOn_cube (hc q)), mul_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, Module.End.one_apply, Finsupp.smul_apply, smul_eq_mul,
      pow_Ainf_fourier hmsq]
    simp only [Polynomial.eval_monomial, mul_assoc]
    rw [integral_const_mul]; ring

/-! ### Integrability of `1/λ` for `d ≥ 3` -/

theorem lamR_nonneg (k : Fin d → ℝ) : 0 ≤ lamR k :=
  Finset.sum_nonneg fun i _ => by linarith [Real.cos_le_one (k i)]

theorem lamR_le (k : Fin d → ℝ) : lamR k ≤ 4 * d := by
  calc lamR k ≤ ∑ _i : Fin d, (4 : ℝ) :=
        Finset.sum_le_sum fun i _ => by linarith [Real.neg_one_le_cos (k i)]
    _ = 4 * d := by simp [mul_comm]

theorem lamR_ge {k : Fin d → ℝ} (hk : k ∈ cube d) :
    4 / Real.pi ^ 2 * ∑ i, k i ^ 2 ≤ lamR k := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Real.cos_le_one_sub_mul_cos_sq (x := k i) (abs_le.2 (hk i (Set.mem_univ i)))
  have : 4 / Real.pi ^ 2 * k i ^ 2 = 2 * (2 / Real.pi ^ 2 * k i ^ 2) := by ring
  linarith

theorem integrableOn_abs_rpow {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun x : ℝ => |x| ^ r) (Icc (-Real.pi) Real.pi) := by
  have hpi := Real.pi_pos
  have h1 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 Real.pi := by
    refine (intervalIntegral.intervalIntegrable_rpow' hr).congr fun x hx => ?_
    rw [Set.uIoc_of_le hpi.le] at hx
    simp [abs_of_pos hx.1]
  have h2 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (-Real.pi) 0 := by
    rw [IntervalIntegrable.iff_comp_neg, neg_neg, neg_zero]
    simpa using h1.symm
  have h3 := h2.trans h1
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 h3

theorem ae_cube_ne_zero :
    ∀ᵐ k ∂(volume.restrict (cube d)), k ∈ cube d ∧ ∀ i, k i ≠ 0 := by
  have h : ∀ᵐ k : Fin d → ℝ ∂volume, ∀ i, k i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    rw [volume_pi]
    exact Measure.ae_eval_ne _ i 0
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc),
    ae_restrict_of_ae h] with k hk hk'
  exact ⟨hk, hk'⟩

theorem lamR_pos {k : Fin d → ℝ} (hk : k ∈ cube d) {i : Fin d} (hi : k i ≠ 0) : 0 < lamR k := by
  refine lt_of_lt_of_le ?_ (lamR_ge hk)
  refine mul_pos (by positivity) ?_
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => k i ^ 2)
    (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i))

theorem inv_lamR_le (hd : 1 ≤ d) {k : Fin d → ℝ} (hk : k ∈ cube d) (hk0 : ∀ i, k i ≠ 0) :
    (lamR k)⁻¹ ≤ Real.pi ^ 2 / 4 * ∏ i, |k i| ^ (-2 / d : ℝ) := by
  set S := ∑ i, k i ^ 2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have i0 : Fin d := ⟨0, hd⟩
  have hS : 0 < S := lt_of_lt_of_le (by have := hk0 i0; positivity)
    (Finset.single_le_sum (f := fun i => k i ^ 2) (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i0))
  have hl := lamR_ge hk
  have hlpos : 0 < lamR k := lt_of_lt_of_le (by positivity) hl
  have hprod : ∏ i, |k i| ^ (2 / d : ℝ) ≤ S := by
    calc ∏ i, |k i| ^ (2 / d : ℝ) ≤ ∏ _i : Fin d, S ^ (1 / d : ℝ) := by
          refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
          rw [show (2 / d : ℝ) = 2 * (1 / d) by ring, Real.rpow_mul (abs_nonneg _)]
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
          exact Finset.single_le_sum (f := fun i => k i ^ 2) (fun j _ => sq_nonneg (k j))
            (Finset.mem_univ i)
      _ = S := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
            ← Real.rpow_mul hS.le, one_div_mul_cancel hd'.ne', Real.rpow_one]
  have hppos : 0 < ∏ i, |k i| ^ (2 / d : ℝ) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (abs_pos.2 (hk0 i)) _
  have heq : ∏ i, |k i| ^ (-2 / d : ℝ) = (∏ i, |k i| ^ (2 / d : ℝ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [neg_div, Real.rpow_neg (abs_nonneg _)]
  rw [heq]
  calc (lamR k)⁻¹ ≤ (4 / Real.pi ^ 2 * S)⁻¹ := inv_anti₀ (by positivity) hl
    _ = Real.pi ^ 2 / 4 * S⁻¹ := by field_simp
    _ ≤ Real.pi ^ 2 / 4 * (∏ i, |k i| ^ (2 / d : ℝ))⁻¹ := by
        gcongr

theorem integrable_inv_lamR (hd : 3 ≤ d) :
    IntegrableOn (fun k : Fin d → ℝ => (lamR k)⁻¹)
      (Set.pi Set.univ fun _ => Set.Icc (-Real.pi) Real.pi) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : -1 < (-2 / d : ℝ) := by
    rw [neg_div, neg_lt_neg_iff, div_lt_one (by linarith)]; linarith
  have hG : IntegrableOn (fun k : Fin d → ℝ => Real.pi ^ 2 / 4 * ∏ i, |k i| ^ (-2 / d : ℝ))
      (cube d) := by
    refine Integrable.const_mul ?_ _
    show Integrable _ (volume.restrict (cube d))
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (f := fun _ x => |x| ^ (-2 / d : ℝ))
      fun _ => integrableOn_abs_rpow hr
  refine hG.mono' (continuous_lamR.measurable.inv.aestronglyMeasurable) ?_
  filter_upwards [ae_cube_ne_zero] with k ⟨hk, hk0⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (lamR_nonneg k))]
  exact inv_lamR_le (by omega) hk hk0

/-! ### The Green's function and its decomposition -/

/-- `(-Δ^{ℤ^d})^{-1}(0, z) = (2π)^{-d} ∫_{[-π,π]^d} cos(k·z)/λ(k) dk`. -/
def greenZd (d : ℕ) (z : Zd d) : ℝ :=
  (2 * Real.pi)⁻¹ ^ d * ∫ k in Set.pi Set.univ (fun _ => Set.Icc (-Real.pi) Real.pi),
    Real.cos (∑ i, k i * z i) / lamR k

theorem lamR_div_mem (hd : 1 ≤ d) (k : Fin d → ℝ) : lamR k / (2 * d) ∈ Icc (0 : ℝ) 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨div_nonneg (lamR_nonneg k) (by positivity), ?_⟩
  rw [div_le_iff₀ (by positivity)]; linarith [lamR_le k]

variable (P : PtFamily)

theorem measurable_eval_uncurry : Measurable fun q : ℝ × ℝ => (P.P q.2).eval q.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (x t : ℝ) => (P.P t).eval x)
    (fun t => (P.P t).continuous) P.measurable

theorem measurable_integral_scales (S : Set ℝ) :
    Measurable fun u : ℝ => ∫ t in S, t * (P.P t).eval u := by
  have h : StronglyMeasurable (Function.uncurry fun (u t : ℝ) => t * (P.P t).eval u) :=
    (measurable_snd.mul (measurable_eval_uncurry P)).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right (ν := volume.restrict S) h).measurable

/-- The covariance of the scales `(a, b]` at `m² = 0` in Fourier form. -/
theorem covZ_eq_integral (hd : 1 ≤ d) {a : ℝ} (b : ℝ) (ha : 0 ≤ a) (z : Zd d) :
    covZ P d 0 (Ioc a b) z = ∫ k in cube d, (2 * Real.pi)⁻¹ ^ d * (2 * (d : ℝ))⁻¹ *
      ((∫ t in Ioc a b, t * (P.P t).eval (lamR k / (2 * d))) * Real.cos (dotZ k z)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hne : 2 * (d : ℝ) + 0 ≠ 0 := by positivity
  obtain ⟨K, hK0, hK⟩ := eval_le_const P
  unfold covZ
  have h1 : ∀ t : ℝ, t * Polynomial.aeval (Ainf d 0) (P.P t) (Finsupp.single 0 1) z =
      (2 * Real.pi)⁻¹ ^ d * ∫ k in cube d,
        t * ((P.P t).eval (lamR k / (2 * d)) * Real.cos (dotZ k z)) := by
    intro t
    rw [aeval_Ainf_fourier hne, integral_const_mul]
    simp only [add_zero, dotZ]
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  have hint : Integrable (Function.uncurry fun (t : ℝ) (k : Fin d → ℝ) =>
      t * ((P.P t).eval (lamR k / (2 * d)) * Real.cos (dotZ k z)))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (cube d))) := by
    rw [Measure.prod_restrict]
    refine Measure.integrableOn_of_bounded (M := |b| * K) ?_ ?_ ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp [Real.volume_Ioc]) isCompact_cube.measure_lt_top.ne
    · refine Measurable.aestronglyMeasurable ?_
      refine measurable_fst.mul (Measurable.mul ?_ ?_)
      · exact (measurable_eval_uncurry P).comp
          (((continuous_lamR.measurable.comp measurable_snd).div_const _).prodMk measurable_fst)
      · exact (Real.continuous_cos.comp ((continuous_dotZ z).comp continuous_snd)).measurable
    · refine (ae_restrict_iff' (measurableSet_Ioc.prod
        (MeasurableSet.univ_pi fun _ => measurableSet_Icc))).2
        (Filter.Eventually.of_forall fun q hq => ?_)
      have ht : q.1 ∈ Ioc a b := hq.1
      have ht0 : 0 < q.1 := lt_of_le_of_lt ha ht.1
      have hu := lamR_div_mem hd q.2
      have h0 := P.nonneg q.1 ht0 _ hu
      have hK' := hK q.1 ht0 _ hu
      show ‖q.1 * ((P.P q.1).eval (lamR q.2 / (2 * d)) * Real.cos (dotZ q.2 z))‖ ≤ |b| * K
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos ht0, abs_of_nonneg h0]
      calc q.1 * ((P.P q.1).eval (lamR q.2 / (2 * d)) * |Real.cos (dotZ q.2 z)|)
          ≤ |b| * (K * 1) := by
            gcongr
            · exact ht.2.trans (le_abs_self b)
            · exact Real.abs_cos_le_one _
        _ = |b| * K := by ring
  rw [integral_integral_swap hint, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [add_zero]
  rw [← integral_mul_const]
  have : ∀ t : ℝ, t * ((P.P t).eval (lamR k / (2 * d)) * Real.cos (dotZ k z)) =
      t * (P.P t).eval (lamR k / (2 * d)) * Real.cos (dotZ k z) := fun t => by ring
  simp_rw [this]
  ring

theorem iUnion_scales {L : ℝ} (hL : 1 < L) :
    ⋃ j : ℕ, Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2) = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨j, h1, -⟩
    exact lt_of_le_of_lt (lowEnd_nonneg (by linarith) _) h1
  · intro ht
    have hex : ∃ n : ℕ, t ≤ L ^ (n + 1) / 2 := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * t) hL
      refine ⟨n, ?_⟩
      have : L ^ n ≤ L ^ (n + 1) := pow_le_pow_right₀ hL.le (Nat.le_succ n)
      linarith
    classical
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simpa [lowEnd] using ht
    · rw [lowEnd_succ L hpos]
      have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel hpos] at hmin
      exact lt_of_not_ge hmin

theorem disjoint_scales {L : ℝ} (hL : 1 ≤ L) :
    Pairwise (Function.onFun Disjoint fun j : ℕ => Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2)) := by
  have key : ∀ i j : ℕ, i < j →
      Disjoint (Ioc (lowEnd L (i + 1)) (L ^ (i + 1) / 2)) (Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2)) := by
    intro i j hij
    have h1 : L ^ (i + 1) / 2 ≤ lowEnd L (j + 1) := by
      rw [lowEnd_succ L (by omega)]
      have := pow_le_pow_right₀ hL (show i + 1 ≤ j by omega)
      linarith
    exact Set.disjoint_left.2 fun t ht1 ht2 => by linarith [ht1.2, ht2.1]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem hasSum_scales {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) {L : ℝ} (hL : 1 < L) :
    HasSum (fun j : ℕ => ∫ t in Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2), t * (P.P t).eval u)
      (1 / u) := by
  have h := hasSum_integral_iUnion (μ := volume) (f := fun t => t * (P.P t).eval u)
    (fun j : ℕ => measurableSet_Ioc) (disjoint_scales hL.le)
    (by rw [iUnion_scales hL]; exact integrableOn_Ioi P hu le_rfl)
  rwa [iUnion_scales hL, P.integral_eq u hu] at h

/-- `(-Δ^{ℤ^d})^{-1} = ∑_{j ≥ 1} c_j` at `m² = 0`. -/
theorem hasSum_covZ_green (hd : 3 ≤ d) {L : ℝ} (hL : 1 < L) (z : Zd d) :
    HasSum (fun j : ℕ => covZ P d 0 (Set.Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2)) z)
      (greenZd d z) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hc0 : 0 ≤ (2 * Real.pi)⁻¹ ^ d * (2 * (d : ℝ))⁻¹ := by positivity
  have hcov : (fun j : ℕ => covZ P d 0 (Set.Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2)) z) =
      fun j => ∫ k in cube d, (2 * Real.pi)⁻¹ ^ d * (2 * (d : ℝ))⁻¹ *
        ((∫ t in Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2), t * (P.P t).eval (lamR k / (2 * d))) *
          Real.cos (dotZ k z)) :=
    funext fun j => covZ_eq_integral P hd1 _ (lowEnd_nonneg (by linarith) _) z
  have hgreen : greenZd d z =
      ∫ k in cube d, (2 * Real.pi)⁻¹ ^ d * ((lamR k)⁻¹ * Real.cos (dotZ k z)) := by
    rw [greenZd, integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [dotZ, div_eq_inv_mul]
  rw [hcov, hgreen]
  have hI0 : ∀ (j : ℕ) (k : Fin d → ℝ),
      0 ≤ ∫ t in Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2), t * (P.P t).eval (lamR k / (2 * d)) :=
    fun j k => setIntegral_nonneg measurableSet_Ioc fun t ht => by
      have ht0 : 0 < t := lt_of_le_of_lt (lowEnd_nonneg (by linarith) _) ht.1
      exact mul_nonneg ht0.le (P.nonneg t ht0 _ (lamR_div_mem hd1 k))
  have hsum : ∀ k : Fin d → ℝ, k ∈ cube d → (∀ i, k i ≠ 0) →
      HasSum (fun j : ℕ => (2 * Real.pi)⁻¹ ^ d * (2 * (d : ℝ))⁻¹ *
        ∫ t in Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2), t * (P.P t).eval (lamR k / (2 * d)))
        ((2 * Real.pi)⁻¹ ^ d * (lamR k)⁻¹) := by
    intro k hk hk0
    have hl : 0 < lamR k := lamR_pos hk (hk0 ⟨0, by omega⟩)
    have hu : lamR k / (2 * d) ∈ Ioc (0 : ℝ) 2 :=
      ⟨by positivity, (lamR_div_mem hd1 k).2⟩
    convert (hasSum_scales P hu hL).mul_left ((2 * Real.pi)⁻¹ ^ d * (2 * (d : ℝ))⁻¹) using 1
    field_simp
  refine hasSum_integral_of_dominated_convergence
    (fun j k => (2 * Real.pi)⁻¹ ^ d * (2 * (d : ℝ))⁻¹ *
      ∫ t in Ioc (lowEnd L (j + 1)) (L ^ (j + 1) / 2), t * (P.P t).eval (lamR k / (2 * d)))
    ?_ ?_ ?_ ?_ ?_
  · intro j
    refine Measurable.aestronglyMeasurable ?_
    refine measurable_const.mul (Measurable.mul ?_ ?_)
    · exact (measurable_integral_scales P _).comp (continuous_lamR.measurable.div_const _)
    · exact (Real.continuous_cos.comp (continuous_dotZ z)).measurable
  · intro j
    refine Filter.Eventually.of_forall fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg (hI0 j k)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hI0 j k) (Real.abs_cos_le_one _)) hc0
  · filter_upwards [ae_cube_ne_zero] with k ⟨hk, hk0⟩
    exact (hsum k hk hk0).summable
  · refine ((integrable_inv_lamR hd).const_mul ((2 * Real.pi)⁻¹ ^ d)).congr ?_
    filter_upwards [ae_cube_ne_zero] with k ⟨hk, hk0⟩
    exact (hsum k hk hk0).tsum_eq.symm
  · filter_upwards [ae_cube_ne_zero] with k ⟨hk, hk0⟩
    convert (hsum k hk hk0).mul_right (Real.cos (dotZ k z)) using 1
    · funext j; ring
    · ring

end

end FRD
