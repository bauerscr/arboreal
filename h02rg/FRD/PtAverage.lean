import FRD.Pt

/-!
# Averaging over dyadic scales

Given a family `P⁰_t` with all the properties of `FRD.PtFamily` except the positivity of the
tails, but vanishing for `t < 1` and bounded below by a constant `A > 0` for `t ∈ [1, 2]`, the
average `P_t = ∑_j w_j 4^{-j} P⁰_{t / 2^j}` (with `w_j = 1/(W j!)`, `∑ w_j = 1`) is a `PtFamily`.
-/

namespace FRD

open MeasureTheory Set Polynomial Filter Topology
open scoped Nat ENNReal

/-- A family with all properties of `PtFamily` except tail positivity, vanishing for `t < 1`
and bounded below by `A > 0` for `t ∈ [1, 2]`. -/
structure PrePtFamily where
  P : ℝ → ℝ[X]
  eq_zero : ∀ t, t < 1 → P t = 0
  natDegree_le : ∀ t, 0 < t → ((P t).natDegree : ℝ) ≤ t
  nonneg : ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2, 0 ≤ (P t).eval u
  A : ℝ
  A_pos : 0 < A
  ge_A : ∀ t ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (0 : ℝ) 2, A ≤ (P t).eval u
  bound : ∀ s : ℝ, 0 ≤ s → ∃ K : ℝ, ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2,
    (P t).eval u ≤ K * (1 + t ^ 2 * u) ^ (-s)
  measurable : ∀ u, Measurable fun t => (P t).eval u
  integral_eq : ∀ u ∈ Ioc (0 : ℝ) 2, ∫ t in Ioi 0, t * (P t).eval u = 1 / u

namespace PrePtFamily

variable (F : PrePtFamily)

/-- Unnormalized weights. -/
noncomputable def w (j : ℕ) : ℝ := 1 / (j ! : ℝ)

lemma w_pos (j : ℕ) : 0 < w j := by unfold w; positivity

lemma summable_w : Summable w := by
  have : w = fun n : ℕ => (1 : ℝ) ^ n / n ! := by funext n; simp [w]
  rw [this]; exact Real.summable_pow_div_factorial 1

/-- The total weight. -/
noncomputable def W : ℝ := ∑' j, w j

lemma W_pos : 0 < W :=
  summable_w.tsum_pos (fun j => (w_pos j).le) 0 (w_pos 0)

/-- The coefficients `a_j = w_j / (W 4^j)`. -/
noncomputable def a (j : ℕ) : ℝ := w j / (W * 4 ^ j)

lemma a_pos (j : ℕ) : 0 < a j := by
  unfold a; have := w_pos j; have := W_pos; positivity

lemma eval_eq_zero_of_lt {t : ℝ} (ht : t < 1) (u : ℝ) : (F.P t).eval u = 0 := by
  rw [F.eq_zero t ht, eval_zero]

lemma eval_nonneg {t u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) : 0 ≤ (F.P t).eval u := by
  rcases lt_or_ge t 1 with h | h
  · rw [F.eval_eq_zero_of_lt h]
  · exact F.nonneg t (by linarith) u hu

/-- The averaged family. -/
noncomputable def avgP (t : ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (⌊t⌋₊ + 1), C (a j) * F.P (t / 2 ^ j)

lemma lt_one_of_floor_lt {t : ℝ} {j : ℕ} (hj : ⌊t⌋₊ + 1 ≤ j) : t / 2 ^ j < 1 := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [div_lt_one h2]
  have h1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have h3 : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
  have h4 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
  push_cast at h3
  linarith

lemma eval_avgP (t u : ℝ) :
    (F.avgP t).eval u = ∑ j ∈ Finset.range (⌊t⌋₊ + 1), a j * (F.P (t / 2 ^ j)).eval u := by
  simp [avgP, eval_finsetSum]

lemma eval_avgP_eq_tsum (t u : ℝ) :
    (F.avgP t).eval u = ∑' j, a j * (F.P (t / 2 ^ j)).eval u := by
  rw [eval_avgP, tsum_eq_sum]
  intro j hj
  rw [Finset.mem_range, not_lt] at hj
  rw [F.eval_eq_zero_of_lt (lt_one_of_floor_lt hj), mul_zero]

lemma natDegree_avgP (t : ℝ) (ht : 0 < t) : ((F.avgP t).natDegree : ℝ) ≤ t := by
  have : (F.avgP t).natDegree ≤ ⌊t⌋₊ := by
    unfold avgP
    apply natDegree_sum_le_of_forall_le
    intro j _
    refine (natDegree_C_mul_le _ _).trans ?_
    apply Nat.le_floor
    refine (F.natDegree_le _ (by positivity)).trans ?_
    exact div_le_self ht.le (one_le_pow₀ (by norm_num))
  exact (Nat.cast_le.mpr this).trans (Nat.floor_le ht.le)

lemma nonneg_avgP (t : ℝ) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2) : 0 ≤ (F.avgP t).eval u := by
  rw [eval_avgP]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (a_pos j).le (F.eval_nonneg hu)

lemma scale_rpow_le {s X : ℝ} (hs : 0 ≤ s) (hX : 0 ≤ X) (j : ℕ) :
    (1 + X / 4 ^ j) ^ (-s) ≤ ((4 : ℝ) ^ s) ^ j * (1 + X) ^ (-s) := by
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have h4' : (0 : ℝ) < 4 ^ j := by positivity
  have hle : (1 + X) * ((4 : ℝ) ^ j)⁻¹ ≤ 1 + X / 4 ^ j := by
    rw [add_mul, one_mul, ← div_eq_mul_inv]
    have : ((4 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h4
    linarith
  have hpos : 0 < (1 + X) * ((4 : ℝ) ^ j)⁻¹ := by positivity
  refine (Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)).trans (le_of_eq ?_)
  rw [Real.mul_rpow (by linarith) (by positivity), Real.inv_rpow h4'.le, Real.rpow_neg h4'.le,
    inv_inv, mul_comm]
  congr 1
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]

lemma bound_avgP (s : ℝ) (hs : 0 ≤ s) : ∃ K : ℝ, ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2,
    (F.avgP t).eval u ≤ K * (1 + t ^ 2 * u) ^ (-s) := by
  obtain ⟨K, hK⟩ := F.bound s hs
  set K' := max K 0
  set r : ℝ := (4 : ℝ) ^ s / 4
  have hsum : Summable fun j : ℕ => r ^ j / j ! := Real.summable_pow_div_factorial r
  refine ⟨K' / W * ∑' j : ℕ, r ^ j / j !, fun t ht u hu => ?_⟩
  have hX : 0 ≤ t ^ 2 * u := mul_nonneg (by positivity) hu.1
  have hterm : ∀ j : ℕ, a j * (F.P (t / 2 ^ j)).eval u ≤
      K' / W * (r ^ j / j !) * (1 + t ^ 2 * u) ^ (-s) := by
    intro j
    have h1 : (F.P (t / 2 ^ j)).eval u ≤ K' * (1 + (t / 2 ^ j) ^ 2 * u) ^ (-s) := by
      refine (hK _ (by positivity) u hu).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by have := hu.1; positivity) _)
    have h2 : (t / 2 ^ j) ^ 2 * u = t ^ 2 * u / 4 ^ j := by
      have : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this]; ring
    rw [h2] at h1
    have h3 := scale_rpow_le hs hX j
    have ha := a_pos j
    have hK' : 0 ≤ K' := le_max_right _ _
    calc a j * (F.P (t / 2 ^ j)).eval u
        ≤ a j * (K' * (((4 : ℝ) ^ s) ^ j * (1 + t ^ 2 * u) ^ (-s))) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = K' / W * (r ^ j / j !) * (1 + t ^ 2 * u) ^ (-s) := by
          simp only [a, w, r, div_pow]
          have := W_pos
          field_simp
  have hsum' : Summable fun j : ℕ => K' / W * (r ^ j / j !) * (1 + t ^ 2 * u) ^ (-s) :=
    (hsum.mul_left _).mul_right _
  rw [eval_avgP]
  calc ∑ j ∈ Finset.range (⌊t⌋₊ + 1), a j * (F.P (t / 2 ^ j)).eval u
      ≤ ∑ j ∈ Finset.range (⌊t⌋₊ + 1), K' / W * (r ^ j / j !) * (1 + t ^ 2 * u) ^ (-s) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ ≤ ∑' j, K' / W * (r ^ j / j !) * (1 + t ^ 2 * u) ^ (-s) := by
        apply hsum'.sum_le_tsum
        intro j _
        have := W_pos
        have : 0 ≤ r := by positivity
        have : 0 ≤ (1 + t ^ 2 * u) ^ (-s) := Real.rpow_nonneg (by linarith) _
        have : 0 ≤ K' := le_max_right _ _
        positivity
    _ = K' / W * (∑' j : ℕ, r ^ j / j !) * (1 + t ^ 2 * u) ^ (-s) := by
        rw [tsum_mul_right, tsum_mul_left]

lemma measurable_avgP (u : ℝ) : Measurable fun t => (F.avgP t).eval u := by
  simp_rw [eval_avgP]
  let G : ℝ × ℕ → ℝ := fun p => ∑ j ∈ Finset.range (p.2 + 1), a j * (F.P (p.1 / 2 ^ j)).eval u
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro N
    simp only [G]
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact ((F.measurable u).comp (measurable_id.div_const _)).const_mul _
  exact hG.comp (measurable_id.prodMk Nat.measurable_floor)

lemma integrable_P {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) :
    IntegrableOn (fun t => t * (F.P t).eval u) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [F.integral_eq u hu]
  exact (one_div_pos.mpr hu.1).ne'

lemma integral_scaled {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) (j : ℕ) :
    ∫ t in Ioi 0, t * (a j * (F.P (t / 2 ^ j)).eval u) = w j / W * (1 / u) := by
  have h2 : (0 : ℝ) < (2 ^ j)⁻¹ := by positivity
  have := integral_comp_mul_left_Ioi (fun s => s * (F.P s).eval u) 0 h2
  simp only [mul_zero] at this
  rw [F.integral_eq u hu] at this
  have e : ∀ t : ℝ, t * (a j * (F.P (t / 2 ^ j)).eval u) =
      (a j * 2 ^ j) * ((2 ^ j)⁻¹ * t * (F.P ((2 ^ j)⁻¹ * t)).eval u) := by
    intro t
    rw [inv_mul_eq_div]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, this, smul_eq_mul, inv_inv]
  simp only [a]
  have := W_pos
  have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  rw [h4]
  field_simp

lemma integral_avgP {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) :
    ∫ t in Ioi 0, t * (F.avgP t).eval u = 1 / u := by
  have hu' : u ∈ Icc (0 : ℝ) 2 := ⟨hu.1.le, hu.2⟩
  simp_rw [eval_avgP_eq_tsum, ← tsum_mul_left]
  have hmeas : ∀ j : ℕ, Measurable fun t => t * (a j * (F.P (t / 2 ^ j)).eval u) := fun j =>
    measurable_id.mul (((F.measurable u).comp (measurable_id.div_const _)).const_mul _)
  have hint : ∀ j : ℕ, IntegrableOn (fun t => t * (a j * (F.P (t / 2 ^ j)).eval u)) (Ioi 0) := by
    intro j
    apply Integrable.of_integral_ne_zero
    rw [F.integral_scaled hu j]
    have := w_pos j; have := W_pos; have := hu.1
    positivity
  rw [integral_tsum (fun j => (hmeas j).aestronglyMeasurable)]
  · simp_rw [F.integral_scaled hu, tsum_mul_right, tsum_div_const]
    change W / W * (1 / u) = 1 / u
    rw [div_self W_pos.ne', one_mul]
  · have : ∀ j : ℕ, ∫⁻ t in Ioi 0, ‖t * (a j * (F.P (t / 2 ^ j)).eval u)‖ₑ =
        ENNReal.ofReal (w j / W * (1 / u)) := by
      intro j
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hint j), ← F.integral_scaled hu j]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg (le_of_lt ht)
        (mul_nonneg (a_pos j).le (F.eval_nonneg hu')))
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro j; have := w_pos j; have := W_pos; have := hu.1; positivity
    · exact (summable_w.div_const _).mul_right _

lemma tail_pos_avgP {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) (T : ℝ) (hT : 0 < T) :
    0 < ∫ t in Ioi T, t * (F.avgP t).eval u := by
  have hu' : u ∈ Icc (0 : ℝ) 2 := ⟨hu.1.le, hu.2⟩
  have hint : IntegrableOn (fun t => t * (F.avgP t).eval u) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [F.integral_avgP hu]
    exact (one_div_pos.mpr hu.1).ne'
  set m : ℕ := ⌈T⌉₊
  have hmT : T < 2 ^ m := by
    have h1 : T ≤ m := Nat.le_ceil T
    have h2 : (m : ℝ) < 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
    linarith
  set I := Ioo ((2 : ℝ) ^ m) (2 ^ (m + 1))
  have hIT : I ⊆ Ioi T := fun t ht => lt_trans hmT ht.1
  have hlow : ∀ t ∈ I, a m * F.A ≤ t * (F.avgP t).eval u := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have htpos : 1 ≤ t := ht1.trans ht.1.le
    have hmem : m ∈ Finset.range (⌊t⌋₊ + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      apply Nat.le_floor
      have h2 : (m : ℝ) < 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
      linarith [ht.1]
    have hsc : t / 2 ^ m ∈ Icc (1 : ℝ) 2 := by
      have h2 : (0 : ℝ) < 2 ^ m := by positivity
      constructor
      · rw [le_div_iff₀ h2]; linarith [ht.1]
      · rw [div_le_iff₀ h2]; have := ht.2; rw [pow_succ] at this; linarith
    have h1 : a m * F.A ≤ (F.avgP t).eval u := by
      rw [eval_avgP]
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun j => a j * (F.P (t / 2 ^ j)).eval u)
        (fun j _ => mul_nonneg (a_pos j).le (F.eval_nonneg hu')) hmem)
      exact mul_le_mul_of_nonneg_left (F.ge_A _ hsc u hu') (a_pos m).le
    have h0 : 0 ≤ (F.avgP t).eval u := F.nonneg_avgP t u hu'
    nlinarith
  calc (0 : ℝ) < ∫ _ in I, a m * F.A := by
        rw [setIntegral_const, smul_eq_mul]
        apply mul_pos
        · have : (0:ℝ) < 2 ^ m := by positivity
          have h2 : (2 : ℝ) ^ (m + 1) = 2 ^ m * 2 := pow_succ _ _
          simp only [I, Measure.real, Real.volume_Ioo]
          rw [ENNReal.toReal_ofReal (by linarith)]
          linarith
        · exact mul_pos (a_pos m) F.A_pos
    _ ≤ ∫ t in I, t * (F.avgP t).eval u := by
        apply setIntegral_mono_on
        · exact integrableOn_const (by simp [I, Real.volume_Ioo])
        · exact hint.mono_set (hIT.trans (Ioi_subset_Ioi hT.le))
        · exact measurableSet_Ioo
        · exact hlow
    _ ≤ ∫ t in Ioi T, t * (F.avgP t).eval u := by
        apply setIntegral_mono_set
        · exact hint.mono_set (Ioi_subset_Ioi hT.le)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (hT.trans ht).le (F.nonneg_avgP t u hu')
        · exact Eventually.of_forall hIT

/-- The averaged family is a `PtFamily`. -/
noncomputable def toPtFamily : PtFamily where
  P := F.avgP
  natDegree_le := F.natDegree_avgP
  nonneg t _ u hu := F.nonneg_avgP t u hu
  bound := F.bound_avgP
  measurable := F.measurable_avgP
  integral_eq _ hu := F.integral_avgP hu
  tail_pos _ hu T hT := F.tail_pos_avgP hu T hT

end PrePtFamily

end FRD
