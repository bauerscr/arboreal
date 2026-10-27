import FRD.Decomp

/-!
# Continuity in `m²`

The covariances `C_j` (`j < N`) and `C_N` are continuous functions of `m² ≥ 0` (including the
endpoint `m² = 0`), and `C_{N,N}`, `t_N` are continuous for `m² > 0` (Section `sec:frd`,
`sec:finvol`).
-/

namespace FRD

noncomputable section

open Finset MeasureTheory Set Grassmann Filter Topology

variable (P : PtFamily)

/-- `t (1 + c t²)^{-2}` is integrable on `(0, ∞)` for `c > 0`. -/
theorem integrableOn_decay {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t * (1 + t ^ 2 * c) ^ (-(2 : ℝ))) (Ioi 0) := by
  have hsub : Ioi (0 : ℝ) ⊆ Ioc 0 1 ∪ Ioi 1 := by
    intro t ht; rcases le_or_gt t 1 with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsub
  · refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
    · exact (Measurable.aestronglyMeasurable (by fun_prop))
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      have h1 : (1 + t ^ 2 * c) ^ (-(2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [ht.1]) (by norm_num)
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity)]
      calc t * (1 + t ^ 2 * c) ^ (-(2 : ℝ)) ≤ 1 * 1 :=
            mul_le_mul ht.2 h1 (by positivity) zero_le_one
        _ = 1 := one_mul 1
  · have hint : IntegrableOn (fun t : ℝ => c⁻¹ ^ 2 * t ^ (-3 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    refine hint.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := one_pos.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : (1 + t ^ 2 * c) ^ (-(2 : ℝ)) ≤ (t ^ 2 * c) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have h3 : t * (t ^ 2 * c) ^ (-(2 : ℝ)) = c⁻¹ ^ 2 * t ^ (-3 : ℝ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg ht0.le,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, Real.rpow_natCast]
      field_simp
    calc t * (1 + t ^ 2 * c) ^ (-(2 : ℝ)) ≤ t * (t ^ 2 * c) ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 ht0.le
      _ = _ := h3

/-- Continuity of `x ↦ ∫_S t P_t(g x) dt` by dominated convergence. -/
theorem continuousOn_integral {X : Set ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g X)
    (hgX : ∀ x ∈ X, g x ∈ Icc (0 : ℝ) 2) {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ Ioi 0)
    {B : ℝ → ℝ} (hB : IntegrableOn B S) (hbound : ∀ x ∈ X, ∀ t ∈ S, t * (P.P t).eval (g x) ≤ B t) :
    ContinuousOn (fun x => ∫ t in S, t * (P.P t).eval (g x)) X := by
  refine continuousOn_of_dominated (bound := B) (fun x _ => ?_) (fun x hx => ?_) hB ?_
  · exact (measurable_id.mul (P.measurable _)).aestronglyMeasurable
  · refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := hS ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0.le (P.nonneg t ht0 _ (hgX x hx)))]
    exact hbound x hx t ht
  · exact Eventually.of_forall fun t =>
      continuousOn_const.mul ((Polynomial.continuous_aeval (P.P t)).comp_continuousOn hg)

variable {d n : ℕ} [NeZero n]

theorem continuousOn_uhat {X : Set ℝ} (hX : ∀ x ∈ X, 0 ≤ x) (hd : 1 ≤ d) (m : Torus d n) :
    ContinuousOn (fun msq => uhat msq m) X := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith [hX x hx]

theorem continuousOn_fmat {X : Set ℝ} {w : ℝ → Torus d n → ℝ}
    (hw : ∀ m, ContinuousOn (fun x => w x m) X) (x y : Torus d n) :
    ContinuousOn (fun msq => fmat (w msq) x y) X := by
  simp only [fmat]
  exact continuousOn_const.mul (continuousOn_finsetSum _ fun m _ => (hw m).mul continuousOn_const)

theorem continuousOn_inv_two_d {X : Set ℝ} (hX : ∀ x ∈ X, 0 ≤ x) (hd : 1 ≤ d) :
    ContinuousOn (fun msq : ℝ => (2 * (d : ℝ) + msq)⁻¹) X := by
  refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith [hX x hx]

/-- `C_j` is continuous in `m² ≥ 0`, including `m² = 0`. -/
theorem Cj_continuousOn (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (j : ℕ) (x y : Torus d n) :
    ContinuousOn (fun msq => Cj P msq L j x y) (Ici 0) := by
  obtain ⟨K, hK0, hK⟩ := eval_le_const P
  refine continuousOn_fmat (fun m => ?_) x y
  refine (continuousOn_inv_two_d (fun x hx => hx) hd).mul ?_
  refine continuousOn_integral P (continuousOn_uhat (fun x hx => hx) hd m)
    (fun x hx => uhat_mem hx m) measurableSet_Ioc
    (fun t ht => lt_of_le_of_lt (lowEnd_nonneg hL j) ht.1) (B := fun _ => |L ^ j / 2| * K)
    (integrableOn_const (by simp)) fun msq hmsq t ht => ?_
  have ht0 : 0 < t := lt_of_le_of_lt (lowEnd_nonneg hL j) ht.1
  exact mul_le_mul (ht.2.trans (le_abs_self _)) (hK t ht0 _ (uhat_mem hmsq m))
    (P.nonneg t ht0 _ (uhat_mem hmsq m)) (abs_nonneg _)

/-- Dominated convergence on the unbounded scales when `û ≥ c > 0`. -/
theorem continuousOn_integral_Ioi {X : Set ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g X)
    (hgX : ∀ x ∈ X, g x ∈ Icc (0 : ℝ) 2) {c : ℝ} (hc : 0 < c) (hgc : ∀ x ∈ X, c ≤ g x)
    {a : ℝ} (ha : 0 ≤ a) : ContinuousOn (fun x => ∫ t in Ioi a, t * (P.P t).eval (g x)) X := by
  obtain ⟨K, hK⟩ := P.bound 2 (by norm_num)
  refine continuousOn_integral P hg hgX measurableSet_Ioi (fun t ht => lt_of_le_of_lt ha ht)
    (B := fun t => |K| * (t * (1 + t ^ 2 * c) ^ (-(2 : ℝ))))
    (((integrableOn_decay hc).mono_set (Ioi_subset_Ioi ha)).const_mul _) fun x hx t ht => ?_
  have ht0 : 0 < t := lt_of_le_of_lt ha ht
  have h1 := hK t ht0 _ (hgX x hx)
  have h2 : (1 + t ^ 2 * g x) ^ (-(2 : ℝ)) ≤ (1 + t ^ 2 * c) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr; exact hgc x hx) (by norm_num)
  calc t * (P.P t).eval (g x) ≤ t * (|K| * (1 + t ^ 2 * c) ^ (-(2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) ht0.le
        exact mul_le_mul (le_abs_self K) h2
          (Real.rpow_nonneg (by nlinarith [(hgX x hx).1, sq_nonneg t]) _) (abs_nonneg K)
    _ = _ := by ring

theorem continuousOn_of_Icc {f : ℝ → ℝ} (h : ∀ M, 0 < M → ContinuousOn f (Icc 0 M)) :
    ContinuousOn f (Ici 0) := by
  intro x hx
  have := h (x + 1) (by linarith [mem_Ici.1 hx])
  refine (this x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.2 ⟨Iio (x + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, hy.1.le⟩⟩

theorem continuousOn_of_Icc_pos {f : ℝ → ℝ} (h : ∀ δ M, 0 < δ → δ < M → ContinuousOn f (Icc δ M)) :
    ContinuousOn f (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  have := h (x / 2) (x + 1) (by linarith) (by linarith)
  refine (this x ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.2 ⟨Ioo (x / 2) (x + 1), isOpen_Ioo, ⟨by linarith, by linarith⟩,
    fun y hy => ⟨hy.1.1.le, hy.1.2.le⟩⟩

theorem lam_pos {m : Torus d n} (hm : m ≠ 0) : 0 < lam m := by
  obtain ⟨i, hi⟩ : ∃ i, co m i ≠ 0 := by
    by_contra h; push Not at h; exact hm (funext h)
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hv : 0 < (co m i).val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).2 hi)
  have hvn : ((co m i).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hlt : cosk m i < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
    have h0 := (Real.cos_eq_one_iff_of_lt_of_lt (x := 2 * Real.pi * (co m i).val / n)
      (by have : 0 < 2 * Real.pi * (co m i).val / n := by positivity
          linarith [Real.pi_pos]) ?_).1 h
    · have : 0 < 2 * Real.pi * (co m i).val / n := by positivity
      linarith
    · rw [div_lt_iff₀ hn]; nlinarith [Real.pi_pos]
  refine Finset.sum_pos' (fun j _ => by linarith [cosk_le m j]) ⟨i, mem_univ i, by linarith⟩

/-- `C_N` is continuous in `m² ≥ 0`, including `m² = 0`. -/
theorem CN_continuousOn (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (x y : Torus d n) :
    ContinuousOn (fun msq => CN P msq L N x y) (Ici 0) := by
  refine continuousOn_of_Icc fun M hM => ?_
  refine continuousOn_fmat (fun m => ?_) x y
  split_ifs with hm
  · exact continuousOn_const
  · refine (continuousOn_inv_two_d (fun x hx => hx.1) hd).mul ?_
    have hdpos : (0 : ℝ) < 2 * d + M := by have : (0 : ℝ) ≤ d := d.cast_nonneg; linarith
    refine continuousOn_integral_Ioi P (continuousOn_uhat (fun x hx => hx.1) hd m)
      (fun x hx => uhat_mem hx.1 m) (div_pos (lam_pos hm) hdpos) (fun x hx => ?_)
      (lowEnd_nonneg hL N)
    unfold uhat
    have h1 : 0 < 2 * (d : ℝ) + x := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith [hx.1]
    rw [div_le_div_iff₀ hdpos h1]
    nlinarith [hx.1, hx.2, lam_nonneg m]

/-- `t_N` is a continuous function of `m² > 0`. -/
theorem tN_continuousOn (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    ContinuousOn (fun msq => tN P d msq L N) (Ioi 0) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine continuousOn_of_Icc_pos fun δ M hδ hδM => ?_
  refine (continuousOn_inv_two_d (fun x hx => hδ.le.trans hx.1) hd).mul ?_
  have hdpos : (0 : ℝ) < 2 * d + M := by linarith
  refine continuousOn_integral_Ioi P (g := fun msq => msq / (2 * d + msq))
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => by linarith [hx.1])
    (fun x hx => ?_) (div_pos hδ hdpos) (fun x hx => ?_) (lowEnd_nonneg hL N)
  · have h1 : 0 < 2 * (d : ℝ) + x := by linarith [hx.1]
    refine ⟨div_nonneg (by linarith [hx.1]) h1.le, ?_⟩
    rw [div_le_iff₀ h1]; linarith [hx.1]
  · have h1 : 0 < 2 * (d : ℝ) + x := by linarith [hx.1]
    rw [div_le_div_iff₀ hdpos h1]
    nlinarith [hx.1, hx.2]

end

end FRD
