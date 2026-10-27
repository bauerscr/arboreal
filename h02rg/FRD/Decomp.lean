import FRD.Pt
import FRD.Fourier
import FRD.Dist

/-!
# The finite range decomposition (Section `sec:frd`, Appendix `app:decomp`)

Fix a family `P : PtFamily` (`e:decomp-Pt`), the dimension `d`, the torus `Λ = (ℤ/nℤ)^d` and
`m² ≥ 0`.  With `û(k) = (λ(k) + m²)/(2d + m²)`, a set `S ⊆ (0, ∞)` of scales defines the
covariance `cov P m² S` with Fourier symbol `(2d+m²)^{-1} ∫_S t^2 P_t(û(k)) dt/t`.  Then

* `Cj P m² L j` is `C_j`, with `S = (L^{j-1}/2, L^j/2]` (`S = (0, L/2]` for `j = 1`);
* `CNN P m² L N` is `C_{N,N}`, with `S = (L^{N-1}/2, ∞)`;
* `CN`, `tN`, `QN` are `C_N`, `t_N`, `Q_N` of `e:CNN-def`.

The appendix writes the lower limit of the integrals defining `C_{N,N}`, `C_N`, `t_N` as
`L^N/2`; for `e:C-def` to hold it must be `L^{N-1}/2` (the upper limit of `C_{N-1}`), which is
what we use.
-/

namespace FRD

noncomputable section

open Finset MeasureTheory Set Grassmann

variable (P : PtFamily)

/-! ### Integrability in `t` -/

theorem eval_le_const : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2, (P.P t).eval u ≤ K := by
  obtain ⟨K, hK⟩ := P.bound 0 le_rfl
  refine ⟨max K 0, le_max_right _ _, fun t ht u hu => ?_⟩
  have := hK t ht u hu
  rw [neg_zero, Real.rpow_zero, mul_one] at this
  exact this.trans (le_max_left _ _)

theorem integrableOn_Ioc {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) {a : ℝ} (b : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun t => t * (P.P t).eval u) (Ioc a b) := by
  obtain ⟨K, hK0, hK⟩ := eval_le_const P
  refine Measure.integrableOn_of_bounded (M := |b| * K) (by simp) ?_ ?_
  · exact (measurable_id.mul (P.measurable u)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    have h1 := hK t ht0 u hu
    have h0 := P.nonneg t ht0 u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_pos ht0]
    have : t ≤ |b| := ht.2.trans (le_abs_self b)
    exact mul_le_mul this h1 h0 (abs_nonneg b)

theorem integrableOn_Ioi {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t => t * (P.P t).eval u) (Ioi a) := by
  have hu' : u ∈ Icc (0 : ℝ) 2 := ⟨hu.1.le, hu.2⟩
  have hu0 : 0 < u := hu.1
  obtain ⟨K, hK⟩ := P.bound 2 (by norm_num)
  have hsub : Ioi a ⊆ Ioc 0 (max a 1) ∪ Ioi (max a 1) := by
    intro t ht
    rcases le_or_gt t (max a 1) with h | h
    · exact Or.inl ⟨lt_of_le_of_lt ha ht, h⟩
    · exact Or.inr h
  refine IntegrableOn.mono_set ?_ hsub
  refine (integrableOn_Ioc P hu' _ le_rfl).union ?_
  -- on `(max a 1, ∞)`: `t P_t(u) ≤ K u^{-2} t^{-3}`
  have hint : IntegrableOn (fun t : ℝ => |K| * u⁻¹ ^ 2 * t ^ (-3 : ℝ)) (Ioi (max a 1)) := by
    refine Integrable.const_mul ?_ _
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine hint.mono' ((measurable_id.mul (P.measurable u)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht1 : 1 < t := lt_of_le_of_lt (le_max_right _ _) ht
  have ht0 : 0 < t := one_pos.trans ht1
  have h0 := P.nonneg t ht0 u hu'
  have h1 := hK t ht0 u hu'
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_pos ht0]
  have hpos : 0 < 1 + t ^ 2 * u := by positivity
  have h2 : (1 + t ^ 2 * u) ^ (-(2 : ℝ)) ≤ (t ^ 2 * u) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have h3 : (t ^ 2 * u) ^ (-(2 : ℝ)) = u⁻¹ ^ 2 * t ^ (-4 : ℝ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg ht0.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  calc t * (P.P t).eval u ≤ t * (|K| * (u⁻¹ ^ 2 * t ^ (-4 : ℝ))) := by
        gcongr
        calc (P.P t).eval u ≤ K * (1 + t ^ 2 * u) ^ (-(2 : ℝ)) := h1
          _ ≤ |K| * (t ^ 2 * u) ^ (-(2 : ℝ)) := by
              gcongr
              · exact le_abs_self K
          _ = _ := by rw [h3]
    _ = |K| * u⁻¹ ^ 2 * t ^ (-3 : ℝ) := by
        rw [show (-3 : ℝ) = 1 + (-4) by norm_num, Real.rpow_add ht0, Real.rpow_one]; ring

/-! ### The covariances -/

variable {d n : ℕ} [NeZero n]

/-- `û(k) = (λ(k) + m²)/(2d + m²)`. -/
def uhat (msq : ℝ) (m : Torus d n) : ℝ := (lam m + msq) / (2 * d + msq)

/-- The Fourier symbol `(2d+m²)^{-1} ∫_S t^2 P_t(û(k)) dt/t` of the covariance of the scales `S`. -/
def wt (msq : ℝ) (S : Set ℝ) (m : Torus d n) : ℝ :=
  (2 * d + msq)⁻¹ * ∫ t in S, t * (P.P t).eval (uhat msq m)

/-- The covariance of the scales `S`:
`(x, y) ↦ ((2d+m²)|Λ|)^{-1} ∑_k e^{ik·(x-y)} ∫_S t^2 P_t(û(k)) dt/t`. -/
def cov (msq : ℝ) (S : Set ℝ) : Matrix (Torus d n) (Torus d n) ℝ := fmat (wt P msq S)

/-- The lower end of the scales of `C_j`: `0` for `j ≤ 1`, `L^{j-1}/2` otherwise. -/
def lowEnd (L : ℝ) (j : ℕ) : ℝ := if j ≤ 1 then 0 else L ^ (j - 1) / 2

/-- `C_j`, `1 ≤ j < N`. -/
def Cj (msq L : ℝ) (j : ℕ) : Matrix (Torus d n) (Torus d n) ℝ :=
  cov P msq (Ioc (lowEnd L j) (L ^ j / 2))

/-- `C_{N,N}`. -/
def CNN (msq L : ℝ) (N : ℕ) : Matrix (Torus d n) (Torus d n) ℝ := cov P msq (Ioi (lowEnd L N))

/-- `C_N`: `C_{N,N}` without the zero mode. -/
def CN (msq L : ℝ) (N : ℕ) : Matrix (Torus d n) (Torus d n) ℝ :=
  fmat fun m => if m = 0 then 0 else wt P msq (Ioi (lowEnd L N)) m

/-- `t_N = (2d+m²)^{-1} ∫_{L^{N-1}/2}^∞ t^2 P_t(m²/(2d+m²)) dt/t`. -/
def tN (d : ℕ) (msq L : ℝ) (N : ℕ) : ℝ :=
  (2 * d + msq)⁻¹ * ∫ t in Ioi (lowEnd L N), t * (P.P t).eval (msq / (2 * d + msq))

/-- `Q_N`, the projection onto the zero mode. -/
def QN : Matrix (Torus d n) (Torus d n) ℝ := fun _ _ => ((n : ℝ) ^ d)⁻¹

/-! ### Basic properties of the symbols -/

theorem cosk_le (m : Torus d n) (i : Fin d) : cosk m i ≤ 1 := Real.cos_le_one _
theorem neg_one_le_cosk (m : Torus d n) (i : Fin d) : -1 ≤ cosk m i := Real.neg_one_le_cos _

theorem lam_nonneg (m : Torus d n) : 0 ≤ lam m :=
  sum_nonneg fun i _ => by linarith [cosk_le m i]

theorem lam_le (m : Torus d n) : lam m ≤ 4 * d := by
  calc lam m ≤ ∑ _i : Fin d, (4 : ℝ) :=
        sum_le_sum fun i _ => by linarith [neg_one_le_cosk m i]
    _ = 4 * d := by simp [mul_comm]

theorem uhat_mem {msq : ℝ} (hmsq : 0 ≤ msq) (m : Torus d n) : uhat msq m ∈ Icc (0 : ℝ) 2 := by
  unfold uhat
  rcases (show (0 : ℝ) ≤ 2 * d + msq by positivity).eq_or_lt with h | h
  · rw [← h, div_zero]; exact ⟨le_rfl, by norm_num⟩
  · refine ⟨div_nonneg (by linarith [lam_nonneg m]) h.le, ?_⟩
    rw [div_le_iff₀ h]; linarith [lam_le m]

theorem uhat_mem_Ioc {msq : ℝ} (hmsq : 0 < msq) (m : Torus d n) : uhat msq m ∈ Ioc (0 : ℝ) 2 :=
  ⟨div_pos (by linarith [lam_nonneg m]) (by positivity), (uhat_mem hmsq.le m).2⟩

theorem uhat_even (msq : ℝ) : Even' (uhat (d := d) (n := n) msq) := fun m => by
  simp [uhat, lam_neg]

theorem wt_even (msq : ℝ) (S : Set ℝ) : Even' (wt P (d := d) (n := n) msq S) := fun m => by
  simp [wt, uhat_even msq m]

theorem wt_nonneg {msq : ℝ} (hmsq : 0 ≤ msq) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) (m : Torus d n) : 0 ≤ wt P msq S m := by
  refine mul_nonneg (inv_nonneg.2 (by positivity)) ?_
  refine setIntegral_nonneg hSm fun t ht => ?_
  have ht0 : 0 < t := hS ht
  exact mul_nonneg ht0.le (P.nonneg t ht0 _ (uhat_mem hmsq m))

theorem lowEnd_nonneg {L : ℝ} (hL : 0 ≤ L) (j : ℕ) : 0 ≤ lowEnd L j := by
  unfold lowEnd; split_ifs <;> positivity

/-! ### Positive semidefiniteness -/

theorem cov_posSemidef {msq : ℝ} (hmsq : 0 ≤ msq) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) : (cov P msq S : Matrix (Torus d n) (Torus d n) ℝ).PosSemidef :=
  fmat_posSemidef (wt_nonneg P hmsq hSm hS)

/-- `C_j` is positive semidefinite. -/
theorem Cj_posSemidef {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L) (j : ℕ) :
    (Cj P msq L j : Matrix (Torus d n) (Torus d n) ℝ).PosSemidef :=
  cov_posSemidef P hmsq measurableSet_Ioc fun _ ht =>
    lt_of_le_of_lt (lowEnd_nonneg hL j) ht.1

/-- `C_{N,N}` is positive semidefinite. -/
theorem CNN_posSemidef {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L) (N : ℕ) :
    (CNN P msq L N : Matrix (Torus d n) (Torus d n) ℝ).PosSemidef :=
  cov_posSemidef P hmsq measurableSet_Ioi fun _ ht =>
    lt_of_le_of_lt (lowEnd_nonneg hL N) ht

/-- `C_N` is positive semidefinite. -/
theorem CN_posSemidef {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L) (N : ℕ) :
    (CN P msq L N : Matrix (Torus d n) (Torus d n) ℝ).PosSemidef := by
  refine fmat_posSemidef fun m => ?_
  split_ifs
  · exact le_rfl
  · exact wt_nonneg P hmsq measurableSet_Ioi (fun _ ht => lt_of_le_of_lt (lowEnd_nonneg hL N) ht) m

/-! ### The decomposition `e:C-def` -/

theorem lowEnd_succ (L : ℝ) {j : ℕ} (hj : 1 ≤ j) : lowEnd L (j + 1) = L ^ j / 2 := by
  simp [lowEnd, show ¬ j + 1 ≤ 1 by omega]

theorem lowEnd_le {L : ℝ} (hL : 1 ≤ L) (j : ℕ) : lowEnd L j ≤ L ^ j / 2 := by
  unfold lowEnd
  split_ifs
  · positivity
  · have : L ^ (j - 1) ≤ L ^ j := pow_le_pow_right₀ hL (by omega)
    linarith

/-- The scales of `C_1, …, C_{N-1}, C_{N,N}` exhaust `(0, ∞)`. -/
theorem integral_split {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 2) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Ico 1 N, ∫ t in Ioc (lowEnd L j) (L ^ j / 2), t * (P.P t).eval u) +
      ∫ t in Ioi (lowEnd L N), t * (P.P t).eval u = ∫ t in Ioi 0, t * (P.P t).eval u := by
  induction N, hN using Nat.le_induction with
  | base => simp [lowEnd]
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, add_assoc, lowEnd_succ L hN, ← ih]
    congr 1
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi,
      Ioc_union_Ioi_eq_Ioi (lowEnd_le hL N)]
    · exact integrableOn_Ioc P ⟨hu.1.le, hu.2⟩ _ (lowEnd_nonneg (by linarith) N)
    · exact integrableOn_Ioi P hu (by positivity)

theorem negLap_add_eq (msq : ℝ) :
    (negLap + msq • 1 : Matrix (Torus d n) (Torus d n) ℝ) = fmat fun m => lam m + msq := by
  rw [negLap_eq_fmat, ← fmat_const, fmat_add]

theorem fmat_sum {ι : Type*} (s : Finset ι) (w : ι → Torus d n → ℝ) :
    ∑ i ∈ s, fmat (w i) = fmat fun m => ∑ i ∈ s, w i m := by
  classical
  induction s using Finset.induction_on with
  | empty => ext x y; simp [fmat]
  | insert i s hi ih => rw [sum_insert hi, ih, fmat_add]; simp [sum_insert hi]

/-- The finite range decomposition `e:C-def`:
`(-Δ + m²) (C_1 + ⋯ + C_{N-1} + C_{N,N}) = 1`. -/
theorem decomposition {msq : ℝ} (hmsq : 0 < msq) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    (negLap + msq • 1 : Matrix (Torus d n) (Torus d n) ℝ) *
      (∑ j ∈ Finset.Ico 1 N, Cj P msq L j + CNN P msq L N) = 1 := by
  have hsum : (∑ j ∈ Finset.Ico 1 N, Cj P msq L j + CNN P msq L N : Matrix (Torus d n) _ ℝ) =
      fmat fun m => (lam m + msq)⁻¹ := by
    simp only [Cj, CNN, cov, fmat_sum, fmat_add]
    congr 1; funext m
    simp only [wt, ← Finset.mul_sum, ← mul_add]
    rw [integral_split P (uhat_mem_Ioc hmsq m) hL hN, P.integral_eq _ (uhat_mem_Ioc hmsq m), uhat]
    have h1 : 0 < lam m + msq := by linarith [lam_nonneg m]
    have h2 : (0 : ℝ) < 2 * d + msq := by positivity
    field_simp
  rw [hsum, negLap_add_eq, fmat_mul (fun m => by simp [lam_neg]) (fun m => by simp [lam_neg])]
  convert fmat_one using 2
  funext m
  have h1 : 0 < lam m + msq := by linarith [lam_nonneg m]
  field_simp

/-- `(-Δ + m²)^{-1} = C_1 + ⋯ + C_{N-1} + C_{N,N}`. -/
theorem decomposition_inv {msq : ℝ} (hmsq : 0 < msq) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    (negLap + msq • 1 : Matrix (Torus d n) (Torus d n) ℝ)⁻¹ =
      ∑ j ∈ Finset.Ico 1 N, Cj P msq L j + CNN P msq L N :=
  Matrix.inv_eq_right_inv (decomposition P hmsq hL hN)

/-! ### The finite range property `e:C-range` -/

/-- `A = (-Δ + m²)/(2d + m²) = fmat û`. -/
theorem fmat_uhat (msq : ℝ) :
    (fmat (uhat msq) : Matrix (Torus d n) (Torus d n) ℝ) =
      (2 * d + msq)⁻¹ • (negLap + msq • 1) := by
  rw [negLap_add_eq, fmat_smul]; congr 1; funext m; simp [uhat, div_eq_inv_mul]

theorem negLap_eq_zero {x y : Torus d n} (h : 1 < supNorm (x - y)) :
    (negLap + (msq : ℝ) • 1 : Matrix (Torus d n) (Torus d n) ℝ) x y = 0 := by
  have hxy : x ≠ y := by rintro rfl; rw [sub_self, supNorm_zero] at h; omega
  have he : ∀ e : Dir d, y ≠ x + dirVec e := by
    rintro e rfl
    rw [show x - (x + dirVec e) = -dirVec e by abel, supNorm_neg] at h
    exact absurd (supNorm_dirVec_le e) (by omega)
  simp [negLap, hxy, he]

theorem pow_uhat_eq_zero (msq : ℝ) (k : ℕ) {x y : Torus d n} (h : k < supNorm (x - y)) :
    ((fmat (uhat msq) : Matrix (Torus d n) (Torus d n) ℝ) ^ k) x y = 0 := by
  induction k generalizing x with
  | zero =>
    have hxy : x ≠ y := by rintro rfl; rw [sub_self, supNorm_zero] at h; omega
    simp [hxy]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine sum_eq_zero fun z _ => ?_
    have htri : supNorm (x - y) ≤ supNorm (x - z) + supNorm (z - y) := by
      have := supNorm_add_le (x - z) (z - y)
      rwa [sub_add_sub_cancel] at this
    rcases le_or_gt (supNorm (x - z)) 1 with h1 | h1
    · rw [ih (by omega), mul_zero]
    · rw [fmat_uhat, Matrix.smul_apply, negLap_eq_zero h1, smul_zero, zero_mul]

/-- Polynomials of degree `≤ k` in `A` have range `k`. -/
theorem aeval_uhat_eq_zero (msq : ℝ) (p : Polynomial ℝ) {x y : Torus d n}
    (h : p.natDegree < supNorm (x - y)) :
    (Polynomial.aeval (fmat (uhat msq) : Matrix (Torus d n) (Torus d n) ℝ) p) x y = 0 := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
  refine sum_eq_zero fun i hi => ?_
  rw [Matrix.smul_apply, pow_uhat_eq_zero msq i (by simp at hi; omega), smul_zero]

/-- The covariance of bounded scales as an integral of polynomials of `A`:
`cov x y = (2d+m²)^{-1} ∫_S t (P_t(A))(x, y) dt`. -/
theorem cov_apply_Ioc {msq : ℝ} (hmsq : 0 ≤ msq) {a : ℝ} (b : ℝ) (ha : 0 ≤ a) (x y : Torus d n) :
    cov P msq (Ioc a b) x y = (2 * d + msq)⁻¹ * ∫ t in Ioc a b,
      t * (Polynomial.aeval (fmat (uhat msq) : Matrix (Torus d n) (Torus d n) ℝ) (P.P t)) x y := by
  simp only [aeval_fmat (uhat_even msq), cov, fmat, wt]
  have h1 : ∀ t, (2 * (d : ℝ) + msq)⁻¹ * (t * (((n : ℝ) ^ d)⁻¹ *
      ∑ m : Torus d n, (P.P t).eval (uhat msq m) * (char m (x - y)).re)) =
      ∑ m : Torus d n, (((n : ℝ) ^ d)⁻¹ * (2 * (d : ℝ) + msq)⁻¹ * (char m (x - y)).re) *
        (t * (P.P t).eval (uhat msq m)) := by
    intro t
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun m _ => by ring
  rw [← integral_const_mul, integral_congr_ae (Filter.Eventually.of_forall h1)]
  rw [integral_finset_sum _ fun m _ => (integrableOn_Ioc P (uhat_mem hmsq m) b ha).const_mul _,
    Finset.mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_const_mul]; ring

/-- The finite range property `e:C-range`: `C_j(x, y) = 0` if `|x - y|_∞ ≥ L^j/2`. -/
theorem Cj_finiteRange {msq : ℝ} (hmsq : 0 ≤ msq) {L : ℝ} (hL : 1 ≤ L) (j : ℕ) {x y : Torus d n}
    (h : L ^ j / 2 ≤ supNorm (x - y)) : Cj P msq L j x y = 0 := by
  rw [Cj, cov_apply_Ioc P hmsq _ (lowEnd_nonneg (by linarith) j), integral_Ioc_eq_integral_Ioo]
  refine mul_eq_zero_of_right _ (setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_)
  have ht0 : 0 < t := lt_of_le_of_lt (lowEnd_nonneg (by linarith) j) ht.1
  have hdeg := P.natDegree_le t ht0
  rw [aeval_uhat_eq_zero msq _ (by exact_mod_cast (hdeg.trans_lt (ht.2.trans_le h))), mul_zero]

/-! ### Translation invariance -/

theorem fmat_translate (w : Torus d n → ℝ) (x y a : Torus d n) :
    fmat w (x + a) (y + a) = fmat w x y := by
  simp only [fmat, add_sub_add_right_eq_sub]

/-- `C_j(x + a, y + a) = C_j(x, y)`. -/
theorem Cj_translate (msq L : ℝ) (j : ℕ) (x y a : Torus d n) :
    Cj P msq L j (x + a) (y + a) = Cj P msq L j x y := fmat_translate _ x y a

/-! ### The zero mode `e:CNN-def` and `t_N` (`e:tN`) -/

theorem lam_zero : lam (0 : Torus d n) = 0 := by
  simp [lam, cosk, co_zero]

theorem fmat_delta (c : ℝ) :
    (fmat (fun m => if m = 0 then c else 0) : Matrix (Torus d n) (Torus d n) ℝ) = c • QN := by
  ext x y
  simp [fmat, QN, char_zero_left, mul_comm]

/-- `e:CNN-def`: `C_{N,N} = C_N + t_N Q_N`. -/
theorem CNN_eq (msq L : ℝ) (N : ℕ) :
    (CNN P msq L N : Matrix (Torus d n) (Torus d n) ℝ) = CN P msq L N + tN P d msq L N • QN := by
  have : wt P msq (Ioi (lowEnd L N)) (0 : Torus d n) = tN P d msq L N := by
    simp [wt, tN, uhat, lam_zero]
  rw [← this, ← fmat_delta, CN, fmat_add, CNN, cov]
  congr 1; funext m
  split_ifs with h
  · subst h; simp
  · simp

theorem uhat_zero (msq : ℝ) : uhat msq (0 : Torus d n) = msq / (2 * d + msq) := by
  simp [uhat, lam_zero]

/-- `t_N > 0`. -/
theorem tN_pos {msq : ℝ} (hmsq : 0 < msq) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) : 0 < tN P d msq L N := by
  have hu : msq / (2 * d + msq) ∈ Ioc (0 : ℝ) 2 := by
    rw [← uhat_zero (n := 1)]; exact uhat_mem_Ioc hmsq 0
  refine mul_pos (inv_pos.2 (by positivity)) ?_
  rcases (lowEnd_nonneg hL N).eq_or_lt with h | h
  · rw [← h, P.integral_eq _ hu]; exact one_div_pos.2 hu.1
  · exact P.tail_pos _ hu _ h

/-- `e:tN`: `0 ≤ 1/m² - t_N ≤ K L^{2N}` (for `d ≥ 1`), with `K` independent of `m²`, `L`, `N`. -/
theorem tN_sub_inv {d : ℕ} (hd : 1 ≤ d) : ∃ K : ℝ, ∀ msq : ℝ, 0 < msq → ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
    0 ≤ 1 / msq - tN P d msq L N ∧ 1 / msq - tN P d msq L N ≤ K * L ^ (2 * N) := by
  obtain ⟨K, hK0, hK⟩ := eval_le_const P
  refine ⟨K / 16, fun msq hmsq L hL N => ?_⟩
  set u := msq / (2 * d + msq)
  have hc : (0 : ℝ) < 2 * d + msq := by positivity
  have hu : u ∈ Ioc (0 : ℝ) 2 := by
    rw [show u = uhat (d := d) (n := 1) msq 0 from (uhat_zero msq).symm]; exact uhat_mem_Ioc hmsq 0
  set a := lowEnd L N
  have ha : 0 ≤ a := lowEnd_nonneg (by linarith) N
  have hsplit : ∫ t in Ioi 0, t * (P.P t).eval u =
      (∫ t in Ioc 0 a, t * (P.P t).eval u) + ∫ t in Ioi a, t * (P.P t).eval u := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_Ioc P ⟨hu.1.le, hu.2⟩ a le_rfl) (integrableOn_Ioi P hu ha),
      Ioc_union_Ioi_eq_Ioi ha]
  have hinv : 1 / msq = (2 * d + msq)⁻¹ * ∫ t in Ioi 0, t * (P.P t).eval u := by
    rw [P.integral_eq _ hu]; simp only [u]; field_simp
  have hdiff : 1 / msq - tN P d msq L N = (2 * d + msq)⁻¹ * ∫ t in Ioc 0 a, t * (P.P t).eval u := by
    rw [hinv, hsplit, tN]; ring
  have hnn : 0 ≤ ∫ t in Ioc 0 a, t * (P.P t).eval u :=
    setIntegral_nonneg measurableSet_Ioc fun t ht => mul_nonneg ht.1.le (P.nonneg t ht.1 u ⟨hu.1.le, hu.2⟩)
  have hle : ∫ t in Ioc 0 a, t * (P.P t).eval u ≤ K * a ^ 2 / 2 := by
    calc ∫ t in Ioc 0 a, t * (P.P t).eval u ≤ ∫ t in Ioc 0 a, K * t := by
          refine setIntegral_mono_on (integrableOn_Ioc P ⟨hu.1.le, hu.2⟩ a le_rfl)
            ((continuous_const.mul continuous_id).integrableOn_Ioc) measurableSet_Ioc
            fun t ht => ?_
          rw [mul_comm K]
          exact mul_le_mul_of_nonneg_left (hK t ht.1 u ⟨hu.1.le, hu.2⟩) ht.1.le
      _ = K * a ^ 2 / 2 := by
          rw [← intervalIntegral.integral_of_le ha, intervalIntegral.integral_const_mul,
            integral_id]; ring
  refine ⟨hdiff ▸ mul_nonneg (inv_nonneg.2 hc.le) hnn, ?_⟩
  rw [hdiff]
  have ha2 : a ^ 2 ≤ L ^ (2 * N) / 4 := by
    have h1 : a ≤ L ^ N / 2 := lowEnd_le hL N
    calc a ^ 2 ≤ (L ^ N / 2) ^ 2 := pow_le_pow_left₀ ha h1 2
      _ = L ^ (2 * N) / 4 := by rw [pow_mul']; ring
  have hc2 : (2 * d + msq)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; refine one_div_le_one_div_of_le (by norm_num) ?_
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc (2 * d + msq)⁻¹ * ∫ t in Ioc 0 a, t * (P.P t).eval u
      ≤ 1 / 2 * (K * (L ^ (2 * N) / 4) / 2) := by
        refine mul_le_mul hc2 (hle.trans ?_) hnn (by norm_num)
        gcongr
    _ = K / 16 * L ^ (2 * N) := by ring

end

end FRD
