import PtCorr2.Restart.RestartBulk

/-!
# B3, T6: the restarted product versus the reference product; the relative form (pure layer)

* **`r3_frakN2F_sub_le`**: `|𝔫F_i − 𝔫^{(2)}_i| ≤ (4/3)q·2^{-(i−m)}` (the memory of the scales `< m`;
  the difference form of `frakN2F_mem_le`).
* **`r3_prod_cmp`**: `|a_i − b_i| ≤ e_i`, `|b_i| ≤ 1/8` ⇒
  `∏_{i<j}|1 − a_i| ≤ exp((8/7)∑_{i<j}e_i)·∏_{i<j}|1 − b_i|`.
* `r3_geom_half`: `∑_{i<j}(1/2)^i ≤ 2`.
* **`r3_beta_lower`**: for `β_{i+1} = β_i(1 − n_i) − e_i` with `|e_i| ≤ x_i|β_i(1 − n_i)|`,
  `0 ≤ x_i ≤ 1/2`: `exp(−2∑_{i<j}x_{k+i})|β_k|∏_{i<j}|1 − n_{k+i}| ≤ |β_{k+j}|`.
* `r3_gsq_sum`: `g_i + (β/4)g_i² ≤ g_{i+1}` ⇒ `(β/4)∑_{i<j}g_{k+i}² ≤ g_{k+j} − g_k`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Bulk

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (m : ℕ)
  (o' : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))

/-- **The memory term of the restarted one-loop coefficient** (difference form of
`frakN2F_mem_le`). -/
theorem r3_frakN2F_sub_le (h0 : o'.IsObs) (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) {n : ℕ}
    {Bτ qq : ℝ} (hqq0 : 0 ≤ qq) (hqq4 : qq ≤ 1 / 4)
    (hT : ∀ k j, k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k j‖ ≤ Bτ * qq ^ (j - k) * (t k).1)
    (hBg : ∀ k < n, Bτ * (t k).1 ≤ 1) {i : ℕ} (hmi : m ≤ i) (hin : i < n) :
    ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i -
        frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖ ≤ 4 / 3 * qq * (1 / 2) ^ (i - m) := by
  rw [frakN2F_eq_sub _ _ _ hmi]
  have e1 : frakN2 P (histCovO R t) (histVF2 R P m o' t) i =
      frakN2 P (histCovO R t) (histVO2 R P o₀ t) i := by
    rw [frakN2, frakN2, nuBar2_histVF2_eq R P m o' t h0 o₀ ho₀,
      sum_congr rfl fun k _ => tadInc2_histVF2_eq R P m o' t h0 o₀ ho₀ k i]
  rw [e1, sub_sub_cancel_left, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ k ∈ range m, ‖tadInc2 P (histCovO R t) (histVF2 R P m o' t) k i‖ ≤
      qq ^ (i - m) * qq ^ (m - k) := by
    intro k hk
    have hk' := mem_range.1 hk
    rw [tadInc2_histVF2_eq R P m o' t h0 o₀ ho₀]
    refine (hT k i (by omega) hin).trans ?_
    have hq : 0 ≤ qq ^ (i - k) := pow_nonneg hqq0 _
    have := hBg k (by omega)
    calc Bτ * qq ^ (i - k) * (t k).1 = qq ^ (i - k) * (Bτ * (t k).1) := by ring
      _ ≤ qq ^ (i - k) * 1 := mul_le_mul_of_nonneg_left this hq
      _ = qq ^ (i - m) * qq ^ (m - k) := by rw [mul_one, ← pow_add]; congr 1; omega
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  have h2 := rs_geom_small hqq0 hqq4 m
  have h3 : qq ^ (i - m) ≤ (1 / 2) ^ (i - m) := pow_le_pow_left₀ hqq0 (by linarith) _
  have h4 : 0 ≤ ∑ k ∈ range m, qq ^ (m - k) := sum_nonneg fun _ _ => pow_nonneg hqq0 _
  calc qq ^ (i - m) * ∑ k ∈ range m, qq ^ (m - k) ≤ (1 / 2) ^ (i - m) * (4 / 3 * qq) :=
        mul_le_mul h3 h2 h4 (by positivity)
    _ = 4 / 3 * qq * (1 / 2) ^ (i - m) := by ring

end Bulk

/-- `∑_{i<j}(1/2)^i ≤ 2`. -/
theorem r3_geom_half (j : ℕ) : ∑ i ∈ range j, (1 / 2 : ℝ) ^ i ≤ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : ∑ i ∈ range (j + 1), (1 / 2 : ℝ) ^ i = 1 + 1 / 2 * ∑ i ∈ range j, (1 / 2 : ℝ) ^ i := by
      rw [sum_range_succ', mul_sum]
      simp only [pow_succ, pow_zero]
      rw [add_comm]; congr 1
      exact sum_congr rfl fun i _ => by ring
    rw [e]; linarith

/-- **Comparison of products**: `∏|1 − a_i| ≤ exp((8/7)∑e_i)∏|1 − b_i|`. -/
theorem r3_prod_cmp (a b : ℕ → ℂ) (e : ℕ → ℝ) (j : ℕ)
    (hab : ∀ i < j, ‖a i - b i‖ ≤ e i) (hb : ∀ i < j, ‖b i‖ ≤ 1 / 8) :
    ∏ i ∈ range j, ‖1 - a i‖ ≤
      Real.exp (8 / 7 * ∑ i ∈ range j, e i) * ∏ i ∈ range j, ‖1 - b i‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih' := ih (fun i hi => hab i (by omega)) (fun i hi => hb i (by omega))
    have hbj := hb j (by omega)
    have hej := hab j (by omega)
    have h78 : 7 / 8 ≤ ‖1 - b j‖ := by
      have := norm_sub_norm_le (1 : ℂ) (b j)
      rw [norm_one] at this; linarith
    have hstep : ‖1 - a j‖ ≤ Real.exp (8 / 7 * e j) * ‖1 - b j‖ := by
      have h1 : ‖1 - a j‖ ≤ ‖1 - b j‖ + e j := by
        have := norm_sub_le (1 - b j) (a j - b j)
        rw [show 1 - b j - (a j - b j) = 1 - a j by ring] at this
        linarith
      have he0 : 0 ≤ e j := (norm_nonneg _).trans hej
      have h2 : 1 + 8 / 7 * e j ≤ Real.exp (8 / 7 * e j) := by
        have := Real.add_one_le_exp (8 / 7 * e j); linarith
      have h3 : e j ≤ 8 / 7 * e j * ‖1 - b j‖ := by nlinarith
      nlinarith [norm_nonneg (1 - b j)]
    rw [prod_range_succ, prod_range_succ, sum_range_succ, mul_add, Real.exp_add]
    have hP0 : 0 ≤ ∏ i ∈ range j, ‖1 - a i‖ := prod_nonneg fun _ _ => norm_nonneg _
    calc (∏ i ∈ range j, ‖1 - a i‖) * ‖1 - a j‖
        ≤ (Real.exp (8 / 7 * ∑ i ∈ range j, e i) * ∏ i ∈ range j, ‖1 - b i‖) *
          (Real.exp (8 / 7 * e j) * ‖1 - b j‖) :=
          mul_le_mul ih' hstep (norm_nonneg _)
            ((prod_nonneg fun _ _ => norm_nonneg _).trans ih')
      _ = _ := by ring

/-- `exp(−2x) ≤ 1 − x` for `0 ≤ x ≤ 1/2`. -/
theorem r3_exp_neg_two_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Real.exp (-(2 * x)) ≤ 1 - x := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by have := Real.add_one_le_exp (2 * x); linarith
  have hp : 0 < Real.exp (2 * x) := Real.exp_pos _
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hp]
  have : 1 ≤ (1 + 2 * x) * (1 - x) := by nlinarith
  nlinarith

/-- **The lower bound of a perturbed product flow.** -/
theorem r3_beta_lower (β n e : ℕ → ℂ) (x : ℕ → ℝ) (k nn : ℕ)
    (hflow : ∀ i < nn, β (i + 1) = β i * (1 - n i) - e i)
    (he : ∀ i < nn, ‖e i‖ ≤ x i * ‖β i * (1 - n i)‖) (hx0 : ∀ i < nn, 0 ≤ x i)
    (hx : ∀ i < nn, x i ≤ 1 / 2) :
    ∀ j, k + j ≤ nn → Real.exp (-(2 * ∑ i ∈ range j, x (k + i))) * ‖β k‖ *
      ∏ i ∈ range j, ‖1 - n (k + i)‖ ≤ ‖β (k + j)‖ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have hjn : k + j < nn := by omega
    set y := x (k + j)
    have hstep : (1 - y) * ‖β (k + j) * (1 - n (k + j))‖ ≤ ‖β (k + j + 1)‖ := by
      rw [hflow _ hjn]
      have := norm_sub_norm_le (β (k + j) * (1 - n (k + j))) (e (k + j))
      have := he (k + j) hjn
      linarith
    have hy := r3_exp_neg_two_le (hx0 (k + j) hjn) (hx (k + j) hjn)
    rw [sum_range_succ, mul_add, neg_add, Real.exp_add, prod_range_succ, ← add_assoc]
    rw [norm_mul] at hstep
    calc Real.exp (-(2 * ∑ i ∈ range j, x (k + i))) * Real.exp (-(2 * y)) * ‖β k‖ *
          ((∏ i ∈ range j, ‖1 - n (k + i)‖) * ‖1 - n (k + j)‖)
        = (Real.exp (-(2 * ∑ i ∈ range j, x (k + i))) * ‖β k‖ *
            ∏ i ∈ range j, ‖1 - n (k + i)‖) * (Real.exp (-(2 * y)) * ‖1 - n (k + j)‖) := by ring
      _ ≤ ‖β (k + j)‖ * ((1 - y) * ‖1 - n (k + j)‖) :=
          mul_le_mul ih (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
            (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (norm_nonneg _)
      _ = (1 - y) * (‖β (k + j)‖ * ‖1 - n (k + j)‖) := by ring
      _ ≤ _ := hstep

/-- `g_i + (β/4)g_i² ≤ g_{i+1}` ⇒ `(β/4)∑_{i<j}g_{k+i}² ≤ g_{k+j} − g_k`. -/
theorem r3_gsq_sum (g : ℕ → ℝ) {β : ℝ} (k : ℕ) {n : ℕ}
    (hg : ∀ i < n, g i + β / 4 * g i ^ 2 ≤ g (i + 1)) :
    ∀ j, k + j ≤ n → β / 4 * ∑ i ∈ range j, g (k + i) ^ 2 ≤ g (k + j) - g k := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hg (k + j) (by omega)
    rw [sum_range_succ, mul_add, show k + (j + 1) = k + j + 1 by omega]
    linarith

end

end PtCorr2
