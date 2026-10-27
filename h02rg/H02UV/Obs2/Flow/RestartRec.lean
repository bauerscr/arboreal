import Obs2.Flow.RelRec

/-!
# The restart recursion: the relative recursion with a transient initial activity (B3, T4)

`RelRec` (`Obs2/Flow/RelRec`) starts from `𝒲_0 = K_0 = 0`, `D_0 = 0` and bounds everything by the
coupling `b_j = |β_j| > 0`. For the restart of the one-point flow at an intermediate scale `m`
(shift–relocate–restart, Log "B3") the datum at `m` has a coupling `b_0` which may be much
smaller than its activity, so the sizes are measured by an **envelope** instead:

  `M_j = M₀ ∏_{k<j} a_k` (`rkEnv`), `a_k = |1 − 𝔫_k|`,

with `M₀ > 0` a free parameter dominating the datum: `b_0 + D_0 ≤ M₀`, `𝒲_0 ≤ c_W r_0·2s_0M₀`,
`K_0 ≤ k₀` with the a priori `8k₀ ≤ (c_k − 60B)r_0²c_W·2s_0M₀` (so `k₀` may be `O(c_k r_0²)`
relative to `s_0M₀`, i.e. **not** `r²`-small when `c_k ≫ B`). The extra source `X_j ≤ x_h 2^{-j}M₀`
carries the initial `𝒲` (its tadpoles against the later covariances).

`RelRecK`: the inputs (as `RelIn`, with `dg = 0`, a general `c_k ≥ 60B` in the `K` step), the
transient data, and the flow relations **with the upper coupling bound**
`b_{j+1} ≤ a_jb_j + E_j` (from the exact flow `β_{j+1} = β_j(1 − 𝔫_j) − ∑err_j`).

**`RelRecK.close`**: with `c_t = c_K k₀/(s_0M₀) + x_h + t_n ≤ 1/48`, `ρ = 3/4`, for `j ≤ n`:

* `b_j ≤ (b_0/M₀ + c_δ∑_{k<j}r_k² + (7/3)c_t∑_{k<j}ρ^k) M_j`,
* `D_j ≤ (D_0/M₀ + 2c_δ∑_{k<j}r_k² + (14/3)c_t∑_{k<j}ρ^k) M_j`,
* `‖𝒲_j‖ ≤ c_W r_j·2s_jM_j`, `K_j ≤ 2^{-j}k₀ + 15c_WB r_j²s_jM_j` (the transient decays),
* `E_j ≤ (c_δr_j²a_j + 2c_tρ^j) M_j` (`j < n`).

**`RelRecK.restart_le`** (the restart estimate, linear in the datum):
`b_j ≤ (b_0 + (1/8 + 10c_t)M₀) ∏_{k<j} a_k`, i.e.
`|β_j| ≤ (|β_0| + c_δ(∑r²)M₀ + 10(c_Kk₀/s_0 + (x_h + t_n)M₀)) ∏_{k<j}|1 − 𝔫_k|`.

The one-loop coefficients may carry a transient, `nn_i ≤ c_g r_i + t_n 2^{-i}` (the memory of
the scales before the restart in the restarted coefficient `𝔫F`); `c_t = c_Kk₀/(s_0M₀) + x_h +
t_n`.
-/

open Finset

namespace Obs2

/-! ### The envelope and geometric sums -/

/-- The envelope `M_j = M₀ ∏_{k<j} a_k`. -/
def rkEnv (M₀ : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ := M₀ * ∏ k ∈ range j, a k

theorem rkEnv_zero (M₀ : ℝ) (a : ℕ → ℝ) : rkEnv M₀ a 0 = M₀ := by simp [rkEnv]

theorem rkEnv_succ (M₀ : ℝ) (a : ℕ → ℝ) (j : ℕ) : rkEnv M₀ a (j + 1) = a j * rkEnv M₀ a j := by
  unfold rkEnv; rw [prod_range_succ]; ring

theorem rkEnv_pos {M₀ : ℝ} {a : ℕ → ℝ} (hM : 0 < M₀) :
    ∀ j, (∀ k < j, 0 < a k) → 0 < rkEnv M₀ a j := by
  intro j hj
  unfold rkEnv
  exact mul_pos hM (prod_pos fun k hk => hj k (mem_range.1 hk))

theorem rkEnv_le {M₀ : ℝ} {a : ℕ → ℝ} (hM : 0 < M₀) {j : ℕ} (ha : ∀ k < j, 6 / 7 ≤ a k) :
    ∀ i ≤ j, rkEnv M₀ a i ≤ (7 / 6) ^ (j - i) * rkEnv M₀ a j := by
  refine le_pow_mul_of_step (by norm_num) fun l hl => ?_
  rw [rkEnv_succ]
  have h0 := rkEnv_pos hM l fun k hk => lt_of_lt_of_le (by norm_num) (ha k (by omega))
  have := ha l hl
  nlinarith

/-- `∑_{k ≤ i < j} (14/9)^{j-i} ≤ (14/5)((14/9)^{j-k} − 1)`. -/
theorem rk_geom_Ico {k : ℕ} : ∀ j, k ≤ j →
    ∑ i ∈ Ico k j, (14 / 9 : ℝ) ^ (j - i) ≤ 14 / 5 * ((14 / 9 : ℝ) ^ (j - k) - 1) := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hkj ih =>
    rw [sum_Ico_succ_top hkj, Nat.add_sub_cancel_left, pow_one]
    have e : ∑ i ∈ Ico k j, (14 / 9 : ℝ) ^ (j + 1 - i) =
        (14 / 9) * ∑ i ∈ Ico k j, (14 / 9 : ℝ) ^ (j - i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := (mem_Ico.1 hi).2
      rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]; ring
    rw [e, show j + 1 - k = (j - k) + 1 by omega, pow_succ]
    have := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 14 / 9)
    linarith

/-- `∑_{k<j} y^{j-k} ≤ 2/3` for `0 ≤ y ≤ 2/5`. -/
theorem rk_geom_tail {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 2 / 5) :
    ∀ j : ℕ, ∑ k ∈ range j, y ^ (j - k) ≤ 2 / 3 := by
  intro j
  induction j with
  | zero => simp only [range_zero, sum_empty]; norm_num
  | succ j ih =>
    have e : ∑ k ∈ range (j + 1), y ^ (j + 1 - k) = y * (∑ k ∈ range j, y ^ (j - k) + 1) := by
      rw [sum_range_succ, Nat.add_sub_cancel_left, pow_one, mul_add, mul_sum, mul_one]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      have hk' := mem_range.1 hk
      rw [show j + 1 - k = (j - k) + 1 by omega, pow_succ]; ring
    rw [e]
    have h1 : ∑ k ∈ range j, y ^ (j - k) + 1 ≤ 5 / 3 := by linarith
    have h2 : 0 ≤ ∑ k ∈ range j, y ^ (j - k) + 1 := by
      have : 0 ≤ ∑ k ∈ range j, y ^ (j - k) := sum_nonneg fun _ _ => pow_nonneg hy0 _
      linarith
    have := mul_le_mul hy h1 h2 (by norm_num)
    linarith

/-- `∑_{i<j} (3/4)^i ≤ 4`. -/
theorem rk_geom_rho (j : ℕ) : ∑ i ∈ range j, (3 / 4 : ℝ) ^ i ≤ 4 := by
  have h := geom_sum_eq (show (3 / 4 : ℝ) ≠ 1 by norm_num) j
  rw [h]
  have : 0 ≤ (3 / 4 : ℝ) ^ j := by positivity
  have e : ((3 / 4 : ℝ) ^ j - 1) / (3 / 4 - 1) = 4 * (1 - (3 / 4 : ℝ) ^ j) := by ring
  rw [e]; linarith

/-- **The memory (drift) sum**: summands `≤ Y(14/9)^{j-i}`, tadpoles `≤ B_τq^{j-k}`, `q ≤ 1/4`. -/
theorem rk_drift {j : ℕ} {f : ℕ → ℝ} {T : ℕ → ℝ} {Y Bτ q : ℝ} (hY : 0 ≤ Y) (hBτ : 0 ≤ Bτ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) (hf : ∀ i < j, f i ≤ Y * (14 / 9) ^ (j - i))
    (hT : ∀ k < j, 0 ≤ T k ∧ T k ≤ Bτ * q ^ (j - k)) :
    ∑ k ∈ range j, T k * ∑ i ∈ Ico k j, f i ≤ 2 * Bτ * Y := by
  have h1 : ∀ k ∈ range j, T k * ∑ i ∈ Ico k j, f i ≤
      14 / 5 * Bτ * Y * (14 / 9 * q) ^ (j - k) := by
    intro k hk
    have hkj := mem_range.1 hk
    obtain ⟨hT0, hT1⟩ := hT k hkj
    have hs : ∑ i ∈ Ico k j, f i ≤ Y * (14 / 5 * (14 / 9 : ℝ) ^ (j - k)) := by
      refine (sum_le_sum fun i hi => hf i (mem_Ico.1 hi).2).trans ?_
      rw [← mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hY
      have := rk_geom_Ico j hkj.le
      linarith
    have hs0 : 0 ≤ Y * (14 / 5 * (14 / 9 : ℝ) ^ (j - k)) := by positivity
    calc T k * ∑ i ∈ Ico k j, f i ≤ T k * (Y * (14 / 5 * (14 / 9 : ℝ) ^ (j - k))) :=
          mul_le_mul_of_nonneg_left hs hT0
      _ ≤ Bτ * q ^ (j - k) * (Y * (14 / 5 * (14 / 9 : ℝ) ^ (j - k))) :=
          mul_le_mul_of_nonneg_right hT1 hs0
      _ = 14 / 5 * Bτ * Y * (14 / 9 * q) ^ (j - k) := by rw [mul_pow]; ring
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  have hg := rk_geom_tail (y := 14 / 9 * q) (by positivity) (by linarith) j
  have h0 : 0 ≤ 14 / 5 * Bτ * Y := by positivity
  have := mul_le_mul_of_nonneg_left hg h0
  linarith

/-! ### The recursion -/

/-- **The inputs of the restart recursion** (as `RelIn`, `dg = 0`, `K` step with a general
`c_k`, the transient datum `M₀`, `k₀`, `x_h`). -/
structure RelInK (n : ℕ) (b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (Wb Kb : ℕ → ℝ → Prop) (C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn : ℝ) : Prop where
  hC₁ : 0 ≤ C₁
  hcW1 : 1 ≤ cW
  hcWC : 3 * C₁ ≤ cW
  hBk : 0 ≤ Bk
  hck : 60 * Bk ≤ ck
  hcK : 0 ≤ cK
  hcP : 0 ≤ cP
  hcg : 0 ≤ cg
  hBτ : 0 ≤ Bτ
  hq0 : 0 ≤ q
  hq : q ≤ 1 / 4
  hcδ0 : 0 ≤ cδ
  /-- the choice of `c_δ` -/
  hcδ : 16 * cK * cW * Bk + 3 * cP * cW + 4 * Bτ * cg * (1 + cg) +
    4 * Bτ * cg * cδ * rb ≤ 6 / 7 * cδ
  /-- the memory of the transient -/
  hτ : 2 * Bτ * cg * rb ≤ 1 / 2
  /-- summability of the relative errors -/
  hsum : cδ * ∑ k ∈ range n, r k ^ 2 ≤ 1 / 8
  hr0 : ∀ j ≤ n, 0 ≤ r j
  hrb : ∀ j ≤ n, r j ≤ rb
  hrm : ∀ j < n, r j ≤ r (j + 1)
  hs : ∀ j ≤ n, 0 < s j
  hss : ∀ j < n, s j ≤ 6 / 5 * s (j + 1)
  ha : ∀ j < n, 6 / 7 ≤ a j ∧ a j ≤ 2
  /-- the datum -/
  hM0 : 0 < M₀
  hk₀ : 0 ≤ k₀
  hxh : 0 ≤ xh
  htn : 0 ≤ tn
  hct : cK * k₀ / (s 0 * M₀) + xh + tn ≤ 1 / 48
  hbD0 : b 0 + D 0 ≤ M₀
  hWm : ∀ j x y, Wb j x → x ≤ y → Wb j y
  hKm : ∀ j x y, Kb j x → x ≤ y → Kb j y
  hW0 : Wb 0 (cW * r 0 * (2 * s 0 * M₀))
  hK0 : Kb 0 k₀
  h8 : 8 * k₀ ≤ (ck - 60 * Bk) * r 0 ^ 2 * (cW * (2 * s 0 * M₀))
  hθW : ∀ j < n, θW j ≤ 1 / 6
  hθK : ∀ j < n, θK j ≤ 1 / 16
  /-- the `𝒲^{obs}` step -/
  hW : ∀ j < n, ∀ m w, 0 ≤ m → 0 ≤ w → s j * A j ≤ m → Wb j w →
    Wb (j + 1) (θW j * w + C₁ * r j * m)
  /-- the `K^{obs}` step (a priori `8k ≤ c_k r² m`) -/
  hK : ∀ j < n, ∀ m k, 0 < m → 0 ≤ k → s j * A j ≤ m → Wb j (r j * m) → Kb j k →
    8 * k ≤ ck * r j ^ 2 * m → Kb (j + 1) (θK j * (8 * k) + Bk * r j ^ 2 * m)
  /-- the activity term of `E_j` -/
  hKt : ∀ j < n, ∀ k, 0 ≤ k → Kb j k → Kt j ≤ cK * k / s j
  /-- the product parts of `E_j` -/
  hPr : ∀ j < n, ∀ m : ℕ → ℝ, (∀ i ≤ j, 0 ≤ m i ∧ s i * A i ≤ m i ∧ Wb i (r i * m i)) →
    Pr j ≤ cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * m i / s i)
  /-- the source of the initial `𝒲` -/
  hX : ∀ j < n, X j ≤ xh * (1 / 2) ^ j * M₀
  hT : ∀ k j, k < j → j < n → 0 ≤ T k j ∧ T k j ≤ Bτ * q ^ (j - k)
  hG : ∀ i < n, 0 ≤ G i ∧ G i ≤ cg * r i
  /-- the one-loop coefficient, with a transient (the memory of the scales before the restart) -/
  hnn : ∀ i < n, 0 ≤ nn i ∧ nn i ≤ cg * r i + tn * (1 / 2) ^ i

/-- **The restart recursion**: `RelInK` and the flow relations with the upper coupling bound. -/
structure RelRecK (n : ℕ) (b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (Wb Kb : ℕ → ℝ → Prop) (C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn : ℝ) : Prop
    extends RelInK n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ
      M₀ k₀ xh tn where
  hb : ∀ j ≤ n, 0 ≤ b j
  hD0' : ∀ j ≤ n, 0 ≤ D j
  hA0 : ∀ j ≤ n, 0 ≤ A j
  hE0 : ∀ j < n, 0 ≤ E j
  hDstep : ∀ j < n, D (j + 1) ≤ a j * D j + 2 * E j
  hbup : ∀ j < n, b (j + 1) ≤ a j * b j + E j
  hA : ∀ j ≤ n, A j ≤ b j + D j
  /-- the split of `E_j` -/
  hE : ∀ j < n, E j ≤ Kt j + ∑ k ∈ range j, T k j *
    ∑ i ∈ Ico k j, G i * (nn i * A i + E i) + Pr j + X j

namespace RelRecK

variable {n : ℕ} {b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ} {T : ℕ → ℕ → ℝ}
  {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn : ℝ}
  (H : RelRecK n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn)
include H

theorem sum_le {j : ℕ} (hj : j ≤ n) : cδ * ∑ k ∈ range j, r k ^ 2 ≤ 1 / 8 := by
  have h : ∑ k ∈ range j, r k ^ 2 ≤ ∑ k ∈ range n, r k ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj) fun k _ _ => sq_nonneg _
  exact (mul_le_mul_of_nonneg_left h H.hcδ0).trans H.hsum

theorem env_pos {j : ℕ} (hj : j ≤ n) : 0 < rkEnv M₀ a j :=
  rkEnv_pos H.hM0 j fun k hk => lt_of_lt_of_le (by norm_num) (H.ha k (by omega)).1

theorem env_le {j : ℕ} (hj : j ≤ n) : ∀ i ≤ j, rkEnv M₀ a i ≤ (7 / 6) ^ (j - i) * rkEnv M₀ a j :=
  rkEnv_le H.hM0 fun k hk => (H.ha k (by omega)).1

theorem s_le {j : ℕ} (hj : j ≤ n) : ∀ i ≤ j, s i ≤ (6 / 5) ^ (j - i) * s j :=
  le_pow_mul_of_step (by norm_num) fun l hl => H.hss l (by omega)

theorem r_mono {j : ℕ} (hj : j ≤ n) : ∀ i ≤ j, r i ≤ r j := by
  have := le_pow_mul_of_step (x := r) (by norm_num : (0 : ℝ) ≤ 1)
    (j := j) (fun l hl => by rw [one_mul]; exact H.hrm l (by omega))
  intro i hi; simpa using this i hi

/-- `s_0M₀ ≤ 2^j s_jM_j`. -/
theorem sM_le {j : ℕ} (hj : j ≤ n) : s 0 * M₀ ≤ 2 ^ j * (s j * rkEnv M₀ a j) := by
  have h1 := H.s_le hj 0 (Nat.zero_le _)
  have h2 := H.env_le hj 0 (Nat.zero_le _)
  rw [rkEnv_zero, Nat.sub_zero] at h2
  rw [Nat.sub_zero] at h1
  have hs0 := H.hs 0 (Nat.zero_le _)
  have hM := H.hM0
  have hsj := H.hs j hj
  have hMj := H.env_pos hj
  have h3 : s 0 * M₀ ≤ ((6 / 5) ^ j * s j) * ((7 / 6) ^ j * rkEnv M₀ a j) :=
    mul_le_mul h1 h2 hM.le (by positivity)
  have h4 : ((6 / 5 : ℝ) ^ j * s j) * ((7 / 6) ^ j * rkEnv M₀ a j) =
      (7 / 5 : ℝ) ^ j * (s j * rkEnv M₀ a j) := by
    rw [show (7 / 5 : ℝ) = 6 / 5 * (7 / 6) by norm_num, mul_pow]; ring
  have h5 : (7 / 5 : ℝ) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have h6 := mul_le_mul_of_nonneg_right h5 (mul_pos hsj hMj).le
  linarith

/-- The transient of the activity term, relative to the envelope. -/
theorem kt_tr_le {j : ℕ} (hj : j ≤ n) :
    cK * ((1 / 2) ^ j * k₀) / s j ≤
      cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * rkEnv M₀ a j := by
  have h1 := H.s_le hj 0 (Nat.zero_le _)
  have h2 := H.env_le hj 0 (Nat.zero_le _)
  rw [rkEnv_zero, Nat.sub_zero] at h2
  rw [Nat.sub_zero] at h1
  have hs0 := H.hs 0 (Nat.zero_le _)
  have hM := H.hM0
  have hsj := H.hs j hj
  have hMj := H.env_pos hj
  have hcK := H.hcK
  have hk := H.hk₀
  -- `1/s_j ≤ (6/5)^j/s_0`, `M₀ ≤ (7/6)^j M_j`
  have e1 : cK * ((1 / 2) ^ j * k₀) / s j = cK * k₀ * (1 / 2) ^ j * (s j)⁻¹ := by ring
  have hsi : (s j)⁻¹ ≤ (6 / 5) ^ j * (s 0)⁻¹ := by
    have h6 : (0 : ℝ) < (6 / 5) ^ j := by positivity
    have e : (s j)⁻¹ = (6 / 5) ^ j * ((6 / 5) ^ j * s j)⁻¹ := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left (inv_anti₀ hs0 h1) h6.le
  have hM1 : 1 ≤ (7 / 6) ^ j * rkEnv M₀ a j / M₀ := by rw [le_div_iff₀ hM]; linarith
  have hA : 0 ≤ cK * k₀ * (1 / 2) ^ j := by positivity
  calc cK * ((1 / 2) ^ j * k₀) / s j = cK * k₀ * (1 / 2) ^ j * (s j)⁻¹ := e1
    _ ≤ cK * k₀ * (1 / 2) ^ j * ((6 / 5) ^ j * (s 0)⁻¹) := mul_le_mul_of_nonneg_left hsi hA
    _ ≤ cK * k₀ * (1 / 2) ^ j * ((6 / 5) ^ j * (s 0)⁻¹) *
          ((7 / 6) ^ j * rkEnv M₀ a j / M₀) :=
        le_mul_of_one_le_right (by positivity) hM1
    _ = cK * k₀ / (s 0 * M₀) * (7 / 10) ^ j * rkEnv M₀ a j := by
        rw [show (7 / 10 : ℝ) = 1 / 2 * (6 / 5) * (7 / 6) by norm_num, mul_pow, mul_pow]
        field_simp
    _ ≤ cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * rkEnv M₀ a j := by
        have h7 : (7 / 10 : ℝ) ^ j ≤ (3 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
        have h8 : 0 ≤ cK * k₀ / (s 0 * M₀) := by positivity
        have := mul_le_mul_of_nonneg_left h7 h8
        exact mul_le_mul_of_nonneg_right this hMj.le

/-- The initial-`𝒲` source, relative to the envelope. -/
theorem x_le {j : ℕ} (hj : j < n) : X j ≤ xh * (3 / 4) ^ j * rkEnv M₀ a j := by
  have h2 := H.env_le hj.le 0 (Nat.zero_le _)
  rw [rkEnv_zero, Nat.sub_zero] at h2
  have hxh := H.hxh
  have hMj := H.env_pos hj.le
  refine (H.hX j hj).trans ?_
  calc xh * (1 / 2) ^ j * M₀ ≤ xh * (1 / 2) ^ j * ((7 / 6) ^ j * rkEnv M₀ a j) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = xh * (7 / 12) ^ j * rkEnv M₀ a j := by
        rw [show (7 / 12 : ℝ) = 1 / 2 * (7 / 6) by norm_num, mul_pow]; ring
    _ ≤ xh * (3 / 4) ^ j * rkEnv M₀ a j := by
        have h7 : (7 / 12 : ℝ) ^ j ≤ (3 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
        have := mul_le_mul_of_nonneg_left h7 hxh
        exact mul_le_mul_of_nonneg_right this hMj.le

/-- **The error at step `j`** (steady part `c_δr_j²a_jM_j`, transient `2c_tρ^jM_j`). -/
theorem E_le {j : ℕ} (hj : j < n) (hAi : ∀ i ≤ j, A i ≤ 2 * rkEnv M₀ a i)
    (hEi : ∀ i < j, E i ≤ (cδ * r i ^ 2 * a i +
      2 * (cK * k₀ / (s 0 * M₀) + xh + tn) * (3 / 4) ^ i) * rkEnv M₀ a i)
    (hKj : Kb j ((1 / 2) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * rkEnv M₀ a j)))
    (hWi : ∀ i ≤ j, Wb i (cW * r i * (2 * s i * rkEnv M₀ a i))) :
    E j ≤ (cδ * r j ^ 2 * a j +
      2 * (cK * k₀ / (s 0 * M₀) + xh + tn) * (3 / 4) ^ j) * rkEnv M₀ a j := by
  set M := rkEnv M₀ a with hMdef
  set ct := cK * k₀ / (s 0 * M₀) + xh + tn with hct
  have hMj := H.env_pos hj.le
  have hsj := H.hs j hj.le
  have hrj := H.hr0 j hj.le
  have hcW0 : 0 ≤ cW := by linarith [H.hcW1]
  have hcg := H.hcg
  have hcδ0 := H.hcδ0
  have hBk := H.hBk
  have hcK := H.hcK
  have hrb0 : 0 ≤ rb := hrj.trans (H.hrb j hj.le)
  have hct0 : 0 ≤ ct := by
    have := H.hk₀; have := H.hxh; have := H.htn; have := H.hs 0 (Nat.zero_le _); have := H.hM0
    positivity
  have hri := H.r_mono hj.le
  have hMi := H.env_le hj.le
  -- the activity term
  have hKt : Kt j ≤ 16 * cK * cW * Bk * r j ^ 2 * M j + cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * M j := by
    have h := H.hKt j hj _ (by have := H.hk₀; positivity) hKj
    have h2 := H.kt_tr_le hj.le
    have e : cK * ((1 / 2) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * M j)) / s j =
        cK * ((1 / 2) ^ j * k₀) / s j + 15 * cK * cW * Bk * r j ^ 2 * M j := by
      field_simp
    have : 0 ≤ cK * cW * Bk * r j ^ 2 * M j := by positivity
    linarith
  -- the drift: steady and transient summands
  set Xs := 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * M j with hXs
  have hXs0 : 0 ≤ Xs := by positivity
  have htn := H.htn
  set Xt := cg * rb * (2 * (ct + tn)) * (3 / 4) ^ j * M j with hXt
  have hXt0 : 0 ≤ Xt := by positivity
  have hterm : ∀ i < j, G i * (nn i * A i + E i) ≤ (Xs + Xt) * (14 / 9) ^ (j - i) := by
    intro i hij
    have hin : i < n := by omega
    have hMi' : M i ≤ (4 / 3) ^ (j - i) * M j := by
      refine (hMi i hij.le).trans (mul_le_mul_of_nonneg_right ?_ hMj.le)
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hMi0 : 0 < M i := H.env_pos (by omega)
    have hri' := hri i hij.le
    have hr0i := H.hr0 i hin.le
    have hrbi := H.hrb i hin.le
    obtain ⟨hG0, hG1⟩ := H.hG i hin
    obtain ⟨hnn0, hnn1⟩ := H.hnn i hin
    obtain ⟨ha1, ha2⟩ := H.ha i hin
    set Pm := (4 / 3 : ℝ) ^ (j - i) * M j with hPm
    have hPm0 : 0 ≤ Pm := by positivity
    have hAi' : A i ≤ 2 * Pm := (hAi i hij.le).trans (by linarith)
    have hGi : G i ≤ cg * r j := hG1.trans (mul_le_mul_of_nonneg_left hri' hcg)
    -- steady part of `E_i`
    have hE1 : cδ * r i ^ 2 * a i * M i ≤ cδ * (rb * r j) * (2 * Pm) := by
      have h1 : r i ^ 2 ≤ rb * r j := by rw [sq]; exact mul_le_mul hrbi hri' hr0i hrb0
      have h2 : a i * M i ≤ 2 * Pm := mul_le_mul ha2 hMi' hMi0.le (by norm_num)
      have e : cδ * r i ^ 2 * a i * M i = (cδ * r i ^ 2) * (a i * M i) := by ring
      rw [e]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hcδ0) h2
        (mul_nonneg (by linarith) hMi0.le) (by positivity)
    -- transient part of `E_i`
    have h1ρ : (3 / 4 : ℝ) ^ i * M i ≤ (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
        have e : (3 / 4 : ℝ) ^ j * (14 / 9) ^ (j - i) = (3 / 4) ^ i * (7 / 6) ^ (j - i) := by
          have hji : (3 / 4 : ℝ) ^ j = (3 / 4) ^ i * (3 / 4) ^ (j - i) := by
            rw [← pow_add]; congr 1; omega
          rw [hji, mul_assoc, ← mul_pow]; norm_num
        rw [← mul_assoc, e, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hMi i hij.le) (by positivity)
    have hE2 : 2 * ct * (3 / 4) ^ i * M i ≤ 2 * ct * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
      have := mul_le_mul_of_nonneg_left h1ρ (by positivity : (0 : ℝ) ≤ 2 * ct)
      linarith
    have hE3 : 2 * tn * (3 / 4) ^ i * M i ≤ 2 * tn * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
      have := mul_le_mul_of_nonneg_left h1ρ (by positivity : (0 : ℝ) ≤ 2 * tn)
      linarith
    have hEi' := hEi i hij
    have hEsplit : E i ≤ cδ * (rb * r j) * (2 * Pm) +
        2 * ct * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
      have e : (cδ * r i ^ 2 * a i + 2 * ct * (3 / 4) ^ i) * M i =
          cδ * r i ^ 2 * a i * M i + 2 * ct * (3 / 4) ^ i * M i := by ring
      linarith
    have t2 : nn i * A i ≤ cg * r j * (2 * Pm) + 2 * tn * (3 / 4) ^ i * M i := by
      have hA0i := H.hA0 _ hin.le
      have h1 : nn i * A i ≤ (cg * r i + tn * (1 / 2) ^ i) * A i :=
        mul_le_mul_of_nonneg_right hnn1 hA0i
      have h2 : cg * r i * A i ≤ cg * r j * (2 * Pm) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hri' hcg) hAi' hA0i (by positivity)
      have h3 : tn * (1 / 2) ^ i * A i ≤ tn * (1 / 2) ^ i * (2 * M i) :=
        mul_le_mul_of_nonneg_left (hAi i hij.le) (by positivity)
      have h4 : (1 / 2 : ℝ) ^ i ≤ (3 / 4) ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
      have h5 : tn * (1 / 2) ^ i * (2 * M i) ≤ 2 * tn * (3 / 4) ^ i * M i := by
        have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * tn * M i)
        linarith
      linarith [show (cg * r i + tn * (1 / 2) ^ i) * A i = cg * r i * A i +
        tn * (1 / 2) ^ i * A i by ring]
    have hsum0 : 0 ≤ nn i * A i + E i := add_nonneg (mul_nonneg hnn0 (H.hA0 _ hin.le)) (H.hE0 i hin)
    have t3 : G i * (nn i * A i + E i) ≤ cg * r j * (cg * r j * (2 * Pm) +
        (cδ * (rb * r j) * (2 * Pm) +
          2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j))) :=
      mul_le_mul hGi (by linarith) hsum0 (by positivity)
    have hP43 : Pm ≤ (14 / 9) ^ (j - i) * M j := by
      refine mul_le_mul_of_nonneg_right ?_ hMj.le
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hrj' : cg * r j * (2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j)) ≤
        Xt * (14 / 9) ^ (j - i) := by
      have h1 : cg * r j ≤ cg * rb := mul_le_mul_of_nonneg_left (H.hrb j hj.le) hcg
      have h2 : 0 ≤ 2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by positivity
      have := mul_le_mul_of_nonneg_right h1 h2
      rw [hXt]
      linarith [show cg * rb * (2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j)) =
        cg * rb * (2 * (ct + tn)) * (3 / 4) ^ j * M j * (14 / 9) ^ (j - i) by ring]
    have hst : cg * r j * (cg * r j * (2 * Pm) + cδ * (rb * r j) * (2 * Pm)) ≤
        Xs * (14 / 9) ^ (j - i) := by
      have e : cg * r j * (cg * r j * (2 * Pm) + cδ * (rb * r j) * (2 * Pm)) =
          2 * cg * (cg + cδ * rb) * r j ^ 2 * Pm := by ring
      rw [e, hXs]
      have h1 : 2 * cg * (cg + cδ * rb) * r j ^ 2 * Pm ≤
          2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * Pm := by
        have : 0 ≤ 2 * cg * r j ^ 2 * Pm := by positivity
        have e1 : 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * Pm =
            2 * cg * (cg + cδ * rb) * r j ^ 2 * Pm + 2 * cg * r j ^ 2 * Pm := by ring
        linarith
      have h2 : 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * Pm ≤
          2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * ((14 / 9) ^ (j - i) * M j) :=
        mul_le_mul_of_nonneg_left hP43 (by positivity)
      linarith [show 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * ((14 / 9) ^ (j - i) * M j) =
        2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * M j * (14 / 9) ^ (j - i) by ring]
    have e : cg * r j * (cg * r j * (2 * Pm) +
        (cδ * (rb * r j) * (2 * Pm) + 2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j))) =
        cg * r j * (cg * r j * (2 * Pm) + cδ * (rb * r j) * (2 * Pm)) +
          cg * r j * (2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j)) := by ring
    rw [e] at t3
    linarith [show (Xs + Xt) * (14 / 9) ^ (j - i) = Xs * (14 / 9) ^ (j - i) +
      Xt * (14 / 9) ^ (j - i) by ring]
  have hdrift := rk_drift (f := fun i => G i * (nn i * A i + E i)) (T := fun k => T k j)
    (add_nonneg hXs0 hXt0) H.hBτ H.hq0 H.hq hterm fun k hk => H.hT k j hk hj
  -- the product parts
  have hprod : Pr j ≤ 3 * cP * cW * r j ^ 2 * M j := by
    have h := H.hPr j hj (fun i => cW * (2 * s i * M i)) fun i hi => by
      have hsi := H.hs i (by omega)
      have hMi0 := H.env_pos (j := i) (by omega)
      refine ⟨by positivity, ?_, H.hWm i _ _ (hWi i hi) (le_of_eq (by ring))⟩
      have h1 : s i * A i ≤ s i * (2 * M i) := mul_le_mul_of_nonneg_left (hAi i hi) hsi.le
      have h2 : 2 * s i * M i ≤ cW * (2 * s i * M i) :=
        le_mul_of_one_le_left (by positivity) H.hcW1
      linarith [show s i * (2 * M i) = 2 * s i * M i by ring]
    refine h.trans ?_
    have h1 : ∀ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (cW * (2 * s i * M i)) / s i) ≤
        2 * cW * r j ^ 2 * M j * (4 / 3 * q) ^ (j - i) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
      have hsi := H.hs i (by omega)
      have hr2 : r i ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ (H.hr0 i (by omega)) (hri i hij) 2
      have hMi' : M i ≤ (4 / 3) ^ (j - i) * M j := by
        refine (hMi i hij).trans (mul_le_mul_of_nonneg_right ?_ hMj.le)
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have e : r i ^ 2 * (cW * (2 * s i * M i)) / s i = r i ^ 2 * (2 * cW * M i) := by
        field_simp
      rw [e]
      have hMi0 := H.env_pos (j := i) (by omega)
      have h2 : r i ^ 2 * (2 * cW * M i) ≤ r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * M j)) :=
        mul_le_mul hr2 (mul_le_mul_of_nonneg_left hMi' (by positivity)) (by positivity)
          (sq_nonneg _)
      calc _ ≤ q ^ (j - i) * (r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * M j))) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg H.hq0 _)
        _ = _ := by rw [mul_pow]; ring
    have h2 := sum_le_sum h1
    rw [← mul_sum] at h2
    have hg := geom_tail_le' (y := 4 / 3 * q) (by have := H.hq0; positivity)
      (by have := H.hq; linarith) j
    have h3 : 0 ≤ 2 * cW * r j ^ 2 * M j := by positivity
    have h4 := mul_le_mul_of_nonneg_left hg h3
    have h5 := mul_le_mul_of_nonneg_left (h2.trans h4) H.hcP
    linarith
  have hXj := H.x_le hj
  have hE := H.hE j hj
  -- the steady and transient totals
  have hτ := H.hτ
  have hBτ := H.hBτ
  have hdt : 2 * Bτ * Xt ≤ (ct + tn) * (3 / 4) ^ j * M j := by
    rw [hXt]
    have h1 : 0 ≤ (ct + tn) * (3 / 4) ^ j * M j := by positivity
    have e : 2 * Bτ * (cg * rb * (2 * (ct + tn)) * (3 / 4) ^ j * M j) =
        (2 * Bτ * cg * rb) * (2 * ((ct + tn) * (3 / 4) ^ j * M j)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hτ
      (by positivity : (0 : ℝ) ≤ 2 * ((ct + tn) * (3 / 4) ^ j * M j))
    linarith
  have hsteady : 16 * cK * cW * Bk * r j ^ 2 * M j + 2 * Bτ * Xs + 3 * cP * cW * r j ^ 2 * M j ≤
      cδ * r j ^ 2 * a j * M j := by
    have e : 16 * cK * cW * Bk * r j ^ 2 * M j + 2 * Bτ * Xs + 3 * cP * cW * r j ^ 2 * M j =
        (16 * cK * cW * Bk + 3 * cP * cW + 4 * Bτ * cg * (1 + cg) +
          4 * Bτ * cg * cδ * rb) * (r j ^ 2 * M j) := by rw [hXs]; ring
    rw [e]
    have hrM : 0 ≤ r j ^ 2 * M j := by positivity
    have h6 := mul_le_mul_of_nonneg_right H.hcδ hrM
    have h7 : 6 / 7 * cδ * (r j ^ 2 * M j) ≤ cδ * r j ^ 2 * a j * M j := by
      have := mul_le_mul_of_nonneg_left (H.ha j hj).1 (mul_nonneg hcδ0 hrM)
      linarith
    linarith
  have hct' : cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * M j + (ct + tn) * (3 / 4) ^ j * M j +
      xh * (3 / 4) ^ j * M j = 2 * ct * (3 / 4) ^ j * M j := by rw [hct]; ring
  have hfin : E j ≤ cδ * r j ^ 2 * a j * M j + 2 * ct * (3 / 4) ^ j * M j := by
    have e2 : 2 * Bτ * (Xs + Xt) = 2 * Bτ * Xs + 2 * Bτ * Xt := by ring
    linarith
  linarith [show (cδ * r j ^ 2 * a j + 2 * ct * (3 / 4) ^ j) * M j =
    cδ * r j ^ 2 * a j * M j + 2 * ct * (3 / 4) ^ j * M j by ring]

/-- The bounds at scale `j` of the induction. -/
def Base (_H : RelRecK n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ
    M₀ k₀ xh tn) (j : ℕ) : Prop :=
  b j ≤ (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * rkEnv M₀ a j ∧
    D j ≤ (D 0 / M₀ + 2 * (cδ * ∑ k ∈ range j, r k ^ 2) +
      14 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * rkEnv M₀ a j ∧
    Wb j (cW * r j * (2 * s j * rkEnv M₀ a j)) ∧
    Kb j ((1 / 2) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * rkEnv M₀ a j))

omit H in
theorem base_A {bj Dj Aj b0 D0 M₀' S T' ct Mj : ℝ} (hM : 0 < M₀') (hMj : 0 < Mj)
    (hb : bj ≤ (b0 / M₀' + S + 7 / 3 * ct * T') * Mj)
    (hD : Dj ≤ (D0 / M₀' + 2 * S + 14 / 3 * ct * T') * Mj) (hA : Aj ≤ bj + Dj)
    (hbD : b0 + D0 ≤ M₀') (hS : S ≤ 1 / 8) (hT0 : 0 ≤ T') (hT : T' ≤ 4) (_hct0 : 0 ≤ ct)
    (hct : ct ≤ 1 / 48) :
    Aj ≤ 2 * Mj := by
  have h1 : (b0 + D0) / M₀' ≤ 1 := by rw [div_le_one hM]; exact hbD
  have h2 : ct * T' ≤ 1 / 48 * 4 := mul_le_mul hct hT hT0 (by norm_num)
  have e : (b0 / M₀' + S + 7 / 3 * ct * T') * Mj + (D0 / M₀' + 2 * S + 14 / 3 * ct * T') * Mj =
      ((b0 + D0) / M₀' + 3 * S + 7 * ct * T') * Mj := by rw [add_div]; ring
  have h3 : (b0 + D0) / M₀' + 3 * S + 7 * ct * T' ≤ 2 := by linarith
  have := mul_le_mul_of_nonneg_right h3 hMj.le
  linarith

set_option maxHeartbeats 1000000 in
/-- **The restart recursion closes.** -/
theorem close : ∀ j ≤ n, (∀ i ≤ j, H.Base i) ∧
    (∀ i < j, E i ≤ (cδ * r i ^ 2 * a i +
      2 * (cK * k₀ / (s 0 * M₀) + xh + tn) * (3 / 4) ^ i) * rkEnv M₀ a i) := by
  have hcW : 1 ≤ cW := H.hcW1
  have hcW0 : 0 ≤ cW := by linarith
  have hBk := H.hBk
  have hM := H.hM0
  have hs0 := H.hs 0 (Nat.zero_le _)
  set ct := cK * k₀ / (s 0 * M₀) + xh + tn with hct
  have hct0 : 0 ≤ ct := by
    have := H.hk₀; have := H.hxh; have := H.htn; have := H.hcK; positivity
  have hctb : ct ≤ 1 / 48 := H.hct
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    obtain rfl : i = 0 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rkEnv_zero]; simp only [range_zero, sum_empty, mul_zero, add_zero]
      rw [div_mul_cancel₀ _ hM.ne']
    · rw [rkEnv_zero]; simp only [range_zero, sum_empty, mul_zero, add_zero]
      rw [div_mul_cancel₀ _ hM.ne']
    · rw [rkEnv_zero]; exact H.hW0
    · rw [rkEnv_zero]
      refine H.hKm 0 _ _ H.hK0 ?_
      have := H.hr0 0 (Nat.zero_le _); have := H.hk₀
      simp only [pow_zero, one_mul]
      have : 0 ≤ 15 * cW * Bk * r 0 ^ 2 * (s 0 * M₀) := by positivity
      linarith
  | succ j ih =>
    intro hj1
    have hj : j < n := by omega
    obtain ⟨hB, hEs⟩ := ih hj.le
    have hMj := H.env_pos hj.le
    have hMj1 := H.env_pos hj1
    have hsj := H.hs j hj.le
    have hrj := H.hr0 j hj.le
    have hAi : ∀ i ≤ j, A i ≤ 2 * rkEnv M₀ a i := by
      intro i hi
      obtain ⟨hbi, hDi, -, -⟩ := hB i hi
      exact base_A hM (H.env_pos (by omega)) hbi hDi (H.hA i (by omega)) H.hbD0
        (H.sum_le (by omega)) (sum_nonneg fun _ _ => by positivity) (rk_geom_rho i) hct0 hctb
    obtain ⟨hbj, hDj, hWj, hKj⟩ := hB j le_rfl
    have hEj := H.E_le hj hAi hEs hKj fun i hi => (hB i hi).2.2.1
    have hEs' : ∀ i < j + 1, E i ≤ (cδ * r i ^ 2 * a i + 2 * ct * (3 / 4) ^ i) * rkEnv M₀ a i := by
      intro i hi
      rcases Nat.lt_or_ge i j with h | h
      · exact hEs i h
      · obtain rfl : i = j := by omega
        exact hEj
    refine ⟨fun i hi => ?_, hEs'⟩
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact hB i (by omega)
    obtain rfl : i = j + 1 := by omega
    obtain ⟨ha1, ha2⟩ := H.ha j hj
    have hMs : rkEnv M₀ a (j + 1) = a j * rkEnv M₀ a j := rkEnv_succ M₀ a j
    -- `E_j ≤ (c_δ r_j² + (7/3) c_t ρ^j) M_{j+1}`
    have hErel : E j ≤ (cδ * r j ^ 2 + 7 / 3 * ct * (3 / 4) ^ j) * rkEnv M₀ a (j + 1) := by
      refine hEj.trans ?_
      rw [hMs]
      have h0 : 0 ≤ ct * (3 / 4) ^ j * rkEnv M₀ a j := by positivity
      have := mul_le_mul_of_nonneg_left ha1 h0
      linarith
    have hsr : ∑ k ∈ range (j + 1), r k ^ 2 = ∑ k ∈ range j, r k ^ 2 + r j ^ 2 := sum_range_succ _ _
    have hsρ : ∑ k ∈ range (j + 1), (3 / 4 : ℝ) ^ k = ∑ k ∈ range j, (3 / 4 : ℝ) ^ k + (3 / 4) ^ j :=
      sum_range_succ _ _
    have hsb : s j * rkEnv M₀ a j ≤ 7 / 5 * (s (j + 1) * rkEnv M₀ a (j + 1)) := by
      have hss := H.hss j hj
      have h1 : rkEnv M₀ a j ≤ 7 / 6 * rkEnv M₀ a (j + 1) := by
        rw [hMs]; have := mul_le_mul_of_nonneg_right ha1 hMj.le; linarith
      have h2 : s j * rkEnv M₀ a j ≤ 6 / 5 * s (j + 1) * (7 / 6 * rkEnv M₀ a (j + 1)) :=
        mul_le_mul hss h1 hMj.le (by have := H.hs (j + 1) hj1; positivity)
      linarith
    have hrm := H.hrm j hj
    have hsj1 := H.hs (j + 1) hj1
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the coupling
      have h1 := H.hbup j hj
      have h2 : a j * b j ≤ (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
          7 / 3 * ct * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * rkEnv M₀ a (j + 1) := by
        rw [hMs]; have := mul_le_mul_of_nonneg_left hbj (by linarith : 0 ≤ a j)
        linarith
      rw [hsr, hsρ]
      linarith
    · -- the deviation
      have h1 := H.hDstep j hj
      have h2 : a j * D j ≤ (D 0 / M₀ + 2 * (cδ * ∑ k ∈ range j, r k ^ 2) +
          14 / 3 * ct * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * rkEnv M₀ a (j + 1) := by
        rw [hMs]; have := mul_le_mul_of_nonneg_left hDj (by linarith : 0 ≤ a j)
        linarith
      rw [hsr, hsρ]
      linarith
    · -- `𝒲^{obs}`
      have hAj := hAi j le_rfl
      have hm : s j * A j ≤ 2 * s j * rkEnv M₀ a j := by
        have := mul_le_mul_of_nonneg_left hAj hsj.le
        linarith [show s j * (2 * rkEnv M₀ a j) = 2 * s j * rkEnv M₀ a j by ring]
      have h := H.hW j hj (2 * s j * rkEnv M₀ a j) _ (by positivity) (by positivity) hm hWj
      refine H.hWm _ _ _ h ?_
      have hθ := H.hθW j hj
      have hC₁ := H.hC₁
      set Y := r j * (s j * rkEnv M₀ a j)
      set Y' := r (j + 1) * (s (j + 1) * rkEnv M₀ a (j + 1))
      have hY0 : 0 ≤ Y := by positivity
      have hYY : Y ≤ 7 / 5 * Y' := by
        have := mul_le_mul hrm hsb (by positivity) (by linarith)
        linarith [show r (j + 1) * (7 / 5 * (s (j + 1) * rkEnv M₀ a (j + 1))) = 7 / 5 * Y' by ring]
      have h1 : θW j * (cW * r j * (2 * s j * rkEnv M₀ a j)) ≤ 1 / 6 * (2 * cW * Y) := by
        have := mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ cW * r j * (2 * s j * rkEnv M₀ a j))
        linarith [show cW * r j * (2 * s j * rkEnv M₀ a j) = 2 * cW * Y by ring]
      have h2 : C₁ * r j * (2 * s j * rkEnv M₀ a j) = 2 * C₁ * Y := by ring
      have h3 : (cW / 3 + 2 * C₁) * Y ≤ (cW / 3 + 2 * C₁) * (7 / 5 * Y') :=
        mul_le_mul_of_nonneg_left hYY (by positivity)
      have h4 : (cW / 3 + 2 * C₁) * (7 / 5) ≤ 2 * cW := by have := H.hcWC; linarith
      have hY'0 : 0 ≤ Y' := by have := H.hr0 (j + 1) hj1; positivity
      have h5 := mul_le_mul_of_nonneg_right h4 hY'0
      linarith [show cW * r (j + 1) * (2 * s (j + 1) * rkEnv M₀ a (j + 1)) = 2 * cW * Y' by ring]
    · -- `K^{obs}`
      have hAj := hAi j le_rfl
      set m := cW * (2 * s j * rkEnv M₀ a j) with hmdef
      have hm0 : 0 < m := by positivity
      have hm : s j * A j ≤ m := by
        have := mul_le_mul_of_nonneg_left hAj hsj.le
        have h2 : 2 * s j * rkEnv M₀ a j ≤ m := le_mul_of_one_le_left (by positivity) hcW
        linarith [show s j * (2 * rkEnv M₀ a j) = 2 * s j * rkEnv M₀ a j by ring]
      have hW' : Wb j (r j * m) := H.hWm j _ _ hWj (le_of_eq (by rw [hmdef]; ring))
      set κ := (1 / 2) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * rkEnv M₀ a j) with hκ
      have hk0 : 0 ≤ κ := by have := H.hk₀; positivity
      -- the a priori condition
      have h8 : 8 * κ ≤ ck * r j ^ 2 * m := by
        have hsM := H.sM_le hj.le
        have hr0j : r 0 ^ 2 ≤ r j ^ 2 :=
          pow_le_pow_left₀ (H.hr0 0 (Nat.zero_le _)) (H.r_mono hj.le 0 (Nat.zero_le _)) 2
        have hck := H.hck
        have hc0 : 0 ≤ ck - 60 * Bk := by linarith
        have h80 := H.h8
        -- `8 (1/2)^j k₀ ≤ (c_k − 60B) r_j² m`
        have hA : 8 * ((1 / 2) ^ j * k₀) ≤ (ck - 60 * Bk) * r j ^ 2 * m := by
          have e1 : 8 * ((1 / 2) ^ j * k₀) = (1 / 2) ^ j * (8 * k₀) := by ring
          rw [e1]
          have h2 : (1 / 2 : ℝ) ^ j * (8 * k₀) ≤
              (1 / 2) ^ j * ((ck - 60 * Bk) * r 0 ^ 2 * (cW * (2 * (s 0 * M₀)))) := by
            refine mul_le_mul_of_nonneg_left (le_trans h80 (le_of_eq ?_)) (by positivity)
            ring
          have h3 : (1 / 2 : ℝ) ^ j * (s 0 * M₀) ≤ s j * rkEnv M₀ a j := by
            have := mul_le_mul_of_nonneg_left hsM (by positivity : (0 : ℝ) ≤ (1 / 2) ^ j)
            calc (1 / 2 : ℝ) ^ j * (s 0 * M₀) ≤ (1 / 2) ^ j * (2 ^ j * (s j * rkEnv M₀ a j)) := this
              _ = s j * rkEnv M₀ a j := by rw [← mul_assoc, ← mul_pow]; norm_num
          have h4 : (1 / 2 : ℝ) ^ j * ((ck - 60 * Bk) * r 0 ^ 2 * (cW * (2 * (s 0 * M₀)))) =
              (ck - 60 * Bk) * r 0 ^ 2 * (2 * cW) * ((1 / 2) ^ j * (s 0 * M₀)) := by ring
          have h5 : (ck - 60 * Bk) * r 0 ^ 2 * (2 * cW) * ((1 / 2) ^ j * (s 0 * M₀)) ≤
              (ck - 60 * Bk) * r j ^ 2 * (2 * cW) * (s j * rkEnv M₀ a j) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr0j hc0)
              (by positivity)) h3 (by positivity) (by positivity)
          have h6 : (ck - 60 * Bk) * r j ^ 2 * (2 * cW) * (s j * rkEnv M₀ a j) =
              (ck - 60 * Bk) * r j ^ 2 * m := by rw [hmdef]; ring
          linarith
        have hB8 : 8 * (15 * cW * Bk * r j ^ 2 * (s j * rkEnv M₀ a j)) = 60 * Bk * r j ^ 2 * m := by
          rw [hmdef]; ring
        have e : ck * r j ^ 2 * m = (ck - 60 * Bk) * r j ^ 2 * m + 60 * Bk * r j ^ 2 * m := by ring
        rw [hκ, e]
        linarith
      have h := H.hK j hj m κ hm0 hk0 hm hW' hKj h8
      refine H.hKm _ _ _ h ?_
      have hθ := H.hθK j hj
      have h1 : θK j * (8 * κ) ≤ 1 / 2 * κ := by
        have := mul_le_mul_of_nonneg_right hθ (by positivity : (0 : ℝ) ≤ 8 * κ)
        linarith
      have hr2 : r j ^ 2 ≤ r (j + 1) ^ 2 := pow_le_pow_left₀ hrj hrm 2
      have h2 : r j ^ 2 * (s j * rkEnv M₀ a j) ≤
          r (j + 1) ^ 2 * (7 / 5 * (s (j + 1) * rkEnv M₀ a (j + 1))) :=
        mul_le_mul hr2 hsb (by positivity) (sq_nonneg _)
      have hc : 0 ≤ cW * Bk := by positivity
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 2) hc)
      have e : 1 / 2 * κ + Bk * r j ^ 2 * m =
          (1 / 2) ^ (j + 1) * k₀ + 19 / 2 * (cW * Bk) * (r j ^ 2 * (s j * rkEnv M₀ a j)) := by
        rw [hκ, hmdef, pow_succ]; ring
      have e2 : 19 / 2 * (cW * Bk) * (r (j + 1) ^ 2 * (7 / 5 * (s (j + 1) * rkEnv M₀ a (j + 1)))) =
          133 / 10 * cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1)) := by ring
      have h4 : 133 / 10 * cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1)) ≤
          15 * cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1)) := by
        have : 0 ≤ cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1)) := by positivity
        linarith
      linarith

/-- **The restart estimate** (linear in the datum):
`b_j ≤ (b_0 + (1/8 + 10c_t)M₀) ∏_{k<j} a_k`, `c_t = c_Kk₀/(s_0M₀) + x_h`. -/
theorem restart_le {j : ℕ} (hj : j ≤ n) :
    b j ≤ (b 0 + (1 / 8 + 10 * (cK * k₀ / (s 0 * M₀) + xh + tn)) * M₀) * ∏ k ∈ range j, a k := by
  obtain ⟨hbj, -, -, -⟩ := (H.close j hj).1 j le_rfl
  have hM := H.hM0
  have hct0 : 0 ≤ cK * k₀ / (s 0 * M₀) + xh + tn := by
    have := H.hk₀; have := H.hxh; have := H.htn; have := H.hcK; have := H.hs 0 (Nat.zero_le _)
    positivity
  have hS := H.sum_le hj
  have hT := rk_geom_rho j
  have hP : 0 ≤ ∏ k ∈ range j, a k :=
    prod_nonneg fun k hk => by have := (H.ha k (by have := mem_range.1 hk; omega)).1; linarith
  refine hbj.trans ?_
  unfold rkEnv
  have h1 : (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ ≤
      b 0 + (1 / 8 + 10 * (cK * k₀ / (s 0 * M₀) + xh + tn)) * M₀ := by
    have e : (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
        7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ =
        b 0 + (cδ * ∑ k ∈ range j, r k ^ 2 +
          7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ := by
      rw [add_mul, add_mul, div_mul_cancel₀ _ hM.ne']; ring
    rw [e]
    have h2 : 7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k ≤
        10 * (cK * k₀ / (s 0 * M₀) + xh + tn) := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn))
      linarith
    have := mul_le_mul_of_nonneg_right (add_le_add hS h2) hM.le
    linarith
  have := mul_le_mul_of_nonneg_right h1 hP
  linarith [show (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) *
      (M₀ * ∏ k ∈ range j, a k) = (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ *
      ∏ k ∈ range j, a k by ring]

end RelRecK

end Obs2
