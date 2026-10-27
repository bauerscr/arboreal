import Obs2.Flow.RestartRec

/-!
# The restart recursion with large transients (B3, T4′)

`RelRecK` (`Obs2/Flow/RestartRec`) needs the initial `𝒲` and `K` of the datum to be small relative to
the envelope: `𝒲_0 ≤ c_W r_0·2s_0M₀` and `8k₀ ≤ (c_k − 60B)r_0²c_W·2s_0M₀`. For the difference
datum of T6 these force `M₀ ≳ |β|` (Log, "B3, T6 preparation", item 3). Here both are replaced by
**transients that are large relative to the envelope**:

* `𝒲_0 ≤ c_W r_0·2s_0M₀ + w₀` with `w₀ ≥ 0` arbitrary (the transient decays as `6^{-j}`);
* `K_0 ≤ k₀` with `k₀ ≥ 120B r̄w₀` arbitrary (the transient decays as `(8/15)^j`).

The `K` step is used with a **per-step constant** `c` in place of `c_k` (`hK`: any `c ≥ 0` with
`c r_j ≤ c_k r_j + κ̄`), and with the activity size taken larger than the envelope
(`m' = m_j + w̃_j/r_j + 8k̃_j/(κ̄r_j)`), which is allowed since the `K` step bound is linear in
`m` with coefficient `B r_j²`: the transient feeds into the next `K` with the factor
`8Br_j/κ̄ ≤ 1/8` (`64Br̄ ≤ κ̄`). The `K`-step coefficient bound is `θK ≤ 1/20` (instead of `1/16`).

The product parts are used at `m'_i = m_i + w̃_i/r_i`, giving the extra transient
`c_P∑_i q^{j−i}r_iw̃_i/s_i ≤ x_p(3/4)^jM_j` with `x_p ≥ 5c_Pr̄w₀/(s_0M₀)`.

**`RelRecT.close`**: with `c_t = c_Kk₀/(s_0M₀) + x_h + t_n + x_p ≤ 1/48`: as `RelRecK.close`,
with `𝒲_j ≤ c_W r_j·2s_jM_j + 6^{-j}w₀`, `K_j ≤ (8/15)^jk₀ + 15c_WBr_j²s_jM_j`.
**`RelRecT.restart_le`**: `b_j ≤ (b_0 + (1/8 + 10c_t)M₀)∏_{k<j}a_k`.

So the envelope only has to dominate `|β_0| + D_0`, `c_Kk₀/s_0`, `x_hM₀` (the tadpoles of the
initial `𝒲`) and `5c_Pr̄w₀/s_0`, all **linear** in the datum; no `r_0^{-2}` or `r_0^{-1}` factor.
-/

open Finset

namespace Obs2

/-- **The inputs of the restart recursion with large transients.** -/
structure RelInT (n : ℕ) (b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (Wb Kb : ℕ → ℝ → Prop)
    (C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp : ℝ) : Prop where
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
  hcδ : 16 * cK * cW * Bk + 3 * cP * cW + 4 * Bτ * cg * (1 + cg) +
    4 * Bτ * cg * cδ * rb ≤ 6 / 7 * cδ
  hτ : 2 * Bτ * cg * rb ≤ 1 / 2
  hsum : cδ * ∑ k ∈ range n, r k ^ 2 ≤ 1 / 8
  hr0 : ∀ j ≤ n, 0 ≤ r j
  hrb : ∀ j ≤ n, r j ≤ rb
  hrm : ∀ j < n, r j ≤ r (j + 1)
  hs : ∀ j ≤ n, 0 < s j
  hss : ∀ j < n, s j ≤ 6 / 5 * s (j + 1)
  ha : ∀ j < n, 6 / 7 ≤ a j ∧ a j ≤ 2
  hM0 : 0 < M₀
  hk₀ : 0 ≤ k₀
  hxh : 0 ≤ xh
  htn : 0 ≤ tn
  /-- the transients -/
  hw₀ : 0 ≤ w₀
  hκb : 0 < κb
  h64 : 64 * Bk * rb ≤ κb
  hr0p : 0 < r 0
  hkw : 120 * Bk * rb * w₀ ≤ k₀
  hxp : 5 * cP * rb * w₀ / (s 0 * M₀) ≤ xp
  hct : cK * k₀ / (s 0 * M₀) + xh + tn + xp ≤ 1 / 48
  hbD0 : b 0 + D 0 ≤ M₀
  hWm : ∀ j x y, Wb j x → x ≤ y → Wb j y
  hKm : ∀ j x y, Kb j x → x ≤ y → Kb j y
  hW0 : Wb 0 (cW * r 0 * (2 * s 0 * M₀) + w₀)
  hK0 : Kb 0 k₀
  hθW : ∀ j < n, θW j ≤ 1 / 6
  hθK : ∀ j < n, θK j ≤ 1 / 20
  hW : ∀ j < n, ∀ m w, 0 ≤ m → 0 ≤ w → s j * A j ≤ m → Wb j w →
    Wb (j + 1) (θW j * w + C₁ * r j * m)
  /-- the `K^{obs}` step with a per-step constant `c` -/
  hK : ∀ j < n, ∀ m k c, 0 < m → 0 ≤ k → 0 ≤ c → c * r j ≤ ck * r j + κb → s j * A j ≤ m →
    Wb j (r j * m) → Kb j k → 8 * k ≤ c * r j ^ 2 * m →
    Kb (j + 1) (θK j * (8 * k) + Bk * r j ^ 2 * m)
  hKt : ∀ j < n, ∀ k, 0 ≤ k → Kb j k → Kt j ≤ cK * k / s j
  hPr : ∀ j < n, ∀ m : ℕ → ℝ, (∀ i ≤ j, 0 ≤ m i ∧ s i * A i ≤ m i ∧ Wb i (r i * m i)) →
    Pr j ≤ cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * m i / s i)
  hX : ∀ j < n, X j ≤ xh * (1 / 2) ^ j * M₀
  hT : ∀ k j, k < j → j < n → 0 ≤ T k j ∧ T k j ≤ Bτ * q ^ (j - k)
  hG : ∀ i < n, 0 ≤ G i ∧ G i ≤ cg * r i
  hnn : ∀ i < n, 0 ≤ nn i ∧ nn i ≤ cg * r i + tn * (1 / 2) ^ i

/-- **The restart recursion with large transients**: `RelInT` and the flow relations. -/
structure RelRecT (n : ℕ) (b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (Wb Kb : ℕ → ℝ → Prop)
    (C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp : ℝ) : Prop
    extends RelInT n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ
      M₀ k₀ xh tn w₀ κb xp where
  hb : ∀ j ≤ n, 0 ≤ b j
  hD0' : ∀ j ≤ n, 0 ≤ D j
  hA0 : ∀ j ≤ n, 0 ≤ A j
  hE0 : ∀ j < n, 0 ≤ E j
  hDstep : ∀ j < n, D (j + 1) ≤ a j * D j + 2 * E j
  hbup : ∀ j < n, b (j + 1) ≤ a j * b j + E j
  hA : ∀ j ≤ n, A j ≤ b j + D j
  hE : ∀ j < n, E j ≤ Kt j + ∑ k ∈ range j, T k j *
    ∑ i ∈ Ico k j, G i * (nn i * A i + E i) + Pr j + X j

namespace RelRecT

variable {n : ℕ} {b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ} {T : ℕ → ℕ → ℝ}
  {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp : ℝ}
  (H : RelRecT n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀
    xh tn w₀ κb xp)
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

theorem r_pos {j : ℕ} (hj : j ≤ n) : 0 < r j :=
  lt_of_lt_of_le H.hr0p (H.r_mono hj 0 (Nat.zero_le _))

theorem ct_nonneg : 0 ≤ cK * k₀ / (s 0 * M₀) + xh + tn + xp := by
  have := H.hk₀; have := H.hxh; have := H.htn; have := H.hcK; have := H.hs 0 (Nat.zero_le _)
  have := H.hM0
  have hxp0 : 0 ≤ xp := le_trans (by
    have := H.hcP; have := H.hw₀
    have : 0 ≤ rb := (H.hr0 0 (Nat.zero_le _)).trans (H.hrb 0 (Nat.zero_le _))
    positivity) H.hxp
  positivity

/-- `s_0M₀ ≤ (7/5)^j s_jM_j`. -/
theorem sM_le' {j : ℕ} (hj : j ≤ n) : s 0 * M₀ ≤ (7 / 5) ^ j * (s j * rkEnv M₀ a j) := by
  have h1 := H.s_le hj 0 (Nat.zero_le _)
  have h2 := H.env_le hj 0 (Nat.zero_le _)
  rw [rkEnv_zero, Nat.sub_zero] at h2
  rw [Nat.sub_zero] at h1
  have hM := H.hM0
  have hsj := H.hs j hj
  have hMj := H.env_pos hj
  have h3 : s 0 * M₀ ≤ ((6 / 5) ^ j * s j) * ((7 / 6) ^ j * rkEnv M₀ a j) :=
    mul_le_mul h1 h2 hM.le (by positivity)
  have h4 : ((6 / 5 : ℝ) ^ j * s j) * ((7 / 6) ^ j * rkEnv M₀ a j) =
      (7 / 5 : ℝ) ^ j * (s j * rkEnv M₀ a j) := by
    rw [show (7 / 5 : ℝ) = 6 / 5 * (7 / 6) by norm_num, mul_pow]; ring
  linarith

/-- The `K` transient of the activity term, relative to the envelope. -/
theorem kt_tr_le {j : ℕ} (hj : j ≤ n) :
    cK * ((8 / 15) ^ j * k₀) / s j ≤
      cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * rkEnv M₀ a j := by
  have hsM := H.sM_le' hj
  have hs0 := H.hs 0 (Nat.zero_le _)
  have hM := H.hM0
  have hsj := H.hs j hj
  have hMj := H.env_pos hj
  have hcK := H.hcK
  have hk := H.hk₀
  have hA : 0 ≤ cK * k₀ := mul_nonneg hcK hk
  -- `(8/15)^j / s_j ≤ (3/4)^j M_j/(s_0M₀)`
  have key : (8 / 15 : ℝ) ^ j * (s 0 * M₀) ≤ (3 / 4) ^ j * (s j * rkEnv M₀ a j) := by
    have h1 := mul_le_mul_of_nonneg_left hsM (by positivity : (0 : ℝ) ≤ (8 / 15) ^ j)
    have e : (8 / 15 : ℝ) ^ j * ((7 / 5) ^ j * (s j * rkEnv M₀ a j)) =
        (56 / 75) ^ j * (s j * rkEnv M₀ a j) := by
      rw [show (56 / 75 : ℝ) = 8 / 15 * (7 / 5) by norm_num, mul_pow]; ring
    have h2 : (56 / 75 : ℝ) ^ j ≤ (3 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have h3 := mul_le_mul_of_nonneg_right h2 (mul_pos hsj hMj).le
    linarith
  rw [div_le_iff₀ hsj]
  have e : cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * rkEnv M₀ a j * s j =
      cK * k₀ * ((3 / 4) ^ j * (s j * rkEnv M₀ a j)) / (s 0 * M₀) := by ring
  rw [e, le_div_iff₀ (mul_pos hs0 hM)]
  have := mul_le_mul_of_nonneg_left key hA
  linarith [show cK * ((8 / 15) ^ j * k₀) * (s 0 * M₀) =
    cK * k₀ * ((8 / 15) ^ j * (s 0 * M₀)) by ring]

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

/-- The `𝒲` transient of the product parts, relative to the envelope. -/
theorem pr_tr_le {j : ℕ} (hj : j ≤ n) :
    cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (r i * ((1 / 6) ^ i * w₀) / s i) ≤
      xp * (3 / 4) ^ j * rkEnv M₀ a j := by
  have hs0 := H.hs 0 (Nat.zero_le _)
  have hM := H.hM0
  have hMj := H.env_pos hj
  have hw := H.hw₀
  have hcP := H.hcP
  have hrb0 : 0 ≤ rb := (H.hr0 0 (Nat.zero_le _)).trans (H.hrb 0 (Nat.zero_le _))
  have h1 : ∀ i ∈ range (j + 1), q ^ (j - i) * (r i * ((1 / 6) ^ i * w₀) / s i) ≤
      rb * w₀ / s 0 * ((1 / 4) ^ j * (4 / 5) ^ i) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hsi := H.hs i (by omega)
    have hsle : s 0 ≤ (6 / 5) ^ i * s i := by
      have := H.s_le (j := i) (by omega) 0 (Nat.zero_le _); simpa using this
    have hri : r i ≤ rb := H.hrb i (by omega)
    have hr0i := H.hr0 i (by omega)
    have hq1 : q ^ (j - i) ≤ (1 / 4) ^ (j - i) := pow_le_pow_left₀ H.hq0 H.hq _
    have h2 : r i * ((1 / 6) ^ i * w₀) / s i ≤ rb * w₀ / s 0 * (1 / 5) ^ i := by
      rw [div_le_iff₀ hsi]
      have e1 : rb * w₀ / s 0 * (1 / 5) ^ i * s i = rb * w₀ * ((1 / 5) ^ i * s i) / s 0 := by
        ring
      rw [e1, le_div_iff₀ hs0]
      have h3 : (1 / 6 : ℝ) ^ i * s 0 ≤ (1 / 5) ^ i * s i := by
        have := mul_le_mul_of_nonneg_left hsle (by positivity : (0 : ℝ) ≤ (1 / 6) ^ i)
        rw [← mul_assoc, ← mul_pow] at this
        norm_num at this ⊢
        linarith
      have h4 : r i * w₀ ≤ rb * w₀ := mul_le_mul_of_nonneg_right hri hw
      calc r i * ((1 / 6) ^ i * w₀) * s 0 = r i * w₀ * ((1 / 6) ^ i * s 0) := by ring
        _ ≤ rb * w₀ * ((1 / 5) ^ i * s i) :=
            mul_le_mul h4 h3 (by positivity) (by positivity)
    have h5 : 0 ≤ r i * ((1 / 6) ^ i * w₀) / s i := by positivity
    calc q ^ (j - i) * (r i * ((1 / 6) ^ i * w₀) / s i)
        ≤ (1 / 4) ^ (j - i) * (rb * w₀ / s 0 * (1 / 5) ^ i) :=
          mul_le_mul hq1 h2 h5 (by positivity)
      _ = rb * w₀ / s 0 * ((1 / 4) ^ (j - i) * (1 / 5) ^ i) := by ring
      _ = rb * w₀ / s 0 * ((1 / 4) ^ j * (4 / 5) ^ i) := by
          congr 1
          have hji : (1 / 4 : ℝ) ^ j = (1 / 4) ^ (j - i) * (1 / 4) ^ i := by
            rw [← pow_add]; congr 1; omega
          rw [hji, mul_assoc, ← mul_pow]; norm_num
  have h2 := sum_le_sum h1
  rw [← mul_sum, ← mul_sum] at h2
  have hg : ∑ i ∈ range (j + 1), (4 / 5 : ℝ) ^ i ≤ 5 := by
    have h := geom_sum_eq (show (4 / 5 : ℝ) ≠ 1 by norm_num) (j + 1)
    rw [h]
    have : 0 ≤ (4 / 5 : ℝ) ^ (j + 1) := by positivity
    have e : ((4 / 5 : ℝ) ^ (j + 1) - 1) / (4 / 5 - 1) = 5 * (1 - (4 / 5 : ℝ) ^ (j + 1)) := by
      ring
    rw [e]; linarith
  have h3 : rb * w₀ / s 0 * ((1 / 4) ^ j * ∑ i ∈ range (j + 1), (4 / 5 : ℝ) ^ i) ≤
      rb * w₀ / s 0 * ((1 / 4) ^ j * 5) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by positivity)) (by positivity)
  -- `(1/4)^j M₀ ≤ (3/4)^j M_j`
  have h4 : (1 / 4 : ℝ) ^ j * M₀ ≤ (3 / 4) ^ j * rkEnv M₀ a j := by
    have h2' := H.env_le hj 0 (Nat.zero_le _)
    rw [rkEnv_zero, Nat.sub_zero] at h2'
    have := mul_le_mul_of_nonneg_left h2' (by positivity : (0 : ℝ) ≤ (1 / 4) ^ j)
    have e : (1 / 4 : ℝ) ^ j * ((7 / 6) ^ j * rkEnv M₀ a j) = (7 / 24) ^ j * rkEnv M₀ a j := by
      rw [show (7 / 24 : ℝ) = 1 / 4 * (7 / 6) by norm_num, mul_pow]; ring
    have h7 : (7 / 24 : ℝ) ^ j ≤ (3 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have := mul_le_mul_of_nonneg_right h7 hMj.le
    linarith
  have hx := H.hxp
  have hxp0 : 0 ≤ 5 * cP * rb * w₀ / (s 0 * M₀) := by positivity
  have h5 : cP * (rb * w₀ / s 0 * ((1 / 4) ^ j * 5)) =
      5 * cP * rb * w₀ / (s 0 * M₀) * ((1 / 4) ^ j * M₀) := by
    field_simp
  have h6 : 5 * cP * rb * w₀ / (s 0 * M₀) * ((1 / 4) ^ j * M₀) ≤
      xp * ((3 / 4) ^ j * rkEnv M₀ a j) :=
    mul_le_mul hx h4 (by positivity) (hxp0.trans hx)
  have h7 := mul_le_mul_of_nonneg_left (h2.trans h3) hcP
  linarith [show xp * ((3 / 4) ^ j * rkEnv M₀ a j) = xp * (3 / 4) ^ j * rkEnv M₀ a j by ring]

set_option maxHeartbeats 1000000 in
/-- **The error at step `j`** (steady part `c_δr_j²a_jM_j`, transient `2c_tρ^jM_j`). -/
theorem E_le {j : ℕ} (hj : j < n) (hAi : ∀ i ≤ j, A i ≤ 2 * rkEnv M₀ a i)
    (hEi : ∀ i < j, E i ≤ (cδ * r i ^ 2 * a i +
      2 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * (3 / 4) ^ i) * rkEnv M₀ a i)
    (hKj : Kb j ((8 / 15) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * rkEnv M₀ a j)))
    (hWi : ∀ i ≤ j, Wb i (cW * r i * (2 * s i * rkEnv M₀ a i) + (1 / 6) ^ i * w₀)) :
    E j ≤ (cδ * r j ^ 2 * a j +
      2 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * (3 / 4) ^ j) * rkEnv M₀ a j := by
  set M := rkEnv M₀ a with hMdef
  set ct := cK * k₀ / (s 0 * M₀) + xh + tn + xp with hct
  have hMj := H.env_pos hj.le
  have hsj := H.hs j hj.le
  have hrj := H.hr0 j hj.le
  have hcW0 : 0 ≤ cW := by linarith [H.hcW1]
  have hcg := H.hcg
  have hcδ0 := H.hcδ0
  have hBk := H.hBk
  have hcK := H.hcK
  have hrb0 : 0 ≤ rb := hrj.trans (H.hrb j hj.le)
  have hct0 : 0 ≤ ct := H.ct_nonneg
  have hri := H.r_mono hj.le
  have hMi := H.env_le hj.le
  -- the activity term
  have hKt : Kt j ≤ 16 * cK * cW * Bk * r j ^ 2 * M j + cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * M j := by
    have h := H.hKt j hj _ (by have := H.hk₀; positivity) hKj
    have h2 := H.kt_tr_le hj.le
    have e : cK * ((8 / 15) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * M j)) / s j =
        cK * ((8 / 15) ^ j * k₀) / s j + 15 * cK * cW * Bk * r j ^ 2 * M j := by
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
  have hprod : Pr j ≤ 3 * cP * cW * r j ^ 2 * M j + xp * (3 / 4) ^ j * M j := by
    have h := H.hPr j hj (fun i => cW * (2 * s i * M i) + (1 / 6) ^ i * w₀ / r i) fun i hi => by
      have hsi := H.hs i (by omega)
      have hMi0 := H.env_pos (j := i) (by omega)
      have hri0 := H.r_pos (j := i) (by omega)
      have hw := H.hw₀
      refine ⟨by positivity, ?_, H.hWm i _ _ (hWi i hi) (le_of_eq (by field_simp))⟩
      have h1 : s i * A i ≤ s i * (2 * M i) := mul_le_mul_of_nonneg_left (hAi i hi) hsi.le
      have h2 : 2 * s i * M i ≤ cW * (2 * s i * M i) :=
        le_mul_of_one_le_left (by positivity) H.hcW1
      have h3 : 0 ≤ (1 / 6 : ℝ) ^ i * w₀ / r i := by positivity
      linarith [show s i * (2 * M i) = 2 * s i * M i by ring]
    refine h.trans ?_
    have hsplit : ∑ i ∈ range (j + 1), q ^ (j - i) *
        (r i ^ 2 * (cW * (2 * s i * M i) + (1 / 6) ^ i * w₀ / r i) / s i) =
        ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (cW * (2 * s i * M i)) / s i) +
          ∑ i ∈ range (j + 1), q ^ (j - i) * (r i * ((1 / 6) ^ i * w₀) / s i) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      have hri0 := H.r_pos (j := i) (by have := mem_range.1 hi; omega)
      have hsi := H.hs i (by have := mem_range.1 hi; omega)
      field_simp
    rw [hsplit, mul_add]
    have hP2 := H.pr_tr_le hj.le
    suffices hP1 : cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (cW * (2 * s i * M i)) / s i)
        ≤ 3 * cP * cW * r j ^ 2 * M j by linarith
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
      xh * (3 / 4) ^ j * M j + xp * (3 / 4) ^ j * M j = 2 * ct * (3 / 4) ^ j * M j := by
    rw [hct]; ring
  have hfin : E j ≤ cδ * r j ^ 2 * a j * M j + 2 * ct * (3 / 4) ^ j * M j := by
    have e2 : 2 * Bτ * (Xs + Xt) = 2 * Bτ * Xs + 2 * Bτ * Xt := by ring
    linarith
  linarith [show (cδ * r j ^ 2 * a j + 2 * ct * (3 / 4) ^ j) * M j =
    cδ * r j ^ 2 * a j * M j + 2 * ct * (3 / 4) ^ j * M j by ring]


/-- The bounds at scale `j` of the induction. -/
def Base (_H : RelRecT n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ
    M₀ k₀ xh tn w₀ κb xp) (j : ℕ) : Prop :=
  b j ≤ (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * rkEnv M₀ a j ∧
    D j ≤ (D 0 / M₀ + 2 * (cδ * ∑ k ∈ range j, r k ^ 2) +
      14 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * rkEnv M₀ a j ∧
    Wb j (cW * r j * (2 * s j * rkEnv M₀ a j) + (1 / 6) ^ j * w₀) ∧
    Kb j ((8 / 15) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * rkEnv M₀ a j))


set_option maxHeartbeats 1000000 in
/-- **The restart recursion closes.** -/
theorem close : ∀ j ≤ n, (∀ i ≤ j, H.Base i) ∧
    (∀ i < j, E i ≤ (cδ * r i ^ 2 * a i +
      2 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * (3 / 4) ^ i) * rkEnv M₀ a i) := by
  have hcW : 1 ≤ cW := H.hcW1
  have hcW0 : 0 ≤ cW := by linarith
  have hBk := H.hBk
  have hM := H.hM0
  have hs0 := H.hs 0 (Nat.zero_le _)
  set ct := cK * k₀ / (s 0 * M₀) + xh + tn + xp with hct
  have hct0 : 0 ≤ ct := H.ct_nonneg
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
    · rw [rkEnv_zero, pow_zero, one_mul]; exact H.hW0
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
      exact RelRecK.base_A hM (H.env_pos (by omega)) hbi hDi (H.hA i (by omega)) H.hbD0
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
      have hw := H.hw₀
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
      have h1 : θW j * (cW * r j * (2 * s j * rkEnv M₀ a j) + (1 / 6) ^ j * w₀) ≤
          1 / 6 * (2 * cW * Y) + (1 / 6) ^ (j + 1) * w₀ := by
        have := mul_le_mul_of_nonneg_right hθ
          (by positivity : 0 ≤ cW * r j * (2 * s j * rkEnv M₀ a j) + (1 / 6) ^ j * w₀)
        linarith [show cW * r j * (2 * s j * rkEnv M₀ a j) = 2 * cW * Y by ring,
          show (1 / 6 : ℝ) ^ (j + 1) * w₀ = 1 / 6 * ((1 / 6) ^ j * w₀) by ring]
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
      have hrj' : 0 < r j := H.r_pos hj.le
      have hw := H.hw₀
      have hκ := H.hκb
      have hk00 := H.hk₀
      set kt := (8 / 15 : ℝ) ^ j * k₀ with hkt
      have hkt0 : 0 ≤ kt := by positivity
      set wt := (1 / 6 : ℝ) ^ j * w₀ with hwt
      have hwt0 : 0 ≤ wt := by positivity
      set m' := m + wt / r j + 8 * kt / (κb * r j) with hm'
      have hq1 : 0 ≤ wt / r j := by positivity
      have hq2 : 0 ≤ 8 * kt / (κb * r j) := by positivity
      have hmm' : m ≤ m' := by linarith
      have hm'0 : 0 < m' := by linarith
      have hm : s j * A j ≤ m' := by
        have := mul_le_mul_of_nonneg_left hAj hsj.le
        have h2 : 2 * s j * rkEnv M₀ a j ≤ m := le_mul_of_one_le_left (by positivity) hcW
        linarith [show s j * (2 * rkEnv M₀ a j) = 2 * s j * rkEnv M₀ a j by ring]
      have er : r j * m' = r j * m + wt + 8 * kt / κb := by
        rw [hm']; field_simp
      have hW' : Wb j (r j * m') := by
        refine H.hWm j _ _ hWj ?_
        rw [er]
        have : 0 ≤ 8 * kt / κb := by positivity
        linarith [show cW * r j * (2 * s j * rkEnv M₀ a j) = r j * m by rw [hmdef]; ring]
      set κ := kt + 15 * cW * Bk * r j ^ 2 * (s j * rkEnv M₀ a j) with hκd
      have hk0 : 0 ≤ κ := by positivity
      set cc := 60 * Bk + 8 * kt / (r j ^ 2 * m') with hcc
      have hcc0 : 0 ≤ cc := by positivity
      have hcr : cc * r j ≤ ck * r j + κb := by
        have h1 : 8 * kt / (r j ^ 2 * m') * r j ≤ κb := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          -- `8 kt r ≤ κb r² m'`, from `κb r m' ≥ 8 kt`
          have h2 : 8 * kt ≤ κb * r j * m' := by
            have h3 : κb * r j * (8 * kt / (κb * r j)) = 8 * kt := by field_simp
            have h4 : κb * r j * (8 * kt / (κb * r j)) ≤ κb * r j * m' :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            linarith
          have := mul_le_mul_of_nonneg_left h2 hrj'.le
          nlinarith
        have h5 : 60 * Bk * r j ≤ ck * r j := mul_le_mul_of_nonneg_right H.hck hrj'.le
        have e : cc * r j = 60 * Bk * r j + 8 * kt / (r j ^ 2 * m') * r j := by rw [hcc]; ring
        linarith
      have h8 : 8 * κ ≤ cc * r j ^ 2 * m' := by
        have e : cc * r j ^ 2 * m' = 60 * Bk * r j ^ 2 * m' + 8 * kt := by
          rw [hcc]; field_simp
        have h1 : 60 * Bk * r j ^ 2 * m ≤ 60 * Bk * r j ^ 2 * m' :=
          mul_le_mul_of_nonneg_left hmm' (by positivity)
        have e2 : 8 * κ = 8 * kt + 60 * Bk * r j ^ 2 * m := by rw [hκd, hmdef]; ring
        linarith
      have h := H.hK j hj m' κ cc hm'0 hk0 hcc0 hcr hm hW' hKj h8
      refine H.hKm _ _ _ h ?_
      have hθ := H.hθK j hj
      have h1 : θK j * (8 * κ) ≤ 2 / 5 * κ := by
        have := mul_le_mul_of_nonneg_right hθ (by positivity : (0 : ℝ) ≤ 8 * κ)
        linarith
      have e : Bk * r j ^ 2 * m' = Bk * r j ^ 2 * m + Bk * r j * wt + 8 * Bk * r j * kt / κb := by
        rw [hm']; field_simp
      have hrb := H.hrb j hj.le
      have hb1 : Bk * r j * wt ≤ Bk * rb * wt :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrb hBk) hwt0
      have hb2 : 8 * Bk * r j * kt / κb ≤ kt / 8 := by
        rw [div_le_iff₀ hκ]
        have h64 : 64 * Bk * r j ≤ κb := by
          have := mul_le_mul_of_nonneg_left hrb (by positivity : (0 : ℝ) ≤ 64 * Bk)
          linarith only [this, H.h64]
        have := mul_le_mul_of_nonneg_left h64 hkt0
        linarith only [this, show 8 * Bk * r j * kt = kt * (64 * Bk * r j) / 8 by ring,
          show kt / 8 * κb = kt * κb / 8 by ring]
      have hb4 : Bk * rb * wt ≤ (8 / 15) ^ j * k₀ / 120 := by
        have hkw := H.hkw
        have h6 : (1 / 6 : ℝ) ^ j ≤ (8 / 15) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
        have hrb0 : 0 ≤ rb := hrj'.le.trans hrb
        have h7 : Bk * rb * w₀ ≤ k₀ / 120 := by linarith only [hkw]
        have h8' : 0 ≤ Bk * rb * w₀ := by positivity
        calc Bk * rb * wt = (1 / 6) ^ j * (Bk * rb * w₀) := by rw [hwt]; ring
          _ ≤ (8 / 15) ^ j * (k₀ / 120) := mul_le_mul h6 h7 h8' (by positivity)
          _ = (8 / 15) ^ j * k₀ / 120 := by ring
      have hr2 : r j ^ 2 ≤ r (j + 1) ^ 2 := pow_le_pow_left₀ hrj hrm 2
      have h2 : r j ^ 2 * (s j * rkEnv M₀ a j) ≤
          r (j + 1) ^ 2 * (7 / 5 * (s (j + 1) * rkEnv M₀ a (j + 1))) :=
        mul_le_mul hr2 hsb (by positivity) (sq_nonneg _)
      have hc : 0 ≤ cW * Bk := by positivity
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hc)
      have hS : 0 ≤ cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1)) := by positivity
      have e3 : Bk * r j ^ 2 * m = 2 * (cW * Bk) * (r j ^ 2 * (s j * rkEnv M₀ a j)) := by
        rw [hmdef]; ring
      have e4 : 2 / 5 * κ = 2 / 5 * kt + 6 * (cW * Bk) * (r j ^ 2 * (s j * rkEnv M₀ a j)) := by
        rw [hκd]; ring
      have e5 : (8 / 15 : ℝ) ^ (j + 1) * k₀ = 8 / 15 * kt := by rw [hkt, pow_succ]; ring
      have e6 : 8 * (cW * Bk) * (r (j + 1) ^ 2 * (7 / 5 * (s (j + 1) * rkEnv M₀ a (j + 1)))) =
          56 / 5 * (cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1))) := by ring
      have e7 : 15 * cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1)) =
          15 * (cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * rkEnv M₀ a (j + 1))) := by ring
      have e8 : (8 / 15 : ℝ) ^ j * k₀ / 120 = kt / 120 := by rw [hkt]
      rw [e5, e7]
      linarith only [h1, e, hb1, hb2, hb4, e8, e3, e4, h3, e6, hS]

/-- **The restart estimate** (linear in the datum):
`b_j ≤ (b_0 + (1/8 + 10c_t)M₀) ∏_{k<j} a_k`, `c_t = c_Kk₀/(s_0M₀) + x_h`. -/
theorem restart_le {j : ℕ} (hj : j ≤ n) :
    b j ≤ (b 0 + (1 / 8 + 10 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp)) * M₀) * ∏ k ∈ range j, a k := by
  obtain ⟨hbj, -, -, -⟩ := (H.close j hj).1 j le_rfl
  have hM := H.hM0
  have hct0 : 0 ≤ cK * k₀ / (s 0 * M₀) + xh + tn + xp := H.ct_nonneg
  have hS := H.sum_le hj
  have hT := rk_geom_rho j
  have hP : 0 ≤ ∏ k ∈ range j, a k :=
    prod_nonneg fun k hk => by have := (H.ha k (by have := mem_range.1 hk; omega)).1; linarith
  refine hbj.trans ?_
  unfold rkEnv
  have h1 : (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ ≤
      b 0 + (1 / 8 + 10 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp)) * M₀ := by
    have e : (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
        7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ =
        b 0 + (cδ * ∑ k ∈ range j, r k ^ 2 +
          7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ := by
      rw [add_mul, add_mul, div_mul_cancel₀ _ hM.ne']; ring
    rw [e]
    have h2 : 7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k ≤
        10 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp))
      linarith
    have := mul_le_mul_of_nonneg_right (add_le_add hS h2) hM.le
    linarith
  have := mul_le_mul_of_nonneg_right h1 hP
  linarith [show (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) *
      (M₀ * ∏ k ∈ range j, a k) = (b 0 / M₀ + cδ * ∑ k ∈ range j, r k ^ 2 +
      7 / 3 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * ∑ k ∈ range j, (3 / 4 : ℝ) ^ k) * M₀ *
      ∏ k ∈ range j, a k by ring]


end RelRecT

end Obs2
