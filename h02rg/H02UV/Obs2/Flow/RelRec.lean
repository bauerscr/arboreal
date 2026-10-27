import Mathlib

/-!
# The relative coupled recursion (pure real sequences)

The observable bounds along the flow with sizes **proportional to the coupling**:
with `b_j = |β_j|`, `A_j = ∑_B |c_j(B)|`, `D_j` the deviation of the shares, `E_j` the `ℓ¹`
error of the per-block flow, `a_j = |1 - 𝔫_j|`, field scales `s_j` and radii `r_j`, and
monotone predicates `Wb j x` ("all `‖𝒲^{obs}_j(B)‖ ≤ x`") and `Kb j k` (the weighted
`K^{obs}_j` bound), the structure `RelRec` collects

* the per-block flow relations (`D_{j+1} ≤ a_jD_j + 2E_j`, `a_jb_j − E_j ≤ b_{j+1}`,
  `A_j ≤ b_j + D_j`),
* the one-step observable bounds (`𝒲`: contraction `θ_W ≤ 1/6` and source `C₁r m`;
  `K`: contraction `θ_K ≤ 1/16` and source `B r² m`, under the a priori `8k ≤ 64Br²m`),
* the split of `E_j` into the activity term, the drift and the product parts, with
  the activity term `≤ c_K k/s_j`, the product parts `≤ c_P ∑_{i≤j} q^{j-i} r_i² m_i/s_i`,
  the tadpole decay `|τ(C_k,C_j)| ≤ B_τ q^{j-k}`, and bulk bounds `|g'_{i+1}-g'_i| ≤ c_g r_i²`,
  `|g'_i|, |𝔫_i| ≤ c_g r_i`,
* `r` nondecreasing, `s_j ≤ (6/5)s_{j+1}`, `6/7 ≤ a_j ≤ 2`, `q ≤ 1/4`, and the summability
  `c_δ ∑_{k<n} r_k² ≤ 1/8`.

**`RelRec.close`**: then for `j ≤ n`, with `M_j = 2s_jb_j` and `c_W = 3C₁ + 1`,
`b_j > 0`, `D_j ≤ 6c_δ(∑_{k<j} r_k²) b_j`, `‖𝒲^{obs}_j‖ ≤ c_W r_j M_j`,
`K_j ≤ 16 c_W B r_j² s_j b_j`, and `E_j ≤ c_δ r_j² a_j b_j` for `j < n`:
the relative error of step `j` is `δ_j = c_δ r_j²` (summable).

**`rel_prod_le`**: `x_{k+1} = x_ku_k + e_k`, `‖e_k‖ ≤ δ_k‖x_ku_k‖` give
`‖x_j − x_0∏u_k‖ ≤ (∏(1+δ_k) − 1)‖x_0∏u_k‖ ≤ (e^{∑δ_k} − 1)‖x_0∏u_k‖`.
-/

open Finset

namespace Obs2

/-- `x_i ≤ c^{j-i} x_j` from the one-step comparison `x_l ≤ c x_{l+1}`. -/
theorem le_pow_mul_of_step {x : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    ∀ {j : ℕ}, (∀ l < j, x l ≤ c * x (l + 1)) → ∀ i ≤ j, x i ≤ c ^ (j - i) * x j := by
  intro j
  induction j with
  | zero => intro _ i hi; obtain rfl : i = 0 := by omega
            simp
  | succ j ih =>
    intro h i hi
    rcases Nat.lt_or_ge i (j + 1) with hij | hij
    · have h1 := ih (fun l hl => h l (by omega)) i (by omega)
      have h2 := h j (by omega)
      have e : j + 1 - i = (j - i) + 1 := by omega
      rw [e, pow_succ]
      calc x i ≤ c ^ (j - i) * x j := h1
        _ ≤ c ^ (j - i) * (c * x (j + 1)) := mul_le_mul_of_nonneg_left h2 (pow_nonneg hc _)
        _ = c ^ (j - i) * c * x (j + 1) := by ring
    · obtain rfl : i = j + 1 := by omega
      simp

/-- `∑_{k<j} y^{j-k} ≤ 1/2` for `0 ≤ y ≤ 1/3`. -/
theorem geom_tail_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 3) :
    ∀ j : ℕ, ∑ k ∈ range j, y ^ (j - k) ≤ 1 / 2 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : ∑ k ∈ range (j + 1), y ^ (j + 1 - k) = (∑ k ∈ range j, y ^ (j - k)) * y + y := by
      rw [sum_range_succ, Nat.add_sub_cancel_left, pow_one, sum_mul]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      have hk' := mem_range.1 hk
      rw [show j + 1 - k = (j - k) + 1 by omega, pow_succ]
    rw [e]
    nlinarith

theorem geom_tail_le' {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 3) (j : ℕ) :
    ∑ k ∈ range (j + 1), y ^ (j - k) ≤ 3 / 2 := by
  rw [sum_range_succ, Nat.sub_self, pow_zero]
  linarith [geom_tail_le hy0 hy j]

/-- `∑_{k ≤ i < j} (4/3)^{j-i} ≤ 4((4/3)^{j-k} − 1)`. -/
theorem geom_Ico_le {k : ℕ} : ∀ j, k ≤ j →
    ∑ i ∈ Ico k j, (4 / 3 : ℝ) ^ (j - i) ≤ 4 * ((4 / 3 : ℝ) ^ (j - k) - 1) := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hkj ih =>
    rw [sum_Ico_succ_top hkj, Nat.add_sub_cancel_left, pow_one]
    have e : ∑ i ∈ Ico k j, (4 / 3 : ℝ) ^ (j + 1 - i) =
        (4 / 3) * ∑ i ∈ Ico k j, (4 / 3 : ℝ) ^ (j - i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := (mem_Ico.1 hi).2
      rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]; ring
    rw [e, show j + 1 - k = (j - k) + 1 by omega, pow_succ]
    nlinarith

/-- The inputs of the relative coupled recursion (constants, the one-step observable bounds,
the pieces of the error, the bulk bounds). -/
structure RelIn (n : ℕ) (b A D E a s r Kt Pr dg G nn θW θK : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (Wb Kb : ℕ → ℝ → Prop) (C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ) : Prop where
  hC₁ : 0 ≤ C₁
  hcW1 : 1 ≤ cW
  hcWC : 3 * C₁ ≤ cW
  hBk : 0 ≤ Bk
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
  /-- summability of the relative errors -/
  hsum : cδ * ∑ k ∈ range n, r k ^ 2 ≤ 1 / 8
  hr0 : ∀ j ≤ n, 0 ≤ r j
  hrb : ∀ j ≤ n, r j ≤ rb
  hrm : ∀ j < n, r j ≤ r (j + 1)
  hs : ∀ j ≤ n, 0 < s j
  hss : ∀ j < n, s j ≤ 6 / 5 * s (j + 1)
  ha : ∀ j < n, 6 / 7 ≤ a j ∧ a j ≤ 2
  hb0 : 0 < b 0
  hD0 : D 0 = 0
  hWm : ∀ j x y, Wb j x → x ≤ y → Wb j y
  hKm : ∀ j x y, Kb j x → x ≤ y → Kb j y
  hW0 : Wb 0 0
  hK0 : Kb 0 0
  hθW : ∀ j < n, θW j ≤ 1 / 6
  hθK : ∀ j < n, θK j ≤ 1 / 16
  /-- the `𝒲^{obs}` step -/
  hW : ∀ j < n, ∀ m w, 0 ≤ m → 0 ≤ w → s j * A j ≤ m → Wb j w →
    Wb (j + 1) (θW j * w + C₁ * r j * m)
  /-- the `K^{obs}` step -/
  hK : ∀ j < n, ∀ m k, 0 < m → 0 ≤ k → s j * A j ≤ m → Wb j (r j * m) → Kb j k →
    8 * k ≤ 64 * Bk * r j ^ 2 * m → Kb (j + 1) (θK j * (8 * k) + Bk * r j ^ 2 * m)
  /-- the activity term of `E_j` -/
  hKt : ∀ j < n, ∀ k, 0 ≤ k → Kb j k → Kt j ≤ cK * k / s j
  /-- the product parts of `E_j` -/
  hPr : ∀ j < n, ∀ m : ℕ → ℝ, (∀ i ≤ j, 0 ≤ m i ∧ s i * A i ≤ m i ∧ Wb i (r i * m i)) →
    Pr j ≤ cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * m i / s i)
  hT : ∀ k j, k < j → j < n → 0 ≤ T k j ∧ T k j ≤ Bτ * q ^ (j - k)
  hdg : ∀ i < n, 0 ≤ dg i ∧ dg i ≤ cg * r i ^ 2
  hG : ∀ i < n, 0 ≤ G i ∧ G i ≤ cg * r i
  hnn : ∀ i < n, 0 ≤ nn i ∧ nn i ≤ cg * r i

/-- The hypotheses of the relative coupled recursion: `RelIn` and the per-block flow relations. -/
structure RelRec (n : ℕ) (b A D E a s r Kt Pr dg G nn θW θK : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (Wb Kb : ℕ → ℝ → Prop) (C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ) : Prop
    extends RelIn n b A D E a s r Kt Pr dg G nn θW θK T Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ where
  hb : ∀ j ≤ n, 0 ≤ b j
  hA0 : ∀ j ≤ n, 0 ≤ A j
  hE0 : ∀ j < n, 0 ≤ E j
  hDstep : ∀ j < n, D (j + 1) ≤ a j * D j + 2 * E j
  hbstep : ∀ j < n, a j * b j - E j ≤ b (j + 1)
  hA : ∀ j ≤ n, A j ≤ b j + D j
  /-- the split of `E_j` -/
  hE : ∀ j < n, E j ≤ Kt j + ∑ k ∈ range j, T k j *
    ∑ i ∈ Ico k j, (dg i * A (i + 1) + G i * (nn i * A i + E i)) + Pr j


namespace RelRec

variable {n : ℕ} {b A D E a s r Kt Pr dg G nn θW θK : ℕ → ℝ} {T : ℕ → ℕ → ℝ}
  {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ}
  (H : RelRec n b A D E a s r Kt Pr dg G nn θW θK T Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ)
include H

theorem rsq_le {j : ℕ} (hj : j < n) : cδ * r j ^ 2 ≤ 1 / 8 := by
  have h := single_le_sum (f := fun k => r k ^ 2) (fun k _ => sq_nonneg (r k))
    (mem_range.2 hj)
  exact (mul_le_mul_of_nonneg_left h H.hcδ0).trans H.hsum

theorem sum_le {j : ℕ} (hj : j ≤ n) : cδ * ∑ k ∈ range j, r k ^ 2 ≤ 1 / 8 := by
  have h : ∑ k ∈ range j, r k ^ 2 ≤ ∑ k ∈ range n, r k ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj) fun k _ _ => sq_nonneg _
  exact (mul_le_mul_of_nonneg_left h H.hcδ0).trans H.hsum

/-- **The relative error at step `j`**, given the bounds at the scales `≤ j`. -/
theorem E_le {j : ℕ} (hj : j < n) (hbi : ∀ i ≤ j, b i ≤ (4 / 3) ^ (j - i) * b j)
    (hAi : ∀ i ≤ j, A i ≤ 2 * b i)
    (hEi : ∀ i < j, E i ≤ cδ * r i ^ 2 * (a i * b i)) (hri : ∀ i ≤ j, r i ≤ r j)
    (hKtj : Kt j ≤ 16 * cK * cW * Bk * r j ^ 2 * b j)
    (hPrj : Pr j ≤ cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (2 * cW * b i))) :
    E j ≤ cδ * r j ^ 2 * (a j * b j) := by
  have hbj := H.hb j hj.le
  have hrj := H.hr0 j hj.le
  have hcW0 : 0 ≤ cW := by linarith [H.hcW1]
  have hcg := H.hcg
  have hcδ0 := H.hcδ0
  have hrb0 : 0 ≤ rb := hrj.trans (H.hrb j hj.le)
  set X := 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * b j with hX
  have hX0 : 0 ≤ X := by positivity
  -- the summand of the drift
  have hterm : ∀ i < j, dg i * A (i + 1) + G i * (nn i * A i + E i) ≤
      X * (4 / 3) ^ (j - i) := by
    intro i hij
    have hin : i < n := by omega
    set P := (4 / 3 : ℝ) ^ (j - i) * b j with hP
    have hP0 : 0 ≤ P := by positivity
    have hbi' : b i ≤ P := hbi i hij.le
    have hbi1 : b (i + 1) ≤ P := by
      refine (hbi (i + 1) hij).trans (mul_le_mul_of_nonneg_right ?_ hbj)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hri' := hri i hij.le
    have hr0i := H.hr0 i hin.le
    have hrbi := H.hrb i hin.le
    obtain ⟨hdg0, hdg1⟩ := H.hdg i hin
    obtain ⟨hG0, hG1⟩ := H.hG i hin
    obtain ⟨hnn0, hnn1⟩ := H.hnn i hin
    obtain ⟨-, ha2⟩ := H.ha i hin
    have hA1 : A (i + 1) ≤ 2 * P := (hAi (i + 1) hij).trans (by linarith)
    have hAi' : A i ≤ 2 * P := (hAi i hij.le).trans (by linarith)
    have hE1 : E i ≤ cδ * (rb * r j) * (2 * P) := by
      refine (hEi i hij).trans ?_
      have h1 : r i ^ 2 ≤ rb * r j := by
        rw [sq]; exact mul_le_mul hrbi hri' hr0i hrb0
      have h2 : a i * b i ≤ 2 * P := mul_le_mul ha2 hbi' (H.hb i hin.le) (by norm_num)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hcδ0) h2
        (mul_nonneg (by linarith [(H.ha i hin).1]) (H.hb i hin.le)) (by positivity)
    have hr2 : r i ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ hr0i hri' 2
    have t1 : dg i * A (i + 1) ≤ cg * r j ^ 2 * (2 * P) :=
      mul_le_mul (hdg1.trans (mul_le_mul_of_nonneg_left hr2 hcg)) hA1 (H.hA0 _ (by omega))
        (by positivity)
    have t2 : nn i * A i ≤ cg * r j * (2 * P) :=
      mul_le_mul (hnn1.trans (mul_le_mul_of_nonneg_left hri' hcg)) hAi' (H.hA0 _ hin.le)
        (by positivity)
    have t3 : G i * (nn i * A i + E i) ≤
        cg * r j * (cg * r j * (2 * P) + cδ * (rb * r j) * (2 * P)) :=
      mul_le_mul (hG1.trans (mul_le_mul_of_nonneg_left hri' hcg)) (add_le_add t2 hE1)
        (add_nonneg (mul_nonneg hnn0 (H.hA0 _ hin.le)) (H.hE0 i hin)) (by positivity)
    have e : cg * r j ^ 2 * (2 * P) + cg * r j * (cg * r j * (2 * P) + cδ * (rb * r j) * (2 * P)) =
        X * (4 / 3) ^ (j - i) := by rw [hX, hP]; ring
    linarith
  -- the drift
  have hdrift : ∑ k ∈ range j, T k j *
      ∑ i ∈ Ico k j, (dg i * A (i + 1) + G i * (nn i * A i + E i)) ≤ 2 * Bτ * X := by
    have h1 : ∀ k ∈ range j, T k j *
        ∑ i ∈ Ico k j, (dg i * A (i + 1) + G i * (nn i * A i + E i)) ≤
        4 * Bτ * X * ((4 / 3 * q) ^ (j - k)) := by
      intro k hk
      have hkj := mem_range.1 hk
      obtain ⟨hT0, hT1⟩ := H.hT k j hkj hj
      have hs : ∑ i ∈ Ico k j, (dg i * A (i + 1) + G i * (nn i * A i + E i)) ≤
          X * (4 * (4 / 3 : ℝ) ^ (j - k)) := by
        refine (sum_le_sum fun i hi => hterm i (mem_Ico.1 hi).2).trans ?_
        rw [← mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hX0
        have := geom_Ico_le j hkj.le
        linarith
      calc _ ≤ T k j * (X * (4 * (4 / 3 : ℝ) ^ (j - k))) := mul_le_mul_of_nonneg_left hs hT0
        _ ≤ Bτ * q ^ (j - k) * (X * (4 * (4 / 3 : ℝ) ^ (j - k))) :=
            mul_le_mul_of_nonneg_right hT1 (by positivity)
        _ = 4 * Bτ * X * ((4 / 3 * q) ^ (j - k)) := by rw [mul_pow]; ring
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum]
    have hg := geom_tail_le (y := 4 / 3 * q) (by have := H.hq0; positivity)
      (by have := H.hq; linarith) j
    have : 0 ≤ 4 * Bτ * X := by have := H.hBτ; positivity
    nlinarith
  -- the product parts
  have hprod : Pr j ≤ 3 * cP * cW * r j ^ 2 * b j := by
    refine hPrj.trans ?_
    have hc : 0 ≤ cW := hcW0
    have h1 : ∀ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (2 * cW * b i)) ≤
        2 * cW * r j ^ 2 * b j * (4 / 3 * q) ^ (j - i) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
      have hr2 : r i ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ (H.hr0 i (by omega)) (hri i hij) 2
      have hbb := hbi i hij
      have h2 : r i ^ 2 * (2 * cW * b i) ≤
          r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * b j)) :=
        mul_le_mul hr2 (mul_le_mul_of_nonneg_left hbb (by positivity))
          (by have := H.hb i (by omega); positivity) (sq_nonneg _)
      calc _ ≤ q ^ (j - i) * (r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * b j))) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg H.hq0 _)
        _ = _ := by rw [mul_pow]; ring
    have h2 := sum_le_sum h1
    rw [← mul_sum] at h2
    have hg := geom_tail_le' (y := 4 / 3 * q) (by have := H.hq0; positivity)
      (by have := H.hq; linarith) j
    have h3 : 0 ≤ 2 * cW * r j ^ 2 * b j :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) (sq_nonneg _)) hbj
    have h4 := mul_le_mul_of_nonneg_left hg h3
    have h5 := mul_le_mul_of_nonneg_left (h2.trans h4) H.hcP
    nlinarith
  have hE := H.hE j hj
  have hsum : E j ≤ (16 * cK * cW * Bk + 3 * cP * cW +
      4 * Bτ * cg * (1 + cg) + 4 * Bτ * cg * cδ * rb) * (r j ^ 2 * b j) := by
    have e : 2 * Bτ * X = (4 * Bτ * cg * (1 + cg) + 4 * Bτ * cg * cδ * rb) * (r j ^ 2 * b j) := by
      rw [hX]; ring
    nlinarith
  have hrb2 : 0 ≤ r j ^ 2 * b j := by positivity
  have h6 := mul_le_mul_of_nonneg_right H.hcδ hrb2
  have ha := (H.ha j hj).1
  have h7 : 6 / 7 * cδ * (r j ^ 2 * b j) ≤ cδ * r j ^ 2 * (a j * b j) := by
    have := mul_le_mul_of_nonneg_left ha (mul_nonneg hcδ0 hrb2)
    nlinarith
  linarith

/-- The bounds at scale `j` of the induction. -/
def Base (H : RelRec n b A D E a s r Kt Pr dg G nn θW θK T Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ)
    (j : ℕ) : Prop :=
  0 < b j ∧ D j ≤ 6 * (cδ * ∑ k ∈ range j, r k ^ 2) * b j ∧
    Wb j (cW * r j * (2 * s j * b j)) ∧
    Kb j (16 * cW * Bk * r j ^ 2 * (s j * b j))

/-- **The relative coupled recursion closes.** -/
theorem close : ∀ j ≤ n, (∀ i ≤ j, H.Base i) ∧
    (∀ i < j, E i ≤ cδ * r i ^ 2 * (a i * b i)) := by
  have hcW : 1 ≤ cW := H.hcW1
  have hcW0 : 0 ≤ cW := by linarith
  have hBk := H.hBk
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    obtain rfl : i = 0 := by omega
    refine ⟨H.hb0, by rw [H.hD0]; simp, H.hWm 0 0 _ H.hW0 ?_, H.hKm 0 0 _ H.hK0 ?_⟩
    · have := H.hr0 0 (Nat.zero_le _); have := H.hs 0 (Nat.zero_le _); have := H.hb0
      positivity
    · have := H.hs 0 (Nat.zero_le _); have := H.hb0; positivity
  | succ j ih =>
    intro hj1
    have hj : j < n := by omega
    obtain ⟨hB, hEs⟩ := ih hj.le
    -- one-step ratio of `b`
    have hstep : ∀ l < j, b l ≤ 4 / 3 * b (l + 1) := by
      intro l hl
      have hln : l < n := by omega
      have h1 := H.hbstep l hln
      have h2 := hEs l hl
      have h3 := H.rsq_le hln
      obtain ⟨ha1, -⟩ := H.ha l hln
      have hbl := H.hb l (by omega)
      have h4 : a l * b l * (1 - cδ * r l ^ 2) ≤ b (l + 1) := by
        linarith [show a l * b l * (1 - cδ * r l ^ 2) = a l * b l - cδ * r l ^ 2 * (a l * b l) by ring]
      have hx : 3 / 4 ≤ a l * (1 - cδ * r l ^ 2) := by
        have := mul_le_mul ha1 (show 7 / 8 ≤ 1 - cδ * r l ^ 2 by linarith) (by norm_num)
          (by linarith)
        linarith
      have h5 : 3 / 4 * b l ≤ a l * b l * (1 - cδ * r l ^ 2) := by
        have := mul_le_mul_of_nonneg_right hx hbl
        linarith [show a l * b l * (1 - cδ * r l ^ 2) = a l * (1 - cδ * r l ^ 2) * b l by ring]
      linarith
    have hbi := le_pow_mul_of_step (by norm_num : (0 : ℝ) ≤ 4 / 3) hstep
    have hri : ∀ i ≤ j, r i ≤ r j := by
      have := le_pow_mul_of_step (x := r) (by norm_num : (0 : ℝ) ≤ 1)
        (j := j) (fun l hl => by rw [one_mul]; exact H.hrm l (by omega))
      intro i hi; simpa using this i hi
    have hAi : ∀ i ≤ j, A i ≤ 2 * b i := by
      intro i hi
      obtain ⟨hbp, hD, -, -⟩ := hB i hi
      have h1 := H.hA i (by omega)
      have h2 := H.sum_le (j := i) (by omega)
      nlinarith
    obtain ⟨hbj, hDj, hWj, hKj⟩ := hB j le_rfl
    have hsj := H.hs j hj.le
    have hrj := H.hr0 j hj.le
    -- the activity term
    have hKtj : Kt j ≤ 16 * cK * cW * Bk * r j ^ 2 * b j := by
      refine (H.hKt j hj _ (by positivity) hKj).trans (le_of_eq ?_)
      field_simp
    -- the product parts
    have hPrj : Pr j ≤ cP * ∑ i ∈ range (j + 1), q ^ (j - i) *
        (r i ^ 2 * (2 * cW * b i)) := by
      have h := H.hPr j hj (fun i => cW * (2 * s i * b i)) fun i hi => by
        obtain ⟨hbp, -, hW, -⟩ := hB i hi
        have hsi := H.hs i (by omega)
        refine ⟨by positivity, ?_, H.hWm i _ _ hW (le_of_eq (by ring))⟩
        have h1 : s i * A i ≤ s i * (2 * b i) := mul_le_mul_of_nonneg_left (hAi i hi) hsi.le
        have h2 : 2 * s i * b i ≤ cW * (2 * s i * b i) :=
          le_mul_of_one_le_left (by positivity) hcW
        linarith [show s i * (2 * b i) = 2 * s i * b i by ring]
      refine h.trans (le_of_eq ?_)
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have hsi := H.hs i (by have := mem_range.1 hi; omega)
      field_simp
    have hEj := H.E_le hj hbi hAi hEs hri hKtj hPrj
    have hEs' : ∀ i < j + 1, E i ≤ cδ * r i ^ 2 * (a i * b i) := by
      intro i hi
      rcases Nat.lt_or_ge i j with h | h
      · exact hEs i h
      · obtain rfl : i = j := by omega
        exact hEj
    refine ⟨fun i hi => ?_, hEs'⟩
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact hB i (by omega)
    obtain rfl : i = j + 1 := by omega
    -- the new scale
    have hδ := H.rsq_le hj
    obtain ⟨ha1, ha2⟩ := H.ha j hj
    have hE0 := H.hE0 j hj
    have hb1 : a j * b j * (1 - cδ * r j ^ 2) ≤ b (j + 1) := by
      have := H.hbstep j hj
      linarith [show a j * b j * (1 - cδ * r j ^ 2) = a j * b j - cδ * r j ^ 2 * (a j * b j) by ring]
    have hb1' : 3 / 4 * b j ≤ b (j + 1) := by
      have hx : 3 / 4 ≤ a j * (1 - cδ * r j ^ 2) := by
        have := mul_le_mul ha1 (show 7 / 8 ≤ 1 - cδ * r j ^ 2 by linarith) (by norm_num)
          (by linarith)
        linarith
      have := mul_le_mul_of_nonneg_right hx hbj.le
      linarith [show a j * b j * (1 - cδ * r j ^ 2) = a j * (1 - cδ * r j ^ 2) * b j by ring]
    have hbpos : 0 < b (j + 1) := by linarith
    have hsj1 := H.hs (j + 1) hj1
    have hss := H.hss j hj
    have hsb : s j * b j ≤ 8 / 5 * (s (j + 1) * b (j + 1)) := by
      have h1 : s j * b j ≤ 6 / 5 * s (j + 1) * (4 / 3 * b (j + 1)) :=
        mul_le_mul hss (by linarith) hbj.le (by positivity)
      linarith
    have hrm := H.hrm j hj
    refine ⟨hbpos, ?_, ?_, ?_⟩
    · -- the deviation
      have hS := H.sum_le (j := j + 1) hj1
      rw [sum_range_succ, mul_add] at hS ⊢
      set S := cδ * ∑ k ∈ range j, r k ^ 2
      have hS0 : 0 ≤ S := mul_nonneg H.hcδ0 (sum_nonneg fun _ _ => sq_nonneg _)
      have hδ0 : 0 ≤ cδ * r j ^ 2 := mul_nonneg H.hcδ0 (sq_nonneg _)
      have hD1 : D (j + 1) ≤ a j * b j * (6 * S + 2 * (cδ * r j ^ 2)) := by
        have h1 := H.hDstep j hj
        have h2 : a j * D j ≤ a j * (6 * S * b j) := mul_le_mul_of_nonneg_left hDj (by linarith)
        nlinarith
      have hkey : 6 * S + 2 * (cδ * r j ^ 2) ≤
          6 * (S + cδ * r j ^ 2) * (1 - cδ * r j ^ 2) := by nlinarith
      have hab : 0 ≤ a j * b j := by nlinarith
      calc D (j + 1) ≤ a j * b j * (6 * S + 2 * (cδ * r j ^ 2)) := hD1
        _ ≤ a j * b j * (6 * (S + cδ * r j ^ 2) * (1 - cδ * r j ^ 2)) :=
            mul_le_mul_of_nonneg_left hkey hab
        _ = 6 * (S + cδ * r j ^ 2) * (a j * b j * (1 - cδ * r j ^ 2)) := by ring
        _ ≤ 6 * (S + cδ * r j ^ 2) * b (j + 1) :=
            mul_le_mul_of_nonneg_left hb1 (by positivity)
    · -- `𝒲^{obs}`
      have hAj := hAi j le_rfl
      have hm : s j * A j ≤ 2 * s j * b j := by
        have := mul_le_mul_of_nonneg_left hAj hsj.le
        linarith [show s j * (2 * b j) = 2 * s j * b j by ring]
      have h := H.hW j hj (2 * s j * b j) _ (by positivity) (by positivity) hm hWj
      refine H.hWm _ _ _ h ?_
      have hθ := H.hθW j hj
      have hC₁ := H.hC₁
      have hw0 : 0 ≤ cW * r j * (2 * s j * b j) := by positivity
      have h1 : θW j * (cW * r j * (2 * s j * b j)) ≤
          1 / 6 * (cW * r j * (2 * s j * b j)) := by
        exact mul_le_mul_of_nonneg_right hθ hw0
      have h2 : r j * (s j * b j) ≤ r (j + 1) * (8 / 5 * (s (j + 1) * b (j + 1))) :=
        mul_le_mul hrm hsb (by positivity) (by linarith)
      have e : 1 / 6 * (cW * r j * (2 * s j * b j)) + C₁ * r j * (2 * s j * b j) =
          (cW / 6 + C₁) * 2 * (r j * (s j * b j)) := by ring
      have h3 : (cW / 6 + C₁) * 2 * (r j * (s j * b j)) ≤
          (cW / 6 + C₁) * 2 * (r (j + 1) * (8 / 5 * (s (j + 1) * b (j + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (cW / 6 + C₁) * 2 * (r (j + 1) * (8 / 5 * (s (j + 1) * b (j + 1)))) ≤
          cW * r (j + 1) * (2 * s (j + 1) * b (j + 1)) := by
        have hY : 0 ≤ r (j + 1) * (s (j + 1) * b (j + 1)) := by
          have := H.hr0 (j + 1) hj1; positivity
        have hc : (cW / 6 + C₁) * 2 * (8 / 5) ≤ 2 * cW := by have := H.hcWC; linarith
        have := mul_le_mul_of_nonneg_right hc hY
        linarith [show (cW / 6 + C₁) * 2 * (r (j + 1) * (8 / 5 * (s (j + 1) * b (j + 1)))) =
          (cW / 6 + C₁) * 2 * (8 / 5) * (r (j + 1) * (s (j + 1) * b (j + 1))) by ring,
          show cW * r (j + 1) * (2 * s (j + 1) * b (j + 1)) =
          2 * cW * (r (j + 1) * (s (j + 1) * b (j + 1))) by ring]
      linarith
    · -- `K^{obs}`
      have hAj := hAi j le_rfl
      have hm : s j * A j ≤ cW * (2 * s j * b j) := by
        have := mul_le_mul_of_nonneg_left hAj hsj.le
        have h2 : 2 * s j * b j ≤ cW * (2 * s j * b j) :=
          le_mul_of_one_le_left (by positivity) hcW
        linarith [show s j * (2 * b j) = 2 * s j * b j by ring]
      have hW' : Wb j (r j * (cW * (2 * s j * b j))) :=
        H.hWm j _ _ hWj (le_of_eq (by ring))
      have h8 : 8 * (16 * cW * Bk * r j ^ 2 * (s j * b j)) ≤
          64 * Bk * r j ^ 2 * (cW * (2 * s j * b j)) := le_of_eq (by ring)
      have h := H.hK j hj (cW * (2 * s j * b j))
        (16 * cW * Bk * r j ^ 2 * (s j * b j)) (by have := hbj; positivity) (by positivity) hm
        hW' hKj h8
      refine H.hKm _ _ _ h ?_
      have hθ := H.hθK j hj
      have hk0 : 0 ≤ 16 * cW * Bk * r j ^ 2 * (s j * b j) := by positivity
      have h1 : θK j * (8 * (16 * cW * Bk * r j ^ 2 * (s j * b j))) ≤
          1 / 16 * (8 * (16 * cW * Bk * r j ^ 2 * (s j * b j))) := by
        exact mul_le_mul_of_nonneg_right hθ (by positivity)
      have hr2 : r j ^ 2 ≤ r (j + 1) ^ 2 := pow_le_pow_left₀ hrj hrm 2
      have h2 : r j ^ 2 * (s j * b j) ≤ r (j + 1) ^ 2 * (8 / 5 * (s (j + 1) * b (j + 1))) :=
        mul_le_mul hr2 hsb (by positivity) (sq_nonneg _)
      have hc : 0 ≤ cW * Bk := by positivity
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hc)
      have e : 1 / 16 * (8 * (16 * cW * Bk * r j ^ 2 * (s j * b j))) +
          Bk * r j ^ 2 * (cW * (2 * s j * b j)) =
          10 * (cW * Bk) * (r j ^ 2 * (s j * b j)) := by ring
      have e2 : 10 * (cW * Bk) * (r (j + 1) ^ 2 * (8 / 5 * (s (j + 1) * b (j + 1)))) =
          16 * cW * Bk * r (j + 1) ^ 2 * (s (j + 1) * b (j + 1)) := by ring
      linarith

end RelRec

/-- `∏(1 + δ_k) ≤ e^{∑δ_k}` for `δ_k ≥ 0`. -/
theorem prod_one_add_le_exp {δ : ℕ → ℝ} (j : ℕ) (hδ : ∀ k < j, 0 ≤ δ k) :
    ∏ k ∈ range j, (1 + δ k) ≤ Real.exp (∑ k ∈ range j, δ k) := by
  rw [Real.exp_sum]
  refine prod_le_prod (fun k hk => by have := hδ k (mem_range.1 hk); linarith)
    fun k _ => ?_
  have := Real.add_one_le_exp (δ k); linarith

/-- **The product formula with relative errors**: if `x_{k+1} = x_k u_k + e_k` with
`‖e_k‖ ≤ δ_k ‖x_k u_k‖`, then `‖x_j − x_0 ∏_{k<j} u_k‖ ≤ (∏_{k<j}(1 + δ_k) − 1) ‖x_0 ∏_{k<j} u_k‖`. -/
theorem rel_prod_le {x u : ℕ → ℂ} {δ : ℕ → ℝ} {n : ℕ} (hδ : ∀ k < n, 0 ≤ δ k)
    (hx : ∀ k < n, ‖x (k + 1) - x k * u k‖ ≤ δ k * ‖x k * u k‖) :
    ∀ j ≤ n, ‖x j - x 0 * ∏ k ∈ range j, u k‖ ≤
      (∏ k ∈ range j, (1 + δ k) - 1) * ‖x 0 * ∏ k ∈ range j, u k‖ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjn : j < n := by omega
    have ih' := ih hjn.le
    set Q' := x 0 * ∏ k ∈ range j, u k
    set P := ∏ k ∈ range j, (1 + δ k)
    have hP1 : 1 ≤ P := by
      refine Finset.one_le_prod fun k hk => ?_
      have := hδ k (by have := mem_range.1 hk; omega)
      linarith
    have hδj := hδ j hjn
    have hxj : ‖x j‖ ≤ P * ‖Q'‖ := by
      have h := norm_le_norm_sub_add (x j) Q'
      nlinarith
    rw [prod_range_succ, prod_range_succ, ← mul_assoc]
    have e : x (j + 1) - Q' * u j = (x j - Q') * u j + (x (j + 1) - x j * u j) := by ring
    rw [e, norm_mul Q']
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h1 := hx j hjn
    rw [norm_mul] at h1
    have hu := norm_nonneg (u j)
    have h2 : ‖x j - Q'‖ * ‖u j‖ ≤ (P - 1) * ‖Q'‖ * ‖u j‖ := mul_le_mul_of_nonneg_right ih' hu
    have h3 : δ j * (‖x j‖ * ‖u j‖) ≤ δ j * (P * ‖Q'‖ * ‖u j‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxj hu) hδj
    have e2 : (P * (1 + δ j) - 1) * (‖Q'‖ * ‖u j‖) =
        (P - 1) * ‖Q'‖ * ‖u j‖ + δ j * (P * ‖Q'‖ * ‖u j‖) := by ring
    rw [e2]
    linarith

end Obs2
