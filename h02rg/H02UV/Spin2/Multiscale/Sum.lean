import Mathlib

/-!
# `sec:spin`, route (ii): the magnetisation sum (pure analysis)

The magnetisation of `e:PM` is `M_j = 1 - b₀ ∑_{k<j} λ̂_k Γ^int_{k+1}(0,0)`. Along the bulk flow
(`β_k = 1/ǧ_k`, `β_ε = 1/b`), `b₀ λ̂_k Γ^int_{k+1}(0,0) = (β/3) b^{1/3} ǧ_k^{2/3} (1 + O(ǧ_k + a_k))`
with `β = β_1 log L`, i.e. `(1/β_ε)(β_ε/β_k)^{2/3}(log L/2π)`. The sum is a Riemann sum for
`(1/3) β_ε^{-1/3} ∫ β^{-2/3} dβ`, and `M_j = (β_j/β_ε)^{1/3}(1 + O(ǧ_j))`.

In the cube-root variable `w_k = ǧ_k^{1/3}` (so `(β_k/β_ε)^{1/3} = w_0/w_k`) the proof is
algebraic: with `p = w_k`, `q = w_{k+1}`, `δ = 1/p³ - 1/q³ = β + O(e_k + c p³)` (the band),

  `1/p - 1/q - (β/3)p² = (δ - β) p²q²/S + β p² (q-p)(2q+p)/(3S)`,  `S = q² + pq + p²`,

so the per-step defect is `≤ p² e_k + C₁ p⁵`; and `p⁵ ≤ ((M+1)/β')(q² - p²)` from the
monotonicity `ǧ_{k+1} ≥ ǧ_k + β' ǧ_k²`, so `∑ p_k⁵ ≤ ((M+1)/β') w_j²` telescopes.

* `spin_step`: the per-step defect;
* `spin_sum_w`: the sum in the variable `w`;
* `spin_sum`: the statement in terms of `ǧ` and rpow;
* `spin_term`: the product hypothesis from separate hypotheses on `λ̂_k` and `Γ_k`;
* `near_of_log`: a complex number with controlled `log`-modulus and phase is close to its target;
* `beta_sum`: the summed band, `|1/ǧ_n - 1/ǧ_0 + nβ| ≤ ∑ e_k + c ∑ ǧ_k`.
-/

open Finset

namespace Spin2

/-- The per-step defect of the cube-root Riemann sum. -/
theorem spin_step {p q β M c E1 e : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hβ : 0 ≤ β)
    (hp1 : p ^ 3 ≤ 1) (hM : q ^ 3 ≤ M * p ^ 3) (he1 : e ≤ E1) (hc : 0 ≤ c)
    (hband : |1 / q ^ 3 - 1 / p ^ 3 + β| ≤ e + c * p ^ 3) :
    |1 / p - 1 / q - β / 3 * p ^ 2| ≤ p ^ 2 * e + (c + β * M * (β + E1 + c) / 3) * p ^ 5 := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  set S := q ^ 2 + p * q + p ^ 2 with hSd
  have hS : 0 < S := by positivity
  set δ := 1 / p ^ 3 - 1 / q ^ 3 with hδd
  have hδ : |δ - β| ≤ e + c * p ^ 3 := by
    have e1 : δ - β = -(1 / q ^ 3 - 1 / p ^ 3 + β) := by rw [hδd]; ring
    rw [e1, abs_neg]; exact hband
  have hid : 1 / p - 1 / q - β / 3 * p ^ 2 =
      (δ - β) * (p ^ 2 * q ^ 2 / S) + β * p ^ 2 * ((q - p) * (2 * q + p) / (3 * S)) := by
    rw [hδd, hSd]; field_simp; ring
  -- `q³ - p³ = δ p³ q³`
  have hcube : q ^ 3 - p ^ 3 = δ * p ^ 3 * q ^ 3 := by rw [hδd]; field_simp
  have hδu : δ ≤ β + E1 + c := by
    have h1 := (abs_le.1 hδ).2
    have h2 : c * p ^ 3 ≤ c := mul_le_of_le_one_right hc hp1
    linarith only [h1, h2, he1]
  have hqp0 : 0 ≤ q - p := by linarith only [hpq]
  -- `q - p ≤ (β+E1+c) M p⁴ / 3`
  have hqp : q - p ≤ (β + E1 + c) * M * p ^ 4 / 3 := by
    have hfac : q ^ 3 - p ^ 3 = (q - p) * S := by rw [hSd]; ring
    have h3p : (q - p) * (3 * p ^ 2) ≤ (q - p) * S := by
      refine mul_le_mul_of_nonneg_left ?_ hqp0
      rw [hSd]; nlinarith [mul_le_mul hpq hpq hp.le hq.le]
    have hp3 : 0 ≤ p ^ 3 := by positivity
    have hq3 : 0 ≤ q ^ 3 := by positivity
    have hδ0 : δ * p ^ 3 * q ^ 3 ≤ (β + E1 + c) * p ^ 3 * (M * p ^ 3) := by
      have h1 : δ * p ^ 3 * q ^ 3 = δ * (p ^ 3 * q ^ 3) := by ring
      have hδ0' : 0 ≤ δ := by
        have : 0 ≤ q ^ 3 - p ^ 3 := by rw [hfac]; exact mul_nonneg hqp0 hS.le
        rw [hcube] at this
        by_contra hneg
        push Not at hneg
        have : δ * (p ^ 3 * q ^ 3) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
        linarith
      rw [h1]
      calc δ * (p ^ 3 * q ^ 3) ≤ (β + E1 + c) * (p ^ 3 * q ^ 3) :=
            mul_le_mul_of_nonneg_right hδu (by positivity)
        _ ≤ (β + E1 + c) * (p ^ 3 * (M * p ^ 3)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hδ0', hδu])
            exact mul_le_mul_of_nonneg_left hM hp3
        _ = (β + E1 + c) * p ^ 3 * (M * p ^ 3) := by ring
    have h4 : (q - p) * (3 * p ^ 2) ≤ ((β + E1 + c) * M * p ^ 4 / 3) * (3 * p ^ 2) := by
      have e2 : ((β + E1 + c) * M * p ^ 4 / 3) * (3 * p ^ 2) =
          (β + E1 + c) * p ^ 3 * (M * p ^ 3) := by ring
      rw [e2]; linarith only [h3p, hfac, hcube, hδ0]
    exact le_of_mul_le_mul_right h4 (by positivity)
  have h1 : p ^ 2 * q ^ 2 / S ≤ p ^ 2 := by
    rw [div_le_iff₀ hS]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg p)
    rw [hSd]; nlinarith [mul_pos hp hq]
  have h10 : 0 ≤ p ^ 2 * q ^ 2 / S := by positivity
  have h2 : (q - p) * (2 * q + p) / (3 * S) ≤ (q - p) / p := by
    rw [div_le_div_iff₀ (by positivity) hp]
    have : (2 * q + p) * p ≤ 3 * S := by rw [hSd]; nlinarith [mul_pos hp hq]
    have e3 : (q - p) * (2 * q + p) * p = (q - p) * ((2 * q + p) * p) := by ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left this hqp0
  have h20 : 0 ≤ (q - p) * (2 * q + p) / (3 * S) := by
    have : 0 ≤ 2 * q + p := by positivity
    positivity
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (δ - β), abs_of_nonneg h10,
    abs_of_nonneg (mul_nonneg (mul_nonneg hβ (sq_nonneg p)) h20)]
  have hA : |δ - β| * (p ^ 2 * q ^ 2 / S) ≤ (e + c * p ^ 3) * p ^ 2 :=
    mul_le_mul hδ h1 h10 (le_trans (abs_nonneg _) hδ)
  have hB : β * p ^ 2 * ((q - p) * (2 * q + p) / (3 * S)) ≤ β * p ^ 2 * ((q - p) / p) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hB2 : β * p ^ 2 * ((q - p) / p) = β * p * (q - p) := by field_simp
  have hB3 : β * p * (q - p) ≤ β * p * ((β + E1 + c) * M * p ^ 4 / 3) :=
    mul_le_mul_of_nonneg_left hqp (by positivity)
  have e4 : p ^ 2 * e + (c + β * M * (β + E1 + c) / 3) * p ^ 5 =
      (e + c * p ^ 3) * p ^ 2 + β * p * ((β + E1 + c) * M * p ^ 4 / 3) := by ring
  rw [e4]
  linarith only [hA, hB, hB2, hB3]

/-- `p⁵ ≤ ((M+1)/β')(q² - p²)` from `q³ ≥ p³ + β' p⁶` and `q ≤ M p`. -/
theorem spin_five {p q β' M : ℝ} (hp : 0 < p) (hβ' : 0 < β') (hpq : p ≤ q) (hqM : q ≤ M * p)
    (hinc : p ^ 3 + β' * (p ^ 3) ^ 2 ≤ q ^ 3) :
    p ^ 5 ≤ (M + 1) / β' * (q ^ 2 - p ^ 2) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hM1 : 0 < M + 1 := by
    have : p ≤ M * p := hpq.trans hqM
    have : 1 ≤ M := by
      by_contra h; push Not at h
      have : M * p < 1 * p := mul_lt_mul_of_pos_right h hp
      linarith
    linarith
  have hd : 0 ≤ q ^ 2 - p ^ 2 := by nlinarith
  -- `(q² - p²)(q + p)² ≥ (q³ - p³)(q + p)`
  have h1 : (q ^ 3 - p ^ 3) * (q + p) ≤ (q ^ 2 - p ^ 2) * (q + p) ^ 2 := by
    have e : (q ^ 3 - p ^ 3) * (q + p) = (q ^ 2 - p ^ 2) * (q ^ 2 + p * q + p ^ 2) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hd
    nlinarith [mul_pos hp hq]
  have h2 : β' * p ^ 6 * (q + p) ≤ (q ^ 2 - p ^ 2) * (q + p) ^ 2 := by
    have : β' * p ^ 6 ≤ q ^ 3 - p ^ 3 := by nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right this (by positivity)) h1
  have h3 : β' * p ^ 6 ≤ (q ^ 2 - p ^ 2) * (q + p) := by
    have hqp : 0 < q + p := by positivity
    have e : (q ^ 2 - p ^ 2) * (q + p) ^ 2 = ((q ^ 2 - p ^ 2) * (q + p)) * (q + p) := by ring
    rw [e] at h2
    exact le_of_mul_le_mul_right h2 hqp
  have h4 : (q ^ 2 - p ^ 2) * (q + p) ≤ (q ^ 2 - p ^ 2) * ((M + 1) * p) := by
    refine mul_le_mul_of_nonneg_left ?_ hd
    linarith only [hqM]
  have h5 : β' * p ^ 5 * p ≤ ((M + 1) * (q ^ 2 - p ^ 2)) * p := by
    have e1 : β' * p ^ 5 * p = β' * p ^ 6 := by ring
    have e2 : ((M + 1) * (q ^ 2 - p ^ 2)) * p = (q ^ 2 - p ^ 2) * ((M + 1) * p) := by ring
    rw [e1, e2]; exact h3.trans h4
  have h6 : β' * p ^ 5 ≤ (M + 1) * (q ^ 2 - p ^ 2) := le_of_mul_le_mul_right h5 hp
  rw [div_mul_eq_mul_div, le_div_iff₀ hβ']
  linarith only [h6]

/-- The constant of `spin_sum_w`. -/
noncomputable def spinKw (β β' M c E1 B eS aS : ℝ) : ℝ :=
  (c + β * M * (β + E1 + c) / 3 + B) * ((M + 1) / β') + eS + B * aS

/-- **The magnetisation sum in the cube-root variable.** With `g_k = w_k³`:
`‖(1 - ∑_{k<j} T_k) - w_0/w_j‖ ≤ K w_0 w_j²` if `T_k = (β/3) w_0 w_k² (1 + O(w_k³ + a_k))`. -/
theorem spin_sum_w {w e a : ℕ → ℝ} {T : ℕ → ℂ} {β β' M c E1 B eS aS : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hβ' : 0 < β') (hM1 : 1 ≤ M) (hc : 0 ≤ c) (hB : 0 ≤ B) (hE1 : 0 ≤ E1)
    (hw : ∀ k ≤ n, 0 < w k) (hg1 : ∀ k < n, w k ^ 3 ≤ 1)
    (hinc : ∀ k < n, w k ^ 3 + β' * (w k ^ 3) ^ 2 ≤ w (k + 1) ^ 3)
    (hM : ∀ k < n, w (k + 1) ^ 3 ≤ M * w k ^ 3)
    (he0 : ∀ k < n, 0 ≤ e k) (he1 : ∀ k < n, e k ≤ E1) (ha : ∀ k < n, 0 ≤ a k)
    (heS : ∑ k ∈ range n, e k ≤ eS) (haS : ∑ k ∈ range n, a k ≤ aS)
    (hband : ∀ k < n, |1 / w (k + 1) ^ 3 - 1 / w k ^ 3 + β| ≤ e k + c * w k ^ 3)
    (hT : ∀ k < n, ‖T k - ((β / 3 * w 0 * w k ^ 2 : ℝ) : ℂ)‖ ≤
      B * w 0 * w k ^ 2 * (w k ^ 3 + a k)) :
    ∀ j ≤ n, ‖(1 - ∑ k ∈ range j, T k) - ((w 0 / w j : ℝ) : ℂ)‖ ≤
      spinKw β β' M c E1 B eS aS * w 0 * w j ^ 2 := by
  have hpq : ∀ k < n, w k ≤ w (k + 1) := by
    intro k hk
    have h1 : w k ^ 3 ≤ w (k + 1) ^ 3 := by
      have := hinc k hk
      have : 0 ≤ β' * (w k ^ 3) ^ 2 := by positivity
      linarith
    exact (pow_le_pow_iff_left₀ (hw k hk.le).le (hw (k + 1) hk).le (by norm_num)).1 h1
  have hmono : ∀ j ≤ n, ∀ k ≤ j, w k ≤ w j := by
    intro j hj k hk
    induction j with
    | zero => rw [Nat.le_zero.1 hk]
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with h | h
      · exact (ih (by omega) (by omega)).trans (hpq j (by omega))
      · rw [show k = j + 1 by omega]
  have hqM : ∀ k < n, w (k + 1) ≤ M * w k := by
    intro k hk
    have hp := hw k hk.le
    have h1 : w (k + 1) ^ 3 ≤ (M * w k) ^ 3 := by
      have hM3 : M ≤ M ^ 3 := by
        have h1 : M * 1 ≤ M * M ^ 2 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hM1) (by linarith)
        have e : M ^ 3 = M * M ^ 2 := by ring
        linarith
      calc w (k + 1) ^ 3 ≤ M * w k ^ 3 := hM k hk
        _ ≤ M ^ 3 * w k ^ 3 := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = (M * w k) ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ (hw (k + 1) hk).le (by positivity) (by norm_num)).1 h1
  set C1 := c + β * M * (β + E1 + c) / 3 with hC1
  have hC10 : 0 ≤ C1 := by
    have : 0 ≤ M := by linarith
    positivity
  set E : ℕ → ℝ := fun k => w 0 * (w k ^ 2 * e k + B * w k ^ 2 * a k + (C1 + B) * w k ^ 5)
    with hEd
  have hw0 := hw 0 (Nat.zero_le _)
  -- the per-step bound
  have hstep : ∀ k < n, ‖((w 0 / w k : ℝ) : ℂ) - ((w 0 / w (k + 1) : ℝ) : ℂ) - T k‖ ≤ E k := by
    intro k hk
    have hp := hw k hk.le
    have hd := spin_step hp (hpq k hk) hβ (hg1 k hk) (hM k hk) (he1 k hk) hc (hband k hk)
    rw [← hC1] at hd
    have e1 : ((w 0 / w k : ℝ) : ℂ) - ((w 0 / w (k + 1) : ℝ) : ℂ) - T k =
        ((w 0 * (1 / w k - 1 / w (k + 1) - β / 3 * w k ^ 2) : ℝ) : ℂ) -
          (T k - ((β / 3 * w 0 * w k ^ 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hw0]
    have h2 := mul_le_mul_of_nonneg_left hd hw0.le
    have h3 := hT k hk
    have hp5 : w k ^ 2 * w k ^ 3 = w k ^ 5 := by ring
    have e2 : B * w 0 * w k ^ 2 * (w k ^ 3 + a k) =
        w 0 * (B * w k ^ 2 * a k + B * w k ^ 5) := by rw [← hp5]; ring
    have e3 : E k = w 0 * (w k ^ 2 * e k + C1 * w k ^ 5) +
        w 0 * (B * w k ^ 2 * a k + B * w k ^ 5) := by rw [hEd]; ring
    rw [e3]
    linarith only [h2, h3, e2]
  -- telescoping
  have htel : ∀ j ≤ n, ‖(1 - ∑ k ∈ range j, T k) - ((w 0 / w j : ℝ) : ℂ)‖ ≤
      ∑ k ∈ range j, E k := by
    intro j hj
    induction j with
    | zero => simp [div_self hw0.ne']
    | succ j ih =>
      rw [sum_range_succ, sum_range_succ]
      have e : (1 - (∑ k ∈ range j, T k + T j)) - ((w 0 / w (j + 1) : ℝ) : ℂ) =
          ((1 - ∑ k ∈ range j, T k) - ((w 0 / w j : ℝ) : ℂ)) +
            (((w 0 / w j : ℝ) : ℂ) - ((w 0 / w (j + 1) : ℝ) : ℂ) - T j) := by ring
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (ih (by omega)) (hstep j (by omega)))
  intro j hj
  refine (htel j hj).trans ?_
  have hwj := hw j hj
  have hsum : ∑ k ∈ range j, E k = w 0 * (∑ k ∈ range j, w k ^ 2 * e k +
      B * ∑ k ∈ range j, w k ^ 2 * a k + (C1 + B) * ∑ k ∈ range j, w k ^ 5) := by
    rw [hEd]; simp only; rw [← mul_sum, sum_add_distrib, sum_add_distrib, mul_sum, mul_sum]
    congr 1; congr 1; congr 1
    · exact sum_congr rfl fun k _ => by ring
  rw [hsum]
  have hs1 : ∑ k ∈ range j, w k ^ 2 * e k ≤ w j ^ 2 * eS := by
    calc ∑ k ∈ range j, w k ^ 2 * e k ≤ ∑ k ∈ range j, w j ^ 2 * e k := by
          refine sum_le_sum fun k hk => ?_
          have hk' := mem_range.1 hk
          refine mul_le_mul_of_nonneg_right ?_ (he0 k (by omega))
          exact pow_le_pow_left₀ (hw k (by omega)).le (hmono j hj k hk'.le) 2
      _ = w j ^ 2 * ∑ k ∈ range j, e k := by rw [mul_sum]
      _ ≤ w j ^ 2 * eS := by
          refine mul_le_mul_of_nonneg_left (le_trans ?_ heS) (sq_nonneg _)
          exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj)
            (fun k hk _ => he0 k (mem_range.1 hk))
  have hs2 : ∑ k ∈ range j, w k ^ 2 * a k ≤ w j ^ 2 * aS := by
    calc ∑ k ∈ range j, w k ^ 2 * a k ≤ ∑ k ∈ range j, w j ^ 2 * a k := by
          refine sum_le_sum fun k hk => ?_
          have hk' := mem_range.1 hk
          refine mul_le_mul_of_nonneg_right ?_ (ha k (by omega))
          exact pow_le_pow_left₀ (hw k (by omega)).le (hmono j hj k hk'.le) 2
      _ = w j ^ 2 * ∑ k ∈ range j, a k := by rw [mul_sum]
      _ ≤ w j ^ 2 * aS := by
          refine mul_le_mul_of_nonneg_left (le_trans ?_ haS) (sq_nonneg _)
          exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj)
            (fun k hk _ => ha k (mem_range.1 hk))
  have hs3 : ∑ k ∈ range j, w k ^ 5 ≤ (M + 1) / β' * w j ^ 2 := by
    calc ∑ k ∈ range j, w k ^ 5 ≤ ∑ k ∈ range j, (M + 1) / β' * (w (k + 1) ^ 2 - w k ^ 2) :=
          sum_le_sum fun k hk => by
            have hk' := mem_range.1 hk
            exact spin_five (hw k (by omega)) hβ' (hpq k (by omega)) (hqM k (by omega))
              (hinc k (by omega))
      _ = (M + 1) / β' * (w j ^ 2 - w 0 ^ 2) := by
          rw [← mul_sum, sum_range_sub (fun k => w k ^ 2)]
      _ ≤ (M + 1) / β' * w j ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := sq_nonneg (w 0); linarith
  have hfin : ∑ k ∈ range j, w k ^ 2 * e k + B * ∑ k ∈ range j, w k ^ 2 * a k +
      (C1 + B) * ∑ k ∈ range j, w k ^ 5 ≤ spinKw β β' M c E1 B eS aS * w j ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_left hs2 hB
    have h3 := mul_le_mul_of_nonneg_left hs3 (by positivity : (0 : ℝ) ≤ C1 + B)
    have e : spinKw β β' M c E1 B eS aS * w j ^ 2 =
        w j ^ 2 * eS + B * (w j ^ 2 * aS) + (C1 + B) * ((M + 1) / β' * w j ^ 2) := by
      unfold spinKw; rw [hC1]; ring
    rw [e]
    linarith only [hs1, h2, h3]
  have := mul_le_mul_of_nonneg_left hfin hw0.le
  linarith only [this]

theorem cbrt_pos {x : ℝ} (hx : 0 < x) : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx _

theorem cbrt_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- The constant of `spin_sum`. -/
noncomputable def spinK (β β' M c E1 B eS aS : ℝ) : ℝ := spinKw β β' M c E1 B eS aS

/-- **The magnetisation sum** (`sec:spin` (ii)): along a marginal flow `ǧ_k` (`ǧ_0 = b`,
monotone, band `|1/ǧ_{k+1} - 1/ǧ_k + β| ≤ e_k + c ǧ_k`), if
`‖T_k - (β/3) b r_k²‖ ≤ B b r_k² (ǧ_k + a_k)` with `r_k = (ǧ_k/b)^{1/3} = (β_ε/β_k)^{1/3}`, then
`M_j = 1 - ∑_{k<j} T_k` satisfies `‖M_j - (b/ǧ_j)^{1/3}‖ ≤ K (b/ǧ_j)^{1/3} ǧ_j`, i.e.
`M_j = (β_j/β_ε)^{1/3}(1 + O(β_j^{-1}))`. -/
theorem spin_sum {g e a : ℕ → ℝ} {T : ℕ → ℂ} {β β' M c E1 B eS aS : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hβ' : 0 < β') (hM1 : 1 ≤ M) (hc : 0 ≤ c) (hB : 0 ≤ B) (hE1 : 0 ≤ E1)
    (hg : ∀ k ≤ n, 0 < g k) (hg1 : ∀ k < n, g k ≤ 1)
    (hinc : ∀ k < n, g k + β' * g k ^ 2 ≤ g (k + 1))
    (hM : ∀ k < n, g (k + 1) ≤ M * g k)
    (he0 : ∀ k < n, 0 ≤ e k) (he1 : ∀ k < n, e k ≤ E1) (ha : ∀ k < n, 0 ≤ a k)
    (heS : ∑ k ∈ range n, e k ≤ eS) (haS : ∑ k ∈ range n, a k ≤ aS)
    (hband : ∀ k < n, |1 / g (k + 1) - 1 / g k + β| ≤ e k + c * g k)
    (hT : ∀ k < n, ‖T k - ((β / 3 * g 0 * ((g k / g 0) ^ (1 / 3 : ℝ)) ^ 2 : ℝ) : ℂ)‖ ≤
      B * g 0 * ((g k / g 0) ^ (1 / 3 : ℝ)) ^ 2 * (g k + a k)) :
    ∀ j ≤ n, ‖(1 - ∑ k ∈ range j, T k) - (((g 0 / g j) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinK β β' M c E1 B eS aS * (g 0 / g j) ^ (1 / 3 : ℝ) * g j := by
  set w : ℕ → ℝ := fun k => g k ^ (1 / 3 : ℝ) with hwd
  have hw : ∀ k ≤ n, 0 < w k := fun k hk => cbrt_pos (hg k hk)
  have hw3 : ∀ k ≤ n, w k ^ 3 = g k := fun k hk => cbrt_cube (hg k hk).le
  have hg0 := hg 0 (Nat.zero_le _)
  have hr : ∀ k ≤ n, (g k / g 0) ^ (1 / 3 : ℝ) = w k / w 0 := fun k hk =>
    Real.div_rpow (hg k hk).le hg0.le _
  have key := spin_sum_w (w := w) (e := e) (a := a) (T := T) (n := n) hβ hβ' hM1 hc hB hE1 hw
    (fun k hk => by rw [hw3 k hk.le]; exact hg1 k hk)
    (fun k hk => by rw [hw3 k hk.le, hw3 (k + 1) hk]; exact hinc k hk)
    (fun k hk => by rw [hw3 k hk.le, hw3 (k + 1) hk]; exact hM k hk)
    he0 he1 ha heS haS
    (fun k hk => by rw [hw3 k hk.le, hw3 (k + 1) hk]; exact hband k hk)
    (fun k hk => by
      have h := hT k hk
      have hw0 := hw 0 (Nat.zero_le _)
      have e1 : g 0 * ((g k / g 0) ^ (1 / 3 : ℝ)) ^ 2 = w 0 * w k ^ 2 := by
        rw [hr k hk.le, ← hw3 0 (Nat.zero_le _)]; field_simp
      have e2 : β / 3 * g 0 * ((g k / g 0) ^ (1 / 3 : ℝ)) ^ 2 = β / 3 * w 0 * w k ^ 2 := by
        rw [mul_assoc, e1]; ring
      have e3 : B * g 0 * ((g k / g 0) ^ (1 / 3 : ℝ)) ^ 2 * (g k + a k) =
          B * w 0 * w k ^ 2 * (w k ^ 3 + a k) := by
        rw [mul_assoc B, e1, hw3 k hk.le]; ring
      rw [e2, e3] at h; exact h)
  intro j hj
  have h := key j hj
  have hwj := hw j hj
  have hw0 := hw 0 (Nat.zero_le _)
  have e1 : (g 0 / g j) ^ (1 / 3 : ℝ) = w 0 / w j := Real.div_rpow hg0.le (hg j hj).le _
  rw [e1]
  have e2 : spinK β β' M c E1 B eS aS * (w 0 / w j) * g j =
      spinKw β β' M c E1 B eS aS * w 0 * w j ^ 2 := by
    rw [← hw3 j hj]; unfold spinK; field_simp
  rw [e2]; exact h

/-- **The summand from separate hypotheses on the vertex and the covariance**: if
`‖λ - r‖ ≤ K_λ r (g + a)` and `‖Γ - γ r‖ ≤ K_Γ r (g + a)` with `g + a ≤ 3`, then
`‖b λ Γ - γ b r²‖ ≤ (K_λ(γ + 3K_Γ) + K_Γ) b r² (g + a)`. -/
theorem spin_term {lam Gam : ℂ} {r γ b g a Kl KG : ℝ} (hr : 0 ≤ r) (hγ : 0 ≤ γ) (hb : 0 ≤ b)
    (hKl : 0 ≤ Kl) (hKG : 0 ≤ KG) (hga0 : 0 ≤ g + a) (hga : g + a ≤ 3)
    (hl : ‖lam - r‖ ≤ Kl * r * (g + a)) (hG : ‖Gam - ((γ * r : ℝ) : ℂ)‖ ≤ KG * r * (g + a)) :
    ‖(b : ℂ) * lam * Gam - ((γ * b * r ^ 2 : ℝ) : ℂ)‖ ≤
      (Kl * (γ + 3 * KG) + KG) * b * r ^ 2 * (g + a) := by
  have hGn : ‖Gam‖ ≤ r * (γ + 3 * KG) := by
    have h1 : ‖Gam‖ ≤ ‖((γ * r : ℝ) : ℂ)‖ + KG * r * (g + a) := by
      have := norm_le_norm_add_norm_sub' Gam ((γ * r : ℝ) : ℂ)
      linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have h2 : KG * r * (g + a) ≤ KG * r * 3 := mul_le_mul_of_nonneg_left hga (by positivity)
    linarith
  have e : (b : ℂ) * lam * Gam - ((γ * b * r ^ 2 : ℝ) : ℂ) =
      (b : ℂ) * ((lam - r) * Gam + (r : ℂ) * (Gam - ((γ * r : ℝ) : ℂ))) := by push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  have h1 : ‖(lam - r) * Gam + (r : ℂ) * (Gam - ((γ * r : ℝ) : ℂ))‖ ≤
      Kl * r * (g + a) * (r * (γ + 3 * KG)) + r * (KG * r * (g + a)) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul hl hGn (norm_nonneg _) (by positivity)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_left hG hr
  have e2 : (Kl * (γ + 3 * KG) + KG) * b * r ^ 2 * (g + a) =
      b * (Kl * r * (g + a) * (r * (γ + 3 * KG)) + r * (KG * r * (g + a))) := by ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left h1 hb

/-- `|e^w - 1| ≤ |w| e^{|w|}`. -/
theorem abs_exp_sub_one_le' (w : ℝ) : |Real.exp w - 1| ≤ |w| * Real.exp |w| := by
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw, abs_of_nonneg (by linarith [Real.add_one_le_exp w])]
    have h1 := Real.add_one_le_exp (-w)
    have h2 : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
    have h3 : (-w + 1) * Real.exp w ≤ Real.exp (-w) * Real.exp w :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos w).le
    linarith
  · rw [abs_of_nonpos hw, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 hw])]
    have h1 := Real.add_one_le_exp w
    have h2 : 1 ≤ Real.exp (-w) := Real.one_le_exp (by linarith)
    have h3 : -w * 1 ≤ -w * Real.exp (-w) := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith

/-- **Modulus and phase**: if `|log‖x‖ - log r| ≤ K g` and `‖x - ‖x‖‖ ≤ K_φ g ‖x‖`
(`0 ≤ g ≤ 1`), then `‖x - r‖ ≤ (K + K_φ) e^K r g`. -/
theorem near_of_log {x : ℂ} {r g K Kp : ℝ} (hx : x ≠ 0) (hr : 0 < r) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hKp : 0 ≤ Kp) (hlog : |Real.log ‖x‖ - Real.log r| ≤ K * g)
    (hph : ‖x - (‖x‖ : ℂ)‖ ≤ Kp * g * ‖x‖) :
    ‖x - (r : ℂ)‖ ≤ (K + Kp) * Real.exp K * r * g := by
  set u := Real.log ‖x‖ - Real.log r with hud
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hxr : ‖x‖ = r * Real.exp u := by
    rw [hud, Real.exp_sub, Real.exp_log hxn, Real.exp_log hr]; field_simp
  have hKg : K * g ≤ K := mul_le_of_le_one_right hK hg1
  have hu : |u| ≤ K := hlog.trans hKg
  have hex : Real.exp |u| ≤ Real.exp K := Real.exp_le_exp.2 hu
  have hexu : Real.exp u ≤ Real.exp K := (Real.exp_le_exp.2 (le_abs_self u)).trans hex
  have h1 : |‖x‖ - r| ≤ K * g * Real.exp K * r := by
    have e : ‖x‖ - r = r * (Real.exp u - 1) := by rw [hxr]; ring
    rw [e, abs_mul, abs_of_pos hr]
    have := abs_exp_sub_one_le' u
    have h2 : |u| * Real.exp |u| ≤ K * g * Real.exp K :=
      mul_le_mul hlog hex (Real.exp_pos _).le (by positivity)
    have h3 : r * |Real.exp u - 1| ≤ r * (K * g * Real.exp K) :=
      mul_le_mul_of_nonneg_left (this.trans h2) hr.le
    linarith
  have h2 : ‖x‖ ≤ r * Real.exp K := by
    rw [hxr]; exact mul_le_mul_of_nonneg_left hexu hr.le
  have e : x - (r : ℂ) = (x - (‖x‖ : ℂ)) + (((‖x‖ - r : ℝ)) : ℂ) := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h3 : Kp * g * ‖x‖ ≤ Kp * g * (r * Real.exp K) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e2 : (K + Kp) * Real.exp K * r * g = K * g * Real.exp K * r + Kp * g * (r * Real.exp K) := by
    ring
  rw [e2]
  linarith only [hph, h3, h1]

/-- The phase of `Z⁻¹` is that of `Z`: `‖Z - ‖Z‖‖ ≤ K ‖Z‖ → ‖Z⁻¹ - ‖Z⁻¹‖‖ ≤ K ‖Z⁻¹‖`. -/
theorem phase_inv {Z : ℂ} {K : ℝ} (hZ : Z ≠ 0) (h : ‖Z - (‖Z‖ : ℂ)‖ ≤ K * ‖Z‖) :
    ‖Z⁻¹ - (‖Z⁻¹‖ : ℂ)‖ ≤ K * ‖Z⁻¹‖ := by
  have hn : (‖Z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hZ).ne'
  have e : Z⁻¹ - (‖Z⁻¹‖ : ℂ) = -((Z - (‖Z‖ : ℂ)) * Z⁻¹ * (‖Z‖ : ℂ)⁻¹) := by
    rw [norm_inv]; push_cast; field_simp; ring
  rw [e, norm_neg, norm_mul, norm_mul]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  calc ‖Z - (‖Z‖ : ℂ)‖ * ‖Z‖⁻¹ * ‖Z‖⁻¹ ≤ K * ‖Z‖ * ‖Z‖⁻¹ * ‖Z‖⁻¹ := by
        gcongr
    _ = K * ‖Z‖⁻¹ := by field_simp

/-- **The summed band** (`thm:beta`, the running coupling): `|1/g_n - 1/g_0 + nβ| ≤ ∑ e_k + c ∑ g_k`. -/
theorem beta_sum {g e : ℕ → ℝ} {β c : ℝ} {n : ℕ}
    (hband : ∀ k < n, |1 / g (k + 1) - 1 / g k + β| ≤ e k + c * g k) :
    |1 / g n - 1 / g 0 + n * β| ≤ ∑ k ∈ range n, e k + c * ∑ k ∈ range n, g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun k hk => hband k (by omega)
    rw [sum_range_succ, sum_range_succ, mul_add]
    have e : 1 / g (n + 1) - 1 / g 0 + ((n + 1 : ℕ) : ℝ) * β =
        (1 / g n - 1 / g 0 + n * β) + (1 / g (n + 1) - 1 / g n + β) := by push_cast; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have := hband n (by omega)
    linarith

end Spin2
