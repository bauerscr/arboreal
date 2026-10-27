import Mathlib

/-!
# Summing a marginal flow against `log g` (pure analysis, for `prop:gamma`)

Let `g_k > 0` be a marginal coupling with `g_{k+1} ≥ g_k + β' g_k²`, `g_{k+1} ≤ M g_k`, `g_k ≤ 1`, and
the band `|1/g_{k+1} - 1/g_k + β| ≤ e_k + c g_k` (`e_k` summable). If a quantity `y_k` moves by
`-σ g_k` per step up to a telescoping part `p_{k+1} - p_k` and an error `A(g_k² + g_k a_k)`, then
(`log_sum_bound`)

  `|y_n - y_0 - (p_n - p_0) + (σ/β) log(g_n/g_0)| ≤ K g_n`,

`K = (A + (|σ|/β)(M(β + E₁ + c)² + c))/β' + ∑_{k<n} (A a_k + (|σ|/β) e_k)`.

The mechanism: `β g_k = 1 - g_k/g_{k+1} + O(g_k(e_k + c g_k))` (band) and
`log(g_{k+1}/g_k) = 1 - g_k/g_{k+1} + O(g_k²)`; the `g_k²` are summed by
`∑_{k<n} g_k² ≤ (g_n - g_0)/β'` (`sum_sq_le`), and `g_k ≤ g_n` (`g_le_of_inc`).

Also `log_norm_one_add`: `|log‖1 + x‖ - Re x| ≤ 7‖x‖²` for complex `‖x‖ ≤ 1/4`.

Used with `σ = β/3` for `log |Z_j|` (`Step2/Flow/ZetaSharp*.lean`) and `σ = 0`, `σ = -β/3` for the
observable vertices `λ^{(1)}`, `λ^{(2)}` (`Obs2/Flow/Gamma*.lean`).
-/

open Finset

namespace Step2

/-- Monotonicity from `g_{k+1} ≥ g_k + β' g_k²`. -/
theorem g_le_of_inc {g : ℕ → ℝ} {β' : ℝ} {n : ℕ} (hβ' : 0 ≤ β')
    (hinc : ∀ k < n, g k + β' * g k ^ 2 ≤ g (k + 1)) : ∀ k ≤ n, g k ≤ g n := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    have h1 := ih (fun i hi => hinc i (by omega)) (by omega)
    have h2 := hinc (k + m) (by omega)
    have h3 : 0 ≤ β' * g (k + m) ^ 2 := mul_nonneg hβ' (sq_nonneg _)
    rw [← add_assoc]
    linarith only [h1, h2, h3]

/-- `∑_{k<n} g_k² ≤ (g_n - g_0)/β'`. -/
theorem sum_sq_le {g : ℕ → ℝ} {β' : ℝ} (hβ' : 0 < β') :
    ∀ n : ℕ, (∀ k < n, g k + β' * g k ^ 2 ≤ g (k + 1)) →
      ∑ k ∈ range n, g k ^ 2 ≤ (g n - g 0) / β'
  | 0, _ => by simp
  | n + 1, h => by
    rw [sum_range_succ]
    have ih := sum_sq_le hβ' n (fun k hk => h k (by omega))
    have h1 := h n (by omega)
    have h2 : g n ^ 2 ≤ (g (n + 1) - g n) / β' := by
      rw [le_div_iff₀ hβ']; linarith only [h1]
    have e : (g n - g 0) / β' + (g (n + 1) - g n) / β' = (g (n + 1) - g 0) / β' := by ring
    linarith only [ih, h2, e]

/-- `|log(1/(1-u)) - u| ≤ u²/(1-u)` for `0 ≤ u < 1`. -/
theorem log_inv_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    |-Real.log (1 - u) - u| ≤ u ^ 2 / (1 - u) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := u) (by rw [abs_of_nonneg hu0]; exact hu1) 1
  simp only [range_one, sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one] at h
  rw [abs_of_nonneg hu0] at h
  have e : -Real.log (1 - u) - u = -(u + Real.log (1 - u)) := by ring
  rw [e, abs_neg]
  have e2 : u ^ (1 + 1) = u ^ 2 := by norm_num
  rw [e2] at h
  exact h

/-- **One step**: `|log(g'/g) - β g| ≤ M B₁² g² + e g + c g²` with `B₁ = β + E₁ + c`. -/
theorem log_step {g g' β M c e E1 : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hgg : g ≤ g')
    (hM : g' ≤ M * g) (he0 : 0 ≤ e) (he : e ≤ E1) (hc : 0 ≤ c)
    (hband : |1 / g' - 1 / g + β| ≤ e + c * g) :
    |Real.log (g' / g) - β * g| ≤ M * (β + E1 + c) ^ 2 * g ^ 2 + e * g + c * g ^ 2 := by
  have hg' : 0 < g' := lt_of_lt_of_le hg hgg
  set u := 1 - g / g' with hu
  have hu0 : 0 ≤ u := by
    rw [hu, sub_nonneg, div_le_one hg']; exact hgg
  have hu1 : u < 1 := by
    rw [hu]; have : 0 < g / g' := div_pos hg hg'; linarith
  have hlog : Real.log (g' / g) = -Real.log (1 - u) := by
    rw [hu, sub_sub_cancel, Real.log_div hg.ne' hg'.ne', Real.log_div hg'.ne' hg.ne']; ring
  have hug : u = g * (1 / g - 1 / g') := by
    rw [hu, mul_sub, mul_one_div_cancel hg.ne', mul_one_div]
  -- `u - β g`
  have h1 : |u - β * g| ≤ g * (e + c * g) := by
    have e1 : u - β * g = -(g * (1 / g' - 1 / g + β)) := by rw [hug]; ring
    rw [e1, abs_neg, abs_mul, abs_of_pos hg]
    exact mul_le_mul_of_nonneg_left hband hg.le
  -- `u ≤ B₁ g`
  have hB : 1 / g - 1 / g' ≤ β + E1 + c := by
    have := (abs_le.1 hband).1
    have h2 : c * g ≤ c := mul_le_of_le_one_right hc hg1
    linarith only [this, he, h2]
  have hub : u ≤ g * (β + E1 + c) := by rw [hug]; exact mul_le_mul_of_nonneg_left hB hg.le
  -- the log
  have h2 := log_inv_sub_le hu0 hu1
  have hinv : 1 / (1 - u) = g' / g := by rw [hu, sub_sub_cancel, one_div_div]
  have h3 : u ^ 2 / (1 - u) ≤ M * (β + E1 + c) ^ 2 * g ^ 2 := by
    rw [div_eq_mul_one_div, hinv]
    have hgM : g' / g ≤ M := by rw [div_le_iff₀ hg]; linarith only [hM]
    have hu2 : u ^ 2 ≤ (g * (β + E1 + c)) ^ 2 := pow_le_pow_left₀ hu0 hub 2
    have hM0 : 0 ≤ M := by
      have : 0 ≤ g' / g := (div_pos hg' hg).le
      linarith only [this, hgM]
    calc u ^ 2 * (g' / g) ≤ (g * (β + E1 + c)) ^ 2 * M :=
          mul_le_mul hu2 hgM (div_pos hg' hg).le (sq_nonneg _)
      _ = M * (β + E1 + c) ^ 2 * g ^ 2 := by ring
  rw [hlog]
  have e3 : -Real.log (1 - u) - β * g = (-Real.log (1 - u) - u) + (u - β * g) := by ring
  rw [e3]
  refine (abs_add_le _ _).trans ?_
  have e4 : g * (e + c * g) = e * g + c * g ^ 2 := by ring
  linarith only [h2, h3, h1, e4]

/-- **Summing a marginal flow against `log g`.** -/
theorem log_sum_bound {g y p a e : ℕ → ℝ} {β β' M c E1 A σ : ℝ} {n : ℕ}
    (hβ : 0 < β) (hβ' : 0 < β') (hc : 0 ≤ c) (hA : 0 ≤ A) (hM0 : 0 ≤ M) (hE1 : 0 ≤ E1)
    (hg : ∀ k ≤ n, 0 < g k) (hg1 : ∀ k < n, g k ≤ 1)
    (hinc : ∀ k < n, g k + β' * g k ^ 2 ≤ g (k + 1))
    (hM : ∀ k < n, g (k + 1) ≤ M * g k)
    (he0 : ∀ k < n, 0 ≤ e k) (he1 : ∀ k < n, e k ≤ E1) (ha : ∀ k < n, 0 ≤ a k)
    (hband : ∀ k < n, |1 / g (k + 1) - 1 / g k + β| ≤ e k + c * g k)
    (hy : ∀ k < n, |y (k + 1) - y k - (p (k + 1) - p k) + σ * g k| ≤
      A * g k ^ 2 + A * g k * a k) :
    |y n - y 0 - (p n - p 0) + σ / β * Real.log (g n / g 0)| ≤
      ((A + |σ| / β * (M * (β + E1 + c) ^ 2 + c)) / β' +
        ∑ k ∈ range n, (A * a k + |σ| / β * e k)) * g n := by
  have hsb : 0 ≤ |σ| / β := div_nonneg (abs_nonneg _) hβ.le
  set K1 := A + |σ| / β * (M * (β + E1 + c) ^ 2 + c) with hK1
  -- the per-step defect
  set D : ℕ → ℝ := fun k => y (k + 1) - y k - (p (k + 1) - p k) +
    σ / β * (Real.log (g (k + 1)) - Real.log (g k)) with hD
  have hgn := g_le_of_inc hβ'.le hinc
  have hDk : ∀ k < n, |D k| ≤ K1 * g k ^ 2 + (A * a k + |σ| / β * e k) * g k := by
    intro k hk
    have hgk := hg k hk.le
    have hgk1 := hg (k + 1) (by omega)
    have hinck : g k ≤ g (k + 1) := by
      have := hinc k hk; have : 0 ≤ β' * g k ^ 2 := by positivity
      linarith
    have hl := log_step hgk (hg1 k hk) hinck (hM k hk) (he0 k hk) (he1 k hk) hc (hband k hk)
    have e1 : D k = (y (k + 1) - y k - (p (k + 1) - p k) + σ * g k) +
        σ / β * (Real.log (g (k + 1) / g k) - β * g k) := by
      simp only [hD]
      rw [Real.log_div hgk1.ne' hgk.ne']
      have hσ : σ / β * β = σ := div_mul_cancel₀ σ hβ.ne'
      linear_combination (g k) * hσ
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_div, abs_of_pos hβ]
    have h2 := mul_le_mul_of_nonneg_left hl hsb
    have e2 : K1 * g k ^ 2 + (A * a k + |σ| / β * e k) * g k =
        (A * g k ^ 2 + A * g k * a k) +
          |σ| / β * (M * (β + E1 + c) ^ 2 * g k ^ 2 + e k * g k + c * g k ^ 2) := by
      rw [hK1]; ring
    rw [e2]
    exact add_le_add (hy k hk) h2
  -- telescoping
  have htel : ∑ k ∈ range n, D k =
      y n - y 0 - (p n - p 0) + σ / β * (Real.log (g n) - Real.log (g 0)) := by
    have h1 := sum_range_sub (fun k => y k - p k + σ / β * Real.log (g k)) n
    have e : ∀ k, D k = (fun k => y k - p k + σ / β * Real.log (g k)) (k + 1) -
        (fun k => y k - p k + σ / β * Real.log (g k)) k := fun k => by simp only [hD]; ring
    rw [sum_congr rfl fun k _ => e k, h1]; ring
  have hlogn : Real.log (g n / g 0) = Real.log (g n) - Real.log (g 0) :=
    Real.log_div (hg n le_rfl).ne' (hg 0 (Nat.zero_le _)).ne'
  rw [hlogn, ← htel]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun k hk => hDk k (mem_range.1 hk)).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have hs1 := sum_sq_le hβ' n hinc
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  have hs2 : ∑ k ∈ range n, (A * a k + |σ| / β * e k) * g k ≤
      ∑ k ∈ range n, (A * a k + |σ| / β * e k) * g n := by
    refine sum_le_sum fun k hk => ?_
    have hk' := mem_range.1 hk
    have : 0 ≤ A * a k + |σ| / β * e k :=
      add_nonneg (mul_nonneg hA (ha k hk')) (mul_nonneg hsb (he0 k hk'))
    exact mul_le_mul_of_nonneg_left (hgn k hk'.le) this
  rw [← sum_mul] at hs2
  have hg0 := (hg 0 (Nat.zero_le _)).le
  have h3 : K1 * ∑ k ∈ range n, g k ^ 2 ≤ K1 * (g n / β') := by
    refine mul_le_mul_of_nonneg_left (hs1.trans ?_) hK10
    rw [div_le_div_iff_of_pos_right hβ']; linarith only [hg0]
  have e : (K1 / β' + ∑ k ∈ range n, (A * a k + |σ| / β * e k)) * g n =
      K1 * (g n / β') + (∑ k ∈ range n, (A * a k + |σ| / β * e k)) * g n := by ring
  rw [e]
  linarith only [h3, hs2]


/-- `|log‖1 + x‖ - Re x| ≤ 7‖x‖²` for `‖x‖ ≤ 1/4`. -/
theorem log_norm_one_add {x : ℂ} (hx : ‖x‖ ≤ 1 / 4) :
    |Real.log ‖1 + x‖ - x.re| ≤ 7 * ‖x‖ ^ 2 := by
  set u := 2 * x.re + ‖x‖ ^ 2 with hu
  have hn0 := norm_nonneg x
  have hre : |x.re| ≤ ‖x‖ := Complex.abs_re_le_norm x
  have hsq : ‖1 + x‖ ^ 2 = 1 + u := by
    rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_one, one_mul, Complex.conj_re,
      ← Complex.sq_norm, hu]
    ring
  have hu1 : |u| ≤ 9 / 4 * ‖x‖ := by
    rw [hu]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg ‖x‖)]
    have h4 : ‖x‖ ^ 2 ≤ ‖x‖ * (1 / 4) := by rw [sq]; exact mul_le_mul_of_nonneg_left hx hn0
    linarith only [hre, h4]
  have hu2 : |u| ≤ 9 / 16 := by linarith only [hu1, hx]
  have hpos : 0 < 1 + u := by have := (abs_le.1 hu2).1; linarith only [this]
  have hlog : Real.log ‖1 + x‖ = Real.log (1 + u) / 2 := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith only [hu2]) 1
  simp only [range_one, sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
    sub_neg_eq_add, abs_neg] at h
  have hb : |u| ^ (1 + 1) / (1 - |u|) ≤ 16 / 7 * u ^ 2 := by
    rw [div_le_iff₀ (by linarith only [hu2])]
    have : |u| ^ (1 + 1) = u ^ 2 := by rw [show 1 + 1 = 2 by rfl, sq_abs]
    rw [this]
    have h5 : u ^ 2 * 1 ≤ u ^ 2 * (16 / 7 * (1 - |u|)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hu2]) (sq_nonneg u)
    have e5 : 16 / 7 * u ^ 2 * (1 - |u|) = u ^ 2 * (16 / 7 * (1 - |u|)) := by ring
    linarith only [h5, e5]
  have h2 : |Real.log (1 + u) - u| ≤ 16 / 7 * u ^ 2 := by
    have e : Real.log (1 + u) - u = -u + Real.log (1 + u) := by ring
    rw [e]; exact h.trans hb
  have hu2' : u ^ 2 ≤ (9 / 4 * ‖x‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu1 2
  rw [hlog]
  have e : Real.log (1 + u) / 2 - x.re = (Real.log (1 + u) - u) / 2 + ‖x‖ ^ 2 / 2 := by
    rw [hu]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_two, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2 / 2)]
  have e6 : (9 / 4 * ‖x‖) ^ 2 = 81 / 16 * ‖x‖ ^ 2 := by ring
  have h7 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  linarith only [h2, hu2', e6, h7]

end Step2
