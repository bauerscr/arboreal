import Spin2.Pair.PairRed

/-!
# The seed defects of the reduced history summed over the scales above coalescence

The Pauli defects of the quartic seed `ψ̄_aψ_aψ̄_bψ_b` at scale `k` (`Obs2.pauliDef_pbp_mul`,
`pauliDef2_pbp_mul`) are `C_k(a,a)C_k(b,b) - C_k(a,b)C_k(b,a)` and
`C_k(a,a)+C_k(b,b)-C_k(a,b)-C_k(b,a)`; with `b = a + w` (`|w| = n` steps) they are bounded by
`2nℓ_k⁴/L^{k+1}` and `2nℓ_k²/L^{k+1}` (`hist_detDef_le`, `hist_m2Def_le`).

* `sum_Ico_inv_pow_le`: `∑_{j≤k<n}L^{-(k+1)} ≤ L^{-j}/(L-1)`;
* **`seed_detDef_sum_le`**, **`seed_m2Def_sum_le`**: if `n ≤ c₀L^j` and `ℓ_k ≤ ℓ̄`, then
  `∑_{j≤k<n'}|detDef_k| ≤ 2c₀ℓ̄⁴/(L-1)`, `∑_{j≤k<n'}|m2Def_k| ≤ 2c₀ℓ̄²/(L-1)`: the seed defects
  are summable above coalescence, uniformly in `N`, with an extra `1/L`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

/-- `∑_{j≤k<n}L^{-(k+1)} ≤ L^{-j}/(L-1)` for `L ≥ 2`. -/
theorem sum_Ico_inv_pow_le (hL : (2 : ℝ) ≤ L) (j n : ℕ) :
    ∑ k ∈ Ico j n, ((L : ℝ) ^ (k + 1))⁻¹ ≤ ((L : ℝ) ^ j)⁻¹ / ((L : ℝ) - 1) := by
  have hL0 : (0 : ℝ) < L := by linarith
  set x : ℝ := (L : ℝ)⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have e : ∀ k, ((L : ℝ) ^ (k + 1))⁻¹ = x * x ^ k := fun k => by
    rw [hx, ← inv_pow, pow_succ]; ring
  rw [sum_congr rfl fun k _ => e k, ← mul_sum]
  have h1 := geom_sum_Ico_le_of_lt_one (m := j) (n := n) hx0 hx1
  have h2 : x * (x ^ j / (1 - x)) = ((L : ℝ) ^ j)⁻¹ / ((L : ℝ) - 1) := by
    have h1' : (L : ℝ) - 1 ≠ 0 := by linarith
    rw [hx, inv_pow]
    field_simp
  calc x * ∑ k ∈ Ico j n, x ^ k ≤ x * (x ^ j / (1 - x)) := mul_le_mul_of_nonneg_left h1 hx0
    _ = _ := h2

theorem seed_sum_le {f : ℕ → ℝ} {ℓs : ℕ → ℝ} {p n0 : ℕ} {c₀ ℓb : ℝ} (hL : (2 : ℝ) ≤ L)
    (j n : ℕ) (hc₀ : 0 ≤ c₀) (hℓb : 0 ≤ ℓb) (hc : (n0 : ℝ) ≤ c₀ * (L : ℝ) ^ j)
    (hℓ0 : ∀ k, 0 ≤ ℓs k) (hℓ : ∀ k ∈ Ico j n, ℓs k ≤ ℓb)
    (hf : ∀ k ∈ Ico j n, f k ≤ 2 * n0 * (ℓs k ^ 2 / (L : ℝ) ^ (k + 1)) * ℓs k ^ p) :
    ∑ k ∈ Ico j n, f k ≤ 2 * c₀ * ℓb ^ (2 + p) / ((L : ℝ) - 1) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := pow_pos hL0 j
  have hterm : ∀ k ∈ Ico j n, f k ≤ 2 * c₀ * (L : ℝ) ^ j * ℓb ^ (2 + p) * ((L : ℝ) ^ (k + 1))⁻¹ := by
    intro k hk
    refine (hf k hk).trans ?_
    have hk0 := hℓ0 k
    have hpow : ℓs k ^ 2 * ℓs k ^ p ≤ ℓb ^ (2 + p) := by
      rw [← pow_add]; exact pow_le_pow_left₀ hk0 (hℓ k hk) _
    have e : 2 * n0 * (ℓs k ^ 2 / (L : ℝ) ^ (k + 1)) * ℓs k ^ p =
        2 * n0 * (ℓs k ^ 2 * ℓs k ^ p) * ((L : ℝ) ^ (k + 1))⁻¹ := by
      rw [div_eq_mul_inv]; ring
    rw [e]
    have hinv : 0 ≤ ((L : ℝ) ^ (k + 1))⁻¹ := by positivity
    have hn0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
    have h2 : 2 * (n0 : ℝ) * (ℓs k ^ 2 * ℓs k ^ p) ≤ 2 * (c₀ * (L : ℝ) ^ j) * ℓb ^ (2 + p) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hpow
        (mul_nonneg (pow_nonneg hk0 _) (pow_nonneg hk0 _)) (by positivity)
    calc 2 * (n0 : ℝ) * (ℓs k ^ 2 * ℓs k ^ p) * ((L : ℝ) ^ (k + 1))⁻¹
        ≤ 2 * (c₀ * (L : ℝ) ^ j) * ℓb ^ (2 + p) * ((L : ℝ) ^ (k + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right h2 hinv
      _ = _ := by ring
  have hK : 0 ≤ 2 * c₀ * (L : ℝ) ^ j * ℓb ^ (2 + p) := by positivity
  calc ∑ k ∈ Ico j n, f k
      ≤ ∑ k ∈ Ico j n, 2 * c₀ * (L : ℝ) ^ j * ℓb ^ (2 + p) * ((L : ℝ) ^ (k + 1))⁻¹ :=
        sum_le_sum hterm
    _ = 2 * c₀ * (L : ℝ) ^ j * ℓb ^ (2 + p) * ∑ k ∈ Ico j n, ((L : ℝ) ^ (k + 1))⁻¹ := by
        rw [mul_sum]
    _ ≤ 2 * c₀ * (L : ℝ) ^ j * ℓb ^ (2 + p) * (((L : ℝ) ^ j)⁻¹ / ((L : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ico_inv_pow_le hL j n) hK
    _ = 2 * c₀ * ℓb ^ (2 + p) / ((L : ℝ) - 1) := by
        field_simp

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R))

/-- **The determinant defects of the seed, summed above coalescence.** -/
theorem seed_detDef_sum_le (hL : (2 : ℝ) ≤ L) (a : Lam 2 L N) (w : List (Dir 2)) (j n : ℕ)
    {c₀ ℓb : ℝ} (hc₀ : 0 ≤ c₀) (hℓb : 0 ≤ ℓb) (hc : (w.length : ℝ) ≤ c₀ * (L : ℝ) ^ j)
    (ℓs : ℕ → ℝ) (hℓ0 : ∀ k, 0 ≤ ℓs k) (hℓ : ∀ k ∈ Ico j n, ℓs k ≤ ℓb)
    (hC : ∀ k ∈ Ico j n, GoodCov2 k (ℓs k) (Obs2.histCovO R t k)) :
    ∑ k ∈ Ico j n, ‖Obs2.histCovO R t k a a *
        Obs2.histCovO R t k (Obs2.pathEnd a w) (Obs2.pathEnd a w) -
        Obs2.histCovO R t k a (Obs2.pathEnd a w) * Obs2.histCovO R t k (Obs2.pathEnd a w) a‖ ≤
      2 * c₀ * ℓb ^ (2 + 2) / ((L : ℝ) - 1) :=
  seed_sum_le hL j n hc₀ hℓb hc hℓ0 hℓ fun k hk => hist_detDef_le R t (hC k hk) a w

end Hist

end

end Spin2
