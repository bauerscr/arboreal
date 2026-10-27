module

public import Mathlib

/-!
# Log algebra for the superpolynomial bound

`prod_annulus_le`: for `2^(m+2) ≤ D < 2^(m+3)`, the product `∏_{k<m} C (2^k · 2)^{-κ}` is at most
`A exp(-a (log (2+D))^2)`.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

open Finset

theorem prod_annulus_eq (C κ : ℝ) (hC : 0 < C) (m : ℕ) :
    ∏ k ∈ range m, (C * ((2 ^ k * 2 : ℕ) : ℝ) ^ (-κ)) =
      Real.exp (m * Real.log C - κ * Real.log 2 * ((m : ℝ) * (m + 1) / 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have h2 : ((2 ^ m * 2 : ℕ) : ℝ) ^ (-κ) = Real.exp (-κ * ((m : ℝ) + 1) * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      push_cast
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]
      congr 1; ring
    rw [h2, ← Real.exp_log hC, ← Real.exp_add]
    · rw [← Real.exp_add, Real.exp_log hC]
      congr 1
      push_cast; ring

theorem quad_bound {p q : ℝ} (hq : 0 < q) (m : ℝ) : p * m - q * m ^ 2 ≤ p ^ 2 / (4 * q) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * q * m - p)]

/-- The log algebra: constants depending only on `(C, κ)`. -/
theorem prod_annulus_le {C κ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ m D : ℕ, 2 ^ (m + 2) ≤ D → D < 2 ^ (m + 3) →
      ∏ k ∈ range m, (C * ((2 ^ k * 2 : ℕ) : ℝ) ^ (-κ)) ≤
        A * Real.exp (-a * Real.log (2 + (D : ℝ)) ^ 2) := by
  have hℓ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ Real.log C := Real.log_nonneg hC
  set ℓ := Real.log 2 with hℓdef
  set c := Real.log C with hcdef
  set a : ℝ := κ / (4 * ℓ) with ha
  have ha0 : 0 < a := by positivity
  set p : ℝ := c + 3 * κ * ℓ / 2 with hp
  set q : ℝ := κ * ℓ / 4 with hq
  have hq0 : 0 < q := by positivity
  set LA : ℝ := p ^ 2 / (4 * q) + 4 * κ * ℓ with hLA
  refine ⟨Real.exp LA, a, Real.exp_pos _, ha0, fun m D h1 h2 => ?_⟩
  rw [prod_annulus_eq C κ (by linarith) m]
  have hD : (2 : ℝ) + D ≤ 2 ^ (m + 4) := by
    have h3 : D + 1 ≤ 2 ^ (m + 3) := h2
    have h4 : ((D : ℝ) + 1) ≤ 2 ^ (m + 3) := by exact_mod_cast h3
    have h5 : (1 : ℝ) ≤ 2 ^ (m + 3) := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) + D ≤ 2 ^ (m + 3) + 1 := by linarith
      _ ≤ 2 ^ (m + 4) := by
          have : (2 : ℝ) ^ (m + 4) = 2 * 2 ^ (m + 3) := by ring
          linarith
  have hL : Real.log (2 + (D : ℝ)) ≤ ((m : ℝ) + 4) * ℓ := by
    calc Real.log (2 + (D : ℝ)) ≤ Real.log (2 ^ (m + 4)) :=
          Real.log_le_log (by positivity) hD
      _ = ((m : ℝ) + 4) * ℓ := by rw [Real.log_pow]; push_cast; ring
  have hL0 : 0 ≤ Real.log (2 + (D : ℝ)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    linarith)
  have hL2 : Real.log (2 + (D : ℝ)) ^ 2 ≤ (((m : ℝ) + 4) * ℓ) ^ 2 := by
    apply pow_le_pow_left₀ hL0 hL
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hq' := quad_bound (p := p) hq0 (m : ℝ)
  have : -a * Real.log (2 + (D : ℝ)) ^ 2 ≥ -a * (((m : ℝ) + 4) * ℓ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hL2 ha0.le
    linarith
  have key : (m : ℝ) * c - κ * ℓ * ((m : ℝ) * (m + 1) / 2) + a * (((m : ℝ) + 4) * ℓ) ^ 2 =
      p * m - q * m ^ 2 + 4 * κ * ℓ := by
    rw [ha, hp, hq]
    field_simp
    ring
  linarith

end ArborealDecay.Superpoly
