import Mathlib

/-!
# The `λ`-rescaling for the `K^{obs}` contraction (pure analysis)

With the sources rescaled by `λ` (weights `Wt.scale λ`, single sources), the norm of an activity
is `‖K‖_λ = ‖K^∅‖ + λ ‖K^{obs}‖` (`Obs2.KObs2.oTj_scale`). Suppose the full map with sources obeys
the bulk-type bound (the Step2 estimate on the algebra with sources, with the coupling size
`ḡ + λ m` of `V^♭ + V^{obs}` in the `λ`-norm)

  `‖K'‖_λ ≤ θ₀ ‖K‖_λ + C₁ ((ḡ + λm)³ + (ḡ + λm) ‖K‖_λ + ‖K‖_λ²)`.

With `λ = ḡ/m` the coupling size is `2ḡ`; dividing by `λ` and using the a priori bounds
`‖K^∅‖ ≤ c_b ḡ³`, `‖K^{obs}‖ ≤ c_k ḡ² m`, `ḡ ≤ 1` gives (`lam_trick`)

  `k' ≤ (θ₀ + C₁(2 + 2c_b + c_k) ḡ) k + (θ₀ c_b + C₁(8 + 2c_b + c_b²)) ḡ² m`,

the hypothesis `k_{j+1} ≤ θ k_j + B ḡ² m_j` of `Obs2.lin_iter` (with `θ < 1` for small `ḡ`).
-/

namespace Obs2

/-- **The `λ`-trick.** -/
theorem lam_trick {k k' b m g θ₀ C₁ cb ck : ℝ} (hm : 0 < m) (hg : 0 < g) (hg1 : g ≤ 1)
    (hk : 0 ≤ k) (hθ : 0 ≤ θ₀) (hC : 0 ≤ C₁) (hb0 : 0 ≤ b) (hb : b ≤ cb * g ^ 3) (hcb : 0 ≤ cb)
    (hkk : k ≤ ck * g ^ 2 * m) (hck : 0 ≤ ck)
    (h : g / m * k' ≤ θ₀ * (b + g / m * k) +
      C₁ * ((2 * g) ^ 3 + 2 * g * (b + g / m * k) + (b + g / m * k) ^ 2)) :
    k' ≤ (θ₀ + C₁ * (2 + 2 * cb + ck) * g) * k + (θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)) * g ^ 2 * m := by
  set l := g / m with hl
  have hl0 : 0 < l := div_pos hg hm
  have hlm : l * m = g := by rw [hl, div_mul_cancel₀ g hm.ne']
  have hg2 : g ^ 2 ≤ 1 := by nlinarith
  have hg3 : g ^ 3 ≤ g ^ 2 := by nlinarith
  have hg3' : g ^ 3 ≤ g := by nlinarith
  -- the pieces, each `≤ l * (⋯)`
  have e1 : θ₀ * b ≤ l * (θ₀ * cb * g ^ 2 * m) := by
    have : l * (θ₀ * cb * g ^ 2 * m) = θ₀ * (cb * g ^ 2 * (l * m)) := by ring
    rw [this, hlm, show cb * g ^ 2 * g = cb * g ^ 3 by ring]
    exact mul_le_mul_of_nonneg_left hb hθ
  have e2 : C₁ * (2 * g) ^ 3 = l * (C₁ * 8 * g ^ 2 * m) := by
    have : l * (C₁ * 8 * g ^ 2 * m) = C₁ * 8 * g ^ 2 * (l * m) := by ring
    rw [this, hlm]; ring
  have hb' : b ≤ cb * g := hb.trans (mul_le_mul_of_nonneg_left hg3' hcb)
  have e3 : C₁ * (2 * g * b) ≤ l * (C₁ * 2 * cb * g ^ 2 * m) := by
    have : l * (C₁ * 2 * cb * g ^ 2 * m) = C₁ * 2 * cb * g ^ 2 * (l * m) := by ring
    rw [this, hlm]
    have hgb : g * b ≤ cb * g ^ 3 := by
      calc g * b ≤ g * (cb * g ^ 3) := mul_le_mul_of_nonneg_left hb hg.le
        _ = cb * g ^ 3 * g := by ring
        _ ≤ cb * g ^ 3 * 1 := mul_le_mul_of_nonneg_left hg1 (by positivity)
        _ = cb * g ^ 3 := by ring
    calc C₁ * (2 * g * b) = C₁ * 2 * (g * b) := by ring
      _ ≤ C₁ * 2 * (cb * g ^ 3) := mul_le_mul_of_nonneg_left hgb (by positivity)
      _ = C₁ * 2 * cb * g ^ 2 * g := by ring
  have e4 : C₁ * b ^ 2 ≤ l * (C₁ * cb ^ 2 * g ^ 2 * m) := by
    have : l * (C₁ * cb ^ 2 * g ^ 2 * m) = C₁ * (cb ^ 2 * g ^ 2 * (l * m)) := by ring
    rw [this, hlm]
    have hb2 : b ^ 2 ≤ (cb * g ^ 3) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    have h3 : g ^ 3 ≤ 1 := hg3'.trans hg1
    have h4 : (cb * g ^ 3) ^ 2 ≤ cb ^ 2 * g ^ 2 * g := by
      rw [show (cb * g ^ 3) ^ 2 = cb ^ 2 * g ^ 2 * g * g ^ 3 by ring]
      exact mul_le_of_le_one_right (by positivity) h3
    exact mul_le_mul_of_nonneg_left (hb2.trans h4) hC
  have e5 : C₁ * (2 * b * (l * k)) ≤ l * (C₁ * 2 * cb * g * k) := by
    have : C₁ * (2 * b * (l * k)) = l * (C₁ * 2 * b * k) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hl0.le
    calc C₁ * 2 * b * k = (C₁ * 2 * k) * b := by ring
      _ ≤ (C₁ * 2 * k) * (cb * g) := mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = C₁ * 2 * cb * g * k := by ring
  have e6 : C₁ * (l * k) ^ 2 ≤ l * (C₁ * ck * g * k) := by
    have : C₁ * (l * k) ^ 2 = l * (C₁ * (l * k) * k) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hl0.le
    have hlk : l * k ≤ ck * g := by
      have h1 : l * k ≤ l * (ck * g ^ 2 * m) := mul_le_mul_of_nonneg_left hkk hl0.le
      have e : l * (ck * g ^ 2 * m) = ck * g ^ 3 := by
        rw [show l * (ck * g ^ 2 * m) = ck * g ^ 2 * (l * m) by ring, hlm]; ring
      rw [e] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hg3' hck)
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlk hC) hk
    calc C₁ * (l * k) * k ≤ C₁ * (ck * g) * k := this
      _ = C₁ * ck * g * k := by ring
  have key : g / m * k' ≤ l * ((θ₀ + C₁ * (2 + 2 * cb + ck) * g) * k +
      (θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)) * g ^ 2 * m) := by
    refine h.trans ?_
    have hexp : θ₀ * (b + l * k) + C₁ * ((2 * g) ^ 3 + 2 * g * (b + l * k) + (b + l * k) ^ 2) =
        θ₀ * b + l * (θ₀ * k) + C₁ * (2 * g) ^ 3 + C₁ * (2 * g * b) + l * (C₁ * 2 * g * k) +
          C₁ * b ^ 2 + C₁ * (2 * b * (l * k)) + C₁ * (l * k) ^ 2 := by ring
    have hR : l * ((θ₀ + C₁ * (2 + 2 * cb + ck) * g) * k +
        (θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)) * g ^ 2 * m) =
        l * (θ₀ * cb * g ^ 2 * m) + l * (θ₀ * k) + l * (C₁ * 8 * g ^ 2 * m) +
          l * (C₁ * 2 * cb * g ^ 2 * m) + l * (C₁ * 2 * g * k) + l * (C₁ * cb ^ 2 * g ^ 2 * m) +
          l * (C₁ * 2 * cb * g * k) + l * (C₁ * ck * g * k) := by ring
    rw [hexp, hR]
    linarith [e1, e2, e3, e4, e5, e6]
  exact le_of_mul_le_mul_left key hl0

end Obs2
