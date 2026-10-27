import Mathlib

/-!
# The uniform bound on `𝒲` (`h02uv-outline.tex`, Corollary `cor:W-uniform`)

If `w_{k+1} ≤ θ w_k + C (v_k² + w_k²)` with `θ ≤ 1/4`, `w_0 = 0`, `v_k² ≤ 2 v_{k+1}²` and
`v_k ≤ ε ≤ 1/(8C)`, then `w_k ≤ 8 C v_k²` (`w_uniform`). With `v_k = ḡ_k` and
`θ = C₀ L^{-1}` (Proposition `prop:W-contract`) this gives `‖𝒲_k‖_k ≤ 8 C(L) ḡ_k²`.
-/

namespace Flow2

/-- **Corollary `cor:W-uniform`** (on a finite horizon `M`). -/
theorem w_uniform {θ C ε : ℝ} (hθ : θ ≤ 1 / 4) (hC : 0 < C)
    (hε : ε ≤ 1 / (8 * C)) {M : ℕ} (v w : ℕ → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hw0 : ∀ k, 0 ≤ w k)
    (hw00 : w 0 = 0)
    (hrec : ∀ k < M, w (k + 1) ≤ θ * w k + C * (v k ^ 2 + w k ^ 2))
    (hvv : ∀ k < M, v k ^ 2 ≤ 2 * v (k + 1) ^ 2) (hvε : ∀ k ≤ M, v k ≤ ε) :
    ∀ k ≤ M, w k ≤ 8 * C * v k ^ 2 := by
  intro k
  induction k with
  | zero => intro _; rw [hw00]; have := hv0 0; positivity
  | succ k ih =>
    intro hk
    have hwk := ih (by omega)
    have hvk := hv0 k
    have hwk0 := hw0 k
    have hε0 : 0 ≤ ε := hvk.trans (hvε k (by omega))
    have hv2 : v k ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hvk (hvε k (by omega)) 2
    have hε2 : 64 * C ^ 2 * ε ^ 2 ≤ 1 := by
      have h1 : 8 * C * ε ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hε; linarith
      have h2 : 0 ≤ 8 * C * ε := by positivity
      nlinarith
    have hsq : w k ^ 2 ≤ v k ^ 2 := by
      have h1 : w k ^ 2 ≤ (8 * C * v k ^ 2) ^ 2 := pow_le_pow_left₀ hwk0 hwk 2
      have h3 : (8 * C * v k ^ 2) ^ 2 ≤ 64 * C ^ 2 * ε ^ 2 * v k ^ 2 := by
        have := mul_le_mul_of_nonneg_left hv2 (by positivity : (0 : ℝ) ≤ 64 * C ^ 2 * v k ^ 2)
        nlinarith
      have h4 : 64 * C ^ 2 * ε ^ 2 * v k ^ 2 ≤ v k ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hε2 (sq_nonneg (v k))]
      linarith
    have hθw : θ * w k ≤ 2 * C * v k ^ 2 := by
      calc θ * w k ≤ 1 / 4 * (8 * C * v k ^ 2) := mul_le_mul hθ hwk hwk0 (by norm_num)
        _ = 2 * C * v k ^ 2 := by ring
    have hstep : w (k + 1) ≤ 4 * C * v k ^ 2 := by
      have := hrec k (by omega)
      have h1 : C * w k ^ 2 ≤ C * v k ^ 2 := mul_le_mul_of_nonneg_left hsq hC.le
      nlinarith
    have := hvv k (by omega)
    nlinarith

end Flow2
