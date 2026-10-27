import FRD.Decomp

/-!
# `W_N = C_1 + ⋯ + C_N` (`e:WN-def`)

`W_N(x) = (-Δ + m²)^{-1}(0, x) - t_N/|Λ_N|` is the sum of the covariances `C_1, …, C_{N-1}` and
the bounded part `C_N` of the last covariance.
-/

namespace FRD

noncomputable section

open Finset Grassmann

variable (P : PtFamily) {d n : ℕ} [NeZero n]

/-- `W_N(x) = (-Δ + m²)^{-1}(0, x) - t_N/|Λ_N|` (`e:WN-def`). -/
def WN (msq L : ℝ) (N : ℕ) (x : Torus d n) : ℝ :=
  (negLap + msq • 1 : Matrix (Torus d n) (Torus d n) ℝ)⁻¹ 0 x - tN P d msq L N / (n : ℝ) ^ d

/-- `W_N = C_1 + ⋯ + C_{N-1} + C_N`. -/
theorem WN_eq {msq : ℝ} (hmsq : 0 < msq) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : 1 ≤ N)
    (x : Torus d n) :
    WN P msq L N x = ∑ j ∈ Finset.Ico 1 N, Cj P msq L j 0 x + CN P msq L N 0 x := by
  rw [WN, decomposition_inv P hmsq hL hN, CNN_eq, Matrix.add_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.smul_apply, QN, smul_eq_mul]
  ring

end

end FRD
