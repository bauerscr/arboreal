import Grassmann.Torus
import Grassmann.GramC

/-!
# The torus layer for complex covariances

* `ECC_theta_mul_of_finiteRange`: finite range factorisation of `𝔼_C θ` for a complex `C`.
* `Tj_ECC_theta_le`: `‖𝔼_C θ F‖_{T_j(ℓ)} ≤ ‖F‖_{T_j(2ℓ)}` for a covariance with a Gram
  representation satisfying `GramBound` at scale `j`, in every dimension. In `d ≥ 3` this is
  combined with `Tj_succ_le`; in `d = 2` the factor `2` is not compensated by the field scale
  (see `h02uv-outline.tex`, Section `sec:normcontract`).
-/

namespace Grassmann

noncomputable section

variable {d n : ℕ} [NeZero n]

/-- `e:E-contract` on the torus at scale `j`, for a Gram-admissible complex covariance. -/
theorem Tj_ECC_theta_le {L ℓ : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ) (j : ℕ)
    {C : Matrix (Torus d n) (Torus d n) ℂ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {Fv Gv : Torus d n → H} (hC : IsGram C Fv Gv)
    (hB : GramBound (Dir d) (pPhi d) (L ^ j) ℓ Fv Gv) (F : N (Torus d n)) :
    Tj d L j ℓ (ECC C (theta F)) ≤ Tj d L j (2 * ℓ) F :=
  tNorm_ECC_theta_le (by positivity) hℓ hC hB F

end

end Grassmann
