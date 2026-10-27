import Spin2.Case2.Case2RelPairLI
import Spin2.Case2.Case2Top

/-!
# The tadpole kernel along the admissible trajectories; `thm_case2_pairLT`

* `TadConcl ... c_t`: along every admissible trajectory, `0 ≤ c_t`, the Case-(2) tadpole increments
  satisfy `‖tadInc2 i k‖ ≤ c_t(2/L)^{k-i}ǧ_i` for `i < k ≤ N_h` (`C2Ctx.tadInc2_leU`, for every
  point configuration and initial vertex), and `c_tǧ_i ≤ 1` (`ǧ ≤ ε`, `4c_t(B'+1)ε ≤ 1/2`).
* **`thm_case2_pairLT`**: `thm_case2_pairLI` with, in addition, `TadConcl` for `c_t = ceff L c`
  (the constant of `C2Ctx`). Copy of the proof of `thm_case2_pairLI` (one extra conjunct).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The tadpole kernel** along the admissible trajectories. -/
def TadConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε ct : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    0 ≤ ct ∧
    (∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (i k : ℕ), i < k → k ≤ Nh →
      ‖Obs2.tadInc2 P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) i k‖ ≤
        ct * (2 / (L : ℝ)) ^ (k - i) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1) ∧
    ∀ i ≤ Nh, ct * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤ 1

end

end Spin2
