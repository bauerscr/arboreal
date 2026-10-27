import Spin2.Case2.Case2RelPairLI
import Spin2.Gam.GamTopFullL

/-!
# The master construction with the relative `𝒲^{obs}_{N_h+1}` bound: `thm_case2_pairLIZW`

Copy of the proof of `thm_case2_pairLIZ` (same construction and constants) with one more export,
**`LastObsConclW c_W`**: along admissible trajectories (`N_h ≥ 1`, pair vertex, every point
configuration) `‖𝒲^{obs}_{N_h+1}(B)‖ ≤ c_Wǧ_{N_h}s_{N_h}²|β_{N_h}|`, `c_W = 2(3C₁ + 1)max(c, 0)` — the
`LastObsConcl` block of `thm_case2_topL` (`obs_hist_rel2_baseX`, `wobs_hist_stepL`) without the
final weakening `cǧ_{N_h} ≤ 1`. The extra factor `ǧ_{N_h}` makes the `𝒲` tadpole of the last step
small relative to `β_{N-1}` (PR6 item (b)).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The relative block bound of `𝒲^{obs}_{N_h+1}`** (pair vertex, any point configuration,
`N_h ≥ 1`): `c_Wǧ_{N_h}s_{N_h}²|β_{N_h}|`. -/
def LastObsConclW (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cW : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ P : Obs2.ObsPts 2 L N, 0 < Nh →
    WbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Nh + 1) (cW * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R P (zV b) m b μ₀ Nh‖)

end

end Spin2
