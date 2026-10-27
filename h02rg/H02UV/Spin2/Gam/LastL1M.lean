import Spin2.Gam.LastOneM
import Spin2.Gam.LastKRem1
import PtCorr2.Last.LastObsK7
import PtCorr2.Last.LastL1

-- Merged from `Spin2/LastKRemM.lean` (phase 3).
section

/-!
# The master construction with the exports of the last step: `thm_case2_pairLIZWK`

Copy of the proof of `thm_case2_pairLIZW` (same construction and constants) with:

* the regulator requirement `A/2 ≥ A₀(L)` of the jet bound of the last step
  (`PtCorr2.finG_jets_le`) added to `Aext`, and the export
  `∃ r₀ ∈ (0, 1], PtCorr2.LastJetBd L (A/2) r₀`;
* **`LastObsConclK c_K`**: along admissible trajectories (`N_h ≥ 1`, pair vertex, every point
  configuration) `A^{(|𝓑(X)|-4)_+}‖K^{obs}_{N_h+1}(X)‖ ≤ c_Kǧ_{N_h}s_{N_h}²|β_{N_h}|`,
  `c_K = 6B(3C₁ + 1)max(c, 0)`, `B = kB(θ₀, C₁, 8c_x)`: the `K^{obs}` bound at `N_h`
  (`obs_hist_rel2_baseX`) and one step (`PtCorr2.kobs_hist_stepL`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The relative weighted bound of `K^{obs}_{N_h+1}`** (pair vertex, any point configuration,
`N_h ≥ 1`): `c_Kǧ_{N_h}s_{N_h}²|β_{N_h}|`. -/
def LastObsConclK (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cK : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ P : Obs2.ObsPts 2 L N, 0 < Nh →
    KbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Nh + 1) (cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R P (zV b) m b μ₀ Nh‖)

end

end Spin2

end

/-!
# The master construction with the `ℓ¹` size of the shares at `N_h + 1`: `thm_case2_pairLIZWKA`

Copy of the proof of `thm_case2_pairLIZWK` (same construction and constants) with the export

* **`LastL1Concl`**: along admissible trajectories, for the pair vertex and every point
  configuration `P` with `|𝔫^{(2)}_{N_h}| ≤ 1/7`, `∑_B|m₂V_{N_h+1}(B)_a| ≤ 3|β_{N_h+1}|`
  (`PtCorr2.obs_hist_rel2_topA`: the relative recursion at horizon `N_h`, `RelRec.E_top` and one
  `ℓ¹` step `shareDev2_succ_le`; `γ_a ≠ 0` reduced by `obsHist_gaZero`). The inputs at the index
  `N_h` are `C2Ctx.tadInc2_leU`, `prodBd2_histL`, and `c_δ(cǧ_{N_h})² ≤ 1/8` (from the band).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The `ℓ¹` size of the shares at `N_h + 1`** along the admissible trajectories (pair vertex, any
point configuration with `|𝔫^{(2)}_{N_h}| ≤ 1/7`): `∑_B|m₂V_{N_h+1}(B)_a| ≤ 3|β_{N_h+1}|`. -/
def LastL1Concl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ P : Obs2.ObsPts 2 L N, ‖nn2 R P (zV b) m b μ₀ Nh‖ ≤ 1 / 7 →
    Obs2.shA2 (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (Nh + 1) ≤ 3 * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖

end

end Spin2
