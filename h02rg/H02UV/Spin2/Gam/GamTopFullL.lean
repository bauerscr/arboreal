import Spin2.Gam.GamRemLast

/-!
# The master constants with the last step: `GamRemNZ`, `GamRemNZS` discharged

* **`LastObsConcl c_W`**: along every admissible trajectory with `N_h ≥ 1`, for every point
  configuration `P` and the pair vertex `zV b`, the block bound
  `‖𝒲^{obs}_{N_h+1}(B)‖ ≤ c_Ws_{N_h}²|β_{N_h}|` (`WbHc` at `N_h + 1`).
* **`thm_case2_topL`**: copy of `thm_case2_top` (same construction and constants) with, in addition,
  `LastObsConcl (3C₁ + 1)`. The proof runs the relative recursion at horizon `N_h`
  (`obs_hist_rel2_baseX`, which also gives `∑_B|m₂(V_{N_h}(B)_a)| ≤ 2|β_{N_h}|`) and one `𝒲^{obs}`
  step at `N_h` (`wobs_hist_stepL`, `ValidAtL`); `γ_a ≠ 0` is reduced by `obsHist_gaZero`.
* **`gamRemNZ_flow`**: `GamRemNZ c_r` and `GamRemNZS c_r` along admissible trajectories, with
  `c_r = 2c_BQ₁c_W(9/8)ℓ² + C_fℓ⁴` (`gamRemNP_le`, `Case2TopStep` from `TopConcl`).
* **`thm_gamTopBd_case2''`**: `GamTopBd ∧ GamTopBdB` with the master constants, conditional only on
  (H_λ) for `λ` and the smallness `K(K_λ)ǧ_j ≤ 1/2`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The block bound of `𝒲^{obs}_{N_h+1}`** along the admissible trajectories (pair vertex, any
point configuration, `N_h ≥ 1`): `c_Ws_{N_h}²|β_{N_h}|`. -/
def LastObsConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cW : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ P : Obs2.ObsPts 2 L N, 0 < Nh →
    WbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Nh + 1) (cW * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R P (zV b) m b μ₀ Nh‖)

end

end Spin2
