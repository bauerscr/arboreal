import Step2.Flow.FlowHor2Aux
import Step2.Flow.FlowMaster

/-!
# Expected result `thm:flow` up to `N_h = N - 2`, without a mass condition

`thm_flow_hor2`: the statement of `thm_flow` (existence and uniqueness of the admissible `μ₀`,
the band for `1/ǧ`, continuity of `μ₀` and `ǧ_{N_h}`) for **every** horizon `N_h ≤ N - 2` and every
`0 < m² ≤ L^{-2(N-1)}`: the mass factor `ϑ` of `thm_flow` and the `k_L` lost scales of
`thm_flow_horizon` are gone.

The two places where `ϑ` entered are replaced:
* (F1): the mass term `Z ζ_j m² w⁽¹⁾` is bounded with the sharp `|ζ_j| ≤ c_ζ ǧ_j`,
  `c_ζ = (6/5)((8/7)(C₄ L² + 1) + 2)` (`zeta_hist`, `Zcov_hist`); with `m² L^{2j} ≤ L^{-4}`
  (`j ≤ N - 3`) its `ǧ²`-coefficient is `O((C₄ + 1)(M₀ + 1) L^{-2})` (`heA1_of`);
* (Lm): the past dependence of the mass term goes through the separate `ζ`-channel
  (`lip_rg_z`, `Flow2.Hist.admissible_unique_z`): its coefficient is `4` and it multiplies
  `|δζ| = O(ε)|δμ|` along the uniqueness cone.

Now a corollary of `flow_master` (`FlowMaster.lean`): existence, the band and continuity from
`HHyp` (`Flow2.Hist.fh_flow_hist_u`), uniqueness from `ZHyp` (`admissible_unique_z`). The helpers
`msq_j2`, `msq_j4`, `heA1_of` are in `FlowBase.lean`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-- **Expected result `thm:flow` for the RG map, up to `N_h = N - 2`, without a mass condition.** -/
theorem thm_flow_hor2 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      (∀ b ∈ Set.Ioc 0 (bmax (betaL L) (1 / 2) cg Nh ε),
          ∃! μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) ∧
      (∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → ∀ j < Nh,
        |1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ (j + 1)).1 -
            1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 + betaL L| ≤
          2 * (1 + betaL L) * (1 / 2) * betaL L +
            Cgu (betaL L) cg * (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1) ∧
      ContinuousOn (muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε)
        (Set.Ioc 0 (bmax (betaL L) (1 / 2) cg Nh ε)) ∧
      ContinuousOn (gN (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε)
        (Set.Ioc 0 (bmax (betaL L) (1 / 2) cg Nh ε)) := by
  obtain ⟨L₀, h⟩ := flow_master_basic
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨k, ε, aB, U, hX⟩ := h L hL
  refine ⟨k.ℓ, k.A, k.ρ, k.κ, k.cg, k.cm, k.cT, ε, U.hℓ, U.hA, U.hρ, U.hε, U.hκ0, U.hκ1, U.hcg,
    U.hcm, U.hcT, fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  have X := hX N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  exact fh_flow_hist_u X.H U.he U.hε
    (fun b μ₀ μ₁ h₀ h₁ => admissible_unique_z X.H X.HZ U.ha0 U.hs h₀ h₁)

end

end Step2
