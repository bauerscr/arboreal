import Step2.Flow.FlowBase
import Step2.Flow.FlowHor2Thm

/-!
# Expected result `thm:flow` for the RG map (`h02uv-outline.tex`, Section `sec:flow`)

`thm_flow`: for `L ≥ L₀` there are parameters `ℓ, A, ρ` and constants `κ, c_g, c_m, c_T, ε, ϑ` such
that for every `N`, every `0 < m² ≤ L^{-2(N-1)}` and every horizon `N_h` with `N_h + 2 ≤ N` and
`m² L^{2(N_h+1)} ≤ ϑ`, the RG flow of `prop:C6` exists: for every `b ∈ (0, b_max]` there is a unique
admissible `μ₀`; along it `|1/ǧ_{j+1} - 1/ǧ_j + β| ≤ 2(1+β)δβ + C ǧ_j` with
`β = 3 log L/(2π)`, `δ = 1/2`; and `μ₀`, `ǧ_{N_h}` are continuous in `b`.

A corollary of `thm_flow_hor2` (which has no mass condition), hence of `flow_master`
(`FlowMaster.lean`). The helpers that were in this file (`ev_small`, `ev_lin`, the `ℓ`-congruences
`cZ_congr`, …, `kap1_le_half`, `kap1_nonneg`, `betaL`) are in `FlowBase.lean`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-- **Expected result `thm:flow` for the RG map.** -/
theorem thm_flow : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ ϑ κ cg cm cT ε : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ϑ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ ϑ →
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
  obtain ⟨L₀, h⟩ := thm_flow_hor2
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, H⟩ := h L hL
  exact ⟨ℓ, A, ρ, 1, κ, cg, cm, cT, ε, hℓ, hA, hρ, one_pos, hε, hκ0, hκ1, hcg, hcm, hcT,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh _ =>
      H N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh⟩

end

end Step2
