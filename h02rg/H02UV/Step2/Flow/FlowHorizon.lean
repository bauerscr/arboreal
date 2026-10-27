import Step2.Flow.FlowSharp3

/-!
# The flow up to a fixed number of scales before `N`, for every mass `0 < m² ≤ L^{-2(N-1)}`

`thm_flow`, `thm_flow_sharp` and `thm_flow_sharp_sum` are stated for horizons `N_h` with
`N_h + 2 ≤ N` and `m² L^{2(N_h+1)} ≤ ϑ`, where `ϑ = ϑ(L) > 0` depends only on `L`. For
`m² ≤ L^{-2(N-1)}` one has `m² L^{2(N_h+1)} ≤ L^{-2(N-2-N_h)}`, so the mass condition holds as soon
as `N_h` stays `k_L` scales below `N - 2`, where `L^{-2k_L} ≤ ϑ(L)`. The number `k_L` of lost
scales depends only on `L` (not on `N`, `m²`, `b`).

* `msq_horizon`: `m² ≤ L^{-2(N-1)}` and `N_h + k + 2 ≤ N` give `m² L^{2(N_h+1)} ≤ L^{-2k}`.
* `exists_lost_scales`: for `ϑ > 0` and `L ≥ 2` there is `k` with `L^{-2k} ≤ ϑ`.
  (These two and `mass_of_horizon` are in `FlowBase.lean`.)
* `thm_flow_horizon`, `thm_flow_sharp_horizon`, `thm_flow_sharp_sum_horizon`: the three flow
  theorems with the mass condition replaced by `N_h + k_L + 2 ≤ N`.

Why `ϑ` cannot be replaced by `1` (i.e. `N_h = N - 2`) with the present estimates
(see `Log.md`, "Horizon"):
* (F1): the mass term `ζ_j Z m² w⁽¹⁾` of the `ǧ`-flow is bounded with the a-priori bound
  `|ζ_j| ≤ 2 c_z ǧ_j`, `c_z = 16ℓ²/49`, `ℓ ≍ L^{pPhi 2} = L⁴`, giving a `ǧ²`-coefficient
  `(16/7) c_z (M₀+1) m² L^{2j}`; the band `δ = 1/2` needs it `≤ β/2 ≍ log L`.
* (Lm): the `M`-coefficient (dependence on the past) of `m_j` contains `2Kϑ_j`,
  `ϑ_j = m² L^{2(j+2)}`, with the large Lipschitz constant `K` (`Lm_hist`); uniqueness
  (`coef_h`) needs it `≤ a₀(L², κ, C_L)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Flow2 Flow2.Hist Step2.D2

/-- **Expected result `thm:flow` for the RG map, without a mass condition.** For `L ≥ L₀` there
are a number of lost scales `k_L` and the constants of `thm_flow` such that for every `N`, every
`0 < m² ≤ L^{-2(N-1)}` and every horizon `N_h ≤ N - 2 - k_L`: existence and uniqueness of the
admissible `μ₀`, the band for `1/ǧ`, and continuity of `μ₀` and `ǧ_{N_h}` in `b`. -/
theorem thm_flow_horizon : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (k : ℕ) (ℓ A ρ κ cg cm cT ε : ℝ), 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + k + 2 ≤ N →
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
  obtain ⟨L₀, hL₀⟩ := thm_flow
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, ϑ, κ, cg, cm, cT, ε, hℓ, hA, hρ, hϑ, hε, hκ0, hκ1, hcg, hcm, hcT, h⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  obtain ⟨k, hk⟩ := exists_lost_scales hL2 hϑ
  refine ⟨k, ℓ, A, ρ, κ, cg, cm, cT, ε, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  obtain ⟨h1, h2⟩ := mass_of_horizon (by omega) hm hNh hk
  exact h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh h1 h2

end

end Step2
