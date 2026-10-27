import Spin2.Cont.ContEqF4
import Spin2.Cont.ContEqS0

set_option autoImplicit false

/-!
# B3, `r`-dependent form, final assembly (V): the `r`-dependent limit theorems (`prop:equi-r`)

On the master construction of `eqs_master` (`0 < c_{ab}`, `0 < B`):

* **`thm_limit_equi_r`**: for every `r > 0`, every `β_R` with `1/β_R ≤ min(g₀, g(r))` and every
  admissible sequence with `m_N²L^{2N} ≤ μ(r)` eventually, a subsequence of `clF L β_R b`
  converges uniformly on `{‖x‖ ≥ r}` to a `G` uniformly continuous there, with `G ≥ 0`, point-group
  invariance on `{‖x‖ > r}`, a bound and the short-distance law (`thm_limit_of_equiOn` with the
  hypothesis `ClEquiOn` discharged by `eqf_equiOn`).
* **`thm_limit_equi_rAnn`**: if the smallness holds for every `r > r₀`, the same on compacts of
  `{‖x‖ > r₀}` (`thm_limit_of_equiAnn`).
No hypotheses beyond the stated ranges.
-/

namespace Spin2

open Step Step2 PtCorr2 Filter Topology Cont

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The `r`-dependent limit theorem** (one radius). -/
theorem thm_limit_equi_r : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ) (gr μr : ℝ → ℝ), 0 < g₀ ∧
    (∀ r : ℝ, 0 < r → 0 < gr r ∧ 0 < μr r) ∧
    ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∀ r : ℝ, 0 < r → 1 / βR ≤ gr r → ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ),
      ClAdm M N₀ βR R m b →
      (∃ N₁ : ℕ, ∀ N, N₁ ≤ N → m N * (L : ℝ) ^ (2 * N) ≤ μr r) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ,
      UniformContinuousOn G {x | r ≤ dist x 0} ∧
      TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop {x | r ≤ dist x 0} ∧
      (∀ x, r ≤ ‖x‖ → 0 ≤ G x) ∧
      (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, r < ‖x‖ → G (clSgn τ s x) = G x) ∧
      (∃ C, ∀ x, r ≤ ‖x‖ → G x ≤ C) ∧
      (∀ x, r ≤ ‖x‖ → torusNorm x < δ₀ →
        |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, hcab, hBk⟩ := h L hL
  obtain ⟨g₀, N₀, hg, hF⟩ := eqs_limitOn M
  obtain ⟨gr, μr, hpos, hE⟩ := M.eqf_equiOn hcab hBk
  refine ⟨M, g₀, N₀, gr, μr, hg, hpos, fun βR hβ hy => ?_⟩
  obtain ⟨δ₀, K', hδ₀, hδ₁, hK', hlim⟩ := hF βR hβ hy
  exact ⟨δ₀, K', hδ₀, hδ₁, hK', fun r hr hyr R m b hA hm =>
    hlim r hr R m b hA (hE N₀ r βR R m b hr hβ hyr hA hm)⟩

set_option maxHeartbeats 1000000 in
/-- **The `r`-dependent limit theorem on `{‖x‖ > r₀}`**: smallness for every `r > r₀`. -/
theorem thm_limit_equi_rAnn : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ) (gr μr : ℝ → ℝ), 0 < g₀ ∧
    (∀ r : ℝ, 0 < r → 0 < gr r ∧ 0 < μr r) ∧
    ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∀ r₀ : ℝ, 0 ≤ r₀ → (∀ r > r₀, 1 / βR ≤ gr r) → ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ),
      ClAdm M N₀ βR R m b →
      (∀ r > r₀, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → m N * (L : ℝ) ^ (2 * N) ≤ μr r) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ,
      ContinuousOn G {x | r₀ < dist x 0} ∧
      (∀ K ⊆ {x : UnitAddTorus (Fin 2) | r₀ < dist x 0}, IsCompact K →
        TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop K) ∧
      (∀ x, r₀ < ‖x‖ → 0 ≤ G x) ∧
      (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, r₀ < ‖x‖ → G (clSgn τ s x) = G x) ∧
      (∀ δ > r₀, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
      (∀ x, r₀ < ‖x‖ → torusNorm x < δ₀ →
        |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, hcab, hBk⟩ := h L hL
  obtain ⟨g₀, N₀, hg, hF⟩ := eqs_limitAnn M
  obtain ⟨gr, μr, hpos, hE⟩ := M.eqf_equiOn hcab hBk
  refine ⟨M, g₀, N₀, gr, μr, hg, hpos, fun βR hβ hy => ?_⟩
  obtain ⟨δ₀, K', hδ₀, hδ₁, hK', hlim⟩ := hF βR hβ hy
  refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun r₀ hr₀ hyr R m b hA hm => hlim r₀ hr₀ R m b hA ?_⟩
  intro r hr
  exact hE N₀ r βR R m b (lt_of_le_of_lt hr₀ hr) hβ (hyr r hr) hA (hm r hr)

end

end Spin2
