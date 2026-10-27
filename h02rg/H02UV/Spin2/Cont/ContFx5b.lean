import Spin2.Cont.ContFx5a
import Spin2.Cont.ContEqF5

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`), Phase 2, layer 6b: `ClEqui` and the continuum limit on `{x ≠ 0}`

* **`MasterFacts.fx_clEqui (hcab) (hB)`**: there is `g₀ > 0` such that for every `β_R` with
  `1/β_R ≤ g₀` and every admissible sequence (`ClAdm M N₀ β_R R m b`), `clF L β_R b` is
  asymptotically equicontinuous on every `{‖x‖ ≥ r}` (`ClEqui`). Proof: `fx_equiOn` gives
  `r`-independent `g, μ`; with `g₀ = min(g, 4μ)` the window `4m_NL^{2N} ≤ 1/β_R` of `ClAdm`
  implies `m_NL^{2N} ≤ μ`; then `clEqui_iff_on`.
* **`thm_limit_fixed_betaR`**: the unconditional variant of `thm_limit_of_equi` on the master
  construction `eqs_master`: for fixed `β_R` with `1/β_R ≤ g₀(L)` and every admissible sequence,
  a subsequence of `clF L β_R b` converges uniformly on compacts of `𝕋² ∖ {0}` to a `G` continuous
  on `𝕋² ∖ {0}`, with `G ≥ 0`, point-group invariance, `G ≤ C(δ)` on `{‖x‖ ≥ δ}` and the
  short-distance law at `|x| < δ₀` (`eqs_limitAnn` at `r₀ = 0`).
-/

namespace Spin2

open Step Step2 PtCorr2 Filter Topology Cont

noncomputable section

/-- **`ClEqui` at fixed `β_R`.** -/
theorem MasterFacts.fx_clEqui {L : ℕ} [NeZero L] (M : MasterFacts L) (hcab : 0 < M.k2cab)
    (hBk : 0 < M.core.Bk) :
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ (N₀ : ℕ) (βR : ℝ) (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), 0 < βR →
      1 / βR ≤ g₀ → ClAdm M N₀ βR R m b → ClEqui (clF L βR b) := by
  obtain ⟨g, μ, hg, hμ, hE⟩ := M.fx_equiOn hcab hBk
  refine ⟨min g (4 * μ), lt_min hg (by positivity), fun N₀ βR R m b hβ hy hA => ?_⟩
  rw [clEqui_iff_on]
  intro r hr
  refine hE N₀ r βR R m b hr hβ (hy.trans (min_le_left _ _)) hA ⟨N₀, fun N hN => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hmass, -, -⟩ := hA N hN
  have := hy.trans (min_le_right _ _)
  linarith

set_option maxHeartbeats 1000000 in
/-- **The subsequential continuum limit at fixed `β_R` on `𝕋² ∖ {0}`** (no equicontinuity
hypothesis). -/
theorem thm_limit_fixed_betaR : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), ClAdm M N₀ βR R m b →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ, ContinuousOn G {0}ᶜ ∧
      (∀ K ⊆ ({0}ᶜ : Set (UnitAddTorus (Fin 2))), IsCompact K →
        TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop K) ∧
      (∀ x, x ≠ 0 → 0 ≤ G x) ∧
      (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, x ≠ 0 → G (clSgn τ s x) = G x) ∧
      (∀ δ > 0, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
      (∀ x, x ≠ 0 → torusNorm x < δ₀ →
        |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, hcab, hBk⟩ := h L hL
  obtain ⟨g₁, N₀, hg₁, hF⟩ := eqs_limitAnn M
  obtain ⟨g₂, hg₂, hE⟩ := M.fx_clEqui hcab hBk
  refine ⟨M, min g₁ g₂, N₀, lt_min hg₁ hg₂, fun βR hβ hy => ?_⟩
  obtain ⟨δ₀, K', hδ₀, hδ₁, hK', hlim⟩ := hF βR hβ (hy.trans (min_le_left _ _))
  refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun R m b hA => ?_⟩
  have hEq := hE N₀ βR R m b hβ (hy.trans (min_le_right _ _)) hA
  obtain ⟨φ, hφ, G, hc, hu, hnn, hsym, hb, hsh⟩ :=
    hlim 0 le_rfl R m b hA (fun r hr => (clEqui_iff_on _).1 hEq r hr)
  have hset : {x : UnitAddTorus (Fin 2) | (0 : ℝ) < dist x 0} = {0}ᶜ := by
    ext x; simp [dist_pos]
  rw [hset] at hc hu
  refine ⟨φ, hφ, G, hc, hu, fun x hx => hnn x (norm_pos_iff.2 hx),
    fun τ s x hx => hsym τ s x (norm_pos_iff.2 hx), hb,
    fun x hx hδ => hsh x (norm_pos_iff.2 hx) hδ⟩

end

end Spin2
