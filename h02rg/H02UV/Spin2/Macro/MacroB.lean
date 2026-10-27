import Spin2.Macro.MacroA
import Spin2.Cont.ContFx5b

set_option autoImplicit false

/-!
# `thm:macro` at order zero: finite `ε` and every subsequential limit

* **`thm_macro_eps0`** (finite `ε`, uniform in `N`): constants `M, g₀, N₀` depending on `L` only;
  for `δ > 0` a constant `C(δ, L)` such that for `N ≥ N₀`, `4m²L^{2N} ≤ 1/β_R ≤ g₀` and every `b` in
  the bracket, `Z_ε = (β_{N−2}/β_R)^{2/3}` with `β_{N−2}/β_R ∈ [1/4, 5]` and
  `|ϑ_ε^{-2}P_ε(x) − Z_ε| ≤ C/β_R` for all `x ≠ 0` with `|x|/L^N ≥ δ`.
* **`thm_macro_lim0`**: `thm_limit_fixed_betaR` (same `M, g₀, N₀`) together with: for `δ > 0`
  there is `C(δ, L)` such that for every `β_R ≥ 1/g₀`, every admissible sequence and every
  subsequence along which `ϑ_ε^{-2}P_ε` converges at `x` and `y` (`‖x‖, ‖y‖ ≥ δ`), the limits
  satisfy `|G(x) − G(y)| ≤ C/β_R`, and `G(x) ≥ 4^{-2/3} − C/β_R`.
-/

namespace Spin2

open Step Step2 PtCorr2 Filter Topology Cont Grassmann Loc Flow2 Flow2.Hist Step2.D2

noncomputable section

/-- **`thm:macro` at order zero, finite `ε`.** -/
theorem thm_macro_eps0 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR,
      (1 / 4 ≤ betaJ R m b (b - m) (N - 2) / βR ∧ betaJ R m b (b - m) (N - 2) / βR ≤ 5) ∧
      ∀ x : Lam 2 L N, x ≠ 0 → δ ≤ eucl x / (L : ℝ) ^ N →
        |Pconn L N (1 / b) x / thetaEpsSq βR b -
            (betaJ R m b (b - m) (N - 2) / βR) ^ (2 / 3 : ℝ)| ≤ C / βR := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -⟩ := h L hL
  obtain ⟨g₀, N₀, hg, -, hF⟩ := mac_eps M
  exact ⟨M, g₀, N₀, hg, hF⟩

/-- A lower bound `4^{-2/3} ≤ Y^{2/3}` for `Y ≥ 1/4`, in the form used below. -/
theorem mac_rpow23_low {Y : ℝ} (hY : 1 / 4 ≤ Y) : (1 / 4 : ℝ) ^ (2 / 3 : ℝ) ≤ Y ^ (2 / 3 : ℝ) :=
  Real.rpow_le_rpow (by norm_num) hY (by norm_num)

set_option maxHeartbeats 1000000 in
/-- **`thm:macro` at order zero for every subsequential limit** (with the existence statement
`thm_limit_fixed_betaR` on the same master construction). -/
theorem thm_macro_lim0 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    (∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
      ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
      ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), ClAdm M N₀ βR R m b →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ, ContinuousOn G {0}ᶜ ∧
        (∀ K ⊆ ({0}ᶜ : Set (UnitAddTorus (Fin 2))), IsCompact K →
          TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop K) ∧
        (∀ x, x ≠ 0 → 0 ≤ G x) ∧
        (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, x ≠ 0 → G (clSgn τ s x) = G x) ∧
        (∀ δ > 0, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
        (∀ x, x ≠ 0 → torusNorm x < δ₀ →
          |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x))) ∧
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
      ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), ClAdm M N₀ βR R m b →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (G : UnitAddTorus (Fin 2) → ℝ) (x y : UnitAddTorus (Fin 2)),
        δ ≤ ‖x‖ → δ ≤ ‖y‖ →
        Tendsto (fun k => clF L βR b (φ k) x) atTop (𝓝 (G x)) →
        Tendsto (fun k => clF L βR b (φ k) y) atTop (𝓝 (G y)) →
        |G x - G y| ≤ C / βR ∧ (1 / 4 : ℝ) ^ (2 / 3 : ℝ) - C / βR ≤ G x := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, hcab, hBk⟩ := h L hL
  have hL2 : 2 ≤ L := M.ct_L2
  obtain ⟨g₁, N₀, hg₁, hF⟩ := eqs_limitAnn M
  obtain ⟨g₂, hg₂, hE⟩ := M.fx_clEqui hcab hBk
  obtain ⟨g₃, N₃, hg₃, -, hMac⟩ := mac_eps M
  refine ⟨M, min g₁ (min g₂ g₃), N₀, lt_min hg₁ (lt_min hg₂ hg₃), fun βR hβ hy => ?_,
    fun δ hδ => ?_⟩
  · obtain ⟨δ₀, K', hδ₀, hδ₁, hK', hlim⟩ := hF βR hβ (hy.trans (min_le_left _ _))
    refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun R m b hA => ?_⟩
    have hEq := hE N₀ βR R m b hβ (hy.trans ((min_le_right _ _).trans (min_le_left _ _))) hA
    obtain ⟨φ, hφ, G, hc, hu, hnn, hsym, hb, hsh⟩ :=
      hlim 0 le_rfl R m b hA (fun r hr => (clEqui_iff_on _).1 hEq r hr)
    have hset : {x : UnitAddTorus (Fin 2) | (0 : ℝ) < dist x 0} = {0}ᶜ := by
      ext x; simp
    rw [hset] at hc hu
    exact ⟨φ, hφ, G, hc, hu, fun x hx => hnn x (norm_pos_iff.2 hx),
      fun τ s x hx => hsym τ s x (norm_pos_iff.2 hx), hb,
      fun x hx hδ => hsh x (norm_pos_iff.2 hx) hδ⟩
  · obtain ⟨C, hC0, hC⟩ := hMac (δ / 2) (by positivity)
    refine ⟨2 * C, by positivity, fun βR hβ hy R m b hA φ hφ G x y hx hy' hGx hGy => ?_⟩
    have hy3 : 1 / βR ≤ g₃ := hy.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (t6_eventually_small hL2 (show 0 < δ / 2 by positivity))
    -- the finite-`N` bound at `x` and `y`
    have key : ∀ N, max N₀ (max N₃ N₂) ≤ N →
        |clF L βR b N x - clF L βR b N y| ≤ 2 * C / βR ∧
          (1 / 4 : ℝ) ^ (2 / 3 : ℝ) - C / βR ≤ clF L βR b N x := by
      intro N hN
      have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
      have hN3 : N₃ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
      have hN2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
      obtain ⟨i1, i2, hPc, hi0, hRℓ, hRA, hRρ, hm, hmass, hb, -⟩ := hA N hN0
      have hs := hN₂ N hN2
      have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hδ hx
      have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hδ hy'
      obtain ⟨hxne, hxl⟩ := t6_latPt_far hL2 N x (by linarith) hx0
      obtain ⟨hyne, hyl⟩ := t6_latPt_far hL2 N y (by linarith) hy0
      obtain ⟨⟨hY4, -⟩, hB⟩ := hC N (R N) hPc hi0 hRℓ hRA hRρ hN3 (m N) βR hm hβ hmass hy3
        (b N) hb
      have bx := hB _ hxne (by linarith)
      have bY := hB _ hyne (by linarith)
      have hlow := mac_rpow23_low hY4
      unfold clF
      refine ⟨?_, ?_⟩
      · have := abs_sub_le (Pconn L N (1 / b N) (latPtN L N x) / thetaEpsSq βR (b N))
          ((betaJ (R N) (m N) (b N) (b N - m N) (N - 2) / βR) ^ (2 / 3 : ℝ))
          (Pconn L N (1 / b N) (latPtN L N y) / thetaEpsSq βR (b N))
        rw [abs_sub_comm ((betaJ (R N) (m N) (b N) (b N - m N) (N - 2) / βR) ^ (2 / 3 : ℝ))] at this
        have e : 2 * C / βR = C / βR + C / βR := by ring
        linarith
      · have := (abs_le.1 bx).1
        linarith
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hev : ∀ᶠ k in atTop, max N₀ (max N₃ N₂) ≤ φ k := hφt.eventually_ge_atTop _
    refine ⟨?_, ?_⟩
    · have hlim := (hGx.sub hGy).abs
      refine le_of_tendsto hlim (hev.mono fun k hk => (key _ hk).1)
    · have : (1 / 4 : ℝ) ^ (2 / 3 : ℝ) - 2 * C / βR ≤ (1 / 4 : ℝ) ^ (2 / 3 : ℝ) - C / βR := by
        have : 0 ≤ C / βR := div_nonneg hC0 hβ.le
        have e : 2 * C / βR = C / βR + C / βR := by ring
        linarith
      exact this.trans (ge_of_tendsto hGx (hev.mono fun k hk => (key _ hk).2))

end

end Spin2
