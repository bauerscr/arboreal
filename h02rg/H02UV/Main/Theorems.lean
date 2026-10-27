import Spin2.Final.Arboreal

set_option autoImplicit false

/-!
# Main theorems of `h02uv-lean.tex` (the arboreal gas in `d = 2`, without the auxiliary mass)

The theorem-level results of `h02uv-lean.tex` (Section `sec:lean`), with their labels in
`h02uv-lean.tex` and in the paper `summaries/h02uv-outline.tex`:

* `H02UV.thm_arboreal_limit_fixed`: `h02uv-lean.tex` Theorem 1.1 `thm:limit-fixed`
  (= `summaries/h02uv.tex` `thm:limit-fixed`); `h02uv-outline.tex` Theorem 1.5 `thm:limit-fixed`
  for the arboreal gas, without `m²`.
* `H02UV.thm_arboreal_multiscale`: the per-`N` clause of `thm_arboreal_limit_fixed` (bound
  `e:betaN` of `h02uv-lean.tex` Theorem `thm:limit-fixed`); `h02uv-outline.tex` Theorems 1.1
  `thm:beta` and 1.2 `thm:multiscale` for the arboreal gas, without `m²`.

The conclusions `ArbScale`, `ArbShort`, the profile `arbF`, the mass-shift identities
`avg0_mass_indep`, `avg0_eq_Pconn` and the per-`M` core (`MasterFacts.arb_perN`, ...) stay in
`H02UV/Spin2/Final/Arboreal.lean`.
-/

namespace H02UV

open Spin2 Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- **Theorems 1.1 and 1.2 of `h02uv-outline.tex` for the arboreal gas (no auxiliary mass).**
For `L ≥ L₀` there are constants `g₀ > 0`, `K, K_s, K_c, K_ε, E, a ≥ 0` and `N₀ ≥ 3` depending on
`L` only such that for every `N ≥ N₀` and every `β_R` with `1/β_R ≤ g₀` there are `β_ε > 0` and
a sequence `β_j` with the conclusions `ArbScale` (`β_0 = β_ε`,
`|β_ε − β₁ log L^N| ≤ K_ε(1 + β_R + log N)`, the scale-by-scale bound on `β_j`, `β_R/4 ≤ β_j`,
`β_{N−2} ≤ 5β_R`, and `|P_{β_ε}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β_k` for all `x ≠ 0`) and
`ArbShort` (the explicit short-distance form). Here `P_{β}[0 ↔ x] = Pconn L N β x` is the
arboreal gas on `(ℤ/L^Nℤ)²`. -/
theorem thm_arboreal_multiscale : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (g₀ K Ks Kc Kε E a : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧ 3 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
      ∃ (βε : ℝ) (β : ℕ → ℝ), ArbScale L N βR K Kc Kε E a βε β ∧ ArbShort L N βR Ks Kc βε := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, -, -⟩ := h L hL
  obtain ⟨g₀, K, Ks, Kc, Kε, E, a, N₀, hg, hE, ha, hKc, hN₀, hF⟩ := M.arb_perN
  obtain ⟨-, -, -, hε, -⟩ := M.core.hC2
  refine ⟨min g₀ (M.core.ε / 4), K, Ks, Kc, Kε, E, a, N₀, lt_min hg (by positivity), hE, ha, hKc,
    hN₀, fun N hN βR hβR hy => ?_⟩
  have hy₀ : 1 / βR ≤ g₀ := hy.trans (min_le_left _ _)
  have hyε : 4 / M.core.ε ≤ βR := M.arb_eps_le hβR (hy.trans (min_le_right _ _))
  obtain ⟨hm0, hmass⟩ := MasterFacts.arbMass_spec (L := L) N hβR
  obtain ⟨hb0, hbr⟩ := M.arb_adm_at (show 2 ≤ N by omega) hβR hyε
  exact ⟨_, _, hF N (a5wR M N) rfl rfl rfl rfl rfl hN _ βR hm0 hβR hmass hy₀ _ hbr⟩

set_option maxHeartbeats 4000000 in
/-- **Theorem 1.5 of `h02uv-outline.tex` for the arboreal gas (no auxiliary mass).** For
`L ≥ L₀` there are constants `g₀ > 0`, `K, K_s, K_c, K_ε, E, a` and `N₀` depending on `L` only
such that for every `β_R` with `1/β_R ≤ g₀` there are `δ₀ ∈ (0,1)`, `K' ≥ 0` and a sequence
`β_N > 0` (the inverse temperatures) such that: for `N ≥ N₀`, `β_N` has the conclusions of
Theorems 1.1/1.2 (`ArbScale`, with some sequence `β_{N,j}`, and `ArbShort`); the profiles
`f_N(x) = (β_R/β_N)^{-2/3}P_{β_N}[0 ↔ x_N]` (`arbF`) are asymptotically equicontinuous on every
`{|x| ≥ r}`; and a subsequence converges uniformly on compact subsets of `𝕋² ∖ {0}` to a
continuous, nonnegative, point-group invariant `G`, bounded on `{|x| ≥ δ}` for every `δ > 0`, with
`|G(x) − (β₁λ/β_R)^{2/3}| ≤ K'(β₁λ/β_R)^{2/3} log λ/λ`, `λ = log(1/|x|)`, for `0 < |x| < δ₀`. -/
theorem thm_arboreal_limit_fixed : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (g₀ K Ks Kc Kε E a : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 ≤ E ∧ 0 ≤ a ∧ 0 < Kc ∧
    ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∃ βs : ℕ → ℝ,
      (∀ N : ℕ, N₀ ≤ N → ∃ β : ℕ → ℝ,
        ArbScale L N βR K Kc Kε E a (βs N) β ∧ ArbShort L N βR Ks Kc (βs N)) ∧
      ClEqui (arbF L βR βs) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ, ContinuousOn G {0}ᶜ ∧
        (∀ S ⊆ ({0}ᶜ : Set (UnitAddTorus (Fin 2))), IsCompact S →
          TendstoUniformlyOn (fun k => arbF L βR βs (φ k)) G atTop S) ∧
        (∀ x, x ≠ 0 → 0 ≤ G x) ∧
        (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, x ≠ 0 → G (clSgn τ s x) = G x) ∧
        (∀ δ > 0, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
        (∀ x, x ≠ 0 → torusNorm x < δ₀ →
          |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  obtain ⟨L₀, h⟩ := eqs_master
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, -, hcab, hBk⟩ := h L hL
  obtain ⟨g₀, K, Ks, Kc, Kε, E, a, N₀, hg, hE, ha, hKc, hN₀, hF⟩ := M.arb_perN
  obtain ⟨g₁, N₁, hg₁, hN₁, hLim⟩ := arb_eqs_limitAnn M
  obtain ⟨g₂, hg₂, hEq⟩ := M.fx_clEqui hcab hBk
  obtain ⟨-, -, -, hε, -⟩ := M.core.hC2
  refine ⟨min g₀ (min g₁ (min g₂ (M.core.ε / 4))), K, Ks, Kc, Kε, E, a, N₀,
    lt_min hg (lt_min hg₁ (lt_min hg₂ (by positivity))), hE, ha, hKc, fun βR hβR hy => ?_⟩
  have hy₀ : 1 / βR ≤ g₀ := hy.trans (min_le_left _ _)
  have hy₁ : 1 / βR ≤ g₁ := hy.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hy₂ : 1 / βR ≤ g₂ :=
    hy.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hyε : 4 / M.core.ε ≤ βR := by
    have h1 : 1 / βR ≤ M.core.ε / 4 :=
      hy.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    exact M.arb_eps_le hβR h1
  obtain ⟨δ₀, K', hδ₀, hδ₁, hK', hlim⟩ := hLim βR hβR hy₁
  set b : ℕ → ℝ := fun N => M.arbB N βR with hbd
  set m : ℕ → ℝ := fun N => arbMass L N βR with hmd
  have hbN : ∀ N, 2 ≤ N → 0 < b N ∧ b N ∈ ctBracket M (a5wR M N) (m N) βR :=
    fun N hN => M.arb_adm_at hN hβR hyε
  have hAdm : ClAdm M N₁ βR (a5wR M) m b := by
    intro N hN
    obtain ⟨hb0, hbr⟩ := hbN N (by omega)
    obtain ⟨hm0, hmass⟩ := MasterFacts.arbMass_spec (L := L) N hβR
    exact ⟨inferInstance, inferInstance, rfl, rfl, rfl, rfl, rfl, hm0, hmass, hbr, hb0⟩
  have hEq' := hEq N₁ βR (a5wR M) m b hβR hy₂ hAdm
  have hfe : arbF L βR (fun N => 1 / b N) = clF L βR b := arbF_eq_clF βR b
  obtain ⟨φ, hφ, G, hc, hu, hnn, hsym, hbd', hsh⟩ :=
    hlim 0 le_rfl (a5wR M) m b hAdm (fun r hr => (clEqui_iff_on _).1 hEq' r hr)
  have hset : {x : UnitAddTorus (Fin 2) | (0 : ℝ) < dist x 0} = {0}ᶜ := by
    ext x; simp
  rw [hset] at hc hu
  refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun N => 1 / b N, ?_, ?_, φ, hφ, G, hc, ?_, ?_, ?_, hbd', ?_⟩
  · intro N hN
    obtain ⟨hb0, hbr⟩ := hbN N (by omega)
    obtain ⟨hm0, hmass⟩ := MasterFacts.arbMass_spec (L := L) N hβR
    exact ⟨_, hF N (a5wR M N) rfl rfl rfl rfl rfl hN _ βR hm0 hβR hmass hy₀ _ hbr⟩
  · rw [hfe]; exact hEq'
  · rw [hfe]; exact hu
  · exact fun x hx => hnn x (norm_pos_iff.2 hx)
  · exact fun τ s x hx => hsym τ s x (norm_pos_iff.2 hx)
  · exact fun x hx hδ => hsh x (norm_pos_iff.2 hx) hδ

end

end H02UV
