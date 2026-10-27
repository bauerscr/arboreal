import Spin2.Master.MasterL
import Spin2.H0.H0WinConcl
import Spin2.H0.H0Window

/-!
# Route (a1): the `h = 0` point in the window under one master construction

**`thm_h0_window`**: one set of constants (those of `thm_flow_masterLZW`, i.e. of
`thm_flow_masterLZ` with `WinHyp` exported) such that `FlowC2Concl` holds and, for every
`N, R, N_h = N - 2, m² ∈ mRange` and every admissible `(b, μ₀^c)` (final condition `μ_{N_h} = 0`),
every symmetric window `|μ_{N_h}| ≤ c₁` with `c₁ ≤ θ ǧ^c_{N_h}`, `θ(1 + 2p_Wc_μ) < c_μ`,
`ǧ^c_{N_h}(1 + 2p_Wθ) < ε` (e.g. `θ = (3/4)c_μ` if `p_Wc_μ < 1/6`; `p_W = K_h((1+L²)/2,κ,C_L)C_Lε`
is the `ǧ`-slope of the signed cone) has window ends `μ₋ ≤ μ₀^c ≤ μ₊` with targets `∓c₁`, and the
named inputs `H0OnePtUp` (at `μ₊`) and `H0SusceptExit` (on `[μ₋, μ₊]`) put the `h = 0` trajectory
`(b, b - m²)` in the window: in `D_ε` up to `N_h`, `|μ_{N_h}| ≤ c₁`,
`|ǧ_{N_h} - ǧ^c_{N_h}| ≤ 2p_Wc₁`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology PtCorr2 Step2.D2

/-- **The `h = 0` window statement** at given constants and cone slope `p_W` (the conclusion of
`thm_h0_window`). -/
def H0WindowConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε pW : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    ∀ b μc c₁ θ : ℝ, 0 < b → Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μc →
      0 ≤ c₁ → c₁ ≤ θ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      θ * (1 + 2 * pW * cmu ((L : ℝ) ^ 2) cm) < cmu ((L : ℝ) ^ 2) cm →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 * (1 + 2 * pW * θ) < ε →
    ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μl (-c₁) ∧
      AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μu c₁ ∧
      (H0OnePtUp L N m b μu → H0SusceptExit L N m b μl μu →
        b - m ∈ Ioc μl μu ∧
        (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
        |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).2.1| ≤ c₁ ∧
        |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤ pW * (c₁ - -c₁))

/-- **`H0WindowConcl` from `WinHyp`** (the body of `thm_h0_window`; any constants with `WinHyp`). -/
theorem h0WindowConcl_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε : ℝ}
    (hW : WinHyp L ℓ A ρ κ cg cm cT ε) : ∃ pW : ℝ, H0WindowConcl L ℓ A ρ κ cm cT ε pW := by
  obtain ⟨CL, aB, -, he, hcgε, ha0, hs, -, -, hWH⟩ := hW
  refine ⟨Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε), ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc c₁ θ hb hadm hc0 hc1 hθ hgy
  obtain ⟨H, HZ, -⟩ := hWH N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hΛ2 : 1 < (1 + (L : ℝ) ^ 2) / 2 := by linarith [H.hΛ]
  have hp : 0 ≤ Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε) :=
    (coef_h hΛ2 H.hκ1 HZ.hA HZ.ha ha0).1
  have hg := (hadm.1 Nh le_rfl).1
  obtain ⟨w1, w2, w3⟩ := win_sym_conds hg hp (cmu_pos H.hΛ H.hcm).le hθ hgy hc0 hc1
  have hgβ : cg * ε ≤ (1 - 1 / 2) * betaL L := by linarith [H.hβ]
  obtain ⟨μl, μu, h1, h2, h3, h4, h5⟩ := h0_windowed (R.withMsq m) H HZ ha0 hs he hgβ hm.1 hb
    le_rfl hadm (by linarith : -c₁ ≤ 0) hc0 w1 w2 w3
  refine ⟨μl, μu, h1, h2, h3, h4, fun hup hex => ?_⟩
  obtain ⟨k0, k1, k2, k3, k4⟩ := h5 hup hex
  exact ⟨k0, k1, abs_le.2 ⟨k2, k3⟩, k4⟩


theorem thm_h0_window (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ Aext L A ∧
    ∃ pW : ℝ,
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    ∀ b μc c₁ θ : ℝ, 0 < b → Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μc →
      0 ≤ c₁ → c₁ ≤ θ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      θ * (1 + 2 * pW * cmu ((L : ℝ) ^ 2) cm) < cmu ((L : ℝ) ^ 2) cm →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 * (1 + 2 * pW * θ) < ε →
    ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μl (-c₁) ∧
      AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μu c₁ ∧
      (H0OnePtUp L N m b μu → H0SusceptExit L N m b μl μu →
        b - m ∈ Ioc μl μu ∧
        (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
        |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).2.1| ≤ c₁ ∧
        |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤ pW * (c₁ - -c₁)) := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_masterLZW Aext hAext Eext hEext (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, -, -, -, -, hAx, -, -, -, -, hW, -⟩ :=
    hL₀ L hL
  obtain ⟨pW, hpW⟩ := h0WindowConcl_of hW
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hC2, hAx, pW, hpW⟩

end

end Spin2
