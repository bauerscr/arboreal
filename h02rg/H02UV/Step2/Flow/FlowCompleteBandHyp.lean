import Step2.Flow.FlowFinalZHyp
import Step2.Last.FlowLastF1b
import Step2.Flow.FlowMaster

/-!
# The hypothesis package of `thm_flow_complete`, with the sharp band at `j = N - 2`

`flow_band_hyp0`: a copy of `flow_complete_hyp0` (`Step2/Flow/FlowCompleteHyp.lean`) with

* the one-loop inputs taken from the `ValidAtL` versions `HV_histU`, `HD_histU`, `S01_histU`,
  `HVs_histU` (`Step2/Last/FlowLastF1a.lean`), which cover the steps `j < N_h` (via
  `ValidAt.toValidAtL`) and the step `j = N_h = N - 2` with the same constants;
* `F1_rg_sharpL` (`Step2/Last/FlowLastF1b.lean`) at `j = N_h`, with its own cubic constant `C_s`, two
  more `ε`-conditions and `L` above `exp(4π/3 (K_A + E₀ + 2C₀ + 1))` (`K_A` bounds the mass term
  of the step `N - 2`, where `m² L^{2(N-2)} ≤ L^{-2}`, `emL_le`);
* the additional exports `ValidAtL R N_h` and `BandSharp R N_h β K_e C_s` along every
  admissible trajectory (for `N_h + 2 = N`).

This construction is now part of `flow_master` (`Step2/Flow/FlowMaster.lean`), and
`flow_band_hyp0` is a projection of it (same statement).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-- **The hypothesis package of the final flow theorem, with the last two steps and the sharp
band at `j = N - 2`.** -/
theorem flow_band_hyp0 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB Cf Cb Cs : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ CL ∧ 0 ≤ Cf ∧ 0 ≤ Cb ∧ 0 ≤ Cs ∧ 2 * Cb * ε ≤ 1 / 4 ∧ cg * ε ≤ betaL L / 4 ∧
      ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧
      CL * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ CL ∧
      4 * sZ CL (CL * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε)) (Qh κ * (CL * ε)) ≤
        ((L : ℝ) ^ 2 - 1) / 4 ∧
      (∃ p q r s p₂ q₂ r₂ z₂ : ℝ,
        MonoZCoef ((L : ℝ) ^ 2) κ CL (CL * ε) CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂) ∧
      ρ ≤ 1 / 8 ∧ (∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 ρ) ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      (∃ e : ℕ → ℝ, (∀ j < Nh, ValidAt R j) ∧
        HDiff (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh ε ∧
        HHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh CL aB ε ∧
        ZHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh (zetaH R) CL (CL * ε) CL
          (CL * ε) 4 ε ∧
        MonoZHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh (zetaH R) CL (CL * ε) CL
          4 ε (3 / 4) ∧
        (∀ j, 0 ≤ e j) ∧
        (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
          |(rgData R).G j t - (t j).1 - betaL L * (t j).1 ^ 2| ≤
            e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) ∧
        (∀ j < Nh, e j ≤ 1 / 2 * betaL L) ∧
        (∀ j, 1 ≤ j → e j ≤ Ke * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2))) ∧
      (Nh + 2 = N → ValidAtL R Nh ∧ ∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut R Nh Cf (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut R Nh Cb (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
          BandSharp R Nh (betaL L) Ke Cs (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) := by
  obtain ⟨L₀, h⟩ := flow_master_basic
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨k, ε, aB, U, hX⟩ := h L hL
  obtain ⟨p, q, r, s, p₂, q₂, r₂, z₂, hC, -⟩ := U.mono
  refine ⟨k.ℓ, k.A, k.ρ, k.κ, k.cg, k.cm, k.cT, ε, k.Ke, k.CL, aB, k.Cf, k.Cb, k.Cs, U.hℓ, U.hA,
    U.hρ, U.hε, U.hκ0, U.hκ1, U.hcg, U.hcm, U.hcT, U.hKe, U.hCL, U.hCf, U.hCb, U.hCs, U.hCbε,
    U.hgβ, U.he, U.ha0, U.hs, ⟨p, q, r, s, p₂, q₂, r₂, z₂, hC⟩, U.hρ8, U.cov,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  have X := hX N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  obtain ⟨e, he0, F1s, heb, hej⟩ := X.sharp
  exact ⟨⟨e, X.valid, X.HD, X.H, X.HZ, X.HM, he0, F1s, heb, hej⟩, fun hN2 =>
    ⟨(X.top hN2).1, fun b μ₀ hb =>
      ⟨(X.glue hN2 b μ₀ hb.1).1, (X.glue hN2 b μ₀ hb.1).2.1, (X.glue hN2 b μ₀ hb.1).2.2.2⟩⟩⟩

end

end Step2
