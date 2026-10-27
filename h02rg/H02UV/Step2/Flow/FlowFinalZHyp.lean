import Step2.FlowCont.FlowMsqStep
import Flow2.Shoot
import Step2.FlowCont.FlowDiffClamp
import Step2.Flow.FlowHor2Thm
import Step2.Flow.FlowFinalZAux
import Flow2.FixedRParamZ3
import Step2.Flow.FlowMaster

/-!
# The hypothesis package of the final flow theorem without the mass condition

`flow_finalZ_hyp0`: a merge of the proofs of `flow_final_hyp0` (`Step2/FlowFinalHyp.lean`: sharp
(F1) with the summable `e_j`, `CovContM`, `ValidAt`, `HDiff`) and `thm_flow_hor2`
(`Step2/Flow/FlowHor2Thm.lean`: the sharp `|ζ_j| ≤ c_ζ ǧ_j` for the (F1) mass term, the Lipschitz
bounds `lip_rg_z` with the separate `ζ`-channel). For **every** `N_h + 2 ≤ N` and every
`0 < m² ≤ L^{-2(N-1)}` (no `m² L^{2(N_h+1)} ≤ ϑ`) it exports, with constants independent of
`N, m², N_h`:
* `HHyp` with large constants `(C_L, a_B)` (existence, band, continuity);
* `ZHyp` (uniqueness and the signed cone, hidden coupling `ζ`, `b_ζ = 4`) and its numerical
  conditions `C_L ε ≤ a0h((1+L²)/2, κ, C_L)`, `4 s_Z ≤ (L²-1)/4`;
* `MonoZHyp` (monotonicity, fading memory `3/4`) and `MonoZCoef` (`monoZCoef_of_small`);
* the sharp (F1) with `e_j = (32/7) e_{A,j} + E_{0,j}`, `e_j ≤ β/2`,
  `e_j ≤ K_e(L^{-2j} + m²L^{2(j+1)})`;
* `HDiff`, `ValidAt`, `CovContM`, `ρ ≤ 1/8`, `ε ≤ ε₀`, `c_g ε ≤ β/4`.
The mass input of (F1) is `e_{A,j} = (8/7) c_ζ (M₀+1) m² L^{2j}` with `m² L^{2j} ≤ L^{-4}`
(`msq_j4`) and `c_ζ = O(L²)`, so `K_e = O(L²)`.

Now a projection of `flow_master` (`FlowMaster.lean`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-- **The hypothesis package of the final flow theorem without the mass condition.** -/
theorem flow_finalZ_hyp0 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ CL ∧ cg * ε ≤ betaL L / 4 ∧
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
      ∃ e : ℕ → ℝ, (∀ j < Nh, ValidAt R j) ∧
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
        (∀ j, 1 ≤ j → e j ≤ Ke * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2)) := by
  obtain ⟨L₀, h⟩ := flow_master_basic
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨k, ε, aB, U, hX⟩ := h L hL
  obtain ⟨p, q, r, s, p₂, q₂, r₂, z₂, hC, -⟩ := U.mono
  refine ⟨k.ℓ, k.A, k.ρ, k.κ, k.cg, k.cm, k.cT, ε, k.Ke, k.CL, aB, U.hℓ, U.hA, U.hρ, U.hε, U.hκ0,
    U.hκ1, U.hcg, U.hcm, U.hcT, U.hKe, U.hCL, U.hgβ, U.he, U.ha0, U.hs,
    ⟨p, q, r, s, p₂, q₂, r₂, z₂, hC⟩, U.hρ8, U.cov,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  have X := hX N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  obtain ⟨e, he0, F1s, heb, hej⟩ := X.sharp
  exact ⟨e, X.valid, X.HD, X.H, X.HZ, X.HM, he0, F1s, heb, hej⟩

end

end Step2
