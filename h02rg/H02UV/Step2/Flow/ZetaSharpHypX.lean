import Step2.FlowCont.FlowMsqStep
import Flow2.Shoot
import Step2.FlowCont.FlowDiffClamp
import Step2.Flow.FlowHor2Thm
import Step2.Flow.FlowFinalZAux
import Flow2.FixedRParamZ3
import Step2.Flow.ZetaSharp5
import Step2.Flow.FlowMaster

/-!
# The hypothesis package of the final flow theorem, with the dressed-covariance data exported

`flow_finalZ_hyp0_zetaX`: `flow_finalZ_hyp0_zeta` (`Step2/ZetaSharpHyp.lean`, same proof, same
construction) which in addition exports, with constants `c_z, K_G, K_z` depending only on `L`:

* `M_z(j+1) ≤ 2 c_z ǧ_j` along histories in the domain (`j < N_h`);
* `|Z_{j+1} C_j(0,0)| ≤ K_z` along histories in the domain (`Zcov_hist`, the diagonal);
* `|Z_{k+1} C_k(0,0) - log L/2π| ≤ (2π)^{-2}(E_C L^{-2k} + E_B m²(L^{2k} + L^{2(k+1)})) +
  K_G M_z(k+1)` for `1 ≤ k`, `k + 1 < N` (`Cprime_values`, first line; `XG_value_hist` gives
  both lines with one `ζ̄`, so `ρ` is unchanged).

`C'_{k+1}(0,0) = Z_{k+1} C_k(0,0)` (`G_eq_kern`). Used for (H_Γ) of `Spin2.prop_gamma_M`.

Now a projection of `flow_master` (`FlowMaster.lean`); `G_eq_kern` and `XG_value_hist` are stated
there.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-- **`flow_finalZ_hyp0_zeta` with the dressed-covariance data exported.** -/
theorem flow_finalZ_hyp0_zetaX : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB AZ cz KG Kz : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ CL ∧ cg * ε ≤ betaL L / 4 ∧
      ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧
      CL * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ CL ∧
      4 * sZ CL (CL * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε)) (Qh κ * (CL * ε)) ≤
        ((L : ℝ) ^ 2 - 1) / 4 ∧
      (∃ p q r s p₂ q₂ r₂ z₂ : ℝ,
        MonoZCoef ((L : ℝ) ^ 2) κ CL (CL * ε) CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂) ∧
      ρ ≤ 1 / 8 ∧ (∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 ρ) ∧ 0 ≤ AZ ∧ ε ≤ 1 ∧
      0 ≤ cz ∧ 0 ≤ KG ∧ 0 ≤ Kz ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      ∃ e : ℕ → ℝ,
        (∀ k < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε (k + 1) t →
          |Real.log ‖(rawHist R (k + 1 + 1) t).Z‖ - Real.log ‖(rawHist R (k + 1) t).Z‖ +
            betaL L / 3 * (t k).1| ≤ AZ * (t k).1 ^ 2 + AZ * (t k).1 * zA L R.msq k) ∧
        (∀ j < Nh, ValidAt R j) ∧
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
        (∀ j, 1 ≤ j → e j ≤ Ke * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2)) ∧
        (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
          (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cz * (t j).1) ∧
        (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
          ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) 0 0‖ ≤ Kz) ∧
        (∀ k, 1 ≤ k → k + 1 < N → (∀ i ≤ k, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
          ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) 0 0 -
              (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
            (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ k) ^ 2 +
              ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
            KG * (dData L N R.msq (zh R k t)).Mz (k + 1)) := by
  obtain ⟨L₀, h⟩ := flow_master_basic
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨k, ε, aB, U, hX⟩ := h L hL
  obtain ⟨p, q, r, s, p₂, q₂, r₂, z₂, hC, -⟩ := U.mono
  refine ⟨k.ℓ, k.A, k.ρ, k.κ, k.cg, k.cm, k.cT, ε, k.Ke, k.CL, aB, k.AZ, k.cz, k.KG, k.Kz, U.hℓ,
    U.hA, U.hρ, U.hε, U.hκ0, U.hκ1, U.hcg, U.hcm, U.hcT, U.hKe, U.hCL, U.hgβ, U.he, U.ha0, U.hs,
    ⟨p, q, r, s, p₂, q₂, r₂, z₂, hC⟩, U.hρ8, U.cov, U.hAZ, U.hε1, U.hcz, U.hKG, U.hKz,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  have X := hX N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  obtain ⟨e, he0, F1s, heb, hej⟩ := X.sharp
  exact ⟨e, X.zsteps, X.valid, X.HD, X.H, X.HZ, X.HM, he0, F1s, heb, hej, X.Mz, X.covZ, X.covVal⟩

/-- **`flow_finalZ_hyp0_zeta`**: the hypothesis package of `thm_flow_final` with the sharp `ζ` data (a projection of `flow_finalZ_hyp0_zetaX`). -/
theorem flow_finalZ_hyp0_zeta : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB AZ : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ CL ∧ cg * ε ≤ betaL L / 4 ∧
      ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧
      CL * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ CL ∧
      4 * sZ CL (CL * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε)) (Qh κ * (CL * ε)) ≤
        ((L : ℝ) ^ 2 - 1) / 4 ∧
      (∃ p q r s p₂ q₂ r₂ z₂ : ℝ,
        MonoZCoef ((L : ℝ) ^ 2) κ CL (CL * ε) CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂) ∧
      ρ ≤ 1 / 8 ∧ (∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 ρ) ∧ 0 ≤ AZ ∧ ε ≤ 1 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      ∃ e : ℕ → ℝ,
        (∀ k < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε (k + 1) t →
          |Real.log ‖(rawHist R (k + 1 + 1) t).Z‖ - Real.log ‖(rawHist R (k + 1) t).Z‖ +
            betaL L / 3 * (t k).1| ≤ AZ * (t k).1 ^ 2 + AZ * (t k).1 * zA L R.msq k) ∧
        (∀ j < Nh, ValidAt R j) ∧
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
  obtain ⟨L₀, h⟩ := flow_finalZ_hyp0_zetaX
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, AZ, cz, KG, Kz, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, -, -, -, hR⟩ := h L hL
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, AZ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  obtain ⟨e, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, -, -, -⟩ :=
    hR N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  exact ⟨e, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩

end

end Step2
