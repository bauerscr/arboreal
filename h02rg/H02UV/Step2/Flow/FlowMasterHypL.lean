import Step2.Flow.FlowMasterHypLZ
import Step2.Flow.ZetaSharpHypX

/-!
# The master hypothesis package with `ValidLast` exported (copy of `Step2/FlowMasterHyp.lean`)

`flow_master_hyp0L`: `flow_master_hyp0` (same proof, same construction) which in addition exports
`LastN.ValidLast R (N_h + 1)` (the validity of the last step, already used internally for the
last two steps). Below: the original description.

`flow_master_hyp0`: `flow_complete2_hyp0X` (`Step2/Flow/FlowComplete2Hyp.lean`, same proof, same
construction, with `ρ` additionally below the `ζ̄` of `XG_value_hist`) which in addition exports
the data of `flow_finalZ_hyp0_zetaX` (`Step2/Flow/ZetaSharpHypX.lean`): the sharp per-step bound of
`log|Z|` (constant `A_Z`), and, with constants `c_z, K_G, K_z` depending only on `L`,
`M_z(j+1) ≤ 2c_zǧ_j`, `|Z_{j+1}C_j(0,0)| ≤ K_z` and the value of `Z_{k+1}C_k(0,0)`.
So the conclusions of `thm_flow_complete2X` and of `Spin2.thm_flow_final_spinX` hold with one set
of constants (`Spin2/Master/Master.lean`).

Now `flow_master_hyp0L` is a projection of `flow_master_hyp0LZD` (hence of `flow_master`,
`Step2/Flow/FlowMaster.lean`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-- **The master hypothesis package**: `flow_complete2_hyp0X` together with the exports of
`flow_finalZ_hyp0_zetaX` (sharp `log|Z|` steps, `M_z`, `|Z C(0,0)|`, the value of `Z C(0,0)`). -/
theorem flow_master_hyp0L (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB Cf Cb CNW AZ cz KG Kz : ℝ, Aext L A ∧
      0 ≤ AZ ∧ 0 ≤ cz ∧ 0 ≤ KG ∧ 0 ≤ Kz ∧
      ∃ C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx : ℝ,
        StepBounds L A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx ∧
        (∀ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ → Eext L A (cR R₀ ((L : ℝ) ^ 2) cm C₂x) (cx κ cT) ε) ∧
      0 ≤ CNW ∧ kFin L ℓ CL Cf CNW * ε ≤ 1 / 2 ∧
      ε ≤ 1 ∧ 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ CL ∧ 0 ≤ Cf ∧ 0 ≤ Cb ∧ 2 * Cb * ε ≤ 1 / 4 ∧ cg * ε ≤ betaL L / 4 ∧
      ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧
      CL * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ CL ∧
      4 * sZ CL (CL * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε)) (Qh κ * (CL * ε)) ≤
        ((L : ℝ) ^ 2 - 1) / 4 ∧
      (∃ p q r s p₂ q₂ r₂ z₂ : ℝ,
        MonoZCoef ((L : ℝ) ^ 2) κ CL (CL * ε) CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂ ∧
          p₂ = pTwo L CL ∧ r₂ = 2 + p₂ ∧ z₂ = 2 * (2 * CL + 1) ∧ q₂ ≤ 1) ∧
      ρ ≤ 1 / 8 ∧ SplitSmall Pc L ρ ∧ (∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 ρ) ∧
    (∀ (N : ℕ) (R : RGPar 2 L N), R.P = Pc → R.ℓ = ℓ → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ∀ Nh : ℕ, Nh + 2 = N →
        LastN.ValidLast R (Nh + 1)) ∧
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
      (Nh + 2 = N → ∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut R Nh Cf (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut R Nh Cb (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) ∧
      (Nh + 2 = N → ValidAtL R Nh ∧
        ∀ t t', InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t →
          InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t' →
        ∀ M, 0 ≤ M → (∀ i < Nh, (3 / 4 : ℝ) ^ (Nh - 1 - i) * dist3 (t i) (t' i) ≤ M) →
        |(rgData R).G Nh t - (rgData R).G Nh t' - ((t Nh).1 - (t' Nh).1)| ≤
          CL * ε * |(t Nh).1 - (t' Nh).1| +
          CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ + CL * ε * M ∧
        |(rgData R).m Nh t - (rgData R).m Nh t'| ≤ CL * |(t Nh).1 - (t' Nh).1| +
          CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ +
          CL * ε * M + 4 * ‖zetaH R Nh t - zetaH R Nh t'‖ ∧
        ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ ≤
          CL * (|(t Nh).1 - (t' Nh).1| + ‖(t Nh).2.2 - (t' Nh).2.2‖) +
          CL * ε * (|(t Nh).2.1 - (t' Nh).2.1| + M) ∧
        ‖nW1H R (Nh + 1) t - nW1H R (Nh + 1) t'‖ ≤
          2 * ℓ ^ 2 * ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ + CNW * M) ∧
      (ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εsx C₀x C₂x Cqx Clx cSx ∧
        (∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧ BandF1 R Nh κ cg cm cT ε) ∧
      ((∀ k < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε (k + 1) t →
          |Real.log ‖(rawHist R (k + 1 + 1) t).Z‖ - Real.log ‖(rawHist R (k + 1) t).Z‖ +
            betaL L / 3 * (t k).1| ≤ AZ * (t k).1 ^ 2 + AZ * (t k).1 * zA L R.msq k) ∧
        (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
          (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cz * (t j).1) ∧
        (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
          ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) 0 0‖ ≤ Kz) ∧
        (∀ k, 1 ≤ k → k + 1 < N → (∀ i ≤ k, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
          ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) 0 0 -
              (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
            (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ k) ^ 2 +
              ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
            KG * (dData L N R.msq (zh R k t)).Mz (k + 1))) := by
  obtain ⟨L₀, h⟩ := flow_master_hyp0LZD Aext hAext Eext hEext (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, AZ, cz, KG, Kz, hAx, -, hAZ, hcz, hKG,
    hKz, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, -, hcov,
    hVL, h⟩ := h L hL
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, AZ, cz, KG, Kz, hAx, hAZ, hcz, hKG,
    hKz, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov, hVL,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh =>
      let ⟨a, g, c, d, e⟩ := h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
      ⟨a, fun hN2 b μ₀ hb => ⟨(g hN2 b μ₀ hb.1).1, (g hN2 b μ₀ hb.1).2.1⟩, c, d, e⟩⟩

end

end Step2
