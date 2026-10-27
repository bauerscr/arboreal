import Step2.Flow.FlowFinalZHyp
import Step2.Last.FlowLastBand2
import Step2.Last.FlowLastLip6
import Flow2.Complete2
import Step2.Map.SplitSmall
import Step2.Flow.FlowMaster
import Step2.Flow.FlowMasterHypL

/-!
# The hypothesis package with the step `N - 2` in the Lipschitz layer

`flow_complete2_hyp0`: a copy of `flow_complete_hyp0` (`Step2/Flow/FlowCompleteHyp.lean`) with
* `LL.lip_rg_z2` in place of `lip_rg_z`: the same Lipschitz constant `C_L` also controls the
  differences of the step `N_h = N - 2` (under `ValidAtL`): (LGd), (Lmz), (LZ) and the zero mode
  `nW1H_{N-1}` entering the last step (constant `C_{NW}`);
* `monoZCoef_of_small_b` in place of `monoZCoef_of_small`: the cone constants are explicit
  (`p₂ = pTwo L C_L`, `r₂ = 2 + p₂`, `z₂ = 2(2C_L+1)`, `q₂ ≤ 1`);
* one more condition on `ε`: `kFin L ℓ C_L C_f C_{NW} ε ≤ 1/2` (the last map).
It exports, for `N_h + 2 = N`, `ValidAtL R N_h` and the difference bounds of the step `N_h`.

Now `flow_complete2_hyp0X` is a projection of `flow_master_hyp0L` (hence of `flow_master`,
`Step2/Flow/FlowMaster.lean`); `pTwo`, `bMu`, `bZe`, `bWz`, `kFin`, `BandF1` are stated in
`FlowMaster.lean`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2
/-- **The hypothesis package of the final flow theorem, with the last two steps**, with two
external requirements: `A` may be taken in any set `Aext L` containing a half-line, and `ε` in
any set `Eext L A c_R c_x` containing an interval `(0, ε₀)`; here `c_R = cR R₀ L² c_m C₂` and
`c_x = cx κ c_T` are the a priori constants. In addition to the conclusions of
`flow_complete2_hyp0` it exports the bulk data used by the observable flow: the step bounds
`StepBounds` (constants uniform in `N`), and, at every `N`, `ApHyp`, the mass condition and the
band (F1). -/
theorem flow_complete2_hyp0X (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB Cf Cb CNW : ℝ, Aext L A ∧
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
        (∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧ BandF1 R Nh κ cg cm cT ε) := by
  obtain ⟨L₀, h⟩ := flow_master_hyp0L Aext hAext Eext hEext
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, AZ, cz, KG, Kz, hAx, -, -, -, -,
    C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε, hκ0,
    hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov, -,
    h⟩ := h L hL
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, hAx, C₀x, ηx, εsx, CKx, C₂x, CDx,
    Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hCL,
    hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh =>
      let ⟨a, b, c, d, _⟩ := h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
      ⟨a, b, c, d⟩⟩

/-- **The hypothesis package of the final flow theorem, with the last two steps.** -/
theorem flow_complete2_hyp0 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB Cf Cb CNW : ℝ, 0 ≤ CNW ∧ kFin L ℓ CL Cf CNW * ε ≤ 1 / 2 ∧
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
          2 * ℓ ^ 2 * ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ + CNW * M) := by
  obtain ⟨L₀, h⟩ := flow_complete2_hyp0X (fun _ _ => True) (fun _ => ⟨0, fun _ _ => trivial⟩)
    (fun _ _ _ _ _ => True) (fun _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, -, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx,
    Clx, cSx, -, -, hCNW, hkf, hε1, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb,
    hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov, h⟩ := h L hL
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, hCNW, hkf, hε1, hℓ, hA, hρ, hε, hκ0,
    hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh =>
      let ⟨a, b, c, _⟩ := h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
      ⟨a, b, c⟩⟩

end

end Step2
