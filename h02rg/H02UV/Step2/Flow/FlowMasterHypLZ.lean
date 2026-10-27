import Step2.Flow.FlowMaster
import Step2.Flow.ZetaSharpHypX
import Step2.Last.ZeroTOk
import Step2.Flow.FlowWin2

/-!
# The master hypothesis package with the zero-mode bound exported (copy of `Step2/Flow/FlowMasterHypL.lean`)

`flow_master_hyp0LZ`: `flow_master_hyp0L` (same proof) with `ρ` additionally below the `ζ̄` of
`prop_last_d2` (`zeroTOk_of_d2`), and in addition the export `ZeroTOk L ρ`: along every dressed
history with `|ζ_i| ≤ ρ` the normalised zero mode `t = Z_N Γ̂^int_N(0)` of the last step satisfies
`|m²t - 1| ≤ K m² L^{2N}`. This is the only change of the construction.

The construction is now `flow_master` (`Step2/Flow/FlowMaster.lean`, which also exports the sharp
band `BandSharp` of `flow_band_hyp0`); `flow_master_hyp0LZD` is its instance with the external
requirements `Eext`, `Gext` on `ε`, and `flow_master_hyp0` a projection. `inDh_rg_of_D` is stated
in `FlowMaster.lean`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2
/-- **The master hypothesis package, glue along every trajectory in `D_ε`** (route (a1): the last two
steps need only the domain up to `N_h`, no final condition). **The master hypothesis package**: `flow_complete2_hyp0X` together with the exports of
`flow_finalZ_hyp0_zetaX` (sharp `log|Z|` steps, `M_z`, `|Z C(0,0)|`, the value of `Z C(0,0)`).
Route (a1): a second external requirement `Gext L ℓ ρ C_f c_m ε` on `ε` (which may depend on the
internal constants `ℓ, ρ, C_f, c_m`, fixed before `ε`), and the value `c_m = (48L² + 8)ℓ²/49 + 1`.
The window requirement `K_h((1+L²)/2, κ, C_L)·C_Lε·c_μ ≤ 1/12` (`C_L` the exported Lipschitz
constant, fixed before `ε`) is imposed in the `ε` choice and exported with `Gext`. -/
theorem flow_master_hyp0LZD (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε)
    (Gext : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hGext : ∀ (L : ℕ) (ℓ ρ Cf cm : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Gext L ℓ ρ Cf cm ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB Cf Cb CNW AZ cz KG Kz : ℝ, Aext L A ∧
      (cm = 3 * (L : ℝ) ^ 2 * (16 * ℓ ^ 2 / 49) + 8 * ℓ ^ 2 / 49 + 1 ∧ Gext L ℓ ρ Cf cm ε ∧
        Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε) * cmu ((L : ℝ) ^ 2) cm ≤ 1 / 12) ∧
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
      ρ ≤ 1 / 8 ∧ SplitSmall Pc L ρ ∧ ZeroTOk L ρ ∧ (∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 ρ) ∧
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
      (Nh + 2 = N → ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j)) →
        GlueOut R Nh Cf (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut R Nh Cb (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
          ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ.nu /
              (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).Z -
            (L : ℂ) ^ 4 * (((traj (rgData R) ((L : ℝ) ^ 2) b μ₀ Nh).2.1 : ℝ) : ℂ)‖ ≤
            cNuLast R ((L : ℝ) ^ 2) cm ε * (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ Nh).1) ∧
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
  obtain ⟨L₀, h⟩ := flow_master Aext hAext
    (fun L k ε => ∀ hL : L ≠ 0, haveI : NeZero L := ⟨hL⟩
      Eext L k.A (cR (⟨Pc, 0, k.ℓ, k.A, 0, k.ρ⟩ : RGPar 2 L 1) ((L : ℝ) ^ 2) k.cm k.C₂)
        (cx k.κ k.cT) ε ∧ Gext L k.ℓ k.ρ k.Cf k.cm ε)
    (fun L k => by
      by_cases hL : L = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd hL h
      · haveI : NeZero L := ⟨hL⟩
        exact ((hEext L k.A _ _).and (hGext L k.ℓ k.ρ k.Cf k.cm)).mono fun _ hε _ => hε)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨k, ε, aB, hAx, hPx, U, hX⟩ := h L hL
  obtain ⟨hEx, hGx⟩ := hPx (NeZero.ne L)
  refine ⟨k.ℓ, k.A, k.ρ, k.κ, k.cg, k.cm, k.cT, ε, k.Ke, k.CL, aB, k.Cf, k.Cb, k.CNW, k.AZ, k.cz,
    k.KG, k.Kz, hAx, ⟨U.cm_eq, hGx, U.hKhW⟩, U.hAZ, U.hcz, U.hKG, U.hKz, k.C₀, k.η, k.εs, k.CK,
    k.C₂, k.CD, k.Cq, k.Cl, k.cS, U.step,
    fun R₀ hR₀ => by rw [cR_congr (R' := (⟨Pc, 0, k.ℓ, k.A, 0, k.ρ⟩ : RGPar 2 L 1)) hR₀]; exact hEx,
    U.hCNW, U.hkFin, U.hε1, U.hℓ, U.hA, U.hρ, U.hε, U.hκ0, U.hκ1, U.hcg, U.hcm, U.hcT, U.hKe,
    U.hCL, U.hCf, U.hCb, U.hCbε, U.hgβ, U.he, U.ha0, U.hs, U.mono, U.hρ8, U.split, U.zeroT, U.cov,
    U.validLast, fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  have X := hX N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  obtain ⟨e, he0, F1s, heb, hej⟩ := X.sharp
  exact ⟨⟨e, X.valid, X.HD, X.H, X.HZ, X.HM, he0, F1s, heb, hej⟩,
    fun hN2 b μ₀ hb => let g := X.glue hN2 b μ₀ hb; ⟨g.1, g.2.1, g.2.2.1⟩, X.top,
    ⟨X.aph, X.msq1, X.band⟩, X.zsteps, X.Mz, X.covZ, X.covVal⟩

set_option maxHeartbeats 4000000 in
/-- **The master hypothesis package** (along admissible trajectories; a corollary of `flow_master_hyp0LZD`): `flow_complete2_hyp0X` together with the exports of
`flow_finalZ_hyp0_zetaX` (sharp `log|Z|` steps, `M_z`, `|Z C(0,0)|`, the value of `Z C(0,0)`). -/
theorem flow_master_hyp0 (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
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
  obtain ⟨L₀, h0⟩ := flow_master_hyp0LZD Aext hAext Eext hEext (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, AZ, cz, KG, Kz, hAx, -, hAZ, hcz, hKG,
    hKz, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, -, hcov,
    -, h⟩ := h0 L hL
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, AZ, cz, KG, Kz, hAx, hAZ, hcz, hKG,
    hKz, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh =>
      ⟨(h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh).1,
        fun hN2 b μ₀ hb => ⟨((h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh).2.1 hN2 b μ₀ hb.1).1,
          ((h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh).2.1 hN2 b μ₀ hb.1).2.1⟩,
        (h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh).2.2⟩⟩

end

end Step2
