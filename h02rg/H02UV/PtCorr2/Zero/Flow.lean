import PtCorr2.Zero.Glue
import PtCorr2.Zero.ChainFlow
import Step2.Flow.FlowComplete2

/-!
# The zero-mode integration along the complete flow (`sec:corr`, "The last scale")

`thm_zero_mode_flow`: the conclusions of `Step2.thm_flow_complete2` (the flow with horizon
`N_h = N - 2`, the last two steps, the unique, `m²`-continuous shooting `Re ǧ_N = 1/β_R`, and
`ρ ≤ 1/8`) and, for every mass `m² ∈ mRange L N` and every admissible trajectory,
`ZeroModeOut` (`PtCorr2/Zero/Glue.lean`): the zero-mode integration of the final-scale object
restricted to constant fields, `Rc Z̃_{N,N} = 1 + ũ_{N,N} - |Λ| ã_{N,N} ψψ̄`, with `|k⁰| = O(ǧ²)`,
`|Λ| ã_{N,N}/Z_N = L^{2N} ν_N/Z_N + O(ǧ²)`, `L^{2N} ν_N/Z_N = O(ǧ)`, `ǧ = ǧ_{N-2}`. At the shooting
solution `|ǧ_{N-2} - 1/β_R| ≤ 4 C_b β_R^{-2}`, so these errors are `O(β_R^{-2})`.

`Z_N ≠ 0` holds along every history as soon as `ρ < 1` (`rawHist_Z_ne'`, `lastOut_Z_ne`): every
`Z_{j+1} = Z_j (1 + ζ_j)` with the clamped `|ζ_j| ≤ ρ`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2 Step2.D2 Step

variable {L N : ℕ} [NeZero L]

/-- `Z_j ≠ 0` along every history if `ρ < 1` (no validity needed). -/
theorem rawHist_Z_ne' (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hρ : 0 ≤ R.ρ) (hρ1 : R.ρ < 1) :
    ∀ (j : ℕ) (t : Hist.Seq (Xs R)), (rawHist R j t).Z ≠ 0
  | 0, _ => one_ne_zero
  | j + 1, t => by
    show stZ' R (rawHist R j t) ≠ 0
    exact mul_ne_zero (rawHist_Z_ne' R hρ hρ1 j t)
      (Step2.one_add_ne_zero ((absorb_le R hρ _ _).trans_lt hρ1))

/-- `Z_N ≠ 0` for the final-scale object along every history if `ρ < 1`. -/
theorem lastOut_Z_ne (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hρ : 0 ≤ R.ρ)
    (hρ1 : R.ρ < 1) (Nh : ℕ) (t : Hist.Seq (Xs R)) : (lastOut R Nh t).Z ≠ 0 :=
  rawHist_Z_ne' R hρ hρ1 (Nh + 2) t

/-- **`thm:flow` with the last two steps and the zero-mode integration**: the conclusions of
`Step2.thm_flow_complete2` (same constants) and `ZeroModeOut` along every admissible
trajectory. -/
theorem thm_zero_mode_flow : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ Cf ∧ 0 ≤ Cb ∧ 2 * Cb * ε ≤ 1 / 4 ∧ ρ ≤ 1 / 8 ∧ SplitSmall Pc L ρ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N →
      ((∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
      MsqConcl R κ cm cT Nh ε (mRange L N) ∧
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      ContinuousOn (fun q : ℝ × ℝ => gFinB R κ cm cT Nh ε q.1 q.2)
        (UfixM R κ cm cT Nh ε (mRange L N)) ∧
      (∀ m ∈ mRange L N, ∀ βR : ℝ, 2 / ε ≤ βR →
        ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
      (∀ m ∈ mRange L N, ∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, ∀ βR : ℝ,
        gFinB R κ cm cT Nh ε m b = 1 / βR →
        |Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b - 1 / βR| ≤ 4 * Cb * (1 / βR) ^ 2) ∧
      -- strict monotonicity, uniqueness, continuity in `m²`
      (∀ m ∈ mRange L N, StrictMonoOn (gFinB R κ cm cT Nh ε m)
        (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)) ∧
      (∀ m ∈ mRange L N, ∀ βR : ℝ, 2 / ε ≤ βR →
        ∃! b, b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
          gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
      (∀ βR : ℝ, 2 / ε ≤ βR →
        (∀ m ∈ mRange L N, bFin R κ cm cT Nh ε m (1 / βR) ∈
            Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
          gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m (1 / βR)) = 1 / βR) ∧
        ContinuousOn (fun m => bFin R κ cm cT Nh ε m (1 / βR)) (mRange L N)) ∧
      -- validity of the parameters (exported for the zero-mode integration)
      (∀ m ∈ mRange L N, (∀ j < Nh, ValidAt (R.withMsq m) j) ∧ ValidAtL (R.withMsq m) Nh)) ∧
      -- the zero-mode integration of the final-scale object
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        ZeroModeOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      -- the partition function along the trajectory
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        omegaC (Γh (R.withMsq m) 0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (Zh (R.withMsq m) 0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : Alg 2 L N) =
          (∏ j ∈ range (Nh + 1), ch (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) *
            (detStep (R.withMsq m) (Nh + 1)
                (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st *
              Complex.exp (-(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u) *
              (1 + uFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
                (zmRaw (R.withMsq m) (Nh + 1)
                  (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ)))) := by
  obtain ⟨L₀, h⟩ := thm_flow_complete2
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCf, hCb, hCbε, hρ8, hspl, H⟩ := h L hL
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCf, hCb, hCbε, hρ8, hspl, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  have main := H N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  obtain ⟨-, -, hGB, -, -, -, -, -, -, hval⟩ := id main
  refine ⟨main, fun m hm b μ₀ hadm => ?_, fun m hm b μ₀ hadm => ?_⟩
  · obtain ⟨hglue, -⟩ := hGB m hm b μ₀ hadm
    have hg := (hadm.1 Nh le_rfl).1
    have hZ := lastOut_Z_ne (R.withMsq m) (show 0 ≤ R.ρ by rw [hRρ]; exact hρ.le)
      (show R.ρ < 1 by rw [hRρ]; linarith) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
    exact zeroModeOut_of_glue (R.withMsq m) hNh hCf _ hg.le hglue hZ
  · obtain ⟨hglue, -⟩ := hGB m hm b μ₀ hadm
    obtain ⟨-, -, -, -, -, hB, -⟩ := hglue.2
    obtain ⟨hV, hVL⟩ := hval m hm
    have hspl' : SplitSmall (R.withMsq m).P L (R.withMsq m).ρ := by
      show SplitSmall R.P L R.ρ
      rw [hP, hRρ]; exact hspl
    exact hist_omega_traj (R.withMsq m) hNh (show R.ρ < 1 by rw [hRρ]; linarith) hspl' hm.1 hm.2
      hV hVL b μ₀ fun c hc => (hB c hc).1

end

end PtCorr2
