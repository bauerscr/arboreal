import Spin2.Cont.ContScaleM
import PtCorr2.Restart.RerepState

/-!
# B3, T6 input: the coupling of the difference datum (`|δβ| ≲ |β_k|(ǧ_k + a_k)`)

Along the Case-(2) one-point history of the trajectory (`bt2`), the observable state at scale `k`
with vertex position `P.a` is `obsHist (R.withMsq m) P (obsInit V P) k t`. For two positions `P`,
`P'` (same `k`-block, `PtCorr2.rr_restart_identity'`) the difference datum is
`δ = rrStH(o^P) − o^{P'}` (Loc point `P'.a`). Its total coupling is (**`cd_delta_beta`**)
`β^δ_k = β^P_k − β^{P'}_k` (the relocation does not change `∑_B m₂(V(B)_a)`), hence
(**`cd_delta_beta_le`**, `csm_artefact_rel`) `‖β^δ_k‖ ≤ 4K_λ(ǧ_k + a_k)‖β^{P'}_k‖`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

noncomputable section

open Step Step2 PtCorr2
open Finset Grassmann Loc FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

theorem cd_betaTot2_fullV {N : ℕ} (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
    (o : ObsSt .two L N) (k : ℕ) : betaTot2 k (fullV R j st g μ o) = betaTot2 k o.V := by
  unfold betaTot2
  refine sum_congr rfl fun b _ => ?_
  simp [fullV, embF]

/-- `β_k = ∑_B m₂(V^{obs}_k(B)_a)` of the observable state. -/
theorem cd_bt2_eq {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : ObsPts 2 L N) (V : OCoup .two) (m b μ₀ : ℝ) (k : ℕ) :
    bt2 R P V m b μ₀ k = betaTot2 k (obsHist (R.withMsq m) P (obsInit .two V P) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V := by
  rw [bt2, histVO2, cd_betaTot2_fullV]

/-- **The coupling of the difference datum** is the difference of the couplings. -/
theorem cd_delta_beta {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P P' : ObsPts 2 L N) (V : OCoup .two) (m b μ₀ : ℝ) (k : ℕ) (β : (Fin 2 → ℕ) → ℂ) :
    betaTot2 k (subSt (rrStH (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β
      (obsHist (R.withMsq m) P (obsInit .two V P) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      (obsHist (R.withMsq m) P' (obsInit .two V P') k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))).V =
      bt2 R P V m b μ₀ k - bt2 R P' V m b μ₀ k := by
  rw [cd_bt2_eq, cd_bt2_eq, rrStH, rr_delta_beta]

/-- **`|δβ_k| ≤ 4K_λ(ǧ_k + a_k)|β^{P'}_k|`** (`csm_artefact_rel`, master constants). -/
theorem cd_delta_beta_le (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)]
    (hP : R.P = Step2.D2.Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P P' : ObsPts 2 L N) (V : OCoup .two) (hmu : OCoup2.mua V ≠ 0)
    {k : ℕ} (hk : k < Nh)
    (hs0 : 0 ≤ M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hs : M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤ 1 / 2)
    (β : (Fin 2 → ℕ) → ℂ) :
    ‖betaTot2 k (subSt (rrStH (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β
      (obsHist (R.withMsq m) P (obsInit .two V P) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
      (obsHist (R.withMsq m) P' (obsInit .two V P') k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))).V‖ ≤
      4 * (M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) *
        ‖bt2 R P' V m b μ₀ k‖ := by
  rw [cd_delta_beta]
  exact csm_artefact_rel M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P P' V hmu hk hs0 hs

end

end Spin2
