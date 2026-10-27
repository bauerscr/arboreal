import PtCorr2.Zero.ExactHist
import PtCorr2.Zero.ZeroT
import Step2.Map.SplitSmall
import Step2.Last.FlowLastF1a

/-!
# The partition function along the trajectories of the flow (no extra hypotheses)

`hist_omega_traj`: along every trajectory `t = traj (rgData R) L² b μ₀` with `ValidAt` below
`N_h`, `ValidAtL` at `N_h`, `0 ≤ ρ < 1`, the splitting `SplitSmall R.P L ρ` and the coupling form
`V_N(B) = V_{κ_N}(B)` of the final object (from `GlueOut`):

`⟨Z_0⟩_{Γ_0} = ∏_{j ≤ N_h}[det(1 + a_jAΓ_j)e^{-u_{j+1}(Λ)}] · det(1 + a_{N-1}AΓ_{N-1})
e^{-u_N(Λ)} (1 + ũ_{N,N})`.

All hypotheses of `hist_omega` are discharged: `ValidCore` and `RawInv` from validity,
`SplitOK` from `SplitSmall` and `|ζ_i| ≤ ρ` (`rawHist_struct`), exactness from `traj_exact`,
`traj_exactL`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `SplitOK` at every raw state of a history, from `SplitSmall`. -/
theorem splitOK_hist (hρ0 : 0 ≤ R.ρ) (hspl : SplitSmall R.P L R.ρ) (hN : 1 ≤ N)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (t : Hist.Seq (Xs R))
    {j : ℕ} (hj : j < N) : SplitOK R j (rawHist R j t) := by
  obtain ⟨-, -, hb⟩ := rawHist_struct R hρ0 j t
  refine hspl.1 N R.msq hN hm0 hm _ (fun i => ?_) j hj
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact absorb_le R hρ0 _ _
  · rw [Function.update_of_ne hi]; exact hb i

/-- **The partition function along a trajectory.** -/
theorem hist_omega_traj {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N) =
      (∏ j ∈ range (Nh + 1), ch R j t) *
        (detStep R (Nh + 1) (histOut R Nh t).st * Complex.exp (-(lastOut R Nh t).u) *
          (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ))) := by
  intro t
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hLg := hVL.1
  have hcore : ∀ j ≤ Nh, ValidCore R j := fun j hj => by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  have hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t) := rawInv_histU R hV hVL t
  refine hist_omega R hN t hcore hRI (fun j _ => rawD_mem R _ _) (fun j _ => rawK_mem R _ _)
    (fun j hj => splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega))
    (fun j hj => traj_exact R hρ1 hLg b μ₀ (fun i hi => hV i (by omega)))
    (traj_exactL R hρ1 b μ₀ hV hVL) hVN

end

end PtCorr2
