import Spin2.Pair.PairJoint4
import Spin2.Master.MasterAllFactsD
import PtCorr2.Pair.PairEStep1
import PtCorr2.Obs.GamWKBd
import PtCorr2.Obs.ObsHistTop

/-!
# The `E`-step of the joint induction: trajectory facts from the master construction

* **`hBeta_ratio`**: `|β_{a,k}| ≤ (64/49)|β_{a,k+1}|` for `k ≤ N_h` (from the exact `β_a` step
  `hBeta_rel_of`: `‖𝔫‖ ≤ 1/8`, `‖err‖ ≤ (1/7)|β_{a,k+1}|` by `Case2Rel`/`Case2TopStep`), and its
  iterate **`hBeta_ratio_pow`**: `|β_{a,i}| ≤ (64/49)^{k-i}|β_{a,k}|` (`i ≤ k ≤ N_h + 1`).
* **`MasterCore.pairTraj`**: along every admissible trajectory of the master construction:
  `ValidAt` below `N_h`, `ValidAtL` at `N_h` (validity above `N_h` is not needed: the memory terms
  only use the covariances up to `N_h`, `PtCorr2.memABX_hist_leL`), `GoodCov2 k (s_k) (C_k)` for
  `k ≤ N_h` (`goodCov2_histS`, `goodCov2_histSL`), `ValidCore ∧ RawInv` for `i ≤ N_h`.
* **`pairBetaRatio_MF`**: the ratio for every `x ≠ 0` under `MasterFacts` (`relG`, `loop`, `top`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **`|β_{a,k}| ≤ (64/49)|β_{a,k+1}|`** along the pair history (`k ≤ N_h`). -/
theorem hBeta_ratio {Nh : ℕ} (hN : Nh + 2 = N) {m b μ₀ cδ : ℝ} (hb : 0 < b) (x : Lam 2 L N)
    (hrel : Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀) :
    ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ 64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖ := by
  intro k hk
  obtain ⟨-, -, hfl, herr⟩ := hBeta_rel_of R hN hb x hrel hn htop k hk
  set β := hBeta R m b μ₀ x k
  set β' := hBeta R m b μ₀ x (k + 1)
  set n := nn2 R (ptsX x) (zV b) m b μ₀ k
  set e := err2 R (ptsX x) (zV b) m b μ₀ k
  have hnk : ‖n‖ ≤ 1 / 8 := by
    rcases Nat.lt_or_ge k Nh with h | h
    · exact hn k h
    · obtain rfl : k = Nh := by omega
      exact htop.1
  have hu : (if k < Nh then 8 / 7 * (cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2)
      else (1 / 7 : ℝ)) ≤ 1 / 7 := by
    split_ifs with h
    · have := (hrel k h).2; linarith
    · exact le_rfl
  have he : ‖e‖ ≤ 1 / 7 * ‖β'‖ := herr.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  have h1 : (1 - n) * β = β' + e := by rw [hfl]; ring
  have h2 : ‖1 - n‖ * ‖β‖ ≤ 8 / 7 * ‖β'‖ := by
    rw [← norm_mul, h1]
    exact (norm_add_le _ _).trans (by linarith)
  have h3 : 7 / 8 ≤ ‖1 - n‖ := by
    have := norm_sub_norm_le (1 : ℂ) n
    rw [norm_one] at this
    have := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) (1 - n) 0
    have h4 : ‖(1 : ℂ) - (1 - n)‖ = ‖n‖ := by rw [sub_sub_cancel]
    rw [sub_zero, sub_zero, norm_one, h4] at this
    linarith
  have hβ0 := norm_nonneg β
  have : 7 / 8 * ‖β‖ ≤ 8 / 7 * ‖β'‖ := (mul_le_mul_of_nonneg_right h3 hβ0).trans h2
  linarith

/-- **The iterated ratio**: `|β_{a,i}| ≤ (64/49)^{k-i}|β_{a,k}|` for `i ≤ k ≤ N_h + 1`. -/
theorem hBeta_ratio_pow {Nh : ℕ} {m b μ₀ : ℝ} (x : Lam 2 L N)
    (h : ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ 64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖) :
    ∀ i k, i ≤ k → k ≤ Nh + 1 →
      ‖hBeta R m b μ₀ x i‖ ≤ (64 / 49 : ℝ) ^ (k - i) * ‖hBeta R m b μ₀ x k‖ :=
  PtCorr2.ratio_pow_le (β := fun k => ‖hBeta R m b μ₀ x k‖) (by norm_num) (K := Nh + 1)
    (fun i hi => h i (by omega)) (fun _ => norm_nonneg _)

end Traj

set_option maxHeartbeats 4000000 in
/-- **Trajectory facts of the master construction for the `E`-step**: validity below `N_h`,
`ValidAtL` at `N_h`, `GoodCov2` at the field scale up to `N_h`, `ValidCore ∧ RawInv` up to
`N_h`. -/
theorem MasterCore.pairTrajD {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) :
    (∀ i < Nh, ValidAt (R.withMsq m) i) ∧ ValidAtL (R.withMsq m) Nh ∧
    (∀ k ≤ Nh, GoodCov2 k (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)) ∧
    (∀ i ≤ Nh, ValidCore (R.withMsq m) i ∧
      RawInv (R.withMsq m) i (rawHist (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id D.hC2
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = D.A := hRA
  have hSB' : StepBounds L R'.A D.C₀x D.ηx D.εsx D.CKx D.C₂x D.CDx D.Cqx D.Clx D.cSx := by
    rw [hRA']; exact D.hSBx
  have hβ2 := betaL_ge (by have := D.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  refine ⟨hV, hVL, fun k hk => ?_, fun i hi => ?_⟩
  · have htk := inDh_rg_of_D R' F1 hD k hk
    rcases Nat.lt_or_ge k Nh with h | h
    · exact PtCorr2.goodCov2_histS R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H t k h htk
    · obtain rfl : k = Nh := by omega
      exact PtCorr2.goodCov2_histSL R' hSB' hV hm1 hVL hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H t htk
  · refine ⟨?_, rawInv_histU R' hV hVL t i (by omega)⟩
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · obtain rfl : i = Nh := by omega
      exact hVL.2

/-- Corollary of `MasterCore.pairTrajD` (`Admissible` ⟹ the domain condition). -/
theorem MasterCore.pairTraj {L : ℕ} [NeZero L] (D : MasterCore L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μ₀) :
    (∀ i < Nh, ValidAt (R.withMsq m) i) ∧ ValidAtL (R.withMsq m) Nh ∧
    (∀ k ≤ Nh, GoodCov2 k (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)) ∧
    (∀ i ≤ Nh, ValidCore (R.withMsq m) i ∧
      RawInv (R.withMsq m) i (rawHist (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))  :=
  MasterCore.pairTrajD D N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

set_option maxHeartbeats 1000000 in
/-- **The `β_a` ratio under `MasterFacts`** for every `x` along admissible trajectories. -/
theorem pairBetaRatio_MFD {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) :
    ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ 64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖ := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨q, -, -, hl⟩ :=
    (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b)).2.2
  exact hBeta_ratio R hNh hb x
    (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b) (zV_mua_ne hb))
    (fun k hk => (hl k hk).1)
    (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)).1

/-- Corollary of `pairBetaRatio_MFD` (`Admissible` ⟹ the domain condition). -/
theorem pairBetaRatio_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (x : Lam 2 L N) :
    ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ 64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖  :=
  pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm.1 x

end

end Spin2
