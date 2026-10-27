import Spin2.Gam.LastOneM
import Spin2.Pair.PairInitReq
import Spin2.Pair.PairInitW
import PtCorr2.Zero.EpsFlow
import PtCorr2.Pair.SeedSplit2

/-!
# The seed of the `ab` chain in the `wM` weights (wiring `PairInitConclW` into `obs_histFromABL_wM`)

`PairInitConclW` (unconditional under master constants, `thm_case2_pairLIZWW`) bounds the `ab`
component of the reduced activity at coalescence:
`A^{(|𝓑(Y)|-4)_+}‖K'_{j_x}(Y)_{ab}‖ ≤ M_aM_b(2ι_WA)^{(L+18)²}`. On `abSub` the `wM(M_a,M_b)` norm is
`(M_aM_b)^{-1}‖·_{ab}‖` (`Obs2.oTo_of_ab`), so this is exactly the `hK0` input of
`PtCorr2.obs_histFromABL_wM` with `k₀ = (2ι_WA)^{(L+18)²}` and the weights `M_{a,j_x}`,
`M_{b,j_x}` of the two magnetisations at `j_x`:

* **`hK0_of_ab_le`** (general): an `ab` bound `M_aM_bk₀` on an `ObsAbInv` state is the `wM` bound `k₀`;
* **`pairSeed_hK0`**: the `hK0` input from `PairInitConclW`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **An `ab` bound is a `wM` bound** on states without one-point parts. -/
theorem hK0_of_ab_le {c : Obs.Case} {o : ObsSt c L N} {j : ℕ} (hab : ObsAbInv j o)
    {Ma Mb k₀ A ℓ : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    (h : ∀ Y, IsConn j Y → ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
      Tj 2 (L : ℝ) j ℓ (o.K Y : SA c (Lam 2 L N)).ab ≤ ENNReal.ofReal (Ma * Mb * k₀)) :
    ∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
      oTo (wM Ma Mb) j ℓ (o.K X) ≤ ENNReal.ofReal k₀ := by
  intro X hX
  rw [oTo_of_ab _ _ _ (hab.K X hX)]
  have hw : (wM Ma Mb).ab = ENNReal.ofReal (Ma * Mb)⁻¹ := by
    show ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal Mb⁻¹ = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), mul_inv]
  rw [hw, mul_left_comm]
  calc ENNReal.ofReal (Ma * Mb)⁻¹ * (ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ (o.K X : SA c (Lam 2 L N)).ab)
      ≤ ENNReal.ofReal (Ma * Mb)⁻¹ * ENNReal.ofReal (Ma * Mb * k₀) := mul_le_mul_right (h X hX) _
    _ = ENNReal.ofReal k₀ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 (mul_pos hMa hMb).le)]
        congr 1
        field_simp

/-- **The seed of `obs_histFromABL_wM` from `PairInitConclW`**: at `j_x`, in the weights
`wM(M_{a,j_x}, M_{b,j_x})` (`M_{a/b,j_x} = pM(ptsX/ptsS)`), `k₀ = (2ιA)^{(L+18)²}`. -/
theorem pairSeed_hK0 {ℓ A ρ κ cm cT ε ι : ℝ} (hP : PairInitConclW L ℓ A ρ κ cm cT ε ι)
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hRP : R.P = Pc) (hi : R.i₀ = 0)
    (hℓ : R.ℓ = ℓ) (hA : R.A = A) (hρ : R.ρ = ρ) (hN : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N)
    {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (had : Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀)
    (x : Lam 2 L N) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    0 < pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
        (Obs.coal L (0 : Lam 2 L N) x) ∧
      0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
        (Obs.coal L (0 : Lam 2 L N) x) ∧
      ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
        ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
          oTo (wM (pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x))
            (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x)))
            (Obs.coal L (0 : Lam 2 L N) x)
            (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X) ≤
          ENNReal.ofReal ((2 * ι * A) ^ ((L + 18) ^ 2)) := by
  obtain ⟨hpa, hpb, hK⟩ := hP N R hRP hi hℓ hA hρ hN Nh hNh m hm b μ₀ had x h1 hj
  refine ⟨hpa, hpb, ?_⟩
  have hab : ObsAbInv (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ (dxStd (L := L) (N := N)) x) :=
    obsAbInv_redSt _ _ _ _ _ _ _ _ _ _
  have hAm : (R.withMsq m).A = A := hA
  have e : ∀ n : ℕ, ENNReal.ofReal ((R.withMsq m).A ^ n) = ENNReal.ofReal (A ^ n) := fun n => by
    rw [hAm]
  exact hK0_of_ab_le hab hpa hpb fun Y _ => by rw [e]; exact hK Y

end

end Spin2
