import Spin2.Final.FinalWire
import Spin2.H0.MasterH0Slack

/-!
# Final assembly of Expected result `thm:multiscale` at `h = 0` (route (a1))

* **`MasterFacts.fw_multiscale_traj`**: on the `h = 0` trajectory `(b, b − m²)` in `D_ε`, from the
  pair layer `fw_pairAbove_MFD'` (conclusion `FwPairConclD`): (H_λ) for `λ̂ = lamHat2 R P (zV b)`
  (`hLam_pairD`, `K_λ = K_p`), `TwoPtSq` (`twoPtSqD`) and `|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ Kϑ_j²/β_j`
  (`MasterCore.multiscale_h0`). Discharged here: `‖M_k‖ ≤ M_b` (`M_b := ∑_{k≤N_h}‖M_k‖`; the
  final constant does not depend on `M_b`), the smallness `max(K(K_p),0)ǧ_j ≤ 1/2` (monotonicity of
  `ǧ_j`, `gmonoD`) and the eight last-step smallness conditions: all follow from
  `ǧ_{N_h} ≤ fwG` and `m²L^{2N} ≤ fwG`, `fwG = fwG M K_t r₀ > 0` explicit.
* **`thm_multiscale_h0_final`**: for all large `L`, one master construction `M`, constants `p_W`,
  `g₀ > 0`, `C₁v`; under the window condition on the constants `(3/4)c_μ(1 + 2p_Wc_μ) < c_μ`,
  for every `N ≥ 2`, `m² ∈ mRange`, every admissible `(b, μ^c)` with `m²L^{2N} ≤ ǧ^c_{N_h} ≤ g₀`:
  the upper window end `μ₊` exists, and if `r = 1 − b⟨ψ̄_0ψ_0⟩_{μ₊} ≥ 0` (RG input), then for every
  point configuration `P` with `PairDefSizesR3P c_d`, `PairZeroRemAB e₁ e₂` on the `h = 0`
  trajectory, `|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ fwK·ϑ_j²/β_j` for `x ≠ 0`, `j_x ≤ N_h`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- `a·x ≤ c` from `0 ≤ x ≤ c/(|a| + 1)`. -/
theorem fw_le {a x c : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ c / (|a| + 1)) : a * x ≤ c := by
  have h0 : 0 < |a| + 1 := by positivity
  have h1 : a * x ≤ |a| * x := mul_le_mul_of_nonneg_right (le_abs_self a) hx0
  have h2 : (|a| + 1) * x ≤ c := by rw [le_div_iff₀ h0] at hx; linarith
  have e : (|a| + 1) * x = |a| * x + x := by ring
  linarith

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The final pair constant `K_E` (first constant of `PairAboveW1` in `FwPairConclD`). -/
def fwKE (C₁v cd e1 e2 : ℝ) : ℝ :=
  (pl6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb) *
      (2 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 * max (1 + 3 * M.Kp) (2 * (1 + 3 * M.Kp))) *
        (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) +
    cd + (4 * e2 + 2 * ((pl6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb) + e1) +
      2 * ((pl6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb) + e1)) * M.fwKG

/-- **The smallness threshold** for `ǧ_{N_h}` and `m²L^{2N}` (the eight last-step conditions of the
pair layer and `max(K(K_p),0)ǧ_j ≤ 1/2`). -/
def fwG (Kt r₀ : ℝ) : ℝ :=
  min (min (min (1 / 2 / (|M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
          9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
          cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3| + 1))
        (1 / 2 / (|Kt| + 1)))
      (min (1 / (|8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3| + 1))
        (M.core.ρ / (|2 * M.core.Cf| + 1))))
    (min (min (1 / 2 / (|8 * cM * M.core.ℓ ^ 2 * M.core.Cf| + 1))
        (1 / (|PtCorr2.cRho L * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL| + 1)))
      (min (min (r₀ ^ 2 / (|4 * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL| + 1))
          (r₀ / (|cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL| + 1)))
        (1 / 2 / (|max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0| + 1))))

theorem fwG_pos {Kt r₀ : ℝ} (hr₀ : 0 < r₀) : 0 < M.fwG Kt r₀ := by
  obtain ⟨-, -, hρ, -⟩ := M.core.hC2
  unfold fwG
  refine lt_min (lt_min (lt_min ?_ ?_) (lt_min ?_ ?_)) (lt_min (lt_min ?_ ?_) (lt_min (lt_min ?_ ?_) ?_)) <;>
    positivity

end MasterFacts

end

end Spin2
