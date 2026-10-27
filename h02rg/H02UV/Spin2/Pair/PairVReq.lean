import Obs2.Flow.GradAB2
import Obs2.Flow.VObsAB4
import Obs2.Est.WObs2
import Obs2.Est.EstBlock
import Step.Polymers
import Loc.EstCutoff

/-!
# The constants of the `V`-step of the joint induction

The gradient part of the `V`-step (`PtCorr2.gradV_hist_le`) involves three absolute constants
(fixed here by choice) and two `L`-dependent combinations:

* `cSm2` — the number of small sets containing a block (`Step.card_small_containing 2`);
* `cNb2` — the number of blocks `B` with `x ∈ B^□` (`Obs2.card_blocks_near 2`);
* `Ccut2` — the cutoff derivative constant (`Loc.exists_D1_cutP_bound 2 (pPhi 2) 1`);
* **`vA1 L C₁w`** `= (2K_G + 3(9/8)² + 2K_{M4})·2c_Nc_S·c_W` (the `K'` part, `c_W = 4C₁w + 1`) and
  **`vA2 L C₁w`** `= (2K_G + 3 + 2K_{M4})·2L²·L²(2c_{near}Q₁² + Q₁c_W)` (the `S(B_+)` part);
* **`vck L C₁w`** `= 1/(16(vA1 + 1))`: the relative size of `K'` (in units of `c_W m̄`) for which the
  `K'` part of the gradient is `≤ m̄/8`.
-/

namespace Spin2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 FRD Obs2

/-- The number of small sets containing a block (`d = 2`). -/
def cSm2 : ℕ := Classical.choose (card_small_containing 2)

theorem cSm2_spec : ∀ (L : ℕ) [NeZero L] (N j : ℕ) (b : Fin 2 → ℕ),
    b ∈ blockIdx (L := L) (N := N) j →
      ((smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).card ≤ cSm2 :=
  Classical.choose_spec (card_small_containing 2)

/-- The number of blocks `B` with `x ∈ B^□` (`d = 2`). -/
def cNb2 : ℕ := Classical.choose (card_blocks_near 2)

theorem cNb2_spec : ∀ (L : ℕ) [NeZero L] (N j : ℕ) (a : Lam 2 L N)
    (s : Finset (Fin 2 → ℕ)), s ⊆ blockIdx (L := L) (N := N) j →
      (s.filter (fun b => a ∈ nbhd j (blockSet (L := L) (N := N) j b))).card ≤ cNb2 :=
  Classical.choose_spec (card_blocks_near 2)

/-- The cutoff derivative constant (`d = 2`, `|α| ≤ p_Φ`, `m_i ≤ 1`). -/
def Ccut2 : ℝ := Classical.choose (exists_D1_cutP_bound 2 (pPhi 2) 1)

theorem Ccut2_spec : 0 ≤ Ccut2 ∧ ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → ∀ a : Dir 2 → ℕ, Grassmann.mabs a ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) a (cutP m R) u| ≤ Ccut2 * R ^ (∑ i, m i) / R ^ Grassmann.mabs a :=
  Classical.choose_spec (exists_D1_cutP_bound 2 (pPhi 2) 1)

/-- The `K'` part of the `V`-step gradient constant. -/
def vA1 (C₁w : ℝ) : ℝ :=
  (2 * KG 2 Ccut2 4 + 3 * (9 / 8 : ℝ) ^ 2 + 2 * KM4 2 Ccut2) * (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) *
    (4 * C₁w + 1)

/-- The `S(B_+)` part of the `V`-step gradient constant. -/
def vA2 (L : ℕ) (C₁w : ℝ) : ℝ :=
  (2 * KG 2 Ccut2 4 + 3 + 2 * KM4 2 Ccut2) * (2 * (L : ℝ) ^ 2) *
    ((L : ℝ) ^ 2 * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 + Step2.Q1 2 * (4 * C₁w + 1)))

/-- The admissible relative `K'` size of the `V`-step. -/
def vck (C₁w : ℝ) : ℝ := 1 / (16 * (vA1 C₁w + 1))

theorem vA1_nonneg {C₁w : ℝ} (h : 0 ≤ C₁w) : 0 ≤ vA1 C₁w := by
  unfold vA1
  have := KG_nonneg 2 (Cc := Ccut2) (by norm_num : (0 : ℝ) ≤ 4)
  have := KM4_nonneg 2 (Cc := Ccut2)
  positivity

theorem vck_pos {C₁w : ℝ} (h : 0 ≤ C₁w) : 0 < vck C₁w := by
  unfold vck; have := vA1_nonneg h; positivity

theorem vck_le_one {C₁w : ℝ} (h : 0 ≤ C₁w) : vck C₁w ≤ 1 := by
  unfold vck
  have := vA1_nonneg h
  rw [div_le_one (by positivity)]; linarith

theorem four_vA1_vck {C₁w : ℝ} (h : 0 ≤ C₁w) : 4 * (vA1 C₁w * vck C₁w) ≤ 1 / 4 := by
  unfold vck
  have := vA1_nonneg h
  rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

end

end Spin2
