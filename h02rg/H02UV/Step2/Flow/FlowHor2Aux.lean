import Step2.Lip.FlowZetaMain
import Step2.Lip.FlowZetaApriori
import Step2.Flow.FlowBase
import Step2.Flow.FlowSharp1
import Flow2.Hor2Unique

/-!
# The flow up to `N_h = N - 2` without a mass condition: the reduction

* `HS_zeta`: the (F1) mass input `‖Z ζ_j m² w⁽¹⁾‖ ≤ (8/7) c_ζ (M₀ + 1) m_f ǧ_j` from the sharp
  bound `|ζ_j| ≤ c_ζ ǧ_j` (`zeta_hist`).
* `hist_weight`: unweighted past distances satisfy the fading-memory condition.
* `sZ_le`: the size of the hidden differences along the uniqueness cone is `O(ε)`.
* `flow_of_lipz`: `prop:C6` for `rgData` from (F1), (F2), (Kb), (Yb) and the Lipschitz bounds of
  `lip_rg_z` (with the separate `ζ`-channel): existence and the band from `HHyp` with large
  constants, uniqueness from `Flow2.Hist.admissible_unique_z`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

/-- **The (F1) mass input from the sharp `ζ`-bound.** -/
theorem HS_zeta (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ}
    (hV : ∀ i ≤ j, ValidAt R i) (t : Hist.Seq (Xs R)) {cζ mf M₀ g : ℝ} (hg : 0 ≤ g)
    (hcζ : 0 ≤ cζ) (hM₀ : 0 ≤ M₀) (hζ : ‖stZeta R (rawHist R j t)‖ ≤ cζ * g)
    (hmf : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ mf)
    (hS0 : ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ (M₀ + 1) * ((L : ℝ) ^ j) ^ 2) :
    ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤
      8 / 7 * cζ * (M₀ + 1) * mf * g := by
  have hρ := (hV j le_rfl).2.2.2.1
  have hρ8 := (hV j le_rfl).2.2.2.2.1
  have hρ1 : R.ρ < 1 := by linarith
  have HI := rawInv_hist R hρ j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ st).trans hρ8
  have h1ζ : 7 / 8 ≤ ‖1 + stZeta R st‖ := by linarith [norm_one_add_ge (ζ := stZeta R st)]
  have e : stA R st * (R.msq : ℂ) * st.w1 =
      stZeta R st / (1 + stZeta R st) * (R.msq : ℂ) * (stZ' R st * st.w1) := by
    have h1 : (1 + stZeta R st) ≠ 0 := one_add_ne_zero (by linarith)
    show st.Z * stZeta R st * (R.msq : ℂ) * st.w1 = _
    unfold stZ'; field_simp
  rw [e, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hz1 : ‖stZeta R st‖ / ‖1 + stZeta R st‖ ≤ 8 / 7 * (cζ * g) := by
    rw [div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ cζ * g := by positivity
    nlinarith
  have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  calc ‖stZeta R st‖ / ‖1 + stZeta R st‖ * |R.msq| * ‖stZ' R st * st.w1‖
      ≤ 8 / 7 * (cζ * g) * |R.msq| * ((M₀ + 1) * ((L : ℝ) ^ j) ^ 2) := by gcongr
    _ = 8 / 7 * cζ * (M₀ + 1) * g * (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by ring
    _ ≤ 8 / 7 * cζ * (M₀ + 1) * g * mf := by gcongr
    _ = _ := by ring

theorem hist_weight {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {j : ℕ} {t t' : Hist.Seq X}
    {M : ℝ} (h : ∀ i < j, dist3 (t i) (t' i) ≤ M) :
    ∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M := fun i hi => by
  have h1 : (3 / 4 : ℝ) ^ (j - 1 - i) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : 0 ≤ dist3 (t i) (t' i) := by unfold dist3; positivity
  nlinarith [h i hi]

theorem sZ_le {C Kh Qh ε : ℝ} (hC : 0 ≤ C) (hKh : 0 ≤ Kh) (hQh : 0 ≤ Qh) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    sZ C (C * ε) (Kh * (C * ε)) (Qh * (C * ε)) ≤ ε * (C * (2 * C * (Kh + Qh) + 2)) := by
  unfold sZ
  have h1 : C * ε * (Kh * (C * ε) + Qh * (C * ε)) ≤ C * ε * (Kh * C + Qh * C) := by
    have hCe : C * ε ≤ C := mul_le_of_le_one_right hC hε1
    have : Kh * (C * ε) + Qh * (C * ε) ≤ Kh * C + Qh * C := by
      have a := mul_le_mul_of_nonneg_left hCe hKh
      have b := mul_le_mul_of_nonneg_left hCe hQh
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have e1 : C * (Kh * (C * ε) + Qh * (C * ε)) + C * ε * (2 + Kh * (C * ε) + Qh * (C * ε)) =
      ε * (C * C * (Kh + Qh) + 2 * C) + C * ε * (Kh * (C * ε) + Qh * (C * ε)) := by ring
  have e2 : C * ε * (Kh * C + Qh * C) = ε * (C * C * (Kh + Qh)) := by ring
  rw [e1]
  have e3 : ε * (C * (2 * C * (Kh + Qh) + 2)) = ε * (C * C * (Kh + Qh) + 2 * C) +
      ε * (C * C * (Kh + Qh)) := by ring
  linarith

end

end Step2
