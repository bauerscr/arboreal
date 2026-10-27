import Step2.D2.D2HV9

/-!
# The undressed inputs of (HV), uniformly in `j ≥ 0`

* `bubble_value`: `‖-(2𝔅x(C_{≤j}, C_{j+1}) + 𝔅x(C_{j+1}, C_{j+1})) - (1/2π) log L‖ ≤ 2 CB0 + log 2/(2π)`;
* `line1_value`: `|C_{j+1}(e₀, 0) - (1/2π) log L| ≤ ELine`, `ELine` independent of `L`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD

theorem CB0_nonneg : 0 ≤ CB0 := by
  have hpi := Real.pi_pos
  have h1 : 0 ≤ CE aB bB := by
    have := aB_nonneg; have := bB_nonneg; unfold CE; positivity
  have h2 := CM_nonneg
  have h3 := Ia_nonneg 5
  have h4 := Ia_nonneg 4
  have h5 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  unfold CB0; positivity

variable {L N : ℕ} [NeZero L]

/-- **The undressed bubble value**, uniformly in `j ≥ 0`. -/
theorem bubble_value (hL : 7 ≤ L) {j : ℕ} (hjN : j + 1 < N) {msq : ℝ} (hm : 0 < msq)
    (hmN : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) :
    ‖-(2 * bubX (cKer (L ^ (j + 1)) (Cle (frdC Pc (d := 2) (n := L ^ N) msq L N) j))
        (cKer (L ^ (j + 1)) (ofR (frdC Pc (d := 2) (n := L ^ N) msq L N (j + 1)))) +
      bubX (cKer (L ^ (j + 1)) (ofR (frdC Pc (d := 2) (n := L ^ N) msq L N (j + 1))))
        (cKer (L ^ (j + 1)) (ofR (frdC Pc (d := 2) (n := L ^ N) msq L N (j + 1))))) -
      ((Real.log L / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ 2 * CB0 + Real.log 2 / (2 * Real.pi) := by
  have hpi := Real.pi_pos
  have hL1 : 1 ≤ L := by omega
  have hLr : (7 : ℝ) ≤ L := by exact_mod_cast hL
  have hn : 2 * (L ^ (j + 1) + 4) < L ^ N := by
    have h1 : L ^ (j + 1) * L ≤ L ^ N := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hjN
    have h2 : L ≤ L ^ (j + 1) := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : L ^ (j + 1) * 7 ≤ L ^ (j + 1) * L := Nat.mul_le_mul_left _ hL
    omega
  rw [undressed_bubble hm hL1 hjN hn, neg_add, neg_neg]
  have hCB := CB0_nonneg
  have hl2 : 0 ≤ Real.log 2 / (2 * Real.pi) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
  split_ifs with hj
  · have h := bub_line3 hL hj hjN hm hmN
    calc _ = ‖frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) - frakBT L N msq ((L : ℝ) ^ j / 2) -
          ((Real.log L / (2 * Real.pi) : ℝ) : ℂ)‖ := by congr 1
      _ ≤ 2 * CB0 := h
      _ ≤ _ := by linarith
  · have hj0 : j = 0 := by omega
    subst hj0
    have hT : (1 : ℝ) ≤ (L : ℝ) ^ (0 + 1) / 2 := by simp; linarith
    have hmT : msq * ((L : ℝ) ^ (0 + 1) / 2) ^ 2 ≤ 1 := msq_mul_sq_le hL1 hjN hm.le hmN
    have hfl : 2 * (⌊(L : ℝ) ^ (0 + 1) / 2⌋₊ + 4) < L ^ N := by
      have h1 : (⌊(L : ℝ) ^ (0 + 1) / 2⌋₊ : ℝ) ≤ (L : ℝ) ^ (0 + 1) / 2 := Nat.floor_le (by positivity)
      have h2 : (L : ℝ) ^ (0 + 1) * L ≤ (L : ℝ) ^ N := by
        rw [← pow_succ]; exact pow_le_pow_right₀ (by linarith) (by omega)
      have h4 : ((2 * (⌊(L : ℝ) ^ (0 + 1) / 2⌋₊ + 4) : ℕ) : ℝ) < ((L ^ N : ℕ) : ℝ) := by
        push_cast; simp at h1 h2 ⊢; nlinarith
      exact_mod_cast h4
    have h := frakBT_bound (L := L) (N := N) hm hT hmT hfl
    have hlog : Real.log ((L : ℝ) ^ (0 + 1) / 2) = Real.log L - Real.log 2 := by
      rw [pow_one, Real.log_div (by positivity) (by norm_num)]
    rw [hlog] at h
    calc _ = ‖(frakBT L N msq ((L : ℝ) ^ (0 + 1) / 2) -
          (((Real.log L - Real.log 2) / (2 * Real.pi) : ℝ) : ℂ)) -
          (((Real.log 2 / (2 * Real.pi)) : ℝ) : ℂ)‖ := by
          congr 1; push_cast; ring
      _ ≤ CB0 + ‖(((Real.log 2 / (2 * Real.pi)) : ℝ) : ℂ)‖ := (norm_sub_le _ _).trans
          (add_le_add h le_rfl)
      _ ≤ _ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hl2]; linarith

end

end Step2
