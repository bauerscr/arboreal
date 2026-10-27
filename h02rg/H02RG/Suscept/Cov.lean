import Suscept.Moments

/-!
# The covariance `C = (-Δ + m²)^{-1}` on `Λ_N` (`e:S4C`)

* `Cov d L N msq = (-Δ + m²)^{-1}`.
* `Cov_eq`: `C = C_1 + ⋯ + C_{N-1} + C_N + t_N Q_N`, written with the covariances of the flow
  (`Flow.covAt`), for `m² > 0`, `N ≥ 1`.
* `Cov_row_sum`, `Cov_col_sum`: `∑_y C_{xy} = ∑_y C_{yx} = m^{-2}` (`-Δ` annihilates constants).
* `Cov_transl`: translation invariance.
* `tQ_eq_cst`: `t_N Q_N` is the constant covariance `t_N / |Λ|`.
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow

variable {d L : ℕ} [NeZero L]

variable (d L) in
/-- `C = (-Δ + m²)^{-1}` on `Λ_N`. -/
def Cov (N : ℕ) (msq : ℝ) : Matrix (Lam d L N) (Lam d L N) ℝ := (negLap + msq • 1)⁻¹

variable (d L) in
/-- `t_N`. -/
abbrev tNN (N : ℕ) (msq : ℝ) : ℝ := FRD.tN stdPt d msq (L : ℝ) N

/-- `|Λ_N|` as a real number. -/
theorem card_lam (N : ℕ) : (Fintype.card (Lam d L N) : ℝ) = ((L ^ N : ℕ) : ℝ) ^ d := by
  rw [show Fintype.card (Lam d L N) = (L ^ N) ^ d from card_torus]; push_cast; ring

theorem card_lam_pos (N : ℕ) : (0 : ℝ) < Fintype.card (Lam d L N) := by
  exact_mod_cast Fintype.card_pos

theorem tQ_eq_cst (N : ℕ) (t : ℝ) :
    (t • QN : Matrix (Lam d L N) (Lam d L N) ℝ) =
      cst (Lam d L N) (t / Fintype.card (Lam d L N)) := by
  ext x y
  simp [QN, cst, card_lam, div_eq_mul_inv]

theorem sum_Cfrd_eq (M : ℕ) (msq : ℝ) :
    ∑ j ∈ Finset.Ico 1 (M + 1), (Cj stdPt msq (L : ℝ) j : Matrix (Lam d L (M + 1)) _ ℝ) =
      ∑ j ∈ range M, covAt d L (M + 1) msq j := by
  rw [Finset.sum_Ico_eq_sum_range, show M + 1 - 1 = M by omega]
  refine sum_congr rfl fun j hj => ?_
  rw [covAt_lt (by simp at hj; omega)]
  simp [Cfrd, add_comm]

/-- **`e:S4C`**: `(-Δ + m²)^{-1} = C_1 + ⋯ + C_{N-1} + C_N + t_N Q_N`. -/
theorem Cov_eq {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) :
    Cov d L N msq = ∑ j ∈ range N, covAt d L N msq j + tNN d L N msq • QN := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  rw [Cov, decomposition_inv stdPt hmsq hL hN, CNN_eq, sum_Cfrd_eq, sum_range_succ,
    covAt_last, add_assoc]

theorem negLap_row_sum (N : ℕ) (x : Lam d L N) :
    ∑ y, (negLap : Matrix (Lam d L N) (Lam d L N) ℝ) x y = 0 := by
  simp only [negLap, sum_sub_distrib, ← mul_sum]
  rw [Finset.sum_comm]
  simp [Fintype.card_sum]; ring

theorem negLap_col_sum (N : ℕ) (y : Lam d L N) :
    ∑ x, (negLap : Matrix (Lam d L N) (Lam d L N) ℝ) x y = 0 := by
  simp only [negLap, sum_sub_distrib, ← mul_sum]
  rw [Finset.sum_comm]
  have : ∀ e : Dir d, (∑ x : Lam d L N, if y = x + dirVec e then (1 : ℝ) else 0) = 1 := by
    intro e
    rw [Finset.sum_eq_single (y - dirVec e)]
    · simp
    · intro x _ hx
      rw [if_neg]; intro h; exact hx (by rw [h]; abel)
    · simp
  simp [this, Fintype.card_sum]; ring

theorem mul_Cov {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) :
    (negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) * Cov d L N msq = 1 := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  rw [Cov, decomposition_inv stdPt hmsq hL hN]
  exact decomposition stdPt hmsq hL hN

theorem Cov_mul {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) :
    Cov d L N msq * (negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) = 1 :=
  mul_eq_one_comm.1 (mul_Cov hmsq hN)

theorem A_row_sum (msq : ℝ) (N : ℕ) (x : Lam d L N) :
    ∑ y, (negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) x y = msq := by
  simp [Matrix.add_apply, sum_add_distrib, negLap_row_sum, Matrix.one_apply]

theorem A_col_sum (msq : ℝ) (N : ℕ) (y : Lam d L N) :
    ∑ x, (negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) x y = msq := by
  simp [Matrix.add_apply, sum_add_distrib, negLap_col_sum, Matrix.one_apply]

/-- `∑_y C_{xy} = m^{-2}`. -/
theorem Cov_row_sum {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) (x : Lam d L N) :
    ∑ y, Cov d L N msq x y = msq⁻¹ := by
  have h := congrArg (fun M : Matrix (Lam d L N) (Lam d L N) ℝ => ∑ z, M x z) (Cov_mul hmsq hN)
  simp only [Matrix.mul_apply, Matrix.one_apply, sum_ite_eq, mem_univ, if_true] at h
  rw [Finset.sum_comm] at h
  simp only [← mul_sum, A_row_sum, ← sum_mul] at h
  field_simp
  linarith

/-- `∑_x C_{xy} = m^{-2}`. -/
theorem Cov_col_sum {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) (y : Lam d L N) :
    ∑ x, Cov d L N msq x y = msq⁻¹ := by
  have h := congrArg (fun M : Matrix (Lam d L N) (Lam d L N) ℝ => ∑ z, M z y) (mul_Cov hmsq hN)
  simp only [Matrix.mul_apply, Matrix.one_apply, sum_ite_eq', mem_univ, if_true] at h
  rw [Finset.sum_comm] at h
  simp only [← sum_mul, A_col_sum, ← mul_sum] at h
  field_simp
  linarith

/-- Translation invariance of `C`. -/
theorem Cov_transl {msq : ℝ} (hmsq : 0 < msq) {N : ℕ} (hN : 1 ≤ N) (x y a : Lam d L N) :
    Cov d L N msq (x + a) (y + a) = Cov d L N msq x y := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  rw [Cov, decomposition_inv stdPt hmsq hL hN]
  simp only [Matrix.add_apply, Matrix.sum_apply, Cj_translate]
  congr 1
  exact fmat_translate _ x y a

end

end Suscept
