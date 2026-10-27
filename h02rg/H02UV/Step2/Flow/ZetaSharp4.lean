import Step2.Flow.ZetaSharp2
import Step2.Flow.ZetaSharp3
import Step2.Flow.FlowHV
import Step2.D2.D2Dress

/-!
# History-level inputs for the asymptotics of `Z_j`

* `X_eq_kern`: `Z_{k+1} C_k(e₁, 0) = C'_{k+1}(e₁, 0)` for the dressed data of the history;
* `X_value_hist`: `|Z_{k+1} C_k(e₁, 0) - log L/2π| ≤ (2π)^{-2}(E_{C1} L^{-2k} + E_B m²(L^{2k} +
  L^{2(k+1)})) + K M_z(k+1)` for `1 ≤ k`, `k + 1 < N` (`prop:d2`, first line, `Cprime_values`);
* `logZ_succ`: `log|Z_{k+2}| - log|Z_{k+1}| = log|1 + ζ_{k+1}|`;
* `zA`: the summable error sequence `a_0 = 1`, `a_k = L^{-2k} + m² L^{2(k+1)}`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Step2.D2

/-- The error sequence of the sharp flow: `a_0 = 1`, `a_k = L^{-2k} + m² L^{2(k+1)}` (`k ≥ 1`). -/
def zA (L : ℕ) (msq : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else (((L : ℝ) ^ k) ^ 2)⁻¹ + msq * ((L : ℝ) ^ (k + 1)) ^ 2

theorem zA_nonneg (L : ℕ) {msq : ℝ} (hm : 0 ≤ msq) (k : ℕ) : 0 ≤ zA L msq k := by
  unfold zA; split_ifs <;> positivity

theorem zA_zero (L : ℕ) (msq : ℝ) : zA L msq 0 = 1 := if_pos rfl

theorem zA_pos (L : ℕ) (msq : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    zA L msq k = (((L : ℝ) ^ k) ^ 2)⁻¹ + msq * ((L : ℝ) ^ (k + 1)) ^ 2 := if_neg (by omega)


theorem ErrC1_nonneg : 0 ≤ ErrC1 := by
  rw [ErrC1]
  have := ErrA_nonneg; have := KH_nonneg; have := kap_pos; have := Ia_nonneg 3
  have := Real.pi_pos
  positivity

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `Z_{k+1} C_k(e₁, 0)` is the dressed `C'_{k+1}(e₁, 0)`. -/
theorem X_eq_kern (hP : R.P = Pc) {k : ℕ} (hV : ∀ i ≤ k, ValidAt R i) (t : Hist.Seq (Xs R)) :
    stZ' R (rawHist R k t) * stCov R k (rawHist R k t) (dirVec (Sum.inl 0)) 0 =
      DressedFRD.kern ((dData L N R.msq (zh R k t)).Z (k + 1) • (dData L N R.msq (zh R k t)).Gint k)
        (unitT 0) := by
  rw [stZ'_eq_dData R hV t, stCov_eq_dData R hP t le_rfl, DressedFRD.kern_smul]
  simp only [DressedFRD.kmat, sub_zero, dirVec_inl]

/-- **The value of `C'_{k+1}(e₁, 0)` along histories** (`prop:d2`, first line). -/
theorem X_value_hist : ∀ (L : ℕ) [NeZero L], 7 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ k, 1 ≤ k → k + 1 < N → (∀ i ≤ k, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) (dirVec (Sum.inl 0)) 0 -
            (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ k) ^ 2 +
            ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
          K * (dData L N R.msq (zh R k t)).Mz (k + 1) := by
  intro L _ hL
  obtain ⟨ζbar, hζ, K, hK⟩ := Cprime_values (q := 2) le_rfl hL
  refine ⟨ζbar, hζ, max K 0, le_max_right _ _, fun N R _ _ hP hN hm0 hm hρ k hk1 hkN hV t => ?_⟩
  have hz := (hist_dData_hyps R hP hV t).1
  rw [X_eq_kern R hP hV t]
  have h := (hK (L ^ N) N R.msq (zh R k t) hN rfl hm0 hm (fun i => (hz i).trans hρ) k hk1 hkN).2
  have hM := (dData L N R.msq (zh R k t)).Mz_nonneg (k + 1)
  have h2 : K * (dData L N R.msq (zh R k t)).Mz (k + 1) ≤
      max K 0 * (dData L N R.msq (zh R k t)).Mz (k + 1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  exact h.trans (by linarith only [h2])

/-- `log|Z_{k+2}| - log|Z_{k+1}| = log|1 + ζ_{k+1}|`. -/
theorem logZ_succ (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) {k : ℕ} (hV : ∀ i < k + 1, ValidAt R i)
    (t : Hist.Seq (Xs R)) :
    Real.log ‖(rawHist R (k + 1 + 1) t).Z‖ - Real.log ‖(rawHist R (k + 1) t).Z‖ =
      Real.log ‖1 + stZeta R (rawHist R (k + 1) t)‖ := by
  have HI := rawInv_hist R hρ0 (k + 1) hV t
  have hZ : (rawHist R (k + 1) t).Z ≠ 0 := HI.Z_ne_zero (by linarith only [hρ8])
  have hζ : ‖stZeta R (rawHist R (k + 1) t)‖ ≤ 1 / 8 := (norm_stZeta_le hρ0 _).trans hρ8
  have h1 : 1 + stZeta R (rawHist R (k + 1) t) ≠ 0 := by
    intro h
    have : stZeta R (rawHist R (k + 1) t) = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hζ; norm_num at hζ
  have e : (rawHist R (k + 1 + 1) t).Z =
      (rawHist R (k + 1) t).Z * (1 + stZeta R (rawHist R (k + 1) t)) := rfl
  rw [e, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hZ) (norm_ne_zero_iff.2 h1)]
  ring

/-- `Z_{n+1} ≠ 0` along histories valid below `n`. -/
theorem Z_succ_ne_zero (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) {n : ℕ} (hV : ∀ i < n, ValidAt R i)
    (t : Hist.Seq (Xs R)) : (rawHist R (n + 1) t).Z ≠ 0 := by
  have HI := rawInv_hist R hρ0 n hV t
  have hZ : (rawHist R n t).Z ≠ 0 := HI.Z_ne_zero (by linarith only [hρ8])
  have hζ : ‖stZeta R (rawHist R n t)‖ ≤ 1 / 8 := (norm_stZeta_le hρ0 _).trans hρ8
  have h1 : 1 + stZeta R (rawHist R n t) ≠ 0 := by
    intro h
    have : stZeta R (rawHist R n t) = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hζ; norm_num at hζ
  exact mul_ne_zero hZ h1

/-- `|Z_1| = 1`. -/
theorem rawHist_one_Z (t : Hist.Seq (Xs R)) : (rawHist R 1 t).Z = 1 := by
  show (rawHist R 0 t).Z * (1 + absorbZeta R (rawHist R 0 t).Z ((rawHist R 0 t).z +
    (rawHist R 0 t).y)) = 1
  have e : (rawHist R 0 t).z + (rawHist R 0 t).y = 0 := by simp [rawHist]
  have e2 : clampDisk R.ρ (0 : ℂ) = 0 := by unfold clampDisk; simp
  have e3 : (rawHist R 0 t).Z = 1 := rfl
  unfold absorbZeta
  rw [e, zero_div, e2, e3]; simp

end

end Step2
