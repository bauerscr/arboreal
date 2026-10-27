import Step2.Lip.FlowLipHist2

/-!
# The covariances along two histories (Lipschitz bounds, part 15)

The normalised covariance of step `k` is the dressed covariance `C'_{k+1}(ζ) = Cdr` of the
absorbed couplings `ζ_0, …, ζ_k` (`CvH_eq_Cdr`), so by `prop_C5_lip` the difference along two
histories is a good covariance at the field scale
`ℓ_Δ² = K L^{2p_Φ} ∑_{i≤k} ρ^{k-i} |ζ_i - ζ'_i|` (`CvH_sub_good`): **geometric decay in the
past**.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Cov

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem rawHist_zeta : ∀ (j : ℕ) (t : Hist.Seq (Xs R)) (i : ℕ), i < j →
    (rawHist R j t).ζ i = zetaH R i t
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, t, i, hi => by
    have e : (rawHist R (j + 1) t).ζ = Function.update (rawHist R j t).ζ j (zetaH R j t) := rfl
    rw [e]
    by_cases hij : i = j
    · subst hij; rw [Function.update_self]
    · rw [Function.update_of_ne hij]
      exact rawHist_zeta j t i (by omega)

/-- The dressed data of the history at step `k`. -/
def dataH (k : ℕ) (t : Hist.Seq (Xs R)) : DressedFRD.Data 2 (L ^ N) :=
  ⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, (rawHist R (k + 1) t).ζ⟩

variable {R}

theorem CvH_eq_Cdr {k : ℕ} (hV : ∀ i ≤ k, ValidAt R i) (t : Hist.Seq (Xs R)) :
    CvH R k t = Cdr (dataH R k t) k := by
  have hρ0 := (hV 0 (Nat.zero_le _)).2.2.2.1
  have HI := rawInv_hist R hρ0 (k + 1) (fun i hi => hV i (by omega)) t
  rw [CovH_eq, Cdr, kmat_smul]
  congr 1
  rw [HI.hZprod]
  rfl

theorem ellLip_two (Ln : ℕ) (B : ℝ) (k : ℕ) :
    ellLip 2 Ln B k = Real.sqrt B * (Ln : ℝ) ^ pPhi 2 := by
  unfold ellLip
  norm_num

theorem ellLip_two_sq (Ln : ℕ) {B : ℝ} (hB : 0 ≤ B) (k : ℕ) :
    ellLip 2 Ln B k ^ 2 = B * (Ln : ℝ) ^ (2 * pPhi 2) := by
  rw [ellLip_two, mul_pow, Real.sq_sqrt hB, ← pow_mul, mul_comm (pPhi 2) 2]

theorem ellLip_two_nonneg (Ln : ℕ) (B : ℝ) (k : ℕ) : 0 ≤ ellLip 2 Ln B k := by
  rw [ellLip_two]; positivity

/-- **The difference of the normalised covariances of two histories.** -/
theorem CvH_sub_good (P : PtFamily) (hL7 : 7 ≤ L) {ρc : ℝ} (hρc : 0 < ρc) (hρc1 : ρc ≤ 1 / 2) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = P →
      R.ρ ≤ ζbar / 2 → 0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      ∀ (k : ℕ), (∀ i ≤ k, ValidAt R i) → ∀ t t' : Hist.Seq (Xs R),
      GoodCov2 k (ellLip 2 L (Kc * ∑ i ∈ range (k + 1),
          ρc ^ (k - i) * ‖zetaH R i t' - zetaH R i t‖) k) (CvH R k t' - CvH R k t) := by
  obtain ⟨ζbar, hζ, hζ8, Kc, hKc, h⟩ := prop_C5_lip P (d := 2) le_rfl hL7 hρc hρc1
  refine ⟨ζbar, hζ, hζ8, Kc, hKc, fun N R _ _ hP hρ hm0 hm1 k hV t t' => ?_⟩
  have hk : k + 2 < N := (hV k le_rfl).1
  have hρ0 := (hV 0 (Nat.zero_le _)).2.2.2.1
  have HI := rawInv_hist R hρ0 (k + 1) (fun i hi => hV i (by omega)) t
  have HI' := rawInv_hist R hρ0 (k + 1) (fun i hi => hV i (by omega)) t'
  have h1 := h N R.msq (rawHist R (k + 1) t').ζ (rawHist R (k + 1) t).ζ (by omega) hm0 hm1
    (fun i => (HI'.hζ i).trans hρ) (fun i => (HI.hζ i).trans hρ) k (by omega)
  simp only at h1
  rw [CvH_eq_Cdr hV, CvH_eq_Cdr hV]
  have es : ∑ i ∈ range (k + 1), ρc ^ (k - i) *
      ‖(rawHist R (k + 1) t').ζ i - (rawHist R (k + 1) t).ζ i‖ =
      ∑ i ∈ range (k + 1), ρc ^ (k - i) * ‖zetaH R i t' - zetaH R i t‖ := by
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [rawHist_zeta R (k + 1) t' i hi', rawHist_zeta R (k + 1) t i hi']
  rw [es] at h1
  subst hP
  exact h1

end Cov

end

end Step2
