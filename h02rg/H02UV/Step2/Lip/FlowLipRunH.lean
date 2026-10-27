import Step2.Lip.FlowLipT

/-!
# The comparison hypotheses along two histories (Lipschitz bounds, part 32)

`run_of`: two histories in the domain `D_ε` with the a priori bounds, validity, the mass condition
and the decay of the covariances satisfy `Run` with the radius `e = c_E ε`, under explicit
smallness conditions on `ε`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Run

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ β δ κ cg cm cT ε cz cw Kc : ℝ}

theorem nW1H_le (hV : ∀ i ≤ j, ValidAt R i) (t : Hist.Seq (Xs R)) {k : ℕ} (hk : k ≤ j) :
    ‖nW1H R k t‖ ≤ R.ℓ ^ 2 := by
  have hρ := (hV 0 (Nat.zero_le _)).2.2.2.1
  have h := norm_Zw1_le R hρ k (fun i hi => hV i (by omega)) t
  have hL : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have e : nW1H R k t = stZ' R (rawHist R k t) * (rawHist R k t).w1 / (L : ℂ) ^ (2 * k) := rfl
  have e2 : (L : ℝ) ^ (2 * k) = ((L : ℝ) ^ k) ^ 2 := by ring
  rw [e, norm_div, norm_pow, Complex.norm_natCast, e2, div_le_iff₀ hL]
  exact h

/-- The domain at step `k` from `InDh` and the a priori bounds. -/
theorem domH_of (hV : ∀ i ≤ j, ValidAt R i) (ht : Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hA : ∀ k ≤ j, APB R cz cw (t k).1 (rawHist R k t) k) (hcz : 0 ≤ cz)
    (hρ : 2 * cz * ε ≤ R.ρ) (h16 : 2 * cz * ε ≤ 1 / 16) {k : ℕ} (hk : k ≤ j) :
    DomH k t Λ κ cm cT ε cz cw :=
  ⟨fun i hi => hV i (by omega), ht.1 k hk, hA k hk, hcz, hρ, h16⟩

/-- **The comparison hypotheses hold along two histories in the domain.** -/
theorem run_of (hV : ∀ i ≤ j, ValidAt R i) (ht : Hist.InDh Λ β δ κ cg cm cT ε j t)
    (ht' : Hist.InDh Λ β δ κ cg cm cT ε j t')
    (hA : ∀ k ≤ j, APB R cz cw (t k).1 (rawHist R k t) k)
    (hA' : ∀ k ≤ j, APB R cz cw (t' k).1 (rawHist R k t') k)
    (hm : ∀ k ≤ j, |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hC : ∀ k ≤ j, GoodCov2 k (lD R Kc k t t') (CvH R k t' - CvH R k t))
    (hcz : 0 ≤ cz) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hKc : 0 ≤ Kc)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 2 * cz * ε ≤ R.ρ) (h16 : 2 * cz * ε ≤ 1 / 16)
    (hΔ : cDl (7 / 8 * R.ℓ) cz * ε ≤ 1 / 4)
    (hE1 : cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * ε ≤ 1)
    (hnd : 4 * cmu Λ cm * ε * R.ℓ ^ 2 ≤ 1 / 8) :
    Run R j t t' Λ κ cm cT ε cz cw (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * ε) Kc := by
  set cE := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) with hcE
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE1 : 1 ≤ cE := by rw [hcE]; unfold cEr; linarith
  have hcE2 : cw + 3 * cx κ cT ≤ cE := by rw [hcE]; unfold cEr; linarith
  have hcEV : cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) ≤ cE := by rw [hcE]; unfold cEr; linarith
  have hE3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hε2 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have hcEE : cE ≤ cE ^ 2 := by nlinarith
  have nd1 : ∀ (tt : Hist.Seq (Xs R)), Hist.InDh Λ β δ κ cg cm cT ε j tt → ∀ k ≤ j,
      ‖4 * ((tt k).2.1 : ℂ) * nW1H R k tt‖ ≤ 1 / 8 := fun tt htt k hk => by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(4 : ℂ)‖ = 4 by norm_num]
    obtain ⟨hg, hgε, hμ, -⟩ := htt.1 k hk
    have hμ' : |(tt k).2.1| ≤ cmu Λ cm * ε := hμ.trans (mul_le_mul_of_nonneg_left hgε hcmu)
    have := mul_le_mul hμ' (nW1H_le hV tt hk) (norm_nonneg _) (by positivity)
    nlinarith
  refine ⟨fun k hk => ?_, fun k hk => ⟨nW1H_le hV t hk, nW1H_le hV t' hk⟩,
    fun k hk => ⟨nd1 t ht k hk, nd1 t' ht' k hk⟩, hKc, hE1, hε0⟩
  refine ⟨domH_of hV ht hA hcz hρ h16 hk, domH_of hV ht' hA' hcz hρ h16 hk, hm k hk, hcw, hcx,
    hcmu, hε1, hΔ, by positivity, ?_, ?_, ?_, lD_nonneg _ _ _ _, hC k hk⟩
  · exact (mul_le_mul_of_nonneg_right hcEV hε0.le)
  · have h1 : cw * ε ^ 2 + cx κ cT * ε ^ 3 ≤ (cw + cx κ cT) * ε ^ 2 := by nlinarith
    have h2 : (cw + cx κ cT) * ε ^ 2 ≤ cE ^ 2 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    nlinarith
  · have h1 : Real.exp 1 * (cx κ cT * ε ^ 3) ≤ 3 * cx κ cT * ε ^ 2 := by
      have := mul_le_mul hE3 (mul_le_mul_of_nonneg_left hε2 hcx) (by positivity) (by norm_num)
      nlinarith
    have h2 : 3 * cx κ cT * ε ^ 2 ≤ cE ^ 2 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    nlinarith

end Run

end

end Step2
