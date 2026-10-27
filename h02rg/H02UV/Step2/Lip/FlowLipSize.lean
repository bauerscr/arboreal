import Step2.Lip.FlowLipShv

/-!
# Size bounds for the outputs of a step of a history (Lipschitz bounds, part 19)

On the domain, at the radius `r = c_E g` of the history itself, the outputs of step `k` are
bounded: `‖K̂_{k+1}‖ ≤ κ k + C₁(r³ + r k + k²)` with `k = e c_x g³` (`size_K`),
`‖D̂_{k+1}‖ ≤ C₀ L^{-1} c_x g³ + C₃ (r² + r²)²` (`size_D`), and the coupling remainder
`≤ bRem(r, r², k)` (`size_rem`), at any output scale `ℓ_o ≤ 5ℓ/4`. These are the sizes entering
the phase terms and the marginal coordinate.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- The radius constant `c_E = c_V + c_w + 3 c_x + 1`. -/
def cEr (ℓ cz cw cxx cmuu : ℝ) : ℝ := cVf (7 / 8 * ℓ) cz cmuu + cw + 3 * cxx + 1

section Dom

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

theorem cEr_ge (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hc : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm)) :
    1 ≤ cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) := by
  unfold cEr; linarith

/-- The input bounds at the radius `r = c_E g`. -/
theorem DomH.r_bounds (H : DomH k t Λ κ cm cT ε cz cw) (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hg1 : (t k).1 ≤ 1)
    (hΔ : cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4) :
    let r := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1
    Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t)) ≤ ENNReal.ofReal r ∧
      Fnorm k (7 / 8 * R.ℓ) ((sdH R k t).W + (sdH R k t).D) ≤ ENNReal.ofReal (r ^ 2) ∧
      Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t)) ≤
        ENNReal.ofReal (Real.exp 1 * (cx κ cT * (t k).1 ^ 3)) := by
  intro r
  have hℓ : 0 < R.ℓ := Fact.out
  have hA : 0 < R.A := Fact.out
  have hg := H.g_pos
  have hs := H.sdH_OK
  have hsm : cz * (t k).1 ≤ 1 / 16 := by have := H.czg; have := H.h16; linarith
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have := H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE := cEr_ge (R := R) hcw hcx hcV
  refine ⟨?_, ?_, ?_⟩
  · refine (hs.V_le (by positivity) H.hcz hsm hm).trans (ENNReal.ofReal_le_ofReal ?_)
    show cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) * (t k).1 ≤ cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1
    unfold cEr; nlinarith
  · refine (Fnorm_add_le _ _ (by positivity) (by positivity) hs.hWn hs.hDn).trans
      (ENNReal.ofReal_le_ofReal ?_)
    show cw * (t k).1 ^ 2 + cx κ cT * (t k).1 ^ 3 ≤ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2
    have h3 : (t k).1 ^ 3 ≤ (t k).1 ^ 2 := by nlinarith [sq_nonneg (t k).1]
    have hc2 : cw + cx κ cT ≤ cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) ^ 2 := by
      unfold cEr at hcE ⊢; nlinarith
    have := mul_le_mul_of_nonneg_left h3 hcx
    nlinarith [sq_nonneg (t k).1]
  · have h1 : R.A / 2 ≤ R.A * Real.exp (-(1 / 4)) := by
      have := Real.add_one_le_exp (-(1 / 4)); nlinarith
    exact (Knorm_mono_wt (by positivity) h1 _).trans
      (hs.Kf_le (by positivity) hA.le H.hcz hsm hm hΔ)

end Dom

set_option maxHeartbeats 1000000 in
/-- **The size of the coupling remainder of step `k`.** -/
theorem size_rem : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], 2 ≤ R.A →
    ∀ (k : ℕ) (t : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw : ℝ),
      DomH k t Λ κ cm cT ε cz cw →
      |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 → 0 ≤ cw → 0 ≤ cx κ cT → 0 ≤ cmu Λ cm → (t k).1 ≤ 1 →
      cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 →
      cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 ≤ 1 →
      Real.exp 1 * (cx κ cT * (t k).1 ^ 3) ≤ 1 →
      ∀ i : Fin 4, cwt L k i * ‖kapH R k t i - SD.shv R k (sdH R k t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t k).1 ^ 3)) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := coupRem_bound
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R _ _ hA2 k t Λ κ cm cT ε cz cw H hm hcw hcx hcmu hg1 hΔ hr hk i
  have hℓ : 0 < R.ℓ := Fact.out
  have hs := H.sdH_OK
  have hg := H.g_pos
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have := H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE := cEr_ge (R := R) hcw hcx hcV
  obtain ⟨hV, hWD, hKf⟩ := H.r_bounds hm hcw hcx hcmu hg1 hΔ
  have hr0 : 0 ≤ cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 := by positivity
  have hr2 : (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2 ≤ 1 := by nlinarith
  have e1 : kapH R k t i - SD.shv R k (sdH R k t) i =
      coupRem k R.i₀ (sdH R k t).C (nVec R k (sdH R k t).zh (sdH R k t).yh (sdH R k t).g
        (sdH R k t).μ (sdH R k t).w) ((sdH R k t).W + (sdH R k t).D) (SD.Kf R k (sdH R k t)) i := by
    have := SD.kap_eq R k (sdH R k t)
    rw [show kapH R k t = SD.kap R k (sdH R k t) from rfl, this, Pi.add_apply, add_sub_cancel_right]
  rw [e1]
  exact h L hL8 hLp N k hs.hk R.i₀ (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (by positivity) hℓ (by positivity)
    (by linarith) _ hs.hC hs.hCs hs.hCsym _ _ _ (add_mem hs.hW hs.hD) (hs.Kf_mem hL8) (R.A / 2)
    (by linarith) _ _ _ hr0 (sq_nonneg _) (by positivity) hr hr2 hk hV hWD hKf i

end

end Step2
