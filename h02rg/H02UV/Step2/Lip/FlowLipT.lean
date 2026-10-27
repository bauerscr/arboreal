import Step2.Lip.FlowLipFinal

/-!
# (LT) along two histories (Lipschitz bounds, part 31)

From `LT_K`, `LT_D` and `Run.theta_j`: both components of `T_j(t') - T_j(t)` are bounded by
`κ₁ ‖δx_j‖ + (e + ε) C_T (‖δx_j‖ + |δg_j| + |δμ_j| + M)` with
`κ₁ ≥ 8(2 + e) max(κ_K, κ_D)` (`LT_hist`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- The constant `C_T`. -/
def cTT (κK κD C₁ C₃ kThv cxx V : ℝ) : ℝ :=
  8 * κK * kThv + 64 * C₁ * (1 + Real.exp 1 + 2 * kThv) + 8 * κD * (kThv + 28 * cxx * V) +
    256 * C₃ * (2 + Real.exp 1 + 2 * (kThv + 28 * cxx * V))

section Hist

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

set_option maxHeartbeats 1000000 in
/-- **(LT) along two histories.** -/
theorem LT_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (hval : ∀ i ≤ j, ValidAt R i)
    {M V W₁ Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z)
    (hev : ∀ i ≤ j, evH R i t t' ≤ V * M) (heW : eWH R j t t' ≤ (e + ε) * W₁ * M)
    (hew : ewH R j t t' ≤ Z * M) {κK κD C₁ C₃ κ₁ : ℝ} (hκK : 0 ≤ κK) (hκD : 0 ≤ κD)
    (hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃)
    (hκ₁ : 8 * (2 + Real.exp 1) * κK ≤ κ₁) (hκ₁' : 8 * (2 + Real.exp 1) * κD ≤ κ₁)
    (hK : Knorm (j + 1) R.ℓ R.A (nKH R j t' - nKH R j t) ≤
      ENNReal.ofReal (4 * (2 * κK * e ^ 2 + 16 * C₁ * e ^ 3) * relDist e (aIn R j t t')
        (bWIn R cw j t t' + bDIn R (cx κ cT) j t t') (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1
          (R.ℓ / 4)))
    (hD : Fnorm (j + 1) R.ℓ (nDH R j t' - nDH R j t) ≤
      ENNReal.ofReal (4 * (2 * κD * e ^ 2 + 64 * C₃ * e ^ 4) * relDist e (aIn R j t t')
        (bWIn R cw j t t' + bDIn R (cx κ cT) j t t') (bDIn R (cx κ cT) j t t') (lD R Kc j t t') 1
          (R.ℓ / 4))) :
    let C := cTT κK κD C₁ C₃ (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8)
      V W₁ Z) (cx κ cT) V
    let Q := ‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M
    ‖(Tmap R j t').2 - (Tmap R j t).2‖ ≤ κ₁ * ‖(t' j).2.2 - (t j).2.2‖ + (e + ε) * C * Q ∧
      ‖(Tmap R j t').1 - (Tmap R j t).1‖ ≤ κ₁ * ‖(t' j).2.2 - (t j).2.2‖ + (e + ε) * C * Q := by
  intro C Q
  have HC := H.cmp j le_rfl
  have he := HC.he
  have he1 := H.he1
  have hε := H.hε0
  have hε1 := HC.hε1
  have hcx := HC.hcx
  have hE := (Real.exp_pos 1).le
  set kT := kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z with hkTd
  have hkT : 0 ≤ kT := by
    have := HC.hcw; have := HC.hcmu
    rw [hkTd]; unfold kTh cTh; have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
    have := H.hKc
    positivity
  set dx := ‖(t' j).2.2 - (t j).2.2‖
  set Θ := thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t')
  have hdx : 0 ≤ dx := norm_nonneg _
  have hQ : 0 ≤ Q := by simp only [Q]; positivity
  have hdxQ : dx ≤ Q := by
    simp only [Q]; have := abs_nonneg ((t' j).1 - (t j).1); have := abs_nonneg ((t' j).2.1 - (t j).2.1)
    linarith
  have hσ : 0 ≤ e + ε := by linarith
  have hΘ := H.theta_j hM hV hW₁ hZ hev heW hew
  rw [← hkTd] at hΘ
  have hΘ0 := thetaH_nonneg HC
  -- `Θ ≤ (1 + E) dx + σ kT Q`
  have hΘQ : Θ ≤ (1 + Real.exp 1) * dx + (e + ε) * kT * Q := by
    have : (e + ε) * kT * (|(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) ≤ (e + ε) * kT * Q :=
      mul_le_mul_of_nonneg_left (by simp only [Q]; linarith) (by positivity)
    linarith
  have hΘ2 : Θ ≤ (1 + Real.exp 1 + 2 * kT) * Q := by
    have a1 : (1 + Real.exp 1) * dx ≤ (1 + Real.exp 1) * Q := mul_le_mul_of_nonneg_left hdxQ (by positivity)
    have a2 : (e + ε) * kT * Q ≤ 2 * kT * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hkT) hQ
    linarith only [hΘQ, a1, a2, show (1 + Real.exp 1 + 2 * kT) * Q = (1 + Real.exp 1) * Q + 2 * kT * Q by ring]
  have hC0 : 0 ≤ C := by simp only [C]; unfold cTT; positivity
  refine ⟨(LT_K H hval hκK hC₁ hK).trans ?_, (LT_D H hval hκD hC₃ hD).trans ?_⟩
  · -- the activity
    have a1 := mul_le_mul_of_nonneg_left hΘQ (by positivity : (0 : ℝ) ≤ 8 * κK)
    have a2 : 64 * C₁ * e * Θ ≤ (e + ε) * (64 * C₁ * (1 + Real.exp 1 + 2 * kT)) * Q := by
      have := mul_le_mul (mul_le_mul_of_nonneg_left (show e ≤ e + ε by linarith)
        (by positivity : (0 : ℝ) ≤ 64 * C₁)) hΘ2 hΘ0 (by positivity)
      linarith only [this, show 64 * C₁ * (e + ε) * ((1 + Real.exp 1 + 2 * kT) * Q) =
        (e + ε) * (64 * C₁ * (1 + Real.exp 1 + 2 * kT)) * Q by ring]
    have a3 : 8 * κK * ((1 + Real.exp 1) * dx) ≤ κ₁ * dx := by
      have : 8 * κK * (1 + Real.exp 1) ≤ κ₁ := by nlinarith
      have := mul_le_mul_of_nonneg_right this hdx
      linarith only [this, show 8 * κK * ((1 + Real.exp 1) * dx) = 8 * κK * (1 + Real.exp 1) * dx by ring]
    have a4 : (e + ε) * (8 * κK * kT) * Q + (e + ε) * (64 * C₁ * (1 + Real.exp 1 + 2 * kT)) * Q ≤
        (e + ε) * C * Q := by
      have : 8 * κK * kT + 64 * C₁ * (1 + Real.exp 1 + 2 * kT) ≤ C := by
        simp only [C]; unfold cTT
        have : 0 ≤ 8 * κD * (kT + 28 * cx κ cT * V) +
            256 * C₃ * (2 + Real.exp 1 + 2 * (kT + 28 * cx κ cT * V)) := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hσ) hQ
      linarith only [this, show (e + ε) * (8 * κK * kT + 64 * C₁ * (1 + Real.exp 1 + 2 * kT)) * Q =
        (e + ε) * (8 * κK * kT) * Q + (e + ε) * (64 * C₁ * (1 + Real.exp 1 + 2 * kT)) * Q by ring]
    have e1 : 4 * (2 * κK + 16 * C₁ * e) * Θ = 8 * κK * Θ + 64 * C₁ * e * Θ := by ring
    have e2 : 8 * κK * ((1 + Real.exp 1) * dx + (e + ε) * kT * Q) =
        8 * κK * ((1 + Real.exp 1) * dx) + (e + ε) * (8 * κK * kT) * Q := by ring
    linarith only [e1, a1, a2, a3, a4, e2]
  · -- the remainder
    have hbD : bDIn R (cx κ cT) j t t' ≤ dx + (e + ε) * (28 * cx κ cT * V) * Q := by
      unfold bDIn
      have hζ := (eζ_le_ev HC.H HC.H').trans (hev j le_rfl)
      have hg3 : (t j).1 ^ 3 ≤ ε := by
        have h1 : (t j).1 ^ 3 ≤ ε ^ 3 := by have := HC.H.g_pos; have := HC.H.g_le; gcongr
        have h2 : ε ^ 3 ≤ ε := by
          have := pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ 3 by norm_num); simpa using this
        linarith
      have hMQ : M ≤ Q := by
        simp only [Q]; have := abs_nonneg ((t' j).1 - (t j).1)
        have := abs_nonneg ((t' j).2.1 - (t j).2.1); linarith
      have b1 : 14 * (2 * eζH R j t t') * (cx κ cT * (t j).1 ^ 3) ≤ 28 * cx κ cT * ε * (V * M) := by
        have hg0 : 0 ≤ (t j).1 := HC.H.g_pos.le
        have := mul_le_mul hζ (mul_le_mul_of_nonneg_left hg3 hcx) (by positivity)
          (by positivity)
        linarith only [this, show 14 * (2 * eζH R j t t') * (cx κ cT * (t j).1 ^ 3) =
          28 * (eζH R j t t' * (cx κ cT * (t j).1 ^ 3)) by ring,
          show 28 * cx κ cT * ε * (V * M) = 28 * (V * M * (cx κ cT * ε)) by ring]
      have b2 : 28 * cx κ cT * ε * (V * M) ≤ (e + ε) * (28 * cx κ cT * V) * Q := by
        have := mul_le_mul (mul_le_mul_of_nonneg_left (show ε ≤ e + ε by linarith)
          (by positivity : (0 : ℝ) ≤ 28 * cx κ cT)) (mul_le_mul_of_nonneg_left hMQ hV)
          (by positivity) (by positivity)
        linarith only [this, show 28 * cx κ cT * (e + ε) * (V * Q) = (e + ε) * (28 * cx κ cT * V) * Q by ring]
      linarith only [b1, b2]
    set c1 := kT + 28 * cx κ cT * V
    have hc1 : 0 ≤ c1 := by positivity
    have hS : Θ + bDIn R (cx κ cT) j t t' ≤ (2 + Real.exp 1) * dx + (e + ε) * c1 * Q := by
      have := hΘQ
      linarith only [this, hbD, show (e + ε) * c1 * Q = (e + ε) * kT * Q +
        (e + ε) * (28 * cx κ cT * V) * Q by simp only [c1]; ring]
    have hS2 : Θ + bDIn R (cx κ cT) j t t' ≤ (2 + Real.exp 1 + 2 * c1) * Q := by
      have a1 : (2 + Real.exp 1) * dx ≤ (2 + Real.exp 1) * Q := mul_le_mul_of_nonneg_left hdxQ (by positivity)
      have a2 : (e + ε) * c1 * Q ≤ 2 * c1 * Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hc1) hQ
      linarith only [hS, a1, a2, show (2 + Real.exp 1 + 2 * c1) * Q = (2 + Real.exp 1) * Q + 2 * c1 * Q by ring]
    have hS0 : 0 ≤ Θ + bDIn R (cx κ cT) j t t' := by have := HC.bDIn_nonneg; linarith
    have a1 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 8 * κD)
    have a2 : 256 * C₃ * e ^ 2 * (Θ + bDIn R (cx κ cT) j t t') ≤
        (e + ε) * (256 * C₃ * (2 + Real.exp 1 + 2 * c1)) * Q := by
      have he2 : e ^ 2 ≤ e + ε := by
        have : e ^ 2 ≤ e := pow_le_of_le_one he.le he1 (by norm_num)
        linarith
      have := mul_le_mul (mul_le_mul_of_nonneg_left he2 (by positivity : (0 : ℝ) ≤ 256 * C₃)) hS2
        hS0 (by positivity)
      linarith only [this, show 256 * C₃ * (e + ε) * ((2 + Real.exp 1 + 2 * c1) * Q) =
        (e + ε) * (256 * C₃ * (2 + Real.exp 1 + 2 * c1)) * Q by ring]
    have a3 : 8 * κD * ((2 + Real.exp 1) * dx) ≤ κ₁ * dx := by
      have := mul_le_mul_of_nonneg_right hκ₁' hdx
      linarith only [this, show 8 * κD * ((2 + Real.exp 1) * dx) = 8 * (2 + Real.exp 1) * κD * dx by ring]
    have a4 : (e + ε) * (8 * κD * c1) * Q + (e + ε) * (256 * C₃ * (2 + Real.exp 1 + 2 * c1)) * Q ≤
        (e + ε) * C * Q := by
      have : 8 * κD * c1 + 256 * C₃ * (2 + Real.exp 1 + 2 * c1) ≤ C := by
        simp only [C, c1]; unfold cTT
        have : 0 ≤ 8 * κK * kT + 64 * C₁ * (1 + Real.exp 1 + 2 * kT) := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hσ) hQ
      linarith only [this, show (e + ε) * (8 * κD * c1 + 256 * C₃ * (2 + Real.exp 1 + 2 * c1)) * Q =
        (e + ε) * (8 * κD * c1) * Q + (e + ε) * (256 * C₃ * (2 + Real.exp 1 + 2 * c1)) * Q by ring]
    have e1 : 4 * (2 * κD + 64 * C₃ * e ^ 2) * (Θ + bDIn R (cx κ cT) j t t') =
        8 * κD * (Θ + bDIn R (cx κ cT) j t t') + 256 * C₃ * e ^ 2 * (Θ + bDIn R (cx κ cT) j t t') := by
      ring
    have e2 : 8 * κD * ((2 + Real.exp 1) * dx + (e + ε) * c1 * Q) =
        8 * κD * ((2 + Real.exp 1) * dx) + (e + ε) * (8 * κD * c1) * Q := by ring
    linarith only [e1, a1, a2, a3, a4, e2]

end Hist

end

end Step2
