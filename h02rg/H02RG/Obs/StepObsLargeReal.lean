import Mathlib

/-!
# Real inequalities for the large set bound

The elementary real inequalities used in `Obs.StepObsLarge` (kept in a separate file with a small
context, so that `nlinarith` stays fast).
-/

namespace Obs

theorem exp_sub_one_le_two_mul' {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : Real.exp x - 1 ≤ 2 * x := by
  have := (abs_le.1 (Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx))).2
  rw [abs_of_nonneg hx0] at this
  linarith

/-- Auxiliary: `x + x²/2 ≤ 2x` for `0 ≤ x ≤ 1`. -/
theorem sq_half_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x + x ^ 2 / 2 ≤ 2 * x := by
  have := mul_le_mul_of_nonneg_left h1 h0; nlinarith

theorem zle_aux {vbr α s s' GB GO : ℝ} (hv : 0 ≤ vbr) (hα : 0 ≤ α) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (hvG : vbr ≤ GB) (hαG : α ≤ GB) (hsG : s ≤ GO) (hs'G : s' ≤ GO)
    (e1 : Real.exp vbr - 1 ≤ 2 * vbr) (e2 : Real.exp (α + 2 * α) - 1 ≤ 2 * (α + 2 * α))
    (q1 : s + s ^ 2 / 2 ≤ 2 * s) (q2 : s' + s' ^ 2 / 2 ≤ 2 * s') :
    (Real.exp vbr - 1) * (s + s ^ 2 / 2) + (Real.exp (α + 2 * α) - 1) * (s' + s' ^ 2 / 2) ≤
      16 * (GB * GO) := by
  have t1 : (Real.exp vbr - 1) * (s + s ^ 2 / 2) ≤ (2 * vbr) * (2 * s) :=
    mul_le_mul e1 q1 (by nlinarith) (by positivity)
  have t2 : (Real.exp (α + 2 * α) - 1) * (s' + s' ^ 2 / 2) ≤ (2 * (α + 2 * α)) * (2 * s') :=
    mul_le_mul e2 q2 (by nlinarith) (by positivity)
  have t3 := mul_le_mul hvG hsG hs (hv.trans hvG)
  have t4 := mul_le_mul hαG hs'G hs' (hα.trans hαG)
  nlinarith

theorem σle_aux {vbr α s s' GO : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (hsG : s ≤ GO) (hs'G : s' ≤ GO) (t1 : Real.exp vbr ≤ 2) (t2 : Real.exp (α + 2 * α) ≤ 2)
    (q1 : s + s ^ 2 / 2 ≤ 2 * s) (q2 : s' + s' ^ 2 / 2 ≤ 2 * s') :
    Real.exp vbr * (s + s ^ 2 / 2) + Real.exp (α + 2 * α) * (s' + s' ^ 2 / 2) ≤ 8 * GO := by
  have h1 := mul_le_mul t1 q1 (by positivity) (by norm_num)
  have h2 := mul_le_mul t2 q2 (by positivity) (by norm_num)
  linarith

theorem Γle_aux {δ mM z G Q Bs Os kor : ℝ} (hδ : 0 ≤ δ) (hz : 0 ≤ z) (hG1 : 1 ≤ G)
    (hBs : 0 ≤ Bs) (hOs : 0 ≤ Os) (hO1 : Os ≤ 1) (hBO : Bs * Os ≤ 1)
    (hδG : δ ≤ G * kor) (hkor : 0 ≤ kor) (hmM : mM ≤ 2 * G * Os)
    (hzle : z ≤ 16 * G ^ 2 * (Bs * Os)) (hQ3 : Bs * Os ≤ Q) (hQ4 : kor * kor ≤ Q) :
    δ ^ 2 + 2 * mM * z + z ^ 2 ≤ 321 * G ^ 4 * Q := by
  have hG2 : G ^ 2 ≤ G ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
  have hG3 : G ^ 3 ≤ G ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
  have hQ0 : 0 ≤ Q := (mul_nonneg hBs hOs).trans hQ3
  have t1 : δ ^ 2 ≤ G ^ 2 * Q := by
    have h1 := mul_le_mul hδG hδG hδ (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hQ4 (by positivity : (0 : ℝ) ≤ G ^ 2)
    calc δ ^ 2 = δ * δ := sq δ
      _ ≤ G * kor * (G * kor) := h1
      _ = G ^ 2 * (kor * kor) := by ring
      _ ≤ G ^ 2 * Q := h2
  have t3 : 2 * mM * z ≤ 64 * G ^ 3 * Q := by
    have hm0 : 0 ≤ mM ∨ mM < 0 := le_or_gt 0 mM
    have h1 : 2 * mM * z ≤ 2 * (2 * G * Os) * (16 * G ^ 2 * (Bs * Os)) := by
      rcases hm0 with h | h
      · have := mul_le_mul hmM hzle hz (by positivity); nlinarith
      · have : 2 * mM * z ≤ 0 := by nlinarith
        have : 0 ≤ 2 * (2 * G * Os) * (16 * G ^ 2 * (Bs * Os)) := by positivity
        linarith
    have h2 : Os * (Bs * Os) ≤ Bs * Os := by
      have := mul_le_mul_of_nonneg_right hO1 (mul_nonneg hBs hOs); linarith
    have h3 := mul_le_mul_of_nonneg_left (h2.trans hQ3) (by positivity : (0 : ℝ) ≤ 64 * G ^ 3)
    calc 2 * mM * z ≤ 2 * (2 * G * Os) * (16 * G ^ 2 * (Bs * Os)) := h1
      _ = 64 * G ^ 3 * (Os * (Bs * Os)) := by ring
      _ ≤ 64 * G ^ 3 * Q := h3
  have t4 : z ^ 2 ≤ 256 * G ^ 4 * Q := by
    have h1 := mul_le_mul hzle hzle hz (by positivity)
    have h2 : (Bs * Os) * (Bs * Os) ≤ Bs * Os := by
      have := mul_le_mul_of_nonneg_left hBO (mul_nonneg hBs hOs); linarith
    have h3 := mul_le_mul_of_nonneg_left (h2.trans hQ3) (by positivity : (0 : ℝ) ≤ 256 * G ^ 4)
    calc z ^ 2 = z * z := sq z
      _ ≤ 16 * G ^ 2 * (Bs * Os) * (16 * G ^ 2 * (Bs * Os)) := h1
      _ = 256 * G ^ 4 * ((Bs * Os) * (Bs * Os)) := by ring
      _ ≤ 256 * G ^ 4 * Q := h3
  have a1 := mul_le_mul_of_nonneg_right hG2 hQ0
  have a2 := mul_le_mul_of_nonneg_right hG3 hQ0
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The smallness consequences for the parameters of the large set bound. -/
theorem large_real {vbr kbr vor kor CB C₁ CV K₂ G Ld r : ℝ}
    (hvbr0 : 0 ≤ vbr) (hkbr0 : 0 ≤ kbr) (hvor0 : 0 ≤ vor) (hkor0 : 0 ≤ kor)
    (hCB : 0 ≤ CB) (hC₁ : 0 ≤ C₁) (hCV : 1 ≤ CV) (hK₂1 : 1 ≤ K₂)
    (hG1 : 1 ≤ G) (hCBG : 1 + CB ≤ G) (hC₁G : C₁ ≤ G) (hCVK : CV * K₂ ≤ G) (hK₂G : K₂ ≤ G)
    (hLd1 : 1 ≤ Ld) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hGSL : 72 * (G * (vbr + kbr + (vor + kor)) * Ld) ≤ r ^ 2)
    {α s s' q σ z δ mM Γ t Q : ℝ} (hα : α = vbr + CB * kbr) (hs : s = K₂ * vor)
    (hs' : s' = CV * K₂ * (vor + kor)) (hq : q = C₁ * (vbr + kbr))
    (hσ : σ = Real.exp vbr * (s + s ^ 2 / 2) + Real.exp (α + 2 * α) * (s' + s' ^ 2 / 2))
    (hz : z = (Real.exp vbr - 1) * (s + s ^ 2 / 2) +
      (Real.exp (α + 2 * α) - 1) * (s' + s' ^ 2 / 2))
    (hδ : δ = CV * K₂ * kor) (hmM : mM = s + s') (hΓ : Γ = δ ^ 2 + 2 * mM * z + z ^ 2)
    (ht : t = α + s' + (2 * α + s'))
    (hQ : Q = (vbr + kbr + kor) * (vbr + vor + kbr + kor)) :
    K₂ * (vor + kor) ≤ 1 ∧ 2 * (q + σ) ≤ r ^ 2 ∧ 3 * t * Ld ≤ 1 / 8 ∧
      4 * (Γ + 2 * σ * q + q ^ 2) ≤ 1352 * G ^ 4 * Q ∧
      3 * t * Ld * kbr ≤ 9 * (G * Ld) * Q ∧ 0 ≤ z ∧ 0 ≤ σ ∧ 0 ≤ Γ ∧ 0 ≤ t := by
  set Bs := vbr + kbr with hBs
  set Os := vor + kor with hOs
  set S := Bs + Os with hS
  have hBs0 : 0 ≤ Bs := add_nonneg hvbr0 hkbr0
  have hOs0 : 0 ≤ Os := add_nonneg hvor0 hkor0
  have hS0 : 0 ≤ S := add_nonneg hBs0 hOs0
  have hG0 : 0 ≤ G := by linarith
  have hr21 : r ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hr0.le hr1
  have hGSLd : G * S ≤ G * S * Ld := le_mul_of_one_le_right (mul_nonneg hG0 hS0) hLd1
  have hGS : G * S ≤ 1 / 72 := by linarith
  have hGB : G * Bs ≤ 1 / 72 :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hG0) hGS
  have hGO : G * Os ≤ 1 / 72 :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hG0) hGS
  have hB1 : Bs ≤ 1 / 72 := le_trans (le_mul_of_one_le_left hBs0 hG1) hGB
  have hO1 : Os ≤ 1 / 72 := le_trans (le_mul_of_one_le_left hOs0 hG1) hGO
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs'0 : 0 ≤ s' := by rw [hs']; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hαG : α ≤ G * Bs := by
    have h1 := mul_le_mul_of_nonneg_right hCBG hBs0
    have h2 : α ≤ (1 + CB) * Bs := by
      rw [hα, hBs]; have := mul_nonneg hCB hvbr0; linarith
    linarith
  have hsG : s ≤ G * Os := by
    have h1 := mul_le_mul_of_nonneg_right hK₂G hvor0
    have h2 := mul_le_mul_of_nonneg_left (show vor ≤ Os by rw [hOs]; linarith) hG0
    rw [hs]; linarith
  have hs'G : s' ≤ G * Os := by
    rw [hs', hOs]; exact mul_le_mul_of_nonneg_right hCVK hOs0
  have hqG : q ≤ G * Bs := by rw [hq]; exact mul_le_mul_of_nonneg_right hC₁G hBs0
  have hδG : δ ≤ G * kor := by rw [hδ]; exact mul_le_mul_of_nonneg_right hCVK hkor0
  have hvG : vbr ≤ G * Bs := le_trans (by linarith) (le_mul_of_one_le_left hBs0 hG1)
  have hexp1 : Real.exp vbr - 1 ≤ 2 * vbr := exp_sub_one_le_two_mul' hvbr0 (by linarith)
  have hexp2 : Real.exp (α + 2 * α) - 1 ≤ 2 * (α + 2 * α) :=
    exp_sub_one_le_two_mul' (by positivity) (by linarith)
  have hsq : s + s ^ 2 / 2 ≤ 2 * s := sq_half_le hs0 (by linarith)
  have hsq' : s' + s' ^ 2 / 2 ≤ 2 * s' := sq_half_le hs'0 (by linarith)
  have e1 : 0 ≤ Real.exp vbr - 1 := by linarith [Real.add_one_le_exp vbr]
  have e2 : 0 ≤ Real.exp (α + 2 * α) - 1 := by linarith [Real.add_one_le_exp (α + 2 * α)]
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hzle : z ≤ 16 * G ^ 2 * (Bs * Os) := by
    have := zle_aux hvbr0 hα0 hs0 hs'0 hvG hαG hsG hs'G hexp1 hexp2 hsq hsq'
    rw [hz]; linarith [show 16 * (G * Bs * (G * Os)) = 16 * G ^ 2 * (Bs * Os) by ring]
  have hσle : σ ≤ 8 * (G * Os) := by
    rw [hσ]; exact σle_aux hs0 hs'0 hsG hs'G (by linarith) (by linarith) hsq hsq'
  have hQ1 : Bs * S ≤ Q := by
    rw [hQ]
    have e : S = vbr + vor + kbr + kor := by rw [hS, hBs, hOs]; ring
    rw [e]; exact mul_le_mul_of_nonneg_right (by rw [hBs]; linarith) (by positivity)
  have hQ2 : kor * S ≤ Q := by
    rw [hQ]
    have e : S = vbr + vor + kbr + kor := by rw [hS, hBs, hOs]; ring
    rw [e]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hQ3 : Bs * Os ≤ Q := le_trans (mul_le_mul_of_nonneg_left (by linarith) hBs0) hQ1
  have hQ4 : kor * kor ≤ Q := le_trans (mul_le_mul_of_nonneg_left (by linarith) hkor0) hQ2
  have hQ5 : Bs * Bs ≤ Q := le_trans (mul_le_mul_of_nonneg_left (by linarith) hBs0) hQ1
  have hQ0 : 0 ≤ Q := (mul_nonneg hBs0 hOs0).trans hQ3
  have hBO : Bs * Os ≤ 1 := by
    have := mul_le_mul hB1 hO1 hOs0 (by norm_num); linarith
  have hΓle : Γ ≤ 321 * G ^ 4 * Q := by
    rw [hΓ]
    exact Γle_aux hδ0 hz0 hG1 hBs0 hOs0 (by linarith) hBO hδG hkor0
      (by rw [hmM]; linarith) hzle hQ3 hQ4
  have hΓ0 : 0 ≤ Γ := by
    have hmM0 : 0 ≤ mM := by rw [hmM]; linarith
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hmM0) hz0
    rw [hΓ]; nlinarith [sq_nonneg δ, sq_nonneg z]
  have hG2 : G ^ 2 ≤ G ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
  have hΨ : 4 * (Γ + 2 * σ * q + q ^ 2) ≤ 1352 * G ^ 4 * Q := by
    have t1 : 2 * σ * q ≤ 16 * G ^ 2 * Q := by
      have h1 := mul_le_mul hσle hqG hq0 (by positivity)
      have h2 := mul_le_mul_of_nonneg_left hQ3 (by positivity : (0 : ℝ) ≤ 16 * G ^ 2)
      calc 2 * σ * q = 2 * (σ * q) := by ring
        _ ≤ 2 * (8 * (G * Os) * (G * Bs)) := by linarith
        _ = 16 * G ^ 2 * (Bs * Os) := by ring
        _ ≤ 16 * G ^ 2 * Q := h2
    have t2 : q ^ 2 ≤ G ^ 2 * Q := by
      have h1 := mul_le_mul hqG hqG hq0 (by positivity)
      have h2 := mul_le_mul_of_nonneg_left hQ5 (by positivity : (0 : ℝ) ≤ G ^ 2)
      calc q ^ 2 = q * q := sq q
        _ ≤ G * Bs * (G * Bs) := h1
        _ = G ^ 2 * (Bs * Bs) := by ring
        _ ≤ G ^ 2 * Q := h2
    have h3 := mul_le_mul_of_nonneg_right hG2 hQ0
    linarith
  have hρr : 2 * (q + σ) ≤ r ^ 2 := by
    have : G * Bs + G * Os = G * S := by rw [hS]; ring
    linarith
  have htle : t ≤ 3 * (G * S) := by
    rw [ht]
    have : G * Bs + G * Os = G * S := by rw [hS]; ring
    linarith
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hκ : 3 * t * Ld ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_right htle (by positivity : (0 : ℝ) ≤ 3 * Ld)
    have e : 3 * (G * S) * (3 * Ld) = 9 * (G * S * Ld) := by ring
    linarith
  have hW : 3 * t * Ld * kbr ≤ 9 * (G * Ld) * Q := by
    have h1 := mul_le_mul_of_nonneg_right htle (by positivity : (0 : ℝ) ≤ 3 * Ld * kbr)
    have h2 : kbr * S ≤ Q := le_trans (mul_le_mul_of_nonneg_right (by linarith) hS0) hQ1
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 9 * G * Ld)
    calc 3 * t * Ld * kbr = t * (3 * Ld * kbr) := by ring
      _ ≤ 3 * (G * S) * (3 * Ld * kbr) := h1
      _ = 9 * G * Ld * (kbr * S) := by ring
      _ ≤ 9 * G * Ld * Q := h3
      _ = 9 * (G * Ld) * Q := by ring
  refine ⟨?_, hρr, hκ, hΨ, hW, hz0, hσ0, hΓ0, ht0⟩
  have := mul_le_mul_of_nonneg_right hK₂G hOs0
  linarith

/-- The final inequality of the large set bound. -/
theorem large_final_real {a A kor Q M W Ψ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hA1 : 1 ≤ A)
    (hkor : 0 ≤ kor) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hW : W ≤ M * kor + 9 * M * Q)
    (hΨ : Ψ ≤ 1352 * M * Q) :
    a * W + Ψ * A ≤ 1400 * (a * (M * kor)) + 1400 * (M * Q * A) := by
  have h1 := mul_le_mul_of_nonneg_left hW ha0
  have h2 : a * (9 * M * Q) ≤ 9 * M * Q * A := by
    have := mul_le_mul ha1 hA1 (by norm_num) (by linarith)
    have h9 : 0 ≤ 9 * M * Q := by positivity
    nlinarith
  have h3 := mul_le_mul_of_nonneg_right hΨ (by linarith : (0 : ℝ) ≤ A)
  have h4 : 0 ≤ a * (M * kor) := by positivity
  have h5 : 0 ≤ M * Q * A := by have : 0 ≤ A := by linarith
                                positivity
  nlinarith

end Obs
