import Step2.Lip.FlowFadeRun

/-!
# Fading memory: the final step along two histories

The final-step bounds of `FlowLipFin`, `FlowLipFinal`, `FlowLipT` use the coupling errors at all
steps `i ≤ j` only through the covariance bound `lD_j² ≤ 2K_c L⁸ (V M)` and the error at `j`. Here
they are restated with these two facts as hypotheses (`*_w`), so that they apply to the weighted
errors of `run_errors_w`. New: the **difference form** of (LG),
`|δG_j - δǧ_j| ≤ σ 200K⁴ (|δǧ_j| + |δμ_j| + M) + 500K⁴ ‖δx_j‖` (`LGd_hist_w`), from
* `G_lip_d`: `|a'Φ' - aΦ - (a' - a)| ≤ 4s|δa| + |a|(2|δn| + 5|δζ|)`;
* `ghat_sub_sub_le`: `|δĝ - δg| ≤ 2τ|δg| + 2|g||δn|`;
* `G_core_d`, `G_assemble_d`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-! ### The difference form of (LG): elementary estimates -/

theorem norm_Phi_sub_one_le {ζ n : ℂ} {s : ℝ} (hs : s ≤ 1 / 16) (hζ : ‖ζ‖ ≤ s) (hn : ‖n‖ ≤ s) :
    ‖(1 + n) / (1 + ζ) ^ 2 - 1‖ ≤ 4 * s := by
  have hs0 : 0 ≤ s := (norm_nonneg ζ).trans hζ
  have h1 : 1 - s ≤ ‖1 + ζ‖ := le_trans (by linarith) (norm_one_add_ge (ζ := ζ))
  have hne : 1 + ζ ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  have e : (1 + n) / (1 + ζ) ^ 2 - 1 = (n - 2 * ζ - ζ ^ 2) / (1 + ζ) ^ 2 := by
    field_simp; ring
  rw [e, norm_div, norm_pow, div_le_iff₀ (by positivity)]
  have hN : ‖n - 2 * ζ - ζ ^ 2‖ ≤ s + 2 * s + s ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add hn ?_)) ?_
    · rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
    · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hq : (15 / 16 : ℝ) ^ 2 ≤ ‖1 + ζ‖ ^ 2 := by
    have : 15 / 16 ≤ ‖1 + ζ‖ := by linarith
    gcongr
  have h2 : s ^ 2 ≤ s / 16 := by nlinarith
  nlinarith

/-- **The marginal coupling map minus its identity part.** -/
theorem G_lip_d {a a' ζ ζ' n n' : ℂ} {s : ℝ} (hs : s ≤ 1 / 16) (hζ : ‖ζ‖ ≤ s) (hζ' : ‖ζ'‖ ≤ s)
    (hn : ‖n‖ ≤ s) (hn' : ‖n'‖ ≤ s) :
    ‖(a' / (1 + ζ') ^ 2 * (1 + n') - a / (1 + ζ) ^ 2 * (1 + n)) - (a' - a)‖ ≤
      4 * s * ‖a' - a‖ + ‖a‖ * (2 * ‖n' - n‖ + 5 * ‖ζ' - ζ‖) := by
  have hs0 : 0 ≤ s := (norm_nonneg ζ).trans hζ
  -- the triangle inequality around `a' Φ - a' + (a' - a)`: reuse `G_lip` with `a = 0`
  have hG0 := G_lip (a := a) (a' := a) hs hζ hζ' hn hn'
  rw [sub_self, norm_zero, mul_zero, zero_add] at hG0
  have h1 := norm_Phi_sub_one_le hs hζ' hn'
  have e : (a' / (1 + ζ') ^ 2 * (1 + n') - a / (1 + ζ) ^ 2 * (1 + n)) - (a' - a) =
      (a' - a) * ((1 + n') / (1 + ζ') ^ 2 - 1) +
        (a / (1 + ζ') ^ 2 * (1 + n') - a / (1 + ζ) ^ 2 * (1 + n)) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (a' - a))
  linarith only [this, hG0, show ‖a' - a‖ * (4 * s) = 4 * s * ‖a' - a‖ by ring]

/-- The sharp difference of `ĝ = g/(1+n)` minus that of `g`. -/
theorem ghat_sub_sub_le (s s' : SD L N) {τ : ℝ} (hτ : ‖nCor (s'.μ : ℂ) s'.w‖ ≤ τ)
    (hτ2 : τ ≤ 1 / 2) :
    ‖(ghat s' - ghat s) - ((s'.g - s.g : ℝ) : ℂ)‖ ≤
      2 * τ * |s'.g - s.g| + 2 * |s.g| * ‖nCor (s'.μ : ℂ) s'.w - nCor (s.μ : ℂ) s.w‖ := by
  have h1 : 1 - τ ≤ ‖1 + nCor (s'.μ : ℂ) s'.w‖ :=
    le_trans (by linarith) (norm_one_add_ge (ζ := nCor (s'.μ : ℂ) s'.w))
  have hne : 1 + nCor (s'.μ : ℂ) s'.w ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  have e : (ghat s' - ghat s) - ((s'.g - s.g : ℝ) : ℂ) = ((s'.g - s.g : ℝ) : ℂ) *
      ((1 + nCor (s'.μ : ℂ) s'.w)⁻¹ - 1) +
      (s.g : ℂ) * ((1 + nCor (s'.μ : ℂ) s'.w)⁻¹ - (1 + nCor (s.μ : ℂ) s.w)⁻¹) := by
    simp only [ghat]; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hτ
  have a1 : ‖(1 + nCor (s'.μ : ℂ) s'.w)⁻¹ - 1‖ ≤ 2 * τ := by
    have e2 : (1 + nCor (s'.μ : ℂ) s'.w)⁻¹ - 1 =
        -(nCor (s'.μ : ℂ) s'.w) / (1 + nCor (s'.μ : ℂ) s'.w) := by field_simp; ring
    rw [e2, norm_div, norm_neg, div_le_iff₀ (by linarith)]
    nlinarith
  have a2 := norm_inv_one_add_sub_le (norm_nCor_le (s'.μ : ℂ) s'.w) (norm_nCor_le (s.μ : ℂ) s.w)
  have := mul_le_mul_of_nonneg_left a1 (abs_nonneg (s'.g - s.g))
  have := mul_le_mul_of_nonneg_left a2 (abs_nonneg s.g)
  nlinarith

/-- **Assembly for `G - g`.** -/
theorem G_assemble_d {K σ ε dx dg dμ M dĝ Θ d3 dζ dν dw dn1 dG s B3 dκ dĝg : ℝ}
    (H : Pieces K σ ε dx dg dμ M dĝ Θ) (hs : s ≤ σ * K) (hs0 : 0 ≤ s) (hB3 : B3 ≤ σ * K)
    (hB30 : 0 ≤ B3)
    (h3 : d3 ≤ K * Θ + dĝ) (hζ : dζ ≤ K * Θ + K * dĝ + σ * K * M)
    (hν : dν ≤ K * (Θ + dμ + dĝ + M)) (hw : dw ≤ K * M) (hn : dn1 ≤ K * (dν + dw))
    (hζ0 : 0 ≤ dζ) (hn0 : 0 ≤ dn1) (h30 : 0 ≤ d3) (hκ : dκ ≤ K * Θ)
    (hĝg : dĝg ≤ σ * (4 * K) * (dx + dg + dμ + M))
    (hG : dG ≤ 4 * s * d3 + B3 * (2 * dn1 + 5 * dζ) + dκ + dĝg) :
    dG ≤ σ * (200 * K ^ 4) * dg + σ * (200 * K ^ 4) * dμ + 500 * K ^ 4 * dx +
      σ * (200 * K ^ 4) * M := by
  have hK := H.hK
  have hK0 : 0 ≤ K := by linarith
  have hσ := H.hσ
  have hQ := H.Q0
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = dx + dg + dμ + M := ⟨_, rfl⟩
  rw [← hQd] at hQ hĝg
  have hĝQ : dĝ ≤ (1 + 8 * K) * Q := hQd ▸ H.ĝQ
  have hΘQ : Θ ≤ 3 * K * Q := hQd ▸ H.ΘQ
  have hĝ : dĝ ≤ dg + σ * (4 * K) * Q := hQd ▸ H.hĝ
  have hΘ : Θ ≤ K * dx + σ * K * Q := hQd ▸ H.hΘ
  have hxQ : dx ≤ Q := by have := H.hdg; have := H.hdμ; have := H.hM; linarith
  have hgQ : dg ≤ Q := by have := H.hdx; have := H.hdμ; have := H.hM; linarith
  have hμQ : dμ ≤ Q := by have := H.hdx; have := H.hdg; have := H.hM; linarith
  have hMQ : M ≤ Q := by have := H.hdx; have := H.hdg; have := H.hdμ; linarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hK2 : K ^ 2 ≤ K ^ 3 := by nlinarith
  have hK3 : K ^ 3 ≤ K ^ 4 := by nlinarith
  have h3Q : d3 ≤ (3 * K ^ 2 + 8 * K + 1) * Q := by
    have h3' : d3 ≤ K ^ 2 * dx + dg + σ * (K ^ 2 + 4 * K) * Q := by
      have a1 := mul_le_mul_of_nonneg_left hΘ hK0
      have e1 : K * (K * dx + σ * K * Q) = K ^ 2 * dx + σ * K ^ 2 * Q := by ring
      have e2 : σ * (K ^ 2 + 4 * K) * Q = σ * K ^ 2 * Q + σ * (4 * K) * Q := by ring
      linarith only [h3, a1, e1, e2, hĝ]
    have a1 : K ^ 2 * dx ≤ K ^ 2 * Q := mul_le_mul_of_nonneg_left hxQ (by positivity)
    have a3 : σ * (K ^ 2 + 4 * K) * Q ≤ 2 * (K ^ 2 + 4 * K) * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.hσ2 (by positivity)) hQ
    have e1 : (3 * K ^ 2 + 8 * K + 1) * Q = K ^ 2 * Q + Q + 2 * (K ^ 2 + 4 * K) * Q := by ring
    linarith only [h3', a1, hgQ, a3, e1]
  have hζQ : dζ ≤ 14 * K ^ 2 * Q := by
    have a1 := mul_le_mul_of_nonneg_left hΘQ hK0
    have a2 := mul_le_mul_of_nonneg_left hĝQ hK0
    have a3 : σ * K * M ≤ 2 * K * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_right H.hσ2 hK0) hMQ H.hM (by positivity)
    have a4 : K * Q ≤ K ^ 2 * Q := mul_le_mul_of_nonneg_right hKK hQ
    have e1 : K * (3 * K * Q) = 3 * K ^ 2 * Q := by ring
    have e2 : K * ((1 + 8 * K) * Q) = K * Q + 8 * K ^ 2 * Q := by ring
    linarith only [hζ, a1, a2, a3, a4, e1, e2]
  have hνQ : dν ≤ 14 * K ^ 2 * Q := by
    have h1 : Θ + dμ + dĝ + M ≤ (11 * K + 3) * Q := by
      have e1 : (11 * K + 3) * Q = 3 * K * Q + Q + (1 + 8 * K) * Q + Q := by ring
      linarith only [hΘQ, hμQ, hĝQ, hMQ, e1]
    have a1 := mul_le_mul_of_nonneg_left h1 hK0
    have a4 : K * Q ≤ K ^ 2 * Q := mul_le_mul_of_nonneg_right hKK hQ
    have e1 : K * ((11 * K + 3) * Q) = 11 * K ^ 2 * Q + 3 * (K * Q) := by ring
    linarith only [hν, a1, a4, e1]
  have hwQ : dw ≤ K * Q := hw.trans (mul_le_mul_of_nonneg_left hMQ hK0)
  have hnQ : dn1 ≤ 15 * K ^ 3 * Q := by
    have a1 := mul_le_mul_of_nonneg_left (add_le_add hνQ hwQ) hK0
    have e1 : K * (14 * K ^ 2 * Q + K * Q) = 14 * K ^ 3 * Q + K ^ 2 * Q := by ring
    have a2 : K ^ 2 * Q ≤ K ^ 3 * Q := mul_le_mul_of_nonneg_right hK2 hQ
    linarith only [hn, a1, e1, a2]
  have t1 : 4 * s * d3 ≤ 4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) := by
    have a1 := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)) h3Q h30
      (by positivity)
    linarith only [a1, show 4 * (σ * K) * ((3 * K ^ 2 + 8 * K + 1) * Q) =
      4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) by ring]
  have t2 : B3 * (2 * dn1 + 5 * dζ) ≤ σ * K * ((30 * K ^ 3 + 70 * K ^ 2) * Q) := by
    have a1 : 2 * dn1 + 5 * dζ ≤ (30 * K ^ 3 + 70 * K ^ 2) * Q := by
      have e1 : (30 * K ^ 3 + 70 * K ^ 2) * Q = 2 * (15 * K ^ 3 * Q) + 5 * (14 * K ^ 2 * Q) := by ring
      linarith only [hnQ, hζQ, e1]
    exact mul_le_mul hB3 a1 (by positivity) (by positivity)
  have t3 : dκ ≤ K ^ 2 * dx + σ * K ^ 2 * Q := by
    have a1 := mul_le_mul_of_nonneg_left hΘ hK0
    linarith only [hκ, a1, show K * (K * dx + σ * K * Q) = K ^ 2 * dx + σ * K ^ 2 * Q by ring]
  have hS : σ * K ^ 2 * Q + 4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) +
      σ * K * ((30 * K ^ 3 + 70 * K ^ 2) * Q) + σ * (4 * K) * Q ≤ σ * (200 * K ^ 4) * Q := by
    have h1 : K ^ 2 + 4 * K * (3 * K ^ 2 + 8 * K + 1) + K * (30 * K ^ 3 + 70 * K ^ 2) + 4 * K ≤
        200 * K ^ 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hσ hQ)
    linarith only [this, show σ * K ^ 2 * Q + 4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) +
      σ * K * ((30 * K ^ 3 + 70 * K ^ 2) * Q) + σ * (4 * K) * Q = σ * Q * (K ^ 2 +
        4 * K * (3 * K ^ 2 + 8 * K + 1) + K * (30 * K ^ 3 + 70 * K ^ 2) + 4 * K) by ring,
      show σ * (200 * K ^ 4) * Q = σ * Q * (200 * K ^ 4) by ring]
  have hdx' : K ^ 2 * dx ≤ 100 * K ^ 4 * dx := by
    have : K ^ 2 ≤ 100 * K ^ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right this H.hdx
  have hσx : σ * (200 * K ^ 4) * dx ≤ 400 * K ^ 4 * dx := by
    have hx := H.hdx
    have := mul_le_mul_of_nonneg_right H.hσ2 (by positivity : (0 : ℝ) ≤ 200 * K ^ 4 * dx)
    linarith only [this, show σ * (200 * K ^ 4) * dx = σ * (200 * K ^ 4 * dx) by ring]
  have eQ : σ * (200 * K ^ 4) * Q = σ * (200 * K ^ 4) * dx + σ * (200 * K ^ 4) * dg +
      σ * (200 * K ^ 4) * dμ + σ * (200 * K ^ 4) * M := by rw [hQd]; ring
  linarith only [hG, t1, t2, t3, hĝg, hS, hdx', hσx, eQ]

section Hist

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

/-- `Θ_j` at the final step, from the error bounds. -/
theorem Run.theta_j_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W₁ Z : ℝ} (hM : 0 ≤ M)
    (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M))
    (heW : eWH R j t t' ≤ (e + ε) * W₁ * M) (hew : ewH R j t t' ≤ Z * M) :
    thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') ≤
      (1 + Real.exp 1) * ‖(t' j).2.2 - (t j).2.2‖ + (e + ε) * kTh R.ℓ (cmu Λ cm)
        (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z *
          (|(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) := by
  have HC := H.cmp j le_rfl
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have hcTh : 0 ≤ cTh R.ℓ cw (cx κ cT) := by
    have := HC.hcw; have := HC.hcx
    unfold cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hdn := H.dn_le (le_refl j)
  exact theta_final HC.hℓ HC.hcmu hcTh (by have := H.hKc; positivity) HC.he.le H.he1 H.hε0.le
    HC.hε1 hM hV hZ hW₁ (abs_nonneg _) (abs_nonneg _) hev hew heW
    (eζ_le_ev HC.H HC.H') (evH_nonneg j) (ewH_nonneg j) (norm_nonneg _) (norm_nonneg _) hdn
    hΔ (thetaH_le HC)


/-- **The common pieces at the final step.** -/
theorem pieces_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W₁ Z K : ℝ} (hM : 0 ≤ M)
    (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M))
    (heW : eWH R j t t' ≤ (e + ε) * W₁ * M) (hew : ewH R j t t' ≤ Z * M)
    (hK1 : 1 + Real.exp 1 ≤ K)
    (hK2 : kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z ≤ K)
    (hK3 : 2 * cmu Λ cm * R.ℓ ^ 2 ≤ K) (hK4 : 2 * R.ℓ ^ 2 ≤ K)
    (hK5 : 4 * cmu Λ cm * R.ℓ ^ 2 * V + 3 * cmu Λ cm * Z ≤ K) :
    Pieces K (e + ε) ε ‖(t' j).2.2 - (t j).2.2‖ |(t' j).1 - (t j).1| |(t' j).2.1 - (t j).2.1| M
      ‖ghat (sdH R j t') - ghat (sdH R j t)‖ (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t')) := by
  have HC := H.cmp j le_rfl
  have he := HC.he
  have hε := H.hε0
  have hε1 := HC.hε1
  have hcmu := HC.hcmu
  have hE := (Real.exp_pos 1).le
  have hK0 : 1 ≤ K := by linarith
  set dx := ‖(t' j).2.2 - (t j).2.2‖
  set dg := |(t' j).1 - (t j).1|
  set dμ := |(t' j).2.1 - (t j).2.1|
  have hdx : 0 ≤ dx := norm_nonneg _
  have hdg : 0 ≤ dg := abs_nonneg _
  have hdμ : 0 ≤ dμ := abs_nonneg _
  have hQ : 0 ≤ dx + dg + dμ + M := by linarith
  have hσ : 0 ≤ e + ε := by linarith
  refine ⟨hK0, hσ, by linarith [H.he1], by linarith, hε.le, hdx, hdg, hdμ, hM, ?_, ?_,
    thetaH_nonneg HC, norm_nonneg _⟩
  · have h1 := dĝ_hist H hM hV hZ hev hew
    have h2 : 8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤ 4 * K * (dx + dg + dμ + M) := by
      have b1 : 8 * cmu Λ cm * R.ℓ ^ 2 * dg ≤ 4 * K * dg :=
        mul_le_mul_of_nonneg_right (by linarith) hdg
      have b2 : 8 * R.ℓ ^ 2 * dμ ≤ 4 * K * dμ := mul_le_mul_of_nonneg_right (by linarith) hdμ
      have b3 : (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤ 4 * K * M :=
        mul_le_mul_of_nonneg_right (by have := mul_nonneg hcmu hZ; linarith) hM
      have b4 : 0 ≤ 4 * K * dx := by positivity
      have e1 : 4 * K * (dx + dg + dμ + M) = 4 * K * dx + 4 * K * dg + 4 * K * dμ + 4 * K * M := by ring
      linarith only [b1, b2, b3, b4, e1]
    have h3 : ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) ≤ (e + ε) * (4 * K * (dx + dg + dμ + M)) :=
      mul_le_mul (by linarith) h2 (by positivity) hσ
    have e1 : (e + ε) * (4 * K) * (dx + dg + dμ + M) = (e + ε) * (4 * K * (dx + dg + dμ + M)) := by ring
    linarith only [h1, h3, e1]
  · have h1 := H.theta_j_w hM hV hW₁ hZ hev hΔ heW hew
    have b1 : (1 + Real.exp 1) * dx ≤ K * dx := mul_le_mul_of_nonneg_right hK1 hdx
    have b2 : kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z * (dg + dμ + M) ≤
        K * (dx + dg + dμ + M) :=
      mul_le_mul hK2 (by linarith) (by positivity) (by linarith)
    have b3 := mul_le_mul_of_nonneg_left b2 hσ
    have e1 : (e + ε) * kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z *
        (dg + dμ + M) = (e + ε) * (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8)
          V W₁ Z * (dg + dμ + M)) := by ring
    have e2 : (e + ε) * K * (dx + dg + dμ + M) = (e + ε) * (K * (dx + dg + dμ + M)) := by ring
    linarith only [h1, b1, b3, e1, e2]


/-- The common bound on `δζ₁`. -/
theorem dζ_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (F : FinOne R j t ε b₁ cz cmuv)
    (F' : FinOne R j t' ε b₁ cz cmuv) {M V β K : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4))
    (hK8 : 8 * β ≤ K) (hK9 : 3 * R.ℓ ^ 2 / 16 ≤ K) (hK10 : 4 * (2 * Kc * (L : ℝ) ^ 8) * V ≤ K) :
    ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ ≤ K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
      K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + (e + ε) * K * M := by
  have HC := H.cmp j le_rfl
  have h1 := (dζ_eq_le F F').trans (ev_succ_le HC hkap)
  rw [← hβd] at h1
  have hΘ := thetaH_nonneg HC
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have hg : |(sdH R j t).g| ≤ ε := by
      show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
    linarith
  have hε := H.hε0
  have he := HC.he
  have a1 : 8 * β * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') ≤
      K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := mul_le_mul_of_nonneg_right hK8 hΘ
  have a2 : 3 * (R.ℓ / 4) ^ 2 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤
      K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ :=
    mul_le_mul_of_nonneg_right (by linarith [show 3 * (R.ℓ / 4) ^ 2 = 3 * R.ℓ ^ 2 / 16 by ring])
      (norm_nonneg _)
  have a3 : 3 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ (e + ε) * K * M := by
    have b1 := mul_le_mul (mul_le_mul_of_nonneg_left hĝ (by norm_num : (0 : ℝ) ≤ 3)) hΔ
      (sq_nonneg _) (by positivity)
    have hKc := H.hKc
    have b2 : 3 * (8 / 7 * ε) * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) ≤ ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V * M) := by
      have : 0 ≤ ε * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) := by positivity
      nlinarith
    have b3 : ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V * M) ≤ (e + ε) * K * M := by
      have := mul_le_mul (show ε ≤ e + ε by linarith) hK10 (by positivity) (by linarith)
      have := mul_le_mul_of_nonneg_right this hM
      linarith only [this, show ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V * M) =
        ε * (4 * (2 * Kc * (L : ℝ) ^ 8) * V) * M by ring]
    linarith only [b1, b2, b3]
  linarith only [h1, a1, a2, a3]


/-- The common bound on `δ(ν̃ - L²μ)`. -/
theorem dY_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4)) :
    ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) - (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ ≤
      (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) * M +
        (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ +
        (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
  have HC := H.cmp j le_rfl
  have h1 := dY_le HC (kap_rem_scaled HC hkap)
  rw [← hβd] at h1
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have hg : |(sdH R j t).g| ≤ ε := by
      show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
    linarith
  have hm0 : 0 ≤ |R.msq| * ((L : ℝ) ^ j) ^ 2 := by positivity
  have a1 : 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' ≤
      2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V * M := by
    have := mul_le_mul_of_nonneg_left (hζIH0) (by positivity : (0 : ℝ) ≤ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2))
    linarith only [this, show 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * (V * M) =
      2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V * M by ring]
  have a2 : 2 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ 16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hĝ (by norm_num : (0 : ℝ) ≤ 2)) hΔ
      (sq_nonneg _) (by have := H.hε0; positivity)
    linarith only [this, show 2 * (8 / 7 * ε) * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) =
      16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M by ring]
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  set X := 4 * β * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t')
  set Y := R.ℓ ^ 2 / 8 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖
  have hsum : X + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' + Y +
      2 * ‖ghat (sdH R j t)‖ * lD R Kc j t t' ^ 2 ≤ X + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V * M + Y +
        16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V * M := by linarith only [a1, a2]
  have := mul_le_mul_of_nonneg_left hsum hL2
  refine h1.trans (this.trans (le_of_eq ?_))
  simp only [X, Y]
  ring


/-- The bound on `δŵ_{j+1}`. -/
theorem dw_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) (hew : ewH R j t t' ≤ Z * M) :
    ‖whH R (j + 1) t' - whH R (j + 1) t‖ ≤
      (2 * R.ℓ ^ 2 * V + 2 * Z + 9 * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
  have HC := H.cmp j le_rfl
  have h1 : ewH R (j + 1) t t' ≤ _ := ew_succ_le HC
  have hζIH0 : eζH R j t t' ≤ V * M :=
    (eζ_le_ev (H.cmp j le_rfl).H (H.cmp j le_rfl).H').trans hev
  have h2 := nW1H_sub_le HC.H HC.H' (H.whH_le le_rfl)
  have h3 : ‖nW1H R j t' - nW1H R j t‖ ≤ (2 * R.ℓ ^ 2 * V + 2 * Z) * M := by
    have b1 := mul_le_mul_of_nonneg_left (hζIH0) (by positivity : (0 : ℝ) ≤ 2 * R.ℓ ^ 2)
    have b2 := mul_le_mul_of_nonneg_left hew (by norm_num : (0 : ℝ) ≤ 9 / 8)
    have b3 : 9 / 8 * (Z * M) ≤ 2 * Z * M := by nlinarith [mul_nonneg hZ hM]
    linarith only [h2, b1, b2, b3, show (2 * R.ℓ ^ 2 * V + 2 * Z) * M =
      2 * R.ℓ ^ 2 * (V * M) + 2 * Z * M by ring]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have h4 : ‖nW1H R j t' - nW1H R j t‖ / (L : ℝ) ^ 2 ≤ (2 * R.ℓ ^ 2 * V + 2 * Z) * M :=
    (div_le_self (norm_nonneg _) hL1).trans h3
  show ewH R (j + 1) t t' ≤ _
  linarith only [h1, h4, hΔ, show (2 * R.ℓ ^ 2 * V + 2 * Z + 9 * (2 * Kc * (L : ℝ) ^ 8) * V) * M =
    (2 * R.ℓ ^ 2 * V + 2 * Z) * M + 9 * (2 * Kc * (L : ℝ) ^ 8 * (V * M)) by ring]



set_option maxHeartbeats 1000000 in
/-- **(LT) along two histories.** -/
theorem LT_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (hval : ∀ i ≤ j, ValidAt R i)
    {M V W₁ Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z)
    (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) (heW : eWH R j t t' ≤ (e + ε) * W₁ * M)
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
  have hΘ := H.theta_j_w hM hV hW₁ hZ hev hΔ heW hew
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
      have hζ := (eζ_le_ev HC.H HC.H').trans hev
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


/-- **`|δĝ - δg|`.** -/
theorem dĝd_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M) (hew : ewH R j t t' ≤ Z * M) :
    ‖(ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)‖ ≤
      ε * (8 * cmu Λ cm * R.ℓ ^ 2 * |(t' j).1 - (t j).1| + 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by
  have HC := H.cmp j le_rfl
  have hτ := ghat_nCor_le H
  have h1 := ghat_sub_sub_le (sdH R j t) (sdH R j t') (le_refl _)
    ((norm_nCor_le _ _).trans (by norm_num))
  have hg : |(sdH R j t).g| ≤ ε := by
    show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
  have hdn := H.dn_le (le_refl j)
  have hζ := (eζ_le_ev HC.H HC.H').trans hev
  have hε := H.hε0
  have hε1 := HC.hε1
  have hcmu := HC.hcmu
  have hℓ := HC.hℓ
  set dg := |(t' j).1 - (t j).1|
  set dμ := |(t' j).2.1 - (t j).2.1|
  set dn := ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t') - nCor ((t j).2.1 : ℂ) (nW1H R j t)‖
  have hdg : 0 ≤ dg := abs_nonneg _
  have hdn0 : 0 ≤ dn := norm_nonneg _
  have a1 : 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ * dg ≤ ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg) := by
    have := mul_le_mul_of_nonneg_right hτ hdg
    nlinarith
  have a2 : 2 * |(sdH R j t).g| * dn ≤ 2 * ε * dn := by
    have := mul_le_mul_of_nonneg_right hg hdn0
    linarith
  have a3 : dn ≤ 4 * R.ℓ ^ 2 * dμ + (8 * cmu Λ cm * R.ℓ ^ 2 * V + 9 / 2 * cmu Λ cm * Z) * M := by
    have b1 : cmu Λ cm * ε * (2 * R.ℓ ^ 2 * eζH R j t t' + 9 / 8 * ewH R j t t') ≤
        cmu Λ cm * 1 * (2 * R.ℓ ^ 2 * (V * M) + 9 / 8 * (Z * M)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hε1 hcmu)
        (add_le_add (mul_le_mul_of_nonneg_left hζ (by positivity))
          (mul_le_mul_of_nonneg_left hew (by norm_num)))
        (by have := norm_nonneg (zetaH R j t' - zetaH R j t); have := ewH_nonneg (R := R)
                (t := t) (t' := t') j; unfold eζH; positivity) (by positivity)
    have e1 : 4 * (R.ℓ ^ 2 * dμ + cmu Λ cm * 1 * (2 * R.ℓ ^ 2 * (V * M) + 9 / 8 * (Z * M))) =
        4 * R.ℓ ^ 2 * dμ + (8 * cmu Λ cm * R.ℓ ^ 2 * V + 9 / 2 * cmu Λ cm * Z) * M := by ring
    linarith only [hdn, b1, e1]
  have a4 : 2 * ε * dn ≤ ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by
    have := mul_le_mul_of_nonneg_left a3 (by positivity : (0 : ℝ) ≤ 2 * ε)
    have e1 : 2 * ε * (4 * R.ℓ ^ 2 * dμ + (8 * cmu Λ cm * R.ℓ ^ 2 * V + 9 / 2 * cmu Λ cm * Z) * M) =
        ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by ring
    linarith only [this, e1]
  have e3 : ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
      (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) = ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg) +
      ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by ring
  have h1' : ‖(ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)‖ ≤
      2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ * dg + 2 * |(sdH R j t).g| * dn := h1
  linarith only [h1', a1, a2, a4, e3]

/-- **`G_j - ǧ_j` through the normalised outputs.** -/
theorem G_core_d (HO : HistOK R j t) (HO' : HistOK R j t') {s : ℝ} (hs : s ≤ 1 / 16)
    (hζ : ‖zetaH R (j + 1) t‖ ≤ s) (hζ' : ‖zetaH R (j + 1) t'‖ ≤ s)
    (hn : ‖nCor (nuT R j t) (whH R (j + 1) t)‖ ≤ s)
    (hn' : ‖nCor (nuT R j t') (whH R (j + 1) t')‖ ≤ s) :
    |(rgData R).G j t - (rgData R).G j t' - ((t j).1 - (t' j).1)| ≤
      4 * s * ‖kapH R j t' 3 - kapH R j t 3‖ +
      ‖kapH R j t 3‖ * (2 * ‖nCor (nuT R j t') (whH R (j + 1) t') -
        nCor (nuT R j t) (whH R (j + 1) t)‖ + 5 * ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖) +
      ‖(kapH R j t' 3 - kapH R j t 3) - (ghat (sdH R j t') - ghat (sdH R j t))‖ +
      ‖(ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)‖ := by
  have h := G_lip_d (a := kapH R j t 3) (a' := kapH R j t' 3) hs hζ hζ' hn hn'
  show |(histOut R j t).g.re - (histOut R j t').g.re - ((t j).1 - (t' j).1)| ≤ _
  rw [histOut_g_norm HO, histOut_g_norm HO', nCor_out, nCor_out]
  set X := kapH R j t' 3 / (1 + zetaH R (j + 1) t') ^ 2 * (1 + nCor (nuT R j t') (whH R (j + 1) t')) -
    kapH R j t 3 / (1 + zetaH R (j + 1) t) ^ 2 * (1 + nCor (nuT R j t) (whH R (j + 1) t)) with hX
  have e : (kapH R j t 3 / (1 + zetaH R (j + 1) t) ^ 2 * (1 + nCor (nuT R j t) (whH R (j + 1) t))).re -
      (kapH R j t' 3 / (1 + zetaH R (j + 1) t') ^ 2 * (1 + nCor (nuT R j t') (whH R (j + 1) t'))).re -
      ((t j).1 - (t' j).1) = -((X - (((t' j).1 - (t j).1 : ℝ) : ℂ)).re) := by
    rw [hX, Complex.sub_re, Complex.sub_re, Complex.ofReal_re]; ring
  rw [e, abs_neg]
  refine (Complex.abs_re_le_norm _).trans ?_
  have e2 : X - (((t' j).1 - (t j).1 : ℝ) : ℂ) = (X - (kapH R j t' 3 - kapH R j t 3)) +
      ((kapH R j t' 3 - kapH R j t 3) - (ghat (sdH R j t') - ghat (sdH R j t))) +
      ((ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)) := by ring
  rw [e2]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h le_rfl)) le_rfl)

set_option maxHeartbeats 1000000 in
/-- **(LG), difference form, along two histories.** -/
theorem LGd_hist_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {b₁ : ℝ}
    (F : FinOne R j t ε b₁ cz (cmu Λ cm)) (F' : FinOne R j t' ε b₁ cz (cmu Λ cm))
    {M V W₁ Z β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hβ : 0 ≤ β)
    (hb : 0 ≤ b₁) (hev : evH R j t t' ≤ V * M)
    (hΔ : lD R Kc j t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) (heW : eWH R j t t' ≤ (e + ε) * W₁ * M)
    (hew : ewH R j t t' ≤ Z * M) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4))
    (hs16 : ε * (cSz b₁ R.ℓ + cSn L b₁ cz R.ℓ (cmu Λ cm)) ≤ 1 / 16) :
    let K := cKa L β b₁ R.ℓ (cmu Λ cm) cz V Z (2 * Kc * (L : ℝ) ^ 8)
      (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z)
    |(rgData R).G j t - (rgData R).G j t' - ((t j).1 - (t' j).1)| ≤
      (e + ε) * (200 * K ^ 4) * |(t' j).1 - (t j).1| +
      (e + ε) * (200 * K ^ 4) * |(t' j).2.1 - (t j).2.1| + 500 * K ^ 4 * ‖(t' j).2.2 - (t j).2.2‖ +
      (e + ε) * (200 * K ^ 4) * M := by
  intro K
  have HC := H.cmp j le_rfl
  have hε := H.hε0
  have hε1 := HC.hε1
  have he := HC.he
  have hcmu := HC.hcmu
  have hcz := HC.H.hcz
  have hKc := H.hKc
  have hkTh : 0 ≤ kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z := by
    have := HC.hcw; have := HC.hcx
    unfold kTh cTh; have := kX_nonneg R.ℓ; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, -, -, -, -, -, k20⟩ :=
    cKa_ge (β := β) (b₁ := b₁) (ℓ := R.ℓ) (cmu := cmu Λ cm) (cz := cz) (V := V) (Z := Z)
      (Λ0 := 2 * Kc * (L : ℝ) ^ 8) (kThv := kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT))
        (2 * Kc * (L : ℝ) ^ 8) V W₁ Z) L hβ hb hcmu hcz hV hZ (by positivity) hkTh
  have P := pieces_hist_w H hM hV hW₁ hZ hev hΔ heW hew k1 k2 k3 k4 k5
  set σ := e + ε
  set s := ε * (cSz b₁ R.ℓ + cSn L b₁ cz R.ℓ (cmu Λ cm))
  have hp1 : 0 ≤ cSz b₁ R.ℓ := by unfold cSz; positivity
  have hp4 : 0 ≤ cSn L b₁ cz R.ℓ (cmu Λ cm) := by
    unfold cSn cSν cSY; positivity
  have hs0 : 0 ≤ s := by positivity
  have hsz : ∀ {x : ℝ}, x ≤ ε * cSz b₁ R.ℓ → x ≤ s := fun h => h.trans (by
    have := mul_nonneg hε.le hp4
    linarith only [this, show s = ε * cSz b₁ R.ℓ + ε * cSn L b₁ cz R.ℓ (cmu Λ cm) by ring])
  have hsn : ∀ {x : ℝ}, x ≤ ε * cSn L b₁ cz R.ℓ (cmu Λ cm) → x ≤ s := fun h => h.trans (by
    have := mul_nonneg hε.le hp1
    linarith only [this, show s = ε * cSz b₁ R.ℓ + ε * cSn L b₁ cz R.ℓ (cmu Λ cm) by ring])
  have hG := G_core_d F.hO F'.hO hs16 (hsz F.ζ_le) (hsz F'.ζ_le) (hsn F.n_le) (hsn F'.n_le)
  have h3 := d3_le HC (kap_rem_scaled HC hkap)
  rw [← hβd] at h3
  have hζ := dζ_hist_w H F F' hM hV hev hΔ hβd hkap k8 k9 k10
  have hY := dY_hist_w H hM hV hev hΔ hβd hkap
  have hw := dw_hist_w H hM hV hZ hev hΔ hew
  -- `dν`
  have hν : ‖nuT R j t' - nuT R j t‖ ≤ K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
      |(t' j).2.1 - (t j).2.1| + ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + M) := by
    have e1 : nuT R j t' - nuT R j t = ((nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))) + (L : ℂ) ^ 2 * (((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) := by
      push_cast; ring
    have h1 := norm_add_le ((nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))) ((L : ℂ) ^ 2 * (((t' j).2.1 - (t j).2.1 : ℝ) : ℂ))
    rw [← e1] at h1
    have hLμ : ‖(L : ℂ) ^ 2 * (((t' j).2.1 - (t j).2.1 : ℝ) : ℂ)‖ = (L : ℝ) ^ 2 * |(t' j).2.1 - (t j).2.1| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [hLμ] at h1
    have hm1 := HC.hm
    have hΘ := thetaH_nonneg HC
    have hdĝ := norm_nonneg (ghat (sdH R j t') - ghat (sdH R j t))
    have hdμ := abs_nonneg ((t' j).2.1 - (t j).2.1)
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have c1 : (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) * M ≤ (L : ℝ) ^ 2 * (2 * V) * M := by
      have a := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 2 * V)
      have b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a hL2) hM
      have e1 : (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) * M =
          (L : ℝ) ^ 2 * (2 * V * (|R.msq| * ((L : ℝ) ^ j) ^ 2)) * M := by ring
      have e2 : (L : ℝ) ^ 2 * (2 * V) * M = (L : ℝ) ^ 2 * (2 * V * 1) * M := by ring
      linarith only [b, e1, e2]
    have c2 : (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) * M ≤
        (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
      have : 16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V ≤ 3 * (2 * Kc * (L : ℝ) ^ 8) * V := by
        have h0 : 0 ≤ (2 * Kc * (L : ℝ) ^ 8) * V := by positivity
        have := mul_le_mul_of_nonneg_right hε1 h0
        linarith only [this, h0, show 16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V =
          16 / 7 * (ε * ((2 * Kc * (L : ℝ) ^ 8) * V)) by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hL2) hM
    have e2 : K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') + |(t' j).2.1 - (t j).2.1| +
        ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + M) = K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        K * |(t' j).2.1 - (t j).2.1| + K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ + K * M := by ring
    have d1 : (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') ≤
        K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := by
      refine mul_le_mul_of_nonneg_right ?_ hΘ
      have : 0 ≤ (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (4 * β) +
        (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d2 : (L : ℝ) ^ 2 * |(t' j).2.1 - (t j).2.1| ≤ K * |(t' j).2.1 - (t j).2.1| := by
      refine mul_le_mul_of_nonneg_right ?_ hdμ
      have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 +
        (L : ℝ) ^ 2 * (4 * β + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d3 : (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤
        K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
      refine mul_le_mul_of_nonneg_right ?_ hdĝ
      have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) +
        (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d4 : (L : ℝ) ^ 2 * (2 * V) * M + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) * M ≤ K * M := by
      have h0 : (L : ℝ) ^ 2 * (2 * V) + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) ≤ K := by
        have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8) := by positivity
        linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
          3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8) +
          ((L : ℝ) ^ 2 * (2 * V) + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V)) by ring]
      have := mul_le_mul_of_nonneg_right h0 hM
      linarith only [this, show ((L : ℝ) ^ 2 * (2 * V) + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V)) * M
        = (L : ℝ) ^ 2 * (2 * V) * M + (L : ℝ) ^ 2 * (3 * (2 * Kc * (L : ℝ) ^ 8) * V) * M by ring]
    linarith only [h1, hY, c1, c2, e2, d1, d2, d3, d4]
  -- `dn₁`
  have hn : ‖nCor (nuT R j t') (whH R (j + 1) t') - nCor (nuT R j t) (whH R (j + 1) t)‖ ≤
      K * (‖nuT R j t' - nuT R j t‖ + ‖whH R (j + 1) t' - whH R (j + 1) t‖) := by
    have h1 := nCor_sub_le' F'.ν F.w F.nd F'.nd
    have hp3 : 0 ≤ cSν L b₁ cz R.ℓ (cmu Λ cm) := by unfold cSν cSY; positivity
    have b1 : 4 * (R.ℓ ^ 2 * ‖nuT R j t' - nuT R j t‖) ≤ K * ‖nuT R j t' - nuT R j t‖ := by
      have := mul_le_mul_of_nonneg_right k13 (norm_nonneg (nuT R j t' - nuT R j t))
      linarith only [this, show 4 * (R.ℓ ^ 2 * ‖nuT R j t' - nuT R j t‖) =
        4 * R.ℓ ^ 2 * ‖nuT R j t' - nuT R j t‖ by ring]
    have b2 : 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm) * ‖whH R (j + 1) t' - whH R (j + 1) t‖) ≤
        K * ‖whH R (j + 1) t' - whH R (j + 1) t‖ := by
      have h0 : 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) ≤ K := by
        have := mul_le_mul_of_nonneg_right hε1 hp3
        linarith only [k14, this, show 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) =
          4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) by ring]
      have := mul_le_mul_of_nonneg_right h0 (norm_nonneg (whH R (j + 1) t' - whH R (j + 1) t))
      linarith only [this, show 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm) *
        ‖whH R (j + 1) t' - whH R (j + 1) t‖) = 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm)) *
        ‖whH R (j + 1) t' - whH R (j + 1) t‖ by ring]
    linarith only [h1, b1, b2]
  have hB3 : ‖kapH R j t 3‖ ≤ σ * K := F.κ3.trans (by
    have h0 : 0 ≤ cS3 b₁ := by unfold cS3; positivity
    exact mul_le_mul (by linarith) k7 h0 (by linarith))
  have hsK : s ≤ σ * K := mul_le_mul (by linarith) k6 (by positivity) (by linarith)
  have hwK : ‖whH R (j + 1) t' - whH R (j + 1) t‖ ≤ K * M :=
    hw.trans (mul_le_mul_of_nonneg_right k12 hM)
  have h3K : ‖kapH R j t' 3 - kapH R j t 3‖ ≤ K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
      ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
    have : 4 * β ≤ K := by linarith
    have := mul_le_mul_of_nonneg_right this (thetaH_nonneg HC)
    linarith
  -- the difference parts
  have hκĝ : ‖(kapH R j t' 3 - kapH R j t 3) - (ghat (sdH R j t') - ghat (sdH R j t))‖ ≤
      K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := by
    have hk3 := kap_rem_scaled HC hkap 3
    rw [show cwt L j 3 = 1 from rfl, one_mul,
      shv3_sub R j (sdH R j t) (sdH R j t') HC.sOK.hzy HC.sOK.hy HC.sOK'.hzy HC.sOK'.hy,
      ← hβd] at hk3
    have : 4 * β ≤ K := by linarith
    exact hk3.trans (mul_le_mul_of_nonneg_right this (thetaH_nonneg HC))
  have hĝg := dĝd_hist H hM hV hZ hev hew
  have hĝg' : ‖(ghat (sdH R j t') - ghat (sdH R j t)) - (((t' j).1 - (t j).1 : ℝ) : ℂ)‖ ≤
      σ * (4 * K) * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) := by
    have hdx := norm_nonneg ((t' j).2.2 - (t j).2.2)
    have hdg := abs_nonneg ((t' j).1 - (t j).1)
    have hdμ := abs_nonneg ((t' j).2.1 - (t j).2.1)
    have b1 : 8 * cmu Λ cm * R.ℓ ^ 2 * |(t' j).1 - (t j).1| ≤ 4 * K * |(t' j).1 - (t j).1| :=
      mul_le_mul_of_nonneg_right (by linarith) hdg
    have b2 : 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| ≤ 4 * K * |(t' j).2.1 - (t j).2.1| :=
      mul_le_mul_of_nonneg_right (by linarith) hdμ
    have b3 : (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤ 4 * K * M :=
      mul_le_mul_of_nonneg_right (by have := mul_nonneg hcmu hZ; linarith) hM
    have b4 : 0 ≤ 4 * K * ‖(t' j).2.2 - (t j).2.2‖ := by positivity
    have h2 : 8 * cmu Λ cm * R.ℓ ^ 2 * |(t' j).1 - (t j).1| + 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M ≤
        4 * K * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M) := by
      linarith only [b1, b2, b3, b4, show 4 * K * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| +
        |(t' j).2.1 - (t j).2.1| + M) = 4 * K * ‖(t' j).2.2 - (t j).2.2‖ +
        4 * K * |(t' j).1 - (t j).1| + 4 * K * |(t' j).2.1 - (t j).2.1| + 4 * K * M by ring]
    have h3 := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) h2 (by positivity)
      (by simp only [σ]; linarith)
    linarith only [hĝg, h3, show σ * (4 * K) * (‖(t' j).2.2 - (t j).2.2‖ + |(t' j).1 - (t j).1| +
      |(t' j).2.1 - (t j).2.1| + M) = σ * (4 * K * (‖(t' j).2.2 - (t j).2.2‖ +
      |(t' j).1 - (t j).1| + |(t' j).2.1 - (t j).2.1| + M)) by ring]
  exact G_assemble_d P hsK hs0 hB3 (norm_nonneg _) h3K hζ hν hwK hn (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hκĝ hĝg' hG


end Hist

end

end Step2
