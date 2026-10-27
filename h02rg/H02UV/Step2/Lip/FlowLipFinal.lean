import Step2.Lip.FlowLipGH3

/-!
# The final step: (LG) and (Lm) along two histories (Lipschitz bounds, part 30)

The pieces of `G_assemble` and `m_assemble` from the history: `pieces_hist` (`|δĝ|`, `Θ_j`),
`dζ_hist`, `dν_hist`, `dw_hist`, `dn_hist`; then `LG_hist` and `Lm_hist`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- The size constants. -/
def cSz (b₁ ℓ : ℝ) : ℝ := 2 * b₁ + ℓ ^ 2 / 4
def cS3 (b₁ : ℝ) : ℝ := b₁ + 2
def cSY (L : ℕ) (b₁ cz ℓ : ℝ) : ℝ := (L : ℝ) ^ 2 * (b₁ + 3 * cz + ℓ ^ 2 / 7)
def cSν (L : ℕ) (b₁ cz ℓ cmu : ℝ) : ℝ := cSY L b₁ cz ℓ + (L : ℝ) ^ 2 * cmu
def cSn (L : ℕ) (b₁ cz ℓ cmu : ℝ) : ℝ := 4 * cSν L b₁ cz ℓ cmu * ℓ ^ 2

/-- The constant `K` of the assembly. -/
def cKa (L : ℕ) (β b₁ ℓ cmu cz V Z Λ0 kThv : ℝ) : ℝ :=
  1 + (1 + Real.exp 1) + kThv + 2 * cmu * ℓ ^ 2 + 2 * ℓ ^ 2 + (4 * cmu * ℓ ^ 2 * V + 3 * cmu * Z) +
    (cSz b₁ ℓ + cSn L b₁ cz ℓ cmu) + cS3 b₁ + 8 * β + 3 * ℓ ^ 2 / 16 + 4 * Λ0 * V +
    (L : ℝ) ^ 2 * (4 * β + 1 + ℓ ^ 2 / 8 + 2 * V + 3 * Λ0 * V) + (2 * ℓ ^ 2 * V + 2 * Z + 9 * Λ0 * V) +
    4 * ℓ ^ 2 + 4 * cSν L b₁ cz ℓ cmu + (cSY L b₁ cz ℓ + (L : ℝ) ^ 2 * cmu * cSz b₁ ℓ) + 2 * V +
    3 * (L : ℝ) ^ 2 * Λ0 * V + (L : ℝ) ^ 2 * cSz b₁ ℓ + (L : ℝ) ^ 2 * cmu

section KC

variable {β b₁ ℓ cmu cz V Z Λ0 kThv : ℝ}

/-- The requirements on `K = cKa`. -/
theorem cKa_ge (L : ℕ) (hβ : 0 ≤ β) (hb : 0 ≤ b₁) (hcmu : 0 ≤ cmu) (hcz : 0 ≤ cz) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hΛ : 0 ≤ Λ0) (hk : 0 ≤ kThv) :
    let K := cKa L β b₁ ℓ cmu cz V Z Λ0 kThv
    1 + Real.exp 1 ≤ K ∧ kThv ≤ K ∧ 2 * cmu * ℓ ^ 2 ≤ K ∧ 2 * ℓ ^ 2 ≤ K ∧
      4 * cmu * ℓ ^ 2 * V + 3 * cmu * Z ≤ K ∧ cSz b₁ ℓ + cSn L b₁ cz ℓ cmu ≤ K ∧ cS3 b₁ ≤ K ∧
      8 * β ≤ K ∧ 3 * ℓ ^ 2 / 16 ≤ K ∧ 4 * Λ0 * V ≤ K ∧
      (L : ℝ) ^ 2 * (4 * β + 1 + ℓ ^ 2 / 8 + 2 * V + 3 * Λ0 * V) ≤ K ∧
      2 * ℓ ^ 2 * V + 2 * Z + 9 * Λ0 * V ≤ K ∧ 4 * ℓ ^ 2 ≤ K ∧ 4 * cSν L b₁ cz ℓ cmu ≤ K ∧
      cSY L b₁ cz ℓ + (L : ℝ) ^ 2 * cmu * cSz b₁ ℓ ≤ K ∧ 2 * V ≤ K ∧
      3 * (L : ℝ) ^ 2 * Λ0 * V ≤ K ∧ (L : ℝ) ^ 2 * cSz b₁ ℓ ≤ K ∧ (L : ℝ) ^ 2 * cmu ≤ K ∧ 1 ≤ K := by
  intro K
  have hE := (Real.exp_pos 1).le
  have p1 : 0 ≤ cSz b₁ ℓ := by unfold cSz; positivity
  have p2 : 0 ≤ cSY L b₁ cz ℓ := by unfold cSY; positivity
  have p3 : 0 ≤ cSν L b₁ cz ℓ cmu := by unfold cSν; positivity
  have p4 : 0 ≤ cSn L b₁ cz ℓ cmu := by unfold cSn; positivity
  have p5 : 0 ≤ cS3 b₁ := by unfold cS3; positivity
  have q1 : 0 ≤ 2 * cmu * ℓ ^ 2 := by positivity
  have q2 : 0 ≤ 2 * ℓ ^ 2 := by positivity
  have q3 : 0 ≤ 4 * cmu * ℓ ^ 2 * V + 3 * cmu * Z := by positivity
  have q4 : 0 ≤ 8 * β := by positivity
  have q5 : 0 ≤ 3 * ℓ ^ 2 / 16 := by positivity
  have q6 : 0 ≤ 4 * Λ0 * V := by positivity
  have q7 : 0 ≤ (L : ℝ) ^ 2 * (4 * β + 1 + ℓ ^ 2 / 8 + 2 * V + 3 * Λ0 * V) := by positivity
  have q8 : 0 ≤ 2 * ℓ ^ 2 * V + 2 * Z + 9 * Λ0 * V := by positivity
  have q9 : 0 ≤ 4 * ℓ ^ 2 := by positivity
  have q10 : 0 ≤ (L : ℝ) ^ 2 * cmu * cSz b₁ ℓ := by positivity
  have q11 : 0 ≤ 2 * V := by positivity
  have q12 : 0 ≤ 3 * (L : ℝ) ^ 2 * Λ0 * V := by positivity
  have q13 : 0 ≤ (L : ℝ) ^ 2 * cSz b₁ ℓ := by positivity
  have q14 : 0 ≤ (L : ℝ) ^ 2 * cmu := by positivity
  have hKd : K = 1 + (1 + Real.exp 1) + kThv + 2 * cmu * ℓ ^ 2 + 2 * ℓ ^ 2 +
      (4 * cmu * ℓ ^ 2 * V + 3 * cmu * Z) + (cSz b₁ ℓ + cSn L b₁ cz ℓ cmu) + cS3 b₁ + 8 * β +
      3 * ℓ ^ 2 / 16 + 4 * Λ0 * V + (L : ℝ) ^ 2 * (4 * β + 1 + ℓ ^ 2 / 8 + 2 * V + 3 * Λ0 * V) +
      (2 * ℓ ^ 2 * V + 2 * Z + 9 * Λ0 * V) + 4 * ℓ ^ 2 + 4 * cSν L b₁ cz ℓ cmu +
      (cSY L b₁ cz ℓ + (L : ℝ) ^ 2 * cmu * cSz b₁ ℓ) + 2 * V + 3 * (L : ℝ) ^ 2 * Λ0 * V +
      (L : ℝ) ^ 2 * cSz b₁ ℓ + (L : ℝ) ^ 2 * cmu := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hKd] <;> linarith

end KC

section Hist

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

theorem ghat_nCor_le (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) :
    ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ ≤ 4 * cmu Λ cm * ε * R.ℓ ^ 2 := by
  have HC := H.cmp j le_rfl
  rw [nCor_dom (H.nd j le_rfl).2, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show ‖(4 : ℂ)‖ = 4 by norm_num]
  have hμ : |(t' j).2.1| ≤ cmu Λ cm * ε :=
    HC.H'.hD.2.2.1.trans (mul_le_mul_of_nonneg_left HC.H'.g_le HC.hcmu)
  have := mul_le_mul hμ (H.nW j le_rfl).2 (norm_nonneg _) (by have := HC.hcmu; have := H.hε0; positivity)
  nlinarith

/-- **`|δĝ|`.** -/
theorem dĝ_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hev : evH R j t t' ≤ V * M) (hew : ewH R j t t' ≤ Z * M) :
    ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤ |(t' j).1 - (t j).1| + ε * (8 * cmu Λ cm * R.ℓ ^ 2 *
      |(t' j).1 - (t j).1| + 8 * R.ℓ ^ 2 * |(t' j).2.1 - (t j).2.1| +
        (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by
  have HC := H.cmp j le_rfl
  have hτ := ghat_nCor_le H
  have h1 := ghat_sub_le' (sdH R j t) (sdH R j t') (le_refl _)
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
  have e2 : (1 + 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖) * dg =
      dg + 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖ * dg := by ring
  have e3 : ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg + 8 * R.ℓ ^ 2 * dμ +
      (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) = ε * (8 * cmu Λ cm * R.ℓ ^ 2 * dg) +
      ε * (8 * R.ℓ ^ 2 * dμ + (16 * cmu Λ cm * R.ℓ ^ 2 * V + 9 * cmu Λ cm * Z) * M) := by ring
  have h1' : ‖ghat (sdH R j t') - ghat (sdH R j t)‖ ≤
      (1 + 2 * ‖nCor ((t' j).2.1 : ℂ) (nW1H R j t')‖) * dg + 2 * |(sdH R j t).g| * dn := h1
  linarith only [h1', e2, a1, a2, a4, e3]

/-- **The common pieces at the final step.** -/
theorem pieces_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W₁ Z K : ℝ} (hM : 0 ≤ M)
    (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hev : ∀ i ≤ j, evH R i t t' ≤ V * M)
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
  · have h1 := dĝ_hist H hM hV hZ (hev j le_rfl) hew
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
  · have h1 := H.theta_j hM hV hW₁ hZ hev heW hew
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

/-- The final-step facts for one history. -/
structure FinOne (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (j : ℕ) (t : Hist.Seq (Xs R))
    (ε b₁ cz cmuv : ℝ) : Prop where
  hO : HistOK R j t
  ζ_eq : zetaH R (j + 1) t = kapH R j t 0 + kapH R j t 1
  ζ_le : ‖zetaH R (j + 1) t‖ ≤ ε * cSz b₁ R.ℓ
  κ3 : ‖kapH R j t 3‖ ≤ ε * cS3 b₁
  Y : ‖nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)‖ ≤ ε * cSY L b₁ cz R.ℓ
  ν : ‖nuT R j t‖ ≤ ε * cSν L b₁ cz R.ℓ cmuv
  w : ‖whH R (j + 1) t‖ ≤ R.ℓ ^ 2
  nd : ‖4 * nuT R j t * whH R (j + 1) t‖ ≤ 1 / 8
  n_le : ‖nCor (nuT R j t) (whH R (j + 1) t)‖ ≤ ε * cSn L b₁ cz R.ℓ cmuv
  μ : |(t j).2.1| ≤ cmuv * ε

/-- **The final-step facts from the sizes.** -/
theorem finOne_of (HD : DomH j t Λ κ cm cT ε cz cw) {Cq Cl cS : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hε1 : ε ≤ 1)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (hL2 : 2 ≤ L) (hnW : ‖nW1H R j t‖ ≤ R.ℓ ^ 2)
    (hrem : ∀ i : Fin 4, cwt L j i * ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t j).1 ^ 3)))
    (hsmall : ε * cSz (bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) R.ℓ ≤ R.ρ)
    (hsmall2 : ε * cSn L (bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) cz
      R.ℓ (cmu Λ cm) ≤ 1 / 8) :
    FinOne R j t ε (bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)) cz
      (cmu Λ cm) := by
  obtain ⟨s01, s3, sY, -⟩ := HD.sizes hCq hCl hcS hcw hcx hcmu hε1 hm hrem
  set b₁ := bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)
  have HO := HD.histOK
  have hε : 0 ≤ ε := HD.g_pos.le.trans HD.g_le
  have hz : ‖kapH R j t 0 + kapH R j t 1‖ ≤ ε * cSz b₁ R.ℓ :=
    (norm_add_le _ _).trans (by unfold cSz; exact s01)
  have hζ := zeta1_eq HO (hz.trans hsmall)
  have hμ : |(t j).2.1| ≤ cmu Λ cm * ε :=
    HD.hD.2.2.1.trans (mul_le_mul_of_nonneg_left HD.g_le hcmu)
  have hν : ‖nuT R j t‖ ≤ ε * cSν L b₁ cz R.ℓ (cmu Λ cm) := by
    have h1 := norm_add_le (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)) ((L : ℂ) ^ 2 * ((t j).2.1 : ℂ))
    rw [sub_add_cancel] at h1
    have hLμ : ‖(L : ℂ) ^ 2 * ((t j).2.1 : ℂ)‖ = (L : ℝ) ^ 2 * |(t j).2.1| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [hLμ] at h1
    have h2 := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    unfold cSν
    have e1 : ε * (cSY L b₁ cz R.ℓ + (L : ℝ) ^ 2 * cmu Λ cm) =
        ε * cSY L b₁ cz R.ℓ + (L : ℝ) ^ 2 * (cmu Λ cm * ε) := by ring
    unfold cSY at e1 ⊢
    linarith only [h1, sY, h2, e1]
  have hw := HD.whH_succ_le hL2 hnW
  have hn4 : ‖4 * nuT R j t * whH R (j + 1) t‖ ≤ ε * cSn L b₁ cz R.ℓ (cmu Λ cm) := by
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have := mul_le_mul hν hw (norm_nonneg _) ((norm_nonneg _).trans hν)
    unfold cSn
    linarith only [this, show 4 * (ε * cSν L b₁ cz R.ℓ (cmu Λ cm) * R.ℓ ^ 2) =
      ε * (4 * cSν L b₁ cz R.ℓ (cmu Λ cm) * R.ℓ ^ 2) by ring]
  refine ⟨HO, hζ, by rw [hζ]; exact hz, ?_, by unfold cSY; exact sY, hν, hw,
    hn4.trans hsmall2, ?_, hμ⟩
  · unfold cS3; exact s3
  · rw [nCor_dom (hn4.trans hsmall2)]; exact hn4

/-- `ζ₁` differences are coupling differences. -/
theorem dζ_eq_le (F : FinOne R j t ε b₁ cz cmuv) (F' : FinOne R j t' ε b₁ cz cmuv) :
    ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ ≤ evH R (j + 1) t t' := by
  rw [F.ζ_eq, F'.ζ_eq, evH, zhH_succ F.hO, zhH_succ F'.hO, yhH_succ F.hO, yhH_succ F'.hO]
  have e : kapH R j t' 0 + kapH R j t' 1 - (kapH R j t 0 + kapH R j t 1) =
      (kapH R j t' 0 - kapH R j t 0) + (kapH R j t' 1 - kapH R j t 1) := by ring
  rw [e]; exact norm_add_le _ _

/-- The common bound on `δζ₁`. -/
theorem dζ_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) (F : FinOne R j t ε b₁ cz cmuv)
    (F' : FinOne R j t' ε b₁ cz cmuv) {M V β K : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : ∀ i ≤ j, evH R i t t' ≤ V * M) {Cq Cl cS : ℝ}
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
  have hζIH : ∀ i ≤ j, eζH R i t t' ≤ V * M := fun i hi =>
    (eζ_le_ev (H.cmp i hi).H (H.cmp i hi).H').trans (hev i hi)
  have hΔ := lD_sq_le H.hKc j t t' hζIH
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
theorem dY_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : ∀ i ≤ j, evH R i t t' ≤ V * M) {Cq Cl cS : ℝ}
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
  have hζIH : ∀ i ≤ j, eζH R i t t' ≤ V * M := fun i hi =>
    (eζ_le_ev (H.cmp i hi).H (H.cmp i hi).H').trans (hev i hi)
  have hΔ := lD_sq_le H.hKc j t t' hζIH
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have hg : |(sdH R j t).g| ≤ ε := by
      show |(t j).1| ≤ ε; rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
    linarith
  have hm0 : 0 ≤ |R.msq| * ((L : ℝ) ^ j) ^ 2 := by positivity
  have a1 : 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' ≤
      2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V * M := by
    have := mul_le_mul_of_nonneg_left (hζIH j le_rfl) (by positivity : (0 : ℝ) ≤ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2))
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
theorem dw_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V Z : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hev : ∀ i ≤ j, evH R i t t' ≤ V * M) (hew : ewH R j t t' ≤ Z * M) :
    ‖whH R (j + 1) t' - whH R (j + 1) t‖ ≤
      (2 * R.ℓ ^ 2 * V + 2 * Z + 9 * (2 * Kc * (L : ℝ) ^ 8) * V) * M := by
  have HC := H.cmp j le_rfl
  have h1 : ewH R (j + 1) t t' ≤ _ := ew_succ_le HC
  have hζIH : ∀ i ≤ j, eζH R i t t' ≤ V * M := fun i hi =>
    (eζ_le_ev (H.cmp i hi).H (H.cmp i hi).H').trans (hev i hi)
  have hΔ := lD_sq_le H.hKc j t t' hζIH
  have h2 := nW1H_sub_le HC.H HC.H' (H.whH_le le_rfl)
  have h3 : ‖nW1H R j t' - nW1H R j t‖ ≤ (2 * R.ℓ ^ 2 * V + 2 * Z) * M := by
    have b1 := mul_le_mul_of_nonneg_left (hζIH j le_rfl) (by positivity : (0 : ℝ) ≤ 2 * R.ℓ ^ 2)
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
/-- **(LG) along two histories.** -/
theorem LG_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {b₁ : ℝ}
    (F : FinOne R j t ε b₁ cz (cmu Λ cm)) (F' : FinOne R j t' ε b₁ cz (cmu Λ cm))
    {M V W₁ Z β : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hβ : 0 ≤ β)
    (hb : 0 ≤ b₁) (hev : ∀ i ≤ j, evH R i t t' ≤ V * M) (heW : eWH R j t t' ≤ (e + ε) * W₁ * M)
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
    |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + (e + ε) * (200 * K ^ 4)) * |(t' j).1 - (t j).1| +
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
  have P := pieces_hist H hM hV hW₁ hZ hev heW hew k1 k2 k3 k4 k5
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
  have hG := G_core F.hO F'.hO hs16 (hsz F.ζ_le) (hsz F'.ζ_le) (hsn F.n_le) (hsn F'.n_le)
  have h3 := d3_le HC (kap_rem_scaled HC hkap)
  rw [← hβd] at h3
  have hζ := dζ_hist H F F' hM hV hev hβd hkap k8 k9 k10
  have hY := dY_hist H hM hV hev hβd hkap
  have hw := dw_hist H hM hV hZ hev hew
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
  exact G_assemble P hsK hs0 hB3 (norm_nonneg _) h3K hζ hν hwK hn (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hG

set_option maxHeartbeats 1000000 in
/-- **(Lm) along two histories.** The mass condition `|m²| L^{2(j+2)} ≤ ϑ` enters only through
the term `2Kϑ M`. -/
theorem Lm_hist (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {b₁ : ℝ}
    (F : FinOne R j t ε b₁ cz (cmu Λ cm)) (F' : FinOne R j t' ε b₁ cz (cmu Λ cm))
    {M V W₁ Z β ϑ : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hZ : 0 ≤ Z) (hβ : 0 ≤ β)
    (hb : 0 ≤ b₁) (hϑ0 : 0 ≤ ϑ) (hϑ : |R.msq| * ((L : ℝ) ^ (j + 2)) ^ 2 ≤ ϑ)
    (hev : ∀ i ≤ j, evH R i t t' ≤ V * M) (heW : eWH R j t t' ≤ (e + ε) * W₁ * M)
    (hew : ewH R j t t' ≤ Z * M) {Cq Cl cS : ℝ}
    (hβd : β = bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') (lD R Kc j t t') 1 (R.ℓ / 4))
    (hs8 : ε * cSz b₁ R.ℓ ≤ 1 / 8) :
    let K := cKa L β b₁ R.ℓ (cmu Λ cm) cz V Z (2 * Kc * (L : ℝ) ^ 8)
      (kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) V W₁ Z)
    |(rgData R).m j t - (rgData R).m j t'| ≤ 300 * K ^ 4 * (|(t' j).1 - (t j).1| +
      ‖(t' j).2.2 - (t j).2.2‖) + (e + ε) * (300 * K ^ 4) * |(t' j).2.1 - (t j).2.1| +
      ((e + ε) * (300 * K ^ 4) + 2 * K * ϑ) * M := by
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
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8, k9, k10, k11, -, -, -, k15, k16, k17, k18, k19, -⟩ :=
    cKa_ge (β := β) (b₁ := b₁) (ℓ := R.ℓ) (cmu := cmu Λ cm) (cz := cz) (V := V) (Z := Z)
      (Λ0 := 2 * Kc * (L : ℝ) ^ 8) (kThv := kTh R.ℓ (cmu Λ cm) (cTh R.ℓ cw (cx κ cT))
        (2 * Kc * (L : ℝ) ^ 8) V W₁ Z) L hβ hb hcmu hcz hV hZ (by positivity) hkTh
  have P := pieces_hist H hM hV hW₁ hZ hev heW hew k1 k2 k3 k4 k5
  set σ := e + ε
  have hζ := dζ_hist H F F' hM hV hev hβd hkap k8 k9 k10
  have hY := dY_hist H hM hV hev hβd hkap
  have hp1 : 0 ≤ cSz b₁ R.ℓ := by unfold cSz; positivity
  have hζ1 : ‖zetaH R (j + 1) t‖ ≤ 1 / 8 := F.ζ_le.trans hs8
  have hζ1' : ‖zetaH R (j + 1) t'‖ ≤ 1 / 8 := F'.ζ_le.trans hs8
  have hm := m_core F.hO F'.hO hζ1 hζ1'
  have hΘ := thetaH_nonneg HC
  have hdĝ := norm_nonneg (ghat (sdH R j t') - ghat (sdH R j t))
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  -- `dY ≤ K(Θ + dĝ) + ϑ K M + σ K M`
  have hY' : ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) - (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ ≤
      K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') + ‖ghat (sdH R j t') - ghat (sdH R j t)‖) +
        ϑ * K * M + σ * K * M := by
    have d1 : (L : ℝ) ^ 2 * (4 * β) ≤ K := by
      have : 0 ≤ (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (4 * β) +
        (L : ℝ) ^ 2 * (1 + R.ℓ ^ 2 / 8 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have d2 : (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) ≤ K := by
      have : 0 ≤ (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        positivity
      linarith only [k11, this, show (L : ℝ) ^ 2 * (4 * β + 1 + R.ℓ ^ 2 / 8 + 2 * V +
        3 * (2 * Kc * (L : ℝ) ^ 8) * V) = (L : ℝ) ^ 2 * (R.ℓ ^ 2 / 8) +
        (L : ℝ) ^ 2 * (4 * β + 1 + 2 * V + 3 * (2 * Kc * (L : ℝ) ^ 8) * V) by ring]
    have a1 := mul_le_mul_of_nonneg_right d1 hΘ
    have a2 := mul_le_mul_of_nonneg_right d2 hdĝ
    -- the mass term
    have hmj : (L : ℝ) ^ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ ϑ := by
      have e1 : |R.msq| * ((L : ℝ) ^ (j + 2)) ^ 2 =
          (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2)) := by ring
      have h0 : 0 ≤ (L : ℝ) ^ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by positivity
      have := le_mul_of_one_le_left h0 hL1
      linarith only [this, hϑ, e1]
    have a3 : (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) * M ≤ ϑ * K * M := by
      have b1 : (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) ≤ ϑ * (2 * V) := by
        have := mul_le_mul_of_nonneg_right hmj (by positivity : (0 : ℝ) ≤ 2 * V)
        linarith only [this, show (L : ℝ) ^ 2 * (2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * V) =
          (L : ℝ) ^ 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * (2 * V) by ring]
      have b2 : ϑ * (2 * V) ≤ ϑ * K := mul_le_mul_of_nonneg_left k16 hϑ0
      exact mul_le_mul_of_nonneg_right (b1.trans b2) hM
    have a4 : (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) * M ≤ σ * K * M := by
      have b1 : (L : ℝ) ^ 2 * (16 / 7 * ε * (2 * Kc * (L : ℝ) ^ 8) * V) ≤
          σ * (3 * (L : ℝ) ^ 2 * (2 * Kc * (L : ℝ) ^ 8) * V) := by
        have h0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Kc * (L : ℝ) ^ 8) * V := by positivity
        have := mul_le_mul_of_nonneg_right (show ε ≤ σ by simp only [σ]; linarith) h0
        nlinarith
      have b2 : σ * (3 * (L : ℝ) ^ 2 * (2 * Kc * (L : ℝ) ^ 8) * V) ≤ σ * K :=
        mul_le_mul_of_nonneg_left k17 (by simp only [σ]; linarith)
      exact mul_le_mul_of_nonneg_right (b1.trans b2) hM
    have e2 : K * (thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        ‖ghat (sdH R j t') - ghat (sdH R j t)‖) = K * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') +
        K * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by ring
    have e3 : (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') =
        (L : ℝ) ^ 2 * (4 * β) * thetaH R j t t' cw (cx κ cT) e (lD R Kc j t t') := rfl
    linarith only [hY, a1, a2, a3, a4, e2]
  -- `dP`
  set Pt := nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ) * (1 + zetaH R (j + 1) t)
  set Pt' := nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ) * (1 + zetaH R (j + 1) t')
  have hdζ0 := norm_nonneg (zetaH R (j + 1) t' - zetaH R (j + 1) t)
  have hP : ‖Pt' - Pt‖ ≤ ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
      (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ + σ * K * |(t' j).2.1 - (t j).2.1| +
      σ * K * ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ := by
    have e1 : Pt' - Pt = ((nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))) -
        ((L : ℂ) ^ 2 * ((((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) * zetaH R (j + 1) t') +
          (L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * (zetaH R (j + 1) t' - zetaH R (j + 1) t))) := by
      simp only [Pt, Pt']; push_cast; ring
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have b1 := norm_add_le ((L : ℂ) ^ 2 * ((((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) * zetaH R (j + 1) t'))
      ((L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * (zetaH R (j + 1) t' - zetaH R (j + 1) t)))
    have hn1 : ‖(L : ℂ) ^ 2 * ((((t' j).2.1 - (t j).2.1 : ℝ) : ℂ) * zetaH R (j + 1) t')‖ =
        (L : ℝ) ^ 2 * ‖zetaH R (j + 1) t'‖ * |(t' j).2.1 - (t j).2.1| := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]; ring
    have hn2 : ‖(L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * (zetaH R (j + 1) t' - zetaH R (j + 1) t))‖ =
        (L : ℝ) ^ 2 * |(t j).2.1| * ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]; ring
    have c1 : (L : ℝ) ^ 2 * ‖zetaH R (j + 1) t'‖ ≤ σ * K := by
      have := mul_le_mul_of_nonneg_left F'.ζ_le hL2
      have h2 : (L : ℝ) ^ 2 * (ε * cSz b₁ R.ℓ) ≤ σ * K := by
        have := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) k18 (by positivity)
          (by simp only [σ]; linarith)
        linarith only [this, show (L : ℝ) ^ 2 * (ε * cSz b₁ R.ℓ) = ε * ((L : ℝ) ^ 2 * cSz b₁ R.ℓ) by ring]
      linarith only [this, h2]
    have c2 : (L : ℝ) ^ 2 * |(t j).2.1| ≤ σ * K := by
      have := mul_le_mul_of_nonneg_left F.μ hL2
      have h2 : (L : ℝ) ^ 2 * (cmu Λ cm * ε) ≤ σ * K := by
        have := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) k19 (by positivity)
          (by simp only [σ]; linarith)
        linarith only [this, show (L : ℝ) ^ 2 * (cmu Λ cm * ε) = ε * ((L : ℝ) ^ 2 * cmu Λ cm) by ring]
      linarith only [this, h2]
    have d1 := mul_le_mul_of_nonneg_right c1 (abs_nonneg ((t' j).2.1 - (t j).2.1))
    have d2 := mul_le_mul_of_nonneg_right c2 hdζ0
    linarith only [b1, hn1, hn2, d1, d2]
  -- `|P|`
  have hPn : ‖Pt‖ ≤ σ * K := by
    have e1 : Pt = (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)) -
        (L : ℂ) ^ 2 * (((t j).2.1 : ℂ) * zetaH R (j + 1) t) := by simp only [Pt]; ring
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    have a1 := F.Y
    have a2 : (L : ℝ) ^ 2 * (|(t j).2.1| * ‖zetaH R (j + 1) t‖) ≤
        ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) := by
      have := mul_le_mul F.μ F.ζ_le (norm_nonneg _) (by positivity)
      have := mul_le_mul_of_nonneg_left this hL2
      have h3 : (L : ℝ) ^ 2 * (cmu Λ cm * ε * (ε * cSz b₁ R.ℓ)) ≤ ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) := by
        have h0 : 0 ≤ ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) := by positivity
        have := mul_le_mul_of_nonneg_right hε1 h0
        nlinarith
      linarith only [this, h3]
    have h4 : ε * cSY L b₁ cz R.ℓ + ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) ≤ σ * K := by
      have := mul_le_mul (show ε ≤ σ by simp only [σ]; linarith) k15
        (by unfold cSY; positivity) (by simp only [σ]; linarith)
      linarith only [this, show ε * (cSY L b₁ cz R.ℓ + (L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) =
        ε * cSY L b₁ cz R.ℓ + ε * ((L : ℝ) ^ 2 * cmu Λ cm * cSz b₁ R.ℓ) by ring]
    linarith only [a1, a2, h4]
  have := m_assemble P hϑ0 hPn (norm_nonneg _) hζ hdζ0 hY' hP hm
  linarith only [this]

end Hist

end

end Step2
