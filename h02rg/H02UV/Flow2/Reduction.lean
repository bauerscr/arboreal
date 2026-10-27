import Flow2.History

/-!
# The irrelevant coordinates of the renormalisation group flow (`h02uv-outline.tex`,
Section `sec:reduction`)

The irrelevant coordinates are `x = (D, K) ∈ Y_j × Z_j` with the max norm, where
`D = 𝒲 - 𝒲^lin` and `K` is the activity. The hypotheses (F3) and (LT) of `prop:C6` follow from
bounds of the shape that the step estimates provide:

* (Kb) `‖K_{j+1}‖ ≤ κ₁ ‖K‖ + C (g³ + g ‖K‖ + ‖K‖²)` (`Step2.stepK`, at the rescaled input);
* (Yb) `‖D_{j+1}‖ ≤ κ₁ ‖D‖ + C g⁴` (`Step2.TrL_contract'`, `Step2.prodRem_bound`);
* (KL), (YL) Lipschitz bounds `κ₁ ‖δx‖ + C ε (‖δx‖ + |δg| + |δμ| + M)` (`Step2.Kplus_lip`,
  `Step2.RemW_lip`, `Step2.Kplus_lip_cov`, …).

`F3_of_rg` and `LT_of_rg` give (F3) and (LT) with `κ = (1 + κ₁)/2` and `a = C ε`, for `ε` small;
`hhyp_of_rg` assembles `HHyp`, and `flow_of_rg` gives the conclusions of `prop:C6`.
-/

open Set

noncomputable section

namespace Flow2

namespace Hist

variable {Y Z : ℕ → Type*} [∀ j, NormedAddCommGroup (Y j)] [∀ j, NormedAddCommGroup (Z j)]

/-- The irrelevant coordinates `x = (D, K)`. -/
abbrev XP (Y Z : ℕ → Type*) [∀ j, NormedAddCommGroup (Y j)] [∀ j, NormedAddCommGroup (Z j)]
    (j : ℕ) : Type _ := Y j × Z j

variable (F : HData (XP Y Z)) (Λ β δ κ₁ C cg cm cT ε : ℝ)

/-- The bounds (Kb), (Yb) on the domain. -/
def RGBound (N : ℕ) : Prop :=
  ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
    ‖(F.T j t).2‖ ≤ κ₁ * ‖(t j).2.2.2‖ +
      C * ((t j).1 ^ 3 + (t j).1 * ‖(t j).2.2.2‖ + ‖(t j).2.2.2‖ ^ 2) ∧
    ‖(F.T j t).1‖ ≤ κ₁ * ‖(t j).2.2.1‖ + C * (t j).1 ^ 4

/-- The Lipschitz bounds (KL), (YL). -/
def RGLip (N : ℕ) : Prop :=
  ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    ‖(F.T j t).2 - (F.T j t').2‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
      C * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M) ∧
    ‖(F.T j t).1 - (F.T j t').1‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
      C * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M)

variable {F Λ β δ κ₁ C cg cm cT ε}

/-- **(F3) from the step bounds.** -/
theorem F3_of_rg {N : ℕ} (hκ0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1) (hC : 0 ≤ C) (hCc : C ≤ cT) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : C * ε * (1 + cx ((1 + κ₁) / 2) cT) ≤ (1 - κ₁) / 2) (H : RGBound F Λ β δ κ₁ C cg cm cT ε N) :
    ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      ‖F.T j t‖ ≤ (1 + κ₁) / 2 * ‖(t j).2.2‖ + cT * (t j).1 ^ 3 := by
  intro j hj t ht
  obtain ⟨hK, hY⟩ := H j hj t ht
  obtain ⟨hg0, hgε, -, hx⟩ := ht.1 j le_rfl
  set g := (t j).1
  set x := (t j).2.2
  have hy : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
  have hk : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hg1 : g ≤ 1 := hgε.trans hε1
  have hg3 : g ^ 3 ≤ g := by nlinarith [pow_le_one₀ hg0.le hg1 (n := 2)]
  have hcx : 0 ≤ cx ((1 + κ₁) / 2) cT := by
    unfold cx; exact div_nonneg (by nlinarith [hCc, hC]) (by linarith)
  have hkk : ‖x.2‖ ^ 2 ≤ cx ((1 + κ₁) / 2) cT * ε * ‖x‖ := by
    have h1 : ‖x.2‖ ≤ cx ((1 + κ₁) / 2) cT * g ^ 3 := hk.trans hx
    have h2 : cx ((1 + κ₁) / 2) cT * g ^ 3 ≤ cx ((1 + κ₁) / 2) cT * ε :=
      mul_le_mul_of_nonneg_left (hg3.trans hgε) hcx
    nlinarith [norm_nonneg x.2]
  have hK' : ‖(F.T j t).2‖ ≤ (1 + κ₁) / 2 * ‖x‖ + cT * g ^ 3 := by
    refine hK.trans ?_
    have h1 : κ₁ * ‖x.2‖ ≤ κ₁ * ‖x‖ := mul_le_mul_of_nonneg_left hk hκ0
    have h2 : C * (g * ‖x.2‖) ≤ C * ε * ‖x‖ := by
      have : g * ‖x.2‖ ≤ ε * ‖x‖ := mul_le_mul hgε hk (norm_nonneg _) hε.le
      nlinarith
    have h3 : C * ‖x.2‖ ^ 2 ≤ C * ε * cx ((1 + κ₁) / 2) cT * ‖x‖ := by
      have := mul_le_mul_of_nonneg_left hkk hC; nlinarith
    have h4 : C * g ^ 3 ≤ cT * g ^ 3 := mul_le_mul_of_nonneg_right hCc (by positivity)
    have h5 : C * ε * (1 + cx ((1 + κ₁) / 2) cT) * ‖x‖ ≤ (1 - κ₁) / 2 * ‖x‖ :=
      mul_le_mul_of_nonneg_right hsmall hx0
    nlinarith
  have hY' : ‖(F.T j t).1‖ ≤ (1 + κ₁) / 2 * ‖x‖ + cT * g ^ 3 := by
    refine hY.trans ?_
    have h1 : κ₁ * ‖x.1‖ ≤ (1 + κ₁) / 2 * ‖x‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hy hκ0]
    have h2 : C * g ^ 4 ≤ cT * g ^ 3 := by
      have : g ^ 4 ≤ g ^ 3 := pow_le_pow_of_le_one hg0.le hg1 (by norm_num)
      calc C * g ^ 4 ≤ C * g ^ 3 := mul_le_mul_of_nonneg_left this hC
        _ ≤ cT * g ^ 3 := mul_le_mul_of_nonneg_right hCc (by positivity)
    linarith
  rw [Prod.norm_def]
  exact max_le hY' hK'

/-- **(LT) from the step Lipschitz bounds.** -/
theorem LT_of_rg {N : ℕ} (hsmall : C * ε ≤ (1 - κ₁) / 2)
    (H : RGLip F Λ β δ κ₁ C cg cm cT ε N) :
    ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      ‖F.T j t - F.T j t'‖ ≤ (1 + κ₁) / 2 * ‖(t j).2.2 - (t' j).2.2‖ +
        C * ε * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + C * ε * M := by
  intro j hj t t' ht ht' M hM hhist
  obtain ⟨hK, hY⟩ := H j hj t t' ht ht' M hM hhist
  have hb : ∀ r : ℝ, r ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ + C * ε * (‖(t j).2.2 - (t' j).2.2‖ +
      |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M) →
      r ≤ (1 + κ₁) / 2 * ‖(t j).2.2 - (t' j).2.2‖ +
        C * ε * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + C * ε * M := by
    intro r hr
    have := mul_le_mul_of_nonneg_right hsmall (norm_nonneg ((t j).2.2 - (t' j).2.2))
    nlinarith
  rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  exact max_le (hb _ hY) (hb _ hK)

variable (A a : ℝ)

/-- **`HHyp` from the step bounds.** The hypotheses on the relevant and marginal coordinates
(F1), (F2), (LG), (Lm) are taken as given; (F3) and (LT) come from (Kb), (Yb), (KL), (YL). -/
theorem hhyp_of_rg {N : ℕ} (hΛ : 1 < Λ) (hβ : 0 < β) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hκ0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1) (hcg : 0 < cg) (hcm : 0 < cm) (hc : 0 < cT)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCc : C ≤ cT) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : C * ε * (1 + cx ((1 + κ₁) / 2) cT) ≤ (1 - κ₁) / 2) (hCa : C * ε ≤ a)
    (causG : ∀ j < N, Causal j (F.G j)) (causm : ∀ j < N, Causal j (F.m j))
    (causT : ∀ j < N, Causal j (F.T j))
    (contG : ∀ j < N, Continuous (F.G j)) (contm : ∀ j < N, Continuous (F.m j))
    (contT : ∀ j < N, Continuous (F.T j))
    (F1 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    (F2 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → |F.m j t| ≤ cm * (t j).1)
    (LG : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.G j t - F.G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Lm : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Hb : RGBound F Λ β δ κ₁ C cg cm cT ε N) (HL : RGLip F Λ β δ κ₁ C cg cm cT ε N) :
    HHyp F Λ β δ ((1 + κ₁) / 2) cg cm cT N A a ε where
  hΛ := hΛ
  hβ := hβ
  hδ := hδ
  hδ1 := hδ1
  hκ0 := by linarith
  hκ1 := by linarith
  hcg := hcg
  hcm := hcm
  hcT := hc
  hA := hA
  ha := (mul_nonneg hC hε.le).trans hCa
  causG := causG
  causm := causm
  causT := causT
  contG := contG
  contm := contm
  contT := contT
  F1 := F1
  F2 := F2
  F3 := F3_of_rg hκ0 hκ₁ hC hCc hε hε1 hsmall Hb
  LG := LG
  Lm := Lm
  LT := fun j hj t t' ht ht' M hM hh => by
    have hs : C * ε ≤ (1 - κ₁) / 2 := by
      have : 0 ≤ C * ε * cx ((1 + κ₁) / 2) cT := by
        have hcx : 0 ≤ cx ((1 + κ₁) / 2) cT := by
          unfold cx; exact div_nonneg (by linarith) (by linarith)
        positivity
      nlinarith
    refine (LT_of_rg hs HL j hj t t' ht ht' M hM hh).trans ?_
    have h1 := mul_le_mul_of_nonneg_right hCa
      (add_nonneg (abs_nonneg ((t j).1 - (t' j).1)) (abs_nonneg ((t j).2.1 - (t' j).2.1)))
    have h2 := mul_le_mul_of_nonneg_right hCa hM
    linarith

/-- **The flow of `prop:C6` from the step bounds**: existence, uniqueness, the marginal
coordinate and continuity. -/
theorem flow_of_rg {N : ℕ} (hΛ : 1 < Λ) (hβ : 0 < β) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hκ0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1) (hcg : 0 < cg) (hcm : 0 < cm) (hc : 0 < cT)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCc : C ≤ cT) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : C * ε * (1 + cx ((1 + κ₁) / 2) cT) ≤ (1 - κ₁) / 2) (hCa : C * ε ≤ a)
    (he : ε ≤ eps0u Λ β δ ((1 + κ₁) / 2) cg cm) (ha0 : a ≤ a0h Λ ((1 + κ₁) / 2) A)
    (causG : ∀ j < N, Causal j (F.G j)) (causm : ∀ j < N, Causal j (F.m j))
    (causT : ∀ j < N, Causal j (F.T j))
    (contG : ∀ j < N, Continuous (F.G j)) (contm : ∀ j < N, Continuous (F.m j))
    (contT : ∀ j < N, Continuous (F.T j))
    (F1 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    (F2 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → |F.m j t| ≤ cm * (t j).1)
    (LG : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.G j t - F.G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Lm : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Hb : RGBound F Λ β δ κ₁ C cg cm cT ε N) (HL : RGLip F Λ β δ κ₁ C cg cm cT ε N) :
    (∀ b ∈ Ioc 0 (bmax β δ cg N ε), ∃! μ₀, Admissible F Λ ((1 + κ₁) / 2) cm cT N ε b μ₀) ∧
    (∀ b μ₀, Admissible F Λ ((1 + κ₁) / 2) cm cT N ε b μ₀ → ∀ j < N,
      |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
        2 * (1 + β) * δ * β + Cgu β cg * (traj F Λ b μ₀ j).1) ∧
    ContinuousOn (muc F Λ ((1 + κ₁) / 2) cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) ∧
    ContinuousOn (gN F Λ ((1 + κ₁) / 2) cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) :=
  fh_flow_hist (hhyp_of_rg A a hΛ hβ hδ hδ1 hκ0 hκ₁ hcg hcm hc hA hC hCc hε hε1 hsmall hCa causG causm
    causT contG contm contT F1 F2 LG Lm Hb HL) he hε ha0

/-- **`HHyp` from the step bounds, with separate constants** `C_b` for (Kb), (Yb) and `C_l` for
(KL), (YL). Only `C_b ≤ c_T` is needed; the Lipschitz constant may depend on `c_T`. -/
theorem hhyp_of_rg2 {N : ℕ} {Cb Cl : ℝ} (hΛ : 1 < Λ) (hβ : 0 < β) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hκ0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1) (hcg : 0 < cg) (hcm : 0 < cm) (hc : 0 < cT)
    (hA : 0 ≤ A) (hCb : 0 ≤ Cb) (hCc : Cb ≤ cT) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : Cb * ε * (1 + cx ((1 + κ₁) / 2) cT) ≤ (1 - κ₁) / 2) (hCa : Cb * ε ≤ a)
    (hsl : Cl * ε ≤ (1 - κ₁) / 2) (hCla : Cl * ε ≤ a)
    (causG : ∀ j < N, Causal j (F.G j)) (causm : ∀ j < N, Causal j (F.m j))
    (causT : ∀ j < N, Causal j (F.T j))
    (contG : ∀ j < N, Continuous (F.G j)) (contm : ∀ j < N, Continuous (F.m j))
    (contT : ∀ j < N, Continuous (F.T j))
    (F1 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    (F2 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → |F.m j t| ≤ cm * (t j).1)
    (LG : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.G j t - F.G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Lm : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Hb : RGBound F Λ β δ κ₁ Cb cg cm cT ε N) (HL : RGLip F Λ β δ κ₁ Cl cg cm cT ε N) :
    HHyp F Λ β δ ((1 + κ₁) / 2) cg cm cT N A a ε where
  hΛ := hΛ
  hβ := hβ
  hδ := hδ
  hδ1 := hδ1
  hκ0 := by linarith
  hκ1 := by linarith
  hcg := hcg
  hcm := hcm
  hcT := hc
  hA := hA
  ha := (mul_nonneg hCb hε.le).trans hCa
  causG := causG
  causm := causm
  causT := causT
  contG := contG
  contm := contm
  contT := contT
  F1 := F1
  F2 := F2
  F3 := F3_of_rg hκ0 hκ₁ hCb hCc hε hε1 hsmall Hb
  LG := LG
  Lm := Lm
  LT := fun j hj t t' ht ht' M hM hh => by
    refine (LT_of_rg hsl HL j hj t t' ht ht' M hM hh).trans ?_
    have h1 := mul_le_mul_of_nonneg_right hCla
      (add_nonneg (abs_nonneg ((t j).1 - (t' j).1)) (abs_nonneg ((t j).2.1 - (t' j).2.1)))
    have h2 := mul_le_mul_of_nonneg_right hCla hM
    linarith

/-- **The flow of `prop:C6` from the step bounds, with separate constants for the bounds and the
Lipschitz bounds.** -/
theorem flow_of_rg2 {N : ℕ} {Cb Cl : ℝ} (hΛ : 1 < Λ) (hβ : 0 < β) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hκ0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1) (hcg : 0 < cg) (hcm : 0 < cm) (hc : 0 < cT)
    (hA : 0 ≤ A) (hCb : 0 ≤ Cb) (hCc : Cb ≤ cT) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : Cb * ε * (1 + cx ((1 + κ₁) / 2) cT) ≤ (1 - κ₁) / 2) (hCa : Cb * ε ≤ a)
    (hsl : Cl * ε ≤ (1 - κ₁) / 2) (hCla : Cl * ε ≤ a)
    (he : ε ≤ eps0u Λ β δ ((1 + κ₁) / 2) cg cm) (ha0 : a ≤ a0h Λ ((1 + κ₁) / 2) A)
    (causG : ∀ j < N, Causal j (F.G j)) (causm : ∀ j < N, Causal j (F.m j))
    (causT : ∀ j < N, Causal j (F.T j))
    (contG : ∀ j < N, Continuous (F.G j)) (contm : ∀ j < N, Continuous (F.m j))
    (contT : ∀ j < N, Continuous (F.T j))
    (F1 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    (F2 : ∀ j < N, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → |F.m j t| ≤ cm * (t j).1)
    (LG : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.G j t - F.G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Lm : ∀ j < N, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t → InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
        A * ‖(t j).2.2 - (t' j).2.2‖ + a * M)
    (Hb : RGBound F Λ β δ κ₁ Cb cg cm cT ε N) (HL : RGLip F Λ β δ κ₁ Cl cg cm cT ε N) :
    (∀ b ∈ Ioc 0 (bmax β δ cg N ε), ∃! μ₀, Admissible F Λ ((1 + κ₁) / 2) cm cT N ε b μ₀) ∧
    (∀ b μ₀, Admissible F Λ ((1 + κ₁) / 2) cm cT N ε b μ₀ → ∀ j < N,
      |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
        2 * (1 + β) * δ * β + Cgu β cg * (traj F Λ b μ₀ j).1) ∧
    ContinuousOn (muc F Λ ((1 + κ₁) / 2) cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) ∧
    ContinuousOn (gN F Λ ((1 + κ₁) / 2) cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) :=
  fh_flow_hist (hhyp_of_rg2 A a hΛ hβ hδ hδ1 hκ0 hκ₁ hcg hcm hc hA hCb hCc hε hε1 hsmall hCa hsl hCla
    causG causm causT contG contm contT F1 F2 LG Lm Hb HL) he hε ha0

end Hist

end Flow2
