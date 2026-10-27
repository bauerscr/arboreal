import Step2.Flow.FlowHor2Aux
import Flow2.FixedRParamZ2

/-!
# The hypotheses of the `ϑ`-free fixed-`β_R` flow theorem

`hyps_of_lipz`: a copy of `flow_of_lipz` (`Step2/Flow/FlowHor2Aux.lean`) that returns the hypotheses
instead of the conclusions of `prop:C6`: `HHyp` with large constants `(C_L, a_B)`, the uniqueness
hypotheses `ZHyp` with the hidden coupling `ζ` (`zetaH`), and the monotonicity hypotheses
`MonoZHyp` (fading memory `3/4`, `Flow2/FixedRParamZ2.lean`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

theorem hyps_of_lipz (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    {Λ β δ κ₁ cg cm cT ε Cb CL : ℝ} (hΛ : 1 < Λ) (hβ : 0 < β) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hκ0 : 0 ≤ κ₁) (hκ₁ : κ₁ < 1) (hcg : 0 < cg) (hcm : 0 < cm) (hc : 0 < cT)
    (hCL : 0 ≤ CL) (hCb : 0 ≤ Cb) (hCc : Cb ≤ cT) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : Cb * ε * (1 + cx ((1 + κ₁) / 2) cT) ≤ (1 - κ₁) / 2)
    (hsl : CL * ε ≤ (1 - κ₁) / 2)
    (contG : ∀ j < Nh, Continuous ((rgData R).G j)) (contm : ∀ j < Nh, Continuous ((rgData R).m j))
    (contT : ∀ j < Nh, Continuous ((rgData R).T j))
    (F1 : ∀ j < Nh, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      |(rgData R).G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    (F2 : ∀ j < Nh, ∀ t, InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      |(rgData R).m j t| ≤ cm * (t j).1)
    (Hb : RGBound (rgData R) Λ β δ κ₁ Cb cg cm cT ε Nh)
    (LGd : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
      |(rgData R).G j t - (rgData R).G j t' - ((t j).1 - (t' j).1)| ≤
        CL * ε * |(t j).1 - (t' j).1| +
        CL * ε * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ + CL * ε * M)
    (Lmz : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
      |(rgData R).m j t - (rgData R).m j t'| ≤ CL * |(t j).1 - (t' j).1| +
        CL * ε * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ +
        CL * ε * M + 4 * ‖zetaH R j t - zetaH R j t'‖)
    (LZ : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
      ‖zetaH R (j + 1) t - zetaH R (j + 1) t'‖ ≤
        CL * (|(t j).1 - (t' j).1| + ‖(t j).2.2 - (t' j).2.2‖) +
        CL * ε * (|(t j).2.1 - (t' j).2.1| + M))
    (LT : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' →
      ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
      ‖((rgData R).T j t).2 - ((rgData R).T j t').2‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
        CL * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M) ∧
      ‖((rgData R).T j t).1 - ((rgData R).T j t').1‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
        CL * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M)) :
    HHyp (rgData R) Λ β δ ((1 + κ₁) / 2) cg cm cT Nh CL ((CL + Cb) * ε + 4 * (CL + 2 * (CL * ε))) ε ∧
      ZHyp (rgData R) Λ β δ ((1 + κ₁) / 2) cg cm cT Nh (zetaH R) CL (CL * ε) CL (CL * ε) 4 ε ∧
      MonoZHyp (rgData R) Λ β δ ((1 + κ₁) / 2) cg cm cT Nh (zetaH R) CL (CL * ε) CL 4 ε (3 / 4) := by
  have hCε : 0 ≤ CL * ε := mul_nonneg hCL hε.le
  -- (KL), (YL) with unweighted histories
  have HL : RGLip (rgData R) Λ β δ κ₁ CL cg cm cT ε Nh := fun j hj t t' ht ht' M hM hh =>
    LT j hj t t' ht ht' M hM (hist_weight hh)
  -- the hidden coupling at the current scale, from the past
  have hζM : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      ‖zetaH R j t - zetaH R j t'‖ ≤ (CL + 2 * (CL * ε)) * M := by
    intro j hj t t' ht ht' M hM hh
    cases j with
    | zero =>
      have e : zetaH R 0 t - zetaH R 0 t' = 0 := sub_eq_zero.2 rfl
      rw [e, norm_zero]; positivity
    | succ i =>
      have hti := InDh_mono ht
      have hti' := InDh_mono ht'
      have h := LZ i (by omega) t t' hti hti' M hM
        (hist_weight (fun k hk => hh k (by omega)))
      have hd := hh i (by omega)
      unfold dist3 at hd
      have a1 := mul_le_mul_of_nonneg_left
        (show |(t i).1 - (t' i).1| + ‖(t i).2.2 - (t' i).2.2‖ ≤ M by
          linarith only [hd, abs_nonneg ((t i).2.1 - (t' i).2.1)]) hCL
      have a2 := mul_le_mul_of_nonneg_left
        (show |(t i).2.1 - (t' i).2.1| + M ≤ 2 * M by
          linarith only [hd, abs_nonneg ((t i).1 - (t' i).1), norm_nonneg ((t i).2.2 - (t' i).2.2)])
        hCε
      linarith only [h, a1, a2, show (CL + 2 * (CL * ε)) * M = CL * M + CL * ε * (2 * M) by ring]
  -- `HHyp` with large constants (existence, band, continuity)
  obtain ⟨aB, haBd⟩ : ∃ aB, aB = (CL + Cb) * ε + 4 * (CL + 2 * (CL * ε)) := ⟨_, rfl⟩
  have hCa : Cb * ε ≤ aB := by
    rw [haBd]; have : 0 ≤ CL * ε := hCε
    nlinarith [mul_nonneg hCb hε.le]
  have hCla : CL * ε ≤ aB := by
    rw [haBd]; nlinarith [mul_nonneg hCb hε.le]
  have hCLa : CL * ε + 4 * (CL + 2 * (CL * ε)) ≤ aB := by
    rw [haBd]; nlinarith [mul_nonneg hCb hε.le]
  have LGh : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + CL * ε) * |(t j).1 - (t' j).1| +
        CL * ε * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ + CL * ε * M := by
    intro j hj t t' ht ht' M hM hh
    have h := LGd j hj t t' ht ht' M hM (hist_weight hh)
    have h2 := abs_sub_abs_le_abs_sub ((rgData R).G j t - (rgData R).G j t') ((t j).1 - (t' j).1)
    linarith only [h, h2]
  have LGB : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + aB) * |(t j).1 - (t' j).1| +
        aB * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ + aB * M := by
    intro j hj t t' ht ht' M hM hh
    have h := LGh j hj t t' ht ht' M hM hh
    have a1 := mul_le_mul_of_nonneg_right hCla (abs_nonneg ((t j).1 - (t' j).1))
    have a2 := mul_le_mul_of_nonneg_right hCla (abs_nonneg ((t j).2.1 - (t' j).2.1))
    have a3 := mul_le_mul_of_nonneg_right hCla hM
    linarith only [h, a1, a2, a3]
  have LmB : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |(rgData R).m j t - (rgData R).m j t'| ≤ CL * |(t j).1 - (t' j).1| +
        aB * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ + aB * M := by
    intro j hj t t' ht ht' M hM hh
    have h := Lmz j hj t t' ht ht' M hM (hist_weight hh)
    have hz := hζM j hj t t' ht ht' M hM hh
    have a2 := mul_le_mul_of_nonneg_right hCla (abs_nonneg ((t j).2.1 - (t' j).2.1))
    have a3 := mul_le_mul_of_nonneg_right hCLa hM
    linarith only [h, hz, a2, a3, show (CL * ε + 4 * (CL + 2 * (CL * ε))) * M =
      CL * ε * M + 4 * ((CL + 2 * (CL * ε)) * M) by ring]
  have H := hhyp_of_rg2 (F := rgData R) (Λ := Λ) (β := β) (δ := δ) (κ₁ := κ₁) (cg := cg) (cm := cm)
    (cT := cT) (ε := ε) (N := Nh) (Cb := Cb) (Cl := CL) CL aB hΛ hβ hδ hδ1 hκ0 hκ₁ hcg hcm hc hCL
    hCb hCc hε hε1 hsmall hCa hsl hCla (fun j _ => causal_G R j) (fun j _ => causal_m R j)
    (fun j _ => causal_T R j) contG contm contT F1 F2 LGB LmB Hb HL
  -- uniqueness
  have LTz := LT_of_rg hsl HL
  have HZ : ZHyp (rgData R) Λ β δ ((1 + κ₁) / 2) cg cm cT Nh (zetaH R) CL (CL * ε) CL (CL * ε) 4 ε :=
    { hA := hCL, ha := hCε, hAζ := hCL, haζ := hCε, hbζ := by norm_num
      Z0 := fun t t' => rfl
      LG := LGh
      Lmz := fun j hj t t' ht ht' M hM hh => Lmz j hj t t' ht ht' M hM (hist_weight hh)
      LT := fun j hj t t' ht ht' M hM hh => by
        have h := LTz j hj t t' ht ht' M hM hh
        linarith only [h]
      LZ := fun j hj t t' ht ht' M hM hh => LZ j hj t t' ht ht' M hM (hist_weight hh) }
  -- the monotonicity hypotheses (weighted histories)
  have LTw : ∀ j < Nh, ∀ t t', InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t →
      InDh Λ β δ ((1 + κ₁) / 2) cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
      ‖(rgData R).T j t - (rgData R).T j t'‖ ≤ (1 + κ₁) / 2 * ‖(t j).2.2 - (t' j).2.2‖ +
        CL * ε * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + CL * ε * M := by
    intro j hj t t' ht ht' M hM hh
    obtain ⟨hY, hK⟩ := LT j hj t t' ht ht' M hM hh
    have hb : ∀ r : ℝ, r ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ + CL * ε * (‖(t j).2.2 - (t' j).2.2‖ +
        |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M) →
        r ≤ (1 + κ₁) / 2 * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * ε * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + CL * ε * M := by
      intro r hr
      have := mul_le_mul_of_nonneg_right hsl (norm_nonneg ((t j).2.2 - (t' j).2.2))
      nlinarith
    rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
    exact max_le (hb _ hK) (hb _ hY)
  have HMZ : MonoZHyp (rgData R) Λ β δ ((1 + κ₁) / 2) cg cm cT Nh (zetaH R) CL (CL * ε) CL 4 ε
      (3 / 4) :=
    { hw0 := by norm_num, hw1 := by norm_num, hA := hCL, ha := hCε, hAζ := hCL
      hbζ := by norm_num, Z0 := fun t t' => rfl
      LGd := LGd, Lmz := Lmz, LT := LTw, LZ := LZ }
  rw [haBd] at H
  exact ⟨H, HZ, HMZ⟩

end

end Step2
