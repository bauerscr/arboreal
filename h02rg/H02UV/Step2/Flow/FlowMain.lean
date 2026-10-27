import Step2.Flow.FlowValid
import Step2.FlowCont.FlowCont

/-!
# Expected result `thm:flow` from the step estimates (`h02uv-outline.tex`, Section `sec:flow`)

`flow_rg`: the conclusions of `prop:C6` (`Flow2.Hist.flow_of_rg`) for the RG data `rgData R`, with
* causality (`causal_G`, `causal_m`, `causal_T`), continuity (`rgData_cont`), (Kb)/(Yb)
  (`rgBound_rg`), (F2) (`F2_rg`) and (F1) (`F1_rg`) discharged;
* the inputs of (F1) — the one-loop values (`HV`), the decay of the past coefficients (`HD`) and the
  sharp zero-mode / first-difference bounds (`HS`) — and the Lipschitz bounds (LG), (Lm), (LT) as
  hypotheses.
The constants are parameters subject to explicit inequalities.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist

set_option maxHeartbeats 2000000 in
/-- **`thm:flow` for the RG map, conditional on (HV), (HD), (HS) and the Lipschitz bounds.** -/
theorem flow_rg : ∃ Cq Cl cS CqD ClD : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧ 0 ≤ CqD ∧ 0 ≤ ClD ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (C₀ η εs CK C₂ CD Cq' Cl' cS' : ℝ),
      StepBounds L R.A C₀ η εs CK C₂ CD Cq' Cl' cS' → 0 ≤ C₀ → 0 ≤ CK → 0 ≤ CD → 2 ≤ R.A →
    ∀ (Nh : ℕ), (∀ j < Nh, ValidAt R j) → (∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) →
      (∀ j < Nh, CovCont R j) →
    ∀ (β δ cg cm cT ε A a : ℝ),
      let κ₁ := kap1 L R.A C₀ η
      let C := cB R ((L : ℝ) ^ 2) cm C₂ CK CD
      κ₁ < 1 → ApHyp R ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cg cm cT ε εs C₀ C₂ Cq' Cl' cS' →
      0 < β → 0 ≤ δ → δ ≤ 1 / 2 → 0 < cg → 0 < cm → 0 < cT → 0 ≤ A → C ≤ cT →
      C * ε * (1 + cx ((1 + κ₁) / 2) cT) ≤ (1 - κ₁) / 2 → C * ε ≤ a →
      ε ≤ eps0u ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm → a ≤ a0h ((L : ℝ) ^ 2) ((1 + κ₁) / 2) A →
      -- (F2)
      cF2 R + (16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 +
        (L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cm cT C₂ Cq' Cl' cS') *
          cmu ((L : ℝ) ^ 2) cm +
        2 * ((L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cm cT C₂ Cq' Cl' cS')) * ε ≤ cm →
      -- (F1)
      cg * ε ≤ β / 2 → cR R ((L : ℝ) ^ 2) cm C₂ * ε ≤ 1 → 8 * cx ((1 + κ₁) / 2) cT * ε ≤ 1 →
    ∀ (KB E0 E1 eA eB : ℝ), 0 ≤ KB → 0 ≤ eA → 0 ≤ eB →
      (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm cT ε j t →
        ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤ eA * (t j).1 ∧
        ‖stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 *
            (rawHist R j t).w1 -
          stZ' R (rawHist R j t) ^ 2 * stCov R j (rawHist R j t) 0 0 * (rawHist R j t).w1‖ ≤ eB) →
      (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm cT ε j t → ‖hqTil R j t‖ ≤ KB ∧
        ∑ k ∈ range j, ((j : ℝ) - k + 1) * 2 ^ (j - k) * ‖hbTil R j t k‖ ≤ KB) →
      (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm cT ε j t →
        |(f1Coef R j t).re - β| ≤ E0 + E1 * (t j).1) →
      f1cn R.ℓ (cmu ((L : ℝ) ^ 2) cm) * ε ≤ 1 / 8 →
      f1cn' L R.ℓ (cZ R) (cmu ((L : ℝ) ^ 2) cm) Cq (f1cRQ Cl cS (cx ((1 + κ₁) / 2) cT))
        (f1cRL L Cl (cV R ((L : ℝ) ^ 2) cm) (cW R ((L : ℝ) ^ 2) cm C₂)) * ε ≤ 1 / 8 →
      (R.ℓ ^ 2 / 7 + f1cw R.ℓ (cmu ((L : ℝ) ^ 2) cm) Cq (f1cRQ Cl cS (cx ((1 + κ₁) / 2) cT))
        (f1cRL L Cl (cV R ((L : ℝ) ^ 2) cm) (cW R ((L : ℝ) ^ 2) cm C₂))) * ε ≤ R.ρ →
      f1e eA eB + E0 ≤ δ * β →
      f1c3 L R.ℓ (cZ R) (cmu ((L : ℝ) ^ 2) cm) Cq (f1cRQ Cl cS (cx ((1 + κ₁) / 2) cT))
          (f1cRL L Cl (cV R ((L : ℝ) ^ 2) cm) (cW R ((L : ℝ) ^ 2) cm C₂))
          CqD (f1cRD L ClD (cx ((1 + κ₁) / 2) cT)) KB
          ((24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu ((L : ℝ) ^ 2) cm) + 2 * (2 * β + 1)) * KB) eA eB +
          E1 ≤ cg →
      -- the Lipschitz bounds
      (∀ j < Nh, ∀ t t', InDh ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm cT ε j t →
        InDh ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm cT ε j t' → ∀ M, 0 ≤ M →
        (∀ i < j, dist3 (t i) (t' i) ≤ M) →
        |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| +
          a * |(t j).2.1 - (t' j).2.1| + A * ‖(t j).2.2 - (t' j).2.2‖ + a * M) →
      (∀ j < Nh, ∀ t t', InDh ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm cT ε j t →
        InDh ((L : ℝ) ^ 2) β δ ((1 + κ₁) / 2) cg cm cT ε j t' → ∀ M, 0 ≤ M →
        (∀ i < j, dist3 (t i) (t' i) ≤ M) →
        |(rgData R).m j t - (rgData R).m j t'| ≤ A * |(t j).1 - (t' j).1| +
          a * |(t j).2.1 - (t' j).2.1| + A * ‖(t j).2.2 - (t' j).2.2‖ + a * M) →
      RGLip (rgData R) ((L : ℝ) ^ 2) β δ κ₁ C cg cm cT ε Nh →
      (∀ b ∈ Set.Ioc 0 (bmax β δ cg Nh ε),
          ∃! μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cm cT Nh ε b μ₀) ∧
      (∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cm cT Nh ε b μ₀ → ∀ j < Nh,
        |1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ (j + 1)).1 -
            1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 + β| ≤
          2 * (1 + β) * δ * β + Cgu β cg * (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1) ∧
      ContinuousOn (muc (rgData R) ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cm cT Nh ε)
        (Set.Ioc 0 (bmax β δ cg Nh ε)) ∧
      ContinuousOn (gN (rgData R) ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cm cT Nh ε)
        (Set.Ioc 0 (bmax β δ cg Nh ε)) := by
  obtain ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, hF1⟩ := F1_rg
  refine ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, ?_⟩
  intro L _ hL8 hLp N R _ _ C₀ η εs CK C₂ CD Cq' Cl' cS' hSB hC₀ hCK hCD hA2 Nh hV hm hc β δ cg cm cT
    ε A a κ₁ C hκ₁ H hβ hδ0 hδ1 hcg hcm hcT hA hCc hsmall hCa he ha0 hF2 hcgβ hcR1 hk1 KB E0 E1 eA eB
    hKB heA heB HS HD HV hs1 hs2 hs3 hband hcg3 LG Lm HL
  have hκ0 : 0 ≤ κ₁ := by
    show 0 ≤ kap1 L R.A C₀ η
    unfold kap1
    have : 0 < R.A := Fact.out
    positivity
  have hC0 : 0 ≤ C := by
    show 0 ≤ cB R ((L : ℝ) ^ 2) cm C₂ CK CD
    unfold cB; exact le_max_of_le_left (by positivity)
  have hΛ : (1 : ℝ) < (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
    nlinarith
  have hδ1' : δ ≤ 1 := by linarith only [hδ1]
  have Hb := rgBound_rg (κ₁ := κ₁) (β := β) (δ := δ) R hSB hV hm hβ.le hδ1' rfl hC₀ hCK hCD H
  have F2 := F2_rg (β := β) (δ := δ) R hSB hV hm hβ.le hδ1' H hF2
  have F1 := hF1 L hL8 hLp N R C₀ η εs CK C₂ CD Cq' Cl' cS' hSB hA2 Nh hV hm ((L : ℝ) ^ 2) β δ
    ((1 + κ₁) / 2) cg cm cT ε H hβ hδ1 hcgβ hcR1 hk1 KB E0 E1 eA eB hKB heA heB HS HD HV hs1 hs2 hs3
    hband hcg3
  obtain ⟨cG, cmm, cT'⟩ := rgData_cont R hV hc
  exact flow_of_rg A a hΛ hβ hδ0 hδ1 hκ0 hκ₁ hcg hcm hcT hA hC0 hCc H.hε H.hε1 hsmall hCa he ha0
    (fun j _ => causal_G R j) (fun j _ => causal_m R j) (fun j _ => causal_T R j) cG cmm cT'
    F1 F2 LG Lm Hb HL


end

end Step2
