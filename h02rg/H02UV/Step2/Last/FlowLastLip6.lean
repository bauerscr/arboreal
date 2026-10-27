import Step2.Last.FlowLastLip5

/-!
# The Lipschitz hypotheses including the step `N_h` under `ValidAtL` (namespace `Step2.LL`)

`lip_rg_z2`: `lip_rg_z` (same statement, same structure of constants) with one more conclusion:
if `ValidAtL R N_h` and `m² L^{2(N_h+1)} ≤ 1`, the bounds (LGd), (Lmz), (LZ) hold also at the step
`j = N_h` (e.g. `N_h = N - 2`), with the same `C_L`, together with the bound on the zero mode
entering the step `N_h + 1` (`lip_pair_top`). The coupling-remainder constants are chosen to
serve both `cmp_kap`/`size_rem` and their `ValidAtL` versions (`cmp_kap_both`, `size_rem_both`),
and the covariance differences come from one application of `prop_C5_lip` (`LL.CvH_sub_good`).
-/

namespace Step2.LL

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

theorem mono_aux1 {Cq Cl cS Cq' Cl' cS' X k : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl) (hcS : 0 ≤ cS)
    (h1 : Cq ≤ Cq') (h2 : Cl ≤ Cl') (h3 : cS ≤ cS') (hX : 0 ≤ X) (hk : 0 ≤ k) :
    Cq * X * (cS * (Cl * k)) ≤ Cq' * X * (cS' * (Cl' * k)) := by
  have b1 : Cl * k ≤ Cl' * k := mul_le_mul_of_nonneg_right h2 hk
  have b2 : cS * (Cl * k) ≤ cS' * (Cl' * k) :=
    mul_le_mul h3 b1 (mul_nonneg hCl hk) (hcS.trans h3)
  have b3 : Cq * X ≤ Cq' * X := mul_le_mul_of_nonneg_right h1 hX
  exact mul_le_mul b3 b2 (mul_nonneg hcS (mul_nonneg hCl hk)) (mul_nonneg (hCq.trans h1) hX)

theorem mono_aux2 {Cq Cl Cq' Cl' X Y : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (h1 : Cq ≤ Cq') (h2 : Cl ≤ Cl') (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Cq * X * (Cl * Y) ≤ Cq' * X * (Cl' * Y) := by
  have b1 : Cl * Y ≤ Cl' * Y := mul_le_mul_of_nonneg_right h2 hY
  have b3 : Cq * X ≤ Cq' * X := mul_le_mul_of_nonneg_right h1 hX
  exact mul_le_mul b3 b1 (mul_nonneg hCl hY) (mul_nonneg (hCq.trans h1) hX)

/-- `bRem` is monotone in its constants `C_q, C_l, c_S`. -/
theorem bRem_le_C {Cq Cl cS Cq' Cl' cS' ℓ ℓ' ℓC v w k : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (h1 : Cq ≤ Cq') (h2 : Cl ≤ Cl') (h3 : cS ≤ cS') (hw : 0 ≤ w) (hk : 0 ≤ k) :
    bRem L Cq Cl cS ℓ ℓ' ℓC v w k ≤ bRem L Cq' Cl' cS' ℓ ℓ' ℓC v w k := by
  have hσ := BHsig_nonneg (L := L) (v := v) hw
  have hY : 0 ≤ (L : ℝ) ^ 2 * BH.sig 2 L v w := mul_nonneg (by positivity) hσ
  unfold bRem
  have a1 := mono_aux1 hCq hCl hcS h1 h2 h3 (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ ℓ ^ 2)) hk
  have a2 := mono_aux1 hCq hCl hcS h1 h2 h3 (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ ℓ ^ 4)) hk
  have a3 := mono_aux2 hCq hCl h1 h2 (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ ℓ' ^ 2)) hY
  have a4 := mono_aux2 hCq hCl h1 h2 (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ ℓ' ^ 4)) hY
  have a5 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a2 (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ℓC)
  linarith

/-- The comparison of `Cmp` (weak validity at `k`) with `Step2.Cmp`, given `ValidAt R k`. -/
theorem Cmp.toOld {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ}
    {t t' : Hist.Seq (Xs R)} {Λ κ cm cT ε cz cw e ℓΔ : ℝ}
    (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ) (hk : ValidAt R k) :
    Step2.Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ :=
  ⟨⟨fun i hi => (lt_or_eq_of_le hi).elim (H.H.hV i) (fun h => h ▸ hk), H.H.hD, H.H.hA, H.H.hcz,
      H.H.hρ, H.H.h16⟩,
    ⟨fun i hi => (lt_or_eq_of_le hi).elim (H.H'.hV i) (fun h => h ▸ hk), H.H'.hD, H.H'.hA,
      H.H'.hcz, H.H'.hρ, H.H'.h16⟩, H.hm, H.hcw, H.hcx, H.hcmu, H.hε1, H.hΔ, H.he, H.he1,
    H.he2, H.he3, H.hℓΔ, H.hC⟩

set_option maxHeartbeats 1000000 in
/-- **The coupling remainders, both versions with common constants.** -/
theorem cmp_kap_both : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L → 2 ^ (2 + 4) + 4 < L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], 2 ≤ R.A →
    ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ),
      (Step2.Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ → e ≤ 1 / 2 →
      ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)) ∧
      (Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ → e ≤ 1 / 2 →
      ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := Step2.cmp_kap
  obtain ⟨Cq', hCq', Cl', hCl', cS', hcS', h'⟩ := LL.cmp_kap
  refine ⟨max Cq Cq', le_max_of_le_left hCq, max Cl Cl', le_max_of_le_left hCl, max cS cS',
    le_max_of_le_left hcS, fun L _ hL8 hLp hLg N R _ _ hA2 k t t' Λ κ cm cT ε cz cw e ℓΔ =>
      ⟨fun H he i => ?_, fun H he i => ?_⟩⟩
  · refine (h L hL8 hLp N R hA2 k t t' Λ κ cm cT ε cz cw e ℓΔ H he i).trans ?_
    have hr := relDist_nonneg (ℓΔ := ℓΔ) (τ := 1) (ℓC := R.ℓ / 4) H.he H.aIn_nonneg
      (add_nonneg H.bWIn_nonneg H.bDIn_nonneg) H.cIn_nonneg
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bRem_le_C hCq hCl (by linarith)
      (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) (by positivity) (by positivity))
      (by norm_num)) hr
  · refine (h' L hL8 hLp N R hA2 k t t' Λ κ cm cT ε cz cw e ℓΔ H he i).trans ?_
    have hr := relDist_nonneg (ℓΔ := ℓΔ) (τ := 1) (ℓC := R.ℓ / 4) H.he H.aIn_nonneg
      (add_nonneg H.bWIn_nonneg H.bDIn_nonneg) H.cIn_nonneg
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bRem_le_C hCq' hCl'
      (by linarith) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (by positivity)
      (by positivity)) (by norm_num)) hr

set_option maxHeartbeats 1000000 in
/-- **The size of the coupling remainder, both versions with common constants.** -/
theorem size_rem_both : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L → 2 ^ (2 + 4) + 4 < L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], 2 ≤ R.A →
    ∀ (k : ℕ) (t : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw : ℝ),
      (Step2.DomH k t Λ κ cm cT ε cz cw →
      |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 → 0 ≤ cw → 0 ≤ cx κ cT → 0 ≤ cmu Λ cm → (t k).1 ≤ 1 →
      cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 →
      cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 ≤ 1 →
      Real.exp 1 * (cx κ cT * (t k).1 ^ 3) ≤ 1 →
      ∀ i : Fin 4, cwt L k i * ‖kapH R k t i - SD.shv R k (sdH R k t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t k).1 ^ 3))) ∧
      (DomH k t Λ κ cm cT ε cz cw →
      |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1 → 0 ≤ cw → 0 ≤ cx κ cT → 0 ≤ cmu Λ cm → (t k).1 ≤ 1 →
      cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 →
      cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1 ≤ 1 →
      Real.exp 1 * (cx κ cT * (t k).1 ^ 3) ≤ 1 →
      ∀ i : Fin 4, cwt L k i * ‖kapH R k t i - SD.shv R k (sdH R k t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t k).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t k).1 ^ 3))) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := Step2.size_rem
  obtain ⟨Cq', hCq', Cl', hCl', cS', hcS', h'⟩ := LL.size_rem
  refine ⟨max Cq Cq', le_max_of_le_left hCq, max Cl Cl', le_max_of_le_left hCl, max cS cS',
    le_max_of_le_left hcS, fun L _ hL8 hLp hLg N R _ _ hA2 k t Λ κ cm cT ε cz cw =>
      ⟨fun H hm hcw hcx hcmu hg1 hΔ hr hk i => ?_, fun H hm hcw hcx hcmu hg1 hΔ hr hk i => ?_⟩⟩
  · refine (h L hL8 hLp N R hA2 k t Λ κ cm cT ε cz cw H hm hcw hcx hcmu hg1 hΔ hr hk i).trans ?_
    exact bRem_le_C hCq hCl (by linarith) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
      (sq_nonneg _) (by have := H.g_pos; positivity)
  · refine (h' L hL8 hLp N R hA2 k t Λ κ cm cT ε cz cw H hm hcw hcx hcmu hg1 hΔ hr hk i).trans ?_
    exact bRem_le_C hCq' hCl' (by linarith) (le_max_right _ _) (le_max_right _ _)
      (le_max_right _ _) (sq_nonneg _) (by have := H.g_pos; positivity)

set_option maxHeartbeats 4000000 in
/-- **(LGd), (Lm) and (LT) for the RG map, with fading memory `(3/4)^{j-1-i}`.**

The constants `C₀K, ηK` (`cmp_K`), `C₀W` (`cmp_W`), `C₀D` (`cmp_D`), `Cqk, Clk, cSk` (`cmp_kap`),
`Cqs, Cls, cSs` (`size_rem`) are absolute; `C₂W, C₃` depend on `L`; `ζbar, Kc` on `L` and the
point family `P`; `ε₁, C₁` on `L` and `A`. The step bounds must hold with `C₀ ≥ C₀l` and
`η ≤ ηl`. The Lipschitz constant is
`C_L = cLip L ℓ b b₁ c_μ c_z c_x c_w Kc C₂W κ_W κ_K κ_D C₁ C₃ c_E` with `c_z = cZ R`,
`c_w = cW R L² cm C₂`, `c_x = cx κ cT`, `c_μ = cmu L² cm`, `c_E = cEr ℓ c_z c_w c_x c_μ`,
`κ_W = C₀W L²/L³`, `κ_K = C₀K (L²/L³ + (A/2)^{-ηK})`, `κ_D = C₀D L²/L³`,
`b = bRem L Cqk Clk cSk (7ℓ/8) ℓ (ℓ/2) 2 2 2`, `b₁ = bR1 L Cqs Cls cSs ℓ c_E c_x`. -/
theorem lip_rg_z2 : ∃ (C₀l ηl : ℝ) (L₀ : ℕ), 0 ≤ C₀l ∧ 0 < ηl ∧
    ∃ C₀K ηK C₀W C₀D Cqk Clk cSk Cqs Cls cSs : ℝ, 0 ≤ C₀K ∧ 0 < ηK ∧ 0 ≤ C₀W ∧ 0 ≤ C₀D ∧
      0 ≤ Cqk ∧ 0 ≤ Clk ∧ 1 ≤ cSk ∧ 0 ≤ Cqs ∧ 0 ≤ Cls ∧ 1 ≤ cSs ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₂W C₃ : ℝ, 0 ≤ C₂W ∧ 0 ≤ C₃ ∧
    ∀ P : PtFamily, ∃ ζbar Kc : ℝ, 0 < ζbar ∧ 0 ≤ Kc ∧ ∃ A₀ : ℝ, 2 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₁ C₁ : ℝ, 0 < ε₁ ∧ 0 ≤ C₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = P → R.A = A →
      R.ρ ≤ ζbar / 2 → 0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ (C₀ η εs CK C₂ CD Cq Cl cS : ℝ), StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS →
      C₀l ≤ C₀ → η ≤ ηl →
    ∀ (Nh : ℕ), (∀ j < Nh, ValidAt R j) →
    ∀ ϑ : ℝ, 0 ≤ ϑ → ϑ ≤ 1 → (∀ j < Nh, |R.msq| * ((L : ℝ) ^ (j + 2)) ^ 2 ≤ ϑ) →
    ∀ (β δ cg cm cT ε : ℝ), 0 ≤ β → δ ≤ 1 →
      let κ₁ := kap1 L R.A C₀ η
      let κ := (1 + κ₁) / 2
      let Λ := (L : ℝ) ^ 2
      let cz := cZ R
      let cw := cW R Λ cm C₂
      let cE := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)
      let b := bRem L Cqk Clk cSk (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2
      let b₁ := bR1 L Cqs Cls cSs R.ℓ cE (cx κ cT)
      let κW := C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)
      ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS →
      -- the smallness conditions
      2 * cz * ε ≤ 1 / 16 → cDl (7 / 8 * R.ℓ) cz * ε ≤ 1 / 4 → cE * ε ≤ 1 / 4 → cE * ε ≤ ε₁ →
      4 * cmu Λ cm * ε * R.ℓ ^ 2 ≤ 1 / 8 →
      (cE + 1) * ε * cCloW L R.ℓ b (cmu Λ cm) (cx κ cT) cw Kc C₂W κW ≤ 1 / 2 →
      ε * cSz b₁ R.ℓ ≤ R.ρ → ε * (cSz b₁ R.ℓ + cSn L b₁ cz R.ℓ (cmu Λ cm)) ≤ 1 / 16 →
      let CL := cLipW L R.ℓ b b₁ (cmu Λ cm) cz (cx κ cT) cw Kc C₂W κW
        (C₀K * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-ηK))) (C₀D * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3))
        C₁ C₃ cE
      -- (LGd)
      (∀ j < Nh, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
        ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
        |(rgData R).G j t - (rgData R).G j t' - ((t j).1 - (t' j).1)| ≤
          CL * ε * |(t j).1 - (t' j).1| +
          CL * ε * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ + CL * ε * M) ∧
      -- (Lmz)
      (∀ j < Nh, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
        ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
        |(rgData R).m j t - (rgData R).m j t'| ≤ CL * |(t j).1 - (t' j).1| +
          CL * ε * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * ε * M + 4 * ‖zetaH R j t - zetaH R j t'‖) ∧
      -- (LZ)
      (∀ j < Nh, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
        ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
        ‖zetaH R (j + 1) t - zetaH R (j + 1) t'‖ ≤
          CL * (|(t j).1 - (t' j).1| + ‖(t j).2.2 - (t' j).2.2‖) +
          CL * ε * (|(t j).2.1 - (t' j).2.1| + M)) ∧
      -- (LT)
      (∀ j < Nh, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
        ∀ M, 0 ≤ M → (∀ i < j, (3 / 4 : ℝ) ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
        ‖((rgData R).T j t).2 - ((rgData R).T j t').2‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M) ∧
        ‖((rgData R).T j t).1 - ((rgData R).T j t').1‖ ≤ κ₁ * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * ε * (‖(t j).2.2 - (t' j).2.2‖ + |(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1| + M)) ∧
      -- the step `N_h` itself, under `ValidAtL`
      (ValidAtL R Nh → |R.msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 →
        ∀ t t', InDh Λ β δ κ cg cm cT ε Nh t → InDh Λ β δ κ cg cm cT ε Nh t' →
        ∀ M, 0 ≤ M → (∀ i < Nh, (3 / 4 : ℝ) ^ (Nh - 1 - i) * dist3 (t i) (t' i) ≤ M) →
        |(rgData R).G Nh t - (rgData R).G Nh t' - ((t Nh).1 - (t' Nh).1)| ≤
          CL * ε * |(t Nh).1 - (t' Nh).1| +
          CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ + CL * ε * M ∧
        |(rgData R).m Nh t - (rgData R).m Nh t'| ≤ CL * |(t Nh).1 - (t' Nh).1| +
          CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ +
          CL * ε * M + 4 * ‖zetaH R Nh t - zetaH R Nh t'‖ ∧
        ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ ≤
          CL * (|(t Nh).1 - (t' Nh).1| + ‖(t Nh).2.2 - (t' Nh).2.2‖) +
          CL * ε * (|(t Nh).2.1 - (t' Nh).2.1| + M) ∧
        ‖nW1H R (Nh + 1) t - nW1H R (Nh + 1) t'‖ ≤
          2 * R.ℓ ^ 2 * ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ + cNW L R.ℓ b Kc * M) := by
  obtain ⟨C₀K, ηK, L₀K, hC₀K, hηK, hKs⟩ := cmp_K
  obtain ⟨C₀W, hC₀W, L₀W, hWs⟩ := cmp_W
  obtain ⟨C₀D, hC₀D, L₀D, hDs⟩ := cmp_D
  obtain ⟨Cqk, hCqk, Clk, hClk, cSk, hcSk, hks⟩ := cmp_kap_both
  obtain ⟨Cqs, hCqs, Cls, hCls, cSs, hcSs, hss⟩ := size_rem_both
  refine ⟨(2 + Real.exp 1) * max C₀K C₀D, ηK,
    max (max L₀K L₀W) (max L₀D (max (max 69 ⌈pauliL0 2⌉₊) (⌈32 * C₀W⌉₊ + 2))),
    by positivity, hηK, C₀K, ηK, C₀W, C₀D, Cqk, Clk, cSk, Cqs, Cls, cSs, hC₀K, hηK, hC₀W, hC₀D,
    hCqk, hClk, hcSk, hCqs, hCls, hcSs, ?_⟩
  intro L _ hL
  have hLK : L₀K ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLW : L₀W ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLD : L₀D ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL3 : max (max 69 ⌈pauliL0 2⌉₊) (⌈32 * C₀W⌉₊ + 2) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL49 : 69 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL3
  have hLg : 2 ^ (2 + 4) + 4 < L := by norm_num; omega
  have hLp : pauliL0 2 ≤ L := by
    have h1 : ⌈pauliL0 2⌉₊ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL3
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hLc : 32 * C₀W ≤ (L : ℝ) := by
    have h1 : ⌈32 * C₀W⌉₊ + 2 ≤ L := le_trans (le_max_right _ _) hL3
    have h2 : (⌈32 * C₀W⌉₊ : ℝ) + 2 ≤ L := by exact_mod_cast h1
    linarith [Nat.le_ceil (32 * C₀W)]
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  obtain ⟨C₂W, hC₂W, hWs⟩ := hWs L hLW
  obtain ⟨C₃, hC₃, hDs⟩ := hDs L hLD
  obtain ⟨A₀, hA₀, hKs⟩ := hKs L hLK
  refine ⟨C₂W, C₃, hC₂W, hC₃, fun P => ?_⟩
  obtain ⟨ζbar, hζ, -, Kc, hKc, hcov⟩ :=
    LL.CvH_sub_good (L := L) P (by omega) (ρc := 1 / 2) (by norm_num) le_rfl
  refine ⟨ζbar, Kc, hζ, hKc, max A₀ 2, le_max_right _ _, fun A hA => ?_⟩
  obtain ⟨ε₁, C₁, hε₁, hC₁, hKs⟩ := hKs A (le_trans (le_max_left _ _) hA)
  refine ⟨ε₁, C₁, hε₁, hC₁, ?_⟩
  intro N R _ _ hP hRA hρζ hm0 hm1 C₀ η εs CK C₂ CD Cq Cl cS hSB hC₀ hη Nh hV ϑ hϑ0 hϑ1 hmϑ
    β δ cg cm cT ε hβ hδ1 κ₁ κ Λ cz cw cE b b₁ κW H h16 hΔ hE1 hE2 hnd hclo hsz1 hsz2 CL
  have hℓ : 0 < R.ℓ := Fact.out
  have hA2 : 2 ≤ R.A := hRA ▸ le_trans (le_max_right _ _) hA
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := fun j hj => by
    have h1 := hmϑ j hj
    have h2 : ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ (j + 2)) ^ 2 := by
      have : (L : ℝ) ^ j ≤ (L : ℝ) ^ (j + 2) := pow_le_pow_right₀ hL1 (by omega)
      gcongr
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg R.msq)
    linarith
  have hAP := apriori R hSB hV hm hβ hδ1 H
  have hcz : 0 ≤ cz := by
    show 0 ≤ cZ R
    unfold cZ; positivity
  have hcw : 0 ≤ cw := by
    show 0 ≤ cW R Λ cm C₂
    unfold cW; have := H.hC₂; positivity
  have hLL : (L : ℝ) ^ 2 / (L : ℝ) ^ 3 = (L : ℝ)⁻¹ := by
    field_simp
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) hC₀
  have hmax : (2 + Real.exp 1) * C₀K ≤ C₀ ∧ (2 + Real.exp 1) * C₀D ≤ C₀ := by
    have he : 0 ≤ 2 + Real.exp 1 := by positivity
    exact ⟨le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) he) hC₀,
      le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) he) hC₀⟩
  have hrp : (A / 2) ^ (-ηK) ≤ (R.A / 2) ^ (-η) := by
    rw [hRA]
    exact Real.rpow_le_rpow_of_exponent_le (by rw [← hRA]; linarith) (by linarith)
  have hrp0 : 0 ≤ (A / 2) ^ (-ηK) := Real.rpow_nonneg (by rw [← hRA]; linarith) _
  have hrp0' : 0 ≤ (R.A / 2) ^ (-η) := Real.rpow_nonneg (by linarith) _
  have hκ₁ : 8 * (2 + Real.exp 1) * (C₀K * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-ηK))) ≤ κ₁ := by
    show _ ≤ 8 * C₀ * ((L : ℝ)⁻¹ + (R.A / 2) ^ (-η))
    rw [hLL]
    have hX : (L : ℝ)⁻¹ + (A / 2) ^ (-ηK) ≤ (L : ℝ)⁻¹ + (R.A / 2) ^ (-η) := by linarith
    have h1 := mul_le_mul hmax.1 hX (by positivity) hC₀0
    linarith
  have hκ₁' : 8 * (2 + Real.exp 1) * (C₀D * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) ≤ κ₁ := by
    show _ ≤ 8 * C₀ * ((L : ℝ)⁻¹ + (R.A / 2) ^ (-η))
    rw [hLL]
    have hX : (L : ℝ)⁻¹ ≤ (L : ℝ)⁻¹ + (R.A / 2) ^ (-η) := by linarith
    have h1 := mul_le_mul hmax.2 hX (by positivity) hC₀0
    linarith
  have hq : 8 * (C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2) ≤ 1 / 2 := by
    rw [hLL]
    have h49 : (49 : ℝ) ≤ L := by exact_mod_cast (show 49 ≤ L by omega)
    have a1 : 8 * (C₀W * (L : ℝ)⁻¹) ≤ 1 / 4 := by
      rw [← div_eq_mul_inv, ← mul_div_assoc, div_le_iff₀ hLr]; linarith
    have a2 : 9 / (8 * (L : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hP' := lip_pair_z (R := R) hV hϑ0 hϑ1 hmϑ (Λ := Λ) (β := β) (δ := δ) (κ := κ) (cg := cg)
    (cm := cm) (cT := cT) (ε := ε) (cz := cz) (cw := cw) (Kc := Kc) hAP
    (fun k hval t t' => hcov N R hP hρζ hm0 hm1 k (fun i hi => hval i hi.le)
      ((hval k le_rfl).toValidAtL hLg) t t')
    (ε₁ := ε₁) (κ₁ := κ₁)
    (fun k t t' e ℓΔ Hc he => hKs N R hRA k t t' _ _ _ _ _ _ _ e ℓΔ Hc he hL8 R.ℓ hℓ
      (by linarith))
    (fun k t t' e ℓΔ Hc he => hDs N R k t t' _ _ _ _ _ _ _ e ℓΔ Hc he hL8 R.ℓ hℓ (by linarith))
    (fun k t t' e ℓΔ Hc he => hWs N R k t t' _ _ _ _ _ _ _ e ℓΔ Hc he hL8 H.hε)
    (fun k t t' e ℓΔ Hc he i => (hks L hL8 hLp hLg N R hA2 k t t' _ _ _ _ _ _ _ e ℓΔ).1 Hc he i)
    (fun k t Hd hmk hg1 hΔk hr hk i => (hss L hL8 hLp hLg N R hA2 k t _ _ _ _ _ _ _).1 Hd hmk hcw
      H.hcx H.hcmu hg1 hΔk hr hk i)
    hcz hcw H.hcx H.hcmu hKc (by positivity) (by positivity) hC₁ hC₃ hC₂W hC₀W hCqk hClk
    (by linarith) hCqs hCls (by linarith) (by omega) hq hκ₁ hκ₁' H.hε H.hε1 H.h1 h16 hΔ hE1 hE2
    hnd hclo hsz1 hsz2
  refine ⟨fun j hj t t' ht ht' M hM hd => (hP' j hj t t' ht ht' M hM hd).2.1,
    fun j hj t t' ht ht' M hM hd => (hP' j hj t t' ht ht' M hM hd).2.2.1,
    fun j hj t t' ht ht' M hM hd => (hP' j hj t t' ht ht' M hM hd).2.2.2,
    fun j hj t t' ht ht' M hM hd => (hP' j hj t t' ht ht' M hM hd).1, fun hVL hmN => ?_⟩
  exact lip_pair_top (R := R) hV hVL hmN (Λ := Λ) (β := β) (δ := δ) (κ := κ) (cg := cg)
    (cm := cm) (cT := cT) (ε := ε) (cz := cz) (cw := cw) (Kc := Kc) (κK := C₀K * ((L : ℝ) ^ 2 /
      (L : ℝ) ^ 3 + (A / 2) ^ (-ηK))) (κD := C₀D * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) (C₁ := C₁)
    (C₃ := C₃) hAP
    (fun k hk t t' => hcov N R hP hρζ hm0 hm1 k (fun i hi => hV i (by omega))
      (by
        rcases lt_or_eq_of_le hk with h | h
        · exact (hV k h).toValidAtL hLg
        · exact h ▸ hVL) t t')
    (fun k hk t t' e ℓΔ Hc he => hWs N R k t t' _ _ _ _ _ _ _ e ℓΔ
      (Hc.toOld ((hV k hk))) he hL8 H.hε)
    (fun k t t' e ℓΔ Hc he i => (hks L hL8 hLp hLg N R hA2 k t t' _ _ _ _ _ _ _ e ℓΔ).2 Hc he i)
    (fun k t Hd hmk hg1 hΔk hr hk i => (hss L hL8 hLp hLg N R hA2 k t _ _ _ _ _ _ _).2 Hd hmk hcw
      H.hcx H.hcmu hg1 hΔk hr hk i)
    hcz hcw H.hcx H.hcmu hKc (by positivity) (by positivity) hC₁ hC₃ hC₂W hC₀W hCqk hClk
    (by linarith) hCqs hCls (by linarith) (by omega) hq H.hε H.hε1 H.h1 h16 hΔ hE1 hnd hclo
    hsz1 hsz2

end

end Step2.LL
