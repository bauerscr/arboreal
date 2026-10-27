import Step2.Lip.FlowLipPair
import Step2.Flow.FlowMain

/-!
# The Lipschitz hypotheses (LG), (Lm), (LT) for the RG map (Lipschitz bounds, part 34)

* `StepBounds.mono`: the step bounds survive increasing `C₀` and decreasing `η` (for `A ≥ 2`);
* `lip_rg`: for `rgData R`, the hypotheses (LG), (Lm) and `Flow2.Hist.RGLip` of `Step2.flow_rg`
  hold with `A = C_L`, `a = C_L (ε + ϑ)` and the Lipschitz constant `C_L` of `lip_pair`, where
  `|m²| L^{2(j+2)} ≤ ϑ`, under explicit smallness conditions on `ε`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist

/-- **Monotonicity of the step bounds** in `C₀` (up) and `η` (down). -/
theorem StepBounds.mono {L : ℕ} [NeZero L] {A C₀ η εs CK C₂ CD Cq Cl cS C₀' η' : ℝ}
    (h : StepBounds L A C₀ η εs CK C₂ CD Cq Cl cS) (hC0 : 0 ≤ C₀) (hC : C₀ ≤ C₀') (hη : η' ≤ η) (hA : 2 ≤ A) :
    StepBounds L A C₀' η' εs CK C₂ CD Cq Cl cS := by
  intro N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 wl dd k r hwl hdd hk hW hDn hKn v hv hr
    hrε hkε
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ :=
    h N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 wl dd k r hwl hdd hk hW hDn hKn hv hr hrε hkε
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hdiv : C₀ / L ≤ C₀' / L := div_le_div_of_nonneg_right hC hL.le
  have hrp : (A / 2) ^ (-η) ≤ (A / 2) ^ (-η') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hX : (L : ℝ)⁻¹ + (A / 2) ^ (-η) ≤ (L : ℝ)⁻¹ + (A / 2) ^ (-η') := by linarith
  have hX0 : 0 ≤ (L : ℝ)⁻¹ + (A / 2) ^ (-η) :=
    add_nonneg (inv_nonneg.2 hL.le) (Real.rpow_nonneg (by linarith) _)
  refine ⟨a1, a2, a3, a4.trans (ENNReal.ofReal_le_ofReal ?_), a5.trans (ENNReal.ofReal_le_ofReal ?_),
    a6.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · have := mul_le_mul_of_nonneg_right hdiv hwl
    linarith
  · have := mul_le_mul_of_nonneg_right hdiv hdd
    linarith
  · have : 8 * C₀ * ((L : ℝ)⁻¹ + (A / 2) ^ (-η)) ≤ 8 * C₀' * ((L : ℝ)⁻¹ + (A / 2) ^ (-η')) :=
      mul_le_mul (by linarith) hX hX0 (by linarith)
    have := mul_le_mul_of_nonneg_right this hk
    linarith

set_option maxHeartbeats 4000000 in
/-- **(LG), (Lm) and (LT) for the RG map.**

The constants `C₀K, ηK` (`cmp_K`), `C₀W` (`cmp_W`), `C₀D` (`cmp_D`), `Cqk, Clk, cSk` (`cmp_kap`),
`Cqs, Cls, cSs` (`size_rem`) are absolute; `C₂W, C₃` depend on `L`; `ζbar, Kc` on `L` and the
point family `P`; `ε₁, C₁` on `L` and `A`. The step bounds must hold with `C₀ ≥ C₀l` and
`η ≤ ηl`. The Lipschitz constant is
`C_L = cLip L ℓ b b₁ c_μ c_z c_x c_w Kc C₂W κ_W κ_K κ_D C₁ C₃ c_E` with `c_z = cZ R`,
`c_w = cW R L² cm C₂`, `c_x = cx κ cT`, `c_μ = cmu L² cm`, `c_E = cEr ℓ c_z c_w c_x c_μ`,
`κ_W = C₀W L²/L³`, `κ_K = C₀K (L²/L³ + (A/2)^{-ηK})`, `κ_D = C₀D L²/L³`,
`b = bRem L Cqk Clk cSk (7ℓ/8) ℓ (ℓ/2) 2 2 2`, `b₁ = bR1 L Cqs Cls cSs ℓ c_E c_x`. -/
theorem lip_rg : ∃ (C₀l ηl : ℝ) (L₀ : ℕ), 0 ≤ C₀l ∧ 0 < ηl ∧
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
      (cE + 1) * ε * cClo L R.ℓ b (cmu Λ cm) (cx κ cT) cw Kc C₂W κW ≤ 1 / 2 →
      ε * cSz b₁ R.ℓ ≤ R.ρ → ε * (cSz b₁ R.ℓ + cSn L b₁ cz R.ℓ (cmu Λ cm)) ≤ 1 / 16 →
      let CL := cLip L R.ℓ b b₁ (cmu Λ cm) cz (cx κ cT) cw Kc C₂W κW
        (C₀K * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-ηK))) (C₀D * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3))
        C₁ C₃ cE
      -- (LG)
      (∀ j < Nh, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
        ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
        |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + CL * (ε + ϑ)) * |(t j).1 - (t' j).1| +
          CL * (ε + ϑ) * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * (ε + ϑ) * M) ∧
      -- (Lm)
      (∀ j < Nh, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
        ∀ M, 0 ≤ M → (∀ i < j, dist3 (t i) (t' i) ≤ M) →
        |(rgData R).m j t - (rgData R).m j t'| ≤ CL * |(t j).1 - (t' j).1| +
          CL * (ε + ϑ) * |(t j).2.1 - (t' j).2.1| + CL * ‖(t j).2.2 - (t' j).2.2‖ +
          CL * (ε + ϑ) * M) ∧
      -- (LT)
      RGLip (rgData R) Λ β δ κ₁ CL cg cm cT ε Nh := by
  obtain ⟨C₀K, ηK, L₀K, hC₀K, hηK, hKs⟩ := cmp_K
  obtain ⟨C₀W, hC₀W, L₀W, hWs⟩ := cmp_W
  obtain ⟨C₀D, hC₀D, L₀D, hDs⟩ := cmp_D
  obtain ⟨Cqk, hCqk, Clk, hClk, cSk, hcSk, hks⟩ := cmp_kap
  obtain ⟨Cqs, hCqs, Cls, hCls, cSs, hcSs, hss⟩ := size_rem
  refine ⟨(2 + Real.exp 1) * max C₀K C₀D, ηK,
    max (max L₀K L₀W) (max L₀D (max (max 49 ⌈pauliL0 2⌉₊) (⌈32 * C₀W⌉₊ + 2))),
    by positivity, hηK, C₀K, ηK, C₀W, C₀D, Cqk, Clk, cSk, Cqs, Cls, cSs, hC₀K, hηK, hC₀W, hC₀D,
    hCqk, hClk, hcSk, hCqs, hCls, hcSs, ?_⟩
  intro L _ hL
  have hLK : L₀K ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLW : L₀W ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLD : L₀D ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL3 : max (max 49 ⌈pauliL0 2⌉₊) (⌈32 * C₀W⌉₊ + 2) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL49 : 49 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL3
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
    CvH_sub_good (L := L) P (by omega) (ρc := 1 / 2) (by norm_num) le_rfl
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
    have h49 : (49 : ℝ) ≤ L := by exact_mod_cast hL49
    have a1 : 8 * (C₀W * (L : ℝ)⁻¹) ≤ 1 / 4 := by
      rw [← div_eq_mul_inv, ← mul_div_assoc, div_le_iff₀ hLr]; linarith
    have a2 : 9 / (8 * (L : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hP' := lip_pair (R := R) hV hϑ0 hϑ1 hmϑ (Λ := Λ) (β := β) (δ := δ) (κ := κ) (cg := cg)
    (cm := cm) (cT := cT) (ε := ε) (cz := cz) (cw := cw) (Kc := Kc) hAP
    (fun k hval t t' => hcov N R hP hρζ hm0 hm1 k hval t t')
    (ε₁ := ε₁) (κ₁ := κ₁)
    (fun k t t' e ℓΔ Hc he => hKs N R hRA k t t' _ _ _ _ _ _ _ e ℓΔ Hc he hL8 R.ℓ hℓ
      (by linarith))
    (fun k t t' e ℓΔ Hc he => hDs N R k t t' _ _ _ _ _ _ _ e ℓΔ Hc he hL8 R.ℓ hℓ (by linarith))
    (fun k t t' e ℓΔ Hc he => hWs N R k t t' _ _ _ _ _ _ _ e ℓΔ Hc he hL8 H.hε)
    (fun k t t' e ℓΔ Hc he i => hks L hL8 hLp N R hA2 k t t' _ _ _ _ _ _ _ e ℓΔ Hc he i)
    (fun k t Hd hmk hg1 hΔk hr hk i => hss L hL8 hLp N R hA2 k t _ _ _ _ _ _ _ Hd hmk hcw H.hcx
      H.hcmu hg1 hΔk hr hk i)
    hcz hcw H.hcx H.hcmu hKc (by positivity) (by positivity) hC₁ hC₃ hC₂W hC₀W hCqk hClk
    (by linarith) hCqs hCls (by linarith) (by omega) hq hκ₁ hκ₁' H.hε H.hε1 H.h1 h16 hΔ hE1 hE2
    hnd hclo hsz1 hsz2
  refine ⟨fun j hj t t' ht ht' M hM hd => (hP' j hj t t' ht ht' M hM hd).2.1,
    fun j hj t t' ht ht' M hM hd => (hP' j hj t t' ht ht' M hM hd).2.2,
    fun j hj t t' ht ht' M hM hd => (hP' j hj t t' ht ht' M hM hd).1⟩


end

end Step2
