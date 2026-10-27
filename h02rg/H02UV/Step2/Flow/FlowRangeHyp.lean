import Step2.Flow.FlowSharp2

/-!
# The hypotheses of the sharp range for the RG map

`flow_range_hyp`: the proof of `thm_flow_sharp` (`Step2/Flow/FlowSharp2.lean`), stopped before the
application of `fh_flow_hist`. It exports the hypothesis package of `prop:C6` for `rgData`
(`HHyp`, the smallness `ε ≤ eps0u`, `a ≤ a0h`) together with the sharp (F1)
`|G_j - g - β g²| ≤ e_j g² + c_g g³` on regular histories, with `e_j ≤ β/2` and, for `j ≥ 1`,
`e_j ≤ K_e (L^{-2j} + m² L^{2(j+1)})`, and the additional smallness `c_g ε ≤ β/4`.
These are the inputs of the abstract sharp range `Flow2.Hist.fh_flow_range`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

set_option maxHeartbeats 20000000 in
/-- **The hypothesis package of the sharp range for the RG map.** -/
theorem flow_range_hyp : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ ϑ κ cg cm cT ε Ke : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ϑ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ cg * ε ≤ betaL L / 4 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ ϑ →
      ∃ (Ah ah : ℝ) (e : ℕ → ℝ),
        HHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh Ah ah ε ∧
        ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧ ah ≤ a0h ((L : ℝ) ^ 2) κ Ah ∧
        (∀ j, 0 ≤ e j) ∧
        (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
          |(rgData R).G j t - (t j).1 - betaL L * (t j).1 ^ 2| ≤
            e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) ∧
        (∀ j < Nh, e j ≤ 1 / 2 * betaL L) ∧
        (∀ j, 1 ≤ j → e j ≤ Ke * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2)) := by
  obtain ⟨C₀s, ηs, L₀s, hC₀s, hηs, hSBs⟩ := rg_step_bounds
  obtain ⟨C₀l, ηl, L₀l, hC₀l, hηl, C₀K, ηK, C₀W, C₀D, Cqk, Clk, cSk, Cqs, Cls, cSs, hC₀K, hηK,
    hC₀W, hC₀D, hCqk, hClk, hcSk, hCqs, hCls, hcSs, hLip⟩ := lip_rg
  obtain ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, hF1⟩ := F1_rg_sharp
  obtain ⟨E0, hE0, hHV⟩ := HV_hist
  obtain ⟨M₀, M₂, hM₀, hM₂, hS01⟩ := S01_hist
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = max C₀s C₀l := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = min ηs ηl := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := hC₀ ▸ le_max_of_le_left hC₀s
  have hη0 : 0 < η := hη ▸ lt_min hηs hηl
  obtain ⟨C0, hC0d⟩ : ∃ C0, C0 = max C0sh 0 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C0 := hC0d ▸ le_max_right _ _
  have hC0sh : C0sh ≤ C0 := hC0d ▸ le_max_left _ _
  obtain ⟨Lb, hLbd⟩ : ∃ Lb : ℝ, Lb = Real.exp (4 * Real.pi / 3 * (E0 + 2 * C0 + 1)) :=
    ⟨_, rfl⟩
  refine ⟨max (max L₀s L₀l) (max 49 (max ⌈pauliL0 2⌉₊ (max (⌈32 * C₀ + 1⌉₊) (⌈Lb⌉₊)))),
    fun L _ hL => ?_⟩
  have hLs : L₀s ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLl : L₀l ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL' := le_trans (le_max_right _ _) hL
  have hL49 : 49 ≤ L := le_trans (le_max_left _ _) hL'
  have hL'' := le_trans (le_max_right _ _) hL'
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_left _ _) hL'')
  have hL''' := le_trans (le_max_right _ _) hL''
  have hL32 : 32 * C₀ + 1 ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_left _ _) hL''')
  have hLb : Lb ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL''')
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  -- the band
  have hβ0 : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
    positivity
  have hband0 : E0 + 2 * C0 + 1 ≤ 1 / 2 * betaL L := by
    have hlog : Real.log Lb ≤ Real.log L :=
      Real.log_le_log (by rw [hLbd]; exact Real.exp_pos _) hLb
    rw [hLbd, Real.log_exp] at hlog
    unfold betaL
    have hpi := Real.pi_pos
    rw [show 1 / 2 * (3 * (Real.log L / (2 * Real.pi))) = 3 / (4 * Real.pi) * Real.log L by
      field_simp; ring]
    have : E0 + 2 * C0 + 1 = 3 / (4 * Real.pi) * (4 * Real.pi / 3 * (E0 + 2 * C0 + 1)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  -- the constants at scale `L`
  obtain ⟨A₀s, hA₀s, hSBA⟩ := hSBs L hLs
  obtain ⟨C₂W, C₃, hC₂W, hC₃, hLipP⟩ := hLip L hLl
  obtain ⟨ζl, Kc, hζl, hKc, A₀l, hA₀l, hLipA⟩ := hLipP Pc
  obtain ⟨ζHV, hζHV, E1, hE1, hHVL⟩ := hHV L hL49
  obtain ⟨ζHVs, hζHVs, E1s, hE1s, hHVsL⟩ := HVs_hist L hL49
  obtain ⟨ζHD, hζHD, KB, hKB, hHDL⟩ := HD_hist L hL49
  obtain ⟨ζS, hζS, hS01L⟩ := hS01 L hL49
  obtain ⟨ℓ, hℓ, ζv, hζv, hζv8, hVal⟩ := validAt_concrete (L := L) Pc hL8
  obtain ⟨ζc, hζc, hCov⟩ := covCont_of_small (d := 2) (L := L) Pc le_rfl (by omega)
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = max (max A₀s A₀l) (2 * (32 * C₀ + 1) ^ η⁻¹) := ⟨_, rfl⟩
  have hAs : A₀s ≤ A := hAd ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hAl : A₀l ≤ A := hAd ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hAκ : 2 * (32 * C₀ + 1) ^ η⁻¹ ≤ A := hAd ▸ le_max_right _ _
  have hA2 : 2 ≤ A := hA₀l.trans hAl
  have hA0 : 0 < A := by linarith
  obtain ⟨εs, CK, C₂, CD, Cq', Cl', cS', hεs, hCK, hC₂, hCD, hCq', hCl', hcS', hSB0⟩ := hSBA A hAs
  obtain ⟨ε₁, C₁, hε₁, hC₁, hLipR⟩ := hLipA A hAl
  have hSB := hSB0.mono hC₀s (hC₀ ▸ le_max_left _ _) (hη ▸ min_le_left _ _) hA2
  have hC₀l' : C₀l ≤ C₀ := hC₀ ▸ le_max_right _ _
  have hηl' : η ≤ ηl := hη ▸ min_le_right _ _
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = min (min (ζl / 2) (min ζHV ζHVs)) (min (min ζHD ζS) (min ζv (ζc / 2))) :=
    ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρd]; positivity
  have hρl : ρ ≤ ζl / 2 := hρd ▸ le_trans (min_le_left _ _) (min_le_left _ _)
  have hρHV : ρ ≤ ζHV :=
    hρd ▸ le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρHVs : ρ ≤ ζHVs :=
    hρd ▸ le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρHD : ρ ≤ ζHD := hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρS : ρ ≤ ζS := hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρv : ρ ≤ ζv := hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρc : ρ < ζc := by
    have : ρ ≤ ζc / 2 := hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  have hρ8 : ρ ≤ 1 / 8 := hρv.trans hζv8
  -- `κ₁ ≤ 1/2`
  obtain ⟨κ₁, hκ₁d⟩ : ∃ κ₁, κ₁ = kap1 L A C₀ η := ⟨_, rfl⟩
  have hκ₁h : κ₁ ≤ 1 / 2 := hκ₁d ▸ kap1_le_half hC₀0 hη0 hL32 hAκ
  have hκ₁0 : 0 ≤ κ₁ := hκ₁d ▸ kap1_nonneg hC₀0 hA0
  -- the reference parameters
  obtain ⟨R₀, hR₀ℓ⟩ : ∃ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ := ⟨⟨Pc, 0, ℓ, A, 0, ρ⟩, rfl⟩
  have hΛ : (1 : ℝ) < (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
    nlinarith
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = (1 + κ₁) / 2 := ⟨_, rfl⟩
  have hκ1 : κ < 1 := by rw [hκd]; linarith
  have hκ0 : 0 ≤ κ := by rw [hκd]; linarith
  obtain ⟨cz, hczd⟩ : ∃ cz, cz = cZ R₀ := ⟨_, rfl⟩
  have hcz : 0 ≤ cz := by rw [hczd]; unfold cZ; positivity
  obtain ⟨cm, hcmd⟩ : ∃ cm, cm = cF2 R₀ + 1 := ⟨_, rfl⟩
  have hcm : 0 < cm := by
    rw [hcmd]; unfold cF2 cZ; positivity
  obtain ⟨cmuv, hcmud⟩ : ∃ cmuv, cmuv = cmu ((L : ℝ) ^ 2) cm := ⟨_, rfl⟩
  have hcmu : 0 < cmuv := by rw [hcmud]; unfold cmu; have := sub_pos.2 hΛ; positivity
  obtain ⟨Cb, hCbd⟩ : ∃ Cb, Cb = cB R₀ ((L : ℝ) ^ 2) cm C₂ CK CD := ⟨_, rfl⟩
  have hCb : 0 ≤ Cb := by
    rw [hCbd]; unfold cB; exact le_max_of_le_left (by positivity)
  obtain ⟨cT, hcTd⟩ : ∃ cT, cT = Cb + 1 := ⟨_, rfl⟩
  have hcT : 0 < cT := by rw [hcTd]; linarith
  obtain ⟨cxv, hcxd⟩ : ∃ cxv, cxv = cx κ cT := ⟨_, rfl⟩
  have hcx : 0 ≤ cxv := by rw [hcxd]; unfold cx; have := sub_pos.2 hκ1; positivity
  obtain ⟨cV0, hcV0d⟩ : ∃ c, c = cV R₀ ((L : ℝ) ^ 2) cm := ⟨_, rfl⟩
  have hcV0 : 0 ≤ cV0 := by
    rw [hcV0d]; unfold cV cZ; have := hcmud ▸ hcmu.le; positivity
  obtain ⟨cw, hcwd⟩ : ∃ c, c = cW R₀ ((L : ℝ) ^ 2) cm C₂ := ⟨_, rfl⟩
  have hcw : 0 ≤ cw := by rw [hcwd]; unfold cW; rw [← hcV0d]; positivity
  -- the (F1) constants
  obtain ⟨ϑ₀, hϑ₀d⟩ : ∃ ϑ₀ : ℝ, ϑ₀ = (L : ℝ) ^ 4 / (32 / 7 * (16 / 7) * cz * (M₀ + 1) + 1) :=
    ⟨_, rfl⟩
  have hϑ₀ : 0 < ϑ₀ := by rw [hϑ₀d]; positivity
  obtain ⟨eA, heAd⟩ : ∃ eA, eA = 16 / 7 * cz * (M₀ + 1) * (ϑ₀ / (L : ℝ) ^ 4) := ⟨_, rfl⟩
  have heA : 0 ≤ eA := by rw [heAd]; positivity
  have heA1 : 32 / 7 * eA ≤ 1 := by
    rw [heAd, hϑ₀d]
    have hX : 0 ≤ 32 / 7 * (16 / 7) * cz * (M₀ + 1) := by positivity
    have hL4 : (0 : ℝ) < (L : ℝ) ^ 4 := by positivity
    rw [show 32 / 7 * (16 / 7 * cz * (M₀ + 1) * ((L : ℝ) ^ 4 /
        (32 / 7 * (16 / 7) * cz * (M₀ + 1) + 1) / (L : ℝ) ^ 4)) =
        (32 / 7 * (16 / 7) * cz * (M₀ + 1)) / (32 / 7 * (16 / 7) * cz * (M₀ + 1) + 1) by
      field_simp]
    rw [div_le_one (by linarith)]; linarith
  have hband : 1 + (E0 + 2 * C0) ≤ 1 / 2 * betaL L := by linarith only [hband0]
  obtain ⟨cRQ, hcRQd⟩ : ∃ c, c = f1cRQ Cl cS cxv := ⟨_, rfl⟩
  obtain ⟨cRL, hcRLd⟩ : ∃ c, c = f1cRL L Cl cV0 cw := ⟨_, rfl⟩
  obtain ⟨cRD, hcRDd⟩ : ∃ c, c = f1cRD L ClD cxv := ⟨_, rfl⟩
  obtain ⟨cES, hcESd⟩ : ∃ c, c = (24 * (2 * cz) + 3 * f1cn ℓ cmuv + 2 * (2 * betaL L + 1)) * KB :=
    ⟨_, rfl⟩
  obtain ⟨cg, hcgd⟩ : ∃ cg, cg = max (f1c3s L ℓ cz cmuv Cq cRQ cRL CqD cRD KB cES 1) 0 +
      (E1 + E1s) * (2 * cz) + 1 := ⟨_, rfl⟩
  have hcg : 0 < cg := by rw [hcgd]; positivity
  obtain ⟨K1, hK1d⟩ : ∃ K1, K1 = 32 / 7 * (16 / 7 * cz * (M₀ + 1)) := ⟨_, rfl⟩
  have hK1 : 0 ≤ K1 := by rw [hK1d]; positivity
  obtain ⟨Csh, hCshd⟩ : ∃ Csh, Csh = max (2 * (1 + betaL L) * (K1 + C0)) (Cgu (betaL L) cg) :=
    ⟨_, rfl⟩
  have hCsh1 : 2 * (1 + betaL L) * (K1 + C0) ≤ Csh := hCshd ▸ le_max_left _ _
  have hCsh2 : Cgu (betaL L) cg ≤ Csh := hCshd ▸ le_max_right _ _
  have hCsh0 : 0 ≤ Csh := le_trans (by positivity) hCsh1
  -- the Lipschitz constants
  obtain ⟨cEl, hcEld⟩ : ∃ c, c = cEr ℓ cz cw cxv cmuv := ⟨_, rfl⟩
  obtain ⟨bb, hbbd⟩ : ∃ c, c = bRem L Cqk Clk cSk (7 / 8 * ℓ) ℓ ((1 + 1) * (ℓ / 4)) 2 2 2 := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁d⟩ : ∃ c, c = bR1 L Cqs Cls cSs ℓ cEl cxv := ⟨_, rfl⟩
  obtain ⟨κW, hκWd⟩ : ∃ c, c = C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) := ⟨_, rfl⟩
  obtain ⟨CL, hCLd⟩ : ∃ c, c = cLip L ℓ bb b₁ cmuv cz cxv cw Kc C₂W κW
      (C₀K * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-ηK))) (C₀D * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3))
      C₁ C₃ cEl := ⟨_, rfl⟩
  obtain ⟨CLp, hCLpd⟩ : ∃ c, c = max CL 0 := ⟨_, rfl⟩
  have hCLp : 0 ≤ CLp := hCLpd ▸ le_max_right _ _
  have hCLle : CL ≤ CLp := hCLpd ▸ le_max_left _ _
  obtain ⟨a0, ha0d⟩ : ∃ a0, a0 = a0h ((L : ℝ) ^ 2) κ CLp := ⟨_, rfl⟩
  have ha0 : 0 < a0 := ha0d ▸ a0h_pos hΛ hκ1 hCLp
  obtain ⟨ϑ, hϑd⟩ : ∃ ϑ : ℝ, ϑ = min 1 (min ϑ₀ (a0 / (2 * (CLp + Cb) + 1))) := ⟨_, rfl⟩
  have hϑ0 : 0 < ϑ := by rw [hϑd]; exact lt_min one_pos (lt_min hϑ₀ (by positivity))
  have hϑ1 : ϑ ≤ 1 := hϑd ▸ min_le_left _ _
  have hϑϑ₀ : ϑ ≤ ϑ₀ := hϑd ▸ le_trans (min_le_right _ _) (min_le_left _ _)
  have hϑa : (CLp + Cb) * ϑ ≤ a0 / 2 := by
    have h1 : ϑ ≤ a0 / (2 * (CLp + Cb) + 1) := hϑd ▸ le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- `F2`
  obtain ⟨cEv, hcEvd⟩ : ∃ c, c = cE R₀ ((L : ℝ) ^ 2) κ cm cT C₂ Cq' Cl' cS' := ⟨_, rfl⟩
  obtain ⟨cRv, hcRvd⟩ : ∃ c, c = cR R₀ ((L : ℝ) ^ 2) cm C₂ := ⟨_, rfl⟩
  have hcRv : 0 ≤ cRv := by rw [hcRvd]; unfold cR; rw [← hcV0d, ← hcwd]; positivity
  have heps0 : 0 < eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm := by
    unfold eps0u
    refine lt_min (eps0_pos hβ0 hκ1 hcg) ?_
    have hb : 0 < betap (betaL L) (1 / 2) cg := by unfold betap; positivity
    have : 0 < cmu ((L : ℝ) ^ 2) cm := hcmud ▸ hcmu
    positivity
  have hκ12 : 0 < (1 - κ₁) / 2 := by linarith
  -- the choice of `ε`
  have hℓ147 : 0 < 16 * ℓ ^ 2 / 147 := by positivity
  have hβ2 : 0 < betaL L / 2 := by linarith
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (1 * ε ≤ 1 ∧ (2 * cz) * ε ≤ ρ ∧ (8 * cM * ℓ ^ 2 * cz) * ε ≤ 1 / 2 ∧ cxv * ε ≤ 1 ∧
      cRv * ε ≤ εs ∧ (8 * cxv) * ε ≤ εs ∧ cg * ε ≤ 1 / 6 ∧ cEv * ε ≤ 16 * ℓ ^ 2 / 147 ∧
      cg * ε ≤ betaL L / 2 ∧ cRv * ε ≤ 1 ∧ (8 * cxv) * ε ≤ 1) ∧
      (f1cn ℓ cmuv * ε ≤ 1 / 8 ∧ f1cn' L ℓ cz cmuv Cq cRQ cRL * ε ≤ 1 / 8 ∧
      (ℓ ^ 2 / 7 + f1cw ℓ cmuv Cq cRQ cRL) * ε ≤ ρ ∧
      (16 / 7 * (L : ℝ) ^ 2 * (8 * ℓ ^ 2 / 49 + (L : ℝ) ^ 2 * cEv) * cmuv +
        2 * ((L : ℝ) ^ 2 * cEv)) * ε ≤ 1) ∧
      ((2 * cz) * ε ≤ 1 / 16 ∧ cDl (7 / 8 * ℓ) cz * ε ≤ 1 / 4 ∧ cEl * ε ≤ 1 / 4 ∧ cEl * ε ≤ ε₁ ∧
      (4 * cmuv * ℓ ^ 2) * ε ≤ 1 / 8 ∧
      ((cEl + 1) * cClo L ℓ bb cmuv cxv cw Kc C₂W κW) * ε ≤ 1 / 2 ∧ cSz b₁ ℓ * ε ≤ ρ ∧
      (cSz b₁ ℓ + cSn L b₁ cz ℓ cmuv) * ε ≤ 1 / 16) ∧
      ((Cb * (1 + cxv)) * ε ≤ (1 - κ₁) / 2 ∧ CLp * ε ≤ (1 - κ₁) / 2 ∧
      1 * ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧ (CLp + Cb) * ε ≤ a0 / 2 ∧
      cg * ε ≤ betaL L / 4) ∧
      0 < ε := by
    filter_upwards [ev_lin 1 one_pos, ev_lin (2 * cz) hρ0,
      ev_lin (8 * cM * ℓ ^ 2 * cz) (by norm_num : (0 : ℝ) < 1 / 2), ev_lin cxv one_pos,
      ev_lin cRv hεs, ev_lin (8 * cxv) hεs, ev_lin cg (by norm_num : (0 : ℝ) < 1 / 6),
      ev_lin cEv hℓ147, ev_lin cg hβ2, ev_lin cRv one_pos, ev_lin (8 * cxv) one_pos,
      ev_lin (f1cn ℓ cmuv) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin (f1cn' L ℓ cz cmuv Cq cRQ cRL) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin (ℓ ^ 2 / 7 + f1cw ℓ cmuv Cq cRQ cRL) hρ0,
      ev_lin (16 / 7 * (L : ℝ) ^ 2 * (8 * ℓ ^ 2 / 49 + (L : ℝ) ^ 2 * cEv) * cmuv +
        2 * ((L : ℝ) ^ 2 * cEv)) one_pos,
      ev_lin (2 * cz) (by norm_num : (0 : ℝ) < 1 / 16),
      ev_lin (cDl (7 / 8 * ℓ) cz) (by norm_num : (0 : ℝ) < 1 / 4),
      ev_lin cEl (by norm_num : (0 : ℝ) < 1 / 4), ev_lin cEl hε₁,
      ev_lin (4 * cmuv * ℓ ^ 2) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin ((cEl + 1) * cClo L ℓ bb cmuv cxv cw Kc C₂W κW) (by norm_num : (0 : ℝ) < 1 / 2),
      ev_lin (cSz b₁ ℓ) hρ0, ev_lin (cSz b₁ ℓ + cSn L b₁ cz ℓ cmuv) (by norm_num : (0 : ℝ) < 1 / 16),
      ev_lin (Cb * (1 + cxv)) hκ12, ev_lin CLp hκ12, ev_lin 1 heps0,
      ev_lin (CLp + Cb) (by positivity : 0 < a0 / 2),
      ev_lin cg (by positivity : 0 < betaL L / 4), self_mem_nhdsWithin]
      with ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
        h25 h26 h27 h28 h29
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩,
      ⟨h16, h17, h18, h19, h20, h21, h22, h23⟩, ⟨h24, h25, h26, h27, h28⟩, h29⟩
  obtain ⟨ε, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩, ⟨e12, e13, e14, e15⟩,
    ⟨e16, e17, e18, e19, e20, e21, e22, e23⟩, ⟨e24, e25, e26, e27, e28⟩, hε0⟩ := hev.exists
  have hε : 0 < ε := hε0
  have hKe : 0 ≤ K1 + C0 := add_nonneg hK1 hC0
  refine ⟨ℓ, A, ρ, ϑ, κ, cg, cm, cT, ε, K1 + C0, hℓ, hA0, hρ0, hϑ0, hε, hκ0, hκ1, hcg, hcm, hcT,
    hKe, e28, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh hmass
  have hℓR : R.ℓ = R₀.ℓ := hRℓ.trans hR₀ℓ.symm
  have hcZR : cZ R = cz := (cZ_congr hℓR).trans hczd.symm
  have hcVR : cV R ((L : ℝ) ^ 2) cm = cV0 := (cV_congr hℓR _ _).trans hcV0d.symm
  have hcWR : cW R ((L : ℝ) ^ 2) cm C₂ = cw := (cW_congr hℓR _ _ _).trans hcwd.symm
  have hcRR : cR R ((L : ℝ) ^ 2) cm C₂ = cRv := (cR_congr hℓR _ _ _).trans hcRvd.symm
  have hcER : cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq' Cl' cS' = cEv := (cE_congr hℓR _ _ _ _ _ _ _ _).trans hcEvd.symm
  have hcBR : cB R ((L : ℝ) ^ 2) cm C₂ CK CD = Cb := (cB_congr hℓR _ _ _ _ _).trans hCbd.symm
  have hcF2R : cF2 R = cm - 1 := by rw [cF2_congr hℓR, hcmd]; ring
  have hk1R : kap1 L R.A C₀ η = κ₁ := by rw [hRA, hκ₁d]
  -- the mass
  have hLpow : ∀ j k : ℕ, j ≤ k → ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 := fun j k h =>
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ L by omega)) h) 2
  have hmass2 : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ (j + 2)) ^ 2 ≤ ϑ := fun j hj => by
    rw [abs_of_pos hm0]
    exact (mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) hm0.le).trans hmass
  have hm4 : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 * (L : ℝ) ^ 4 ≤ ϑ := fun j hj => by
    have e : |R.msq| * ((L : ℝ) ^ j) ^ 2 * (L : ℝ) ^ 4 = |R.msq| * ((L : ℝ) ^ (j + 2)) ^ 2 := by ring
    rw [e]; exact hmass2 j hj
  have hm1 : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := fun j hj => by
    have hL4 : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ L by omega))
    have h0 : 0 ≤ |R.msq| * ((L : ℝ) ^ j) ^ 2 := by positivity
    exact (le_mul_of_one_le_right h0 hL4).trans ((hm4 j hj).trans hϑ1)
  have hmf : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ ϑ₀ / (L : ℝ) ^ 4 := fun j hj => by
    rw [le_div_iff₀ (by positivity)]; exact (hm4 j hj).trans hϑϑ₀
  -- validity and continuity
  have hV : ∀ j < Nh, ValidAt R j := fun j hj =>
    hVal N R hP hN hm0 hm (le_of_eq hRℓ.symm) (by rw [hRρ]; exact hρ0.le) (by rw [hRρ]; exact hρv) j
      (by omega)
  have hcov : ∀ j < Nh, CovCont R j := fun j hj =>
    hCov N R hP hN hm0 hm (by rw [hRρ]; exact hρc) j (by omega)
  -- the a priori hypotheses
  have H : ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εs C₀ C₂ Cq' Cl' cS' :=
    { hε := hε, hε1 := by linarith only [e1], hcm := hcm.le, hcmu := hcmud ▸ hcmu.le,
      hcx := hcxd ▸ hcx, hcg := hcg.le,
      hC₀ := by rw [div_le_iff₀ hL0]; linarith only [hL32, hC₀0]
      hC₂ := hC₂, hCq := hCq', hCl := hCl', hcS := hcS'
      h1 := by rw [hcZR, hRρ]; linarith only [e2]
      h2 := by rw [hRℓ, hcZR]; linarith only [e3]
      h3 := by rw [← hcxd]; linarith only [e4]
      h4 := by rw [hcRR]; exact e5
      h5 := by rw [← hcxd]; exact e6
      h6 := e7
      h7 := by rw [hcER, hRℓ]; exact e8 }
  have Hk : ApHyp R ((L : ℝ) ^ 2) ((1 + kap1 L R.A C₀ η) / 2) cg cm cT ε εs C₀ C₂ Cq' Cl' cS' := by
    rw [hk1R, ← hκd]; exact H
  have hSBR : StepBounds L R.A C₀ η εs CK C₂ CD Cq' Cl' cS' := by rw [hRA]; exact hSB
  have hA2R : 2 ≤ R.A := by rw [hRA]; exact hA2
  have hVle : ∀ j, j < Nh → ∀ i ≤ j, ValidAt R i := fun j hj i hi => hV i (lt_of_le_of_lt hi hj)
  have hjN : ∀ j, j < Nh → j + 1 < N := fun j hj => by omega
  have hδ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hδ1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- (F2)
  have F2 := F2_rg (β := betaL L) (δ := 1 / 2) R hSBR hV hm1 hβ0.le hδ1 H
    (by rw [hcF2R, hcER, hRℓ, ← hcmud]; linarith only [e15])
  -- (Kb), (Yb)
  have Hb := rgBound_rg (κ₁ := kap1 L R.A C₀ η) (β := betaL L) (δ := 1 / 2) R hSBR hV hm1 hβ0.le
    hδ1 rfl hC₀0 hCK hCD Hk
  rw [hcBR, hk1R] at Hb
  -- the sharp inputs and (F1)
  have hcgβ : cg * ε ≤ betaL L / 2 := e9
  -- the sharp inputs
  obtain ⟨eAf, heAf⟩ : ∃ f : ℕ → ℝ, f = fun j => 16 / 7 * cz * (M₀ + 1) * (|R.msq| * ((L : ℝ) ^ j) ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨E0f, hE0f⟩ : ∃ f : ℕ → ℝ, f = fun j =>
      if j = 0 then E0 else C0 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) :=
    ⟨_, rfl⟩
  have hE0f0 : E0f 0 = E0 := by rw [hE0f]; exact if_pos rfl
  have hE0fj : ∀ j, 1 ≤ j →
      E0f j = C0 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) := fun j hj => by
    rw [hE0f]; exact if_neg (by omega)
  have hBj : ∀ j, 0 ≤ (((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 := fun j => by
    positivity
  have hE0f_nn : ∀ j, 0 ≤ E0f j := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hE0f0]; exact hE0
    · rw [hE0fj j hj1]; exact mul_nonneg hC0 (hBj j)
  have hE0f_le : ∀ j < Nh, E0f j ≤ E0 + 2 * C0 := fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hE0f0]; linarith only [hC0]
    · rw [hE0fj j hj1]
      have h1 : (((L : ℝ) ^ j) ^ 2)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_pow₀ (by exact_mod_cast (show 1 ≤ L by omega))))
      have h2 : R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 ≤ 1 :=
        ((mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) hm0.le).trans hmass).trans hϑ1
      have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC0
      linarith only [h3, hE0]
  have heAf0 : ∀ j, 0 ≤ eAf j := fun j => by simp only [heAf]; positivity
  have heAf1 : ∀ j < Nh, 32 / 7 * eAf j ≤ 1 := fun j hj => by
    simp only [heAf]
    have h0 : 0 ≤ 16 / 7 * cz * (M₀ + 1) := by positivity
    have hk := mul_le_mul_of_nonneg_left (hmf j hj) h0
    have e : 16 / 7 * cz * (M₀ + 1) * (ϑ₀ / (L : ℝ) ^ 4) = eA := heAd.symm
    linarith only [hk, e, heA1]
  have hcgβ : cg * ε ≤ betaL L / 2 := e9
  have HSj : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤ eAf j * (t j).1 ∧
      (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cz * (t j).1 := fun j hj t ht => by
    obtain ⟨S0, S1⟩ := hS01L N R hP hN hm0 hm (by rw [hRρ]; exact hρS) j (hjN j hj) (hVle j hj) t
    obtain ⟨h1, -, h3⟩ := HS_of_S01 R hSBR (Nh := j + 1) (fun i hi => hV i (by omega))
      (fun i hi => hm1 i (by omega)) H hβ0.le (by norm_num) hcgβ hM₀ hM₂
      (mf := |R.msq| * ((L : ℝ) ^ j) ^ 2)
      (fun i hi => mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) (abs_nonneg _))
      (Nat.lt_succ_self j) t ht S0 S1
    refine ⟨le_of_le_of_eq h1 (by simp only [heAf, hcZR]), ?_⟩
    rw [← hcZR]; exact h3
  have HVf : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      |(f1Coef R j t + htad R j t).re - betaL L| ≤
        E0f j + (E1 + E1s) * (2 * cz) * (t j).1 := fun j hj t ht => by
    have hMz := (HSj j hj t ht).2
    have hg0 : 0 ≤ (t j).1 := (ht.1 j le_rfl).1.le
    have hb : 0 ≤ 2 * cz * (t j).1 := by positivity
    have e : betaL L = 3 * (Real.log L / (2 * Real.pi)) := rfl
    have e2 : (E1 + E1s) * (2 * cz) * (t j).1 = E1 * (2 * cz * (t j).1) + E1s * (2 * cz * (t j).1) := by
      ring
    rw [e, e2]
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · have h1 := hHVL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHV) 0 (hjN 0 hj) (hVle 0 hj) t
      rw [htad_zero, add_zero, hE0f0]
      have h3 := mul_le_mul_of_nonneg_left hMz hE1
      have h4 := mul_nonneg hE1s hb
      linarith only [h1, h3, h4]
    · have h1 := hHVsL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHVs) j hj1 (hjN j hj) (hVle j hj) t
      rw [hE0fj j hj1]
      have h2 := mul_le_mul_of_nonneg_right hC0sh (hBj j)
      have h3 := mul_le_mul_of_nonneg_left hMz hE1s
      have h4 := mul_nonneg hE1 hb
      linarith only [h1, h2, h3, h4]
  have F1s := hF1 L hL8 hLp N R C₀ η εs CK C₂ CD Cq' Cl' cS' hSBR hA2R Nh hV hm1 ((L : ℝ) ^ 2)
    (betaL L) (1 / 2) κ cg cm cT ε H hβ0 (by norm_num) hcgβ (by rw [hcRR]; linarith only [e10])
    (by rw [← hcxd]; linarith only [e11]) KB ((E1 + E1s) * (2 * cz)) 1 eAf E0f hKB heAf0 heAf1
    (fun j hj t ht => (HSj j hj t ht).1)
    (fun j hj t ht => hHDL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHD) j (hjN j hj) (hVle j hj) t)
    HVf
    (by rw [hRℓ, ← hcmud]; exact e12)
    (by rw [hRℓ, hcZR, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQd, ← hcRLd]; exact e13)
    (by rw [hRℓ, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQd, ← hcRLd, hRρ]; exact e14)
    (by
      rw [hRℓ, hcZR, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQd, ← hcRLd, ← hcRDd, ← hcESd, hcgd]
      have := le_max_left (f1c3s L ℓ cz cmuv Cq cRQ cRL CqD cRD KB cES 1) 0
      linarith only [this])
  -- the band (F1) with `δ = 1/2`
  have F1 : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      |(rgData R).G j t - (t j).1 - betaL L * (t j).1 ^ 2| ≤
        1 / 2 * betaL L * (t j).1 ^ 2 + cg * (t j).1 ^ 3 := fun j hj t ht => by
    have h := F1s j hj t ht
    have hb : 32 / 7 * eAf j + E0f j ≤ 1 / 2 * betaL L := by
      linarith only [heAf1 j hj, hE0f_le j hj, hband]
    have := mul_le_mul_of_nonneg_right hb (sq_nonneg (t j).1)
    linarith only [h, this]
  -- the Lipschitz bounds
  have HLip := hLipR N R hP hRA (by rw [hRρ]; exact hρl) hm0 hm C₀ η εs CK C₂ CD Cq' Cl' cS' hSBR
    hC₀l' hηl' Nh hV ϑ hϑ0.le hϑ1 hmass2 (betaL L) (1 / 2) cg cm cT ε hβ0.le hδ1 Hk
    (by rw [hcZR]; linarith only [e16])
    (by rw [hRℓ, hcZR]; exact e17)
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld]; exact e18)
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld]; exact e19)
    (by rw [← hcmud, hRℓ]; linarith only [e20])
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hbbd, ← hκWd]
        linarith only [e21])
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hb₁d, hRρ]
        linarith only [e22])
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hb₁d]
        linarith only [e23])
  simp only [hk1R, hRA, ← hκ₁d, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hbbd, ← hb₁d,
    ← hκWd, ← hCLd] at HLip
  obtain ⟨LG, Lm, HL⟩ := HLip
  -- the constants of the reduction
  obtain ⟨a, had⟩ : ∃ a, a = (CLp + Cb) * (ε + ϑ) := ⟨_, rfl⟩
  have hCLa : CL * (ε + ϑ) ≤ a := by
    rw [had]; have h0 : 0 ≤ ε + ϑ := by positivity
    have h1 := mul_le_mul_of_nonneg_right hCLle h0
    have h2 := mul_nonneg hCb h0
    linarith only [h1, h2]
  have hCLa' : CL * ε ≤ a := by
    rw [had]
    have h1 := mul_le_mul_of_nonneg_right hCLle hε.le
    have h2 : 0 ≤ (CLp + Cb) * ϑ := by positivity
    have h3 : 0 ≤ Cb * ε := by positivity
    linarith only [h1, h2, h3]
  have hCba : Cb * ε ≤ a := by
    rw [had]
    have h2 : 0 ≤ (CLp + Cb) * ϑ := by positivity
    have h3 : 0 ≤ CLp * ε := by positivity
    linarith only [h2, h3]
  have ha0' : a ≤ a0h ((L : ℝ) ^ 2) κ CLp := by
    rw [had, ← ha0d]; linarith only [hϑa, e27]
  have LG' : ∀ j < Nh, ∀ t t', InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| +
        a * |(t j).2.1 - (t' j).2.1| + CLp * ‖(t j).2.2 - (t' j).2.2‖ + a * M :=
    fun j hj t t' ht ht' M hM hh => (LG j hj t t' ht ht' M hM hh).trans (by gcongr)
  have Lm' : ∀ j < Nh, ∀ t t', InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
      (∀ i < j, dist3 (t i) (t' i) ≤ M) →
      |(rgData R).m j t - (rgData R).m j t'| ≤ CLp * |(t j).1 - (t' j).1| +
        a * |(t j).2.1 - (t' j).2.1| + CLp * ‖(t j).2.2 - (t' j).2.2‖ + a * M :=
    fun j hj t t' ht ht' M hM hh => (Lm j hj t t' ht ht' M hM hh).trans (by gcongr)
  obtain ⟨cG, cmm, cT'⟩ := rgData_cont R hV hcov
  have H' := hhyp_of_rg2 (F := rgData R) (Λ := (L : ℝ) ^ 2) (β := betaL L) (δ := 1 / 2)
    (κ₁ := κ₁) (cg := cg) (cm := cm) (cT := cT) (ε := ε) (N := Nh) (Cb := Cb) (Cl := CL) CLp a hΛ hβ0
    hδ0 (le_refl _) hκ₁0 (by linarith) hcg hcm hcT hCLp hCb (by rw [hcTd]; linarith) hε
    (by linarith only [e1])
    (by rw [← hκd, ← hcxd]; linarith only [e24]) hCba
    (by linarith only [e25, mul_le_mul_of_nonneg_right hCLle hε.le]) hCLa'
    (fun j _ => causal_G R j) (fun j _ => causal_m R j) (fun j _ => causal_T R j) cG cmm cT'
    (by rw [← hκd]; exact F1) (by rw [← hκd]; exact F2) (by rw [← hκd]; exact LG')
    (by rw [← hκd]; exact Lm') Hb HL
  rw [← hκd] at H'
  have he' : ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm := by linarith only [e26]
  refine ⟨CLp, a, fun j => 32 / 7 * eAf j + E0f j, H', he', ha0',
    fun j => add_nonneg (mul_nonneg (by norm_num) (heAf0 j)) (hE0f_nn j), F1s,
    fun j hj => by linarith only [heAf1 j hj, hE0f_le j hj, hband], fun j hj1 => ?_⟩
  have hA : 32 / 7 * eAf j ≤ K1 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) := by
    simp only [heAf, hK1d]
    rw [abs_of_pos hm0]
    have h1 : R.msq * ((L : ℝ) ^ j) ^ 2 ≤ R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) hm0.le
    have h2 : R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 ≤
        (((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 := by
      have : 0 ≤ (((L : ℝ) ^ j) ^ 2)⁻¹ := by positivity
      linarith only [this]
    have h0 : 0 ≤ 32 / 7 * (16 / 7 * cz * (M₀ + 1)) := by positivity
    have := mul_le_mul_of_nonneg_left (h1.trans h2) h0
    linarith only [this]
  show 32 / 7 * eAf j + E0f j ≤ _
  rw [hE0fj j hj1]
  have e1 : (K1 + C0) * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) =
      K1 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) +
        C0 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) := by ring
  rw [e1]
  linarith only [hA]

end

end Step2
