import Spin2.Master.MasterAllCore

/-!
# `MasterCore`: the loop conclusion (block of `thm_case2_pairLIZWKA`)
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

set_option maxHeartbeats 4000000 in
/-- `LoopConcl` under the consolidated master constants (block `hLoop` of `thm_case2_pairLIZWKA`). -/
theorem MasterCore.loopConclD {L : ℕ} [NeZero L] (D : MasterCore L) :
    LoopConclD L D.ℓ D.A D.ρ D.κ D.cm D.cT D.ε D.B₁ D.B₂ D.B₃ D.cq D.B' := by
  obtain
    ⟨Cq, Cl, cS, hCq, hCl, hcS, hNu, Cpf, εpf, hCpf, hPB, C₀o, ηo, hC₀o, hηo, Kw, hKw, C₀u, ηu,
      hC₀u, hηu, Cw, hCw, hWw, Lo, Lu, hLo, hLuL, hLc, hLb, hL49, hLpl, hlog, ℓ, A, ρ, κ, cg, cm,
      cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hA2, hAx, hAu, hAJ, hVC, hLV, hZT, C₀x,
      ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hXm, c, hc, ζbar, K, cS2, hζ0, hK, hcS2, hLc',
      hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp, ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁,
      hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab, ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, htopR⟩ := D
  dsimp only [MasterCore.ce, MasterCore.B₁, MasterCore.B₂, MasterCore.B₃, MasterCore.cq, MasterCore.B', MasterCore.Bk, MasterCore.cgb, MasterCore.cP, MasterCore.cδ, MasterCore.cRel, MasterCore.cw, MasterCore.cGB, MasterCore.cWL, MasterCore.cKL, MasterCore.cρ, MasterCore.cWo, MasterCore.ιW]
  have hLr : (Lo : ℝ) ≤ L := by exact_mod_cast hLo
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id hC2
  obtain ⟨-, hθ⟩ := hAx hLo
  set ce := ceff L c with hce
  set B' := c2Bp Cq Cl cS L K cS2 c (cx κ cT) with hB'
  have hβ2 := betaL_ge (by omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hθ0 : 0 ≤ kθ0 L A C₀o ηo := by
    unfold kθ0
    exact mul_nonneg hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hLwk : Kw / L ≤ 1 / 12 := by
    rw [div_le_iff₀ hL0]; linarith
  have hcx : 0 ≤ cx κ cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id hC2
    unfold cx; exact div_nonneg (by linarith) (by linarith)
  set Bk := kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT) with hBk
  have hBk0 : 0 ≤ Bk := by
    have h1 := mul_nonneg hθ0 (by positivity : (0 : ℝ) ≤ 8 * cx κ cT)
    have h2 := mul_nonneg hC₁k
      (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L A C₀o ηo * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  set cgb := c2gF B' c with hcgb
  set cP := prodCP2 L (Cpf L) with hcP
  set cδ := c2dF L (Cpf L) B' C₁w Bk c with hcδd
  have hcm2 : (2 : ℝ) ≤ max c 2 := le_max_right _ _
  have hB0' : (0 : ℝ) ≤ max B' 0 := le_max_right _ _
  have hcgb0 : 0 ≤ cgb := div_nonneg (by linarith) (by linarith)
  have hce2 : 0 ≤ ceff L (max c 2) := by unfold ceff; linarith
  have hcP0 : 0 ≤ cP := by
    show 0 ≤ (cbnC : ℝ) * Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := hCpf L; positivity
  set Xc := 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * Bk + 3 * cP * (3 * C₁w + 1) +
    4 * ceff L (max c 2) * cgb * (1 + cgb) with hXc
  have hcδX : cδ = 3 * Xc := rfl
  have hX0 : 0 ≤ Xc := by positivity
  have hcδ0 : 0 ≤ cδ := by rw [hcδX]; positivity
  have hq4 : (2 : ℝ) / L ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have : (49 : ℝ) ≤ L := by exact_mod_cast hL49
    linarith
  have hcδc : 0 ≤ cδ * c ^ 2 := mul_nonneg hcδ0 (sq_nonneg c)
  set Dℓ : ℝ := 9 / 8 * ℓ ^ 2 with hDℓ
  set Kw' : ℝ := 128 * (csN 2 : ℝ) * (3 * C₁w + 1) * Bk * (Dℓ + 1) +
    2 * (cBn : ℝ) * Q1 2 * (3 * C₁w + 1) * Dℓ with hKw'
  have hKw0 : 0 ≤ Kw' := by
    have hQ := one_le_Q1 (d := 2) (by norm_num)
    have : (0 : ℝ) ≤ csN 2 := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
    have : 0 ≤ Dℓ := by positivity
    have : 0 ≤ 3 * C₁w + 1 := by linarith
    have : 0 ≤ Q1 2 := by linarith
    positivity
  set cwF := max c 0 * Kw' with hcwF
  have hcw0 : 0 ≤ cwF := by rw [hcwF]; exact mul_nonneg (le_max_right _ _) hKw0
  have hLoop : LoopConclD L ℓ A ρ κ cm cT ε (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
      (9 / 64 * ce ^ 2) (7 * ce) B' := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := inDh_rg_of_D R' F1 hD Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := by rw [hc]; exact cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
    have hSB' : StepBounds L R'.A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx := by rw [hRA']; exact hSBx
    have hmsq : R'.msq ∈ mRange L N := hm
    have X := c2ctx_master R' hNh hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε ht
    rw [hcR] at X
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
    have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
    have hP' : R'.P = Pc := hP
    have hce0 : 0 ≤ ce := X.c_nonneg
    have hbulk : Case2Bulk R P Nh m b μ₀ (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
        (9 / 64 * ce ^ 2) (7 * ce) := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · exact X.bubble_le hP' hLc' hK hcS2 hm.1 hm.2 hgε hζε hk P.a
      · have h := X.nuflow_le hCq hCl hcS hNu hSB' hm1 hβ0 (by norm_num) H ht
          (by rw [hRA']; exact hA2) (by rw [hcR]; exact hcε) hc'ε hk P.a
        rw [hcR] at h
        exact h
      · exact X.drift_le hk P.a
      · exact X.q_le hk P.a
    have hB1 : 0 ≤ bubB L ce K cS2 := by
      unfold bubB; have := bubE_nonneg; have := bubF_nonneg (L := L) hce0 hK hcS2
      have : 0 ≤ betaL L / 3 := by linarith
      positivity
    have hB2 : 0 ≤ nuB L Cq Cl cS (cx κ cT) c ce := by
      have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
      have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
      have hcx : 0 ≤ cx κ cT := H.hcx
      have hQc : 0 ≤ cNear 2 L * Q1 2 ^ 2 + Q1 2 :=
        add_nonneg (mul_nonneg hN0 (sq_nonneg _)) (by linarith)
      unfold nuB
      have : 0 ≤ 16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cx κ cT :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCq) (by linarith)) hCl) hcx
      have : 0 ≤ 2 * Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) * c ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCq) hCl)
          (sq_nonneg _)) hQc) (sq_nonneg _)
      linarith
    have hB3 : 0 ≤ 9 / 64 * ce ^ 2 := by positivity
    refine ⟨by linarith, hbulk,
      case2Loop_of (fun i hi => hV i hi) hB1 hB2 hB3 ?_ hβ0 ?_ ?_ ?_ ?_ hbulk⟩
    · positivity
    · exact fun k hk => ⟨(X.hg k hk.le).1.le, (X.hg k hk.le).2⟩
    · exact fun k hk => ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith) (le_trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (pow_le_pow_right₀ (by linarith) (by omega)) 2) hm.1.le) X.hm)⟩
    · exact fun k hk => X.hg2 k hk
    · intro k hk
      have h1 := hgε k hk.le
      have h0 := (X.hg k hk.le).1.le
      have hB0 : 0 ≤ B' := by
        show 0 ≤ case2BK (betaL L) (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
          (9 / 64 * ce ^ 2) (7 * ce) 2
        unfold case2BK
        have : 0 ≤ 7 * ce * (2 + 1) := by positivity
        have : 0 ≤ betaL L / 3 := by linarith
        linarith
      exact (mul_le_mul_of_nonneg_left h1 hB0).trans hsm
  exact hLoop

/-- `loopConcl` from its `D_ε` form (`loopConclD`). -/
theorem MasterCore.loopConcl {L : ℕ} [NeZero L] (D : MasterCore L) :
    LoopConcl L D.ℓ D.A D.ρ D.κ D.cm D.cT D.ε D.B₁ D.B₂ D.B₃ D.cq D.B'  :=
  D.loopConclD.adm

end

end Spin2
