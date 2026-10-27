import Spin2.Master.MasterAllRel

/-!
# `MasterCore`: `PairInitConclW` (block of `thm_case2_pairLIZWW`)
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

set_option maxHeartbeats 4000000 in
/-- `PairInitConclW ι_W` under the consolidated master constants. -/
theorem MasterCore.pairInitConclWD {L : ℕ} [NeZero L] (D : MasterCore L) :
    PairInitConclWD L D.ℓ D.A D.ρ D.κ D.cm D.cT D.ε D.ιW := by
  have hLoop := MasterCore.loopConclD D
  have hRelG := MasterCore.relConcl2GD D
  obtain
    ⟨Cq, Cl, cS, hCq, hCl, hcS, hNu, Cpf, εpf, hCpf, hPB, C₀o, ηo, hC₀o, hηo, Kw, hKw, C₀u, ηu,
      hC₀u, hηu, Cw, hCw, hWw, Lo, Lu, hLo, hLuL, hLc, hLb, hL49, hLpl, hlog, ℓ, A, ρ, κ, cg, cm,
      cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hA2, hAx, hAu, hAJ, hVC, hLV, hZT, C₀x,
      ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hXm, c, hc, ζbar, K, cS2, hζ0, hK, hcS2, hLc',
      hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp, ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁,
      hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab, ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, htopR⟩ := D
  dsimp only [MasterCore.ce, MasterCore.B₁, MasterCore.B₂, MasterCore.B₃, MasterCore.cq, MasterCore.B', MasterCore.Bk, MasterCore.cgb, MasterCore.cP, MasterCore.cδ, MasterCore.cRel, MasterCore.cw, MasterCore.cGB, MasterCore.cWL, MasterCore.cKL, MasterCore.cρ, MasterCore.cWo, MasterCore.ιW] at hLoop hRelG ⊢
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
  have hPI : PairInitConclWD L ℓ A ρ κ cm cT ε (iotaW L Cw (3 * C₁w + 1)) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD x hx1 hxN
    have hb : 0 < b := by
      have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
    have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb
    have hNh0 : 0 < Nh := by omega
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
    have hc2 : 2 ≤ c := hcR ▸ two_le_cR R' H.hcmu H.hC₂
    have hmc : max c 2 = c := max_eq_left hc2
    have hce0 : 0 ≤ ce := X.c_nonneg
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
    have hε0 : 0 ≤ ε := by have := H.hε; linarith
    have hOS : ∀ P : Obs2.ObsPts 2 L N, ∀ j ≤ Nh,
        OneSz R' P (zV0 b) t j (c * (t j).1) (3 * C₁w + 1) Bk := by
      intro P
      obtain ⟨hB0, -, q, -, -, hl⟩ :=
        hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P (zV0 b)
      have hB'0 : 0 ≤ B' := by
        show 0 ≤ case2BK (betaL L) (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
          (9 / 64 * ce ^ 2) (7 * ce) 2
        unfold case2BK
        have : 0 ≤ 7 * ce * (2 + 1) := by positivity
        have : 0 ≤ betaL L / 3 := by linarith
        linarith
      have hmB : max B' 0 = B' := max_eq_left hB'0
      have hcgc : cgb * c = B' + 1 := by
        rw [hcgb, c2gF, hmB, hmc]; field_simp
      have hPr := prodBd2_hist R' hPB (hCpf L) hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H
        hρ0' hρ8' P (zV0 b) rfl t Nh le_rfl (by omega) hVL ht (by rw [hcR]; exact hεp)
        (hLb.trans hLr)
      rw [hcR] at hPr
      have hcg1 : 1 ≤ cgb * cR R' ((L : ℝ) ^ 2) cm C₂x := by rw [hcR, hcgc]; linarith
      have hcgε' : cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) ≤ 1 / 7 := by
        rw [hcR, ← mul_assoc, hcgc]; rw [hmB] at hgε7; exact hgε7
      have hcδ' : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) *
          kB (kθ0 L R'.A C₀o ηo) C₁k (8 * cx κ cT) +
          3 * cP * (3 * C₁w + 1) + 4 * ce * cgb * (1 + cgb) +
          4 * ce * cgb * cδ * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) ≤ 6 / 7 * cδ := by
        rw [hRA', hcR]
        have e1 : 4 * ce * cgb * cδ * (c * ε) =
            (4 * ceff L (max c 2) * (max B' 0 + 1) * ε) * cδ := by
          rw [hmc, hmB, hce, ← hcgc]; ring
        have e2 := mul_le_mul_of_nonneg_right hBτε hcδ0
        have e3 : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * Bk + 3 * cP * (3 * C₁w + 1) +
            4 * ce * cgb * (1 + cgb) = cδ / 3 := by rw [hcδX, hXc, hmc]; ring
        rw [e1]
        linarith
      have hsumε : cδ * (cR R' ((L : ℝ) ^ 2) cm C₂x ^ 2 * (ε / (betaL L / 4))) ≤ 1 / 8 := by
        rw [hcR]
        have e : cδ * (c ^ 2 * (ε / (betaL L / 4))) = cδ * c ^ 2 * (4 / betaL L) * ε := by
          field_simp
        rw [e]; exact hcδε
      have hT : ∀ k j, k < j → j < Nh →
          ‖Obs2.tadInc2 P (Obs2.histCovO R' t)
            (Obs2.histVO2 R' P (Obs2.obsInit .two (zV0 b) P) t) k j‖ ≤
            ce * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := fun k j hkj hj =>
        X.tadInc2_le P _ (Obs2.obsInit_isObs .two (zV0 b) P) hkj hj
      have hnn : ∀ i < Nh,
          ‖Obs2.frakN2 P (Obs2.histCovO R' t)
            (Obs2.histVO2 R' P (Obs2.obsInit .two (zV0 b) P) t) i‖ ≤
            cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * (t i).1) := by
        intro i hi
        rw [hcR, ← mul_assoc, hcgc]
        have h := (hl i hi).2.1
        have hg := (X.hg i hi.le).1.le
        have h' : B' * (t i).1 ≤ (B' + 1) * (t i).1 := by
          rw [add_mul, one_mul]; exact le_add_of_nonneg_right hg
        exact h.trans h'
      have key := PtCorr2.obs_hist_rel2_baseX R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV
        hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P (zV0 b) rfl hmu t Nh le_rfl hNh0
        (by omega) ht
        (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
        (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk) hLwk
        (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
        (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcgε' hcδ'
        hsumε hT hnn (by rw [hcR]; exact hPr)
      rw [hcR, hRA'] at key
      intro j hj
      obtain ⟨h1, h2, h3, h4⟩ := key j hj
      exact ⟨h1, h2, h3, h4⟩
    have hrat : ∀ P : Obs2.ObsPts 2 L N, ∀ j < Nh,
        ‖Obs2.betaTot2 (L := L) (N := N) j
          (Obs2.histVO2 R' P (Obs2.obsInit .two (zV0 b) P) t j)‖ ≤
        64 / 49 * ‖Obs2.betaTot2 (L := L) (N := N) (j + 1)
          (Obs2.histVO2 R' P (Obs2.obsInit .two (zV0 b) P) t (j + 1))‖ := fun P j hj =>
      bt2_ratio R P (zV0 b) (by omega)
        (hRelG N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P (zV0 b) hmu)
        (hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P (zV0 b)).2.2 hj
    obtain ⟨ε₀u, C₁u, hε₀u, hC₁u, hKBu, h1u, h2u, h3u, h4u, h5u⟩ := hkab
    have hsX := PtCorr2.histS_pos' R' hρ0' hρ8' t (Obs.coal L (0 : Lam 2 L N) x)
    have hpX : 0 < pM R' (ptsX x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x) := by
      have := (hOS (ptsX x) _ hxN).1
      show 0 < 2 * PtCorr2.histS R' (Obs.coal L (0 : Lam 2 L N) x) t ^ 2 * _; positivity
    have hpS : 0 < pM R' (ptsS x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x) := by
      have := (hOS (ptsS x) _ hxN).1
      show 0 < 2 * PtCorr2.histS R' (Obs.coal L (0 : Lam 2 L N) x) t ^ 2 * _; positivity
    refine ⟨hpX, hpS, fun Y => ?_⟩
    have hVc : ValidCore R' (Obs.coal L (0 : Lam 2 L N) x) := by
      rcases lt_or_eq_of_le hxN with h | h
      · exact (hV _ h).toValidCore
      · rw [h]; exact hVL.2
    have hmsj : |R'.msq| * ((L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x)) ^ 2 ≤ 1 := by
      rcases lt_or_eq_of_le hxN with h | h
      · exact hm1 _ h
      · rw [h, abs_of_pos hmsq.1]
        have h1 := PtCorr2.msq_mul_pow_le_one (L := L) (N := N) (by omega) (by omega) hmsq.2
        have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
        have h2 : ((L : ℝ) ^ Nh) ^ 2 ≤ (L : ℝ) ^ (2 * (N - 1)) := by
          rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
        have h0 := hmsq.1
        exact (mul_le_mul_of_nonneg_left h2 h0.le).trans h1
    have key := pairInit_trajW R' (by rw [hRA']; exact hKBu) hC₀u hC₁u hSB' hV hm1 hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H hL8 hρ0' hρ8' (by rw [hRA']; linarith) t
      (traj_zero_X R m b μ₀) ht b x hx1 hxN (by omega) (by linarith : (1 : ℝ) ≤ 3 * C₁w + 1)
      hBk0 (by rw [hcR]; exact hOS (ptsX x)) (by rw [hcR]; exact hOS (ptsS x))
      (hrat (ptsX x)) (hrat (ptsS x)) (by rw [hcR]; exact hcε) (by rw [hcR]; exact h1u)
      (by rw [hcR, hRA']; exact h2u) (by rw [hcR, hRA']; exact h3u)
      (by rw [hcR, hRA']; exact h4u) (by rw [hcR, hRA']; exact h5u) hWw hCw hVc hmsj Y
    rw [hRA'] at key
    exact key
  exact hPI

/-- `pairInitConclW` from its `D_ε` form (`pairInitConclWD`). -/
theorem MasterCore.pairInitConclW {L : ℕ} [NeZero L] (D : MasterCore L) :
    PairInitConclW L D.ℓ D.A D.ρ D.κ D.cm D.cT D.ε D.ιW  :=
  D.pairInitConclWD.adm

end

end Spin2
