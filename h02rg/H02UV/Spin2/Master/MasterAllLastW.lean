import Spin2.Master.MasterAllLoop

/-!
# `MasterCore`: `LastObsConclW` (block of `thm_case2_pairLIZWKA`)
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

set_option maxHeartbeats 4000000 in
/-- `LastObsConclW c_{WL}` under the consolidated master constants. -/
theorem MasterCore.lastObsConclWD {L : ℕ} [NeZero L] (D : MasterCore L) :
    LastObsConclWD L D.ℓ D.A D.ρ D.κ D.cm D.cT D.ε D.cWL := by
  have hLoop := MasterCore.loopConclD D
  obtain
    ⟨Cq, Cl, cS, hCq, hCl, hcS, hNu, Cpf, εpf, hCpf, hPB, C₀o, ηo, hC₀o, hηo, Kw, hKw, C₀u, ηu,
      hC₀u, hηu, Cw, hCw, hWw, Lo, Lu, hLo, hLuL, hLc, hLb, hL49, hLpl, hlog, ℓ, A, ρ, κ, cg, cm,
      cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hA2, hAx, hAu, hAJ, hVC, hLV, hZT, C₀x,
      ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hXm, c, hc, ζbar, K, cS2, hζ0, hK, hcS2, hLc',
      hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp, ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁,
      hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab, ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, htopR⟩ := D
  dsimp only [MasterCore.ce, MasterCore.B₁, MasterCore.B₂, MasterCore.B₃, MasterCore.cq, MasterCore.B', MasterCore.Bk, MasterCore.cgb, MasterCore.cP, MasterCore.cδ, MasterCore.cRel, MasterCore.cw, MasterCore.cGB, MasterCore.cWL, MasterCore.cKL, MasterCore.cρ, MasterCore.cWo, MasterCore.ιW] at hLoop ⊢
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
  have hLastW : LastObsConclWD L ℓ A ρ κ cm cT ε (2 * (3 * C₁w + 1) * max c 0) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P hNh0
    have hb : 0 < b := by
      have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
    have hWeq : ∀ x, WbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) x ↔
        WbHc (R.withMsq m) P (Obs2.obsInit .two (PtCorr2.gaZero (zV b)) P)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) x := by
      intro x; unfold WbHc
      rw [(PtCorr2.obsHist_gaZero (R.withMsq m) P (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (zV b)
        (traj_zero_X R m b μ₀) (Nh + 1) (by omega)).2.1]
    rw [hWeq, bt2_gaZero R P (zV b)]
    set V := PtCorr2.gaZero (zV b) with hVd
    have hga : Obs2.OCoup2.ga V = 0 := rfl
    have hmu : Obs2.OCoup2.mua V ≠ 0 := zV_mua_ne hb
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
    obtain ⟨hB0, -, q, -, -, hl⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V
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
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
    have hPr := prodBd2_hist R' hPB (hCpf L) hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H
      hρ0' hρ8' P V hga t Nh le_rfl (by omega) hVL ht (by rw [hcR]; exact hεp) (hLb.trans hLr)
    rw [hcR] at hPr
    have hε0 : 0 ≤ ε := by have := H.hε; linarith
    have hcg1 : 1 ≤ cgb * cR R' ((L : ℝ) ^ 2) cm C₂x := by rw [hcR, hcgc]; linarith
    have hcgε' : cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) ≤ 1 / 7 := by
      rw [hcR, ← mul_assoc, hcgc]; rw [hmB] at hgε7; exact hgε7
    have hcδ' : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * kB (kθ0 L R'.A C₀o ηo) C₁k (8 * cx κ cT) +
        3 * cP * (3 * C₁w + 1) + 4 * ce * cgb * (1 + cgb) +
        4 * ce * cgb * cδ * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) ≤ 6 / 7 * cδ := by
      rw [hRA', hcR]
      have e1 : 4 * ce * cgb * cδ * (c * ε) = (4 * ceff L (max c 2) * (max B' 0 + 1) * ε) * cδ := by
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
        ‖Obs2.tadInc2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P (Obs2.obsInit .two V P) t) k j‖ ≤
          ce * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := fun k j hkj hj =>
      X.tadInc2_le P _ (Obs2.obsInit_isObs .two V P) hkj hj
    have hnn : ∀ i < Nh,
        ‖Obs2.frakN2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P (Obs2.obsInit .two V P) t) i‖ ≤
          cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * (t i).1) := by
      intro i hi
      rw [hcR, ← mul_assoc, hcgc]
      have h := (hl i hi).2.1
      have hg := (X.hg i hi.le).1.le
      have h' : B' * (t i).1 ≤ (B' + 1) * (t i).1 := by
        rw [add_mul, one_mul]; exact le_add_of_nonneg_right hg
      exact h.trans h'
    have key := PtCorr2.obs_hist_rel2_baseX R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV hm1 hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P V hga hmu t Nh le_rfl hNh0 (by omega) ht
      (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
      (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk) hLwk
      (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
      (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcgε' hcδ'
      hsumε hT hnn (by rw [hcR]; exact hPr)
    rw [hcR, hRA'] at key
    have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
    have hc0 : 0 ≤ c := by linarith
    have hg0N : 0 ≤ (t Nh).1 := (X.hg Nh le_rfl).1.le
    obtain ⟨-, hA2, hWb, -⟩ := key Nh le_rfl
    have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
      rw [abs_of_nonneg X.hm0]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
    have hs := PtCorr2.histS_pos' R' hρ0' hρ8' t Nh
    set B0 := ‖bt2 R P V m b μ₀ Nh‖ with hB0
    set S2 := PtCorr2.histS R' Nh t ^ 2 with hS2
    have hA2' : Obs2.shA2 (Obs2.histVO2 R' P (Obs2.obsInit .two V P) t) Nh ≤ 2 * B0 := hA2
    have hWb' : WbHc R' P (Obs2.obsInit .two V P) t Nh
        ((3 * C₁w + 1) * (c * (t Nh).1) * (2 * S2 * B0)) := hWb
    have hm0 : 0 ≤ 2 * S2 * B0 := by positivity
    have hVo : ∀ b' ∈ blockIdx (L := L) (N := N) Nh, Obs2.oTo Obs2.wA Nh (PtCorr2.histS R' Nh t)
        ((Obs2.obsHist R' P (Obs2.obsInit .two V P) Nh t).V b') ≤ ENNReal.ofReal (2 * S2 * B0) := by
      intro b' hb'
      refine (PtCorr2.vobs2_block_le R' P V hga t Nh hs b' hb').trans
        (ENNReal.ofReal_le_ofReal ?_)
      have := mul_le_mul_of_nonneg_left hA2' (sq_nonneg (PtCorr2.histS R' Nh t))
      rw [← hS2] at this
      linarith
    have hcW1 : (1 : ℝ) ≤ 3 * C₁w + 1 := by linarith
    have hW1 := PtCorr2.wobs_hist_stepL R' hWB hSB' hV hm1 hVL hmN hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H P Obs2.wA Obs2.wA_ab (Obs2.obsInit .two V P)
      (Obs2.obsInit_isObs .two V P) (PtCorr2.obsLocInv_init .two V P)
      (PtCorr2.obsSymInv_init .two V P) t ht (by rw [hcR]; exact hε₁') (2 * S2 * B0)
      ((3 * C₁w + 1) * (c * (t Nh).1) * (2 * S2 * B0)) hm0 (by positivity) hVo hWb'
    rw [hcR] at hW1
    intro c' hc'
    refine (hW1 c' hc').trans (ENNReal.ofReal_le_ofReal ?_)
    set r := c * (t Nh).1 with hr
    set M := 2 * S2 * B0 with hM
    have hr0 : 0 ≤ r := mul_nonneg hc0 hg0N
    have hr1 : r ≤ 1 := (mul_le_mul_of_nonneg_left (hgε Nh le_rfl) hc0).trans hcε
    have hC1r : C₁w * r ≤ 1 / 12 :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgε Nh le_rfl) hc0) hC₁w).trans hC₁ε
    have hKwL0 : 0 ≤ Kw / L := div_nonneg hKw hL0.le
    have ha : Kw / L + C₁w * r ≤ 1 / 6 := by linarith
    have hrM : (3 * C₁w + 1) * r * M ≤ (3 * C₁w + 1) * M := by
      have h31 := mul_le_mul_of_nonneg_left hr1 (by positivity : (0 : ℝ) ≤ 3 * C₁w + 1)
      calc (3 * C₁w + 1) * r * M ≤ (3 * C₁w + 1) * 1 * M := mul_le_mul_of_nonneg_right h31 hm0
        _ = (3 * C₁w + 1) * M := by ring
    have h1 : (Kw / L + C₁w * r) * ((3 * C₁w + 1) * r * M) ≤ 1 / 6 * ((3 * C₁w + 1) * M) :=
      mul_le_mul ha hrM (by positivity) (by norm_num)
    have h2 : C₁w * r * M ≤ 1 / 12 * M := mul_le_mul_of_nonneg_right hC1r hm0
    have h3 : M ≤ (3 * C₁w + 1) * M := le_mul_of_one_le_left hm0 hcW1
    have hrM0 : 0 ≤ r * M := mul_nonneg hr0 hm0
    have g1 : (Kw / L + C₁w * r) * ((3 * C₁w + 1) * r * M) ≤ 1 / 6 * ((3 * C₁w + 1) * r * M) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    have g2 : C₁w * (r * M) ≤ (5 / 6 * (3 * C₁w + 1)) * (r * M) :=
      mul_le_mul_of_nonneg_right (by linarith) hrM0
    have hfin : (Kw / L + C₁w * r) * ((3 * C₁w + 1) * r * M) + C₁w * r * M ≤
        (3 * C₁w + 1) * r * M := by linarith
    refine hfin.trans (le_of_eq ?_)
    show (3 * C₁w + 1) * r * M = 2 * (3 * C₁w + 1) * max c 0 * (t Nh).1 * histS R' Nh t ^ 2 * B0
    rw [hM, hS2, hr, max_eq_left hc0]
    ring
  exact hLastW

/-- `lastObsConclW` from its `D_ε` form (`lastObsConclWD`). -/
theorem MasterCore.lastObsConclW {L : ℕ} [NeZero L] (D : MasterCore L) :
    LastObsConclW L D.ℓ D.A D.ρ D.κ D.cm D.cT D.ε D.cWL  :=
  D.lastObsConclWD.adm

end

end Spin2
