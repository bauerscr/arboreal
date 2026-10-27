import Spin2.Cont.ContWire1
import PtCorr2.Cont.ContTop3

set_option autoImplicit false

/-!
# Top coalescence: the error `E_{N_h}` of the restarted flow and `|β| + D ≤ 2M` under the master
constants

**`MasterCore.ct_restartDT_top`** (copy of the `cw2_restartDT` setup; no new master field): for the
data of `restartDT` (pair vertex `V`), plus `|𝔫^{(2)}_{N_h}| ≤ 1/8` of the reference history
`obsInit V P` (`TopConclD` gives it for `V = zV b`):

* `|β_{m_r+j}| + D_{m_r+j} ≤ 2M_j` for `j ≤ N_h − m_r`;
* the error of the top step `E_{N_h} ≤ (c_δ(cǧ_{N_h})²a_{N_h} + (1/24)(3/4)^{N_h−m_r})M_{N_h−m_r}`
  (`a_{N_h} = |1 − 𝔫F_{N_h}|`; `ct_obs_hist_restartBT_top`, the inputs at `N_h` from
  `C2Ctx.tadInc2_leU` and the band);
* `|𝔫F_{N_h}| ≤ 1/7`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

set_option maxHeartbeats 2000000 in
/-- **The error of the top step of the restarted flow under the master constants.** -/
theorem MasterCore.ct_restartDT_top {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (mr : ℕ) (o' : Obs2.ObsSt .two L N),
      0 < mr → mr ≤ Nh → o'.IsObs → ObsLocInv P mr o' → ObsSymInv mr o' →
      (∀ b, Obs2.Loc2Form P.a (o'.V b : Obs.SA .two (Lam 2 L N)).a) →
      (∀ b, (o'.V b : Obs.SA .two (Lam 2 L N)).a =
        Obs.LocObs.mass2 (o'.V b : Obs.SA .two (Lam 2 L N)).a • Obs.LocObs.pbp P.a) →
    ∀ M₀ k₀ w₀ : ℝ, 0 < M₀ → 0 ≤ k₀ → 0 ≤ w₀ → 120 * D.Bk * (D.c * D.ε) * w₀ ≤ k₀ →
      8 * (PtCorr2.csN 2 : ℝ) * k₀ / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) +
        cbnC * (1280 * Obs2.locK 2 ^ 2 * (8 / (7 * L)) + 1) *
          (D.cWo * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ mr).1) *
            (2 * histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) + w₀) /
          (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) +
        4 / 3 * (2 / (L : ℝ)) +
        5 * D.cP * (D.c * D.ε) * w₀ / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) ≤ 1 / 48 →
      ‖Obs2.betaTot2 (L := L) (N := N) mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr)‖ +
        Obs2.shareDev2 P.a mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr) ≤ M₀ →
      WbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr
        (D.cWo * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ mr).1) *
          (2 * histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) + w₀) →
      KbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr k₀ →
      ‖Obs2.frakN2 P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) Nh‖ ≤ 1 / 8 →
      (∀ j ≤ Nh - mr,
        ‖Obs2.betaTot2 (L := L) (N := N) (mr + j)
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + j))‖ +
          Obs2.shareDev2 P.a (mr + j) (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + j)) ≤
          2 * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) j) ∧
      Obs2.shareErrL1_2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (histWF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histKF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh ≤
        (D.cδ * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ^ 2 *
            ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh‖ +
          1 / 24 * (3 / 4) ^ (Nh - mr)) * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) (Nh - mr) ∧
      ‖Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh‖ ≤ 1 / 7 := by
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
  have hLb' : prodLb ≤ (L : ℝ) := hLb.trans hLr
  have hq56 : 4 / 3 * (2 / (L : ℝ)) ≤ 1 / 56 := by
    have hpl : (1010 : ℝ) ≤ prodLb := by
      unfold prodLb; have := Obs2.one_le_locK 2; nlinarith
    rw [show 4 / 3 * (2 / (L : ℝ)) = 8 / (3 * L) by ring, div_le_div_iff₀ (by positivity)
      (by norm_num)]
    linarith
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V mr o' hmr0 hmrN h0 hl0 hs0 hf0 hp0
    M₀ k₀ w₀ hM0 hk₀ hw₀ hkw hct hbD0 hW0 hK0 hn8N
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
  have X := c2ctx_master R' (by omega) hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε ht
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
  have hε0 : 0 ≤ ε := by have := H.hε; linarith
  have hcg1 : 1 ≤ cgb * cR R' ((L : ℝ) ^ 2) cm C₂x := by rw [hcR, hcgc]; linarith
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
  have hτ : 2 * ce * cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) ≤ 1 / 2 := by
    rw [hcR]
    have e1 : 2 * ce * cgb * (c * ε) = (4 * ceff L (max c 2) * (max B' 0 + 1) * ε) / 2 := by
      rw [hmc, hmB, hce, ← hcgc]; ring
    rw [e1]; linarith
  have hsumε : cδ * (cR R' ((L : ℝ) ^ 2) cm C₂x ^ 2 * (ε / (betaL L / 4))) ≤ 1 / 8 := by
    rw [hcR]
    have e : cδ * (c ^ 2 * (ε / (betaL L / 4))) = cδ * c ^ 2 * (4 / betaL L) * ε := by
      field_simp
    rw [e]; exact hcδε
  set o₀ := Obs2.obsInit .two V P with ho₀d
  have ho₀ : o₀.IsObs := Obs2.obsInit_isObs .two V P
  have hT : ∀ k j, k < j → j < Nh →
      ‖Obs2.tadInc2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) k j‖ ≤
        ce * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := fun k j hkj hj =>
    X.tadInc2_le P _ ho₀ hkj hj
  have hceε : ce * ε ≤ 1 / 8 := by
    have h1 : ce * ε ≤ ce * ε * (max B' 0 + 1) := le_mul_of_one_le_right (by positivity)
      (by linarith)
    have h2 : 4 * ceff L (max c 2) * (max B' 0 + 1) * ε = 4 * (ce * ε * (max B' 0 + 1)) := by
      rw [hmc, hce]; ring
    have h3 : 4 * (ce * ε * (max B' 0 + 1)) ≤ 1 / 2 := h2 ▸ hBτε
    linarith
  have hBg : ∀ k < Nh, ce * (t k).1 ≤ 1 := fun k hk => by
    have hgk : (t k).1 ≤ ε := (ht.1 k hk.le).2.1
    have := mul_le_mul_of_nonneg_left hgk hce0
    linarith
  have hnn : ∀ i < Nh,
      ‖Obs2.frakN2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) i‖ ≤
        cgb * (cR R' ((L : ℝ) ^ 2) cm C₂x * (t i).1) := by
    intro i hi
    rw [hcR, ← mul_assoc, hcgc]
    have h := (hl i hi).2.1
    have hg := (X.hg i hi.le).1.le
    have h' : B' * (t i).1 ≤ (B' + 1) * (t i).1 := by
      rw [add_mul, one_mul]; exact le_add_of_nonneg_right hg
    exact h.trans h'
  have hn8 : ∀ i < Nh, ‖Obs2.frakN2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) i‖ ≤ 1 / 8 :=
    fun i hi => (hl i hi).1
  have hck : 60 * kB (kθ0 L R'.A C₀o ηo) C₁k (8 * cx κ cT) ≤ 64 * kB (kθ0 L R'.A C₀o ηo) C₁k (8 * cx κ cT) := by
    rw [hRA']; linarith
  -- the per-step constant `κ̄ = 64B(cε) + η`
  have hcε0 : 0 ≤ c * ε := mul_nonneg (by linarith) hε0
  have hcε72 : c * ε ≤ 1 / 72 := by
    have h := hBτε
    rw [hmc] at h
    unfold ceff at h
    exact rdt_ce_le hβ0 (by linarith) hε0 (le_max_right B' 0) h
  obtain ⟨hκb, h64κ, hκC, hκε⟩ := rdt_kappa hε₀ hC₁k hBk0 (by positivity : 0 ≤ 8 * cx κ cT)
    hcε0 hcε72 hsmk hεk
  set κb := 64 * Bk * (c * ε) + ε₀ / (120 * (C₁k * ε₀ + 1)) with hκbd
  have hxp : 5 * cP * (cR R' ((L : ℝ) ^ 2) cm C₂x * ε) * w₀ / (histS R' mr t ^ 2 * M₀) ≤
      5 * (prodCP2 L (Cpf L)) * (c * ε) * w₀ / (histS R' mr t ^ 2 * M₀) := by
    rw [hcR]
  -- the inputs at the index `N_h`
  have hTN : ∀ k < Nh,
      ‖Obs2.tadInc2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) k Nh‖ ≤
        ce * (2 / (L : ℝ)) ^ (Nh - k) * (t k).1 := fun k hk => X.tadInc2_leU P _ ho₀ hk le_rfl
  have hBgN : ce * (t Nh).1 ≤ 1 := by
    have hgk : (t Nh).1 ≤ ε := (ht.1 Nh le_rfl).2.1
    have := mul_le_mul_of_nonneg_left hgk hce0
    linarith
  have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    show |m| * _ ≤ 1
    rw [abs_of_pos hm.1]
    have h1 := PtCorr2.msq_mul_pow_le_one (L := L) (N := N) (by omega) (by omega) hm.2
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have h2 : ((L : ℝ) ^ Nh) ^ 2 ≤ (L : ℝ) ^ (2 * (N - 1)) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
    exact (mul_le_mul_of_nonneg_left h2 hm.1.le).trans h1
  have hn7F : ‖Obs2.frakN2F P (Obs2.histCovO R' t) (histVF2 R' P mr o' t) mr Nh‖ ≤ 1 / 7 := by
    have hTall : ∀ k j, k < j → j < Nh + 1 →
        ‖Obs2.tadInc2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) k j‖ ≤
          ce * (2 / (L : ℝ)) ^ (j - k) * (t k).1 := by
      intro k j hkj hjn
      rcases Nat.lt_or_ge j Nh with h | h
      · exact hT k j hkj h
      · obtain rfl : j = Nh := by omega
        exact hTN k hkj
    have hBgall : ∀ k < Nh + 1, ce * (t k).1 ≤ 1 := by
      intro k hk
      rcases Nat.lt_or_ge k Nh with h | h
      · exact hBg k h
      · obtain rfl : k = Nh := by omega
        exact hBgN
    have h1 := frakN2F_mem_le R' P mr o' t h0 o₀ ho₀ (by positivity) hq4 hTall hBgall (i := Nh) hmrN
      (Nat.lt_succ_self Nh)
    have h3 : (1 / 2 : ℝ) ^ (Nh - mr) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h4 : 4 / 3 * (2 / (L : ℝ)) * (1 / 2) ^ (Nh - mr) ≤ 4 / 3 * (2 / (L : ℝ)) :=
      mul_le_of_le_one_right (by positivity) h3
    have h5 : ‖Obs2.frakN2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P o₀ t) Nh‖ ≤ 1 / 8 := hn8N
    linarith
  have key2 := ct_obs_hist_restartBT_top R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P t Nh le_rfl (by omega) ht hmrN o' h0 hl0 hs0
    hf0 hp0 _ hck (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
    (κb := κb) hκb (by rw [hRA', hcR]; exact h64κ)
    hκC
    (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk)
    (by rw [hcR]; exact hκε) hLwk
    (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
    (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcδ' hτ hsumε hM0 hk₀ hw₀
    (by rw [hRA', hcR]; exact hkw) hxp
    hct (by rw [hcR]; rfl) hbD0 (by rw [hcR]; exact hW0) hK0
    o₀ ho₀ hT hBg hnn hn8 hq56 hPB (hCpf L) (by rw [hcR]; exact hεp)
    hLb' hVL hmr0 rfl rfl rfl (by omega) hmN hTN hBgN hn8N
  obtain ⟨hbD, hE⟩ := key2
  refine ⟨hbD, ?_, hn7F⟩
  simp only [add_zero] at hE
  rw [show mr + (Nh - mr) = Nh by omega, hcR] at hE
  refine hE.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl ?_) ?_)
  · have hp : (0 : ℝ) ≤ (3 / 4) ^ (Nh - mr) := by positivity
    refine le_trans (le_of_eq (mul_assoc _ _ _)) ?_
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hct hp) (by norm_num)).trans
      (le_of_eq (by ring))
  · unfold Obs2.rkEnv
    exact mul_nonneg hM0.le (Finset.prod_nonneg fun _ _ => norm_nonneg _)

end

end Spin2
