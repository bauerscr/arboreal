import Spin2.Cont.ContDiff4a
import Spin2.Cont.ContWire3

/-!
# B3, T6: the bulk inputs and the share deviation along `D_ε`

The `h = 0` trajectories `(b, b − m)` are in `D_ε` but not admissible (`μ_{N_h} ≠ 0`). Copies along
`D_ε` (only `Admissible.1` resp. `loopConclD`/`inDh_rg_of_D` are used):

* **`MasterFacts.cdd_iotaD`**: `T_k(I'(B)_∅) ≤ rpIota 0 0` (`cd4_iota`);
* **`MasterFacts.cdd_regD`**: `A^{|𝓑(W)|}T_k(K♭_k(W)) ≤ 1` under `A⁴c_xǧ_k³ ≤ 1` (`cd4_reg`);
* **`MasterCore.cdd_relDevD`**: `shareDev2 P.a j V_j ≤ 6c_δc²(ǧ_j/(β/4))|β_j|` (`relDev`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **`ι` from `MasterFacts`**: `T_k(I'(B)_∅) ≤ 2e^{3/2}` for every observable `o`. -/
theorem MasterFacts.cdd_iotaD (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    {k : ℕ} (hkN : k < Nh) (o : ObsSt .two L N) (ho : o.IsObs) (a a' : Lam 2 L N)
    (β : (Fin 2 → ℕ) → ℂ) (b' : Fin 2 → ℕ) (hq : b' ∈ blockIdx (L := L) (N := N) k) :
    Tj 2 (L : ℝ) k (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      ((IbO (fun b'' => emb (stVf (R.withMsq m) k (rawHist (R.withMsq m) k
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.1 b'' +
        stDelta (R.withMsq m) k (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) b'') +
        (o.V b'' - rrD a a' β b''))
        (fullW (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (rawD (R.withMsq m) (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.2) o) b' :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (rpIota 0 0) := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have ht := inDh_rg_of_D R' F1 hD k hkN.le
  have hRA' : R'.A = M.core.A := hRA
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by rw [hRA']; exact M.core.hSBx
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hval := hist_valid R' hV t (n := k + 1) (by omega)
  have hVc : ValidCore R' k := (hval k (by omega)).1
  obtain ⟨hb1, hb2⟩ := inV_fullW_bulk_le R' hSB' hV hm1 (by linarith : (0 : ℝ) ≤ betaL L)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' t k hkN.le ht hVc (hm1 k hkN)
    (by rw [hcR]; exact M.core.hcε)
  have hs : 0 < histS R' k t := histS_pos' R' hρ0' hρ8' t k
  refine le_trans (r3_IbO_e_le (c := .two) k hs _ _ b'
    (stVf R' k (rawHist R' k t) (t k).1 (t k).2.1 b' + stDelta R' k (rawHist R' k t) b')
    (((rawHist R' k t).Wl + rawD R' (rawHist R' k t).u (t k).2.2) b') ?_ ?_ ?_
    (by norm_num : (0 : ℝ) ≤ 3 / 2) zero_le_one (hb1 b' hq) (hb2 b' hq))
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  · rw [map_add, bulk_emb, map_sub, ho.V b']
    have : bulk (rrD a a' β b') = 0 := by
      apply Subtype.ext; rw [coe_bulk]; exact rrD_e a a' β b'
    rw [this, sub_zero, add_zero]; rfl
  · rw [← bulkF_apply, bulkF_fullW _ _ ho]; rfl
  · rw [AddMemClass.coe_add, map_add, stVf_eq_kap, eps_VfamL k _ b', eps_stDelta, add_zero]
  · unfold rpIota; ring_nf

set_option maxHeartbeats 1000000 in
/-- **The regulator from `MasterFacts`**: `A^{|𝓑(W)|}T_k(K♭_k(W)) ≤ 1` for connected `W`, under the
scale condition `A⁴c_xǧ_k³ ≤ 1`. -/
theorem MasterFacts.cdd_regD (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    {k : ℕ} (hkN : k < Nh)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 3) ≤ 1) :
    ∀ W, IsConn k W → ENNReal.ofReal ((R.withMsq m).A ^ nb k W) *
      Tj 2 (L : ℝ) k (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rawK (R.withMsq m) (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.2 W : Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1 := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hval := hist_valid R' hV t (n := k + 1) (by omega)
  have HI := (hval k (by omega)).2
  have hρ1 : R'.ρ < 1 := by rw [show R'.ρ = M.core.ρ from hRρ]; linarith
  have hZ := HI.Z_ne_zero hρ1
  have hK := Knorm_rawK R' HI.hu hZ (t k).2.2
  have hx : ‖(t k).2.2‖ ≤ cx M.core.κ M.core.cT * (t k).1 ^ 3 := (hD k hkN.le).2.2.2
  have hA1 : 1 ≤ R'.A := by rw [show R'.A = M.core.A from hRA]; linarith [M.core.hA2]
  exact PtCorr2.r3_reg_of_Knorm hA1 _ (hK.le.trans (ENNReal.ofReal_le_ofReal ((norm_snd_le _).trans hx)))
    (by rw [show R'.A = M.core.A from hRA]; exact hreg)


set_option maxHeartbeats 4000000 in
/-- **The share deviation of the one-point flow is `O(ǧ_j)`** (`PtCorr2.obs_hist_rel2_baseXD`
under the master constants): `D_j ≤ 6c_δc²(ǧ_j/(β/4))|β_j|`, `j ≤ N_h`. -/
theorem MasterCore.cdd_relDevD {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), Obs2.OCoup2.ga V = 0 →
      Obs2.OCoup2.mua V ≠ 0 → 0 < Nh → ∀ j ≤ Nh,
      Obs2.shareDev2 P.a j (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j) ≤
        6 * (D.cδ * (D.c ^ 2 * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 / (betaL L / 4)))) *
          ‖bt2 R P V m b μ₀ j‖ := by
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
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga hmu hNh0
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have ht := inDh_rg_of_D R' F1 hadm Nh le_rfl
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
  obtain ⟨hB0, -, q, -, -, hl⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
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
  have key := PtCorr2.obs_hist_rel2_baseXD R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV hm1 hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P V hga hmu t Nh le_rfl hNh0 (by omega) ht
    (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
    (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk) hLwk
    (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
    (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcgε' hcδ'
    hsumε hT hnn (by rw [hcR]; exact hPr)
  rw [hcR] at key
  exact key

end

end Spin2
