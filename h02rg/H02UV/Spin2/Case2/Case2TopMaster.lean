import Spin2.Case2.Case2RelPairL
import Spin2.Gam.GamLastBd
import Spin2.Case2.Case2Top

/-!
# The step `N_h` under the master constants: `Case2TopStep` and `ρ_{N_h}`

* `topReq L A c c' ε`: `(4L² + 3)·c_eff·ε ≤ 1/8` (`topReq_ev`: eventually for small `ε`); it makes
  the crude bound `|𝔫^{(2)}_{N_h}| ≤ (4L² + 3)c_effǧ_{N_h}` (`C2Ctx.frakN2_top_le`) at most `1/8`.
* **`TopConcl c_ρ`**: along every admissible trajectory, for every point configuration `P` and the
  pair vertex `zV b`: `Case2TopStep` (`|𝔫_{N_h}| ≤ 1/8`,
  `|err_{N_h}| ≤ (1/8)|β_{N_h}(1 − 𝔫_{N_h})|`) and
  `|ρ_{N_h}| ≤ c_ρ|β_{N_h}|/|Z_{N_h+1}|` (`ρ_{N_h} = gamRem2` of the pair history).
* **`thm_case2_top`**: copy of `thm_case2_pairL` with the ε-requirement
  `c2RelReq ∧ gbEReq ∧ topReq`; in addition `0 ≤ c_ρ` and `TopConcl c_ρ`, with
  `c_ρ = (256c_N c_W B_k + 2c_BQ₁c_W)(9/8)ℓ² + K_b(ℓ, max(c_μ,0), 16ℓ²/49)`.
  The step `N_h` uses `obs_hist_rel2_top` (the relative recursion closed at horizon `N_h` plus one
  error bound, `RelRec.E_top`), `prodBd2_histL`, `C2Ctx.tadInc2_leU`, and for `ρ_{N_h}` the split
  `gamRem2_split_histU`, `gamRem2_top_le`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- The requirement on `ε` for the step `N_h`: `(4L² + 3)·c_eff(L, c)·ε ≤ 1/8`. -/
def topReq (L : ℕ) (_A c _c' ε : ℝ) : Prop := (4 * (L : ℝ) ^ 2 + 3) * ceff L c * ε ≤ 1 / 8

theorem topReq_ev (L : ℕ) (A c c' : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), topReq L A c c' ε := by
  filter_upwards [ev_lin ((4 * (L : ℝ) ^ 2 + 3) * ceff L c) (by norm_num : (0 : ℝ) < 1 / 8)]
    with ε h
  exact h

/-- **The step `N_h` along the admissible trajectories**: `Case2TopStep` for the pair vertex at
every point configuration, and `|ρ_{N_h}| ≤ c_ρ|β_{N_h}|/|Z_{N_h+1}|`. -/
def TopConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cρ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ P : Obs2.ObsPts 2 L N,
    Case2TopStep R P (zV b) Nh m b μ₀ ∧
    ‖Obs2.gamRem2 (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh‖ ≤
      cρ * ‖bt2 R P (zV b) m b μ₀ Nh‖ *
        (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1))⁻¹

set_option maxHeartbeats 16000000 in
/-- **`thm_case2_pair` with the validity of the last step**: the same construction through
`thm_flow_masterL` (same `Aext`/`Eext` requirements); in addition `0 ≤ K_Z`, `GMonoConcl` and
`LastValidConcl`. -/
theorem thm_case2_top : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG B₁ B₂ B₃ cq B' cδ cw ce cρ : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      LoopConcl L ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B' ∧ 0 ≤ cδ ∧
      RelConcl2G L ℓ A ρ κ cm cT ε cδ ∧ 0 ≤ cw ∧ WKConcl L ℓ A ρ κ cm cT ε cw ∧
      0 ≤ ce ∧ GamBulkConcl L ℓ A ρ κ cm cT ε ce ∧ 0 ≤ KZ ∧ GMonoConcl L ℓ A ρ κ cm cT ε ∧
      LastValidConcl L ℓ ρ ∧ 0 ≤ cρ ∧ TopConcl L ℓ A ρ κ cm cT ε cρ := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hnu⟩ := nu_sharp
  obtain ⟨Cpf, εpf, L₀p, hCpf, hPf⟩ := prod_raw_step
  obtain ⟨C₀o, ηo, L₀k, hC₀o, hηo, hk⟩ := kobs_bounds
  obtain ⟨Kw, L₀w, hKw, hw⟩ := wobs_bounds
  obtain ⟨Lo, hLod⟩ : ∃ Lo : ℕ, Lo = max (max L₀k L₀w)
      (max (⌈144 * C₀o + 12 * Kw⌉₊ + 8) (max L₀p ⌈prodLb⌉₊)) := ⟨_, rfl⟩
  have hLk : L₀k ≤ Lo := hLod ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLw' : L₀w ≤ Lo := hLod ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLp : L₀p ≤ Lo := hLod ▸ le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hLb : prodLb ≤ (Lo : ℝ) := by
    have h1 : ⌈prodLb⌉₊ ≤ Lo := hLod ▸ le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hLc8 : ⌈144 * C₀o + 12 * Kw⌉₊ + 8 ≤ Lo :=
    hLod ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hLc : 144 * C₀o + 12 * Kw + 8 ≤ (Lo : ℝ) := by
    have h2 := Nat.le_ceil (144 * C₀o + 12 * Kw)
    have h3 : ((⌈144 * C₀o + 12 * Kw⌉₊ + 8 : ℕ) : ℝ) ≤ Lo := by exact_mod_cast hLc8
    push_cast at h3
    linarith
  have h7 : 7 ≤ Lo := by omega
  obtain ⟨L₀, hL₀⟩ := thm_flow_masterL (fun L A => 2 ≤ A ∧ obsAReq C₀o ηo Lo L A)
    (fun L => by
      obtain ⟨A₀, hA₀⟩ := obsAReq_ev hC₀o hηo hk hLk (by linarith) L
      exact ⟨max 2 A₀, fun A hA => ⟨le_trans (le_max_left _ _) hA,
        hA₀ A (le_trans (le_max_right _ _) hA)⟩⟩)
    (fun L A c c' ε => c2RelReq Cq Cl cS C₀o ηo Kw Lo Cpf εpf L A c c' ε ∧ gbEReq L A c c' ε ∧
      topReq L A c c' ε)
    (fun L A c c' => (c2RelReq_ev Cq Cl cS Cpf εpf hw hLw' h7
      (fun L _ hL => (hPf L (hLp.trans hL)).1) L A c c').and
        ((gbEReq_ev L A c c').and (topReq_ev L A c c')))
  refine ⟨max (max L₀ (max Lo (max 49 ⌈pauliL0 2⌉₊))) gbL0, fun L _ hLL => ?_⟩
  have hL := le_trans (le_max_left _ _) hLL
  have hLg : gbL0 ≤ L := le_trans (le_max_right _ _) hLL
  have hlog := log_ge_gbLog hLg
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp,
    ⟨hA2, hAx⟩, -, hLV, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hXm⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hLo : Lo ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLr : (Lo : ℝ) ≤ L := by exact_mod_cast hLo
  have hL49 : 49 ≤ L := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hL
  have hLpl : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hL)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
  have hMag := magConcl_of hL2 hε1 hKZ hKG hSp
  have hGM : GMonoConcl L ℓ A ρ κ cm cT ε :=
    gMonoConcl_of (by omega) hC2.2.2.2.2.2.2.1.le
      (fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
        ⟨(hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).1.h6,
          (hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).2.2⟩)
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id hC2
  let R₀ : RGPar 2 L 1 := ⟨Pc, 0, ℓ, A, 0, ρ⟩
  obtain ⟨-, hθ⟩ := hAx hLo
  obtain ⟨ζbar, K, cS2, -, hK, hcS2, hLc', hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp,
    ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁, hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε⟩ :=
    (hEx R₀ rfl).1 hLo hAx
  obtain ⟨ζg, Kg, -, hKg, hCp, hζg, hKgε, -⟩ := (hEx R₀ rfl).2.1 (by omega)
  have htopR := (hEx R₀ rfl).2.2
  obtain ⟨-, hPB⟩ := hPf L (hLp.trans hLo)
  set c := cR R₀ ((L : ℝ) ^ 2) cm C₂x with hc
  set ce := ceff L c with hce
  set B' := c2Bp Cq Cl cS L K cS2 c (cx κ cT) with hB'
  have hNu := hnu L hL8 hLpl
  have hβ2 := betaL_ge (by omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hθ0 : 0 ≤ kθ0 L A C₀o ηo := by
    unfold kθ0
    exact mul_nonneg hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hLwk : Kw / L ≤ 1 / 12 := by
    rw [div_le_iff₀ hL0]; linarith
  -- the loop conclusion (as in `thm_multiscale_case2C`)
  have hLoop : LoopConcl L ℓ A ρ κ cm cT ε (bubB L ce K cS2) (nuB L Cq Cl cS (cx κ cT) c ce)
      (9 / 64 * ce ^ 2) (7 * ce) B' := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
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
  -- nonnegativity of the constants
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
  have hRel : RelConcl2 L ℓ A ρ κ cm cT ε (cδ * c ^ 2) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga hmu
    rcases Nat.eq_zero_or_pos Nh with h0 | hNh0
    · intro k hk; omega
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
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
    have key := obs_hist_rel2 R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV hm1 hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P V hga hmu t Nh le_rfl hNh0 (by omega) ht
      (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
      (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk) hLwk
      (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
      (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcgε' hcδ'
      hsumε hT hnn (by rw [hcR]; exact hPr)
    rw [hcR] at key
    intro k hk
    obtain ⟨h1, h2⟩ := key k hk
    have e : cδ * c ^ 2 * (t k).1 ^ 2 = cδ * (c * (t k).1) ^ 2 := by ring
    rw [e]
    exact ⟨h1, h2⟩
  have hRelG := relConcl2G_of hRel
  have hcδc : 0 ≤ cδ * c ^ 2 := by positivity
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
  obtain ⟨cwF, hcwF⟩ : ∃ x : ℝ, x = max c 0 * Kw' := ⟨_, rfl⟩
  have hcw0 : 0 ≤ cwF := by rw [hcwF]; exact mul_nonneg (le_max_right _ _) hKw0
  have hWK : WKConcl L ℓ A ρ κ cm cT ε cwF := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V0 hmu0 k hk
    rw [gamWK2_traj_gaZero, bt2_gaZero]
    set V := PtCorr2.gaZero V0 with hVd
    have hga : Obs2.OCoup2.ga V = 0 := rfl
    have hmu : Obs2.OCoup2.mua V ≠ 0 := hmu0
    rcases Nat.eq_zero_or_pos Nh with h0 | hNh0
    · omega
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
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
    have key := PtCorr2.obs_hist_rel2_base R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV hm1 hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P V hga hmu t Nh le_rfl hNh0 (by omega) ht
      (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
      (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk) hLwk
      (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
      (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcgε' hcδ'
      hsumε hT hnn (by rw [hcR]; exact hPr)
    rw [hcR, hRA'] at key
    have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
    have hc0 : 0 ≤ c := by linarith
    have hcwF0 : 0 ≤ cwF := by rw [hcwF]; exact mul_nonneg (le_max_right _ _) hKw0
    have hg0 : 0 ≤ (t k).1 := (X.hg k hk.le).1.le
    have hzA : 0 ≤ zA L m k := zA_nonneg L hm.1.le k
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hz : Obs2.gamWK2 (R.withMsq m) P (Obs2.obsInit .two V P)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) 0 = 0 :=
        PtCorr2.gamWK2_zero _ P V (traj_zero_X R m b μ₀)
      rw [hz, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hcwF0 (add_nonneg hg0 hzA)) (norm_nonneg _))
        (norm_nonneg _)
    obtain ⟨hb0, hWb, hKb⟩ := key k hk.le
    have hkN : k + 1 < N := by omega
    have hs2 : 0 ≤ histS R' k t ^ 2 := sq_nonneg _
    have hbd := PtCorr2.gamWK2_le R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hLpl P
      (Obs2.obsInit .two V P) (PtCorr2.obsLocInv_init .two V P) t k hk hkN
      ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
      (by positivity) (by positivity) hWb hKb
    -- the lower bound `|Z_{k+1}Γ_k| ≥ 1`
    have hlow := X.gamInt_lower hm.1 hm.2 hCp hKg hζg hKgε hgε hlog hk1 hk
    have hℓ' : R'.ℓ = ℓ := hRℓ
    have hVk := hV k hk
    have hρ1 : R'.ρ < 1 := by linarith [hVk.2.2.2.2.1]
    have HIk := rawInv_hist R' hVk.2.2.2.1 k (fun i hi => hV i (by omega)) t
    have hZk : (rawHist R' k t).Z ≠ 0 := HIk.Z_ne_zero hρ1
    have hsG := histS_sq_le_gam R' t k hρ0' hρ8' hZk hlow
    rw [hℓ'] at hsG
    have hs : 0 < PtCorr2.histS R' k t := mul_pos (fscale_pos hZk) (Fact.out : 0 < R'.ℓ)
    have hCaa : ‖Obs2.histCovO R' t k P.a P.a‖ = ‖gamT R m b μ₀ k‖ := by
      rw [histCov_gamInt_at R hP m t k P.a]; rfl
    rw [hCaa] at hbd
    have hr1 : c * (t k).1 ≤ 1 := (mul_le_mul_of_nonneg_left (hgε k hk.le) hc0).trans hcε
    have hcc : max c 0 = c := max_eq_left hc0
    rw [hcwF, hcc]
    exact wk_alg hbd rfl rfl hs hsG rfl (mul_nonneg hc0 hg0) hr1 hzA hc0
      (Nat.cast_nonneg _) (by linarith) hBk0 (Nat.cast_nonneg _)
      (by have := one_le_Q1 (d := 2) (by norm_num); linarith) (norm_nonneg _) (norm_nonneg _)
  have hGB : GamBulkConcl L ℓ A ρ κ cm cT ε
      (gbK L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49)) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm a k hk
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
    have hSB' : StepBounds L R'.A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx := by rw [hRA']; exact hSBx
    have hmsq : R'.msq ∈ mRange L N := hm
    have hβ0 : 0 ≤ betaL L := by have := betaL_ge (by omega : 8 ≤ L); linarith
    have X := c2ctx_master R' hNh hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε ht
    rw [hcR] at X
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
    have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
    have hDh : ∀ j ≤ Nh, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t := fun j hj =>
      ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
    have hzy : ∀ j < Nh, ‖(rawHist R' j t).z + (rawHist R' j t).y‖ ≤
        2 * cZ R' * (t j).1 * zH R' t j := by
      intro j hj
      obtain ⟨hz, hy, -⟩ := apriori R' hSB' hV hm1 hβ0 (by norm_num) H j hj.le t (hDh j hj.le)
      have hZ := zH_pos R' hρ0' hρ8' t j
      have hZne : (rawHist R' j t).Z ≠ 0 := norm_pos_iff.1 hZ
      have e : (rawHist R' j t).z + (rawHist R' j t).y =
          (rawHist R' j t).Z * ((rawHist R' j t).z / (rawHist R' j t).Z +
            (rawHist R' j t).y / (rawHist R' j t).Z) := by field_simp
      rw [e, norm_mul]
      have := (norm_add_le _ _).trans (add_le_add hz hy)
      have e2 : 2 * cZ R' * (t j).1 * zH R' t j = zH R' t j * (cZ R' * (t j).1 + cZ R' * (t j).1) := by
        ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left this hZ.le
    have h := X.gamBulk_rel_ctx hP hm.1 hm.2 hCp hKg hζg hKgε hgε hlog hzy a hk
    have hℓ' : R'.ℓ = ℓ := hRℓ
    have hcZ : cZ R' = 16 * ℓ ^ 2 / 49 := by unfold cZ; rw [hℓ']
    have hle : gbK L R'.ℓ (cmu ((L : ℝ) ^ 2) cm) (cZ R') ≤
        gbK L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) := by
      rw [hcZ, hℓ']
      unfold gbK gbKb gbK0
      have h1 := le_max_left (cmu ((L : ℝ) ^ 2) cm) 0
      have h2 : 0 ≤ (L : ℝ) ^ 2 * ℓ ^ 4 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * ℓ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h1 h2
      have := mul_le_mul_of_nonneg_left h1 h3
      nlinarith
    have hga : 0 ≤ (t k).1 + zA L m k :=
      add_nonneg (X.hg k hk.le).1.le (zA_nonneg L hm.1.le k)
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hga) (norm_nonneg _))

  -- the step `N_h`: `Case2TopStep` and `ρ_{N_h}`
  set cρF : ℝ := (256 * (csN 2 : ℝ) * (3 * C₁w + 1) * Bk + 2 * (cBn : ℝ) * Q1 2 * (3 * C₁w + 1)) *
      (9 / 8 * ℓ ^ 2) + gbKb L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) with hcρF
  have hcρ0 : 0 ≤ cρF := by
    have : (0 : ℝ) ≤ csN 2 := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
    have : 0 ≤ 3 * C₁w + 1 := by linarith
    have : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
    have : 0 ≤ gbKb L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) :=
      gbKb_nonneg (le_max_right _ _) (by positivity)
    positivity
  have hTop : TopConcl L ℓ A ρ κ cm cT ε cρF := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P
    have hb : 0 < b := by
      have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
    obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    have hsplit := gamRem2_split_histU (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hV hVL (Obs2.obsInit_isObs .two (zV b) P)
      (fun b' => Obs2.obsInit_two_form P (zV b) b') (le_refl Nh)
    have eβ : Obs2.betaTot2 (L := L) (N := N) Nh (Obs2.histVO2 (R.withMsq m) P
        (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh) =
        bt2 R P (zV b) m b μ₀ Nh := rfl
    rw [hsplit, eβ, gamWK2_traj_gaZero R P (zV b), bt2_gaZero R P (zV b)]
    unfold Case2TopStep
    rw [nn2_gaZero R P (zV b), err2_gaZero R P (zV b), bt2_gaZero R P (zV b)]
    set V := PtCorr2.gaZero (zV b) with hVd
    have hga : Obs2.OCoup2.ga V = 0 := rfl
    have hmu : Obs2.OCoup2.mua V ≠ 0 := zV_mua_ne hb
    set R' := R.withMsq m with hR'
    obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
    have hRA' : R'.A = A := hRA
    have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
    have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
    have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
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
    have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
    have hg0N : 0 ≤ (t Nh).1 := (X.hg Nh le_rfl).1.le
    have hc0 : 0 ≤ c := by linarith
    have hPr := prodBd2_histL R' hPB (hCpf L) hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H
      hρ0' hρ8' P V hga t (Nh + 1) rfl (by omega) hVL ht (by rw [hcR]; exact hεp) (hLb.trans hLr)
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
    -- the inputs at the index `N_h`
    have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
      rw [abs_of_nonneg X.hm0]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
    have hTN : ∀ k < Nh,
        ‖Obs2.tadInc2 P (Obs2.histCovO R' t) (Obs2.histVO2 R' P (Obs2.obsInit .two V P) t) k Nh‖ ≤
          ce * (2 / (L : ℝ)) ^ (Nh - k) * (t k).1 := fun k hk =>
      X.tadInc2_leU P _ (Obs2.obsInit_isObs .two V P) hk le_rfl
    have hnNt : ‖Obs2.frakN2 P (Obs2.histCovO R' t)
        (Obs2.histVO2 R' P (Obs2.obsInit .two V P) t) Nh‖ ≤ 1 / 8 := by
      refine (X.frakN2_top_le P _ (Obs2.obsInit_isObs .two V P)).trans ?_
      have h1 : (4 * (L : ℝ) ^ 2 + 3) * ce * (t Nh).1 ≤ (4 * (L : ℝ) ^ 2 + 3) * ce * ε :=
        mul_le_mul_of_nonneg_left (hgε Nh le_rfl) (by positivity)
      exact h1.trans htopR
    have key := obs_hist_rel2_top R' (by rw [hRA']; exact hKB) hC₁k hWB hC₁w hSB' hV hm1 hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' hρ8' P V hga hmu t Nh le_rfl (by omega) ht
      (by rw [hRA']; exact hθ0) (by rw [hRA']; exact hθ) (by rw [hRA', hcR]; exact hsmk)
      (by rw [hcR]; exact hcε) (by rw [hcR]; exact hεε) (by rw [hRA', hcR]; exact hεk) hLwk
      (by rw [hcR]; exact hC₁ε) (by rw [hcR]; exact hε₁') (by linarith) le_rfl
      (by have := H.h6; linarith) hcgb0 hcP0 hcδ0 hce0 (by positivity) hq4 hcg1 hcgε' hcδ'
      hsumε hT hnn rfl hVL hmN (by omega) hTN (hnNt.trans (by norm_num)) (by rw [hcR]; exact hPr)
    rw [hcR, hRA'] at key
    obtain ⟨hbase, herr⟩ := key
    refine ⟨⟨hnNt, herr.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩, ?_⟩
    · -- `c_δ(cǧ_{N_h})² ≤ 1/8`
      have hβ2' : 0 < betaL L := by linarith
      have hg1 : (t Nh).1 ≤ ε := hgε Nh le_rfl
      have hgg : (t Nh).1 ^ 2 ≤ ε / (betaL L / 4) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : betaL L * (t Nh).1 ≤ 1 / 2 :=
          (mul_le_mul_of_nonneg_left hg1 hβ2'.le).trans hβε
        nlinarith
      have hsum' : cδ * (c ^ 2 * (ε / (betaL L / 4))) ≤ 1 / 8 := by rw [hcR] at hsumε; exact hsumε
      have := mul_le_mul_of_nonneg_left hgg (mul_nonneg hcδ0 (sq_nonneg c))
      nlinarith
    · -- `ρ_{N_h}`
      obtain ⟨-, hWb, hKb⟩ := hbase Nh le_rfl
      have hDh : InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t := ht
      have hzy : ‖(rawHist R' Nh t).z + (rawHist R' Nh t).y‖ ≤
          2 * cZ R' * (t Nh).1 * zH R' t Nh := by
        obtain ⟨hz, hy, -⟩ := apriori R' hSB' hV hm1 hβ0 (by norm_num) H Nh le_rfl t hDh
        have hZ := zH_pos R' hρ0' hρ8' t Nh
        have hZne : (rawHist R' Nh t).Z ≠ 0 := norm_pos_iff.1 hZ
        have e : (rawHist R' Nh t).z + (rawHist R' Nh t).y =
            (rawHist R' Nh t).Z * ((rawHist R' Nh t).z / (rawHist R' Nh t).Z +
              (rawHist R' Nh t).y / (rawHist R' Nh t).Z) := by field_simp
        rw [e, norm_mul]
        have := (norm_add_le _ _).trans (add_le_add hz hy)
        have e2 : 2 * cZ R' * (t Nh).1 * zH R' t Nh =
            zH R' t Nh * (cZ R' * (t Nh).1 + cZ R' * (t Nh).1) := by ring
        rw [e2]
        exact mul_le_mul_of_nonneg_left this hZ.le
      have hr1 : c * (t Nh).1 ≤ 1 := (mul_le_mul_of_nonneg_left (hgε Nh le_rfl) hc0).trans hcε
      have hρb := gamRem2_top_le R' X hSB' hm1 hmN hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hLpl P V
        ht hzy (by linarith : (1 : ℝ) ≤ 3 * C₁w + 1) hBk0 (mul_nonneg hc0 hg0N) hr1 hWb hKb
      refine hρb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
        (norm_nonneg _)) (inv_nonneg.2 (zH_pos R' hρ0' hρ8' t (Nh + 1)).le))
      have hℓ' : R'.ℓ = ℓ := hRℓ
      have hcZ : cZ R' = 16 * ℓ ^ 2 / 49 := by unfold cZ; rw [hℓ']
      rw [hℓ', hcZ, hcρF]
      refine add_le_add le_rfl ?_
      unfold gbKb
      have h1 := le_max_left (cmu ((L : ℝ) ^ 2) cm) 0
      have h2 : 0 ≤ (L : ℝ) ^ 2 * ℓ ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_left h1 h2
      nlinarith

  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, bubB L ce K cS2,
    nuB L Cq Cl cS (cx κ cT) c ce, 9 / 64 * ce ^ 2, 7 * ce, B', cδ * c ^ 2, cwF,
    gbK L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49), cρF, hC2, hε1, hSp, hMag, hLoop, hcδc,
    hRelG, hcw0, hWK, gbK_nonneg (le_max_right _ _) (by positivity), hGB, hKZ, hGM, hLV, hcρ0,
    hTop⟩



end

end Spin2
