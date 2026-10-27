import Spin2.Case2.Case2TopMaster

/-!
# `GamTopBd` at both points: the step `N_h` discharged

`GamLastRem(S)` (`‖ρ‖ ≤ c_r‖β‖‖Γ‖`) is replaced by the form relative to `1/|Z_{N_h+1}|` (no lower
bound on `C_N(0,0)` is available, and `1/|Z_{N_h+1}| ≤ e^{K_Z}θ_{N_h}` by `SpinConcl`):

* `ρ_{N_h}`: `‖ρ_{N_h}‖ ≤ c_ρ‖β_{N_h}‖/|Z_{N_h+1}|` is proved (`TopConcl`, `thm_case2_top`);
* `ρ_N` (the last step, `gamRemG` with `stCovN`): named input **`GamRemNZ c_r`**
  (`‖ρ_N‖ ≤ c_r‖β_{N_h+1}‖/|Z_{N_h+1}|`) and its mirror **`GamRemNZS c_r`**.

`gamLast_pureZ`, **`gamLastRel_ofZ`**, **`gamLastRelS_ofZ`**: `BetaLast K_β` and the two bounds give
`GamLastRel` with `c_L = 2K_β(ℓ²e^{K_Z}/14 + c_re^{K_Z})`.

**`thm_gamTopBd_case2'`**: with the constants of `thm_case2_top`, along every admissible
trajectory, `GamTopBd ∧ GamTopBdB` from (H_λ) for `λ`, `GamRemNZ c_r`, `GamRemNZS c_r` and the
smallness `K(K_λ)ǧ_j ≤ 1/2`. `Case2TopStep` (both points) and the `ρ_{N_h}` half of `GamLastRem(S)`
are discharged.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- Pure assembly of `GamLastRel` with the remainders relative to `z = 1/|Z_{N_h+1}| ≤ Eθ`. -/
theorem gamLast_pureZ {β0 β1 Γ C ρ0 ρ1 : ℂ} {Kβ KC cr bθ θ zi E : ℝ}
    (hKC : 0 ≤ KC) (hcr : 0 ≤ cr) (hE : 0 ≤ E) (hθ : 0 ≤ θ) (hzi : zi ≤ E * θ)
    (h0 : ‖β0‖ ≤ Kβ * bθ) (h1 : ‖β1‖ ≤ Kβ * bθ) (hΓ : ‖Γ‖ ≤ KC * θ) (hC : ‖C‖ ≤ KC * θ)
    (hr0 : ‖ρ0‖ ≤ cr * ‖β0‖ * zi) (hr1 : ‖ρ1‖ ≤ cr * ‖β1‖ * zi) :
    ‖β0 * Γ - ρ0‖ + ‖β1 * C - ρ1‖ ≤ 2 * Kβ * (KC + cr * E) * (bθ * θ) := by
  have key : ∀ {β G ρ : ℂ}, ‖β‖ ≤ Kβ * bθ → ‖G‖ ≤ KC * θ → ‖ρ‖ ≤ cr * ‖β‖ * zi →
      ‖β * G - ρ‖ ≤ Kβ * (KC + cr * E) * (bθ * θ) := by
    intro β G ρ hβ hG hρ
    have hρ' : ‖ρ‖ ≤ cr * ‖β‖ * (E * θ) :=
      hρ.trans (mul_le_mul_of_nonneg_left hzi (mul_nonneg hcr (norm_nonneg _)))
    have hX : 0 ≤ KC * θ + cr * (E * θ) := by positivity
    calc ‖β * G - ρ‖ ≤ ‖β * G‖ + ‖ρ‖ := norm_sub_le _ _
      _ ≤ ‖β‖ * (KC * θ) + cr * ‖β‖ * (E * θ) := by
          rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left hG (norm_nonneg _)) hρ'
      _ = ‖β‖ * (KC * θ + cr * (E * θ)) := by ring
      _ ≤ (Kβ * bθ) * (KC * θ + cr * (E * θ)) := mul_le_mul_of_nonneg_right hβ hX
      _ = Kβ * (KC + cr * E) * (bθ * θ) := by ring
  have e : 2 * Kβ * (KC + cr * E) * (bθ * θ) =
      Kβ * (KC + cr * E) * (bθ * θ) + Kβ * (KC + cr * E) * (bθ * θ) := by ring
  rw [e]
  exact add_le_add (key h0 hΓ hr0) (key h1 hC hr1)

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `1/|Z_{N_h+1}|` along the trajectory. -/
abbrev zInvT (Nh : ℕ) (m b μ₀ : ℝ) : ℝ :=
  (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1))⁻¹

/-- **Named input (the last step, pair history)**: `‖ρ_N‖ ≤ c_r‖β_{N_h+1}‖/|Z_{N_h+1}|`. -/
def GamRemNZ (Nh : ℕ) (m b μ₀ cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖gamRemN R Nh m b μ₀ x‖ ≤ cr * ‖btX R m b μ₀ x (Nh + 1)‖ * zInvT R Nh m b μ₀

/-- **Named input (the last step, mirrored history)**. -/
def GamRemNZS (Nh : ℕ) (m b μ₀ cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖gamRemNS R Nh m b μ₀ x‖ ≤ cr * ‖btMir R m b μ₀ x (Nh + 1)‖ * zInvT R Nh m b μ₀

/-- **`GamLastRel` along one trajectory** from `BetaLast`, the bound on `ρ_{N_h}` relative to
`1/|Z_{N_h+1}|` and `GamRemNZ`: `c_L = 2K_β(ℓ²e^{K_Z}/14 + c_re^{K_Z})`. -/
theorem gamLastRel_ofZ (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ KZ Kβ cr : ℝ} (hb : 0 < b)
    (hKZ : 0 ≤ KZ) (hcr : 0 ≤ cr)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hg : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hZ0 : (rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0)
    (hZ : |Real.log ‖(rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
      1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 / b)| ≤
      KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hβ : BetaLast R Nh m b μ₀ Kβ)
    (hr0 : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ‖gamRemX R m b μ₀ x Nh‖ ≤ cr * ‖btX R m b μ₀ x Nh‖ * zInvT R Nh m b μ₀)
    (hr1 : GamRemNZ R Nh m b μ₀ cr) :
    GamLastRel R Nh m b μ₀ (2 * Kβ * (R.ℓ ^ 2 * Real.exp KZ / 14 + cr * Real.exp KZ)) := by
  intro x hx h1 hj
  obtain ⟨hΓ, hC⟩ := gamT_zCovN_le R hP hb hKZ hV hVL hVN hg hg1 hZ0 hZ
  obtain ⟨hβ0, hβ1⟩ := hβ x hx h1 hj
  have hθ : 0 ≤ thJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hg hb).le _
  have hKC : 0 ≤ R.ℓ ^ 2 * Real.exp KZ / 14 := by positivity
  have hzi : zInvT R Nh m b μ₀ ≤ Real.exp KZ * thJ R m b μ₀ Nh :=
    inv_normZ_le (norm_pos_iff.2 hZ0) hg hg1 hb hKZ hZ
  have h := gamLast_pureZ hKC hcr (Real.exp_pos _).le hθ hzi
    (by rw [← mul_assoc]; exact hβ0) (by rw [← mul_assoc]; exact hβ1) hΓ hC (hr0 x hx h1 hj)
    (hr1 x hx h1 hj)
  have e : b * thJ R m b μ₀ Nh * thJ R m b μ₀ Nh =
      varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    rw [mul_assoc, ← sq]; exact b_thJ_sq hg hb
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **`GamLastRelS` along one trajectory** (as `gamLastRel_ofZ`). -/
theorem gamLastRelS_ofZ (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ KZ Kβ cr : ℝ} (hb : 0 < b)
    (hKZ : 0 ≤ KZ) (hcr : 0 ≤ cr)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hg : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hZ0 : (rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0)
    (hZ : |Real.log ‖(rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
      1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 / b)| ≤
      KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hβ : BetaLastS R Nh m b μ₀ Kβ)
    (hr0 : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ‖gamRemMir R m b μ₀ x Nh‖ ≤ cr * ‖btMir R m b μ₀ x Nh‖ * zInvT R Nh m b μ₀)
    (hr1 : GamRemNZS R Nh m b μ₀ cr) :
    GamLastRelS R Nh m b μ₀ (2 * Kβ * (R.ℓ ^ 2 * Real.exp KZ / 14 + cr * Real.exp KZ)) := by
  intro x hx h1 hj
  obtain ⟨hΓ, hC⟩ := gamT_zCovN_le R hP hb hKZ hV hVL hVN hg hg1 hZ0 hZ
  obtain ⟨hβ0, hβ1⟩ := hβ x hx h1 hj
  have hθ : 0 ≤ thJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hg hb).le _
  have hKC : 0 ≤ R.ℓ ^ 2 * Real.exp KZ / 14 := by positivity
  have hzi : zInvT R Nh m b μ₀ ≤ Real.exp KZ * thJ R m b μ₀ Nh :=
    inv_normZ_le (norm_pos_iff.2 hZ0) hg hg1 hb hKZ hZ
  have h := gamLast_pureZ hKC hcr (Real.exp_pos _).le hθ hzi
    (by rw [← mul_assoc]; exact hβ0) (by rw [← mul_assoc]; exact hβ1) hΓ hC (hr0 x hx h1 hj)
    (hr1 x hx h1 hj)
  have e : b * thJ R m b μ₀ Nh * thJ R m b μ₀ Nh =
      varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    rw [mul_assoc, ← sq]; exact b_thJ_sq hg hb
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  ring

end Traj

set_option maxHeartbeats 4000000 in
/-- **`GamTopBd` at both points with the master constants of `thm_case2_top`**, conditional on
(H_λ) for `λ`, the last-step remainders `GamRemNZ c_r`, `GamRemNZS c_r` and the smallness.
`Case2TopStep` and the `ρ_{N_h}` bound are discharged (`TopConcl`). Constant (both points):
`K₄ = 2(1 + K(K_p + (c_e+c_w)(1+3K_p)) + 2·2(1+3K_p)(ℓ²e^{K_Z}/14 + max(c_ρ,c_r)e^{K_Z}))`. -/
theorem thm_gamTopBd_case2' : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG ce cw Kp cρ : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧ 0 ≤ KZ ∧
      SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      0 ≤ ce ∧ 0 ≤ cw ∧ 0 ≤ Kp ∧ 0 ≤ cρ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl cr : ℝ), 0 ≤ Kl → 0 ≤ cr →
      HLam R Nh m b μ₀ lam Kl →
      GamRemNZ R Nh m b μ₀ cr → GamRemNZS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      GamTopBd R Nh m b μ₀ lam
          (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 +
            2 * (2 * (1 + 3 * Kp)) * (ℓ ^ 2 * Real.exp KZ / 14 + max cρ cr * Real.exp KZ))) ∧
        GamTopBdB R Nh m b μ₀ lam
          (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 +
            2 * (2 * (1 + 3 * Kp)) * (ℓ ^ 2 * Real.exp KZ / 14 + max cρ cr * Real.exp KZ))) := by
  obtain ⟨L₀, hL₀⟩ := thm_case2_top
  refine ⟨max L₀ 49, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, B₁, B₂, B₃, cq, B', cδ, cw, ce, cρ, hF, hε1,
    hSp, hMC, hLoop, hcδ, hRelG, hcw, hWK, hce, hGB, hKZ, hGM, hLV, hcρ, hTop⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL49 : 49 ≤ L := le_trans (le_max_right _ _) hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  set Kp := max (lamRelK (betaL L) cg (B₁ + B₂ + B₃) B' cq cδ (eRange (betaL L) Ke 1) 4) 0
    with hKpd
  have hKp : 0 ≤ Kp := le_max_right _ _
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, ce, cw, Kp, cρ, hF, hε1, hKZ, hSp, hMC,
    hce, hcw, hKp, hcρ, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl cr hKl hcr hl hrN hrNS
    hsmall
  have hB := hGB N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL (R.withMsq m) Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk.le).1.le, ((hadm.1 k hk.le).2.1).trans hε1⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  -- (H_λ) for the pair vertices
  have hLC := lamConcl_of hL2 hε1 hSp
  have hpairP : ∀ P : Obs2.ObsPts 2 L N,
      HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp := by
    intro P
    obtain ⟨hB0, -, hloop⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    have h := hLam_case2 hLC hP hi0 hRℓ hRA hRρ (by omega) hm hadm hB0 hcδ (zV_mua_ne hb)
      (hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)) hloop
    exact hLam_mono hb hm.1.le (fun k hk => (hadm.1 k hk.le).1) h (le_max_left _ _)
  have hrel : ∀ P : Obs2.ObsPts 2 L N, Case2Rel R P (zV b) Nh m b μ₀ cδ := fun P =>
    hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)
  have hn : ∀ P : Obs2.ObsPts 2 L N, ∀ k < Nh, ‖nn2 R P (zV b) m b μ₀ k‖ ≤ 1 / 8 := by
    intro P k hk
    obtain ⟨-, -, q, -, -, hl'⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    exact (hl' k hk).1
  have hmono := hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hT := hTop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, hWT, hWM⟩ := wk_inputs hWK N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβ := betaLast_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x _ _ _ => (hT (ptsX x)).1)
  have hβS := betaLastS_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x _ _ _ => (hT (ptsS x)).1)
  have hRS := gamRemTopS_of R hb hKp hce hcw hval hg ha (fun x _ => hpairP _) hB hWM
  have hcγ : 0 ≤ (ce + cw) * (1 + 3 * Kp) := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hKβ : 0 ≤ 2 * (1 + 3 * Kp) := by linarith
  -- the two top steps
  have hcrr : 0 ≤ max cρ cr := le_trans hcρ (le_max_left _ _)
  have hVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  obtain ⟨hZ0, hZ⟩ :=
    (hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.2.2.1 m hm b μ₀ hadm Nh le_rfl
  have hzi0 : 0 ≤ zInvT R Nh m b μ₀ := inv_nonneg.2 (norm_nonneg _)
  have hr0X : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ‖gamRemX R m b μ₀ x Nh‖ ≤ max cρ cr * ‖btX R m b μ₀ x Nh‖ * zInvT R Nh m b μ₀ :=
    fun x _ _ _ => (hT (ptsX x)).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) hzi0)
  have hr0S : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ‖gamRemMir R m b μ₀ x Nh‖ ≤ max cρ cr * ‖btMir R m b μ₀ x Nh‖ * zInvT R Nh m b μ₀ :=
    fun x _ _ _ => (hT (ptsS x)).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) hzi0)
  have hr1X : GamRemNZ R Nh m b μ₀ (max cρ cr) := fun x hx h1 hj =>
    (hrN x hx h1 hj).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) hzi0)
  have hr1S : GamRemNZS R Nh m b μ₀ (max cρ cr) := fun x hx h1 hj =>
    (hrNS x hx h1 hj).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) hzi0)
  have hgN : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := (hadm.1 Nh le_rfl).1
  have hgN1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 := ((hadm.1 Nh le_rfl).2.1).trans hε1
  have hLast := gamLastRel_ofZ R hP hb hKZ hcrr hval hvalL hVN hgN hgN1 hZ0 hZ hβ hr0X hr1X
  have hLastS := gamLastRelS_ofZ R hP hb hKZ hcrr hval hvalL hVN hgN hgN1 hZ0 hZ hβS hr0S hr1S
  rw [hRℓ] at hLast hLastS
  have hcL : 0 ≤ 2 * (2 * (1 + 3 * Kp)) * (ℓ ^ 2 * Real.exp KZ / 14 + max cρ cr * Real.exp KZ) := by
    positivity
  exact ⟨gamTopBd_flow hF hε1 hL8 hMC hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam
      Kl Kp ce cw _ hKl hKp hce hcw hcL hl (fun x _ => hpairP _) (gamBulkRel_of_A R hB) hWT hLast
      hsmall,
    gamTopBdB_flow hε1 hL8 hMC hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam
      Kl Kp _ _ hKl hKp hcγ hcL hl (fun x _ => hpairP _) hRS hLastS hsmall⟩

end

end Spin2
