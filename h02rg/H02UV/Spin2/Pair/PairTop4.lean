import Spin2.Final.FinalWire

/-!
# Top coalescence: the one-point parts at `N - 1` and `γ_{a,N}` for any `x` (T7)

Along a windowed trajectory (`D_ε` up to `N_h`, `N_h ≥ 1`), for every `x` (no coalescence
condition), with `M = M_{N_h}(λ)`, `ǧ = ǧ_{N_h}`:

* `‖γ_{0,N-1} - M‖ ≤ K_O‖M‖ǧ`, `‖γ_{x,N-1} - M‖ ≤ K_O‖M‖ǧ` (`uA`, `uB` at `N_h + 1`): the
  `j = N_h` estimate of `zBelowU1_of_forms` (the forms `γ_{N_h} = M_{N_h}(λ^γ)`, all `k < N_h`,
  from `WKConclD`, `GamBulkRelA` for every point) and one step of the one-point flow
  (`uA_succ_pos`, `uMir_succ_pos`; `‖β_{N_h}Γ_{N_h} - ρ_{N_h}‖ ≤ K_β(K_C + c_rE)bθ²`,
  `bθ² = ϑǧ`, `TopConclD`);
* `‖γ_{a,N}‖ ≤ K₄‖M‖` (`gamTopBd_of` at `j = N_h`; the last step by `gamRemNP_le`).

**`gamStep_pureZ`** (pure), **`MasterFacts.oneTopD`**.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- One top step, pure: `‖βΓ - ρ‖ ≤ K_β(K_C + c_rE)(bθ·θ)`. -/
theorem gamStep_pureZ {β Γ ρ : ℂ} {Kβ KC cr bθ θ zi E : ℝ}
    (hKC : 0 ≤ KC) (hcr : 0 ≤ cr) (hE : 0 ≤ E) (hθ : 0 ≤ θ) (hzi : zi ≤ E * θ)
    (h0 : ‖β‖ ≤ Kβ * bθ) (hΓ : ‖Γ‖ ≤ KC * θ) (hr0 : ‖ρ‖ ≤ cr * ‖β‖ * zi) :
    ‖β * Γ - ρ‖ ≤ Kβ * (KC + cr * E) * (bθ * θ) := by
  have hρ' : ‖ρ‖ ≤ cr * ‖β‖ * (E * θ) :=
    hr0.trans (mul_le_mul_of_nonneg_left hzi (mul_nonneg hcr (norm_nonneg _)))
  have hX : 0 ≤ KC * θ + cr * (E * θ) := by positivity
  calc ‖β * Γ - ρ‖ ≤ ‖β * Γ‖ + ‖ρ‖ := norm_sub_le _ _
    _ ≤ ‖β‖ * (KC * θ) + cr * ‖β‖ * (E * θ) := by
        rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left hΓ (norm_nonneg _)) hρ'
    _ = ‖β‖ * (KC * θ + cr * (E * θ)) := by ring
    _ ≤ (Kβ * bθ) * (KC * θ + cr * (E * θ)) := mul_le_mul_of_nonneg_right h0 hX
    _ = Kβ * (KC + cr * E) * (bθ * θ) := by ring

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The constant of one top step: `c_L = 2K_β(ℓ²e^{K_Z}/14 + c_re^{K_Z})`, `K_β = 2(1 + 3K_p)`. -/
def topCL : ℝ :=
  2 * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 +
    max M.core.cρ M.fwcr * Real.exp M.core.KZ)

/-- The `λ^γ` constant `F' = max(f(K_p + c_γ), 0)`. -/
def topF' : ℝ :=
  max (spinMK L M.core.cg M.core.Ke M.core.KZ
    (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0

theorem topCL_nonneg : 0 ≤ M.topCL := by
  unfold topCL
  have hKp := M.Kp_nonneg
  have hcρ := M.cρ_nonneg
  have hcr : 0 ≤ max M.core.cρ M.fwcr := le_trans hcρ (le_max_left _ _)
  positivity

theorem topF'_nonneg : 0 ≤ M.topF' := le_max_right _ _

set_option maxHeartbeats 8000000 in
/-- **The one-point parts at `N - 1` and `γ_{a,N}` for any `x`** (windowed trajectory,
`N_h ≥ 1`). -/
theorem oneTopD {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (lam : ℕ → ℂ) {Kl : ℝ} (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) (x : Lam 2 L N) :
    ‖uA R m b μ₀ x (Nh + 1) - Mmag R m b μ₀ lam Nh‖ ≤
        (2 * (M.topF' + max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0) +
          M.topCL) * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ∧
      ‖uB R m b μ₀ x (Nh + 1) - Mmag R m b μ₀ lam Nh‖ ≤
        (2 * (M.topF' + max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0) +
          M.topCL) * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ∧
      ‖gamNa R Nh m b μ₀ x‖ ≤ 2 * (1 + M.topF' + M.topCL) * ‖Mmag R m b μ₀ lam Nh‖ := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hε1 := M.eps_le
  have hF := M.flow
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hce := M.cGB_nonneg
  have hcw := M.cw_nonneg
  have hKZ := M.KZ_nonneg
  have hcρ := M.cρ_nonneg
  have hcWL := M.cWL_nonneg
  have hN2 : 2 ≤ N := by omega
  have hNh1 : 1 ≤ Nh := by omega
  have hB := M.gamBulkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL (R.withMsq m) Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hCf0 : 0 ≤ M.core.Cf := hF.2.2.2.2.2.2.2.2.2.2.1
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk.le).1.le, ((hD k hk.le).2.1).trans hε1⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  have hpairP := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD
  have hrel : ∀ P : Obs2.ObsPts 2 L N, Case2Rel R P (zV b) Nh m b μ₀ M.core.cRel := fun P =>
    M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b) (zV_mua_ne hb)
  have hn : ∀ P : Obs2.ObsPts 2 L N, ∀ k < Nh, ‖nn2 R P (zV b) m b μ₀ k‖ ≤ 1 / 8 := by
    intro P k hk
    obtain ⟨-, -, q, -, -, hl'⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b)
    exact (hl' k hk).1
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hT := M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  obtain ⟨-, -, -, hWM⟩ := wk_inputsD M.wkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hWX : ∀ k < Nh, ‖gamWKX R m b μ₀ x k‖ ≤
      M.core.cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) *
        ‖btX R m b μ₀ x k‖ * ‖gamT R m b μ₀ k‖ := fun k hk =>
    M.wkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b) (zV_mua_ne hb) k hk
  have hcr : 0 ≤ M.fwcr := by
    unfold fwcr
    have : (0 : ℝ) ≤ PtCorr2.cBn := Nat.cast_nonneg _
    have : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
    positivity
  have hcrr : 0 ≤ max M.core.cρ M.fwcr := le_trans hcρ (le_max_left _ _)
  have hVN := M.lastValid N R hP hRℓ hRρ hN2 Nh hNh m hm
  obtain ⟨hZ0, hZ⟩ :=
    (M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ₀ hD Nh le_rfl
  have hgN : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := (hD Nh le_rfl).1
  have hgN1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 := ((hD Nh le_rfl).2.1).trans hε1
  have hG : GlueOut (R.withMsq m) Nh M.core.Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD).1
  -- the common sizes
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 with hgd
  set θ := thJ R m b μ₀ Nh with hθd
  set v := varthJ R m b μ₀ Nh with hvd
  set Mn := ‖Mmag R m b μ₀ lam Nh‖ with hMnd
  set KC := R.ℓ ^ 2 * Real.exp M.core.KZ / 14 with hKCd
  set crr := max M.core.cρ M.fwcr with hcrrd
  set Kβ := 2 * (1 + 3 * M.Kp) with hKβd
  have hθ : 0 ≤ θ := Real.rpow_nonneg (div_pos hgN hb).le _
  have hv : 0 ≤ v := Real.rpow_nonneg (div_pos hb hgN).le _
  have hKC : 0 ≤ KC := by positivity
  have hKβ : 0 ≤ Kβ := by rw [hKβd]; linarith
  have hzi : zInvT R Nh m b μ₀ ≤ Real.exp M.core.KZ * θ :=
    inv_normZ_le (norm_pos_iff.2 hZ0) hgN hgN1 hb hKZ hZ
  obtain ⟨hΓ, hCN⟩ := gamT_zCovN_le R hP hb hKZ hval hvalL hVN hgN hgN1 hZ0 hZ
  have hbθ : b * θ * θ = v * g := by rw [mul_assoc, ← sq]; exact b_thJ_sq hgN hb
  have hcLe : Kβ * (KC + crr * Real.exp M.core.KZ) * (v * g) ≤ M.topCL / 2 * (v * g) := by
    have e : M.topCL / 2 = Kβ * (KC + crr * Real.exp M.core.KZ) := by
      rw [hKβd, hKCd, hcrrd, hRℓ]; unfold topCL; ring
    rw [e]
  -- `ϑ ≤ 2‖M‖`
  have hMag := magAt_ofD R M.magD hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hMl := hMag lam Kl hKl hl Nh le_rfl
  set F := max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 with hFd
  have hF0 : 0 ≤ F := le_max_right _ _
  have hvM : v ≤ 2 * Mn := varth_le_two_norm hv hgN.le hMl (hsmall Nh le_rfl)
  -- one top step for a point configuration `P`
  have hstep : ∀ P : Obs2.ObsPts 2 L N,
      ‖bt2 R P (zV b) m b μ₀ Nh * gamT R m b μ₀ Nh -
          Obs2.gamRem2 (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh‖ ≤ M.topCL / 2 * (v * g) ∧
      ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ Kβ * b * θ ∧ ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ ≤ Kβ * b * θ := by
    intro P
    have hk : Nh - 1 < Nh := by omega
    have hmo := hmono (Nh - 1) hk
    rw [show Nh - 1 + 1 = Nh by omega] at hmo
    obtain ⟨hβ0, hβ1⟩ := bt2_last_le R P hNh hNh1 hb hKp (hpairP P) (hrel P) (hn P _ hk)
      (hg _ hk).1 hmo (add_nonneg (hg _ hk).1 (ha _ hk).1)
      (by linarith [(hg _ hk).2, (ha _ hk).2]) (hT P).1
    have hr0 : ‖Obs2.gamRem2 (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh‖ ≤
        crr * ‖bt2 R P (zV b) m b μ₀ Nh‖ * zInvT R Nh m b μ₀ :=
      (hT P).2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (inv_nonneg.2 (norm_nonneg _)))
    have h := gamStep_pureZ hKC hcrr (Real.exp_pos _).le hθ hzi
      (by rw [← mul_assoc]; exact hβ0) hΓ hr0
    rw [hbθ] at h
    refine ⟨h.trans hcLe, ?_, ?_⟩
    · rw [hKβd]; exact hβ0
    · rw [hKβd]; exact hβ1
  have hθa : ∀ k < Nh, 0 ≤ thJ R m b μ₀ k *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := fun k hk =>
    mul_nonneg (Real.rpow_nonneg (div_pos (hD k hk.le).1 hb).le _)
      (add_nonneg (hg k hk).1 (zA_nonneg L hm.1.le k))
  set cγ := (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp) with hcγd
  have hcγ : 0 ≤ cγ := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hF'e : M.topF' = max (spinMK L M.core.cg M.core.Ke M.core.KZ (M.Kp + cγ) M.core.KG 0) 0 :=
    rfl
  -- the `a` side: `γ_{0,N_h} = M_{N_h}(λ^γ)`
  have hrem := gamRemX_top_le R hb hKp hce hcw hval hg ha (hpairP (ptsX x))
    (gamBulkRel_of_A R hB) hWX
  have hlG := hLam_lamG R hb hcγ (hpairP (ptsX x)) hθa hrem
  have h0 : ∀ k < Nh, gamT R m b μ₀ k = 0 → gamRemX R m b μ₀ x k = 0 := by
    intro k hk hΓ0
    have := hrem k hk
    rw [hΓ0, norm_zero, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hU := uA_eq_mmag R hP hb.ne' x hNh1 h0
  have hKp' : 0 ≤ M.Kp + cγ := add_nonneg hKp hcγ
  have hnear := mmag_near_of R hMag hm.1.le hb (fun k hk => (hD k hk).1) hKl hl le_rfl
    (hsmall Nh le_rfl) hKp' (fun k hk => hlG k hk)
  rw [← hF'e] at hnear
  -- the `b` side (mirror)
  have hremS : ∀ k < Nh, ‖gamRemMir R m b μ₀ x k‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) *
        (b * ‖gamT R m b μ₀ k‖) := by
    intro k hk
    have hθk : 0 ≤ thJ R m b μ₀ k := Real.rpow_nonneg (div_nonneg (hg k hk).1 hb.le) _
    have hga0 := add_nonneg (hg k hk).1 (ha k hk).1
    have hga3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k ≤ 3 := by
      linarith only [(hg k hk).2, (ha k hk).2]
    have hlh : lamHat2 R (ptsS x) (zV b) m b μ₀ k = btMir R m b μ₀ x k / b := by
      unfold lamHat2
      rw [show bt2 R (ptsS x) (zV b) m b μ₀ 0 = btMir R m b μ₀ x 0 from rfl, btMir_zero]
      rfl
    rw [gamRemMir_split R hval x hk]
    exact rem_bound_gb hb hKp hce hcw hθk hga0 hga3 (norm_nonneg _) hlh
      (hpairP (ptsS x) k hk) (hWM x k hk) (hB x k hk)
  have hlGS := hLam_lamGMir R hb hcγ (hpairP (ptsS x)) hθa hremS
  have h0S : ∀ k < Nh, gamT R m b μ₀ k = 0 → gamRemMir R m b μ₀ x k = 0 := by
    intro k hk hΓ0
    have := hremS k hk
    rw [hΓ0, norm_zero, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hUS := uMir_eq_mmag R hP hb.ne' x hNh1 h0S
  have hnearS := mmag_near_of R hMag hm.1.le hb (fun k hk => (hD k hk).1) hKl hl le_rfl
    (hsmall Nh le_rfl) hKp' (fun k hk => hlGS k hk)
  rw [← hF'e] at hnearS
  -- the steps `N_h → N_h + 1`
  obtain ⟨hsA, hβA0, hβA1⟩ := hstep (ptsX x)
  obtain ⟨hsB, -, -⟩ := hstep (ptsS x)
  have hcL0 := M.topCL_nonneg
  have hF'0 := M.topF'_nonneg
  have hvg : M.topCL / 2 * (v * g) ≤ M.topCL * Mn * g := by
    have := mul_le_mul_of_nonneg_left hvM (mul_nonneg (by linarith : 0 ≤ M.topCL / 2) hgN.le)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [uA_succ_pos R hP m b μ₀ x hNh1, hU]
    have e : Mmag R m b μ₀ (lamG R m b μ₀ x) Nh -
        (btX R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemX R m b μ₀ x Nh) - Mmag R m b μ₀ lam Nh =
        (Mmag R m b μ₀ (lamG R m b μ₀ x) Nh - Mmag R m b μ₀ lam Nh) -
          (btX R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemX R m b μ₀ x Nh) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := add_le_add hnear (hsA.trans hvg)
    calc _ ≤ 2 * (M.topF' + F) * Mn * g + M.topCL * Mn * g := this
      _ = _ := by ring
  · rw [uB_eq_uMir, uMir_succ_pos R hP m b μ₀ x hNh1, hUS]
    have e : Mmag R m b μ₀ (lamGMir R m b μ₀ x) Nh -
        (btMir R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemMir R m b μ₀ x Nh) -
          Mmag R m b μ₀ lam Nh =
        (Mmag R m b μ₀ (lamGMir R m b μ₀ x) Nh - Mmag R m b μ₀ lam Nh) -
          (btMir R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemMir R m b μ₀ x Nh) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := add_le_add hnearS (hsB.trans hvg)
    calc _ ≤ 2 * (M.topF' + F) * Mn * g + M.topCL * Mn * g := this
      _ = _ := by ring
  · -- `γ_{a,N}`: the last step
    have hW1 := M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (by omega)
    have hW : WbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
        (M.core.cWL * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖) := by
      intro B hB'
      refine (hW1 B hB').trans (ENNReal.ofReal_le_ofReal ?_)
      have hX : 0 ≤ M.core.cWL * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖ := by positivity
      have := mul_le_mul_of_nonneg_left hgN1 hX
      calc M.core.cWL * g *
            histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖
          = M.core.cWL * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖ * g := by ring
        _ ≤ _ := by linarith
    have hr1 := gamRemNP_le R hNh hval hvalL hVN hLp (ptsX x) hG hCf0 hgN1 hcWL hW (hT (ptsX x)).1
    rw [hRℓ] at hr1
    have hr1' : ‖gamRemN R Nh m b μ₀ x‖ ≤ crr * ‖btX R m b μ₀ x (Nh + 1)‖ * zInvT R Nh m b μ₀ := by
      rw [gamRemN_eq_P]
      exact hr1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (inv_nonneg.2 (norm_nonneg _)))
    have hN1 := gamStep_pureZ hKC hcrr (Real.exp_pos _).le hθ hzi
      (by rw [← mul_assoc]; exact hβA1) hCN hr1'
    rw [hbθ] at hN1
    have hGU : ‖gamNa R Nh m b μ₀ x - uA R m b μ₀ x Nh‖ ≤ M.topCL * v * g := by
      rw [gamNa_sub_uA R hP hNh1]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg]
      have hsA' : ‖btX R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemX R m b μ₀ x Nh‖ ≤
          M.topCL / 2 * (v * g) := hsA
      have := add_le_add hsA' (hN1.trans hcLe)
      calc _ ≤ M.topCL / 2 * (v * g) + M.topCL / 2 * (v * g) := this
        _ = M.topCL * v * g := by ring
    have hM' := hMag (lamG R m b μ₀ x) (M.Kp + cγ) hKp' hlG Nh le_rfl
    have hM'' : ‖Mmag R m b μ₀ (lamG R m b μ₀ x) Nh - ((v : ℝ) : ℂ)‖ ≤ M.topF' * v * g := by
      rw [hF'e]
      exact hM'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
        hgN.le)
    have hMj : ‖Mmag R m b μ₀ lam Nh - ((v : ℝ) : ℂ)‖ ≤ F * v * g :=
      hMl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
        hgN.le)
    exact gamTop_pure hv le_rfl hgN.le hgN1 hgN.le hF'0 hF0 hcL0 hU hM'' hGU hMj
      (hsmall Nh le_rfl)

end MasterFacts

end

end Spin2
