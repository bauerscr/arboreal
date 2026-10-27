import Spin2.Pair.PairLoop6D
import Spin2.H0.MasterH0Multi

/-!
# Final wiring (route (a1)), part 1: `GamLastRem(S)` discharged in the pair layer

`pairAbove_final4_MF'`/`MFD'` take the last-two-step remainder bounds `GamLastRem(S) c_r`
(`‖ρ‖ ≤ c_r‖β‖‖Γ‖`, relative to the covariances) as named inputs; they are only used to build
`GamTopBd` (`gamTopBd_both_flowD`). `GamLastRem` is **not** implied by the `1/|Z_{N_h+1}|` form
`GamRemNZ` (no lower bound on `‖Γ_{N_h}‖`, `‖C_N(0,0)‖`), so instead `GamTopBd` is obtained
directly by the route of `thm_gamTopBd_case2''_MF` (`TopConcl` for `ρ_{N_h}`, `gamRemNP_le` +
`LastObsConclWD` for `ρ_N`, `gamLastRel_ofZ`), in the windowed form:

* **`MasterFacts.fw_gamTopBdD`**: `GamTopBd … lam fwKG` along every trajectory in `D_ε` for any
  vertex with (H_λ) and the smallness; `fwKG = 2(1 + K(K_p + (c_e+c_w)(1+3K_p)) +
  2·2(1+3K_p)(ℓ²e^{K_Z}/14 + max(c_ρ, c_r)e^{K_Z}))`, `c_r = fwcr = 2c_BQ₁c_{WL}(9/8)ℓ² + C_fℓ⁴`.
* **`fw_pairAbove_atD`** (copy of the body of `pairAbove_final4_atD`), **`fw_pairAbove_MFD'`**:
  `pairAbove_final4_MFD'` without `GamLastRem`, `GamLastRemS` (conclusion `FwPairConclD`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The last-step remainder constant `c_r = 2c_BQ₁c_{WL}(9/8)ℓ² + C_fℓ⁴` (of `gamRemNP_le`). -/
def fwcr : ℝ :=
  2 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL * (9 / 8 * M.core.ℓ ^ 2)) + M.core.Cf * M.core.ℓ ^ 4

/-- The `GamTopBd` constant at the master constants. -/
def fwKG : ℝ :=
  2 * (1 + max (spinMK L M.core.cg M.core.Ke M.core.KZ
      (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
    2 * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 +
      max M.core.cρ M.fwcr * Real.exp M.core.KZ))

set_option maxHeartbeats 4000000 in
/-- **`GamTopBd` along windowed trajectories without remainder inputs** (the route of
`thm_gamTopBd_case2''_MF` in `D_ε` form). -/
theorem fw_gamTopBdD {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (lam : ℕ → ℂ) {Kl : ℝ} (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) :
    GamTopBd R Nh m b μ₀ lam M.fwKG := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hε1 := M.eps_le
  have hF := M.flow
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hce := M.cGB_nonneg
  have hcw := M.cw_nonneg
  have hKZ := M.KZ_nonneg
  have hcρ := M.cρ_nonneg
  have hcWL := M.cWL_nonneg
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
  obtain ⟨-, -, hWT, -⟩ := wk_inputsD M.wkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hβ := betaLast_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x _ _ _ => (hT (ptsX x)).1)
  have hcr : 0 ≤ M.fwcr := by
    unfold fwcr
    have : (0 : ℝ) ≤ PtCorr2.cBn := Nat.cast_nonneg _
    have : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
    positivity
  have hcrr : 0 ≤ max M.core.cρ M.fwcr := le_trans hcρ (le_max_left _ _)
  have hVN := M.lastValid N R hP hRℓ hRρ hN2 Nh hNh m hm
  obtain ⟨hZ0, hZ⟩ :=
    (M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ₀ hD Nh le_rfl
  have hzi0 : 0 ≤ zInvT R Nh m b μ₀ := inv_nonneg.2 (norm_nonneg _)
  have hr0X : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ‖gamRemX R m b μ₀ x Nh‖ ≤ max M.core.cρ M.fwcr * ‖btX R m b μ₀ x Nh‖ * zInvT R Nh m b μ₀ :=
    fun x _ _ _ => (hT (ptsX x)).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) hzi0)
  have hgN : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := (hD Nh le_rfl).1
  have hgN1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 := ((hD Nh le_rfl).2.1).trans hε1
  have hG : GlueOut (R.withMsq m) Nh M.core.Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD).1
  have hlastP : ∀ P : Obs2.ObsPts 2 L N, 0 < Nh →
      ‖gamRemNP R P Nh m b μ₀‖ ≤ M.fwcr * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ * zInvT R Nh m b μ₀ := by
    intro P hNh0
    have hW1 := M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P hNh0
    have hW : WbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
        (M.core.cWL * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R P (zV b) m b μ₀ Nh‖) := by
      intro B hB
      refine (hW1 B hB).trans (ENNReal.ofReal_le_ofReal ?_)
      have hX : 0 ≤ M.core.cWL * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R P (zV b) m b μ₀ Nh‖ := by positivity
      have := mul_le_mul_of_nonneg_left hgN1 hX
      calc M.core.cWL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
            histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R P (zV b) m b μ₀ Nh‖
          = M.core.cWL * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R P (zV b) m b μ₀ Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by ring
        _ ≤ _ := by linarith
    have h := gamRemNP_le R hNh hval hvalL hVN hLp P hG hCf0 hgN1 hcWL hW (hT P).1
    rw [hRℓ] at h
    exact h
  have hr1X : GamRemNZ R Nh m b μ₀ (max M.core.cρ M.fwcr) := fun x hx h1 hj => by
    rw [gamRemN_eq_P]
    exact (hlastP (ptsX x) (by omega)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) hzi0)
  have hLast := gamLastRel_ofZ R hP hb hKZ hcrr hval hvalL hVN hgN hgN1 hZ0 hZ hβ hr0X hr1X
  rw [hRℓ] at hLast
  have hcL : 0 ≤ 2 * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 +
      max M.core.cρ M.fwcr * Real.exp M.core.KZ) := by positivity
  unfold fwKG
  exact gamTopBd_flowD hF hε1 hL8 M.magD M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
    lam Kl M.Kp M.core.cGB M.core.cw _ hKl hKp hce hcw hcL hl (fun x _ => hpairP _)
    (gamBulkRel_of_A R hB) hWT hLast hsmall

end MasterFacts


end

end Spin2
