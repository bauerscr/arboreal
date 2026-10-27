import Spin2.Gam.GamTopB
import Spin2.Case2.Case2RelPairThm

/-!
# `BetaLast`, `BetaLastS` and `GamRemTopS` from the Case-(2) relative recursion

**The vertex at the two top scales.** `β_{N_h} = β_{N_h-1}(1 - 𝔫_{N_h-1}) - err_{N_h-1}` and
`β_{N_h+1} = β_{N_h}(1 - 𝔫_{N_h}) - err_{N_h}` (`bt2_flow`, the second one with horizon `N_h + 1`,
which is still `< N`; the `μ^{(2)}` chain identity is algebraic). The first step is covered by
`Case2Rel` and `Case2Loop` at `k = N_h - 1 < N_h` (`cδǧ² ≤ 1/8`, `‖𝔫‖ ≤ 1/8`); the second by
**`Case2TopStep`**: the same two bounds at `k = N_h` (`Case2Rel` extended by one step,
`case2TopStep_of_rel`). With (H_λ) at `k = N_h - 1` (`‖β_{N_h-1}‖ ≤ (1 + 3K_p)bθ_{N_h-1}`) and
`θ_{N_h-1} ≤ θ_{N_h}` (`GMonoConcl`):

  `‖β_{N_h}‖, ‖β_{N_h+1}‖ ≤ 2(1 + 3K_p)bθ_{N_h}` (**`bt2_last_le`**; `(81/64)² ≤ 2`).

Hence **`betaLast_of`**, **`betaLastS_of`** (both points).

**`GamRemTopS`** (**`gamRemTopS_of`**): `gamRemMir_split` (`ρ^{mir}_k = gamWKMir_k + β^{mir}_kE_k(x)`),
`GamBulkRelA` at `a = x`, the mirrored all-`k` bound of `wk_inputs`, and (H_λ) for the mirrored
vertex, as in `gamRemRelS_ofA` but for all `k < N_h`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- One step of the `β` flow with relative errors `≤ 1/8`. -/
theorem beta_step_le {β n e : ℂ} (hn : ‖n‖ ≤ 1 / 8) (he : ‖e‖ ≤ 1 / 8 * ‖β * (1 - n)‖) :
    ‖β * (1 - n) - e‖ ≤ 81 / 64 * ‖β‖ := by
  have h1 : ‖1 - n‖ ≤ 9 / 8 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have h2 : ‖β * (1 - n)‖ ≤ 9 / 8 * ‖β‖ := by
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left h1 (norm_nonneg β)
    linarith
  calc ‖β * (1 - n) - e‖ ≤ ‖β * (1 - n)‖ + ‖e‖ := norm_sub_le _ _
    _ ≤ 9 / 8 * ‖β * (1 - n)‖ := by linarith
    _ ≤ 81 / 64 * ‖β‖ := by linarith

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Named input (the `μ^{(2)}` step at `k = N_h`)**: `‖𝔫_{N_h}‖ ≤ 1/8` and
`‖err_{N_h}‖ ≤ (1/8)‖β_{N_h}(1 - 𝔫_{N_h})‖` — `Case2Rel`/`Case2Loop` at the step `N_h` (the step with
`ValidAtL`, not covered by the bulk recursion). -/
def Case2TopStep (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (Nh : ℕ) (m b μ₀ : ℝ) : Prop :=
  ‖nn2 R P V m b μ₀ Nh‖ ≤ 1 / 8 ∧
    ‖err2 R P V m b μ₀ Nh‖ ≤ 1 / 8 * ‖bt2 R P V m b μ₀ Nh * (1 - nn2 R P V m b μ₀ Nh)‖

/-- `Case2TopStep` is `Case2Rel` with horizon `N_h + 1`, at its last step, plus `‖𝔫_{N_h}‖ ≤ 1/8`. -/
theorem case2TopStep_of_rel {P : Obs2.ObsPts 2 L N} {V : Obs2.OCoup .two} {Nh : ℕ} {m b μ₀ cδ : ℝ}
    (hrel : Case2Rel R P V (Nh + 1) m b μ₀ cδ) (hn : ‖nn2 R P V m b μ₀ Nh‖ ≤ 1 / 8) :
    Case2TopStep R P V Nh m b μ₀ := by
  obtain ⟨h1, h2⟩ := hrel Nh (Nat.lt_succ_self _)
  exact ⟨hn, h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))⟩

theorem bt2_zV_zero (P : Obs2.ObsPts 2 L N) (m b μ₀ : ℝ) : bt2 R P (zV b) m b μ₀ 0 = b := by
  rw [bt2_zero]; simp [zV]

/-- **The vertex at the two top scales**: `‖β_{N_h}‖, ‖β_{N_h+1}‖ ≤ 2(1 + 3K_p)bθ_{N_h}`. -/
theorem bt2_last_le (P : Obs2.ObsPts 2 L N) {Nh : ℕ} (hNh : Nh + 2 = N) (h1 : 1 ≤ Nh)
    {m b μ₀ Kp cδ : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hl : HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp)
    (hrel : Case2Rel R P (zV b) Nh m b μ₀ cδ)
    (hn : ‖nn2 R P (zV b) m b μ₀ (Nh - 1)‖ ≤ 1 / 8)
    (hg : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1)
    (hmono : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hga0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 + zA L m (Nh - 1))
    (hga3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 + zA L m (Nh - 1) ≤ 3)
    (htop : Case2TopStep R P (zV b) Nh m b μ₀) :
    ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ 2 * (1 + 3 * Kp) * b * thJ R m b μ₀ Nh ∧
      ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ ≤ 2 * (1 + 3 * Kp) * b * thJ R m b μ₀ Nh := by
  obtain ⟨k, rfl⟩ : ∃ k, Nh = k + 1 := ⟨Nh - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hn hg hmono hga0 hga3
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  -- the vertex at `k = N_h - 1`
  have hθk : 0 ≤ thJ R m b μ₀ k := Real.rpow_nonneg (div_nonneg hg hb.le) _
  have hθ : thJ R m b μ₀ k ≤ thJ R m b μ₀ (k + 1) :=
    Real.rpow_le_rpow (div_nonneg hg hb.le) (div_le_div_of_nonneg_right hmono hb.le) (by norm_num)
  have hlk := hl k (Nat.lt_succ_self _)
  have hlh : lamHat2 R P (zV b) m b μ₀ k = bt2 R P (zV b) m b μ₀ k / b := by
    unfold lamHat2; rw [bt2_zV_zero]
  rw [hlh] at hlk
  have hβk : ‖bt2 R P (zV b) m b μ₀ k‖ ≤ (1 + 3 * Kp) * b * thJ R m b μ₀ k := by
    have hβb : ‖bt2 R P (zV b) m b μ₀ k‖ = b * ‖bt2 R P (zV b) m b μ₀ k / b‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]; field_simp
    have h2 := norm_le_insert' (bt2 R P (zV b) m b μ₀ k / b) ((thJ R m b μ₀ k : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθk] at h2
    have hlk' : ‖bt2 R P (zV b) m b μ₀ k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
        Kp * thJ R m b μ₀ k * ((t k).1 + zA L m k) := hlk
    have h3 : Kp * thJ R m b μ₀ k * ((t k).1 + zA L m k) ≤ Kp * thJ R m b μ₀ k * 3 :=
      mul_le_mul_of_nonneg_left hga3 (mul_nonneg hKp hθk)
    have h4 : ‖bt2 R P (zV b) m b μ₀ k / b‖ ≤ (1 + 3 * Kp) * thJ R m b μ₀ k := by linarith
    rw [hβb]
    have := mul_le_mul_of_nonneg_left h4 hb.le
    linarith
  -- the step `N_h - 1 → N_h`
  have hf1 := bt2_flow R P (zV b) (Nh := k + 1) (by omega) m b μ₀ (k := k) (Nat.lt_succ_self _)
  obtain ⟨hr1, hr2⟩ := hrel k (Nat.lt_succ_self _)
  have hs1 : ‖bt2 R P (zV b) m b μ₀ (k + 1)‖ ≤ 81 / 64 * ‖bt2 R P (zV b) m b μ₀ k‖ := by
    rw [hf1]
    exact beta_step_le hn (hr1.trans (mul_le_mul_of_nonneg_right hr2 (norm_nonneg _)))
  -- the step `N_h → N_h + 1`
  have hf2 := bt2_flow R P (zV b) (Nh := k + 2) (by omega) m b μ₀ (k := k + 1) (by omega)
  have hs2 : ‖bt2 R P (zV b) m b μ₀ (k + 1 + 1)‖ ≤ 81 / 64 * ‖bt2 R P (zV b) m b μ₀ (k + 1)‖ := by
    rw [hf2]
    exact beta_step_le htop.1 htop.2
  have hX : 0 ≤ (1 + 3 * Kp) * b := mul_nonneg (by linarith) hb.le
  have hB : (1 + 3 * Kp) * b * thJ R m b μ₀ k ≤ (1 + 3 * Kp) * b * thJ R m b μ₀ (k + 1) :=
    mul_le_mul_of_nonneg_left hθ hX
  have hθ1 : 0 ≤ (1 + 3 * Kp) * b * thJ R m b μ₀ (k + 1) := mul_nonneg hX (hθk.trans hθ)
  have e : 2 * (1 + 3 * Kp) * b * thJ R m b μ₀ (k + 1) =
      2 * ((1 + 3 * Kp) * b * thJ R m b μ₀ (k + 1)) := by ring
  rw [e]
  constructor
  · linarith
  · linarith

/-- **`BetaLast` from the Case-(2) recursion**, `K_β = 2(1 + 3K_p)`. -/
theorem betaLast_of {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Kp cδ : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hrel : ∀ x : Lam 2 L N, x ≠ 0 → Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hmono : ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1)
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀) :
    BetaLast R Nh m b μ₀ (2 * (1 + 3 * Kp)) := by
  intro x hx h1 hj
  have hN1 : 1 ≤ Nh := h1.trans hj
  have hk : Nh - 1 < Nh := by omega
  have hmo := hmono (Nh - 1) hk
  rw [show Nh - 1 + 1 = Nh by omega] at hmo
  exact bt2_last_le R (ptsX x) hNh hN1 hb hKp (hl x hx) (hrel x hx) (hn x hx _ hk) (hg _ hk).1 hmo
    (add_nonneg (hg _ hk).1 (ha _ hk).1) (by linarith [(hg _ hk).2, (ha _ hk).2])
    (htop x hx h1 hj)

/-- **`BetaLastS` from the Case-(2) recursion** (mirror), `K_β = 2(1 + 3K_p)`. -/
theorem betaLastS_of {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Kp cδ : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp)
    (hrel : ∀ x : Lam 2 L N, x ≠ 0 → Case2Rel R (ptsS x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsS x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hmono : ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1)
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsS x) (zV b) Nh m b μ₀) :
    BetaLastS R Nh m b μ₀ (2 * (1 + 3 * Kp)) := by
  intro x hx h1 hj
  have hN1 : 1 ≤ Nh := h1.trans hj
  have hk : Nh - 1 < Nh := by omega
  have hmo := hmono (Nh - 1) hk
  rw [show Nh - 1 + 1 = Nh by omega] at hmo
  exact bt2_last_le R (ptsS x) hNh hN1 hb hKp (hl x hx) (hrel x hx) (hn x hx _ hk) (hg _ hk).1 hmo
    (add_nonneg (hg _ hk).1 (ha _ hk).1) (by linarith [(hg _ hk).2, (ha _ hk).2])
    (htop x hx h1 hj)

/-- **`GamRemTopS` from `GamBulkRelA`**, the mirrored all-`k` `K`/`𝒲` bound (`wk_inputs`) and (H_λ)
for the mirrored vertex, with `c_γ = (c_e + c_w)(1 + 3K_p)`. -/
theorem gamRemTopS_of {Nh : ℕ} {m b μ₀ Kp ce cw : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hce : 0 ≤ ce) (hcw : 0 ≤ cw) (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp)
    (hB : GamBulkRelA R Nh m b μ₀ ce)
    (hW : ∀ x : Lam 2 L N, ∀ k < Nh, ‖gamWKMir R m b μ₀ x k‖ ≤
      cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖btMir R m b μ₀ x k‖ *
        ‖gamT R m b μ₀ k‖) :
    GamRemTopS R Nh m b μ₀ ((ce + cw) * (1 + 3 * Kp)) := by
  intro x hx _ _ k hk
  have hθ : 0 ≤ thJ R m b μ₀ k := Real.rpow_nonneg (div_nonneg (hg k hk).1 hb.le) _
  have hga0 := add_nonneg (hg k hk).1 (ha k hk).1
  have hga3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k ≤ 3 := by
    linarith only [(hg k hk).2, (ha k hk).2]
  have hlh : lamHat2 R (ptsS x) (zV b) m b μ₀ k = btMir R m b μ₀ x k / b := by
    unfold lamHat2
    rw [show bt2 R (ptsS x) (zV b) m b μ₀ 0 = btMir R m b μ₀ x 0 from rfl, btMir_zero]
    rfl
  rw [gamRemMir_split R hV x hk]
  exact rem_bound_gb hb hKp hce hcw hθ hga0 hga3 (norm_nonneg _) hlh (hl x hx k hk)
    (hW x k hk) (hB x k hk)

end Traj

end

end Spin2
