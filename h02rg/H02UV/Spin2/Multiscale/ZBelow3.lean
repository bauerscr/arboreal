import Spin2.Multiscale.ZBelow2

/-!
# `TwoPtSq` from the `γ` flow under the master constants

* `varth_le_pure`, **`varth_le_of_betaAsym`**: `ϑ_n = (b/ǧ_n)^{1/3} ≤ Θ = 1 + |2(1+β)e_R| +
  C_{gu}|K_{βa}|` from `BetaAsym` (`ǧ_n` cannot drop much below `ǧ_0 = b`), hence
  `‖M_k‖ ≤ M_b = Θ(1 + K(λ))` (`mmag_bound_of`): the bookkeeping hypothesis of `twoPtSq_of_zz1`.
* **`twoPtSq_of_gam_flow`**: with the constants of `FlowC2Concl`, `SpinConcl`, `MagConcl` (one set,
  `thm_flow_master_all`), along every admissible trajectory with `b ≤ μ₀ + m²`: (H_λ) for `λ`,
  (H_λ) for the pair vertex `μ_{0,k}/μ_{0,0}` (e.g. from `Case2Rel`, `Case2Loop` of the pair history,
  `hLam_case2`), `GamRemRel`, `GamFormB`, `PairAboveW1`, `TwoPtNear` and the smallness
  `K(λ)ǧ_j ≤ 1/2` give `TwoPtSq` (constants `zbKM`, `zbMb`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- `ϑ ≤ 1 + C` from the `BetaAsym` inequality (pure). -/
theorem varth_le_pure {β Cg K eR b g n : ℝ} (hβ : 0 < β) (hCg : 0 ≤ Cg) (hb0 : 0 < b)
    (hb1 : b ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1) (hn : 0 ≤ n)
    (h : |1 / g - 1 / b + n * β| ≤ 2 * (1 + β) * eR + Cg * (1 / β * Real.log (g / b) + K * g)) :
    (b / g) ^ (1 / 3 : ℝ) ≤ 1 + (|2 * (1 + β) * eR| + Cg * |K|) := by
  set C := |2 * (1 + β) * eR| + Cg * |K| with hCd
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (mul_nonneg hCg (abs_nonneg _))
  have hbg : b / g ≤ 1 + C := by
    by_cases hgb : b ≤ g
    · exact ((div_le_one hg0).2 hgb).trans (by linarith)
    · push Not at hgb
      have hlog : Real.log (g / b) ≤ 0 :=
        Real.log_nonpos (div_pos hg0 hb0).le ((div_le_one hb0).2 hgb.le)
      have h1 : Cg * (1 / β * Real.log (g / b)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hCg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog)
      have h2 : Cg * (K * g) ≤ Cg * |K| := by
        refine mul_le_mul_of_nonneg_left ?_ hCg
        calc K * g ≤ |K| * g := mul_le_mul_of_nonneg_right (le_abs_self K) hg0.le
          _ ≤ |K| * 1 := mul_le_mul_of_nonneg_left hg1 (abs_nonneg K)
          _ = |K| := mul_one _
      have h3 := le_abs_self (2 * (1 + β) * eR)
      have h4 := (le_abs_self (1 / g - 1 / b + n * β)).trans h
      have hnb : 0 ≤ n * β := mul_nonneg hn hβ.le
      have h5 : 1 / g ≤ 1 / b + C := by nlinarith
      have e : b / g = b * (1 / g) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h5 hb0.le
      rw [mul_add, mul_one_div_cancel hb0.ne'] at this
      nlinarith
  have h1C : 1 ≤ 1 + C := by linarith
  calc (b / g) ^ (1 / 3 : ℝ) ≤ (1 + C) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (div_pos hb0 hg0).le hbg (by norm_num)
    _ ≤ (1 + C) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1C (by norm_num)
    _ = 1 + C := Real.rpow_one _

/-- `Θ = 1 + |2(1+β)e_R| + C_{gu}|K_{βa}|`. -/
def zbTheta (L : ℕ) (cg Ke : ℝ) : ℝ :=
  1 + (|2 * (1 + betaL L) * eRange (betaL L) Ke 1| +
    Cgu (betaL L) cg * |betaAsymK (betaL L) cg (eRange (betaL L) Ke 1)|)

/-- `K_M = 2(K(K_p + c_γ) + K(K_b) + K(K_λ))`, `K(·) = max(spinMK ·, 0)`. -/
def zbKM (L : ℕ) (cg Ke KZ KG Kp cγ Kb Kl : ℝ) : ℝ :=
  2 * (max (spinMK L cg Ke KZ (Kp + cγ) KG 0) 0 + max (spinMK L cg Ke KZ Kb KG 0) 0 +
    max (spinMK L cg Ke KZ Kl KG 0) 0)

/-- `M_b = Θ(1 + K(K_λ))`. -/
def zbMb (L : ℕ) (cg Ke KZ KG Kl : ℝ) : ℝ :=
  zbTheta L cg Ke * (1 + max (spinMK L cg Ke KZ Kl KG 0) 0)

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from the `γ` flow** (master constants). -/
theorem twoPtSq_of_gam_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMC : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl Kp cγ Kb KE KR KN KRN : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ cγ → 0 ≤ Kb →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      GamRemRel R Nh m b μ₀ cγ → GamFormB R Nh m b μ₀ Kb →
      PairAboveW1 R Nh m b μ₀ lam KE KR → TwoPtNear (L := L) (N := N) m b μ₀ KN KRN →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      TwoPtSq R Nh m b μ₀ lam
        (max (zbKM L cg Ke KZ KG Kp cγ Kb Kl * (2 + zbKM L cg Ke KZ KG Kp cγ Kb Kl) + KE) KN)
        (max (1 + 2 * (1 + zbKM L cg Ke KZ KG Kp cγ Kb Kl) * zbMb L cg Ke KZ KG Kl + KR) KRN) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam Kl Kp cγ Kb KE KR KN KRN
    hKl hKp hcγ hKb hl hpair hrem hB hE hNear hsmall
  have hcg : 0 < cg := hF.2.2.2.2.2.2.1
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hb1 : b ≤ 1 := by
    have := (hadm.1 0 (Nat.zero_le _)).2.1; rw [Hist.traj_zero] at this; exact this.trans hε1
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := fun k hk =>
    (hadm.1 k hk).1
  have hg1 : ∀ k ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ((hadm.1 k hk).2.1).trans hε1
  have hMag := magAt_of R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hadm
  have hA := gamFormA_of R hP hb hm.1.le hcγ hg hpair hrem
  have hZ := zBelowU1_of_forms R hMag hm.1.le hb hg hKl hl hsmall (add_nonneg hKp hcγ) hKb hA hB
  have hβ : 0 < betaL L := by
    have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
    have := Real.log_pos hL1
    unfold betaL; positivity
  have hCg : 0 ≤ Cgu (betaL L) cg := by unfold Cgu; positivity
  obtain ⟨-, -, -, -, hBA, -⟩ := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hΘ : ∀ k ≤ Nh, varthJ R m b μ₀ k ≤ zbTheta L cg Ke := fun k hk =>
    varth_le_pure hβ hCg hb hb1 (hg k hk) (hg1 k hk) (Nat.cast_nonneg k)
      (hBA m hm b μ₀ hadm k hk)
  have hMb := mmag_bound_of R hMag (fun k hk => ⟨(hg k hk).le, hg1 k hk⟩) hKl hl hΘ hb.le
  have hKM : 0 ≤ zbKM L cg Ke KZ KG Kp cγ Kb Kl := by
    unfold zbKM
    have := le_max_right (spinMK L cg Ke KZ (Kp + cγ) KG 0) 0
    have := le_max_right (spinMK L cg Ke KZ Kb KG 0) 0
    have := le_max_right (spinMK L cg Ke KZ Kl KG 0) 0
    linarith
  exact twoPtSq_of_zz1_flow hF hε1 hL N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam
    _ _ KE KR KN KRN hKM hMb hZ hE hNear

/-- (H_λ) for the pair vertex `μ_{0,k}/μ_{0,0}` from `Case2Rel`, `Case2Loop` of the pair histories
(uniform constants), via `hLam_case2`. -/
theorem pairHLam_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke : ℝ}
    (hLC : LamConcl L ℓ A ρ κ cg cm cT ε Ke) {N : ℕ} {R : RGPar 2 L N} [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = ℓ) (hRA : R.A = A)
    (hRρ : R.ρ = ρ) {Nh : ℕ} (hNh : Nh + 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) (hb : 0 < b)
    {B B' cq cδ : ℝ} (hB : 0 ≤ B) (hcδ : 0 ≤ cδ)
    (hrel : ∀ x : Lam 2 L N, x ≠ 0 → Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hloop : ∀ x : Lam 2 L N, x ≠ 0 → Case2Loop R (ptsX x) (zV b) Nh m b μ₀ B B' cq) :
    ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀)
      (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4) := fun x hx =>
  hLam_case2 hLC hP hi0 hRℓ hRA hRρ hNh hm hadm hB hcδ
    (by simp [zV]; exact hb.ne') (hrel x hx) (hloop x hx)

end

end Spin2
