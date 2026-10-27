import Ward.ObsLimitPair

/-!
# Continuity of `Q1 = q^{(1)}_∞/λ̄²`

`Qone x` is jointly continuous in `(m², b₀) ∈ [0, ∞) × B(0, λ̄)` (`Qone_joint`): it is the
uniform limit of the jointly continuous `q_N/λ̄²` (`PtCorr.FlowData.qN_joint`) with the rate of
`qN_rate`, whose constant is bounded uniformly for `|b₀| ≤ λ̄` (`Kq_mono`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs : ℝ} (hCs : 0 ≤ Cs)
  (hS1 : StepBd1 d L A ℓ₀ V₀c lbar C κ Cs)
include H hd hCs hS1

theorem Kq_mono {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    Kq lbar C κ Cs ℓ₀ b₀ L ≤ Kq lbar C κ Cs ℓ₀ (lbar : ℂ) L := by
  have hb : ‖b₀‖ ≤ ‖(lbar : ℂ)‖ := by rw [norm_lbar H]; exact hb₀
  have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
  have h1 : 0 < 1 - th L κ := by linarith
  have hlb := H.fd.lbar_pos
  have hC0 := H.fd.C_nonneg
  have hE : C * lbar * ‖b₀‖ ≤ C * lbar * ‖(lbar : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hE0 : 0 ≤ C * lbar * ‖b₀‖ := by positivity
  have hR : Rm lbar C κ Cs b₀ L ≤ Rm lbar C κ Cs (lbar : ℂ) L :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hCs) h1.le
  have hR0 : 0 ≤ Rm lbar C κ Cs b₀ L := by unfold Rm; positivity
  have hL : Lm lbar C κ Cs b₀ L ≤ Lm lbar C κ Cs (lbar : ℂ) L := by
    unfold Lm; linarith [div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hCs) h1.le]
  have hL0 : 0 ≤ Lm lbar C κ Cs b₀ L := by unfold Lm; positivity
  unfold Kq
  have hq : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ hq
  have : Lm lbar C κ Cs b₀ L ^ 2 ≤ Lm lbar C κ Cs (lbar : ℂ) L ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have : 2 * Cs * (C * lbar * ‖b₀‖) ≤ 2 * Cs * (C * lbar * ‖(lbar : ℂ)‖) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  linarith

/-- **Joint continuity of `Q1(x)`** on `[0, ∞) × B(0, λ̄)` (`x ≠ 0`). -/
theorem Qone_joint (hd3 : 3 ≤ d) {x : Zd d} (hx0 : x ≠ 0) :
    ContinuousOn (fun p : ℝ × ℂ => Qone d L V₀c lbar p.1 p.2 x) (Set.Ici 0 ×ˢ ball 0 lbar) := by
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hρ1 := rho_lt_one hd3 hL2 (L := L)
  have hρp : 0 < rho d L :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hlb := H.fd.lbar_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Kq lbar C κ Cs ℓ₀ (lbar : ℂ) L * (1 + 1 / (1 - rho d L)) /
      (rho d L * lbar ^ 2) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    have := Kq_nonneg H hd hCs hS1 (lbar : ℂ)
    have : 0 < 1 - rho d L := by linarith
    rw [hB]; positivity
  have hU : TendstoUniformlyOn (fun (N : ℕ) (p : ℝ × ℂ) =>
      qN d L .one N p.1 (V₀c p.1 p.2) (initObs .one (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) /
        (lbar : ℂ) ^ 2) (fun p => Qone d L V₀c lbar p.1 p.2 x) atTop
      (Set.Ici 0 ×ˢ ball 0 lbar) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)).const_mul B
    rw [mul_zero] at ht
    filter_upwards [(tendsto_order.1 ht).2 ε hε, eventually_ge_atTop (2 + supNormZ x)]
      with N hN hN2 p hp
    have hb₀ : ‖p.2‖ ≤ lbar := (mem_ball_zero_iff.1 hp.2).le
    have hs : supNormZ x ≤ L ^ (N - 1) := by
      have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
      have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hr := qN_rate H hd hCs hS1 hd3 (Set.mem_Ici.1 hp.1) hb₀ hx0 (by omega) hs
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt (hr.trans ?_) hN
    have hK := Kq_mono H hd hCs hS1 hb₀
    have hc : 0 ≤ (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
      have : 0 < 1 - rho d L := by linarith
      have := Real.rpow_nonneg (Nat.cast_nonneg L) (-(((d : ℝ) - 2) * N))
      positivity
    rw [hB]
    calc Kq lbar C κ Cs ℓ₀ p.2 L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
          (L : ℝ) ^ (-(((d : ℝ) - 2) * N))
        = Kq lbar C κ Cs ℓ₀ p.2 L * ((1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
          (L : ℝ) ^ (-(((d : ℝ) - 2) * N))) := by ring
      _ ≤ Kq lbar C κ Cs ℓ₀ (lbar : ℂ) L * ((1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
          (L : ℝ) ^ (-(((d : ℝ) - 2) * N))) := mul_le_mul_of_nonneg_right hK hc
      _ = _ := by ring
  refine hU.continuousOn (Frequently.of_forall fun N => ?_)
  exact (H.fd.qN_joint hd (initObs .one (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x)).div_const _

end

end Ward
