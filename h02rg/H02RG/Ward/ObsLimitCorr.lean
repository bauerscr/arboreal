import Ward.ObsLimit
import PtCorr.TwoPtTwo
import Psi4.Defs

/-!
# Infinite-volume limits: identification of `γ^{(2)}_{a,∞}` with the limit of `⟨ψ̄₀ψ₀⟩` at `m² > 0`

For `m² > 0` and `|b₀| ≤ λ̄`: `⟨ψ̄₀ψ₀⟩_{Λ_N} → GamA(m², b₀)` as `N → ∞` (`avg_pbp_tendsto`).

Proof: `PtCorr.prop_1pt_of` gives, at finite `N`,
`⟨ψ̄₀ψ₀⟩ = γ_{a,N} + (λ_{a,N} τ + E)/(1 + ũ)` with `|E| ≤ C|b₀|(L^{-(d-2+κ)N} + L^{-κN}/(m²|Λ|))`;
`γ_{a,N} → GamA` with rate `L^{-(d-2)N}` (`gamA2_rate`), `τ ≤ 1/(m²|Λ|) → 0`, `λ_{a,N}` is
bounded, and `|ũ| ≤ C|b₀|L^{-κN} → 0` once `m² L^{2N} ≥ 1` (`Psi4.utN_le_of_mass`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem tendsto_rpow_neg_mul (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => (L : ℝ) ^ (-(s * N))) atTop (𝓝 0) := by
  have h0 : 0 ≤ (L : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (L : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < L)) (by linarith)
  refine (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).congr fun N => ?_
  exact (rpow_neg_mul_nat (Nat.cast_nonneg _) s N).symm

theorem tendsto_inv_card (hd : 1 ≤ d) (hL : 2 ≤ L) {msq : ℝ} (hmsq : 0 < msq) :
    Tendsto (fun N : ℕ => 1 / (msq * Fintype.card (Lam d L N))) atTop (𝓝 0) := by
  have hc : ∀ N : ℕ, (N : ℝ) ≤ Fintype.card (Lam d L N) := fun N => by
    rw [Suscept.card_lam]
    have h1 : N < L ^ N := Nat.lt_pow_self (by omega)
    have h2 : (1 : ℝ) ≤ ((L ^ N : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _).ne'
    calc (N : ℝ) ≤ ((L ^ N : ℕ) : ℝ) := by exact_mod_cast h1.le
      _ = ((L ^ N : ℕ) : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ ((L ^ N : ℕ) : ℝ) ^ d := pow_le_pow_right₀ h2 hd
  have ht : Tendsto (fun N : ℕ => msq * (Fintype.card (Lam d L N) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hmsq (tendsto_atTop_mono hc tendsto_natCast_atTop_atTop)
  refine ht.inv_tendsto_atTop.congr fun N => ?_
  simp [one_div]

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) {Cs : ℝ} (hCs : 0 ≤ Cs)
  (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs)
include H hCs hS

/-- **`⟨ψ̄₀ψ₀⟩_{Λ_N} → γ^{(2)}_{a,∞}`** at `m² > 0`. -/
theorem avg_pbp_tendsto (hd : 3 ≤ d) {msq : ℝ} (hmsq : 0 < msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    Tendsto (fun N => avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
      (psibar (0 : Lam d L N) * psi (0 : Lam d L N))) atTop (𝓝 (GamA d L V₀c lbar msq b₀)) := by
  have hd1 : 1 ≤ d := by omega
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  obtain ⟨C1, hC1, h1pt⟩ := PtCorr.prop_1pt_of hd H.fd
  have hlb := H.fd.lbar_pos
  have hκ := H.fd.κ_pos
  -- the bound
  obtain ⟨bd, hbd_def⟩ : ∃ bd : ℕ → ℝ, bd = fun N : ℕ =>
    K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) *
      (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) +
    2 * ((1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
      C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
        (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N))))) := ⟨_, rfl⟩
  have hbd : Tendsto bd atTop (𝓝 0) := by
    have t1 := tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith)
    have t2 := tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2 + κ)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith)
    have t3 := tendsto_rpow_neg_mul (L := L) hL2 hκ
    have t4 := tendsto_inv_card (d := d) hd1 hL2 hmsq
    have := ((t1.const_mul (K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) /
      (rho d L * lbar))).add (((t4.const_mul (1 + C1 * ‖b₀‖)).add
      ((t2.add (t3.mul t4)).const_mul (C1 * ‖b₀‖))).const_mul 2))
    rw [hbd_def]; simpa using this
  -- eventually the mass condition and `|ũ| ≤ 1/2`
  have hev1 : ∀ᶠ N : ℕ in atTop, 1 ≤ msq * (L : ℝ) ^ (2 * N) := by
    have : Tendsto (fun N : ℕ => msq * (L : ℝ) ^ (2 * N)) atTop atTop := by
      refine Tendsto.const_mul_atTop hmsq ?_
      have h1 : Tendsto (fun N : ℕ => ((L : ℝ) ^ 2) ^ N) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by
          have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
          nlinarith)
      exact h1.congr fun N => by rw [← pow_mul]
    exact this.eventually_ge_atTop 1
  have hev2 : ∀ᶠ N : ℕ in atTop, (C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar))) * ‖b₀‖ *
      (L : ℝ) ^ (-(κ * N)) ≤ 1 / 2 := by
    have := (tendsto_rpow_neg_mul (L := L) hL2 hκ).const_mul
      ((C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar))) * ‖b₀‖)
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 (1 / 2) (by norm_num) |>.mono fun N h => h.le
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hev1, hev2, eventually_ge_atTop 2] with N hm hu2 hN
  have hu : ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ 1 / 2 :=
    (Psi4.utN_le_of_mass hd1 H.fd hmsq hm hb₀).trans hu2
  have hu0 : 1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 := by
    intro h
    have : Suscept.utN d L N msq (V₀c msq b₀) = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hu; norm_num at hu
  have hu1 : 1 / 2 ≤ ‖1 + Suscept.utN d L N msq (V₀c msq b₀)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-Suscept.utN d L N msq (V₀c msq b₀))
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  have hx : ctr d L N ≠ 0 := (ctr_ne_zero hd1 hL3 hN).symm
  obtain ⟨⟨hlam, -, E, hE, havg⟩, -⟩ := h1pt N msq b₀ (ctr d L N) (by omega) hmsq hb₀ hx hu0
  have hg := gamA2_rate H hd1 hCs hS hd hmsq.le hb₀ hN hx
  have hτ := norm_tau_le (d := d) (L := L) (N := N) hd1 hmsq
  have hlam' : ‖lamA2 d L N msq (V₀c msq b₀) lbar (ctr d L N)‖ ≤ 1 + C1 * ‖b₀‖ := by
    calc _ = ‖(lamA2 d L N msq (V₀c msq b₀) lbar (ctr d L N) - 1) + 1‖ := by ring_nf
      _ ≤ ‖lamA2 d L N msq (V₀c msq b₀) lbar (ctr d L N) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖b₀‖ + 1 := by rw [norm_one]; linarith
      _ = 1 + C1 * ‖b₀‖ := by ring
  have hq : ‖(lamA2 d L N msq (V₀c msq b₀) lbar (ctr d L N) * tau d L N msq + E) /
      (1 + Suscept.utN d L N msq (V₀c msq b₀))‖ ≤
      2 * ((1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
        C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N))))) := by
    rw [norm_div]
    have hpos : 0 < ‖1 + Suscept.utN d L N msq (V₀c msq b₀)‖ := by linarith
    rw [div_le_iff₀ hpos]
    have h1 : ‖lamA2 d L N msq (V₀c msq b₀) lbar (ctr d L N) * tau d L N msq + E‖ ≤
        (1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
          C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
            (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N)))) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul hlam' hτ (norm_nonneg _) (by positivity)
      · refine hE.trans (le_of_eq ?_); ring
    have h0 : 0 ≤ (1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
        C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N)))) := by
      have := Suscept.card_lam_pos (d := d) (L := L) N
      positivity
    nlinarith
  calc ‖avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
        (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) - GamA d L V₀c lbar msq b₀‖
      = ‖(gamA2 d L N msq (V₀c msq b₀) lbar (ctr d L N) - GamA d L V₀c lbar msq b₀) +
          (lamA2 d L N msq (V₀c msq b₀) lbar (ctr d L N) * tau d L N msq + E) /
            (1 + Suscept.utN d L N msq (V₀c msq b₀))‖ := by rw [havg]; ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ bd N := by rw [hbd_def]; exact add_le_add hg hq

end

end Ward
