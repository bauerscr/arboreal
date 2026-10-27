import Ward.ObsLimitQ2
import Ward.ObsLimitCorr

/-!
# The truncated four-point function converges to `Q2` at `m² > 0`

`trunc_tendsto`: for `m² > 0`, `|b₀| ≤ λ̄`, `x ∈ ℤ^d ∖ {0}`,
`⟨ψ̄₀ψ₀ ψ̄_xψ_x⟩_N - ⟨ψ̄₀ψ₀⟩_N ⟨ψ̄_xψ_x⟩_N → Qtwo x`.

Proof: with `U = 1 + ũ`, the Case (2) component formulas (`PtCorr.ε_ZtO_ab_two`,
`PtCorr.ε_ZtO_a_two`, `PtCorr.ε_ZtO_b_two`) give
`T_N - q_N/λ̄² = (R τ + k_ab)/(λ̄² U) - (γ_a B + A γ_b + A B)/λ̄²` (`trunc_alg`), where
`A = (λ̃_a τ + ε(K_a))/U`, `B = (λ̃_b τ + ε(K_b))/U`, `R = η - (r_a + r_b) + λ̃_a γ_b + λ̃_b γ_a`;
all of `γ`, `λ̃`, `η`, `r` are bounded uniformly in `N`, and `τ`, `ε(K)`, `k_ab` are
`O(τ + |b₀| L^{-κN}) → 0`.  With `qN2_rate`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem trunc_alg {q ga gb a1 a2 b1 b2 R k l U τ Q : ℂ} (hU : U ≠ 0) (hl : l ≠ 0) :
    ((q + ga * gb) * U + R * τ + k) / (l ^ 2 * U) -
        (ga * U + a1 * τ + a2) / (l * U) * ((gb * U + b1 * τ + b2) / (l * U)) - Q =
      ((R * τ + k) / (l ^ 2 * U) - (ga * ((b1 * τ + b2) / U) + (a1 * τ + a2) / U * gb +
        (a1 * τ + a2) / U * ((b1 * τ + b2) / U)) / l ^ 2) + (q / l ^ 2 - Q) := by
  field_simp; ring

/-- Norm bound for the right side of `trunc_alg`. -/
theorem trunc_bd {ga gb A' B' R k τ U : ℂ} {l G cA cR ck s ℓ2 : ℝ} (hl : 0 < l)
    (hU : 1 / 2 ≤ ‖U‖) (hga : ‖ga‖ ≤ G) (hgb : ‖gb‖ ≤ G) (hA : ‖A'‖ ≤ cA * s)
    (hB : ‖B'‖ ≤ cA * s) (hR : ‖R‖ ≤ cR) (hτ : ‖τ‖ ≤ s) (hk : ‖k‖ ≤ ck * s + ℓ2 * s ^ 2)
    (hs : 0 ≤ s) (hG : 0 ≤ G) (hcA : 0 ≤ cA) (hcR : 0 ≤ cR) :
    ‖(R * τ + k) / (l ^ 2 * U) - (ga * (B' / U) + A' / U * gb + A' / U * (B' / U)) / l ^ 2‖ ≤
      (2 * (cR * s + ck * s + ℓ2 * s ^ 2) + (2 * G * (2 * cA * s) + (2 * cA * s) ^ 2)) / l ^ 2 := by
  have hU0 : 0 < ‖U‖ := by linarith
  have hl2 : 0 < l ^ 2 := by positivity
  have hAU0 : 0 ≤ 2 * cA * s := by positivity
  have hUU := mul_le_mul_of_nonneg_left hU hAU0
  have hAU : ‖A' / U‖ ≤ 2 * cA * s := by
    rw [norm_div, div_le_iff₀ hU0]; nlinarith
  have hBU : ‖B' / U‖ ≤ 2 * cA * s := by
    rw [norm_div, div_le_iff₀ hU0]; nlinarith
  have h1 : ‖(R * τ + k) / (l ^ 2 * U)‖ ≤ 2 * (cR * s + ck * s + ℓ2 * s ^ 2) / l ^ 2 := by
    have hn : ‖R * τ + k‖ ≤ cR * s + (ck * s + ℓ2 * s ^ 2) :=
      (norm_add_le _ _).trans (add_le_add (by rw [norm_mul]; exact mul_le_mul hR hτ (norm_nonneg _) hcR) hk)
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hl.le,
      div_le_div_iff₀ (by positivity) hl2]
    have hX : 0 ≤ cR * s + (ck * s + ℓ2 * s ^ 2) := (norm_nonneg _).trans hn
    have h3 : ‖R * τ + k‖ ≤ 2 * (cR * s + ck * s + ℓ2 * s ^ 2) * ‖U‖ := by nlinarith
    calc ‖R * τ + k‖ * l ^ 2 ≤ (2 * (cR * s + ck * s + ℓ2 * s ^ 2) * ‖U‖) * l ^ 2 :=
          mul_le_mul_of_nonneg_right h3 hl2.le
      _ = 2 * (cR * s + ck * s + ℓ2 * s ^ 2) * (l ^ 2 * ‖U‖) := by ring
  have h2 : ‖(ga * (B' / U) + A' / U * gb + A' / U * (B' / U)) / l ^ 2‖ ≤
      (2 * G * (2 * cA * s) + (2 * cA * s) ^ 2) / l ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hl.le]
    refine div_le_div_of_nonneg_right ?_ hl2.le
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have := mul_le_mul hga hBU (norm_nonneg _) hG
    have := mul_le_mul hAU hgb (norm_nonneg _) hAU0
    have := mul_le_mul hAU hBU (norm_nonneg _) hAU0
    nlinarith
  calc _ ≤ ‖(R * τ + k) / (l ^ 2 * U)‖ +
        ‖(ga * (B' / U) + A' / U * gb + A' / U * (B' / U)) / l ^ 2‖ := norm_sub_le _ _
    _ ≤ 2 * (cR * s + ck * s + ℓ2 * s ^ 2) / l ^ 2 +
        (2 * G * (2 * cA * s) + (2 * cA * s) ^ 2) / l ^ 2 := add_le_add h1 h2
    _ = _ := by ring

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs Cq Cb : ℝ} (hCs : 0 ≤ Cs)
  (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs) (hCq : 0 ≤ Cq) (hCb : 0 ≤ Cb)
  (hP : PairHyp2 d L A ℓ₀ V₀c lbar C κ Cq Cb)
include H hd hCs hS hCq hCb hP

theorem gaN_bd (hd2 : 2 ≤ d) (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ}
    (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ} {b : Lam d L N} (hb : b ≠ ctr d L N) :
    ‖gaN d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N) b‖ ≤
        (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 / (1 - rho d L) ∧
      ‖gbN d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N) b‖ ≤
        (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 / (1 - rho d L) := by
  have hρ0 := rho_nonneg d L
  have hρ1 := rho_lt_one hd3 (by have := three_le_L H; omega) (L := L)
  have hK : 0 ≤ (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 := by
    have := Lm_nonneg H hd hCs hS b₀; have := E_nonneg H hd hCs hS b₀; positivity
  have hsum : ∑ k ∈ range N, rho d L ^ k ≤ 1 / (1 - rho d L) := by
    have := sum_Ico_pow_le hρ0 hρ1 0 N
    rwa [← range_eq_Ico, pow_zero] at this
  constructor
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ range N, ‖gaOf .two (nextAt d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ))
          (ctr d L N) b k)‖
        ≤ ∑ k ∈ range N, (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * rho d L ^ k :=
          sum_le_sum fun k hk => ga_N_bd H hd hCs hS hd2 hmsq hb₀ hb (mem_range.1 hk)
      _ = (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * ∑ k ∈ range N, rho d L ^ k := by
          rw [mul_sum]
      _ ≤ (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * (1 / (1 - rho d L)) :=
          mul_le_mul_of_nonneg_left hsum hK
      _ = _ := by ring
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ range N, ‖gbOf .two (nextAt d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ))
          (ctr d L N) b k)‖
        ≤ ∑ k ∈ range N, (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * rho d L ^ k :=
          sum_le_sum fun k hk => gb_N_bd H hd hCs hS hd2 hmsq hb₀ hb (mem_range.1 hk)
      _ = (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * ∑ k ∈ range N, rho d L ^ k := by
          rw [mul_sum]
      _ ≤ (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * (1 / (1 - rho d L)) :=
          mul_le_mul_of_nonneg_left hsum hK
      _ = _ := by ring

set_option maxHeartbeats 3200000 in
/-- **`⟨ψ̄₀ψ₀ψ̄_xψ_x⟩ - ⟨ψ̄₀ψ₀⟩⟨ψ̄_xψ_x⟩ → Q2(x)`** at `m² > 0`. -/
theorem trunc_tendsto (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 < msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {x : Zd d} (hx0 : x ≠ 0) :
    Tendsto (fun N => avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
        (psibar (0 : Lam d L N) * psi (0 : Lam d L N) *
          (psibar (prj x : Lam d L N) * psi (prj x : Lam d L N))) -
      avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
          (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) *
        avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
          (psibar (prj x : Lam d L N) * psi (prj x : Lam d L N))) atTop
      (𝓝 (Qtwo d L V₀c lbar msq b₀ x)) := by
  have hd2 : 2 ≤ d := by omega
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hlb := H.fd.lbar_pos
  have hκ := H.fd.κ_pos
  have hC0 := H.fd.C_nonneg
  have hθ0 := th_nonneg L κ
  have hθ1 := th_lt_one hL2 hκ (L := L)
  have h1θ : 0 < 1 - th L κ := by linarith
  have hρ1 := rho_lt_one hd3 hL2 (L := L)
  have h1ρ : 0 < 1 - rho d L := by linarith
  have hLm := Lm_nonneg H hd hCs hS b₀
  have hE := E_nonneg H hd hCs hS b₀
  have hℓ2 : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
  -- the uniform constants
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G =
      (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 / (1 - rho d L) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  obtain ⟨cA, hcA⟩ : ∃ cA : ℝ, cA = Lm lbar C κ Cs b₀ L + C * lbar * ‖b₀‖ + ℓ₀ ^ 2 :=
    ⟨_, rfl⟩
  have hcA0 : 0 ≤ cA := by rw [hcA]; positivity
  obtain ⟨cR, hcR⟩ : ∃ cR : ℝ, cR =
      4 * (lbar + Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) ^ 2 * ℓ₀ ^ 2 +
        2 * (Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ)) +
        2 * ((Lm lbar C κ Cs b₀ L + C * lbar * ‖b₀‖) * G) := ⟨_, rfl⟩
  have hcR0 : 0 ≤ cR := by rw [hcR]; positivity
  obtain ⟨ck, hck⟩ : ∃ ck : ℝ, ck = 2 * G * ℓ₀ ^ 2 + ℓ₀ ^ 2 * ℓ₀ ^ 2 := ⟨_, rfl⟩
  -- `s_N = τ_N + e_N`
  obtain ⟨s, hs_def⟩ : ∃ s : ℕ → ℝ, s = fun N : ℕ =>
      1 / (msq * Fintype.card (Lam d L N)) + C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) :=
    ⟨_, rfl⟩
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have t3 := tendsto_rpow_neg_mul (L := L) hL2 hκ
    have t4 := tendsto_inv_card (d := d) hd hL2 hmsq
    have := t4.add (t3.const_mul (C * lbar * ‖b₀‖))
    rw [hs_def]; simpa using this
  obtain ⟨bd, hbd_def⟩ : ∃ bd : ℕ → ℝ, bd = fun N : ℕ =>
      Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2) *
        (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) +
      (2 * (cR * s N + ck * s N + ℓ₀ ^ 2 * s N ^ 2) +
        (2 * G * (2 * cA * s N) + (2 * cA * s N) ^ 2)) / lbar ^ 2 := ⟨_, rfl⟩
  have hbd : Tendsto bd atTop (𝓝 0) := by
    have t1 := tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)
    have := (t1.const_mul (Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) /
        (rho d L * lbar ^ 2))).add
      ((((((hs0.const_mul cR).add (hs0.const_mul ck)).add ((hs0.pow 2).const_mul (ℓ₀ ^ 2))).const_mul
        2).add (((hs0.const_mul (2 * cA)).const_mul (2 * G)).add
          ((hs0.const_mul (2 * cA)).pow 2))).div_const (lbar ^ 2))
    rw [hbd_def]; simpa using this
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
  filter_upwards [hev1, hev2, eventually_ge_atTop (2 + supNormZ x)] with N hm hu2 hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hs : supNormZ x ≤ L ^ (N - 1) := by
    have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
    have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hb := ctr_add_prj_ne hL3 (N := N) hN1 hx0 hs
  have hu : ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ 1 / 2 :=
    (Psi4.utN_le_of_mass hd H.fd hmsq hm hb₀).trans hu2
  have hu0 : 1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 := by
    intro h
    have : Suscept.utN d L N msq (V₀c msq b₀) = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hu; norm_num at hu
  have hu1 : 1 / 2 ≤ ‖1 + Suscept.utN d L N msq (V₀c msq b₀)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-Suscept.utN d L N msq (V₀c msq b₀))
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  have hl : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlb.ne'
  have hgood := H.fd.good N msq hmsq.le
  -- translation to `(ctr, ctr + x)`
  have t4 := avg_four_transl (msq := msq) hmsq hN1 (V₀c msq b₀) (ctr d L N) (0 : Lam d L N)
    (prj x : Lam d L N)
  have t1 := avg_psibar_psi_transl (msq := msq) hmsq hN1 (V₀c msq b₀) (ctr d L N)
    (0 : Lam d L N) (0 : Lam d L N)
  have t2 := avg_psibar_psi_transl (msq := msq) hmsq hN1 (V₀c msq b₀) (ctr d L N)
    (prj x : Lam d L N) (prj x : Lam d L N)
  rw [zero_add] at t4 t1
  rw [add_comm (prj x : Lam d L N)] at t4 t2
  rw [← t4, ← t1, ← t2]
  -- the component formulas
  have h4 := avg_two_ab_eq' hd H.fd.hL8 hN1 hmsq hgood (V₀c msq b₀) hl (ctr d L N)
    (ctr d L N + prj x)
  have ha := avg_two_a_eq' hd H.fd.hL8 hN1 hmsq hgood (V₀c msq b₀) hl (ctr d L N)
    (ctr d L N + prj x)
  have hbb := avg_two_b_eq' hd H.fd.hL8 hN1 hmsq hgood (V₀c msq b₀) hl (ctr d L N)
    (ctr d L N + prj x)
  have f4 := ε_ZtO_ab_two (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) hd H.fd.hL8
    hN1 hmsq hgood
  have fa := ε_ZtO_a_two (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) hd H.fd.hL8
    hN1 hmsq hgood
  have fb := ε_ZtO_b_two (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) hd H.fd.hL8
    hN1 hmsq hgood
  have f4' : ε (((eu d L N msq (V₀c msq b₀) • Gobs d L .two N msq (V₀c msq b₀) (lbar : ℂ)
      (ctr d L N) (ctr d L N + prj x) : OE .two (Lam d L N))) : SA .two (Lam d L N)).ab = _ := f4
  have fa' : ε (((eu d L N msq (V₀c msq b₀) • Gobs d L .two N msq (V₀c msq b₀) (lbar : ℂ)
      (ctr d L N) (ctr d L N + prj x) : OE .two (Lam d L N))) : SA .two (Lam d L N)).a = _ := fa
  have fb' : ε (((eu d L N msq (V₀c msq b₀) • Gobs d L .two N msq (V₀c msq b₀) (lbar : ℂ)
      (ctr d L N) (ctr d L N + prj x) : OE .two (Lam d L N))) : SA .two (Lam d L N)).b = _ := fb
  rw [h4, ha, hbb, f4', fa', fb', trunc_alg hu0 hl]
  have hq := qN2_rate H hd hCs hS hCq hCb hP hd3 hmsq.le hb₀ hx0 hN2 hs
  -- the bounds
  have hθN : (L : ℝ) ^ (-(κ * N)) = th L κ ^ N := rpow_neg_mul_nat (Nat.cast_nonneg _) κ N
  have heN0 : 0 ≤ C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg L) (-(κ * N)); positivity
  have heN : C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) ≤ C * lbar * ‖b₀‖ := by
    rw [hθN]
    calc C * lbar * ‖b₀‖ * th L κ ^ N ≤ C * lbar * ‖b₀‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hθ0 hθ1.le) hE
      _ = _ := mul_one _
  have hτb0 : 0 ≤ 1 / (msq * Fintype.card (Lam d L N)) := by
    have := Suscept.card_lam_pos (d := d) (L := L) N; positivity
  have hsN : s N = 1 / (msq * Fintype.card (Lam d L N)) +
      C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) := by rw [hs_def]
  have hsN0 : 0 ≤ s N := by rw [hsN]; positivity
  have hτ := norm_tau_le (d := d) (L := L) (N := N) hd hmsq
  have hτs : ‖tau d L N msq‖ ≤ s N := by rw [hsN]; linarith
  have heS : C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) ≤ s N := by rw [hsN]; linarith
  have hKN := (H.fd.obs .two N msq (lbar : ℂ) b₀ (ctr d L N + prj x) hmsq.le
    (by rw [norm_lbar H]; exact hb₀) (le_of_eq (norm_lbar H)) hb N le_rfl).2
  rw [norm_lbar H] at hKN
  obtain ⟨k1, k2, k3, k4, k5⟩ := kTwo_bounds H.fd.hℓ₀ H.fd.hA1 heN0 (initObs .two (lbar : ℂ)) hKN
  have hla := la_N_bd H hd hCs hS hmsq.le hb₀ hb (k := N) le_rfl
  have hlb' := lb_N_bd H hd hCs hS hmsq.le hb₀ hb (k := N) le_rfl
  obtain ⟨hgaN, hgbN⟩ := gaN_bd H hd hCs hS hCq hCb hP hd2 hd3 hmsq.le hb₀ hb
  rw [← hG] at hgaN hgbN
  obtain ⟨heta, hra, hrb⟩ := (hP msq hmsq.le b₀ hb₀ N (ctr d L N + prj x) hb).1 N le_rfl
  have hℓN := ellj_sq_le (L := L) hd2 ℓ₀ N
  have hℓN' := ellj_sq_le (L := L) hd2 ℓ₀ (min N (coal L (ctr d L N) (ctr d L N + prj x)))
  set lta := lamtA d L N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
    (ctr d L N + prj x) with hlta_def
  set ltb := lamtB d L N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
    (ctr d L N + prj x) with hltb_def
  set gA' := gaN d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
    (ctr d L N + prj x) with hgA'
  set gB' := gbN d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
    (ctr d L N + prj x) with hgB'
  have hlta : ‖lta‖ ≤ Lm lbar C κ Cs b₀ L + C * lbar * ‖b₀‖ := by
    have := norm_le_insert' lta (laOf .two (VoN d L .two N msq (V₀c msq b₀)
      (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x)))
    rw [norm_sub_rev] at this
    linarith
  have hltb : ‖ltb‖ ≤ Lm lbar C κ Cs b₀ L + C * lbar * ‖b₀‖ := by
    have := norm_le_insert' ltb (lbOf .two (VoN d L .two N msq (V₀c msq b₀)
      (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x)))
    rw [norm_sub_rev] at this
    linarith
  have hLe : 0 ≤ Lm lbar C κ Cs b₀ L + C * lbar * ‖b₀‖ := by positivity
  refine (norm_add_le _ _).trans ?_
  rw [hbd_def]
  refine (add_comm _ _).le.trans (add_le_add hq ?_)
  refine (trunc_bd (l := lbar) (G := G) (cA := cA) (cR := cR) (ck := ck) (s := s N)
    (ℓ2 := ℓ₀ ^ 2) hlb hu1 hgaN hgbN ?_ ?_ ?_ hτs ?_ hsN0 hG0 hcA0 hcR0).trans (le_of_eq rfl)
  · -- `A`
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hlta hτs (norm_nonneg _) hLe
    have : ℓ₀ ^ 2 * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) ≤ ℓ₀ ^ 2 * s N :=
      mul_le_mul_of_nonneg_left heS hℓ2
    have := mul_le_mul_of_nonneg_right hℓN heN0
    rw [hcA]; nlinarith
  · -- `B`
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hltb hτs (norm_nonneg _) hLe
    have : ℓ₀ ^ 2 * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) ≤ ℓ₀ ^ 2 * s N :=
      mul_le_mul_of_nonneg_left heS hℓ2
    have := mul_le_mul_of_nonneg_right hℓN heN0
    rw [hcA]; nlinarith
  · -- `R`
    have h1 : ‖etaOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x)) -
        (raOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x)) +
          rbOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))) +
        lta * gB' + ltb * gA'‖ ≤
        ‖etaOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))‖ +
          (‖raOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))‖ +
            ‖rbOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x))‖) +
          ‖lta‖ * ‖gB'‖ + ‖ltb‖ * ‖gA'‖ := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) (norm_mul_le _ _)))
        (norm_mul_le _ _))
    refine h1.trans ?_
    have e1 : ‖etaOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N)
        (ctr d L N + prj x))‖ ≤ 4 * (lbar + Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) ^ 2 * ℓ₀ ^ 2 :=
      heta
    have e2 : ‖raOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N)
        (ctr d L N + prj x))‖ ≤ Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ) := hra
    have e3 : ‖rbOf .two (Vo2 d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N)
        (ctr d L N + prj x))‖ ≤ Cb * ℓ₀ ^ 2 * (C * lbar * ‖b₀‖) / (1 - th L κ) := hrb
    have e4 := mul_le_mul hlta hgbN (norm_nonneg _) hLe
    have e5 := mul_le_mul hltb hgaN (norm_nonneg _) hLe
    rw [hcR]; nlinarith
  · -- `k_ab`
    refine k5.trans ?_
    have hga2 : ‖gA'‖ + ‖gB'‖ ≤ 2 * G := by linarith
    have p1 : (‖gA'‖ + ‖gB'‖) * ellj d L ℓ₀ N ^ 2 ≤ 2 * G * ℓ₀ ^ 2 :=
      mul_le_mul hga2 hℓN (sq_nonneg _) (by positivity)
    have p2 : ellj d L ℓ₀ N ^ 2 * ellj d L ℓ₀ (min N (coal L (ctr d L N) (ctr d L N + prj x))) ^ 2
        ≤ ℓ₀ ^ 2 * ℓ₀ ^ 2 := mul_le_mul hℓN hℓN' (sq_nonneg _) hℓ2
    have p3 : ‖tau d L N msq‖ *
        ellj d L ℓ₀ (min N (coal L (ctr d L N) (ctr d L N + prj x))) ^ 2 ≤ s N * ℓ₀ ^ 2 :=
      mul_le_mul hτs hℓN' (sq_nonneg _) hsN0
    have hX : 0 ≤ (‖gA'‖ + ‖gB'‖) * ellj d L ℓ₀ N ^ 2 +
        ellj d L ℓ₀ N ^ 2 * ellj d L ℓ₀ (min N (coal L (ctr d L N) (ctr d L N + prj x))) ^ 2 +
        ‖tau d L N msq‖ * ellj d L ℓ₀ (min N (coal L (ctr d L N) (ctr d L N + prj x))) ^ 2 := by
      positivity
    calc ((‖gA'‖ + ‖gB'‖) * ellj d L ℓ₀ N ^ 2 +
          ellj d L ℓ₀ N ^ 2 * ellj d L ℓ₀ (min N (coal L (ctr d L N) (ctr d L N + prj x))) ^ 2 +
          ‖tau d L N msq‖ * ellj d L ℓ₀ (min N (coal L (ctr d L N) (ctr d L N + prj x))) ^ 2) *
          (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)))
        ≤ (2 * G * ℓ₀ ^ 2 + ℓ₀ ^ 2 * ℓ₀ ^ 2 + s N * ℓ₀ ^ 2) * s N :=
          mul_le_mul (by linarith) heS heN0 (by positivity)
      _ = ck * s N + ℓ₀ ^ 2 * s N ^ 2 := by rw [hck]; ring

end

end Ward
