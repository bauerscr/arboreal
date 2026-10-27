import PtCorr.Const
import PtCorr.SusceptObs
import PtCorr.CoupBd
import PtCorr.Recur
import PtCorr.Setup

/-!
# Finite-`N` bound on `λ^{(1)}` (Section `sec:obs`, `lem:1pt` Case (1), Tier 1)

The paper proves `λ^{(1)}_{x,∞} = λ₀` by an `N → ∞` argument.  At finite `N` and `m² > 0` we
combine instead:
* the `λ^{(1)}` identity (`PtCorr.c1m_RcO_Gobs_one_a`, via the susceptibility):
  `c1m (Rc Z̃^obs)_a = l₀ (1 + ũ - ã/m²)`;
* the component formula (`PtCorr.c1m_RcO_ZtO_a_one`): `c1m (Rc Z̃^obs)_a = λ_{a,N} + k_a`,
  `|k_a| ≤ ‖K^obs_N‖_N` (`kOne_bounds`);
so `λ_{a,N} - l₀ = l₀ (ũ - ã/m²) - k_a` (`la_N_sub_eq_one`), and the same for `b`
(`λ_{b,N} - l₀ = l₀ (ũ - ã/m²) + k_b`).  Then
`|ũ - ã/m²| ≤ |ũ - t_N ã| + |ã| (1/m² - t_N) ≤ ‖K_N‖ + K ℓ₀^{-2} (‖V_N‖ + ‖K_N‖)`
(`norm_utN_sub_atN_div_le`), `= O(|b₀| L^{-κN})` along the bulk flow (`FlowData.bulk`).  Summing
`Obs.Vobs_recursion_one` backwards (`PtCorr.lam_one_tail`) gives the bound for all `j ≤ N`
(`lam_one_tail_flow`).  For a given flow with `FlowData` this is `lamOne_of`; with the flow
of `PtCorr.setup`:

**`lamOne_bound`**: `‖λ_{a,j} - l₀‖, ‖λ_{b,j} - l₀‖ ≤ C ‖l₀‖ ‖b₀‖ L^{-κ j}` for all `j ≤ N`
(`a = ctr`, `b ≠ a`, `m² > 0`, `‖b₀‖ ≤ ‖l₀‖ ≤ λ̄`).

**Deviation** (simplification): no `N → ∞` limit, no consistency of the observable flow; the
constants do not depend on `N`, `m² > 0`, `b`.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD

variable {d L : ℕ} [NeZero L]

variable (d L) in
/-- `λ_{a,j}` along the Case (1) observable flow started at `initObs .one l₀`. -/
abbrev laOne (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N) (j : ℕ) : ℂ :=
  laOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1

variable (d L) in
/-- `λ_{b,j}` along the Case (1) observable flow started at `initObs .one l₀`. -/
abbrev lbOne (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N) (j : ℕ) : ℂ :=
  lbOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1

/-- `|ũ - ã/m²| ≤ ‖K_N‖_N + K ℓ₀^{-2} (‖V_N‖_N + ‖K_N‖_N)` (`m² > 0`), with the constant `K`
of `FRD.tN_sub_inv`. -/
theorem norm_utN_sub_atN_div_le (hd : 1 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℕ) [NeZero L] (N : ℕ)
    {ℓ₀ : ℝ}, 0 < ℓ₀ → ∀ (A msq : ℝ), 0 < msq → ∀ V₀ : Vcoup,
    ‖Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ)‖ ≤
      (Suscept.KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal + K * (ℓ₀ ^ 2)⁻¹ *
        ((Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N) (Suscept.VN d L N msq V₀)).toReal +
          (Suscept.KNnorm d L N msq V₀ (ellj d L ℓ₀ N) A).toReal) := by
  obtain ⟨K, hK0, hK⟩ := norm_atN_mul_inv_sub_tN_le hd
  refine ⟨K, hK0, fun L _ N ℓ₀ hℓ₀ A msq hmsq V₀ => ?_⟩
  obtain ⟨h0, h1⟩ := hK L N hℓ₀ A msq hmsq V₀
  have h2 := norm_utN_sub_le (d := d) (L := L) (N := N) hℓ₀ A msq V₀
  have hm : (msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmsq.ne'
  have e : Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ) =
      (Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ * (Suscept.tNN d L N msq : ℂ)) -
        Suscept.atN d L N msq V₀ * ((1 / msq - Suscept.tNN d L N msq : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add h2 ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

section Main

variable {N : ℕ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N) {msq ℓ₀ : ℝ}

/-- `λ_{a,N} - l₀ = l₀ (ũ - ã/m²) - k_a` and `λ_{b,N} - l₀ = l₀ (ũ - ã/m²) + k_b`. -/
theorem la_N_sub_eq_one (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j)) :
    laOne d L N msq V₀ l₀ a b N - l₀ =
        l₀ * (Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ)) -
          kaOne d L N msq V₀ (initObs .one l₀) a b ∧
      lbOne d L N msq V₀ l₀ a b N - l₀ =
        l₀ * (Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ)) +
          kbOne d L N msq V₀ (initObs .one l₀) a b := by
  have h1 := c1m_RcO_ZtO_a_one V₀ l₀ a b hd hL hN hmsq hgood
  have h2 := c1m_RcO_Gobs_one_a V₀ l₀ a b hd hL hN hmsq hgood
  have h3 := c1p_ZtO_b_one V₀ l₀ a b hd hL hN hmsq hgood
  have h4 := c1p_RcO_Gobs_one_b V₀ l₀ a b hd hL hN hmsq hgood
  rw [coe_RcO_b, c1p_Rc] at h4
  have ea : laOne d L N msq V₀ l₀ a b N + kaOne d L N msq V₀ (initObs .one l₀) a b =
      l₀ * (1 + Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ)) := by
    rw [← h2]; exact h1.symm
  have eb : -lbOne d L N msq V₀ l₀ a b N + kbOne d L N msq V₀ (initObs .one l₀) a b =
      -(l₀ * (1 + Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ))) := by
    rw [← h4]; exact h3.symm
  constructor
  · linear_combination ea
  · linear_combination -eb

/-- **Finite-`N` bound at the last scale**: with `|ũ - ã/m²| ≤ U` and `‖K^obs_N‖_N ≤ e`,
`‖λ_{a,N} - l₀‖, ‖λ_{b,N} - l₀‖ ≤ ‖l₀‖ U + e`. -/
theorem la_N_sub_le_one (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j))
    (hℓ₀ : 0 < ℓ₀) {A : ℝ} (hA : 1 ≤ A) {U e : ℝ} (he : 0 ≤ e)
    (hU : ‖Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ)‖ ≤ U)
    (hK : KnormObs .one ℓ₀ a b N A (flowO d L .one N msq V₀ (initObs .one l₀) a b N).2 ≤
      ENNReal.ofReal e) :
    ‖laOne d L N msq V₀ l₀ a b N - l₀‖ ≤ ‖l₀‖ * U + e ∧
      ‖lbOne d L N msq V₀ l₀ a b N - l₀‖ ≤ ‖l₀‖ * U + e := by
  obtain ⟨ea, eb⟩ := la_N_sub_eq_one V₀ l₀ a b hd hL hN hmsq hgood
  obtain ⟨ka, kb, -⟩ := kOne_bounds hℓ₀ hA he (initObs .one l₀) hK
  have hl : ‖l₀ * (Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ))‖ ≤
      ‖l₀‖ * U := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hU (norm_nonneg _)
  rw [ea, eb]
  exact ⟨(norm_sub_le _ _).trans (add_le_add hl ka), (norm_add_le _ _).trans (add_le_add hl kb)⟩

end Main

/-- **Summing `lem:Vobs-recursion` backwards** (Case (1)): if `‖K^obs_k‖_k ≤ e θ^k` for
`k < N` and `‖λ_{x,N} - l₀‖ ≤ B θ^N` (`x = a, b`), then
`‖λ_{x,j} - l₀‖ ≤ (B + C_S e/(1-θ)) θ^j` for all `j ≤ N` (`C_S` of `Obs.Vobs_recursion_one`). -/
theorem lam_one_tail_flow (d : ℕ) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L], 1 ≤ d →
    2 ^ (d + 3) ≤ L → ∀ (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (ℓ₀ : ℝ), 0 < ℓ₀ →
    (∀ k < N, GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k)) →
    ∀ (l₀ : ℂ) (a b : Lam d L N) (A : ℝ), 1 ≤ A → ∀ {e θ B : ℝ}, 0 ≤ e → 0 ≤ θ → θ < 1 →
    0 ≤ B →
    (∀ k < N, KnormObs .one ℓ₀ a b k A (flowO d L .one N msq V₀ (initObs .one l₀) a b k).2 ≤
      ENNReal.ofReal (e * θ ^ k)) →
    ‖laOne d L N msq V₀ l₀ a b N - l₀‖ ≤ B * θ ^ N →
    ‖lbOne d L N msq V₀ l₀ a b N - l₀‖ ≤ B * θ ^ N →
    ∀ j ≤ N, ‖laOne d L N msq V₀ l₀ a b j - l₀‖ ≤ (B + Cs * e / (1 - θ)) * θ ^ j ∧
      ‖lbOne d L N msq V₀ l₀ a b j - l₀‖ ≤ (B + Cs * e / (1 - θ)) * θ ^ j := by
  obtain ⟨Cs, hCs, hrec⟩ := Vobs_recursion_one d
  refine ⟨Cs, hCs, ?_⟩
  intro L _ hd1 hL N msq V₀ ℓ₀ hℓ₀ hC l₀ a b A hA e θ B he hθ0 hθ1 hB hK hNa hNb j hj
  have hstep : ∀ k < N,
      ‖laOne d L N msq V₀ l₀ a b (k + 1) - laOne d L N msq V₀ l₀ a b k‖ ≤ Cs * (e * θ ^ k) ∧
      ‖lbOne d L N msq V₀ l₀ a b (k + 1) - lbOne d L N msq V₀ l₀ a b k‖ ≤ Cs * (e * θ ^ k) := by
    intro k hk
    have H := hrec L N k ℓ₀ hℓ₀ (Flow.covAt d L N msq k)
      (flowO d L .one N msq V₀ (initObs .one l₀) a b k).1
      (flowO d L .one N msq V₀ (initObs .one l₀) a b k).2 a b A hA (e * θ ^ k) (by positivity)
      (hK k hk) (fun hlt Y hY => abSmall_flowO V₀ l₀ a b hd1 hL hC hk hlt hY)
    exact ⟨H.1, H.2.1⟩
  exact ⟨lam_one_tail (fun k => laOne d L N msq V₀ l₀ a b k) l₀ hB hCs he hθ0 hθ1 hNa
      (fun k hk => (hstep k hk).1) hj,
    lam_one_tail (fun k => lbOne d L N msq V₀ l₀ a b k) l₀ hB hCs he hθ0 hθ1 hNb
      (fun k hk => (hstep k hk).2) hj⟩

/-- **Finite-`N` `λ^{(1)}` bound for a given flow** `V₀c` with `FlowData` (replaces the
`N → ∞` part of `lem:1pt` Case (1)): for `m² > 0`, `‖b₀‖ ≤ ‖l₀‖ ≤ λ̄`, `b ≠ a = ctr` and all
`j ≤ N`, `‖λ_{a,j} - l₀‖ ≤ C ‖l₀‖ ‖b₀‖ L^{-κ j}`, and the same for `λ_{b,j}`. -/
theorem lamOne_of (hd : 3 ≤ d) {L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ}
    {V₀c : ℝ → ℂ → Vcoup} (HF : FlowData d L A ℓ₀ V₀c lbar C κ) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧
      ∀ (N : ℕ) (msq : ℝ) (l₀ b₀ : ℂ) (b : Lam d L N), 0 < msq →
        ‖b₀‖ ≤ ‖l₀‖ → ‖l₀‖ ≤ lbar → b ≠ ctr d L N → ∀ j ≤ N,
          ‖laOne d L N msq (V₀c msq b₀) l₀ (ctr d L N) b j - l₀‖ ≤
              Cl * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
            ‖lbOne d L N msq (V₀c msq b₀) l₀ (ctr d L N) b j - l₀‖ ≤
              Cl * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) := by
  obtain ⟨Kt, hKt, hU⟩ := norm_utN_sub_atN_div_le (d := d) (by omega)
  obtain ⟨Cs, hCs, htail⟩ := lam_one_tail_flow d
  have hℓ₀ := HF.hℓ₀
  have hlbar := HF.lbar_pos
  have hC := HF.C_nonneg
  have hκ := HF.κ_pos
  have hL8 := HF.hL8
  have hA1 := HF.hA1
  have hgood := HF.good
  have hbulk := HF.bulk
  have hobs := HF.obs
  have hLr1 : (1 : ℝ) < L := by
    have : 2 ≤ L := le_trans (by
      have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this) hL8
    exact_mod_cast (by omega : 1 < L)
  set θ : ℝ := (L : ℝ) ^ (-κ) with hθdef
  obtain ⟨hθ0, hθ1⟩ := theta_one hLr1 hκ
  have h1θ : 0 < 1 - θ := by linarith
  set C₁ : ℝ := C * lbar + Kt * (ℓ₀ ^ 2)⁻¹ * (C + C * lbar) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨C₁ + C + Cs * C / (1 - θ), by positivity, ?_⟩
  intro N msq l₀ b₀ b hmsq hbl hll hne j hj
  have hpow : ∀ k : ℕ, (L : ℝ) ^ (-(κ * k)) = θ ^ k := fun k =>
    rpow_neg_mul_nat Lr_pos.le κ k
  have hb₀ : ‖b₀‖ ≤ lbar := hbl.trans hll
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    obtain rfl : j = 0 := by omega
    have e0 : laOne d L 0 msq (V₀c msq b₀) l₀ (ctr d L 0) b 0 = l₀ := rfl
    have e1 : lbOne d L 0 msq (V₀c msq b₀) l₀ (ctr d L 0) b 0 = l₀ := rfl
    rw [e0, e1, sub_self, norm_zero]
    have : 0 ≤ (C₁ + C + Cs * C / (1 - θ)) * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * ((0 : ℕ) : ℝ))) := by
      positivity
    exact ⟨this, this⟩
  -- the flow bounds
  have hK : ∀ k ≤ N, KnormObs .one ℓ₀ (ctr d L N) b k A
      (flowO d L .one N msq (V₀c msq b₀) (initObs .one l₀) (ctr d L N) b k).2 ≤
        ENNReal.ofReal ((C * ‖l₀‖ * ‖b₀‖) * θ ^ k) := by
    intro k hk
    have := (hobs .one N msq l₀ b₀ b hmsq.le hbl hll hne k hk).2
    rwa [hpow k] at this
  obtain ⟨hVN, hKN⟩ := hbulk N msq b₀ hmsq.le hb₀ N le_rfl
  rw [hpow N] at hVN hKN
  -- `|ũ - ã/m²| ≤ C₁ |b₀| θ^N`
  have hUN : ‖Suscept.utN d L N msq (V₀c msq b₀) - Suscept.atN d L N msq (V₀c msq b₀) /
      (msq : ℂ)‖ ≤ C₁ * ‖b₀‖ * θ ^ N := by
    refine (hU L N hℓ₀ A msq hmsq (V₀c msq b₀)).trans ?_
    have hθN : 0 ≤ θ ^ N := by positivity
    have hK' : (Suscept.KNnorm d L N msq (V₀c msq b₀) (ellj d L ℓ₀ N) A).toReal ≤
        C * lbar * ‖b₀‖ * θ ^ N := by
      refine hKN.trans ?_
      have : ‖b₀‖ ^ 2 ≤ lbar * ‖b₀‖ := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hb₀ (norm_nonneg _)
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hC hθN)
      nlinarith
    have hsum : (Vnorm (d := d) (L := L) (N := N) N (ellj d L ℓ₀ N)
          (Suscept.VN d L N msq (V₀c msq b₀))).toReal +
        (Suscept.KNnorm d L N msq (V₀c msq b₀) (ellj d L ℓ₀ N) A).toReal ≤
          (C + C * lbar) * ‖b₀‖ * θ ^ N := by
      have := add_le_add hVN hK'
      nlinarith
    have hk2 : 0 ≤ Kt * (ℓ₀ ^ 2)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hsum hk2
    rw [hC₁]
    nlinarith
  have hla := la_N_sub_le_one (V₀c msq b₀) l₀ (ctr d L N) b (by omega) hL8 hN1 hmsq
    (hgood N msq hmsq.le) hℓ₀ hA1 (by positivity) hUN (hK N le_rfl)
  have hB : ‖l₀‖ * (C₁ * ‖b₀‖ * θ ^ N) + C * ‖l₀‖ * ‖b₀‖ * θ ^ N =
      ((C₁ + C) * ‖l₀‖ * ‖b₀‖) * θ ^ N := by ring
  rw [hB] at hla
  obtain ⟨t1, t2⟩ := htail L (by omega) hL8 N msq (V₀c msq b₀) ℓ₀ hℓ₀ (hgood N msq hmsq.le) l₀
    (ctr d L N) b A hA1 (e := C * ‖l₀‖ * ‖b₀‖) (by positivity) hθ0 hθ1 (by positivity)
    (fun k hk => hK k hk.le) hla.1 hla.2 j hj
  have hfin : ((C₁ + C) * ‖l₀‖ * ‖b₀‖ + Cs * (C * ‖l₀‖ * ‖b₀‖) / (1 - θ)) * θ ^ j =
      (C₁ + C + Cs * C / (1 - θ)) * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) := by
    rw [hpow j]; field_simp
  rw [hfin] at t1 t2
  exact ⟨t1, t2⟩

/-- **Finite-`N` `λ^{(1)}` bound** (`lamOne_of` for the flow of `setup`): for `m² > 0`,
`‖b₀‖ ≤ ‖l₀‖ ≤ λ̄`, `b ≠ a = ctr` and all `j ≤ N`:
`‖λ_{a,j} - l₀‖, ‖λ_{b,j} - l₀‖ ≤ C ‖l₀‖ ‖b₀‖ L^{-κ j}`. -/
theorem lamOne_bound (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), 0 < lbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      ∀ (N : ℕ) (msq : ℝ) (l₀ b₀ : ℂ) (b : Lam d L N), 0 < msq →
        ‖b₀‖ ≤ ‖l₀‖ → ‖l₀‖ ≤ lbar → b ≠ ctr d L N → ∀ j ≤ N,
          ‖laOne d L N msq (V₀c msq b₀) l₀ (ctr d L N) b j - l₀‖ ≤
              C * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
            ‖lbOne d L N msq (V₀c msq b₀) l₀ (ctr d L N) b j - l₀‖ ≤
              C * ‖l₀‖ * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setup hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H⟩ := H L hL hLodd
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hKℓ' => ?_⟩
  obtain ⟨V₀c, lbar, Cf, κ, HF⟩ := H A hA ℓ₀ hℓ₀ hKℓ'
  obtain ⟨C, hC, hlam⟩ := lamOne_of hd HF
  exact ⟨V₀c, lbar, C, κ, HF.lbar_pos, hC, HF.κ_pos, HF.hb, hlam⟩

end

end PtCorr
