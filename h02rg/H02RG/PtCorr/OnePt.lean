import PtCorr.FlowTwo
import PtCorr.Setup
import PtCorr.Const
import PtCorr.Bridge

/-!
# `lem:1pt` / `prop:1pt`, Case (2) (Tier 1: finite `N`, `m² > 0`)

With the observable pair `(a, b) = (ctr, ctr + x)` (`x ≠ 0`, `L` odd, as required by
`Obs.flowObs_of_thm_flow`), the flow started at `initObs .two l₀` with the fixed `l₀ = λ̄`
(`lbar`), and the normalised **finite-`N` point couplings**

* `lamA2 … x = λ_{a,N}/l₀`, `lamB2 … x = λ_{b,N}/l₀` (the `V`-part of `V^obs_N`),
* `gamA2 … x = γ_{a,N}/l₀`, `gamB2 … x = γ_{b,N}/l₀` (the accumulated `u`-parts `gaN`, `gbN`),

`prop_1pt` states, for `m² > 0` and `1 + ũ ≠ 0`:
`|λ - 1| ≤ C|b₀|`, `|γ - W_N(0)| ≤ C|b₀|` and
`⟨ψ̄_0 ψ_0⟩ = γ + (λ τ + E)/(1 + ũ)`, `|E| ≤ C|b₀| (L^{-(d-2+κ)N} + L^{-κN}/(m²|Λ|))`,
both for the couplings at `a` and at `b` (translation invariance: `⟨ψ̄_0ψ_0⟩ = ⟨ψ̄_aψ_a⟩
= ⟨ψ̄_bψ_b⟩`).  The correlation does not depend on `l₀`.

**Deviations (Tier 1).**
* The paper's `N`-independent `λ_∞`, `γ_∞` are replaced by the couplings at scale `N` at the
  actual point.  With these, the formula holds exactly as stated; in
  particular the (false) bound `e:gammainfbd` is not used.  The comparison `γ ≈ W_N(0)`
  (torus, `m² > 0`) replaces `G_{ℤ^d, m²}(0)` (the difference `W_N(0) - G(0)` is of order
  `L^{-(d-2)N}` without a factor `b₀`).
* The 1-point couplings are those of the pair `(ctr, ctr + x)`; the `a`-slot values do not in
  fact depend on `x` (`Obs.nextObs_a_eq`), but this is not needed.
* `E` enters with the factor `1/(1+ũ)` (it comes from `ε(Z̃^obs_a)/(1+ũ)`).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD

/-! ### Pure algebra -/

/-- `‖τ‖ ≤ 1/(m² |Λ|)`. -/
theorem norm_tau_le {d L N : ℕ} [NeZero L] (hd : 1 ≤ d) {msq : ℝ} (hmsq : 0 < msq) :
    ‖tau d L N msq‖ ≤ 1 / (msq * Fintype.card (Lam d L N)) := by
  obtain ⟨ht0, ht1⟩ := tNN_nonneg_le hd hmsq L N
  have hn : (0 : ℝ) < Fintype.card (Lam d L N) := by exact_mod_cast Fintype.card_pos
  rw [tau, Complex.norm_real, Real.norm_of_nonneg (div_nonneg ht0 hn.le)]
  calc Suscept.tNN d L N msq / Fintype.card (Lam d L N) ≤ (1 / msq) / Fintype.card (Lam d L N) :=
        div_le_div_of_nonneg_right ht1 hn.le
    _ = 1 / (msq * Fintype.card (Lam d L N)) := by rw [div_div]

/-- The algebra of the 1-point formula. -/
theorem onePt_alg {l₀ u av εG g la lt k τ W : ℂ} {lbar K Cf t e θN ℓ₀ ℓN T : ℝ}
    (hl : ‖l₀‖ = lbar) (hlbar : 0 < lbar) (hu : 1 + u ≠ 0)
    (he : e = Cf * lbar * t) (hCf : 0 ≤ Cf) (ht : 0 ≤ t)
    (havg : av = εG / (l₀ * (1 + u))) (hεG : εG = g * (1 + u) + lt * τ + k)
    (hla : ‖la - l₀‖ ≤ K * e) (hg : ‖g - la * W‖ ≤ K * e * ℓ₀ ^ 2)
    (hlt : ‖la - lt‖ ≤ e * θN) (hk : ‖k‖ ≤ ℓN ^ 2 * (e * θN))
    (hW : ‖W‖ ≤ 2 * ℓ₀ ^ 2) (hτ : ‖τ‖ ≤ T) (hθN : 0 ≤ θN) :
    ‖la / l₀ - 1‖ ≤ K * Cf * t ∧
    ‖g / l₀ - W‖ ≤ 3 * K * Cf * ℓ₀ ^ 2 * t ∧
    ∃ E : ℂ, ‖E‖ ≤ Cf * t * (θN * T + ℓN ^ 2 * θN) ∧
      av = g / l₀ + (la / l₀ * τ + E) / (1 + u) := by
  have hl0 : l₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hl; linarith
  have hdiv : ∀ z : ℂ, ‖z / l₀‖ = ‖z‖ / lbar := fun z => by rw [norm_div, hl]
  have h1 : ‖la / l₀ - 1‖ ≤ K * Cf * t := by
    rw [show la / l₀ - 1 = (la - l₀) / l₀ by field_simp, hdiv, div_le_iff₀ hlbar]
    calc ‖la - l₀‖ ≤ K * e := hla
      _ = K * Cf * t * lbar := by rw [he]; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [show g / l₀ - W = (g - la * W) / l₀ + (la / l₀ - 1) * W by field_simp; ring]
    refine (norm_add_le _ _).trans ?_
    rw [hdiv, norm_mul]
    have e1 : ‖g - la * W‖ / lbar ≤ K * Cf * ℓ₀ ^ 2 * t := by
      rw [div_le_iff₀ hlbar]
      calc ‖g - la * W‖ ≤ K * e * ℓ₀ ^ 2 := hg
        _ = K * Cf * ℓ₀ ^ 2 * t * lbar := by rw [he]; ring
    have e2 : ‖la / l₀ - 1‖ * ‖W‖ ≤ K * Cf * t * (2 * ℓ₀ ^ 2) :=
      mul_le_mul h1 hW (norm_nonneg _) ((norm_nonneg _).trans h1)
    nlinarith
  · refine ⟨((lt - la) * τ + k) / l₀, ?_, ?_⟩
    · rw [hdiv, div_le_iff₀ hlbar]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_sub_rev]
      have he0 : 0 ≤ e := by rw [he]; positivity
      have := mul_le_mul hlt hτ (norm_nonneg _) (by positivity)
      have hT : 0 ≤ T := (norm_nonneg _).trans hτ
      calc ‖la - lt‖ * ‖τ‖ + ‖k‖ ≤ e * θN * T + ℓN ^ 2 * (e * θN) := by linarith
        _ = Cf * t * (θN * T + ℓN ^ 2 * θN) * lbar := by rw [he]; ring
    · rw [havg, hεG]
      field_simp
      ring

/-! ### Definitions: the normalised point couplings -/

section Defs

variable (d L : ℕ) [NeZero L] (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (l₀ : ℂ) (x : Lam d L N)

/-- `λ_{a,N}/l₀` for the pair `(a, b) = (ctr, ctr + x)` (Case (2)). -/
def lamA2 : ℂ :=
  laOf .two (VoN d L .two N msq V₀ (initObs .two l₀) (ctr d L N) (ctr d L N + x)) / l₀

/-- `λ_{b,N}/l₀` for the pair `(a, b) = (ctr, ctr + x)` (Case (2)). -/
def lamB2 : ℂ :=
  lbOf .two (VoN d L .two N msq V₀ (initObs .two l₀) (ctr d L N) (ctr d L N + x)) / l₀

/-- `γ_{a,N}/l₀` for the pair `(a, b) = (ctr, ctr + x)` (accumulated `u`-part). -/
def gamA2 : ℂ := gaN d L .two N msq V₀ (initObs .two l₀) (ctr d L N) (ctr d L N + x) / l₀

/-- `γ_{b,N}/l₀` for the pair `(a, b) = (ctr, ctr + x)` (accumulated `u`-part). -/
def gamB2 : ℂ := gbN d L .two N msq V₀ (initObs .two l₀) (ctr d L N) (ctr d L N + x) / l₀

end Defs

/-! ### `prop:1pt` -/

variable {d : ℕ}

theorem sum_covAt_ofReal {L N : ℕ} [NeZero L] (msq : ℝ) (a b : Lam d L N) :
    (∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)) =
      ((∑ k ∈ range N, Flow.covAt d L N msq k a b : ℝ) : ℂ) := by push_cast; rfl

theorem norm_sum_covAt_le {L N : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 2 ≤ L) {ℓ₀ msq : ℝ}
    (hℓ₀ : 0 < ℓ₀) (hC : ∀ k < N, GoodCov k ℓ₀ (Flow.covAt d L N msq k)) (a b : Lam d L N) :
    ‖(∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ))‖ ≤ 2 * ℓ₀ ^ 2 := by
  refine (norm_sum_le _ _).trans ?_
  simpa [Complex.norm_real] using sum_abs_covAt_le hd hL hℓ₀ hC a b le_rfl

set_option maxHeartbeats 1000000 in
/-- **`prop:1pt`, Tier 1, for a given flow** `V₀c` with `FlowData` (see `prop_1pt`). -/
theorem prop_1pt_of (hd : 3 ≤ d) {L : ℕ} [NeZero L] {A ℓ₀ lbar Cf κ : ℝ}
    {V₀c : ℝ → ℂ → Vcoup} (HF : FlowData d L A ℓ₀ V₀c lbar Cf κ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ) (x : Lam d L N), 1 ≤ N → 0 < msq → ‖b₀‖ ≤ lbar → x ≠ 0 →
        1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
        (‖lamA2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
          ‖gamA2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ C * ‖b₀‖ ∧
          ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
              (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
            avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
                (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
              gamA2 d L N msq (V₀c msq b₀) lbar x +
                (lamA2 d L N msq (V₀c msq b₀) lbar x * tau d L N msq + E) /
                  (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
        (‖lamB2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
          ‖gamB2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ C * ‖b₀‖ ∧
          ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
              (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
            avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
                (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
              gamB2 d L N msq (V₀c msq b₀) lbar x +
                (lamB2 d L N msq (V₀c msq b₀) lbar x * tau d L N msq + E) /
                  (1 + Suscept.utN d L N msq (V₀c msq b₀))) := by
  obtain ⟨Cs, hCs, hcore⟩ := flowTwo_core hd
  have hL8 := HF.hL8
  have hA1 := HF.hA1
  have hℓ₀ := HF.hℓ₀
  have hlbar := HF.lbar_pos
  have hCf := HF.C_nonneg
  have hκ := HF.κ_pos
  have hmain := HF.two
  have hd1 : 1 ≤ d := by omega
  have hL2 : 2 ≤ L := by
    have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL0 : (0 : ℝ) < L := Lr_pos
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  set θ : ℝ := (L : ℝ) ^ (-κ) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  set K := KTwo Cs θ lbar (Cf * lbar * lbar) with hKdef
  have hK0 : 0 ≤ K := KTwo_nonneg hCs hθ1 hlbar.le (by positivity)
  set C := Cf * (1 + ℓ₀ ^ 2) + K * Cf + 3 * K * Cf * ℓ₀ ^ 2 with hCdef
  have hKCf : 0 ≤ K * Cf := by positivity
  refine ⟨C, by positivity, ?_⟩
  intro N msq b₀ x hN hmsq hb₀ hx hu
  set V₀ := V₀c msq b₀ with hV₀
  set a := ctr d L N with ha
  set b := ctr d L N + x with hbdef
  have hba : b ≠ a := by
    intro h; apply hx; rw [hbdef, ha] at h
    exact add_eq_left.1 h
  obtain ⟨hC, hK⟩ := hmain N msq b₀ b hmsq.le hb₀ hba
  have hnl : ‖(lbar : ℂ)‖ = lbar := by rw [Complex.norm_real, Real.norm_of_nonneg hlbar.le]
  have hl0 : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlbar.ne'
  set e := Cf * lbar * ‖b₀‖ with he
  have he0 : 0 ≤ e := by positivity
  have heb : e ≤ Cf * lbar * lbar := by
    rw [he]; exact mul_le_mul_of_nonneg_left hb₀ (by positivity)
  obtain ⟨c1, c2, c3, c4, -, -, -, -⟩ := hcore L hL8 N msq V₀ ℓ₀ hℓ₀ hC (lbar : ℂ) a b A hA1
    θ e lbar (Cf * lbar * lbar) hθ0 hθ1 he0 hnl.le heb (fun k hk => hK k hk)
  obtain ⟨k1, k2, k3, k4, -⟩ := kTwo_bounds hℓ₀ hA1 (by positivity : 0 ≤ e * θ ^ N)
    (initObs .two (lbar : ℂ)) (hK N le_rfl)
  have hτ := norm_tau_le (L := L) (N := N) hd1 hmsq
  -- the exponents
  have hθN : θ ^ N = (L : ℝ) ^ (-(κ * N)) := (rpow_neg_mul_nat hL0.le κ N).symm
  have hℓN : ellj d L ℓ₀ N ^ 2 * θ ^ N = ℓ₀ ^ 2 * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) := by
    rw [ellj_sq, mul_assoc, pow_mul_pow_rpow hL0, rpow_neg_mul_nat hL0.le]
  have hEb : ∀ E : ℂ, ‖E‖ ≤ Cf * ‖b₀‖ * (θ ^ N * (1 / (msq * Fintype.card (Lam d L N))) +
      ellj d L ℓ₀ N ^ 2 * θ ^ N) →
      ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
        (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) := by
    intro E hE
    refine hE.trans ?_
    rw [hℓN, hθN]
    have hX1 : 0 ≤ (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) := by positivity
    have hX2 : 0 ≤ (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N)) := by positivity
    have hc : Cf * (1 + ℓ₀ ^ 2) ≤ C := by rw [hCdef]; nlinarith [mul_nonneg hKCf (sq_nonneg ℓ₀)]
    have hb0 : 0 ≤ ‖b₀‖ := norm_nonneg _
    have : Cf * ‖b₀‖ * ((L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N))) +
        ℓ₀ ^ 2 * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N))) ≤
        Cf * (1 + ℓ₀ ^ 2) * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) := by
      rw [mul_one_div]
      have := mul_nonneg (mul_nonneg hCf hb0) hX1
      have := mul_nonneg (mul_nonneg hCf hb0) hX2
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCf hb0) (sq_nonneg ℓ₀)) hX2]
    refine this.trans ?_
    gcongr
  have hC1 : K * Cf ≤ C := by rw [hCdef]; nlinarith [mul_nonneg hKCf (sq_nonneg ℓ₀)]
  have hC2 : 3 * K * Cf * ℓ₀ ^ 2 ≤ C := by rw [hCdef]; nlinarith [mul_nonneg hKCf (sq_nonneg ℓ₀)]
  have hb0 : 0 ≤ ‖b₀‖ := norm_nonneg _
  -- translation
  have htra : avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi a) =
      avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) := by
    have := avg_psibar_psi_diag_transl hmsq hN V₀ a 0; rwa [zero_add] at this
  have htrb : avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar b * psi b) =
      avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) := by
    have := avg_psibar_psi_diag_transl hmsq hN V₀ b 0; rwa [zero_add] at this
  -- `W_N(0)`
  have hWa : (∑ k ∈ range N, (Flow.covAt d L N msq k a a : ℂ)) =
      (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ) := by
    rw [sum_covAt_ofReal, sum_covAt_diag_eq_WN hmsq hN a]
  have hWb : (∑ k ∈ range N, (Flow.covAt d L N msq k b b : ℂ)) =
      (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ) := by
    rw [sum_covAt_ofReal, sum_covAt_diag_eq_WN hmsq hN b]
  have hWn := norm_sum_covAt_le hd hL2 hℓ₀ hC a a
  have hWn' := norm_sum_covAt_le hd hL2 hℓ₀ hC b b
  rw [hWa] at c3 hWn
  rw [hWb] at c4 hWn'
  refine ⟨?_, ?_⟩
  · obtain ⟨g1, g2, E, hE, hEq⟩ := onePt_alg hnl hlbar hu he hCf hb0
      (avg_two_a_eq' hd1 hL8 hN hmsq hC V₀ hl0 a b)
      (ε_ZtO_a_two V₀ (lbar : ℂ) a b hd1 hL8 hN hmsq hC) c1 c3 k1 k3 hWn hτ (by positivity)
    refine ⟨g1.trans (mul_le_mul_of_nonneg_right hC1 hb0),
      g2.trans (mul_le_mul_of_nonneg_right hC2 hb0), E, hEb E hE, ?_⟩
    rw [← htra]; exact hEq
  · obtain ⟨g1, g2, E, hE, hEq⟩ := onePt_alg hnl hlbar hu he hCf hb0
      (avg_two_b_eq' hd1 hL8 hN hmsq hC V₀ hl0 a b)
      (ε_ZtO_b_two V₀ (lbar : ℂ) a b hd1 hL8 hN hmsq hC) c2 c4 k2 k4 hWn' hτ (by positivity)
    refine ⟨g1.trans (mul_le_mul_of_nonneg_right hC1 hb0),
      g2.trans (mul_le_mul_of_nonneg_right hC2 hb0), E, hEb E hE, ?_⟩
    rw [← htrb]; exact hEq

/-- **`prop:1pt`, Tier 1** (see the module docstring). -/
theorem prop_1pt (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), 0 < lbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ) (x : Lam d L N), 1 ≤ N → 0 < msq → ‖b₀‖ ≤ lbar → x ≠ 0 →
        1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
        (‖lamA2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
          ‖gamA2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ C * ‖b₀‖ ∧
          ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
              (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
            avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
                (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
              gamA2 d L N msq (V₀c msq b₀) lbar x +
                (lamA2 d L N msq (V₀c msq b₀) lbar x * tau d L N msq + E) /
                  (1 + Suscept.utN d L N msq (V₀c msq b₀))) ∧
        (‖lamB2 d L N msq (V₀c msq b₀) lbar x - 1‖ ≤ C * ‖b₀‖ ∧
          ‖gamB2 d L N msq (V₀c msq b₀) lbar x -
              (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ C * ‖b₀‖ ∧
          ∃ E : ℂ, ‖E‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
              (L : ℝ) ^ (-(κ * N)) / (msq * Fintype.card (Lam d L N))) ∧
            avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
                (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) =
              gamB2 d L N msq (V₀c msq b₀) lbar x +
                (lamB2 d L N msq (V₀c msq b₀) lbar x * tau d L N msq + E) /
                  (1 + Suscept.utN d L N msq (V₀c msq b₀))) := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setup hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H⟩ := H L hL hLodd
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hKℓ' => ?_⟩
  obtain ⟨V₀c, lbar, Cf, κ, HF⟩ := H A hA ℓ₀ hℓ₀ hKℓ'
  obtain ⟨C, hC, h⟩ := prop_1pt_of hd HF
  exact ⟨V₀c, lbar, C, κ, HF.lbar_pos, hC, HF.κ_pos, HF.hb, h⟩

end

end PtCorr
