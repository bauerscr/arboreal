import Spin2.Cont.ContShortX
import Spin2.Multiscale.ConnSym
import Cont.LatEmb
import Cont.AscoliStep

-- Merged from `Spin2/ContBound.lean` (phase 3).
section

/-!
# A uniform bound on `ϑ_ε^{-2}P_ε` away from the origin (for the Ascoli step)

* **`thm_bound_eps`**: for fixed `β_R` and `δ > 0` there is `C` (depending on `β_R`, `δ`, `L`) with
  `ϑ_ε^{-2}P_ε(x) ≤ C` for every sample (`CsPtX`: all `N ≥ N₀`, all `b` in the bracket, all
  `x ≠ 0`) with `|x|/L^N ≥ δ`. (From `thm_short_epsX` (C):
  `ϑ_ε^{-2}P_ε(x) ≤ (1 + |K|)((β₁λ + K_c(1 + β_R + log(1 + λ)))/β_R)^{2/3}`, `λ = log(1/ℓ)`.)

A bound uniform over **all** `x ≠ 0` and `N` is false: at `|x| = 1`, `λ = N log L` and
`ϑ_ε^{-2}P_ε(x) ≈ (β₁N log L/β_R)^{2/3} → ∞`. The norm comparison `|x|_∞ ≤ |x| ≤ √2|x|_∞` is
`cx_supNorm_eucl` (`Spin2/Cont/ContShortX`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Filter Topology

/-- **The bound `ϑ_ε^{-2}P_ε(x) ≤ C(δ)` for `|x|/L^N ≥ δ`**, uniformly in `N ≥ N₀`, `b` in the
bracket and `x`. Constants `M, g₀, N₀` depend on `L` only; `C` on `β_R`, `δ`, `L`. -/
theorem thm_bound_eps : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ P ℓ : ℝ, CsPtX M N₀ βR P ℓ → δ ≤ ℓ → P ≤ C := by
  obtain ⟨L₀, h⟩ := thm_short_epsX
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, Kc, N₀, hg, hKc, hF⟩ := h L hL
  refine ⟨M, g₀, N₀, hg, fun βR hβR hy δ hδ => ?_⟩
  set Λ := max (Real.log (1 / δ)) 0 with hΛd
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hb1 := betaOne_pos
  refine ⟨(1 + |K|) * ((betaOne * Λ + Kc * (1 + βR + Real.log (1 + Λ))) / βR) ^ (2 / 3 : ℝ),
    fun P ℓ hP hℓ => ?_⟩
  obtain ⟨N, hN, R, _, _, hPc, hi0, hRℓ, hRA, hRρ, m, b, hm, hmass, hb, x, hx, rfl, rfl⟩ := hP
  obtain ⟨hlam0, -, -, hC⟩ := hF N R hPc hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb x hx
  refine hC.trans ?_
  set lam := Real.log (1 / (eucl x / (L : ℝ) ^ N)) with hlamd
  have hlΛ : lam ≤ Λ := by
    refine le_trans ?_ (le_max_left _ _)
    rw [hlamd, one_div, one_div, Real.log_inv, Real.log_inv, neg_le_neg_iff]
    exact Real.log_le_log hδ hℓ
  have hlog : Real.log (1 + lam) ≤ Real.log (1 + Λ) := Real.log_le_log (by linarith) (by linarith)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.rpow_le_rpow ?_ ?_ (by norm_num)
  · have : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
    have : 0 ≤ Kc * (1 + βR + Real.log (1 + lam)) := mul_nonneg hKc.le (by linarith)
    exact div_nonneg (by nlinarith) hβR.le
  · refine div_le_div_of_nonneg_right ?_ hβR.le
    have := mul_le_mul_of_nonneg_left hlΛ hb1.le
    have := mul_le_mul_of_nonneg_left (show 1 + βR + Real.log (1 + lam) ≤ 1 + βR + Real.log (1 + Λ)
      by linarith) hKc.le
    linarith

end

end Spin2

end

/-!
# B3, T6 (c): subsequential continuum limits of `ϑ_ε^{-2}P_ε`, given asymptotic equicontinuity

`clF L βR b N x := Pconn L N (1/b_N) (latPtN L N x) / thetaEpsSq βR b_N` on `𝕋²`
(translation invariance is built in: `P_ε(x) = P[0 ↔ x]`).

* `t6_short_bound`: `thm_bound_eps` and `thm_short_eps_logX` **for one master construction `M`**
  (the two theorems have separate existentials; this restates both from `thm_short_epsX`).
* `ClAdm M N₀ βR R m b`: for `N ≥ N₀` the master parameters `R N`, a mass `m_N` in the window and
  `b_N > 0` in the bracket `ctBracket M (R N) m_N βR`.
* `ClEqui f`: asymptotic equicontinuity on every `{|x| ≥ r}` (the hypothesis of
  `ascoli_asymp_exists_subseq_torus`). **This is the open input of B3** (task T6 (a)/(b)).
* **`thm_limit_of_equi`**: under `ClAdm` and `ClEqui (clF L βR b)` there is a subsequence
  converging uniformly on compacts of `𝕋² ∖ {0}` to a `G` continuous on `𝕋² ∖ {0}`, with
  `G ≥ 0`, point-group invariance `G ∘ clSgn τ s = G`, the bound `G ≤ C(δ)` on `{‖x‖ ≥ δ}` and the
  short-distance law `|G(x) − (β₁λ/β_R)^{2/3}| ≤ K'(β₁λ/β_R)^{2/3}(log λ)/λ`, `λ = log(1/|x|)`,
  for `|x| < δ₀`.
* Unconditional ingredients: `t6_bdd` (uniform boundedness on `{‖x‖ ≥ r}`, all `N`),
  `t6_eucl_tendsto` (`|latPtN x|/L^N → |x|`), `t6_sym_tendsto` (`f_N(σx) − f_N(x) → 0` under
  `ClEqui`).
-/

set_option autoImplicit false

namespace Spin2

open Step Step2 PtCorr2 Cont

noncomputable section

open Filter Topology

set_option maxHeartbeats 1000000 in
/-- `thm_bound_eps` and `thm_short_eps_logX` for **one** master construction `M` (copies of the
two proofs from `thm_short_epsX`). -/
theorem t6_short_bound : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ P ℓ : ℝ, CsPtX M N₀ βR P ℓ → δ ≤ ℓ → P ≤ C) ∧
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
      (∀ P ℓ : ℝ, CsPtX M N₀ βR P ℓ → ℓ ≤ δ₀ → |P - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ) ∧
      ∀ (Pk ℓk : ℕ → ℝ) (G ℓ : ℝ), 0 < ℓ → ℓ < δ₀ → Tendsto Pk atTop (𝓝 G) →
        Tendsto ℓk atTop (𝓝 ℓ) → (∀ᶠ k in atTop, CsPtX M N₀ βR (Pk k) (ℓk k)) →
        |G - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ := by
  obtain ⟨L₀, h⟩ := thm_short_epsX
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, Kc, N₀, hg, hKc, hF⟩ := h L hL
  refine ⟨M, g₀, N₀, hg, fun βR hβR hy => ⟨fun δ hδ => ?_, ?_⟩⟩
  · set Λ := max (Real.log (1 / δ)) 0 with hΛd
    have hΛ0 : 0 ≤ Λ := le_max_right _ _
    have hb1 := betaOne_pos
    refine ⟨(1 + |K|) * ((betaOne * Λ + Kc * (1 + βR + Real.log (1 + Λ))) / βR) ^ (2 / 3 : ℝ),
      fun P ℓ hP hℓ => ?_⟩
    obtain ⟨N, hN, R, _, _, hPc, hi0, hRℓ, hRA, hRρ, m, b, hm, hmass, hb, x, hx, rfl, rfl⟩ := hP
    obtain ⟨hlam0, -, -, hC⟩ := hF N R hPc hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb x hx
    refine hC.trans ?_
    set lam := Real.log (1 / (eucl x / (L : ℝ) ^ N)) with hlamd
    have hlΛ : lam ≤ Λ := by
      refine le_trans ?_ (le_max_left _ _)
      rw [hlamd, one_div, one_div, Real.log_inv, Real.log_inv, neg_le_neg_iff]
      exact Real.log_le_log hδ hℓ
    have hlog : Real.log (1 + lam) ≤ Real.log (1 + Λ) := Real.log_le_log (by linarith) (by linarith)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.rpow_le_rpow ?_ ?_ (by norm_num)
    · have : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
      have : 0 ≤ Kc * (1 + βR + Real.log (1 + lam)) := mul_nonneg hKc.le (by linarith)
      exact div_nonneg (by nlinarith) hβR.le
    · refine div_le_div_of_nonneg_right ?_ hβR.le
      have := mul_le_mul_of_nonneg_left hlΛ hb1.le
      have := mul_le_mul_of_nonneg_left (show 1 + βR + Real.log (1 + lam) ≤ 1 + βR + Real.log (1 + Λ)
        by linarith) hKc.le
      linarith
  · have hb1 := betaOne_pos
    have hev : ∀ᶠ y in atTop, (1 + βR + Real.log y) / y ≤ betaOne / (4 * Kc) :=
      (ct_rate_tendsto (1 + βR)).eventually (ge_mem_nhds (by positivity))
    obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 hev
    set l₀ := max (max y₀ 1) (Real.exp 1) with hl₀d
    have hl₀1 : 1 ≤ l₀ := (le_max_right _ _).trans (le_max_left _ _)
    have hl₀e : Real.exp 1 ≤ l₀ := le_max_right _ _
    have hl₀y : y₀ ≤ l₀ := (le_max_left _ _).trans (le_max_left _ _)
    set K' := (Kc * (3 + βR) + 2 * |K|) / betaOne with hK'd
    have hK' : 0 ≤ K' := by positivity
    -- the two facts at `λ ≥ λ₀`
    have hlam : ∀ lam : ℝ, l₀ ≤ lam →
        2 * (Kc * (1 + βR + Real.log (1 + lam))) ≤ betaOne * lam ∧
        (Kc * (1 + βR + Real.log (1 + lam)) + 2 * K) / (betaOne * lam) ≤
          K' * (Real.log lam / lam) := by
      intro lam hl
      have hl1 : 1 ≤ lam := hl₀1.trans hl
      have hl0 : 0 < lam := by linarith
      have hq := hy₀ (1 + lam) (by linarith)
      rw [div_le_div_iff₀ (by linarith) (by positivity)] at hq
      have hlg : 1 ≤ Real.log lam := (Real.le_log_iff_exp_le hl0).2 (hl₀e.trans hl)
      have hl2 : Real.log (1 + lam) ≤ 2 * Real.log lam := by
        have h1 : Real.log (1 + lam) ≤ Real.log (2 * lam) := Real.log_le_log (by linarith) (by linarith)
        rw [Real.log_mul (by norm_num) hl0.ne'] at h1
        have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        linarith
      refine ⟨by nlinarith only [hq, hl1, hb1], ?_⟩
      rw [div_le_iff₀ (by positivity)]
      have e : K' * (Real.log lam / lam) * (betaOne * lam) =
          (Kc * (3 + βR) + 2 * |K|) * Real.log lam := by
        rw [hK'd]; field_simp
      rw [e]
      have hlog0 : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
      have t1 : Kc * (1 + βR) ≤ Kc * (1 + βR) * Real.log lam :=
        le_mul_of_one_le_right (by positivity) hlg
      have t2 : Kc * Real.log (1 + lam) ≤ Kc * (2 * Real.log lam) :=
        mul_le_mul_of_nonneg_left hl2 hKc.le
      have t3 : 2 * K ≤ 2 * |K| * Real.log lam := by
        have := le_mul_of_one_le_right (show 0 ≤ 2 * |K| by positivity) hlg
        have := le_abs_self K
        linarith
      nlinarith only [t1, t2, t3]
    -- the pointwise bound
    have hpt : ∀ P ℓ : ℝ, CsPtX M N₀ βR P ℓ → ℓ ≤ Real.exp (-l₀) →
        |P - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ := by
      intro P ℓ hP hℓ
      obtain ⟨N, hN, R, _, _, hPc, hi0, hRℓ, hRA, hRρ, m, b, hm, hmass, hb, x, hx, rfl, rfl⟩ :=
        hP
      have hℓ0 : 0 < eucl x / (L : ℝ) ^ N := by
        have := cs_one_le_eucl hx
        have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by have := M.ct_L2; omega)
        positivity
      set lam := Real.log (1 / (eucl x / (L : ℝ) ^ N)) with hlamd
      have hll : l₀ ≤ lam := by
        have h1 := Real.log_le_log hℓ0 hℓ
        rw [Real.log_exp] at h1
        rw [hlamd, one_div, Real.log_inv]; linarith
      obtain ⟨h2, h3⟩ := hlam lam hll
      have hB := (hF N R hPc hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb x hx).2.2.1 h2
      rw [← hlamd] at hB
      have hA0 : 0 ≤ csA βR (eucl x / (L : ℝ) ^ N) := by
        unfold csA; rw [← hlamd]
        exact Real.rpow_nonneg (div_nonneg (mul_nonneg hb1.le (by linarith)) hβR.le) _
      unfold csRate
      rw [← hlamd]
      refine hB.trans ?_
      have := mul_le_mul_of_nonneg_left h3 hA0
      unfold csA at this ⊢
      rw [← hlamd] at this ⊢
      linarith
    refine ⟨Real.exp (-l₀), K', Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith), hK', hpt, ?_⟩
    intro Pk ℓk G ℓ hℓ0 hℓδ hPk hℓk hev'
    have hlamℓ : l₀ < Real.log (1 / ℓ) := by
      have h1 := Real.log_lt_log hℓ0 hℓδ
      rw [Real.log_exp] at h1
      rw [one_div, Real.log_inv]; linarith
    have hne : Real.log (1 / ℓ) ≠ 0 := by linarith
    have h1 : ContinuousAt (fun t : ℝ => 1 / t) ℓ := continuousAt_const.div continuousAt_id hℓ0.ne'
    have hlog : ContinuousAt (fun t : ℝ => Real.log (1 / t)) ℓ := h1.log (one_div_pos.2 hℓ0).ne'
    have hA : ContinuousAt (fun t => csA βR t) ℓ :=
      ((continuousAt_const.mul hlog).div_const βR).rpow_const (Or.inr (by norm_num))
    have hR : ContinuousAt (fun t => csRate t) ℓ := (hlog.log hne).div hlog hne
    have hB : ContinuousAt (fun t => K' * csA βR t * csRate t) ℓ :=
      (continuousAt_const.mul hA).mul hR
    have hT := ((hPk.sub (hA.tendsto.comp hℓk)).abs.sub (hB.tendsto.comp hℓk))
    have hle : ∀ᶠ k in atTop, |Pk k - csA βR (ℓk k)| - K' * csA βR (ℓk k) * csRate (ℓk k) ≤ 0 := by
      filter_upwards [hev', hℓk.eventually (ge_mem_nhds hℓδ)] with k hk hk2
      have := hpt _ _ hk hk2
      linarith
    have := le_of_tendsto hT hle
    linarith

end

end Spin2
