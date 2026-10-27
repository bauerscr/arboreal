import Spin2.Cont.ContEqS2

set_option autoImplicit false

/-!
# Per-`M` copies of `eqs_shortX`, `eqs_shortBound`, `eqs_limitAnn` with `3 ≤ N₀`

Verbatim copies of the bodies of `Spin2/Cont/ContEqS2.lean`; the only change is that the statements
also export `3 ≤ N₀` (the horizon threshold comes from `eqs_allB`, which has `3 ≤ N₀`). This is
needed to construct admissible sequences (`ClAdm`) from `N₀` on in `Spin2/Final/Arboreal.lean`.
-/

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- `eqs_shortX` with `3 ≤ N₀`. -/
theorem arb_eqs_shortX (M : MasterFacts L) :
    ∃ (g₀ K Kc : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 < Kc ∧ 3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR, ∀ x : Lam 2 L N, x ≠ 0 →
      0 < Real.log (1 / (eucl x / (L : ℝ) ^ N)) ∧
      (∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
        jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
        |Pconn L N (1 / b) x / thetaEpsSq βR b -
            (betaJ R m b (b - m) (min jp (N - 2)) / βR) ^ (2 / 3 : ℝ)| ≤
          K * (betaJ R m b (b - m) (min jp (N - 2)) / βR) ^ (2 / 3 : ℝ) /
            betaJ R m b (b - m) (min jp (N - 2)) ∧
        |betaJ R m b (b - m) (min jp (N - 2)) -
            betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N))| ≤
          Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))))) ∧
      (2 * (Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))))) ≤
          betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) →
        |Pconn L N (1 / b) x / thetaEpsSq βR b -
            (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) / βR) ^ (2 / 3 : ℝ)| ≤
          (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) / βR) ^ (2 / 3 : ℝ) *
            ((Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N)))) + 2 * K) /
              (betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N))))) ∧
      Pconn L N (1 / b) x / thetaEpsSq βR b ≤
        (1 + |K|) * ((betaOne * Real.log (1 / (eucl x / (L : ℝ) ^ N)) +
          Kc * (1 + βR + Real.log (1 + Real.log (1 / (eucl x / (L : ℝ) ^ N))))) / βR) ^
            (2 / 3 : ℝ) := by
  obtain ⟨g₀, K, N₀, hg, hg1, hN₀, hF⟩ := eqs_allB M
  have hβ := ct_betaL_pos M.ct_L2
  have hb1 := betaOne_pos
  set β := betaL L with hβd
  set a := M.ctA
  set E := M.ctE
  set c := a * |Real.log (2 * a)|
  have ha := M.ctA_nonneg
  have hE := M.ctE_nonneg
  have hc : 0 ≤ c := mul_nonneg ha (abs_nonneg _)
  set Kc := 2 * β + 5 + E + 2 * a * (betaOne + E + c) + 10 * a + a with hKcd
  have hKc : 0 < Kc := by positivity
  refine ⟨g₀, K, Kc, N₀, hg, hKc, hN₀, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb x hx
  obtain ⟨hmR, -, hB, -⟩ := hF N R hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy
  obtain ⟨hb0, hD, hPb, hgl⟩ := hB b hb
  obtain ⟨jp, hjp, hj1, hj2, hPj⟩ := hPb x hx
  obtain ⟨hℓ0, hlam0⟩ := cx_lam_pos hx
  set k := min jp (N - 2) with hkd
  have hkN : k ≤ N - 2 := min_le_right _ _
  have hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have := one_div_pos.2 hβR
    have h0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
    linarith
  have hT : 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1 ≤ 5 * βR := by
    have hg0 : 0 < 1 / βR / 5 := by positivity
    rw [div_le_iff₀ (hg0.trans_le hgl)]
    have e : 5 * βR * (1 / βR / 5) = 1 := by field_simp
    nlinarith only [hgl, e, hβR]
  have hX : 0 < betaJ R m b (b - m) k := one_div_pos.2 (hD k hkN).1
  have core := cs_core (P := Pconn L N (1 / b) x) (K := K) hβR hb0 hX rfl rfl hPj
  set lam := Real.log (1 / (eucl x / (L : ℝ) ^ N)) with hlamd
  -- `n = N − 2 − k` vs `λ`
  have hjk : ((N - 2 - k : ℕ) : ℝ) * β ≤ betaOne * lam ∧
      |((N - 2 - k : ℕ) : ℝ) * β - betaOne * lam| ≤ 2 * β := by
    rcases le_or_gt jp (N - 2) with hjl | hjl
    · have hk : k = jp := min_eq_left hjl
      rw [hk]
      exact cs_jphys M.ct_L2 hjp hjl (by omega)
    · have hk : k = N - 2 := min_eq_right hjl.le
      have h0 : N - 2 - k = 0 := by omega
      have htop := cx_jphys_top M.ct_L2 hjp (by omega) (by omega)
      rw [← hβd, ← hlamd] at htop
      rw [h0]
      have : 0 ≤ betaOne * lam := mul_nonneg hb1.le hlam0.le
      push_cast
      rw [zero_mul, zero_sub, abs_neg, abs_of_nonneg this]
      constructor <;> linarith
  -- `β_k` vs `β₁λ`
  have hBJ : |betaJ R m b (b - m) k - betaOne * lam| ≤ Kc * (1 + βR + Real.log (1 + lam)) := by
    have hl0 := hlam0.le
    have H := M.ct_beta_scale R hP hi0 hRℓ hRA hRρ (by omega) hmR hm1 hD hT k hkN
    obtain ⟨j1, j2⟩ := hjk
    set x' := ((N - 2 - k : ℕ) : ℝ) * β
    have hx0 : 0 ≤ x' := by positivity
    have hL := ct_log_lin (x := x') (s := betaOne) (t := lam) (D := 5 * βR + E + c)
      (by positivity) hb1.le hl0 hx0 (by nlinarith only [j1, hb1, hl0])
    rw [show x' + (5 * βR + E + c) = x' + (5 * βR + E) + c by ring] at hL
    have hL' := mul_le_mul_of_nonneg_left hL ha
    have hlog : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
    have t : |betaJ R m b (b - m) k - betaOne * lam| ≤
        |betaJ R m b (b - m) k - x'| + 2 * β := by
      have := abs_sub_le (betaJ R m b (b - m) k) x' (betaOne * lam)
      linarith
    have hprod : 0 ≤ 2 * a * (betaOne + E + c) := by positivity
    have k1 : (5 + 10 * a) * βR ≤ Kc * βR := mul_le_mul_of_nonneg_right (by linarith) hβR.le
    have k2 : a * Real.log (1 + lam) ≤ Kc * Real.log (1 + lam) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog
    have e : a * (2 * (betaOne + (5 * βR + E + c)) + Real.log (1 + lam)) =
        2 * a * (betaOne + E + c) + 10 * a * βR + a * Real.log (1 + lam) := by ring
    have e2 : Kc * (1 + βR + Real.log (1 + lam)) = Kc + Kc * βR + Kc * Real.log (1 + lam) := by
      ring
    linarith
  refine ⟨hlam0, ⟨jp, hjp, hj1, hj2, core.1, hBJ⟩, fun h2 => ?_, ?_⟩
  · have hpos : 0 < betaOne * lam := mul_pos hb1 hlam0
    exact core.2 _ _ hpos hBJ h2
  · -- (C)
    set X := (betaJ R m b (b - m) k / βR) ^ (2 / 3 : ℝ) with hXd
    have hX0 : 0 ≤ X := by positivity
    have hβk1 : 1 ≤ betaJ R m b (b - m) k := by
      obtain ⟨hg0, hgε, -⟩ := hD k hkN
      unfold betaJ
      rw [le_one_div one_pos hg0, div_one]
      exact hgε.trans M.eps_le
    have h1 := (abs_le.1 core.1).2
    have h2 : K * X / betaJ R m b (b - m) k ≤ |K| * X := by
      rw [div_le_iff₀ hX]
      have : K * X ≤ |K| * X := mul_le_mul_of_nonneg_right (le_abs_self K) hX0
      have : |K| * X ≤ |K| * X * betaJ R m b (b - m) k :=
        le_mul_of_one_le_right (by positivity) hβk1
      linarith
    have h3 : X ≤ ((betaOne * lam + Kc * (1 + βR + Real.log (1 + lam))) / βR) ^ (2 / 3 : ℝ) := by
      refine Real.rpow_le_rpow (div_nonneg hX.le hβR.le) ?_ (by norm_num)
      exact div_le_div_of_nonneg_right (by linarith [(abs_le.1 hBJ).2]) hβR.le
    have h4 : (1 + |K|) * X ≤ (1 + |K|) *
        ((betaOne * lam + Kc * (1 + βR + Real.log (1 + lam))) / βR) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e : (1 + |K|) * X = X + |K| * X := by ring
    unfold thetaEpsSq
    linarith

set_option maxHeartbeats 1000000 in
/-- `eqs_shortBound` with `3 ≤ N₀`. -/
theorem arb_eqs_shortBound (M : MasterFacts L) :
    ∃ (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 3 ≤ N₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ P ℓ : ℝ, CsPtX M N₀ βR P ℓ → δ ≤ ℓ → P ≤ C) ∧
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
      (∀ P ℓ : ℝ, CsPtX M N₀ βR P ℓ → ℓ ≤ δ₀ → |P - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ) ∧
      ∀ (Pk ℓk : ℕ → ℝ) (G ℓ : ℝ), 0 < ℓ → ℓ < δ₀ → Tendsto Pk atTop (𝓝 G) →
        Tendsto ℓk atTop (𝓝 ℓ) → (∀ᶠ k in atTop, CsPtX M N₀ βR (Pk k) (ℓk k)) →
        |G - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ := by
  obtain ⟨g₀, K, Kc, N₀, hg, hKc, hN₀, hF⟩ := arb_eqs_shortX M
  refine ⟨g₀, N₀, hg, hN₀, fun βR hβR hy => ⟨fun δ hδ => ?_, ?_⟩⟩
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

/-- `thm_limit_of_equiAnn` for a given `M`. -/
theorem arb_eqs_limitAnn (M : MasterFacts L) :
    ∃ (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 3 ≤ N₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∀ r₀ : ℝ, 0 ≤ r₀ → ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), ClAdm M N₀ βR R m b →
      (∀ r > r₀, ClEquiOn (clF L βR b) r) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ,
      ContinuousOn G {x | r₀ < dist x 0} ∧
      (∀ K ⊆ {x : UnitAddTorus (Fin 2) | r₀ < dist x 0}, IsCompact K →
        TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop K) ∧
      (∀ x, r₀ < ‖x‖ → 0 ≤ G x) ∧
      (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, r₀ < ‖x‖ → G (clSgn τ s x) = G x) ∧
      (∀ δ > r₀, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
      (∀ x, r₀ < ‖x‖ → torusNorm x < δ₀ →
        |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  have hL2 : 2 ≤ L := M.ct_L2
  obtain ⟨g₀, N₀, hg, hN₀, hF⟩ := arb_eqs_shortBound M
  refine ⟨g₀, N₀, hg, hN₀, fun βR hβR hy => ?_⟩
  obtain ⟨hB, δ₀, K', hδ₀, hδ₁, hK', -, hlim⟩ := hF βR hβR hy
  refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun r₀ hr₀ R m b hA hE => ?_⟩
  have hbd := t6_bdd hL2 hβR hA hB
  obtain ⟨φ, hφ, G, hGc, -, hGu⟩ := ascoli_asymp_exists_subseq_annulus (0 : UnitAddTorus (Fin 2))
    r₀ (clF L βR b) (fun r hr => hbd r (lt_of_le_of_lt hr₀ hr)) (fun r hr => hE r hr)
  have hpt : ∀ x : UnitAddTorus (Fin 2), r₀ < ‖x‖ →
      Tendsto (fun k => clF L βR b (φ k) x) atTop (𝓝 (G x)) := by
    intro x hx
    have hK : ({x} : Set (UnitAddTorus (Fin 2))) ⊆ {x | r₀ < dist x 0} := by
      intro y hy; rw [Set.mem_singleton_iff.1 hy]; show r₀ < dist x 0; rwa [dist_zero_right]
    exact (hGu _ hK isCompact_singleton).tendsto_at (Set.mem_singleton x)
  have hne : ∀ x : UnitAddTorus (Fin 2), r₀ < ‖x‖ → x ≠ 0 := fun x hx h0 => by
    rw [h0, norm_zero] at hx; linarith
  refine ⟨φ, hφ, G, hGc, hGu, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ge_of_tendsto (hpt x hx) ?_
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N₀)] with k hk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb0⟩ := hA (φ k) hk
    exact t6_clF_nonneg hβR hb0 x
  · intro τ s x hx
    have hr : r₀ < (r₀ + ‖x‖) / 2 := by linarith
    exact ascoli_asymp_limit_eq_of_tendsto_sub hφ (hpt x hx)
      (hpt _ (by rw [norm_clSgn]; exact hx))
      (t6_sym_tendsto_on hL2 (hE _ hr) τ s (by linarith))
  · intro δ hδ
    obtain ⟨C, hC⟩ := hbd δ (lt_of_le_of_lt hr₀ hδ)
    refine ⟨C, fun x hx => ?_⟩
    refine le_of_tendsto (hpt x (lt_of_lt_of_le hδ hx)) (Eventually.of_forall fun k => ?_)
    exact (le_abs_self _).trans (hC _ x (by rwa [dist_zero_right]))
  · intro x hx hxδ
    exact t6_short_at hL2 hA hlim hφ (hne x hx) hxδ (hpt x hx)

end

end Spin2
