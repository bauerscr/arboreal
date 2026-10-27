import PtCorr.OnePt

/-!
# `lem:2pt`, Case (2): the formula `e:2pt-b` (Tier 1: finite `N`, `m² > 0`)

For `x ≠ 0`, the pair `(a, b) = (ctr, ctr + x)`, `r = |x|_∞`, `W = W_N(x)`, and the finite-`N`
point couplings `λ_a = lamA2 … x`, `λ_b = lamB2 … x`, `γ_a = gamA2 … x`, `γ_b = gamB2 … x`
(`PtCorr.OnePt`), `lem_2pt_two` states (for `m² > 0`, `1 + ũ ≠ 0`):

`⟨ψ̄_0ψ_0 ψ̄_xψ_x⟩ = -λ_aλ_b W² + γ_aγ_b + (-2λ_aλ_b W + λ_aγ_b + λ_bγ_a) τ/(1+ũ)
   + E₁ + E₂/(1+ũ)`,

`|E₁| ≤ C|b₀| r^{-(2(d-2)+κ)}`,
`|E₂| ≤ C|b₀| (L^{-(d-2+κ)N} + (L^{-κN} + r^{-(d-2+κ)})/(m²|Λ|))`.

Proof: `⟨ψ̄_aψ_aψ̄_bψ_b⟩ = ε(Z̃^obs_ab)/(l₀²(1+ũ))` (`avg_two_ab_eq'`), the component formula
`ε_ZtO_ab_two`, the summed recursions of `PtCorr.FlowTwo` (`q_N = -λ_aλ_b W² + O(…)`,
`η_N = -2λ_aλ_b W + O(…)`, `r_{x,N} = O(…)`, `γ_{x,N} = O(1)`), `kTwo_bounds`, the conversions
of `PtCorr.Conv`, and translation invariance (`avg_four_transl`).

**Deviations (Tier 1).**
* `λ_∞²`, `γ_∞²` are replaced by the products `λ_aλ_b`, `γ_aγ_b` of the finite-`N` couplings at
  the two points.
* Placement of the error terms: `E₁` (the error of the `q_N`-sum) is outside
  `1/(1+ũ)`, all other errors (`η`, `r`, `λ̃ - λ`, and the constant `k_ab` of `K_N(Λ)`, which
  contributes `O(b₀L^{-(d-2+κ)N})`) come with the factor `1/(1+ũ)`, since they arise from
  `ε(Z̃^obs_ab)/(1+ũ)` with no factor `(1+ũ)`.  The paper places `O(b₀L^{-(d-2+κ)N})` outside.
  The two agree when `|ũ|` is small.
* The error `E₂` carries `r^{-(d-2+κ)}/(m²|Λ|)` (from `η`, `r` times `τ`), as in the task
  statement.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs FRD

/-- The algebra of `e:2pt-b`. -/
theorem twoPt_alg {l₀ u av εG q ga gb la lb lta ltb η ra rb k τ W : ℂ} {lbar : ℝ}
    (hl : ‖l₀‖ = lbar) (hlbar : 0 < lbar) (hu : 1 + u ≠ 0)
    (havg : av = εG / (l₀ ^ 2 * (1 + u)))
    (hεG : εG = (q + ga * gb) * (1 + u) + (η - (ra + rb) + lta * gb + ltb * ga) * τ + k) :
    ∃ E₁ E₂ : ℂ, ‖E₁‖ = ‖q + la * lb * W ^ 2‖ / lbar ^ 2 ∧
      ‖E₂‖ ≤ ((‖η + 2 * (la * lb) * W‖ + ‖ra‖ + ‖rb‖ + ‖lta - la‖ * ‖gb‖ +
          ‖ltb - lb‖ * ‖ga‖) * ‖τ‖ + ‖k‖) / lbar ^ 2 ∧
      av = -(la / l₀) * (lb / l₀) * W ^ 2 + (ga / l₀) * (gb / l₀) +
        (-2 * (la / l₀) * (lb / l₀) * W + (la / l₀) * (gb / l₀) + (lb / l₀) * (ga / l₀)) * τ /
          (1 + u) + E₁ + E₂ / (1 + u) := by
  have hl0 : l₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hl; linarith
  refine ⟨(q + la * lb * W ^ 2) / l₀ ^ 2,
    ((η + 2 * (la * lb) * W - (ra + rb) + (lta - la) * gb + (ltb - lb) * ga) * τ + k) / l₀ ^ 2,
    by rw [norm_div, norm_pow, hl], ?_, ?_⟩
  · rw [norm_div, norm_pow, hl]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 := norm_add_le (η + 2 * (la * lb) * W - (ra + rb) + (lta - la) * gb) ((ltb - lb) * ga)
    have h2 := norm_add_le (η + 2 * (la * lb) * W - (ra + rb)) ((lta - la) * gb)
    have h3 := norm_sub_le (η + 2 * (la * lb) * W) (ra + rb)
    have h4 := norm_add_le ra rb
    rw [norm_mul] at h1 h2
    have hP : ‖η + 2 * (la * lb) * W - (ra + rb) + (lta - la) * gb + (ltb - lb) * ga‖ ≤
        ‖η + 2 * (la * lb) * W‖ + ‖ra‖ + ‖rb‖ + ‖lta - la‖ * ‖gb‖ + ‖ltb - lb‖ * ‖ga‖ := by
      linarith
    have h5 := norm_add_le ((η + 2 * (la * lb) * W - (ra + rb) + (lta - la) * gb +
      (ltb - lb) * ga) * τ) k
    rw [norm_mul] at h5
    have h6 := mul_le_mul_of_nonneg_right hP (norm_nonneg τ)
    linarith
  · rw [havg, hεG]
    field_simp
    ring

theorem three_terms {a1 a2 a3 Y1 Y2 Y3 T M : ℝ} (hY1 : 0 ≤ Y1) (hY2 : 0 ≤ Y2) (hY3 : 0 ≤ Y3)
    (hT : 0 ≤ T) (h1 : a1 ≤ M) (h2 : a2 ≤ M) (h3 : a3 ≤ M) :
    a1 * Y1 + a2 * Y2 * T + a3 * Y3 * T ≤ M * (Y1 + (Y2 + Y3) * T) := by
  nlinarith [mul_le_mul_of_nonneg_right h1 hY1, mul_le_mul_of_nonneg_right h2 (mul_nonneg hY2 hT),
    mul_le_mul_of_nonneg_right h3 (mul_nonneg hY3 hT)]

variable {d : ℕ}

set_option maxHeartbeats 2000000 in
/-- **`lem:2pt`, Case (2), `e:2pt-b`, Tier 1, for a given flow** `V₀c` with `FlowData`
(see `lem_2pt_two`). -/
theorem lem_2pt_two_of (hd : 3 ≤ d) {L : ℕ} [NeZero L] {A ℓ₀ lbar Cf κ : ℝ}
    {V₀c : ℝ → ℂ → Vcoup} (HF : FlowData d L A ℓ₀ V₀c lbar Cf κ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ) (x : Lam d L N), 1 ≤ N → 0 < msq → ‖b₀‖ ≤ lbar → x ≠ 0 →
        1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
        ∃ E₁ E₂ : ℂ,
          ‖E₁‖ ≤ C * ‖b₀‖ * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) ∧
          ‖E₂‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
            ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) /
              (msq * Fintype.card (Lam d L N))) ∧
          avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
              (psibar (0 : Lam d L N) * psi (0 : Lam d L N) * (psibar x * psi x)) =
            -lamA2 d L N msq (V₀c msq b₀) lbar x * lamB2 d L N msq (V₀c msq b₀) lbar x *
                (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) ^ 2 +
              gamA2 d L N msq (V₀c msq b₀) lbar x * gamB2 d L N msq (V₀c msq b₀) lbar x +
              (-2 * lamA2 d L N msq (V₀c msq b₀) lbar x * lamB2 d L N msq (V₀c msq b₀) lbar x *
                  (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
                lamA2 d L N msq (V₀c msq b₀) lbar x * gamB2 d L N msq (V₀c msq b₀) lbar x +
                lamB2 d L N msq (V₀c msq b₀) lbar x * gamA2 d L N msq (V₀c msq b₀) lbar x) *
                tau d L N msq / (1 + Suscept.utN d L N msq (V₀c msq b₀)) +
              E₁ + E₂ / (1 + Suscept.utN d L N msq (V₀c msq b₀)) := by
  obtain ⟨Cs, hCs, hcore⟩ := flowTwo_core hd
  have hL8 := HF.hL8
  have hA1 := HF.hA1
  have hℓ₀ := HF.hℓ₀
  have hlbar := HF.lbar_pos
  have hCf := HF.C_nonneg
  have hκ := HF.κ_pos
  have hmain := HF.two
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hL2 : 2 ≤ L := by
    have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL0 : (0 : ℝ) < L := Lr_pos
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  set θ : ℝ := (L : ℝ) ^ (-κ) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  set eb := Cf * lbar * lbar with heb_def
  have heb0 : 0 ≤ eb := by positivity
  set K := KTwo Cs θ lbar eb with hKdef
  have hK0 : 0 ≤ K := KTwo_nonneg hCs hθ1 hlbar.le heb0
  set Gb := K * eb * ℓ₀ ^ 2 + (lbar + K * eb) * (2 * ℓ₀ ^ 2) with hGb
  have hGb0 : 0 ≤ Gb := by positivity
  set Lc2 : ℝ := (L : ℝ) ^ ((d : ℝ) - 2 + κ) with hLc2
  set Lc4 : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2) + κ) with hLc4
  set C1 := K * Cf / lbar * (ℓ₀ ^ 4 * Lc4) with hC1
  set C2 := Cf / lbar * (3 * K * ℓ₀ ^ 2 * Lc2 + (2 * Gb + ℓ₀ ^ 2) * (1 + ℓ₀ ^ 2)) with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro N msq b₀ x hN hmsq hb₀ hx hu
  set V₀ := V₀c msq b₀ with hV₀
  set a := ctr d L N with ha
  set b := ctr d L N + x with hbdef
  have hba : b ≠ a := by
    intro h; apply hx; rw [hbdef, ha] at h
    exact add_eq_left.1 h
  have hab : a ≠ b := fun h => hba h.symm
  obtain ⟨hC, hK⟩ := hmain N msq b₀ b hmsq.le hb₀ hba
  have hnl : ‖(lbar : ℂ)‖ = lbar := by rw [Complex.norm_real, Real.norm_of_nonneg hlbar.le]
  have hl0 : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlbar.ne'
  set t := ‖b₀‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  set e := Cf * lbar * t with he
  have he0 : 0 ≤ e := by positivity
  have heb : e ≤ eb := by
    rw [he, heb_def]; exact mul_le_mul_of_nonneg_left hb₀ (by positivity)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hcore L hL8 N msq V₀ ℓ₀ hℓ₀ hC (lbar : ℂ) a b A hA1
    θ e lbar eb hθ0 hθ1 he0 hnl.le heb (fun k hk => hK k hk)
  obtain ⟨k1, k2, -, -, k5⟩ := kTwo_bounds hℓ₀ hA1 (by positivity : 0 ≤ e * θ ^ N)
    (initObs .two (lbar : ℂ)) (hK N le_rfl)
  have hτ := norm_tau_le (L := L) (N := N) hd1 hmsq
  set T : ℝ := 1 / (msq * Fintype.card (Lam d L N)) with hT
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hτ
  -- `W`
  have hW : (∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)) =
      (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) := by
    rw [sum_covAt_ofReal, sum_covAt_eq_WN hmsq hN a b,
      show b - a = x by rw [hbdef, ha]; abel]
  rw [hW] at c5 c6
  -- `r = |x|`
  have hr : (supNorm (a - b) : ℝ) = supNorm x := by
    rw [show a - b = -x by rw [hbdef, ha]; abel, supNorm_neg]
  -- the γ's are bounded
  have hga : ‖gaN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b‖ ≤ Gb := by
    have hWn := norm_sum_covAt_le hd hL2 hℓ₀ hC a a
    have hla : ‖laOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)‖ ≤ lbar + K * eb := by
      have := norm_sub_norm_le (laOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b))
        (lbar : ℂ)
      rw [hnl] at this
      nlinarith [mul_le_mul_of_nonneg_left heb hK0]
    have h1 := norm_sub_norm_le (gaN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)
      (laOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b) *
        ∑ k ∈ range N, (Flow.covAt d L N msq k a a : ℂ))
    rw [norm_mul] at h1
    have h2 := mul_le_mul hla hWn (norm_nonneg _) (by positivity)
    have h3 : K * e * ℓ₀ ^ 2 ≤ K * eb * ℓ₀ ^ 2 := by gcongr
    rw [hGb]; linarith
  have hgb : ‖gbN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b‖ ≤ Gb := by
    have hWn := norm_sum_covAt_le hd hL2 hℓ₀ hC b b
    have hla : ‖lbOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)‖ ≤ lbar + K * eb := by
      have := norm_sub_norm_le (lbOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b))
        (lbar : ℂ)
      rw [hnl] at this
      nlinarith [mul_le_mul_of_nonneg_left heb hK0]
    have h1 := norm_sub_norm_le (gbN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)
      (lbOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b) *
        ∑ k ∈ range N, (Flow.covAt d L N msq k b b : ℂ))
    rw [norm_mul] at h1
    have h2 := mul_le_mul hla hWn (norm_nonneg _) (by positivity)
    have h3 : K * e * ℓ₀ ^ 2 ≤ K * eb * ℓ₀ ^ 2 := by gcongr
    rw [hGb]; linarith
  -- exponents
  set ℓN := ellj d L ℓ₀ N with hℓN
  set jab := coal L a b with hjab
  have hθN : θ ^ N = (L : ℝ) ^ (-(κ * N)) := (rpow_neg_mul_nat hL0.le κ N).symm
  have hℓNθ : ℓN ^ 2 * θ ^ N = ℓ₀ ^ 2 * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) := by
    rw [hℓN, ellj_sq, mul_assoc, pow_mul_pow_rpow hL0, rpow_neg_mul_nat hL0.le]
  have hX2 : ellj d L ℓ₀ jab ^ 2 * θ ^ jab ≤
      ℓ₀ ^ 2 * (Lc2 * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) := by
    have := ellj_coal_sq_mul_pow_le hd2 hL2 ℓ₀ hκ.le hab; rwa [hr] at this
  have hX4 : ellj d L ℓ₀ jab ^ 4 * θ ^ jab ≤
      ℓ₀ ^ 4 * (Lc4 * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ))) := by
    have := ellj_coal_pow_four_mul_pow_le hd2 hL2 ℓ₀ hκ.le hab; rwa [hr] at this
  have hX2n : 0 ≤ ellj d L ℓ₀ jab ^ 2 * θ ^ jab := by positivity
  have hℓ' : ellj d L ℓ₀ (min N jab) ^ 2 ≤ ℓ₀ ^ 2 := by
    rw [ellj_sq]
    have : ((L : ℝ) ^ (-((d : ℝ) - 2))) ^ (min N jab) ≤ 1 :=
      pow_le_one₀ (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos hL1.le
        (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
            linarith))
    nlinarith [sq_nonneg ℓ₀]
  -- the algebra
  obtain ⟨E₁, E₂, hE₁, hE₂, hEq⟩ := twoPt_alg (la := laOf .two (VoN d L .two N msq V₀
      (initObs .two (lbar : ℂ)) a b)) (lb := lbOf .two (VoN d L .two N msq V₀
      (initObs .two (lbar : ℂ)) a b)) (W := (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ))
    hnl hlbar hu (avg_two_ab_eq' hd1 hL8 hN hmsq hC V₀ hl0 a b)
    (ε_ZtO_ab_two V₀ (lbar : ℂ) a b hd1 hL8 hN hmsq hC)
  refine ⟨E₁, E₂, ?_, ?_, ?_⟩
  · -- `E₁`
    rw [hE₁, div_le_iff₀ (by positivity)]
    have hY : 0 ≤ (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) := by positivity
    have h := mul_le_mul_of_nonneg_left hX4 (mul_nonneg hK0 he0)
    refine c6.trans (h.trans ?_)
    have heq : K * e * (ℓ₀ ^ 4 * (Lc4 * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)))) =
        C1 * t * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) * lbar ^ 2 := by
      rw [hC1, he]; field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) ht0) hY) (by positivity)
  · -- `E₂`
    refine hE₂.trans ?_
    have hk' : ‖kabTwo d L N msq V₀ (initObs .two (lbar : ℂ)) a b‖ ≤
        ((Gb + Gb) * ℓN ^ 2 + ℓN ^ 2 * ℓ₀ ^ 2 + T * ℓ₀ ^ 2) * (e * θ ^ N) := by
      refine k5.trans ?_
      gcongr
    have hB1 := k1; rw [norm_sub_rev] at hB1
    have hB2 := k2; rw [norm_sub_rev] at hB2
    have hnum : ((‖etaOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b) +
        2 * (laOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b) *
          lbOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)) *
          (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ)‖ +
        ‖raOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)‖ +
        ‖rbOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)‖ +
        ‖lamtA d L N msq V₀ (initObs .two (lbar : ℂ)) a b -
          laOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)‖ *
          ‖gbN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b‖ +
        ‖lamtB d L N msq V₀ (initObs .two (lbar : ℂ)) a b -
          lbOf .two (VoN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b)‖ *
          ‖gaN d L .two N msq V₀ (initObs .two (lbar : ℂ)) a b‖) * ‖tau d L N msq‖ +
        ‖kabTwo d L N msq V₀ (initObs .two (lbar : ℂ)) a b‖) ≤
        ((K * e * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) + K * e * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) +
          K * e * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) + e * θ ^ N * Gb + e * θ ^ N * Gb) * T +
          ((Gb + Gb) * ℓN ^ 2 + ℓN ^ 2 * ℓ₀ ^ 2 + T * ℓ₀ ^ 2) * (e * θ ^ N)) := by
      gcongr
    have hY1 : 0 ≤ (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) := by positivity
    have hY2 : 0 ≤ (L : ℝ) ^ (-(κ * N)) := by positivity
    have hY3 : 0 ≤ (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) := by positivity
    -- the bracket
    have hbr : ((K * e * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) + K * e * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) +
          K * e * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) + e * θ ^ N * Gb + e * θ ^ N * Gb) * T +
          ((Gb + Gb) * ℓN ^ 2 + ℓN ^ 2 * ℓ₀ ^ 2 + T * ℓ₀ ^ 2) * (e * θ ^ N)) =
        e * ((2 * Gb + ℓ₀ ^ 2) * ℓ₀ ^ 2 * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          (2 * Gb + ℓ₀ ^ 2) * (L : ℝ) ^ (-(κ * N)) * T +
          3 * K * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) * T) := by
      linear_combination (2 * e * Gb * T + e * T * ℓ₀ ^ 2) * hθN + e * (2 * Gb + ℓ₀ ^ 2) * hℓNθ
    have hb3 : 3 * K * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) * T ≤
        (3 * K * ℓ₀ ^ 2 * Lc2) * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) * T := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hX2 (by positivity : 0 ≤ 3 * K)) hT0
      refine this.trans (le_of_eq ?_); ring
    set M2 := 3 * K * ℓ₀ ^ 2 * Lc2 + (2 * Gb + ℓ₀ ^ 2) * (1 + ℓ₀ ^ 2) with hM2
    have hP0 : 0 ≤ 3 * K * ℓ₀ ^ 2 * Lc2 := by positivity
    have hQ : 0 ≤ 2 * Gb + ℓ₀ ^ 2 := by positivity
    have hQl : 0 ≤ (2 * Gb + ℓ₀ ^ 2) * ℓ₀ ^ 2 := by positivity
    have hM2e : M2 = 3 * K * ℓ₀ ^ 2 * Lc2 + (2 * Gb + ℓ₀ ^ 2) + (2 * Gb + ℓ₀ ^ 2) * ℓ₀ ^ 2 := by
      rw [hM2]; ring
    have h3t := three_terms hY1 hY2 hY3 hT0 (a1 := (2 * Gb + ℓ₀ ^ 2) * ℓ₀ ^ 2)
      (a2 := 2 * Gb + ℓ₀ ^ 2) (a3 := 3 * K * ℓ₀ ^ 2 * Lc2) (M := M2)
      (by rw [hM2e]; linarith) (by rw [hM2e]; linarith) (by rw [hM2e]; linarith)
    rw [div_le_iff₀ (by positivity)]
    refine hnum.trans ?_
    rw [hbr]
    have hS : (2 * Gb + ℓ₀ ^ 2) * ℓ₀ ^ 2 * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          (2 * Gb + ℓ₀ ^ 2) * (L : ℝ) ^ (-(κ * N)) * T +
          3 * K * (ellj d L ℓ₀ jab ^ 2 * θ ^ jab) * T ≤
        M2 * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) * T) := by
      linarith
    have hfin : e * (M2 * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) * T)) =
        C2 * t * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) /
            (msq * Fintype.card (Lam d L N))) * lbar ^ 2 := by
      rw [hC2, he, hM2, hT]; field_simp
    refine (mul_le_mul_of_nonneg_left hS he0).trans ?_
    rw [hfin]
    have hZ : 0 ≤ (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
        ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) /
          (msq * Fintype.card (Lam d L N)) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) ht0) hZ) (by positivity)
  · -- the identity, translated to `(0, x)`
    have htr := avg_four_transl hmsq hN V₀ a 0 x
    rw [zero_add, add_comm x a] at htr
    rw [← htr, hEq]
    simp only [lamA2, lamB2, gamA2, gamB2]
    ring

/-- **`lem:2pt`, Case (2), `e:2pt-b`, Tier 1** (see the module docstring). -/
theorem lem_2pt_two (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), 0 < lbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      ∀ (N : ℕ) (msq : ℝ) (b₀ : ℂ) (x : Lam d L N), 1 ≤ N → 0 < msq → ‖b₀‖ ≤ lbar → x ≠ 0 →
        1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
        ∃ E₁ E₂ : ℂ,
          ‖E₁‖ ≤ C * ‖b₀‖ * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) ∧
          ‖E₂‖ ≤ C * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
            ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) /
              (msq * Fintype.card (Lam d L N))) ∧
          avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
              (psibar (0 : Lam d L N) * psi (0 : Lam d L N) * (psibar x * psi x)) =
            -lamA2 d L N msq (V₀c msq b₀) lbar x * lamB2 d L N msq (V₀c msq b₀) lbar x *
                (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) ^ 2 +
              gamA2 d L N msq (V₀c msq b₀) lbar x * gamB2 d L N msq (V₀c msq b₀) lbar x +
              (-2 * lamA2 d L N msq (V₀c msq b₀) lbar x * lamB2 d L N msq (V₀c msq b₀) lbar x *
                  (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
                lamA2 d L N msq (V₀c msq b₀) lbar x * gamB2 d L N msq (V₀c msq b₀) lbar x +
                lamB2 d L N msq (V₀c msq b₀) lbar x * gamA2 d L N msq (V₀c msq b₀) lbar x) *
                tau d L N msq / (1 + Suscept.utN d L N msq (V₀c msq b₀)) +
              E₁ + E₂ / (1 + Suscept.utN d L N msq (V₀c msq b₀)) := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setup hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H⟩ := H L hL hLodd
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hKℓ' => ?_⟩
  obtain ⟨V₀c, lbar, Cf, κ, HF⟩ := H A hA ℓ₀ hℓ₀ hKℓ'
  obtain ⟨C, hC, h⟩ := lem_2pt_two_of hd HF
  exact ⟨V₀c, lbar, C, κ, HF.lbar_pos, hC, HF.κ_pos, HF.hb, h⟩

end

end PtCorr
