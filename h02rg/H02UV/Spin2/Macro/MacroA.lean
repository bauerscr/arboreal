import Spin2.Cont.ContEqS2
import Spin2.Cont.ContEqS3

set_option autoImplicit false

/-!
# `thm:macro` at order zero, finite `ε` (uniform in `N`)

* `MasterFacts.mac_beta_diff`: along a `D_ε` trajectory (`h = 0` start `(b, b − m²)`), for
  `j ≤ N − 2`: `|β_j − β_{N−2}| ≤ (N−2−j)(β + C_gu) + 4c₁` (the per-step band of `SpinConclD`
  summed from `j` to `N − 2`, with `ǧ_k ≤ 1`); no `β_R` in the bound.
* `mac_eps` (per `M`): for `δ > 0` there is `C = C(δ, L)` such that for `N ≥ N₀`,
  `4m²L^{2N} ≤ 1/β_R ≤ g₀`, every `b` in the bracket: `Z := β_{N−2}/β_R ∈ [1/4, 5]` and every
  `x ≠ 0` with `|x|/L^N ≥ δ` has `|ϑ_ε^{-2}P_ε(x) − Z^{2/3}| ≤ C/β_R`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- `c₁ + C_gu`-type constant of `mac_beta_diff`: `4c₁`, `c₁ = 2(1+β)max(K_e, β/2)`. -/
def macE : ℝ := 4 * (2 * (1 + betaL L) * max M.core.Ke (betaL L / 2))

/-- Slope of `mac_beta_diff`: `β + C_gu`. -/
def macS : ℝ := betaL L + Cgu (betaL L) M.core.cg

theorem macE_nonneg : 0 ≤ M.macE := by
  have hβ := ct_betaL_pos M.ct_L2
  have : 0 ≤ max M.core.Ke (betaL L / 2) := le_max_of_le_right (by linarith)
  unfold macE; positivity

theorem macS_nonneg : 0 ≤ M.macS := by
  have hβ := ct_betaL_pos M.ct_L2
  obtain ⟨-, -, -, -, -, -, hcg, -⟩ := M.core.hC2
  unfold macS Cgu; positivity

set_option maxHeartbeats 1000000 in
/-- **`β_j − β_{N−2}` along a `D_ε` trajectory**, uniformly in `β_R`. -/
theorem mac_beta_diff {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N)
    (hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1) {b : ℝ}
    (hD : ∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) :
    ∀ j ≤ N - 2, |betaJ R m b (b - m) j - betaJ R m b (b - m) (N - 2)| ≤
      ((N - 2 - j : ℕ) : ℝ) * M.macS + M.macE := by
  intro j hj
  set Nh := N - 2 with hNh
  obtain ⟨-, -, -, hstep, -⟩ := M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hβ := ct_betaL_pos M.ct_L2
  obtain ⟨-, -, -, -, -, -, hcg, -⟩ := M.core.hC2
  set β := betaL L with hβd
  set cg := M.core.cg
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  set g : ℕ → ℝ := fun k => (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) k).1 with hgd
  have hg1 : ∀ k ≤ Nh, g k ≤ 1 := fun k hk => (hD k hk).2.1.trans M.eps_le
  have hsum : ∀ n, j ≤ n → n ≤ Nh → |1 / g n - 1 / g j + ((n : ℝ) - j) * β| ≤
      2 * (1 + β) * max M.core.Ke (β / 2) * ∑ k ∈ Ico j n, zA L m k +
        Cgu β cg * ∑ k ∈ Ico j n, g k := by
    intro n hjn
    induction n, hjn using Nat.le_induction with
    | base => intro _; simp
    | succ n hjn ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hstep m hm b (b - m) hD n (by omega)
      rw [sum_Ico_succ_top hjn, sum_Ico_succ_top hjn]
      have e : 1 / g (n + 1) - 1 / g j + (((n + 1 : ℕ) : ℝ) - j) * β =
          (1 / g n - 1 / g j + ((n : ℝ) - j) * β) +
            (1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (n + 1)).1 -
              1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) n).1 + β) := by
        simp only [hgd]; push_cast; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have e2 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) n).1 = g n := rfl
      rw [e2] at h2
      nlinarith only [h1, h2]
  have H := hsum Nh hj le_rfl
  have hzA : ∑ k ∈ Ico j Nh, zA L m k ≤ 4 := by
    have hm0 : 0 ≤ m := hm.1.le
    have h1 : ∑ k ∈ Ico j Nh, zA L m k ≤ ∑ k ∈ range Nh, zA L m k :=
      sum_le_sum_of_subset_of_nonneg (by intro k hk; simp at hk ⊢; omega)
        (fun k _ _ => zA_nonneg L hm0 k)
    have h2 := sum_zA_le (Ln := L) rfl (by exact_mod_cast M.ct_L2) hm0 Nh
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by have := M.ct_L2; omega)
    have h3 : ((L : ℝ) ^ Nh) ^ 2 ≤ (L : ℝ) ^ (2 * N) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
    have h4 : m * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := (mul_le_mul_of_nonneg_left h3 hm0).trans hm1
    linarith
  have hgs : ∑ k ∈ Ico j Nh, g k ≤ ((Nh - j : ℕ) : ℝ) := by
    have : ∑ k ∈ Ico j Nh, g k ≤ ∑ _k ∈ Ico j Nh, (1 : ℝ) :=
      sum_le_sum fun k hk => hg1 k (by simp at hk; omega)
    simpa using this
  have hc₁ : 0 ≤ 2 * (1 + β) * max M.core.Ke (β / 2) := by
    have : 0 ≤ max M.core.Ke (β / 2) := le_max_of_le_right (by linarith)
    positivity
  have t1 := mul_le_mul_of_nonneg_left hzA hc₁
  have t2 := mul_le_mul_of_nonneg_left hgs hCgu
  have eN : ((Nh : ℝ) - j) = ((Nh - j : ℕ) : ℝ) := by rw [Nat.cast_sub hj]
  rw [eN] at H
  have hb : betaJ R m b (b - m) j - betaJ R m b (b - m) Nh =
      -(1 / g Nh - 1 / g j + ((Nh - j : ℕ) : ℝ) * β) + ((Nh - j : ℕ) : ℝ) * β := by
    simp only [betaJ, hgd]; ring
  rw [hb]
  have hn0 : (0 : ℝ) ≤ ((Nh - j : ℕ) : ℝ) := Nat.cast_nonneg _
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_of_nonneg (mul_nonneg hn0 hβ.le)]
  unfold macS macE
  rw [← hβd]
  nlinarith only [H, t1, t2]

end MasterFacts

variable {L : ℕ} [NeZero L]

/-- `t^{2/3} ≤ 1 + t` for `t ≥ 0`. -/
theorem mac_rpow23_le {t : ℝ} (ht : 0 ≤ t) : t ^ (2 / 3 : ℝ) ≤ 1 + t := by
  rcases le_or_gt t 1 with h | h
  · have := Real.rpow_le_one ht h (by norm_num : (0 : ℝ) ≤ 2 / 3)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num : (2 / 3 : ℝ) ≤ 1)
    rw [Real.rpow_one] at this
    linarith

/-- `Y^{2/3} ≤ 2Y` for `Y ≥ 1/8`. -/
theorem mac_rpow23_le_two {Y : ℝ} (hY : 1 / 8 ≤ Y) : Y ^ (2 / 3 : ℝ) ≤ 2 * Y := by
  have hY0 : 0 ≤ Y := by linarith
  have ha : 0 ≤ Y ^ (2 / 3 : ℝ) := Real.rpow_nonneg hY0 _
  have h3 : (Y ^ (2 / 3 : ℝ)) ^ 3 = Y ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
  have h3' : (Y ^ (2 / 3 : ℝ)) ^ 3 ≤ (2 * Y) ^ 3 := by
    rw [h3]; nlinarith [sq_nonneg Y]
  exact le_of_pow_le_pow_left₀ (by norm_num) (by linarith) h3'

omit [NeZero L] in
/-- `N − 2 − min(j_p, N − 2) ≤ |log_L δ|` when `j_p = ⌊N + log_L ℓ⌋`, `ℓ ≥ δ > 0`. -/
theorem mac_gap {N jp : ℕ} (hL : 2 ≤ L) {ℓ δ : ℝ} (hδ : 0 < δ) (hℓ : δ ≤ ℓ)
    (hj : (jp : ℤ) = jPhys L N ℓ) :
    (((N - 2 - min jp (N - 2) : ℕ)) : ℝ) ≤ |Real.logb L δ| := by
  rcases le_or_gt (N - 2) jp with h | h
  · rw [min_eq_right h, Nat.sub_self]; simp
  · rw [min_eq_left h.le]
    have h1 : (N : ℝ) + Real.logb L ℓ < (jp : ℝ) + 1 := by
      have := Int.lt_floor_add_one ((N : ℝ) + Real.logb L ℓ)
      rw [jPhys] at hj
      rw [← hj] at this
      exact_mod_cast this
    have h2 : Real.logb L δ ≤ Real.logb L ℓ :=
      Real.logb_le_logb_of_le (by exact_mod_cast (show 1 < L by omega)) hδ hℓ
    have h3 : (((N - 2 - jp : ℕ)) : ℝ) = (N : ℝ) - 2 - jp := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [h3]
    have := neg_le_abs (Real.logb L δ)
    linarith

set_option maxHeartbeats 2000000 in
/-- **`thm:macro` at order zero, finite `ε`** (per `M`). -/
theorem mac_eps (M : MasterFacts L) : ∃ (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 3 ≤ N₀ ∧
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR,
      (1 / 4 ≤ betaJ R m b (b - m) (N - 2) / βR ∧ betaJ R m b (b - m) (N - 2) / βR ≤ 5) ∧
      ∀ x : Lam 2 L N, x ≠ 0 → δ ≤ eucl x / (L : ℝ) ^ N →
        |Pconn L N (1 / b) x / thetaEpsSq βR b -
            (betaJ R m b (b - m) (N - 2) / βR) ^ (2 / 3 : ℝ)| ≤ C / βR := by
  obtain ⟨g₁, K, Kc, N₁, hg₁, -, hS⟩ := eqs_shortX M
  obtain ⟨g₂, K₂, N₂, hg₂, hg₂1, hN₂, hA⟩ := eqs_allB M
  obtain ⟨g₃, N₃, hg₃, hN₃, hU⟩ := eqs_bracketUp M
  have hL2 : 2 ≤ L := M.ct_L2
  set g₀ := min g₁ (min g₂ g₃) with hg₀d
  have hg01 : g₀ ≤ g₁ := min_le_left _ _
  have hg02 : g₀ ≤ g₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hg03 : g₀ ≤ g₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨g₀, max N₁ (max N₂ N₃), lt_min hg₁ (lt_min hg₂ hg₃),
    hN₂.trans ((le_max_left _ _).trans (le_max_right _ _)), fun δ hδ => ?_⟩
  set Δ := |Real.logb L δ| * M.macS + M.macE with hΔd
  have hΔ : 0 ≤ Δ := add_nonneg (mul_nonneg (abs_nonneg _) M.macS_nonneg) M.macE_nonneg
  refine ⟨2 * Δ + 4 * |K| * (6 + Δ), by positivity, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2' : N₂ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : N₃ ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hNge : 2 ≤ N := by omega
  obtain ⟨hmR, -, hB, -⟩ := hA N R hP hi0 hRℓ hRA hRρ hN2' m βR hm hβR hmass (hy.trans hg02)
  obtain ⟨hb0, hD, -, hgl⟩ := hB b hb
  have hup := hU N R hP hi0 hRℓ hRA hRρ hN3 m βR hm hβR hmass (hy.trans hg03) b hb
  have hy0 : 0 < 1 / βR := one_div_pos.2 hβR
  have hy1 : 1 / βR ≤ 1 := hy.trans (hg02.trans hg₂1)
  have hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have h0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
    linarith
  -- `β_j ≥ β_R/4` for `j ≤ N − 2`
  have hlow : ∀ j ≤ N - 2, βR / 4 ≤ betaJ R m b (b - m) j := by
    intro j hj
    have hgj := (hD j hj).1
    have h4 := hup j hj
    unfold betaJ
    rw [le_div_iff₀ hgj]
    have e : 4 * (1 / βR) * βR = 4 := by field_simp
    nlinarith
  set Y := betaJ R m b (b - m) (N - 2) / βR with hYd
  have hY4 : 1 / 4 ≤ Y := by
    rw [hYd, le_div_iff₀ hβR]; linarith [hlow (N - 2) le_rfl]
  have hY5 : Y ≤ 5 := by
    have hgN := (hD (N - 2) le_rfl).1
    rw [hYd, div_le_iff₀ hβR]
    unfold betaJ
    rw [div_le_iff₀ hgN]
    have e : 5 * βR * (1 / βR / 5) = 1 := by field_simp
    nlinarith
  refine ⟨⟨hY4, hY5⟩, fun x hx hxδ => ?_⟩
  obtain ⟨-, ⟨jp, hjp, -, -, hPj, -⟩, -, -⟩ :=
    hS N R hP hi0 hRℓ hRA hRρ hN1 m βR hm hβR hmass (hy.trans hg01) b hb x hx
  set k := min jp (N - 2) with hkd
  have hkN : k ≤ N - 2 := min_le_right _ _
  have hgap := mac_gap hL2 hδ hxδ hjp
  rw [← hkd] at hgap
  have hdiff := M.mac_beta_diff R hP hi0 hRℓ hRA hRρ hNge hmR hm1 hD k hkN
  have hdiff' : |betaJ R m b (b - m) k - betaJ R m b (b - m) (N - 2)| ≤ Δ := by
    refine hdiff.trans ?_
    have := mul_le_mul_of_nonneg_right hgap M.macS_nonneg
    rw [hΔd]; linarith
  set X := betaJ R m b (b - m) k / βR with hXd
  have hβk := hlow k hkN
  have hβk0 : 0 < betaJ R m b (b - m) k := by linarith
  have hX0 : 0 ≤ X := div_nonneg hβk0.le hβR.le
  have hXY : |X - Y| ≤ Δ * (1 / βR) := by
    rw [hXd, hYd, ← sub_div, abs_div, abs_of_pos hβR, div_le_iff₀ hβR]
    have e : Δ * (1 / βR) * βR = Δ := by field_simp
    rw [e]; exact hdiff'
  -- `|X^{2/3} − Y^{2/3}| ≤ 2Δ/β_R`
  have h1 : |X ^ (2 / 3 : ℝ) - Y ^ (2 / 3 : ℝ)| ≤ 2 * Δ * (1 / βR) := by
    have := ct_rpow23_sub hX0 (by linarith : (0 : ℝ) < Y)
    refine this.trans ?_
    have hY2 := mac_rpow23_le_two (Y := Y) (by linarith)
    have hYp : 0 < Y := by linarith
    have hq : Y ^ (2 / 3 : ℝ) * (|X - Y| / Y) ≤ 2 * Y * (|X - Y| / Y) :=
      mul_le_mul_of_nonneg_right hY2 (div_nonneg (abs_nonneg _) hYp.le)
    have e : 2 * Y * (|X - Y| / Y) = 2 * |X - Y| := by field_simp
    linarith
  -- the multiscale error `K X^{2/3}/β_k ≤ 4|K|(6 + Δ)/β_R`
  have h2 : K * X ^ (2 / 3 : ℝ) / betaJ R m b (b - m) k ≤ 4 * |K| * (6 + Δ) * (1 / βR) := by
    have hXr := mac_rpow23_le hX0
    have hX6 : X ≤ 5 + Δ := by
      have := (abs_le.1 hXY).2
      have : Δ * (1 / βR) ≤ Δ := mul_le_of_le_one_right hΔ hy1
      linarith
    have hr0 : 0 ≤ X ^ (2 / 3 : ℝ) := Real.rpow_nonneg hX0 _
    have hKX : K * X ^ (2 / 3 : ℝ) ≤ |K| * (6 + Δ) :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) hr0).trans
        (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K))
    have hinv : 1 / betaJ R m b (b - m) k ≤ 4 * (1 / βR) := by
      have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < βR / 4) hβk
      have e : 1 / (βR / 4) = 4 * (1 / βR) := by field_simp
      linarith
    have hK0 : 0 ≤ |K| * (6 + Δ) := by positivity
    calc K * X ^ (2 / 3 : ℝ) / betaJ R m b (b - m) k
        = K * X ^ (2 / 3 : ℝ) * (1 / betaJ R m b (b - m) k) := by ring
      _ ≤ |K| * (6 + Δ) * (1 / betaJ R m b (b - m) k) :=
          mul_le_mul_of_nonneg_right hKX (by positivity)
      _ ≤ |K| * (6 + Δ) * (4 * (1 / βR)) := mul_le_mul_of_nonneg_left hinv hK0
      _ = 4 * |K| * (6 + Δ) * (1 / βR) := by ring
  have h3 := (abs_sub_le (Pconn L N (1 / b) x / thetaEpsSq βR b) (X ^ (2 / 3 : ℝ))
    (Y ^ (2 / 3 : ℝ)))
  have e : (2 * Δ + 4 * |K| * (6 + Δ)) / βR =
      2 * Δ * (1 / βR) + 4 * |K| * (6 + Δ) * (1 / βR) := by ring
  rw [e]
  linarith

end

end Spin2
