import Spin2.Final.FinalAll
import Spin2.Multiscale.BetaLog

/-!
# `ϑ_ε` at finite `ε`: `ϑ_ε²(log L^N)^{2/3} → (2πβ_R/3)^{2/3}` (`thm:limit`, the `ϑ_ε` part)

`ϑ_ε² := thetaEpsSq β_R b = (β_R b)^{2/3}` (`β_ε = 1/b`). For every `b` in the bracket
`[bFin(1/(2β_R)), bFin(2/β_R)]` (in particular every shooting solution, and every `H0Sol` with the
a priori hypotheses of `thm_multiscale_final_h0_all`):

* **`ct_beta_scale`**: along the `h = 0` trajectory, at every scale `j ≤ N − 2`,
  `|β_j − (N−2−j)β| ≤ (T + E) + a log(2((N−2−j)β + T + E + a|log 2a|))`, `β = betaL L =
  β₁ log L`, `β₁ = betaOne = 3/(2π)`, `T ≥ β_{N−2}`, `a = C_gu/β`, `E = 4c₁ + 2C_gu|K'|`
  (per-step band of `SpinConclD` summed from `j` to `N − 2`; the `ǧ`-sum by `LogSumD`; inverted by
  `beta_eps_log`).
* **`ct_main`**: `fa_main` with the extra bound `ǧ^0_{N−2}(b) ≥ 1/(5β_R)` on the bracket (so
  `T = 5β_R`).
* **`thm_theta_eps`**: `|1/b − Nβ| ≤ K(1 + β_R + log N)` and, when `2K(1 + β_R + log N) ≤ Nβ`,
  `|ϑ_ε²(log L^N)^{2/3} − z_*| ≤ z_*·2K(1 + β_R + log N)/(Nβ)`, `z_* = (2πβ_R/3)^{2/3}`.
* **`thm_theta_eps_tendsto`**: along any sequence `N_k → ∞` of bracket points `b_k` (fixed `β_R`),
  `ϑ_ε²(log L^{N_k})^{2/3} → z_*`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Filter Topology

/-- `β₁ = 3/(2π)`: `β_{j} − β_{j+1} ≈ β₁ log L` (`betaL L = β₁ log L`). -/
def betaOne : ℝ := 3 / (2 * Real.pi)

theorem betaOne_pos : 0 < betaOne := by unfold betaOne; have := Real.pi_pos; positivity

theorem betaL_eq_betaOne (L : ℕ) : betaL L = betaOne * Real.log L := by
  unfold betaL betaOne; ring

theorem ct_betaL_pos {L : ℕ} (hL : 2 ≤ L) : 0 < betaL L := by
  rw [betaL_eq_betaOne]
  exact mul_pos betaOne_pos (Real.log_pos (by exact_mod_cast (show 1 < L by omega)))

/-- `log L / β = 2π/3`. -/
theorem ct_log_div_betaL {L : ℕ} (hL : 2 ≤ L) : Real.log L / betaL L = 2 * Real.pi / 3 := by
  have hl : 0 < Real.log L := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  rw [betaL_eq_betaOne]; unfold betaOne
  have := Real.pi_pos
  field_simp

/-! ## Pure lemmas -/

/-- `|p² − q²|·q ≤ |p³ − q³|` for `p ≥ 0`, `q > 0`. -/
theorem ct_sq_cube {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : |p ^ 2 - q ^ 2| * q ≤ |p ^ 3 - q ^ 3| := by
  rw [show p ^ 2 - q ^ 2 = (p - q) * (p + q) by ring,
    show p ^ 3 - q ^ 3 = (p - q) * (p ^ 2 + p * q + q ^ 2) by ring, abs_mul, abs_mul,
    abs_of_nonneg (by linarith : 0 ≤ p + q), abs_of_nonneg (by positivity : 0 ≤ p ^ 2 + p * q + q ^ 2),
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  nlinarith only [sq_nonneg p, hp, hq]

theorem ct_cube_third {X : ℝ} (hX : 0 ≤ X) : (X ^ (1 / 3 : ℝ)) ^ 3 = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num

theorem ct_sq_third {X : ℝ} (hX : 0 ≤ X) : (X ^ (1 / 3 : ℝ)) ^ 2 = X ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num

/-- **`2/3`-power comparison**: `|X^{2/3} − Y^{2/3}| ≤ Y^{2/3}·|X − Y|/Y` (`X ≥ 0`, `Y > 0`). -/
theorem ct_rpow23_sub {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 < Y) :
    |X ^ (2 / 3 : ℝ) - Y ^ (2 / 3 : ℝ)| ≤ Y ^ (2 / 3 : ℝ) * (|X - Y| / Y) := by
  have hp : 0 ≤ X ^ (1 / 3 : ℝ) := Real.rpow_nonneg hX _
  have hq : 0 < Y ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hY _
  have h := ct_sq_cube hp hq
  have hq3 : 0 < (Y ^ (1 / 3 : ℝ)) ^ 3 := by positivity
  have key : |(X ^ (1 / 3 : ℝ)) ^ 2 - (Y ^ (1 / 3 : ℝ)) ^ 2| ≤ (Y ^ (1 / 3 : ℝ)) ^ 2 *
      (|(X ^ (1 / 3 : ℝ)) ^ 3 - (Y ^ (1 / 3 : ℝ)) ^ 3| / (Y ^ (1 / 3 : ℝ)) ^ 3) := by
    rw [mul_div_assoc', le_div_iff₀ hq3]
    calc |(X ^ (1 / 3 : ℝ)) ^ 2 - (Y ^ (1 / 3 : ℝ)) ^ 2| * (Y ^ (1 / 3 : ℝ)) ^ 3 =
        (|(X ^ (1 / 3 : ℝ)) ^ 2 - (Y ^ (1 / 3 : ℝ)) ^ 2| * Y ^ (1 / 3 : ℝ)) *
          (Y ^ (1 / 3 : ℝ)) ^ 2 := by ring
      _ ≤ |(X ^ (1 / 3 : ℝ)) ^ 3 - (Y ^ (1 / 3 : ℝ)) ^ 3| * (Y ^ (1 / 3 : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = (Y ^ (1 / 3 : ℝ)) ^ 2 * |(X ^ (1 / 3 : ℝ)) ^ 3 - (Y ^ (1 / 3 : ℝ)) ^ 3| := by ring
  rwa [ct_sq_third hX, ct_sq_third hY.le, ct_cube_third hX, ct_cube_third hY.le] at key

/-- `log(2(x + D)) ≤ 2(s + D) + log(1 + t)` for `0 ≤ x ≤ s(1 + t)`. -/
theorem ct_log_lin {x s t D : ℝ} (hD : 0 < D) (hs : 0 ≤ s) (ht : 0 ≤ t) (hx0 : 0 ≤ x)
    (hx : x ≤ s * (1 + t)) : Real.log (2 * (x + D)) ≤ 2 * (s + D) + Real.log (1 + t) := by
  have h1 : 2 * (x + D) ≤ 2 * (s + D) * (1 + t) := by
    have : D ≤ D * (1 + t) := le_mul_of_one_le_right hD.le (by linarith)
    nlinarith only [hx, this]
  have h2 : Real.log (2 * (x + D)) ≤ Real.log (2 * (s + D) * (1 + t)) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul (x := 2 * (s + D)) (y := 1 + t) (by positivity) (by positivity)] at h2
  have h3 := Real.log_le_sub_one_of_pos (show 0 < 2 * (s + D) by positivity)
  linarith

/-! ## The running coupling from scale `j` to `N − 2` -/

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- `a = C_gu/β`. -/
def ctA : ℝ := Cgu (betaL L) M.core.cg / betaL L

/-- `E = 4c₁ + 2C_gu|K'|`, `c₁ = 2(1+β)max(K_e, β/2)`, `K' = betaAsymK`. -/
def ctE : ℝ :=
  4 * (2 * (1 + betaL L) * max M.core.Ke (betaL L / 2)) +
    2 * Cgu (betaL L) M.core.cg * |betaAsymK (betaL L) M.core.cg (eRange (betaL L) M.core.Ke 1)|

include M in
theorem ct_L2 : 2 ≤ L := by have := M.core.hL49; omega

theorem ctA_nonneg : 0 ≤ M.ctA := by
  have hβ := ct_betaL_pos M.ct_L2
  obtain ⟨-, -, -, -, -, -, hcg, -⟩ := M.core.hC2
  unfold ctA Cgu; positivity

theorem ctE_nonneg : 0 ≤ M.ctE := by
  have hβ := ct_betaL_pos M.ct_L2
  obtain ⟨-, -, -, -, -, -, hcg, -⟩ := M.core.hC2
  have : 0 ≤ max M.core.Ke (betaL L / 2) := le_max_of_le_right (by linarith)
  unfold ctE Cgu; positivity

set_option maxHeartbeats 1000000 in
/-- **`β_j` along a `D_ε` trajectory** (`h = 0` start `(b, b − m²)`), for `j ≤ N − 2`, with
`β_{N−2} ≤ T`: `|β_j − (N−2−j)β| ≤ (T + E) + a log(2((N−2−j)β + T + E + a|log 2a|))`. -/
theorem ct_beta_scale {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N)
    (hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1) {b T : ℝ}
    (hD : ∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hT : 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1 ≤ T) :
    ∀ j ≤ N - 2, |betaJ R m b (b - m) j - ((N - 2 - j : ℕ) : ℝ) * betaL L| ≤
      (T + M.ctE) + M.ctA * Real.log (2 * (((N - 2 - j : ℕ) : ℝ) * betaL L + (T + M.ctE) +
        M.ctA * |Real.log (2 * M.ctA)|)) := by
  intro j hj
  set Nh := N - 2 with hNh
  obtain ⟨hLS, -, -, hstep, -⟩ := M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hβ := ct_betaL_pos M.ct_L2
  obtain ⟨-, -, -, -, -, -, hcg, -⟩ := M.core.hC2
  set β := betaL L with hβd
  set cg := M.core.cg
  set eR := eRange β M.core.Ke 1
  set Ka := betaAsymK β cg eR with hKad
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  set g : ℕ → ℝ := fun k => (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) k).1 with hgd
  have hg : ∀ k ≤ Nh, 0 < g k := fun k hk => (hD k hk).1
  have hg1 : ∀ k ≤ Nh, g k ≤ 1 := fun k hk => (hD k hk).2.1.trans M.eps_le
  have hg0 : g 0 = b := rfl
  have hb : 0 < b := hg0 ▸ hg 0 (Nat.zero_le _)
  -- the `ǧ`-sum
  set S : ℕ → ℝ := fun k => ∑ i ∈ range k, g i with hSd
  have LS := hLS m hm b (b - m) hD S (fun _ => 0) (fun _ => 0) 0 (-1) le_rfl (fun _ => le_rfl)
    (fun k _ => by simp [hSd, hgd, sum_range_succ])
  have LS' : ∀ n ≤ Nh, |S n - 1 / β * Real.log (g n / b)| ≤ Ka * g n := by
    intro n hn
    have key := LS n hn
    simp only [sum_range_zero, sub_zero, sub_self, mul_zero, sum_const_zero, add_zero,
      abs_neg, abs_one, hSd] at key ⊢
    have e1 : -1 / β * Real.log (g n / b) = -(1 / β * Real.log (g n / b)) := by ring
    rw [e1, ← sub_eq_add_neg] at key
    simpa [hKad, betaAsymK] using key
  -- the per-step band summed from `j`
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
  -- the `zA` sum
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
  -- the `ǧ` sum from `j`
  have hgs : ∑ k ∈ Ico j Nh, g k ≤ 1 / β * Real.log (g Nh / g j) + 2 * |Ka| := by
    rw [sum_Ico_eq_sub _ hj]
    have a1 := (abs_le.1 (LS' Nh le_rfl)).2
    have a2 := (abs_le.1 (LS' j hj)).1
    have hgj := hg j hj
    have hgN := hg Nh le_rfl
    have el : Real.log (g Nh / g j) = Real.log (g Nh / b) - Real.log (g j / b) := by
      rw [Real.log_div hgN.ne' hgj.ne', Real.log_div hgN.ne' hb.ne', Real.log_div hgj.ne' hb.ne']
      ring
    have k1 : Ka * g Nh ≤ |Ka| :=
      (mul_le_mul_of_nonneg_right (le_abs_self Ka) hgN.le).trans
        (mul_le_of_le_one_right (abs_nonneg _) (hg1 Nh le_rfl))
    have k2 : Ka * g j ≤ |Ka| :=
      (mul_le_mul_of_nonneg_right (le_abs_self Ka) hgj.le).trans
        (mul_le_of_le_one_right (abs_nonneg _) (hg1 j hj))
    rw [el, mul_sub]
    linarith
  have hc₁ : 0 ≤ 2 * (1 + β) * max M.core.Ke (β / 2) := by
    have : 0 ≤ max M.core.Ke (β / 2) := le_max_of_le_right (by linarith)
    positivity
  have H' : |1 / g Nh - 1 / g j + ((Nh - j : ℕ) : ℝ) * β| ≤
      M.ctE + M.ctA * Real.log (g Nh / g j) := by
    rw [Nat.cast_sub hj]
    refine H.trans ?_
    have t1 := mul_le_mul_of_nonneg_left hzA hc₁
    have t2 := mul_le_mul_of_nonneg_left hgs hCgu
    have e : Cgu β cg * (1 / β * Real.log (g Nh / g j) + 2 * |Ka|) =
        M.ctA * Real.log (g Nh / g j) + 2 * Cgu β cg * |Ka| := by
      unfold ctA; rw [← hβd]; ring
    unfold ctE; rw [← hβd]
    linarith
  have := beta_eps_log (hg j hj) (hg Nh le_rfl) (hg1 Nh le_rfl) hT M.ctA_nonneg M.ctE_nonneg
    (by positivity) H'
  exact this

set_option maxHeartbeats 4000000 in
/-- **The bracket with a lower bound on `ǧ^0_{N_h}`** (`fa_bracket_all`, second part, plus
`ǧ^0_{N_h}(b) ≥ (7/8)ǧ^c_{N_h}(b) ≥ 7/(32β_R)`). -/
theorem ct_bracket_g {pW g₀ K : ℝ} (hgε : g₀ ≤ M.core.ε / 2)
    (hs : pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N)
    {m : ℝ} (hm : m ∈ mRange L N)
    (hF' : ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwRes6 M pW K R Nh m b μc)
    {βR : ℝ} (hβ : 0 < βR) (hmass : 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR)
    (hyg : 1 / βR ≤ g₀ / 3) (hcy : 100 * M.core.Cb * (1 / βR) ≤ 1) :
    ∀ b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2))),
      0 < b ∧ (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R Nh m b ∧
      1 / βR / 5 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -, -, -, H⟩ := M.core.hC2
  obtain ⟨hfc, -, -, -, -, hnear, hsm, -, hbF, -⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh
  have fc := hfc m hm
  have hy : 0 < 1 / βR := one_div_pos.2 hβ
  have h6 : 6 ≤ M.core.ε * βR := by
    have : 1 / βR ≤ M.core.ε / 6 := by linarith
    rw [div_le_iff₀ hβ] at this
    linarith
  have e₁ : 1 / (2 * βR) = 1 / βR / 2 := by field_simp
  have e₂ : 1 / (βR / 2) = 2 * (1 / βR) := by field_simp
  obtain ⟨U₁, G₁⟩ := (hbF (2 * βR) (by rw [div_le_iff₀ hε]; linarith)).1 m hm
  obtain ⟨U₂, G₂⟩ := (hbF (βR / 2) (by rw [div_le_iff₀ hε]; linarith)).1 m hm
  set b₁ := bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)) with hb₁d
  set b₂ := bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2)) with hb₂d
  have N₁ := hnear m hm b₁ U₁ (2 * βR) G₁
  have N₂ := hnear m hm b₂ U₂ (βR / 2) G₂
  rw [e₁] at N₁ G₁
  rw [e₂] at N₂ G₂
  have ha₁ := fb_adm_muc U₁.choose_spec.1
  have ha₂ := fb_adm_muc U₂.choose_spec.1
  set μ₁ := Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₁
  set μ₂ := Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₂
  have hb12 : b₁ ≤ b₂ := by
    by_contra hc
    have := hsm m hm U₂ U₁ (not_le.1 hc)
    rw [G₁, G₂] at this
    linarith
  have hb₁ : 0 < b₁ := (ha₁.1 0 (Nat.zero_le _)).1
  set g₁ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1 with hg₁d
  set g₂ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 with hg₂d
  have N₁' : |g₁ - 1 / βR / 2| ≤ 4 * M.core.Cb * (1 / βR / 2) ^ 2 := N₁
  have N₂' : |g₂ - 2 * (1 / βR)| ≤ 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 := N₂
  have hcy2 : M.core.Cb * (1 / βR) ^ 2 ≤ 1 / βR / 100 := by
    have := mul_le_mul_of_nonneg_right (show M.core.Cb * (1 / βR) ≤ 1 / 100 by linarith) hy.le
    calc M.core.Cb * (1 / βR) ^ 2 = M.core.Cb * (1 / βR) * (1 / βR) := by ring
      _ ≤ 1 / 100 * (1 / βR) := this
      _ = 1 / βR / 100 := by ring
  have hgu₂ : g₂ ≤ 3 * (1 / βR) := by
    have e : 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 = 16 * (M.core.Cb * (1 / βR) ^ 2) := by ring
    have := (abs_le.1 N₂').2
    linarith
  have hg₂g : g₂ ≤ g₀ := by linarith
  have hg₂ε : g₂ < M.core.ε := by linarith
  have hgl₁ : 1 / βR / 4 ≤ g₁ := by
    have e : 4 * M.core.Cb * (1 / βR / 2) ^ 2 = M.core.Cb * (1 / βR) ^ 2 := by ring
    have := (abs_le.1 N₁').1
    linarith
  have hm₁ : m * (L : ℝ) ^ (2 * N) ≤ g₁ := by linarith
  have hBe := fun b (hb : b ∈ Icc b₁ b₂) => fb_ufix_between fc ha₁ ha₂ hg₂ε hb
  intro b hb
  obtain ⟨ham, hl, hu⟩ := hBe b hb
  have hgc0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b
      (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b) Nh).1 :=
    (ham.1 Nh le_rfl).1.le
  obtain ⟨hD, hd, hPb⟩ := hF' b _ (hb₁.trans_le hb.1) ham (hm₁.trans hl) (hu.trans hg₂g)
  have hs' := fb_s_le hs hgc0
  have hd' := (abs_le.1 hd).1
  refine ⟨hb₁.trans_le hb.1, hD, hPb, ?_⟩
  linarith

end MasterFacts

/-- The bracket `[bFin(1/(2β_R)), bFin(2/β_R)]` of `thm_multiscale_final_h0_all`. -/
abbrev ctBracket {L : ℕ} [NeZero L] (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (m βR : ℝ) : Set ℝ :=
  Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR)))
    (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (2 / βR))

set_option maxHeartbeats 4000000 in
/-- **`fa_main` with `ǧ^0_{N−2} ≥ 1/(5β_R)` on the bracket** (constants depending on `L` only):
for `N ≥ N₀`, `m² > 0`, `4m²L^{2N} ≤ 1/β_R ≤ g₀`: `m² ∈ mRange`; every `b` in the bracket has
`b > 0`, the `h = 0` trajectory in `D_ε` up to `N − 2`, the pair bound and `ǧ^0_{N−2}(b) ≥ 1/(5β_R)`;
every `H0Sol` with the a priori hypotheses of `thm_multiscale_final_h0_all` is in the bracket. -/
theorem ct_main : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧ g₀ ≤ 1 ∧ 3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
      m ∈ mRange L N ∧
      (∀ b ∈ ctBracket M R m βR, 0 < b ∧
        (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R (N - 2) m b ∧
        1 / βR / 5 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1) ∧
      ∀ b, H0Sol M R m βR b →
        b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε →
        m * (L : ℝ) ^ (2 * N) ≤
          Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b →
        Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b ≤ g₀ →
        b ∈ ctBracket M R m βR := by
  obtain ⟨L₀, h⟩ := fb_consts6
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, pW, g₀, K, hg, hgε, hs, hF⟩ := h L hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -⟩ := M.core.hC2
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  set g₁ := min (g₀ / 3) (min (1 / (100 * (M.core.Cb + 1)))
    (min (1 / (M.Kp + 1)) (min 1 (M.core.ε / 8)))) with hg₁d
  have hg₁3 : g₁ ≤ g₀ / 3 := min_le_left _ _
  have hg₁C : g₁ ≤ 1 / (100 * (M.core.Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hg₁K : g₁ ≤ 1 / (M.Kp + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg₁1 : g₁ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hg₁8 : g₁ ≤ M.core.ε / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hCg : ∀ y, 0 ≤ y → y ≤ g₁ → 100 * M.core.Cb * y ≤ 1 := fun y hy0 hy => by
    have h1 : y * (100 * (M.core.Cb + 1)) ≤ 1 := by
      have := hy.trans hg₁C
      rwa [le_div_iff₀ (by positivity)] at this
    have e : y * (100 * (M.core.Cb + 1)) = 100 * M.core.Cb * y + 100 * y := by ring
    linarith
  have hg₁0 : 0 < g₁ := lt_min (by linarith) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min one_pos (by linarith))))
  refine ⟨M, g₁, K, 4 + ⌈4 * M.Kp⌉₊, hg₁0, hg₁1, by omega, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  have hN2 : 2 ≤ N := by omega
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
  have h4 : 4 * (m * (L : ℝ) ^ (2 * N)) ≤ g₁ := hmass.trans hy
  have hmR : m ∈ mRange L N := fin_mRange hL2 (by omega) hm (by linarith)
  have hKz : M.Kp * zA L m (N - 2 - 1) ≤ 1 / 2 := by
    refine fin_Kz_le hL2 hKp hm.le hN ?_
    have h1 : g₁ * (M.Kp + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hg₁K
    have h2 : M.Kp * (m * (L : ℝ) ^ (2 * N)) ≤ M.Kp * (g₁ / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hKp
    have e : g₁ * (M.Kp + 1) = M.Kp * g₁ + g₁ := by ring
    have h3 : M.Kp * g₁ ≤ 1 := by linarith
    linarith
  have hF' := hF N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m hmR hKz
  have e₂ : (2 : ℝ) / βR = 1 / (βR / 2) := by field_simp
  refine ⟨hmR, ?_, fun b hsol hU hmV hgb => ?_⟩
  · intro b hb
    rw [ctBracket, e₂] at hb
    exact M.ct_bracket_g hgε hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hF' hβ hmass
      (hy.trans hg₁3) (hCg _ (one_div_pos.2 hβ).le hy) b hb
  · obtain ⟨-, hby, -⟩ := hsol
    obtain ⟨-, -, hbr, -, -⟩ := M.fa_locate hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hF' hU hmV
      (hgb.trans (hg₁3.trans (by linarith))) (hgb.trans hg₁8) (hCg _ (hX0.trans hmV) hgb)
    rw [hby] at hbr
    have e₁ : 1 / βR / 2 = 1 / (2 * βR) := by field_simp
    have e₃ : 2 * (1 / βR) = 2 / βR := by field_simp
    rw [e₁, e₃] at hbr
    exact hbr

end

end Spin2

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- `z_* = (2πβ_R/3)^{2/3}`, the limit of `ϑ_ε²(log L^N)^{2/3}`. -/
def thetaStar (βR : ℝ) : ℝ := (2 * Real.pi * βR / 3) ^ (2 / 3 : ℝ)

/-- **The `ϑ_ε` arithmetic** (pure): from `|β_ε − Nβ| ≤ E`, `2E ≤ Nβ`, `log L = (2π/3)β`:
`|(β_R b)^{2/3}(N log L)^{2/3} − z_*| ≤ z_*·2E/(Nβ)`, `b = 1/β_ε`. -/
theorem ct_theta_arith {βR b β lL n E : ℝ} (hβR : 0 < βR) (hb : 0 < b) (hβ : 0 < β) (hn : 0 < n)
    (hlL : lL = 2 * Real.pi / 3 * β) (hE : |1 / b - n * β| ≤ E) (h2 : 2 * E ≤ n * β) :
    |(βR * b) ^ (2 / 3 : ℝ) * (n * lL) ^ (2 / 3 : ℝ) - thetaStar βR| ≤
      thetaStar βR * (2 * E / (n * β)) := by
  have hpi := Real.pi_pos
  have hlL0 : 0 < lL := by rw [hlL]; positivity
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  set Y := 2 * Real.pi * βR / 3 with hYd
  have hY : 0 < Y := by positivity
  have hX : βR * b * (n * lL) = Y * (b * n * β) := by rw [hlL, hYd]; ring
  have key := ct_rpow23_sub (X := βR * b * (n * lL)) (by positivity) hY
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [hX, show Y * (b * n * β) - Y = Y * (b * n * β - 1) by ring, abs_mul, abs_of_pos hY,
    mul_div_cancel_left₀ _ hY.ne']
  set B := 1 / b with hBd
  have hB : 0 < B := by positivity
  have hbB : b = 1 / B := by rw [hBd, one_div_one_div]
  have hBl : n * β / 2 ≤ B := by have := (abs_le.1 hE).1; linarith
  rw [hbB, show 1 / B * n * β - 1 = -(B - n * β) / B by field_simp; ring, abs_div, abs_neg,
    abs_of_pos hB, div_le_div_iff₀ hB (by positivity)]
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  calc |B - n * β| * (n * β) ≤ E * (n * β) := mul_le_mul_of_nonneg_right hE (by positivity)
    _ ≤ E * (2 * B) := mul_le_mul_of_nonneg_left (by linarith) hE0
    _ = 2 * E * B := by ring

set_option maxHeartbeats 1000000 in
/-- **`thm:limit`, the `ϑ_ε` part** (constants `M, g₀, K, N₀` depending on `L` only). For
`N ≥ N₀`, `m² > 0`, `4m²L^{2N} ≤ 1/β_R ≤ g₀` and every `b` in the bracket
`[bFin(1/(2β_R)), bFin(2/β_R)]` (`β_ε = 1/b`):
`|β_ε − Nβ₁ log L| ≤ K(1 + β_R + log N)`, and, if `2K(1 + β_R + log N) ≤ Nβ₁ log L`,
`|ϑ_ε²(log L^N)^{2/3} − (2πβ_R/3)^{2/3}| ≤ (2πβ_R/3)^{2/3}·2K(1 + β_R + log N)/(Nβ₁ log L)`. -/
theorem thm_theta_eps : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 0 < K ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR, 0 < b ∧
      |1 / b - N * betaL L| ≤ K * (1 + βR + Real.log N) ∧
      (2 * (K * (1 + βR + Real.log N)) ≤ N * betaL L →
        |thetaEpsSq βR b * Real.log ((L : ℝ) ^ N) ^ (2 / 3 : ℝ) - thetaStar βR| ≤
          thetaStar βR * (2 * (K * (1 + βR + Real.log N)) / (N * betaL L))) := by
  obtain ⟨L₀, h⟩ := ct_main
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K₀, N₀, hg, hg1, hN₀, hF⟩ := h L hL
  have hβ := ct_betaL_pos M.ct_L2
  set β := betaL L with hβd
  set a := M.ctA
  set E := M.ctE
  set c := a * |Real.log (2 * a)|
  have ha := M.ctA_nonneg
  have hE := M.ctE_nonneg
  have hc : 0 ≤ c := mul_nonneg ha (abs_nonneg _)
  set K := 2 * β + 5 + E + 2 * a * (β + E + c) + 10 * a + a with hKd
  have hK : 0 < K := by positivity
  refine ⟨M, g₀, K, N₀, hg, hK, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy b hb
  obtain ⟨hmR, hB, -⟩ := hF N R hP hi0 hRℓ hRA hRρ hN m βR hm hβR hmass hy
  obtain ⟨hb0, hD, -, hgl⟩ := hB b hb
  have hm1 : m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    have := one_div_pos.2 hβR
    have h0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
    linarith
  have hT : 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1 ≤ 5 * βR := by
    have hg0 : 0 < 1 / βR / 5 := by positivity
    rw [div_le_iff₀ (hg0.trans_le hgl)]
    have e : 5 * βR * (1 / βR / 5) = 1 := by field_simp
    nlinarith only [hgl, e, hβR]
  have H := M.ct_beta_scale R hP hi0 hRℓ hRA hRρ (by omega) hmR hm1 hD hT 0 (Nat.zero_le _)
  have e0 : betaJ R m b (b - m) 0 = 1 / b := rfl
  rw [e0, Nat.sub_zero] at H
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hcast : ((N - 2 : ℕ) : ℝ) = N - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hcast] at H
  have hL := ct_log_lin (x := ((N : ℝ) - 2) * β) (s := β) (t := (N : ℝ) - 1)
    (D := 5 * βR + E + c) (by positivity) hβ.le (by linarith)
    (mul_nonneg (by linarith [show (3 : ℝ) ≤ N by exact_mod_cast (show 3 ≤ N by omega)]) hβ.le)
    (by nlinarith only [hβ])
  rw [show (1 : ℝ) + (N - 1) = N by ring,
    show ((N : ℝ) - 2) * β + (5 * βR + E + c) = ((N : ℝ) - 2) * β + (5 * βR + E) + c by ring] at hL
  have hL' := mul_le_mul_of_nonneg_left hL ha
  have hbd : |1 / b - N * β| ≤ K * (1 + βR + Real.log N) := by
    have t : |1 / b - N * β| ≤ |1 / b - ((N : ℝ) - 2) * β| + 2 * β := by
      have := abs_sub_le (1 / b) (((N : ℝ) - 2) * β) (N * β)
      rw [show ((N : ℝ) - 2) * β - N * β = -(2 * β) by ring, abs_neg,
        abs_of_pos (by linarith : 0 < 2 * β)] at this
      exact this
    have hprod : 0 ≤ 2 * a * (β + E + c) := by positivity
    have k1 : (5 + 10 * a) * βR ≤ K * βR := mul_le_mul_of_nonneg_right (by linarith) hβR.le
    have k2 : a * Real.log N ≤ K * Real.log N := mul_le_mul_of_nonneg_right (by linarith) hlogN
    have e : a * (2 * (β + (5 * βR + E + c)) + Real.log N) =
        2 * a * (β + E + c) + 10 * a * βR + a * Real.log N := by ring
    have e2 : K * (1 + βR + Real.log N) = K + K * βR + K * Real.log N := by ring
    linarith
  refine ⟨hb0, hbd, fun h2 => ?_⟩
  have hlog : Real.log ((L : ℝ) ^ N) = N * Real.log L := Real.log_pow (L : ℝ) N
  have hlL : Real.log L = 2 * Real.pi / 3 * β := by
    have := ct_log_div_betaL M.ct_L2
    rw [← hβd, div_eq_iff hβ.ne'] at this
    rw [this]
  rw [hlog]
  exact ct_theta_arith hβR hb0 hβ (by linarith) hlL hbd h2

/-- A bracket point at horizon `N` (for sequences): `N ≥ N₀`, master parameters `R`, a mass
`m² > 0` in the window `4m²L^{2N} ≤ 1/β_R`, and `b` in the bracket. -/
def CtPt {L : ℕ} [NeZero L] (M : MasterFacts L) (N₀ : ℕ) (βR : ℝ) (N : ℕ) (b : ℝ) : Prop :=
  N₀ ≤ N ∧ ∃ (R : RGPar 2 L N) (_ : Fact (0 < R.ℓ)) (_ : Fact (0 < R.A)), R.P = Pc ∧ R.i₀ = 0 ∧
    R.ℓ = M.core.ℓ ∧ R.A = M.core.A ∧ R.ρ = M.core.ρ ∧
    ∃ m : ℝ, 0 < m ∧ 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR ∧ b ∈ ctBracket M R m βR

theorem ct_rate_tendsto (c : ℝ) :
    Tendsto (fun x : ℝ => (c + Real.log x) / x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa [add_div] using h1.add h2

/-- **`thm:limit`, `ϑ_ε` along sequences**: for fixed `β_R` with `1/β_R ≤ g₀`, along any
`N_k → ∞` and bracket points `b_k` (`CtPt`, eventually), `ϑ_ε²(log L^{N_k})^{2/3} → (2πβ_R/3)^{2/3}`. -/
theorem thm_theta_eps_tendsto : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∀ (Nk : ℕ → ℕ) (bk : ℕ → ℝ), Tendsto Nk atTop atTop →
      (∀ᶠ k in atTop, CtPt M N₀ βR (Nk k) (bk k)) →
      Tendsto (fun k => thetaEpsSq βR (bk k) * Real.log ((L : ℝ) ^ (Nk k)) ^ (2 / 3 : ℝ)) atTop
        (𝓝 (thetaStar βR)) := by
  obtain ⟨L₀, h⟩ := thm_theta_eps
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, N₀, hg, hK, hF⟩ := h L hL
  refine ⟨M, g₀, N₀, hg, fun βR hβR hy Nk bk hNk hpt => ?_⟩
  have hβ := ct_betaL_pos M.ct_L2
  have hN : Tendsto (fun k => ((Nk k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNk
  have hr := (ct_rate_tendsto (1 + βR)).comp hN
  have hz : 0 ≤ thetaStar βR := by unfold thetaStar; positivity
  have hrhs : Tendsto (fun k => thetaStar βR * (2 * K * (((1 + βR) + Real.log (Nk k)) /
      (Nk k)) / betaL L)) atTop (𝓝 0) := by
    have := ((hr.const_mul (2 * K)).div_const (betaL L)).const_mul (thetaStar βR)
    simpa using this
  have hsmall : ∀ᶠ k in atTop, 2 * K * (((1 + βR) + Real.log (Nk k)) / (Nk k)) ≤ betaL L := by
    have := (hr.const_mul (2 * K)).eventually
      (gt_mem_nhds (show 2 * K * 0 < betaL L by simpa using hβ))
    filter_upwards [this] with k hk
    exact hk.le
  have hpos : ∀ᶠ k in atTop, (1 : ℝ) ≤ Nk k := hN.eventually_ge_atTop 1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hrhs
  filter_upwards [hpt, hsmall, hpos] with k hk hs hp
  obtain ⟨hN₀, R, _, _, hP, hi0, hRℓ, hRA, hRρ, m, hm, hmass, hb⟩ := hk
  have hNp : (0 : ℝ) < Nk k := by linarith
  have h2 : 2 * (K * (1 + βR + Real.log (Nk k))) ≤ (Nk k) * betaL L := by
    rw [mul_div_assoc', div_le_iff₀ hNp] at hs
    linarith
  have := ((hF (Nk k) R hP hi0 hRℓ hRA hRρ hN₀ m βR hm hβR hmass hy (bk k) hb).2.2 h2)
  rw [Real.norm_eq_abs]
  refine this.trans (le_of_eq ?_)
  field_simp
