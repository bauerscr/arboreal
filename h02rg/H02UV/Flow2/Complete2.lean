import Flow2.FixedRParamZ3

/-!
# The cone at the horizon, and explicit cone constants

* `traj_cone_top_z`: the conclusion of the proof of `traj_strict_mono_z` at the horizon `N`
  itself: for `b < b'` with admissible trajectories `v, u`, `e = ǧ_N(u) - ǧ_N(v) > 0`,
  `‖δx_N‖ ≤ q₂ e`, `h_max(N) ≤ r₂ e` (the weighted past), `‖δZ_N‖ ≤ z₂ e`, `|δμ_N| ≤ p₂ e`.
  This is the input for one more step (the step `N - 2` of the RG, under `ValidAtL`).
* `monoZCoef_of_small_b`: `monoZCoef_of_small` with the explicit constants
  `p₂ = 32(A + 2(b_ζ+1)(A_ζ+1) + 1)/(Λ-1)`, `r₂ = 2 + p₂`, `z₂ = 2(2A_ζ+1)`, `q₂ ≤ 1`
  (independent of `a`).
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {E : Type*} [NormedAddCommGroup E]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

section Two

variable {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ bζ ε w : ℝ}
  (H : HHyp F Λ β δ κ cg cm cT N A' a' ε)
  (HM : MonoZHyp F Λ β δ κ cg cm cT N Z A a Aζ bζ ε w)
include H HM

/-- **The `ǧ`-cone at the horizon** (the proof of `traj_strict_mono_z`). -/
theorem traj_cone_top_z {p q r s p₂ q₂ r₂ z₂ : ℝ}
    (hC : MonoZCoef Λ κ A a Aζ bζ w p q r s p₂ q₂ r₂ z₂)
    {b b' μ μ' : ℝ} (hbb : b < b') (h : Admissible F Λ κ cm cT N ε b μ)
    (h' : Admissible F Λ κ cm cT N ε b' μ') :
    0 < (traj F Λ b' μ' N).1 - (traj F Λ b μ N).1 ∧
      ‖(traj F Λ b' μ' N).2.2 - (traj F Λ b μ N).2.2‖ ≤
        q₂ * ((traj F Λ b' μ' N).1 - (traj F Λ b μ N).1) ∧
      hmax w (traj F Λ b' μ') (traj F Λ b μ) N ≤
        r₂ * ((traj F Λ b' μ' N).1 - (traj F Λ b μ N).1) ∧
      ‖Z N (traj F Λ b' μ') - Z N (traj F Λ b μ)‖ ≤
        z₂ * ((traj F Λ b' μ' N).1 - (traj F Λ b μ N).1) ∧
      |(traj F Λ b' μ' N).2.1 - (traj F Λ b μ N).2.1| ≤
        p₂ * ((traj F Λ b' μ' N).1 - (traj F Λ b μ N).1) := by
  set u := traj F Λ b' μ'
  set v := traj F Λ b μ
  have hp := hC.hp
  have hq := hC.hq
  -- outside the `μ`-cone
  have hout : ∀ k ≤ N, 0 < (u k).1 - (v k).1 → ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1) →
      hmax w u v k ≤ r₂ * ((u k).1 - (v k).1) → ‖Z k u - Z k v‖ ≤ z₂ * ((u k).1 - (v k).1) →
      |(u k).2.1 - (v k).2.1| ≤ p₂ * ((u k).1 - (v k).1) := by
    intro k hk he hx hh hz
    by_contra hn
    push Not at hn
    set e := (u k).1 - (v k).1
    set m := |(u k).2.1 - (v k).2.1|
    refine not_mu_cone_z H HM hC.hΛ hC.hκ0 hp.le hq hC.hr hC.hs0 hC.eg hC.ex hC.em hC.esz hbb.ne
      h h' hk ?_ ?_ ?_ ?_
    · show |e| ≤ p * m
      rw [abs_of_pos he]
      have h1 := mul_le_mul_of_nonneg_right hC.hp₂ he.le
      have h2 : p₂ * e * p < m * p := mul_lt_mul_of_pos_right hn hp
      linarith only [h1, h2]
    · show ‖(u k).2.2 - (v k).2.2‖ ≤ q * m
      refine hx.trans ?_
      have h1 : q₂ * e ≤ p₂ * q * e := mul_le_mul_of_nonneg_right hC.hq₂ he.le
      have h2 : p₂ * e * q ≤ m * q := mul_le_mul_of_nonneg_right hn.le hq
      linarith only [h1, h2]
    · show hmax w u v k ≤ r * m
      refine hh.trans ?_
      have hr0 : 0 ≤ r := by linarith [hC.hr]
      have h1 : r₂ * e ≤ p₂ * r * e := mul_le_mul_of_nonneg_right hC.hr₂ he.le
      have h2 : p₂ * e * r ≤ m * r := mul_le_mul_of_nonneg_right hn.le hr0
      linarith only [h1, h2]
    · show ‖Z k u - Z k v‖ ≤ s * m
      refine hz.trans ?_
      have h1 : z₂ * e ≤ p₂ * s * e := mul_le_mul_of_nonneg_right hC.hz₂ he.le
      have h2 : p₂ * e * s ≤ m * s := mul_le_mul_of_nonneg_right hn.le hC.hs0
      linarith only [h1, h2]
  -- the `ǧ`-cone
  have key : ∀ k ≤ N, 0 < (u k).1 - (v k).1 ∧
      ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1) ∧
      hmax w u v k ≤ r₂ * ((u k).1 - (v k).1) ∧
      ‖Z k u - Z k v‖ ≤ z₂ * ((u k).1 - (v k).1) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [u, v, traj_zero, sub_self, norm_zero, hmax]
      refine ⟨by linarith, ?_, ?_, ?_⟩
      · exact mul_nonneg hC.hq₂0 (by linarith)
      · exact mul_nonneg hC.hr₂0 (by linarith)
      · rw [HM.Z0 (traj F Λ b' μ') (traj F Λ b μ), sub_self, norm_zero]
        exact mul_nonneg hC.hz₂0 (by linarith)
    | succ k ih =>
      intro hk
      have hlt : k < N := by omega
      obtain ⟨ie, ix, ih', iz⟩ := ih (by omega)
      have im := hout k hlt.le ie ix ih' iz
      obtain ⟨s1, s2, s3, s4, s5⟩ := g_cone_step_z HM hC.hκ0 hC.hc hC.hx hC.hrr hC.hw hC.hq₂0
        hC.hr₂0 hC.hz₂0 hC.hzz hlt (admissible_InDh H h' k hlt.le) (admissible_InDh H h k hlt.le)
        ie im ix ih'
      have e0 := traj_succ H b' μ' hlt
      have e1 := traj_succ H b μ hlt
      have hc0 : 0 < 1 - cLoss A a p₂ q₂ r₂ := by linarith [hC.hc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [u, v] at e0 e1 s1 ⊢; rw [e0, e1]
        exact lt_of_lt_of_le (mul_pos hc0 ie) s1
      · simp only [u, v] at e0 e1 s2 ⊢; rw [e0, e1]; exact s2
      · refine hmax_succ_le u v k ?_ ?_
        · simp only [u, v] at e0 e1 s3 ⊢; rw [e0, e1]; exact s3
        · simp only [u, v] at e0 e1 s4 ⊢; rw [e0, e1]; exact s4
      · simp only [u, v] at e0 e1 s5 ⊢; rw [e0, e1]; exact s5
  obtain ⟨k1, k2, k3, k4⟩ := key N le_rfl
  exact ⟨k1, k2, k3, k4, hout N le_rfl k1 k2 k3 k4⟩

end Two

/-- **`MonoZCoef` holds for small `a`.** -/
theorem monoZCoef_of_small_b {Λ κ A Aζ bζ w : ℝ} (hΛ : 1 < Λ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hA : 0 ≤ A) (hAζ : 0 ≤ Aζ) (hbζ : 0 ≤ bζ) (hw1 : w < 1) :
    ∃ a₁ > 0, ∀ a, 0 ≤ a → a ≤ a₁ →
      ∃ p q r s p₂ q₂ r₂ z₂ : ℝ, MonoZCoef Λ κ A a Aζ bζ w p q r s p₂ q₂ r₂ z₂ ∧
        p₂ = 32 * (A + 2 * (bζ + 1) * (Aζ + 1) + 1) / (Λ - 1) ∧ r₂ = 2 + p₂ ∧
        z₂ = 2 * (2 * Aζ + 1) ∧ q₂ ≤ 1 := by
  obtain ⟨As, hAsd⟩ : ∃ As, As = A + 2 * (bζ + 1) * (Aζ + 1) := ⟨_, rfl⟩
  have hAs : 0 ≤ As := by rw [hAsd]; positivity
  have hAAs : A ≤ As := by rw [hAsd]; have : 0 ≤ 2 * (bζ + 1) * (Aζ + 1) := by positivity
                           linarith
  obtain ⟨a₁, ha₁, hcoef⟩ := monoCoef_of_small_x hΛ hκ0 hκ1 hAs hw1
  obtain ⟨p, hpd⟩ : ∃ p, p = (Λ - 1) / (8 * (As + 1)) := ⟨_, rfl⟩
  have hp : 0 < p := by rw [hpd]; have := sub_pos.2 hΛ; positivity
  obtain ⟨sk, hskd⟩ : ∃ sk, sk = 1 - κ := ⟨_, rfl⟩
  have hsk : 0 < sk := by rw [hskd]; linarith
  obtain ⟨X8, hX8⟩ : ∃ X, X = 4 * Aζ * (p + 1) / sk + 2 + p + 2 * (p + 1) := ⟨_, rfl⟩
  have hX8p : 0 < X8 := by rw [hX8]; positivity
  obtain ⟨X9, hX9⟩ : ∃ X, X = 2 * (3 + 2 * (4 / p)) / sk + 2 + 2 * (4 / p) := ⟨_, rfl⟩
  have hX9p : 0 < X9 := by rw [hX9]; positivity
  refine ⟨min a₁ (min (p / X8) (1 / X9)), lt_min ha₁ (lt_min (by positivity) (by positivity)),
    fun a ha haa => ?_⟩
  have h1 : a ≤ a₁ := haa.trans (min_le_left _ _)
  have h8 : a * X8 ≤ p := mul_le_of_le_div' hX8p (haa.trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have h9 : a * X9 ≤ 1 := mul_le_of_le_div' hX9p (haa.trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  obtain ⟨p', q, r, p₂, q₂, r₂, hC, hp', hq, hr, hp₂, hq₂, hr₂, has, hcl⟩ := hcoef a ha h1
  rw [← hpd] at hp'
  subst p'
  have hq0 := hC.hq
  have hcA : cLoss A a p₂ q₂ r₂ ≤ cLoss As a p₂ q₂ r₂ := by
    unfold cLoss
    have := mul_le_mul_of_nonneg_right hAAs hC.hq₂0
    linarith
  have hc2 : cLoss As a p₂ q₂ r₂ ≤ 1 / 2 := hcl.trans (by linarith)
  have hcA0 : 0 ≤ cLoss A a p₂ q₂ r₂ := by
    unfold cLoss
    have := mul_nonneg ha (show 0 ≤ p₂ by rw [hp₂]; positivity)
    have := mul_nonneg hA hC.hq₂0
    have := mul_nonneg ha hC.hr₂0
    linarith
  -- `q ≤ 2(p+1)`, `q₂ ≤ 1`
  have hqP : q ≤ 2 * (p + 1) := by
    rw [hq, div_le_iff₀ (by linarith)]
    have : a * (p + 1) ≤ (1 - κ) / 2 * (p + 1) :=
      mul_le_mul_of_nonneg_right has (by linarith)
    linarith
  have hAq : Aζ * q ≤ a * (4 * Aζ * (p + 1) / sk) := by
    rw [hq, ← hskd]
    have e : Aζ * (4 * a * (p + 1) / sk) = a * (4 * Aζ * (p + 1) / sk) := by ring
    rw [e]
  have hq₂1 : q₂ ≤ 1 := by
    have e : q₂ = a * (2 * (3 + 2 * (4 / p)) / sk) := by rw [hq₂, hp₂, hskd]; ring
    have : a * (2 * (3 + 2 * (4 / p)) / sk) ≤ a * X9 := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      rw [hX9]
      have : 0 ≤ 2 * (4 / p) := by positivity
      linarith
    linarith
  have hap : a * (p₂ + r₂) ≤ 1 := by
    rw [hr₂, hp₂]
    have : a * (4 / p + (2 + 4 / p)) ≤ a * X9 := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      rw [hX9]
      have : 0 ≤ 2 * (3 + 2 * (4 / p)) / sk := by positivity
      linarith
    linarith
  refine ⟨p, q, r, 2 * (Aζ + 1) * p, p₂, q₂, r₂, 2 * (2 * Aζ + 1), ?_, ?_, hr₂, rfl, hq₂1⟩
  rotate_left
  · rw [hp₂, hpd, hAsd, div_div_eq_mul_div]
    ring
  exact
    { hκ0 := hκ0, hp := hp, hq := hq0, hr := hC.hr, hs0 := by positivity
      eg := by
        have := mul_le_mul_of_nonneg_right hAAs hq0
        linarith [hC.eg]
      ex := hC.ex
      em := by
        have h1 := mul_le_mul_of_nonneg_right hAAs hq0
        have h2 : A * p + bζ * (2 * (Aζ + 1) * p) ≤ As * p := by
          rw [hAsd]
          have : 0 ≤ (2 * (Aζ + 1) * p) := by positivity
          nlinarith
        linarith [hC.em]
      esz := by
        rw [hr]
        have e8 : a * X8 = a * (4 * Aζ * (p + 1) / sk) + a * (2 + p + 2 * (p + 1)) := by
          rw [hX8]; ring
        have hqa : a * q ≤ a * (2 * (p + 1)) := mul_le_mul_of_nonneg_left hqP ha
        have := mul_nonneg hAζ hp.le
        linarith [hAq, hqa, h8, e8]
      hΛ := hC.hΛ, hp₂ := hC.hp₂, hq₂ := hC.hq₂, hr₂ := hC.hr₂
      hz₂ := by
        rw [hp₂]
        have e : 4 / p * (2 * (Aζ + 1) * p) = 8 * (Aζ + 1) := by field_simp; ring
        rw [e]; linarith
      hq₂0 := hC.hq₂0, hr₂0 := hC.hr₂0, hz₂0 := by positivity
      hc := lt_of_le_of_lt hcA hC.hc
      hx := by
        have := mul_le_mul_of_nonneg_left hcA hC.hq₂0
        linarith [hC.hx]
      hrr := by
        have := mul_le_mul_of_nonneg_left hcA hC.hr₂0
        linarith [hC.hrr]
      hw := by linarith [hC.hw]
      hzz := by
        have hc' : cLoss A a p₂ q₂ r₂ ≤ 1 / 2 := hcA.trans hc2
        have h1 : 2 * (2 * Aζ + 1) * (1 / 2) ≤ 2 * (2 * Aζ + 1) * (1 - cLoss A a p₂ q₂ r₂) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h2 : Aζ * q₂ ≤ Aζ * 1 := mul_le_mul_of_nonneg_left hq₂1 hAζ
        linarith [h1, h2, hap] }

end Hist

end Flow2
