import Flow2.FixedRParamZ2

/-!
# The numerical conditions with a hidden coupling are satisfiable

* `monoCoef_of_small_x`: a copy of `monoCoef_of_small` (`Flow2/Mono.lean`) that also returns the
  explicit cone constants and `c ≤ (1-κ)/2`;
* `monoZCoef_of_small`: `MonoZCoef` for small `a`, given `Λ > 1`, `0 ≤ κ < 1`, `A, A_ζ, b_ζ ≥ 0`
  and `0 < w < 1`. The `μ`-cone uses `monoCoef_of_small_x` at the larger constant
  `A* = A + 2(b_ζ+1)(A_ζ+1)` (so that `A_ζ p` and `b_ζ s` with `s = 2(A_ζ+1)p` fit into the slack),
  and `z₂ = 2(2A_ζ+1)`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

/-- **`MonoCoef` holds for small `a`**: given `Λ > 1`, `0 ≤ κ < 1`, `A ≥ 0` and the memory
factor `0 < w < 1`, there is `a₁ > 0` such that for `0 ≤ a ≤ a₁` the conditions hold with
`p = (Λ-1)/(8(A+1))`, `q = 4a(p+1)/(1-κ)`, `r = 1+p+q`, `p₂ = 4/p`, `q₂ = 2a(3+2p₂)/(1-κ)`,
`r₂ = 2+p₂`. -/
theorem monoCoef_of_small_x {Λ κ A w : ℝ} (hΛ : 1 < Λ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hA : 0 ≤ A)
    (hw1 : w < 1) :
    ∃ a₁ > 0, ∀ a, 0 ≤ a → a ≤ a₁ → ∃ p q r p₂ q₂ r₂ : ℝ, MonoCoef Λ κ A a w p q r p₂ q₂ r₂ ∧
      p = (Λ - 1) / (8 * (A + 1)) ∧ q = 4 * a * (p + 1) / (1 - κ) ∧ r = 1 + p + q ∧
      p₂ = 4 / p ∧ q₂ = 2 * a * (3 + 2 * p₂) / (1 - κ) ∧ r₂ = 2 + p₂ ∧
      a ≤ (1 - κ) / 2 ∧ cLoss A a p₂ q₂ r₂ ≤ (1 - κ) / 2 := by
  obtain ⟨s, hsd⟩ : ∃ s, s = 1 - κ := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsd]; linarith
  obtain ⟨p, hpd⟩ : ∃ p, p = (Λ - 1) / (8 * (A + 1)) := ⟨_, rfl⟩
  have hp : 0 < p := by rw [hpd]; have := sub_pos.2 hΛ; positivity
  have hAp : A * p ≤ (Λ - 1) / 8 := by
    rw [hpd, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have := sub_pos.2 hΛ
    nlinarith
  obtain ⟨P, hPd⟩ : ∃ P, P = p + 1 := ⟨_, rfl⟩
  have hP : 0 < P := by rw [hPd]; linarith
  obtain ⟨p₂, hp₂d⟩ : ∃ p₂, p₂ = 4 / p := ⟨_, rfl⟩
  have hp₂ : 0 < p₂ := by rw [hp₂d]; positivity
  have hp₂p : p₂ * p = 4 := by rw [hp₂d]; field_simp
  obtain ⟨K, hKd⟩ : ∃ K, K = 3 + 2 * p₂ := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; linarith
  obtain ⟨B, hBd⟩ : ∃ B, B = 1 + 2 * A / s := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hBd]; positivity
  -- the bounds `a X_i ≤ Y_i`
  obtain ⟨X3, hX3⟩ : ∃ X, X = P * (2 + 4 * (A + 1) / s) := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ X, X = (2 + p) + 4 * P * (A + 1) / s := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ X, X = 2 * K / s + K * B * (2 + p₂) := ⟨_, rfl⟩
  have hX3p : 0 < X3 := by rw [hX3]; positivity
  have hX4p : 0 < X4 := by rw [hX4]; positivity
  have hX7p : 0 < X7 := by rw [hX7]; positivity
  have hKB : 0 < K * B := mul_pos hK hB
  have hY3 : 0 < p * (Λ - 1) / 2 := by have := sub_pos.2 hΛ; positivity
  have hY4 : 0 < 3 / 8 * (Λ - 1) := by have := sub_pos.2 hΛ; positivity
  refine ⟨min (min (s / 2) 1) (min (p * (Λ - 1) / 2 / X3) (min (3 / 8 * (Λ - 1) / X4)
    (min (s / 2 / (K * B)) (min ((1 - w) / (K * B)) (1 / X7))))), ?_, ?_⟩
  · have : 0 < 1 - w := by linarith
    refine lt_min (lt_min (by positivity) one_pos) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  intro a ha ha₁
  have h1 : a ≤ s / 2 := ha₁.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : a ≤ 1 := ha₁.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : a * X3 ≤ p * (Λ - 1) / 2 :=
    mul_le_of_le_div' hX3p (ha₁.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h4 : a * X4 ≤ 3 / 8 * (Λ - 1) := mul_le_of_le_div' hX4p
    (ha₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have h5 : a * (K * B) ≤ s / 2 := mul_le_of_le_div' hKB (ha₁.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have h6 : a * (K * B) ≤ 1 - w := mul_le_of_le_div' hKB (ha₁.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))))
  have h7 : a * X7 ≤ 1 := mul_le_of_le_div' hX7p (ha₁.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))))
  -- the cone constants
  obtain ⟨q, hqd⟩ : ∃ q, q = 4 * a * P / s := ⟨_, rfl⟩
  obtain ⟨q₂, hq₂d⟩ : ∃ q₂, q₂ = 2 * a * K / s := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqd]; positivity
  have hq₂0 : 0 ≤ q₂ := by rw [hq₂d]; positivity
  have hqs : q * s = 4 * a * P := by rw [hqd]; field_simp
  have hq₂s : q₂ * s = 2 * a * K := by rw [hq₂d]; field_simp
  have hcl : cLoss A a p₂ q₂ (2 + p₂) = a * (K * B) := by
    unfold cLoss; rw [hq₂d, hKd, hBd]; field_simp; ring
  have hκq : κ * q = q - q * s := by rw [hsd]; ring
  have hκq₂ : κ * q₂ = q₂ - q₂ * s := by rw [hsd]; ring
  have hqA : a * X3 = 2 * a * P + q * (A + 1) := by rw [hX3, hqd]; field_simp
  have hqA4 : a * X4 = a * (2 + p) + q * (A + 1) := by rw [hX4, hqd]; field_simp
  have hqa : q * (A + a) ≤ q * (A + 1) := mul_le_mul_of_nonneg_left (by linarith) hq0
  have hqP : q ≤ 2 * P := by
    have : q * s ≤ 2 * P * s := by
      rw [hqs]; have := mul_le_mul_of_nonneg_right h1 hP.le; nlinarith
    exact le_of_mul_le_mul_right this hs
  have haq : a * q ≤ a * (2 * P) := mul_le_mul_of_nonneg_left hqP ha
  refine ⟨p, q, 1 + p + q, p₂, q₂, 2 + p₂, ⟨⟨hκ0, hA, ha, hp, hq0, le_rfl, ?_, ?_, ?_, hΛ.le,
    by rw [hp₂p]; norm_num, ?_, ?_, hq₂0, by linarith, ?_, ?_, ?_, ?_⟩, hpd,
    by rw [hqd, hPd, hsd], rfl, hp₂d, by rw [hq₂d, hKd, hsd], rfl, by rw [← hsd]; exact h1,
    by rw [hcl, ← hsd]; exact h5⟩⟩
  · -- eg
    have e : (1 + a) * p + a + A * q + a * (1 + p + q) = p + (2 * a * P + q * (A + a)) := by
      rw [hPd]; ring
    rw [e]
    have e2 : p * ((1 + Λ) / 2) = p + p * (Λ - 1) / 2 := by ring
    rw [e2]
    linarith only [h3, hqA, hqa]
  · -- ex
    rw [hκq]
    have e : a * (p + 1) + a * (1 + p + q) = 2 * a * P + a * q := by rw [hPd]; ring
    linarith only [e, haq, hqs]
  · -- em
    have e : A * p + a + A * q + a * (1 + p + q) = A * p + (a * (2 + p) + q * (A + a)) := by ring
    rw [e]
    linarith only [hAp, h4, hqA4, hqa]
  · -- hq₂
    have e : p₂ * q - q₂ = 10 * a / s := by
      rw [hqd, hq₂d, hKd, hPd]; field_simp; rw [hp₂d]; field_simp; ring
    have : 0 ≤ 10 * a / s := by positivity
    linarith
  · -- hr₂
    have e : p₂ * (1 + p + q) = p₂ + p₂ * p + p₂ * q := by ring
    rw [e, hp₂p]
    have := mul_nonneg hp₂.le hq0
    linarith
  · -- hc
    rw [hcl]; linarith
  · -- hx
    rw [hcl, hκq₂]
    have e : a * (1 + p₂) + a * (2 + p₂) = a * K := by rw [hKd]; ring
    have hc2 : q₂ * (a * (K * B)) ≤ q₂ * (s / 2) := mul_le_mul_of_nonneg_left h5 hq₂0
    have e2 : q₂ * (s / 2) = a * K := by linarith only [hq₂s]
    linarith only [e, hc2, e2, hq₂s]
  · -- hrr
    rw [hcl]
    have e : a * X7 = q₂ + a * (K * B) * (2 + p₂) := by rw [hX7, hq₂d]; field_simp
    linarith only [h7, e]
  · -- hw
    rw [hcl]; linarith

/-- **`MonoZCoef` holds for small `a`.** -/
theorem monoZCoef_of_small {Λ κ A Aζ bζ w : ℝ} (hΛ : 1 < Λ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hA : 0 ≤ A) (hAζ : 0 ≤ Aζ) (hbζ : 0 ≤ bζ) (hw1 : w < 1) :
    ∃ a₁ > 0, ∀ a, 0 ≤ a → a ≤ a₁ →
      ∃ p q r s p₂ q₂ r₂ z₂ : ℝ, MonoZCoef Λ κ A a Aζ bζ w p q r s p₂ q₂ r₂ z₂ := by
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
  refine ⟨p, q, r, 2 * (Aζ + 1) * p, p₂, q₂, r₂, 2 * (2 * Aζ + 1), ?_⟩
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
