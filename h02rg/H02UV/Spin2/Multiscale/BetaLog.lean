import Spin2.Multiscale.Flow

/-!
# `thm:beta`: `β_ε = N_h β_1 log L + O(log N_h)` along the admissible trajectories

From `BetaAsym` (`|β_n - β_ε + nβ| ≤ 2(1+β)e_R + C_gu((1/β) log(β_ε/β_n) + K'ǧ_n)`,
`β = β_1 log L`) at `n = N_h`, for a trajectory whose final coupling satisfies `β_{N_h} ≤ T`:

  `|β_ε - N_h β| ≤ D + a log(2(N_h β + D + a|log 2a|))`,  `D = T + E`, `a = C_gu/β`,

`E = 2(1+β)e_R + C_gu|K'|` (`beta_eps_log`, pure; `BetaLog`, `betaLog_of`). With `N_h = N - 2`
and the lattice spacing `ε_lat = L^{-N}` (`N log L = log(1/ε_lat)`) this is
`β_ε = (3/2π) log(1/ε_lat) + O(log log(1/ε_lat))` (constants depending on `L`, `T`).
-/

namespace Spin2

open Flow2 Flow2.Hist

/-- `a log B ≤ B/2 + a|log 2a|`. -/
theorem mul_log_le_half {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) :
    a * Real.log B ≤ B / 2 + a * |Real.log (2 * a)| := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_mul, add_zero]; linarith
  have h2a : 0 < 2 * a := by linarith
  have e : Real.log B = Real.log (2 * a) + Real.log (B / (2 * a)) := by
    rw [← Real.log_mul h2a.ne' (div_pos hB h2a).ne']; congr 1; field_simp
  have h1 := Real.log_le_sub_one_of_pos (div_pos hB h2a)
  have h2 : a * Real.log (B / (2 * a)) ≤ a * (B / (2 * a) - 1) := mul_le_mul_of_nonneg_left h1 ha
  have h3 : a * (B / (2 * a) - 1) = B / 2 - a := by field_simp
  have h4 : a * Real.log (2 * a) ≤ a * |Real.log (2 * a)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) ha
  rw [e, mul_add]
  linarith

/-- **The summed band inverted** (pure): if `|1/g - 1/b + x| ≤ E + a log(g/b)` with `0 < g ≤ 1`,
`1/g ≤ T`, then `|1/b - x| ≤ (T + E) + a log(2(x + T + E + a|log 2a|))`. -/
theorem beta_eps_log {b g x E a T : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g ≤ 1) (hT : 1 / g ≤ T)
    (ha : 0 ≤ a) (hE : 0 ≤ E) (hx : 0 ≤ x)
    (h : |1 / g - 1 / b + x| ≤ E + a * Real.log (g / b)) :
    |1 / b - x| ≤ (T + E) + a * Real.log (2 * (x + (T + E) + a * |Real.log (2 * a)|)) := by
  set B := 1 / b with hBd
  set Bn := 1 / g with hBnd
  have hB : 0 < B := by positivity
  have hBn : 1 ≤ Bn := by rw [hBnd, le_div_iff₀ hg]; linarith
  have hgb : g / b = B / Bn := by rw [hBd, hBnd]; field_simp
  rw [hgb] at h
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have hT1 : 1 ≤ T := hBn.trans hT
  have hA0 : 0 ≤ a * |Real.log (2 * a)| := mul_nonneg ha (abs_nonneg _)
  have hlogpos : 0 ≤ Real.log (2 * (x + (T + E) + a * |Real.log (2 * a)|)) :=
    Real.log_nonneg (by linarith)
  have hl0 : 0 ≤ a * Real.log (2 * (x + (T + E) + a * |Real.log (2 * a)|)) :=
    mul_nonneg ha hlogpos
  rcases le_or_gt B Bn with hle | hlt
  · -- `log(B/Bn) ≤ 0`
    have hl : Real.log (B / Bn) ≤ 0 :=
      Real.log_nonpos (by positivity) ((div_le_one (by linarith)).2 hle)
    have hal : a * Real.log (B / Bn) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hl
    rw [abs_le]; constructor <;> linarith
  · have hBn0 : 0 < Bn := by linarith
    have hlB : Real.log (B / Bn) ≤ Real.log B := by
      rw [Real.log_div hB.ne' hBn0.ne']; linarith [Real.log_nonneg hBn]
    have hl0' : 0 ≤ Real.log (B / Bn) := Real.log_nonneg ((one_le_div hBn0).2 hlt.le)
    have h3 : a * Real.log (B / Bn) ≤ a * Real.log B := mul_le_mul_of_nonneg_left hlB ha
    have h4 : 0 ≤ a * Real.log (B / Bn) := mul_nonneg ha hl0'
    have h5 := mul_log_le_half ha hB
    have hBup : B ≤ 2 * (x + (T + E) + a * |Real.log (2 * a)|) := by linarith
    have h6 : Real.log B ≤ Real.log (2 * (x + (T + E) + a * |Real.log (2 * a)|)) :=
      Real.log_le_log hB hBup
    have h7 := mul_le_mul_of_nonneg_left h6 ha
    rw [abs_le]; constructor <;> linarith

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]

/-- The constant `E` of `BetaLog`. -/
noncomputable def betaLogE (β cg eR : ℝ) : ℝ :=
  2 * (1 + β) * eR + Cgu β cg * |betaAsymK β cg eR|

/-- **`thm:beta`, `β_ε` vs the horizon**: along every admissible trajectory with
`β_N = 1/ǧ_N ≤ T`, `|β_ε - Nβ| ≤ D + a log(2(Nβ + D + a|log 2a|))`, `D = T + E`, `a = C_gu/β`. -/
def BetaLog (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε eR : ℝ) : Prop :=
  ∀ b μ₀, Admissible F Λ κ cm cT N ε b μ₀ → ∀ T : ℝ, 1 / (traj F Λ b μ₀ N).1 ≤ T →
    |1 / b - N * β| ≤ (T + betaLogE β cg eR) + Cgu β cg / β *
      Real.log (2 * (N * β + (T + betaLogE β cg eR) +
        Cgu β cg / β * |Real.log (2 * (Cgu β cg / β))|))

theorem betaLog_of {F : HData X} {Λ β κ cg cm cT ε eR : ℝ} {N : ℕ} (hβ : 0 < β) (hcg : 0 ≤ cg)
    (heR : 0 ≤ eR) (hε1 : ε ≤ 1) (hBA : BetaAsym F Λ β κ cg cm cT N ε eR) :
    BetaLog F Λ β κ cg cm cT N ε eR := by
  intro b μ₀ hadm T hT
  set g := (traj F Λ b μ₀ N).1 with hgd
  have hg : 0 < g := (hadm.1 N le_rfl).1
  have hg1 : g ≤ 1 := ((hadm.1 N le_rfl).2.1).trans hε1
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; rwa [Hist.traj_zero] at this
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  have h := hBA b μ₀ hadm N le_rfl
  rw [← hgd] at h
  have hK : betaAsymK β cg eR * g ≤ |betaAsymK β cg eR| :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hg.le).trans
      (mul_le_of_le_one_right (abs_nonneg _) hg1)
  have hK' := mul_le_mul_of_nonneg_left hK hCgu
  have h' : |1 / g - 1 / b + N * β| ≤ betaLogE β cg eR + Cgu β cg / β * Real.log (g / b) := by
    refine h.trans ?_
    unfold betaLogE
    have e : Cgu β cg * (1 / β * Real.log (g / b) + betaAsymK β cg eR * g) =
        Cgu β cg / β * Real.log (g / b) + Cgu β cg * (betaAsymK β cg eR * g) := by ring
    rw [e]; linarith
  have hE : 0 ≤ betaLogE β cg eR := by unfold betaLogE; positivity
  exact beta_eps_log hb hg hg1 hT (div_nonneg hCgu hβ.le) hE (by positivity) h'

end Spin2
