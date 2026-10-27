import Step2.Flow.ZetaSharp0
import Step2.Flow.FlowSharp1

/-!
# Summing against `log ǧ` along admissible trajectories (abstract flow)

`log_traj`: for a flow with `HHyp` (band `δ = 1/2`), the sharp (F1)
`|G_j - g_j - β g_j²| ≤ e_j g_j² + c_g g_j³` (`e_j ≤ β/2`), `c_g ε ≤ β/4`, `ε ≤ 1`, and any
admissible trajectory: if a quantity `y` satisfies
`|y_{k+1} - y_k - (p_{k+1} - p_k) + σ ǧ_k| ≤ A ǧ_k² + A ǧ_k a_k` for `k < N`, then for `n ≤ N`

  `|y_n - y_0 - (p_n - p_0) + (σ/β) log(ǧ_n/b)| ≤ K_n ǧ_n`,
  `K_n = (A + (|σ|/β)(M B₁² + c))/(β/4) + ∑_{k<n} (A a_k + (|σ|/β) 2(1+β) e_k)`,

`M = 1 + 3β/2 + c_g`, `c = C_gu(β, c_g)`, `B₁ = β + (1+β)β + c`. The inputs of
`log_sum_bound`: monotonicity `ǧ_{k+1} ≥ ǧ_k + (β/4)ǧ_k²` and `ǧ_{k+1} ≤ M ǧ_k` from the band
(F1) of `HHyp`, the `1/ǧ` form of the sharp (F1) from `ginv_sharp`.
-/

open Finset

namespace Flow2.Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {F : HData X} {Λ β κ cg cm cT : ℝ}

/-- The constant of `log_traj`. -/
noncomputable def logTrajK (β cg A s : ℝ) : ℝ :=
  (A + s * ((1 + 3 / 2 * β + cg) * (β + (1 + β) * β + Cgu β cg) ^ 2 + Cgu β cg)) / (β / 4)

theorem log_trajD {N : ℕ} {A0 a0 ε : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    {y p a : ℕ → ℝ} {A σ : ℝ} (hA : 0 ≤ A) (ha : ∀ k, 0 ≤ a k)
    {b μ₀ : ℝ} (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j))
    (hy : ∀ k < N, |y (k + 1) - y k - (p (k + 1) - p k) + σ * (traj F Λ b μ₀ k).1| ≤
      A * (traj F Λ b μ₀ k).1 ^ 2 + A * (traj F Λ b μ₀ k).1 * a k) :
    ∀ n ≤ N, |y n - y 0 - (p n - p 0) + σ / β * Real.log ((traj F Λ b μ₀ n).1 / b)| ≤
      (logTrajK β cg A (|σ| / β) +
        ∑ k ∈ range n, (A * a k + |σ| / β * (2 * (1 + β) * e k))) * (traj F Λ b μ₀ n).1 := by
  intro n hn
  have hβ := H.hβ
  have hcg := H.hcg
  set g : ℕ → ℝ := fun k => (traj F Λ b μ₀ k).1 with hgd
  have hD := traj_InDh_of H h
  have hg : ∀ k ≤ n, 0 < g k := fun k hk => ((hD k (by omega)).1 k le_rfl).1
  have hg1 : ∀ k < n, g k ≤ 1 := fun k hk => (((hD k (by omega)).1 k le_rfl).2.1).trans hε1
  have hgε : ∀ k < n, g k ≤ ε := fun k hk => ((hD k (by omega)).1 k le_rfl).2.1
  -- the band (F1) at the trajectory
  have hF1 : ∀ k < n, |g (k + 1) - g k - β * g k ^ 2| ≤ 1 / 2 * β * g k ^ 2 + cg * g k ^ 3 := by
    intro k hk
    have := H.F1 k (by omega) _ (hD k (by omega))
    simp only [hgd]
    rw [traj_succ H b μ₀ (show k < N by omega)]
    exact this
  have hinc : ∀ k < n, g k + β / 4 * g k ^ 2 ≤ g (k + 1) := by
    intro k hk
    have h1 := (abs_le.1 (hF1 k hk)).1
    have hgk := hg k hk.le
    have h2 : cg * g k ≤ β / 4 := (mul_le_mul_of_nonneg_left (hgε k hk) hcg.le).trans hcgβ
    have h3 : cg * g k ^ 3 ≤ β / 4 * g k ^ 2 := by
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg (g k))
      have e : cg * g k ^ 3 = cg * g k * g k ^ 2 := by ring
      linarith only [this, e]
    linarith only [h1, h3]
  have hM : ∀ k < n, g (k + 1) ≤ (1 + 3 / 2 * β + cg) * g k := by
    intro k hk
    have h1 := (abs_le.1 (hF1 k hk)).2
    have hgk := hg k hk.le
    have hg1k := hg1 k hk
    have h2 : g k ^ 2 ≤ g k := by rw [sq]; exact mul_le_of_le_one_right hgk.le hg1k
    have h3 : g k ^ 3 ≤ g k := by
      have h6 := mul_le_mul_of_nonneg_right (pow_le_one₀ hgk.le hg1k (n := 2)) hgk.le
      have e : g k ^ 3 = g k ^ 2 * g k := by ring
      linarith only [h6, e]
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 3 / 2 * β)
    have h5 := mul_le_mul_of_nonneg_left h3 hcg.le
    linarith only [h1, h4, h5]
  -- the band in `1/g` form
  have hband : ∀ k < n, |1 / g (k + 1) - 1 / g k + β| ≤
      2 * (1 + β) * e k + Cgu β cg * g k := fun k hk =>
    ginv_sharpD H he h (show k < N by omega) (he0 k) hcg.le (F1s k (by omega))
  have he1 : ∀ k < n, 2 * (1 + β) * e k ≤ (1 + β) * β := by
    intro k hk
    have := mul_le_mul_of_nonneg_left (heb k (by omega)) (by positivity : (0 : ℝ) ≤ 2 * (1 + β))
    linarith only [this]
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  have hmain := Step2.log_sum_bound (g := g) (y := y) (p := p) (a := a)
    (e := fun k => 2 * (1 + β) * e k) (β := β) (β' := β / 4) (M := 1 + 3 / 2 * β + cg)
    (c := Cgu β cg) (E1 := (1 + β) * β) (A := A) (σ := σ) (n := n) hβ (by positivity) hCgu hA
    (by positivity) (by positivity) hg hg1 hinc hM
    (fun k hk => by show 0 ≤ 2 * (1 + β) * e k; have := he0 k; positivity) he1
    (fun k _ => ha k) hband
    (fun k hk => hy k (by omega))
  have hg0 : g 0 = b := by simp only [hgd, traj_zero]
  rw [hg0] at hmain
  unfold logTrajK
  exact hmain



/-- **The summation principle along the admissible trajectories** of a flow: every quantity
moving by `-σ ǧ_k` per step (up to a telescoping part and `A(ǧ_k² + ǧ_k a_k)`) is
`-(σ/β) log(ǧ_n/b) + O(ǧ_n)`. -/
def LogSum (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε eR : ℝ) : Prop :=
  ∀ b μ₀, Admissible F Λ κ cm cT N ε b μ₀ → ∀ (y p a : ℕ → ℝ) (A σ : ℝ), 0 ≤ A →
    (∀ k, 0 ≤ a k) →
    (∀ k < N, |y (k + 1) - y k - (p (k + 1) - p k) + σ * (traj F Λ b μ₀ k).1| ≤
      A * (traj F Λ b μ₀ k).1 ^ 2 + A * (traj F Λ b μ₀ k).1 * a k) →
    ∀ n ≤ N, |y n - y 0 - (p n - p 0) + σ / β * Real.log ((traj F Λ b μ₀ n).1 / b)| ≤
      (logTrajK β cg A (|σ| / β) + A * ∑ k ∈ range n, a k + |σ| / β * (2 * (1 + β) * eR)) *
        (traj F Λ b μ₀ n).1

/-- `LogSum` along every trajectory in `D_ε` up to `N` (no final condition; route (a1)). -/
def LogSumD (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε eR : ℝ) : Prop :=
  ∀ b μ₀, (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) → ∀ (y p a : ℕ → ℝ) (A σ : ℝ), 0 ≤ A →
    (∀ k, 0 ≤ a k) →
    (∀ k < N, |y (k + 1) - y k - (p (k + 1) - p k) + σ * (traj F Λ b μ₀ k).1| ≤
      A * (traj F Λ b μ₀ k).1 ^ 2 + A * (traj F Λ b μ₀ k).1 * a k) →
    ∀ n ≤ N, |y n - y 0 - (p n - p 0) + σ / β * Real.log ((traj F Λ b μ₀ n).1 / b)| ≤
      (logTrajK β cg A (|σ| / β) + A * ∑ k ∈ range n, a k + |σ| / β * (2 * (1 + β) * eR)) *
        (traj F Λ b μ₀ n).1

theorem logSum_ofD {N : ℕ} {A0 a0 ε eR : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (hE : ∑ j ∈ range N, e j ≤ eR)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    LogSumD F Λ β κ cg cm cT N ε eR := by
  intro b μ₀ h y p a A σ hA ha hy n hn
  have key := log_trajD H he hε1 hcgβ he0 heb F1s hA ha h hy n hn
  refine key.trans (mul_le_mul_of_nonneg_right ?_ ((traj_InDh_of H h n hn).1 n le_rfl).1.le)
  have hs : 0 ≤ |σ| / β := div_nonneg (abs_nonneg _) H.hβ.le
  have a1 : ∑ k ∈ range n, (A * a k + |σ| / β * (2 * (1 + β) * e k)) =
      A * ∑ k ∈ range n, a k + |σ| / β * (2 * (1 + β)) * ∑ k ∈ range n, e k := by
    rw [sum_add_distrib, mul_sum, mul_sum]
    congr 1; exact sum_congr rfl fun k _ => by ring
  have hse : ∑ k ∈ range n, e k ≤ eR :=
    le_trans (sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hn) (fun k _ _ => he0 k)) hE
  have h2 := mul_le_mul_of_nonneg_left hse
    (mul_nonneg hs (by have := H.hβ; positivity) : (0 : ℝ) ≤ |σ| / β * (2 * (1 + β)))
  rw [a1]
  have e1 : |σ| / β * (2 * (1 + β) * eR) = |σ| / β * (2 * (1 + β)) * eR := by ring
  linarith only [h2, e1]

/-- `logSum_ofD` restricted to admissible trajectories. -/
theorem logSum_of {N : ℕ} {A0 a0 ε eR : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (hE : ∑ j ∈ range N, e j ≤ eR)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    LogSum F Λ β κ cg cm cT N ε eR :=
  fun b μ₀ h => logSum_ofD H he hε1 hcgβ he0 heb hE F1s b μ₀ h.1

end Flow2.Hist
