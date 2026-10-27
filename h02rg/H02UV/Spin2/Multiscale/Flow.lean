import Spin2.Multiscale.Sum
import Step2.Flow.ZetaSharp6

/-!
# `sec:spin` (ii) and `thm:beta` along the admissible trajectories of an abstract flow

For a flow with `HHyp` (band `δ = 1/2`) and the sharp (F1) with `e_j ≤ β/2`, `∑ e_j ≤ e_R`
(the hypotheses of `Flow2.Hist.logSum_of`):

* `SpinSum` / `spinSum_of`: along every admissible trajectory, every sequence `T_k` with
  `‖T_k - (β/3) b r_k²‖ ≤ B b r_k² (ǧ_k + a_k)`, `r_k = (ǧ_k/b)^{1/3}`, satisfies
  `‖(1 - ∑_{k<j} T_k) - (b/ǧ_j)^{1/3}‖ ≤ K (b/ǧ_j)^{1/3} ǧ_j` (`Spin2.spin_sum`);
* `BetaAsym` / `betaAsym_of`: `|β_n - β_ε + nβ| ≤ 2(1+β)e_R + C_gu((1/β) log(β_ε/β_n) + K' ǧ_n)`
  (`β_n = 1/ǧ_n`, `β_ε = 1/b`, `β = β_1 log L`): the running coupling of `thm:beta`,
  `β_{j+1} = β_j - β_1 log L + O(β_j^{-1}) + e_j`, summed.

The band in `1/ǧ` form is `ginv_sharp`, monotonicity from (F1), as in `log_traj`.
-/

open Finset

namespace Spin2

open Flow2 Flow2.Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {F : HData X} {Λ β κ cg cm cT : ℝ}

/-- The constant of `SpinSum`. -/
noncomputable def spinTrajK (β cg B eR aS : ℝ) : ℝ :=
  spinK β (β / 4) (1 + 3 / 2 * β + cg) (Cgu β cg) ((1 + β) * β) B (2 * (1 + β) * eR) aS

/-- **The magnetisation sum along the admissible trajectories.** -/
def SpinSum (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε eR : ℝ) : Prop :=
  ∀ b μ₀, Admissible F Λ κ cm cT N ε b μ₀ → ∀ (T : ℕ → ℂ) (a : ℕ → ℝ) (B aS : ℝ), 0 ≤ B →
    (∀ k, 0 ≤ a k) → ∑ k ∈ range N, a k ≤ aS →
    (∀ k < N, ‖T k - ((β / 3 * b * (((traj F Λ b μ₀ k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 : ℝ) : ℂ)‖ ≤
      B * b * (((traj F Λ b μ₀ k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 * ((traj F Λ b μ₀ k).1 + a k)) →
    ∀ j ≤ N, ‖(1 - ∑ k ∈ range j, T k) - (((b / (traj F Λ b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinTrajK β cg B eR aS * (b / (traj F Λ b μ₀ j).1) ^ (1 / 3 : ℝ) * (traj F Λ b μ₀ j).1

/-- `SpinSum` along every trajectory in `D_ε` up to `N` (route (a1)). -/
def SpinSumD (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε eR : ℝ) : Prop :=
  ∀ b μ₀, (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) → ∀ (T : ℕ → ℂ) (a : ℕ → ℝ) (B aS : ℝ), 0 ≤ B →
    (∀ k, 0 ≤ a k) → ∑ k ∈ range N, a k ≤ aS →
    (∀ k < N, ‖T k - ((β / 3 * b * (((traj F Λ b μ₀ k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 : ℝ) : ℂ)‖ ≤
      B * b * (((traj F Λ b μ₀ k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 * ((traj F Λ b μ₀ k).1 + a k)) →
    ∀ j ≤ N, ‖(1 - ∑ k ∈ range j, T k) - (((b / (traj F Λ b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinTrajK β cg B eR aS * (b / (traj F Λ b μ₀ j).1) ^ (1 / 3 : ℝ) * (traj F Λ b μ₀ j).1

/-- The constant of `BetaAsym`. -/
noncomputable def betaAsymK (β cg eR : ℝ) : ℝ :=
  logTrajK β cg 0 (1 / β) + 1 / β * (2 * (1 + β) * eR)

/-- **`thm:beta`, the running coupling along the admissible trajectories**:
`|1/ǧ_n - 1/b + nβ| ≤ 2(1+β)e_R + C_gu((1/β) log(ǧ_n/b) + K' ǧ_n)`. -/
def BetaAsym (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε eR : ℝ) : Prop :=
  ∀ b μ₀, Admissible F Λ κ cm cT N ε b μ₀ → ∀ n ≤ N,
    |1 / (traj F Λ b μ₀ n).1 - 1 / b + n * β| ≤ 2 * (1 + β) * eR +
      Cgu β cg * (1 / β * Real.log ((traj F Λ b μ₀ n).1 / b) +
        betaAsymK β cg eR * (traj F Λ b μ₀ n).1)

/-- `BetaAsym` along every trajectory in `D_ε` up to `N` (route (a1)). -/
def BetaAsymD (F : HData X) (Λ β κ cg cm cT : ℝ) (N : ℕ) (ε eR : ℝ) : Prop :=
  ∀ b μ₀, (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) → ∀ n ≤ N,
    |1 / (traj F Λ b μ₀ n).1 - 1 / b + n * β| ≤ 2 * (1 + β) * eR +
      Cgu β cg * (1 / β * Real.log ((traj F Λ b μ₀ n).1 / b) +
        betaAsymK β cg eR * (traj F Λ b μ₀ n).1)

/-- The trajectory facts used by `spinSum_of` and `betaAsym_of` (from `log_traj`). -/
theorem traj_factsD {N : ℕ} {A0 a0 ε : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    {b μ₀ : ℝ} (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) :
    (∀ k ≤ N, 0 < (traj F Λ b μ₀ k).1) ∧ (∀ k < N, (traj F Λ b μ₀ k).1 ≤ 1) ∧
    (∀ k < N, (traj F Λ b μ₀ k).1 + β / 4 * (traj F Λ b μ₀ k).1 ^ 2 ≤
      (traj F Λ b μ₀ (k + 1)).1) ∧
    (∀ k < N, (traj F Λ b μ₀ (k + 1)).1 ≤ (1 + 3 / 2 * β + cg) * (traj F Λ b μ₀ k).1) ∧
    (∀ k < N, |1 / (traj F Λ b μ₀ (k + 1)).1 - 1 / (traj F Λ b μ₀ k).1 + β| ≤
      2 * (1 + β) * e k + Cgu β cg * (traj F Λ b μ₀ k).1) ∧
    (∀ k < N, 2 * (1 + β) * e k ≤ (1 + β) * β) := by
  have hβ := H.hβ
  have hcg := H.hcg
  set g : ℕ → ℝ := fun k => (traj F Λ b μ₀ k).1 with hgd
  have hD := traj_InDh_of H h
  have hg : ∀ k ≤ N, 0 < g k := fun k hk => ((hD k hk).1 k le_rfl).1
  have hg1 : ∀ k < N, g k ≤ 1 := fun k hk => (((hD k hk.le).1 k le_rfl).2.1).trans hε1
  have hgε : ∀ k < N, g k ≤ ε := fun k hk => ((hD k hk.le).1 k le_rfl).2.1
  have hF1 : ∀ k < N, |g (k + 1) - g k - β * g k ^ 2| ≤ 1 / 2 * β * g k ^ 2 + cg * g k ^ 3 := by
    intro k hk
    have := H.F1 k hk _ (hD k hk.le)
    simp only [hgd]
    rw [traj_succ H b μ₀ hk]
    exact this
  refine ⟨hg, hg1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h1 := (abs_le.1 (hF1 k hk)).1
    have hgk := hg k hk.le
    have h2 : cg * g k ≤ β / 4 := (mul_le_mul_of_nonneg_left (hgε k hk) hcg.le).trans hcgβ
    have h3 : cg * g k ^ 3 ≤ β / 4 * g k ^ 2 := by
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg (g k))
      have e : cg * g k ^ 3 = cg * g k * g k ^ 2 := by ring
      linarith only [this, e]
    show g k + β / 4 * g k ^ 2 ≤ g (k + 1)
    linarith only [h1, h3]
  · intro k hk
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
    show g (k + 1) ≤ (1 + 3 / 2 * β + cg) * g k
    linarith only [h1, h4, h5]
  · intro k hk
    exact ginv_sharpD H he h hk (he0 k) hcg.le (F1s k hk)
  · intro k hk
    have := mul_le_mul_of_nonneg_left (heb k hk) (by positivity : (0 : ℝ) ≤ 2 * (1 + β))
    linarith only [this]

/-- `traj_factsD` along an admissible trajectory. -/
theorem traj_facts {N : ℕ} {A0 a0 ε : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) :
    (∀ k ≤ N, 0 < (traj F Λ b μ₀ k).1) ∧ (∀ k < N, (traj F Λ b μ₀ k).1 ≤ 1) ∧
    (∀ k < N, (traj F Λ b μ₀ k).1 + β / 4 * (traj F Λ b μ₀ k).1 ^ 2 ≤
      (traj F Λ b μ₀ (k + 1)).1) ∧
    (∀ k < N, (traj F Λ b μ₀ (k + 1)).1 ≤ (1 + 3 / 2 * β + cg) * (traj F Λ b μ₀ k).1) ∧
    (∀ k < N, |1 / (traj F Λ b μ₀ (k + 1)).1 - 1 / (traj F Λ b μ₀ k).1 + β| ≤
      2 * (1 + β) * e k + Cgu β cg * (traj F Λ b μ₀ k).1) ∧
    (∀ k < N, 2 * (1 + β) * e k ≤ (1 + β) * β) :=
  traj_factsD H he hε1 hcgβ he0 heb F1s h.1

theorem spinSum_ofD {N : ℕ} {A0 a0 ε eR : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (hE : ∑ j ∈ range N, e j ≤ eR)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    SpinSumD F Λ β κ cg cm cT N ε eR := by
  intro b μ₀ h T a B aS hB ha haS hT
  have hβ := H.hβ
  have hcg := H.hcg
  obtain ⟨hg, hg1, hinc, hM, hband, he1⟩ := traj_factsD H he hε1 hcgβ he0 heb F1s h
  have hg0 : (traj F Λ b μ₀ 0).1 = b := by simp only [Hist.traj_zero]
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  have key := spin_sum (g := fun k => (traj F Λ b μ₀ k).1) (e := fun k => 2 * (1 + β) * e k)
    (a := a) (T := T) (β := β) (β' := β / 4) (M := 1 + 3 / 2 * β + cg) (c := Cgu β cg)
    (E1 := (1 + β) * β) (B := B) (eS := 2 * (1 + β) * eR) (aS := aS) (n := N) hβ.le
    (by positivity) (by linarith) hCgu hB (by positivity) hg hg1 hinc hM
    (fun k _ => by have := he0 k; positivity) he1 (fun k _ => ha k)
    (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hE (by positivity)) haS hband
    (fun k hk => by simp only [hg0]; exact hT k hk)
  intro j hj
  have := key j hj
  simp only [hg0] at this
  unfold spinTrajK
  exact this

/-- `spinSum_ofD` restricted to admissible trajectories. -/
theorem spinSum_of {N : ℕ} {A0 a0 ε eR : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (hE : ∑ j ∈ range N, e j ≤ eR)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    SpinSum F Λ β κ cg cm cT N ε eR :=
  fun b μ₀ h => spinSum_ofD H he hε1 hcgβ he0 heb hE F1s b μ₀ h.1

theorem betaAsym_ofD {N : ℕ} {A0 a0 ε eR : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (hE : ∑ j ∈ range N, e j ≤ eR)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    BetaAsymD F Λ β κ cg cm cT N ε eR := by
  intro b μ₀ h n hn
  have hβ := H.hβ
  have hcg := H.hcg
  obtain ⟨hg, -, -, -, hband, -⟩ := traj_factsD H he hε1 hcgβ he0 heb F1s h
  have hg0 : (traj F Λ b μ₀ 0).1 = b := by simp only [Hist.traj_zero]
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  have hb := beta_sum (g := fun k => (traj F Λ b μ₀ k).1) (n := n)
    (fun k hk => hband k (by omega))
  simp only [hg0] at hb
  -- `∑_{k<n} ǧ_k ≤ (1/β) log(ǧ_n/b) + K' ǧ_n`
  have LS := logSum_ofD H he hε1 hcgβ he0 heb hE F1s
  have key := LS b μ₀ h (fun k => ∑ i ∈ range k, (traj F Λ b μ₀ i).1) (fun _ => 0)
    (fun _ => 0) 0 (-1) le_rfl (fun _ => le_rfl)
    (fun k _ => by simp [sum_range_succ]) n hn
  simp only [sum_range_zero, sub_zero, sub_self, mul_zero, sum_const_zero, add_zero,
    abs_neg, abs_one] at key
  have hs : ∑ i ∈ range n, (traj F Λ b μ₀ i).1 ≤
      1 / β * Real.log ((traj F Λ b μ₀ n).1 / b) + betaAsymK β cg eR * (traj F Λ b μ₀ n).1 := by
    have h1 := (abs_le.1 key).2
    have e1 : -1 / β * Real.log ((traj F Λ b μ₀ n).1 / b) =
        -(1 / β * Real.log ((traj F Λ b μ₀ n).1 / b)) := by ring
    unfold betaAsymK
    linarith only [h1, e1]
  have hse : ∑ k ∈ range n, 2 * (1 + β) * e k ≤ 2 * (1 + β) * eR := by
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hE) (by positivity)
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hn) (fun k _ _ => he0 k)
  have := mul_le_mul_of_nonneg_left hs hCgu
  linarith only [hb, hse, this]

/-- `betaAsym_ofD` restricted to admissible trajectories. -/
theorem betaAsym_of {N : ℕ} {A0 a0 ε eR : ℝ} (H : HHyp F Λ β (1 / 2) κ cg cm cT N A0 a0 ε)
    (he : ε ≤ eps0u Λ β (1 / 2) κ cg cm) (hε1 : ε ≤ 1) (hcgβ : cg * ε ≤ β / 4)
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (heb : ∀ j < N, e j ≤ 1 / 2 * β)
    (hE : ∑ j ∈ range N, e j ≤ eR)
    (F1s : ∀ j < N, ∀ t, InDh Λ β (1 / 2) κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e j * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    BetaAsym F Λ β κ cg cm cT N ε eR :=
  fun b μ₀ h => betaAsym_ofD H he hε1 hcgβ he0 heb hE F1s b μ₀ h.1

end Spin2
