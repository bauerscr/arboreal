import Spin2.Pair.PairErrAB3
import Spin2.Pair.PairVReq

/-!
# The constant loop of the joint induction (`c_e`, `c_r`, `m̄`)

`thm_pairAbove_final` (`Spin2/Pair/PairFinal`) asks `crErr2 c_e … ≤ c_σ`, `c_σ ≤ m̄` and the seed
condition `8c_u(2ι_WA)^{(L+18)²} ≤ vck(C₁w)(4C₁w+1)m̄`, while the `E`-step constant `c_e` depends on
`m̄` (the `K'`, `𝒲'`, `S` sizes of the `ab` chain are bounded in units of `m̄`). This file records
the closure:
* `crErr2_eq_mul`: `crErr2` is linear in `c_e`: `crErr2 c_e … = c_e·X`, `X = crErr2 1 … =
  2exp(2(…))` (depends on `L` through `c_δ`, `4/β_L`, `c_t`, `B'`, and on `c_a`).
* **`pairLoop_close`**: if the `E`-step gives `c_e = Θ₀k₀ + Θ₁m̄` (a seed part, independent of
  `m̄`, plus an `m̄`-proportional part) with **`X·Θ₁ ≤ 1/2`**, then every
  `m̄ ≥ max(2XΘ₀k₀, S)` (`S` = the seed lower bound) satisfies all three conditions with
  `c_σ := m̄`. The only smallness is `XΘ₁ ≤ 1/2`.
* **`sum_gsq_Ico_le`**: `∑_{j≤k<n}ǧ_k² ≤ (4/β)(ǧ_n − ǧ_j)` from `GIncConcl` — second-order
  per-scale sizes give `Θ₁ = O(ǧ_{N_h}) = O(ε)` (an `ε`-requirement `X(L)·C(L)·4ε/β_L ≤ 1/2`).
  First-order per-scale sizes `C(L)ǧ_k m̄` without geometric decay in `k − j_x` do **not** close:
  `∑_{j_x≤k<N_h}ǧ_k ≍ β_L^{-1}log(ǧ_{N_h}/ǧ_{j_x})` is unbounded in `b` (see Log.md).
-/

namespace Spin2

open Finset

/-- `crErr2` is linear in `c_e`. -/
theorem crErr2_eq_mul (ce cδ G2 ct B' ca : ℝ) :
    crErr2 ce cδ G2 ct B' ca = ce * crErr2 1 cδ G2 ct B' ca := by
  unfold crErr2; ring

theorem crErr2_one_pos (cδ G2 ct B' ca : ℝ) : 0 < crErr2 1 cδ G2 ct B' ca := by
  unfold crErr2; have := Real.exp_pos (2 * ((8 / 7 * cδ * G2 + 1 / 7) + ca +
    1 / 16 * ((64 / 49 * B' * ct + 8 / 7 * cδ) * G2) + 64 / 49 / 16)); linarith

/-- **The closure of the constant loop** (see the module docstring). -/
theorem pairLoop_close {cδ G2 ct B' ca Θ₀ Θ₁ k₀ S mbar : ℝ} (hΘ₀ : 0 ≤ Θ₀) (hΘ₁ : 0 ≤ Θ₁)
    (hk₀ : 0 ≤ k₀) (hsm : crErr2 1 cδ G2 ct B' ca * Θ₁ ≤ 1 / 2)
    (hm1 : 2 * crErr2 1 cδ G2 ct B' ca * Θ₀ * k₀ ≤ mbar) (hm2 : S ≤ mbar) (hm0 : 0 < mbar) :
    0 ≤ Θ₀ * k₀ + Θ₁ * mbar ∧
    crErr2 (Θ₀ * k₀ + Θ₁ * mbar) cδ G2 ct B' ca ≤ mbar ∧ mbar ≤ mbar ∧ S ≤ mbar ∧ 0 < mbar := by
  have hX := crErr2_one_pos cδ G2 ct B' ca
  refine ⟨by positivity, ?_, le_rfl, hm2, hm0⟩
  rw [crErr2_eq_mul]
  have e : (Θ₀ * k₀ + Θ₁ * mbar) * crErr2 1 cδ G2 ct B' ca =
      crErr2 1 cδ G2 ct B' ca * Θ₀ * k₀ + (crErr2 1 cδ G2 ct B' ca * Θ₁) * mbar := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hsm hm0.le
  linarith

/-- **The existence form**: a `m̄` closing the loop, with the seed lower bound of
`thm_pairAbove_final` (`8c_u(2ι_WA)^{(L+18)²} ≤ vck(C₁w)(4C₁w+1)m̄`). -/
theorem pairLoop_exists {cδ G2 ct B' ca Θ₀ Θ₁ k₀ C₁w seed : ℝ} (hΘ₀ : 0 ≤ Θ₀) (hΘ₁ : 0 ≤ Θ₁)
    (hk₀ : 0 ≤ k₀) (hC₁w : 0 ≤ C₁w) (hsm : crErr2 1 cδ G2 ct B' ca * Θ₁ ≤ 1 / 2) :
    ∃ mbar : ℝ, 0 < mbar ∧
      crErr2 (Θ₀ * k₀ + Θ₁ * mbar) cδ G2 ct B' ca ≤ mbar ∧
      seed ≤ vck C₁w * ((4 * C₁w + 1) * mbar) := by
  have hv : 0 < vck C₁w * (4 * C₁w + 1) := by
    unfold vck
    have := vA1_nonneg hC₁w
    positivity
  set mbar := max (max (2 * crErr2 1 cδ G2 ct B' ca * Θ₀ * k₀) (seed / (vck C₁w * (4 * C₁w + 1)))) 1
  have hm0 : 0 < mbar := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hm1 : 2 * crErr2 1 cδ G2 ct B' ca * Θ₀ * k₀ ≤ mbar :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hm2 : seed / (vck C₁w * (4 * C₁w + 1)) ≤ mbar := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨-, h1, -, -, -⟩ := pairLoop_close hΘ₀ hΘ₁ hk₀ hsm hm1 hm2 hm0
  refine ⟨mbar, hm0, h1, ?_⟩
  rw [div_le_iff₀ hv] at hm2
  linarith

/-- **Second-order sizes are `O(ǧ_n)`**: `∑_{j≤k<n}ǧ_k² ≤ (4/β)(ǧ_n − ǧ_j)` from
`ǧ_k + (β/4)ǧ_k² ≤ ǧ_{k+1}` (`GIncConcl`). -/
theorem sum_gsq_Ico_le {g : ℕ → ℝ} {β : ℝ} (hβ : 0 < β) {j n : ℕ} (hjn : j ≤ n)
    (hinc : ∀ k, j ≤ k → k < n → g k + β / 4 * g k ^ 2 ≤ g (k + 1)) :
    ∑ k ∈ Ico j n, g k ^ 2 ≤ 4 / β * (g n - g j) := by
  induction n, hjn using Nat.le_induction with
  | base => simp
  | succ n hjn ih =>
    rw [sum_Ico_succ_top hjn]
    have h1 := ih (fun k hk hkn => hinc k hk (by omega))
    have h2 := hinc n hjn (by omega)
    have h3 : g n ^ 2 ≤ 4 / β * (g (n + 1) - g n) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ]; linarith
    have e : 4 / β * (g n - g j) + 4 / β * (g (n + 1) - g n) = 4 / β * (g (n + 1) - g j) := by ring
    linarith

end Spin2
