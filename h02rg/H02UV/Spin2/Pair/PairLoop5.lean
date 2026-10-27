import Spin2.Pair.PairLoop
import Obs2.Flow.MemGronwall2

/-!
# The constant loop after the cancellation (pure)

After `Obs2.errABX2_eq3` the per-scale `E`-step sizes are of the form (relative to
`‖M_{j_x}‖ǧ_{j_x}|β|`)

`s_k ≤ seed_k + C_E·m̄·[(cǧ_k)² + ∑_{j≤i<k}q^{k-i}((cǧ_i)² + (cǧ_i)(cǧ_k)) + q^{k-j}cǧ_k]`

(`seed`: from `K'_{j_x} = k₀`, summable without smallness; the convolution: `M₄` sources at
scale `i` seen through `m2D(C_k) ≲ L^{-2(k-i)}`, the `Loc S` part with the vertex factor
`|n_k| ≤ B'ǧ_k`; the last term: first-order sizes decaying from `j_x`).

* `geom_Ico_le_one`: `∑_{j≤i<k}q^{k-i} ≤ 1` for `0 ≤ q ≤ 1/2`;
* **`sfirst_conv_le`**: `∑_k∑_{i<k}q^{k-i}(g_i² + g_ig_k) ≤ 5∑_kg_k²` (`q ≤ 1/2`, `g ≥ 0`);
* `geom_decay_le`: `∑_kq^{k-j}g_k ≤ 2ε` for `g ≤ ε`;
* **`pairLoop2_sum_le`**: `∑_{j≤k<M}s_k ≤ ∑seed + C_E·m̄·(6c²G₂ + 2cε)`;
* **`pairLoop2_close`**: with `∑ǧ² ≤ 4ε/β_L` (`sum_gsq_Ico_le`) the loop of `Spin2/Pair/PairLoop`
  closes under the **`ε`-requirement `X·C_E·(24c²/β_L + 2c)·ε ≤ 1/2`**
  (`X = crErr2 1 …`, `pairLoop_close`).
-/

namespace Spin2

open Finset

/-- `∑_{j≤i<k}q^{k-i} ≤ 1` for `0 ≤ q ≤ 1/2`. -/
theorem geom_Ico_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (j k : ℕ) :
    ∑ i ∈ Ico j k, q ^ (k - i) ≤ 1 := by
  rcases le_or_gt k j with hkj | hjk
  · rw [Ico_eq_empty_of_le hkj, sum_empty]; norm_num
  induction k, hjk using Nat.le_induction with
  | base =>
    rw [Nat.Ico_succ_singleton, sum_singleton, show j + 1 - j = 1 by omega, pow_one]; linarith
  | succ k hk ih =>
    rw [sum_Ico_succ_top (by omega), show k + 1 - k = 1 by omega, pow_one]
    have e : ∑ i ∈ Ico j k, q ^ (k + 1 - i) = q * ∑ i ∈ Ico j k, q ^ (k - i) := by
      rw [mul_sum]
      exact sum_congr rfl fun i hi => by
        rw [show k + 1 - i = (k - i) + 1 by have := (mem_Ico.1 hi).2; omega, pow_succ]; ring
    rw [e]
    have := ih
    nlinarith

/-- **The convolution of two first-order sizes is second order.** -/
theorem sfirst_conv_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i)
    (j M : ℕ) :
    ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * (g i ^ 2 + g i * g k) ≤
      5 * ∑ k ∈ Ico j M, g k ^ 2 := by
  have hA : ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * g i ^ 2 ≤ 2 * ∑ k ∈ Ico j M, g k ^ 2 := by
    have h := Obs2.geom_kernel_weight_le (a := 1) (θ := q) zero_le_one hq0 (by linarith)
      (fun i => g i ^ 2) (fun i => sq_nonneg _) j M
    simp only [one_pow, one_mul, mul_one] at h
    refine le_trans (sum_le_sum fun k _ => sum_le_sum fun i hi => ?_) h
    have hik := (mem_Ico.1 hi).2
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact pow_le_pow_of_le_one hq0 (by linarith) (by omega)
  have hB : ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * (g i * g k) ≤
      ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * g i ^ 2 + ∑ k ∈ Ico j M, g k ^ 2 := by
    have h1 : ∀ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * (g i * g k) ≤
        ∑ i ∈ Ico j k, q ^ (k - i) * g i ^ 2 + g k ^ 2 := by
      intro k _
      have h2 : ∑ i ∈ Ico j k, q ^ (k - i) * (g i * g k) ≤
          ∑ i ∈ Ico j k, q ^ (k - i) * g i ^ 2 + ∑ i ∈ Ico j k, q ^ (k - i) * g k ^ 2 := by
        rw [← sum_add_distrib]
        refine sum_le_sum fun i _ => ?_
        have hp : 0 ≤ q ^ (k - i) := pow_nonneg hq0 _
        have : g i * g k ≤ g i ^ 2 + g k ^ 2 := by nlinarith [hg i, hg k, sq_nonneg (g i - g k)]
        nlinarith
      have h3 : ∑ i ∈ Ico j k, q ^ (k - i) * g k ^ 2 ≤ g k ^ 2 := by
        rw [← sum_mul]
        have := geom_Ico_le_one hq0 hq j k
        nlinarith [sq_nonneg (g k)]
      linarith
    refine (sum_le_sum h1).trans (le_of_eq ?_)
    rw [sum_add_distrib]
  have hsplit : ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * (g i ^ 2 + g i * g k) =
      ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * g i ^ 2 +
        ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * (g i * g k) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [hsplit]
  linarith

/-- `∑_{j≤k<M}q^{k-j}g_k ≤ 2ε` for `0 ≤ g ≤ ε`, `q ≤ 1/2`. -/
theorem geom_decay_le {q ε : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i)
    (hgε : ∀ i, g i ≤ ε) (j M : ℕ) : ∑ k ∈ Ico j M, q ^ (k - j) * g k ≤ 2 * ε := by
  have hε : 0 ≤ ε := (hg 0).trans (hgε 0)
  have h1 : ∑ k ∈ Ico j M, q ^ (k - j) * g k ≤ ∑ k ∈ Ico j M, (1 / 2 : ℝ) ^ (k - j) * ε :=
    sum_le_sum fun k _ => mul_le_mul (pow_le_pow_left₀ hq0 hq _) (hgε k) (hg k) (by positivity)
  refine h1.trans ?_
  rw [← sum_mul]
  have h2 : ∑ k ∈ Ico j M, (1 / 2 : ℝ) ^ (k - j) ≤ 2 := by
    rcases le_or_gt M j with hMj | hjM
    · rw [Ico_eq_empty_of_le hMj, sum_empty]; norm_num
    have e : ∑ k ∈ Ico j M, (1 / 2 : ℝ) ^ (k - j) = ∑ n ∈ range (M - j), (1 / 2 : ℝ) ^ n := by
      rw [sum_Ico_eq_sum_range]; exact sum_congr rfl fun n _ => by rw [Nat.add_sub_cancel_left]
    rw [e]
    have := sum_geometric_two_le (M - j)
    simpa [one_div] using this
  nlinarith

/-- **The summed `E`-step sizes after the cancellation.** -/
theorem pairLoop2_sum_le {q c CE mbar ε G2 : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hc : 0 ≤ c)
    (hCE : 0 ≤ CE) (hm : 0 ≤ mbar) {g s seed : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) (hgε : ∀ i, g i ≤ ε)
    {j M : ℕ} (hG2 : ∑ k ∈ Ico j M, g k ^ 2 ≤ G2)
    (hs : ∀ k ∈ Ico j M, s k ≤ seed k + CE * mbar * ((c * g k) ^ 2 +
      ∑ i ∈ Ico j k, q ^ (k - i) * ((c * g i) ^ 2 + (c * g i) * (c * g k)) +
      q ^ (k - j) * (c * g k))) :
    ∑ k ∈ Ico j M, s k ≤ ∑ k ∈ Ico j M, seed k + CE * mbar * (6 * c ^ 2 * G2 + 2 * c * ε) := by
  have hcg : ∀ i, 0 ≤ c * g i := fun i => mul_nonneg hc (hg i)
  have h1 := sfirst_conv_le hq0 hq hcg j M
  have h2 := geom_decay_le hq0 hq hcg (fun i => mul_le_mul_of_nonneg_left (hgε i) hc) j M
  have h3 : ∑ k ∈ Ico j M, (c * g k) ^ 2 = c ^ 2 * ∑ k ∈ Ico j M, g k ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  have hc2 : ∑ k ∈ Ico j M, (c * g k) ^ 2 ≤ c ^ 2 * G2 := by
    rw [h3]; exact mul_le_mul_of_nonneg_left hG2 (sq_nonneg c)
  have hCm : 0 ≤ CE * mbar := mul_nonneg hCE hm
  refine (sum_le_sum hs).trans ?_
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_add_distrib]
  have hT : ∑ k ∈ Ico j M, (c * g k) ^ 2 +
      ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * ((c * g i) ^ 2 + (c * g i) * (c * g k)) +
      ∑ k ∈ Ico j M, q ^ (k - j) * (c * g k) ≤ 6 * c ^ 2 * G2 + 2 * c * ε := by
    have h1' : ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, q ^ (k - i) * ((c * g i) ^ 2 + (c * g i) * (c * g k))
        ≤ 5 * (c ^ 2 * G2) := h1.trans (mul_le_mul_of_nonneg_left hc2 (by norm_num))
    linarith
  have := mul_le_mul_of_nonneg_left hT hCm
  linarith

/-- **The loop closes after the cancellation**: with `∑ǧ² ≤ G₂ = 4ε/β_L` and the
`ε`-requirement `X·C_E·(6c²G₂ + 2cε) ≤ 1/2` (i.e. `X·C_E·(24c²/β_L + 2c)·ε ≤ 1/2`), every
`m̄ ≥ max(2X·S_seed, m_seed, 1)` gives `crErr2 c_e … ≤ m̄` for `c_e = S_seed + C_E(6c²G₂ + 2cε)m̄`
(`S_seed ≥ ∑seed`). -/
theorem pairLoop2_close {cδ G2 ct B' ca CE c ε Sseed mbar : ℝ} (hCE : 0 ≤ CE) (hc : 0 ≤ c)
    (hε : 0 ≤ ε) (hG2 : 0 ≤ G2) (hS : 0 ≤ Sseed)
    (hreq : crErr2 1 cδ G2 ct B' ca * (CE * (6 * c ^ 2 * G2 + 2 * c * ε)) ≤ 1 / 2)
    (hm : 2 * crErr2 1 cδ G2 ct B' ca * Sseed ≤ mbar) (hm0 : 0 < mbar) :
    crErr2 (Sseed + CE * (6 * c ^ 2 * G2 + 2 * c * ε) * mbar) cδ G2 ct B' ca ≤ mbar := by
  have hΘ : 0 ≤ CE * (6 * c ^ 2 * G2 + 2 * c * ε) := by positivity
  have h := pairLoop_close (Θ₀ := 1) (k₀ := Sseed) (S := 0) zero_le_one hΘ hS hreq
    (by rw [mul_one]; exact hm) hm0.le hm0
  simpa [one_mul] using h.2.1

end Spin2
