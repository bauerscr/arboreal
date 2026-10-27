import Obs2.Flow.MemGronwall

/-!
# Relative Gronwall with memory and an `r`-proportional error

Copies of `rel_gronwall_mem`, `rel_gronwall_geom` (`Obs2/Flow/MemGronwall`) in which the error of the
`r` recursion may contain parts proportional to the earlier couplings `r_i`, `j ≤ i ≤ k`:

* **`rel_gronwall_memR`**: `‖E_k‖ ≤ s_k‖β_{k+1}‖ + (∑_{j≤i≤k}a_{ik}‖r_i/β_i‖)‖β_{k+1}‖`; the
  Gronwall weight becomes `ε_k + ∑_ia_{ik} + ∑_iλ_{ik} + ∑_{i<j}μ_{ik}` (`|ρ_i| ≤ S_i ≤ S_k`, so the
  extra terms are treated like `ρ_ke_k`).
* **`rel_gronwall_geomR`**: `‖E_k‖ ≤ s_k‖β_{k+1}‖ + ∑_{j≤i≤k}η_{ik}‖r_i‖`; same conclusion as
  `rel_gronwall_geom` with `∑_k∑_i(64/49)^{k+1-i}η_{ik}` added in the exponent
  (`‖β_i‖ ≤ (64/49)^{k+1-i}‖β_{k+1}‖`).

This is what the reduced pair flow needs once the mass of `𝒲'` is written as a product term
(`Obs2/Flow/MuChainAB2`): its size is `O(ǧ³)` times the `V'` size of the previous step, i.e.
`η_{k-1,k} = O(ǧ³)`, summable.
-/

set_option linter.unusedSectionVars false

namespace Obs2

open Finset

/-- **Relative Gronwall with memory, `r`-proportional errors allowed.** -/
theorem rel_gronwall_memR (r β n e E : ℕ → ℂ) (t : ℕ → ℕ → ℂ) (s ε : ℕ → ℝ) (a κ lam μ : ℕ → ℕ → ℝ) (j M : ℕ)
    (hr0 : r j = 0) (hs0 : ∀ k, 0 ≤ s k) (hε0 : ∀ k, 0 ≤ ε k) (ha0 : ∀ i k, 0 ≤ a i k) (hκ0 : ∀ i k, 0 ≤ κ i k)
    (hl0 : ∀ i k, 0 ≤ lam i k) (hμ0 : ∀ i k, 0 ≤ μ i k)
    (hr : ∀ k, j ≤ k → k < M → r (k + 1) = (1 - n k) * r k -
      ∑ i ∈ range k, ((if j ≤ i then r i else 0) - r k) * t i k - E k)
    (hβ : ∀ k, j ≤ k → k < M → β (k + 1) = (1 - n k) * β k - e k)
    (hβ0 : ∀ k, j ≤ k → k ≤ M → β k ≠ 0)
    (hE : ∀ k, j ≤ k → k < M → ‖E k‖ ≤ s k * ‖β (k + 1)‖ +
      (∑ i ∈ Icc j k, a i k * ‖r i / β i‖) * ‖β (k + 1)‖)
    (he : ∀ k, j ≤ k → k < M → ‖e k‖ ≤ ε k * ‖β (k + 1)‖)
    (hκ : ∀ k, j ≤ k → k < M → ∀ i ∈ Ico j k, ‖β i‖ * ‖t i k‖ ≤ κ i k * ‖β (k + 1)‖)
    (hlam : ∀ k, j ≤ k → k < M → ∀ i ∈ Ico j k, ‖β i - β k‖ * ‖t i k‖ ≤ lam i k * ‖β (k + 1)‖)
    (hμ : ∀ k, j ≤ k → k < M → ∀ i ∈ range j, ‖β k‖ * ‖t i k‖ ≤ μ i k * ‖β (k + 1)‖)
    (hcol : ∀ l, j ≤ l → l < M → ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l, κ i k ≤ 1 / 2) :
    ∀ k, j ≤ k → k ≤ M → ‖r k‖ ≤ 2 * (∑ i ∈ Ico j M, s i) *
      Real.exp (2 * ∑ k ∈ Ico j M, (ε k + ∑ i ∈ Icc j k, a i k + ∑ i ∈ Ico j k, lam i k + ∑ i ∈ range j, μ i k)) *
      ‖β k‖ := by
  set ρ : ℕ → ℂ := fun k => r k / β k with hρ
  set u : ℕ → ℝ := fun k => ‖ρ (k + 1) - ρ k‖ with hud
  have hrρ : ∀ k, j ≤ k → k ≤ M → r k = ρ k * β k := fun k h1 h2 => by
    simp only [hρ]; rw [div_mul_cancel₀ _ (hβ0 k h1 h2)]
  have hρj : ρ j = 0 := by simp only [hρ, hr0, zero_div]
  have F1 : ∀ k, j ≤ k → ‖ρ k‖ ≤ ∑ l ∈ Ico j k, u l := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [hρj, norm_zero, Ico_self, sum_empty]
    | succ k hk ih =>
      rw [sum_Ico_succ_top hk]
      calc ‖ρ (k + 1)‖ = ‖ρ k + (ρ (k + 1) - ρ k)‖ := by congr 1; ring
        _ ≤ ‖ρ k‖ + u k := norm_add_le _ _
        _ ≤ _ := by linarith
  have F2 : ∀ i k, i ≤ k → ‖ρ i - ρ k‖ ≤ ∑ l ∈ Ico i k, u l := by
    intro i k hik
    induction k, hik using Nat.le_induction with
    | base => rw [sub_self, norm_zero, Ico_self, sum_empty]
    | succ k hk ih =>
      rw [sum_Ico_succ_top hk]
      calc ‖ρ i - ρ (k + 1)‖ = ‖(ρ i - ρ k) - (ρ (k + 1) - ρ k)‖ := by congr 1; ring
        _ ≤ ‖ρ i - ρ k‖ + u k := norm_sub_le _ _
        _ ≤ _ := by linarith
  have F3 : ∀ k, j ≤ k → k < M → u k ≤
      (ε k + ∑ i ∈ Icc j k, a i k + ∑ i ∈ Ico j k, lam i k + ∑ i ∈ range j, μ i k) * ∑ l ∈ Ico j k, u l +
        ∑ l ∈ Ico j k, (∑ i ∈ Icc j l, κ i k) * u l + s k := by
    intro k hk hkM
    have hb1 : 0 < ‖β (k + 1)‖ := norm_pos_iff.2 (hβ0 (k + 1) (by omega) (by omega))
    set D := ∑ i ∈ range k, ((if j ≤ i then r i else 0) - r k) * t i k with hD
    have hrk := hr k hk hkM
    rw [← hD] at hrk
    have hid : β (k + 1) * (ρ (k + 1) - ρ k) = ρ k * e k - D - E k := by
      have h1 : β (k + 1) * ρ (k + 1) = r (k + 1) := by
        rw [hrρ (k + 1) (by omega) (by omega)]; ring
      rw [mul_sub, h1, hrk, hrρ k hk hkM.le, hβ k hk hkM]
      ring
    have hDa : ‖∑ i ∈ Ico 0 j, ((if j ≤ i then r i else 0) - r k) * t i k‖ ≤
        ‖ρ k‖ * (∑ i ∈ range j, μ i k) * ‖β (k + 1)‖ := by
      rw [mul_sum, sum_mul, ← range_eq_Ico]
      refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
      rw [if_neg (by have := mem_range.1 hi; omega), zero_sub, hrρ k hk hkM.le, norm_mul,
        norm_neg, norm_mul, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hμ k hk hkM i hi) (norm_nonneg _)
    have hDb : ‖∑ i ∈ Ico j k, ((if j ≤ i then r i else 0) - r k) * t i k‖ ≤
        (∑ i ∈ Ico j k, (‖ρ i - ρ k‖ * κ i k + ‖ρ k‖ * lam i k)) * ‖β (k + 1)‖ := by
      rw [sum_mul]
      refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
      have hi' := mem_Ico.1 hi
      rw [if_pos hi'.1, hrρ i hi'.1 (by omega), hrρ k hk hkM.le]
      have e1 : (ρ i * β i - ρ k * β k) * t i k =
          (ρ i - ρ k) * (β i * t i k) + ρ k * ((β i - β k) * t i k) := by ring
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul, add_mul, mul_assoc, mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left (hκ k hk hkM i hi) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hlam k hk hkM i hi) (norm_nonneg _))
    have hDn : ‖D‖ ≤ ‖ρ k‖ * (∑ i ∈ range j, μ i k) * ‖β (k + 1)‖ +
        (∑ i ∈ Ico j k, (‖ρ i - ρ k‖ * κ i k + ‖ρ k‖ * lam i k)) * ‖β (k + 1)‖ := by
      rw [hD, range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le j) hk]
      exact (norm_add_le _ _).trans (add_le_add hDa hDb)
    have h1 : ‖ρ k * e k‖ ≤ ‖ρ k‖ * ε k * ‖β (k + 1)‖ := by
      rw [norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (he k hk hkM) (norm_nonneg _)
    have hEk : ‖E k‖ ≤ s k * ‖β (k + 1)‖ + (∑ i ∈ Icc j k, a i k * ‖ρ i‖) * ‖β (k + 1)‖ :=
      hE k hk hkM
    have hu1 : ‖β (k + 1)‖ * u k ≤ ‖β (k + 1)‖ * (‖ρ k‖ * ε k + ∑ i ∈ Icc j k, a i k * ‖ρ i‖ +
        ‖ρ k‖ * ∑ i ∈ range j, μ i k +
        ∑ i ∈ Ico j k, (‖ρ i - ρ k‖ * κ i k + ‖ρ k‖ * lam i k) + s k) := by
      have e2 : ‖β (k + 1)‖ * u k = ‖ρ k * e k - D - E k‖ := by
        simp only [hud]; rw [← norm_mul, hid]
      rw [e2]
      have h3 : ‖ρ k * e k - D - E k‖ ≤ ‖ρ k * e k‖ + ‖D‖ + ‖E k‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      have h4 := add_le_add (add_le_add h1 hDn) hEk
      refine h3.trans (h4.trans (le_of_eq ?_))
      ring
    have hu2 := le_of_mul_le_mul_left hu1 hb1
    have hS := F1 k hk
    have hsum1 : ∑ i ∈ Ico j k, ‖ρ i - ρ k‖ * κ i k ≤
        ∑ l ∈ Ico j k, (∑ i ∈ Icc j l, κ i k) * u l := by
      calc ∑ i ∈ Ico j k, ‖ρ i - ρ k‖ * κ i k ≤ ∑ i ∈ Ico j k, (∑ l ∈ Ico i k, u l) * κ i k :=
            sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (F2 i k (mem_Ico.1 hi).2.le)
              (hκ0 i k)
        _ = ∑ l ∈ Ico j k, ∑ i ∈ Icc j l, u l * κ i k := by
            simp only [sum_mul]
            exact Finset.sum_comm' fun i l => by simp only [mem_Ico, mem_Icc]; omega
        _ = ∑ l ∈ Ico j k, (∑ i ∈ Icc j l, κ i k) * u l := by
            refine sum_congr rfl fun l _ => ?_
            rw [sum_mul]; exact sum_congr rfl fun i _ => mul_comm _ _
    have hsum2 : ∑ i ∈ Ico j k, ‖ρ k‖ * lam i k ≤
        (∑ l ∈ Ico j k, u l) * ∑ i ∈ Ico j k, lam i k := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_right hS (sum_nonneg fun i _ => hl0 i k)
    have hm1 : ‖ρ k‖ * ε k ≤ (∑ l ∈ Ico j k, u l) * ε k :=
      mul_le_mul_of_nonneg_right hS (hε0 k)
    have hma : ∑ i ∈ Icc j k, a i k * ‖ρ i‖ ≤ (∑ l ∈ Ico j k, u l) * ∑ i ∈ Icc j k, a i k := by
      rw [mul_sum]
      refine sum_le_sum fun i hi => ?_
      have hi' := mem_Icc.1 hi
      have h5 : ‖ρ i‖ ≤ ∑ l ∈ Ico j k, u l :=
        (F1 i hi'.1).trans (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hi'.2)
          fun l _ _ => norm_nonneg _)
      rw [mul_comm (∑ l ∈ Ico j k, u l)]
      exact mul_le_mul_of_nonneg_left h5 (ha0 i k)
    have hm2 : ‖ρ k‖ * ∑ i ∈ range j, μ i k ≤ (∑ l ∈ Ico j k, u l) * ∑ i ∈ range j, μ i k :=
      mul_le_mul_of_nonneg_right hS (sum_nonneg fun i _ => hμ0 i k)
    rw [sum_add_distrib] at hu2
    calc u k ≤ _ := hu2
      _ ≤ (∑ l ∈ Ico j k, u l) * ε k + (∑ l ∈ Ico j k, u l) * ∑ i ∈ Icc j k, a i k +
          (∑ l ∈ Ico j k, u l) * ∑ i ∈ range j, μ i k +
          (∑ l ∈ Ico j k, (∑ i ∈ Icc j l, κ i k) * u l +
            (∑ l ∈ Ico j k, u l) * ∑ i ∈ Ico j k, lam i k) + s k := by
          gcongr
      _ = _ := by ring
  have hV := volterra_sum_le u (fun k => ε k + ∑ i ∈ Icc j k, a i k + ∑ i ∈ Ico j k, lam i k + ∑ i ∈ range j, μ i k) s
    (fun l k => ∑ i ∈ Icc j l, κ i k) j M (fun k => norm_nonneg _)
    (fun k => add_nonneg (add_nonneg (add_nonneg (hε0 k) (sum_nonneg fun i _ => ha0 i k))
      (sum_nonneg fun i _ => hl0 i k))
      (sum_nonneg fun i _ => hμ0 i k)) hs0 (fun l k => sum_nonneg fun i _ => hκ0 i k) F3 hcol
  intro k hk hkM
  rw [hrρ k hk hkM, norm_mul]
  exact mul_le_mul_of_nonneg_right ((F1 k hk).trans (hV k hk hkM)) (norm_nonneg _)

/-! ### Geometric kernels -/

/-- **`rel_gronwall_geom` with `r`-proportional errors.** -/
theorem rel_gronwall_geomR (r β n e E : ℕ → ℂ) (t : ℕ → ℕ → ℂ) (s ε g : ℕ → ℝ)
    (η : ℕ → ℕ → ℝ) (c B' q : ℝ)
    (j M : ℕ) (hj : 1 ≤ j) (hr0 : r j = 0) (hs0 : ∀ k, 0 ≤ s k) (hε0 : ∀ k, 0 ≤ ε k) (hη0 : ∀ i k, 0 ≤ η i k)
    (hc : 0 ≤ c) (hB' : 0 ≤ B') (hq0 : 0 ≤ q) (hq : q ≤ 2 / 49)
    (hr : ∀ k, j ≤ k → k < M → r (k + 1) = (1 - n k) * r k -
      ∑ i ∈ range k, ((if j ≤ i then r i else 0) - r k) * t i k - E k)
    (hβ : ∀ k, j ≤ k → k < M → β (k + 1) = (1 - n k) * β k - e k)
    (hβ0 : ∀ k, j ≤ k → k ≤ M → β k ≠ 0)
    (hE : ∀ k, j ≤ k → k < M → ‖E k‖ ≤ s k * ‖β (k + 1)‖ + ∑ i ∈ Icc j k, η i k * ‖r i‖)
    (he : ∀ k, j ≤ k → k < M → ‖e k‖ ≤ ε k * ‖β (k + 1)‖)
    (hε1 : ∀ k, j ≤ k → k < M → ε k ≤ 1 / 7)
    (hn8 : ∀ k, j ≤ k → k < M → ‖n k‖ ≤ 1 / 8)
    (hnB : ∀ k, j ≤ k → k + 1 < M → ‖n k‖ ≤ B' * g k)
    (ht : ∀ k, j ≤ k → k < M → ∀ i < k, ‖t i k‖ ≤ c * q ^ (k - i) * g i)
    (hg0 : ∀ i, 0 ≤ g i) (hcg : ∀ i < M, c * g i ≤ 1)
    (hgm : ∀ i l, i ≤ l → l < M → g i ≤ g l) :
    ∀ k, j ≤ k → k ≤ M → ‖r k‖ ≤ 2 * (∑ i ∈ Ico j M, s i) *
      Real.exp (2 * (∑ i ∈ Ico j M, ε i +
        ∑ k ∈ Ico j M, ∑ i ∈ Icc j k, (64 / 49) ^ (k + 1 - i) * η i k +
        1 / 16 * ∑ l ∈ Ico j M, (if l + 1 < M then 64 / 49 * B' * c * g l ^ 2 + ε l else 0) +
        64 / 49 / 16)) * ‖β k‖ := by
  set a : ℝ := 64 / 49 with ha
  set x : ℝ := a * q with hxd
  have hx0 : 0 ≤ x := mul_nonneg (by norm_num) hq0
  have hx : x ≤ 1 / 18 := by
    have : a * q ≤ a * (2 / 49) := mul_le_mul_of_nonneg_left hq (by norm_num)
    simp only [hxd]; linarith
  have hq18 : q ≤ 1 / 18 := by linarith
  set h : ℕ → ℝ := fun l => if l + 1 < M then a * B' * c * g l ^ 2 + ε l else 0 with hhd
  have hh0 : ∀ l, 0 ≤ h l := fun l => by
    simp only [hhd]; split_ifs with hl
    · exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB') hc) (sq_nonneg _))
        (hε0 l)
    · exact le_rfl
  -- ratio bounds of the vertex
  have r1 : ∀ l, j ≤ l → l < M → ‖β l‖ ≤ a * ‖β (l + 1)‖ := by
    intro l h1 h2
    have hb := hβ l h1 h2
    have he' := he l h1 h2
    have hn' := hn8 l h1 h2
    have hε' := hε1 l h1 h2
    have h3 : ‖(1 - n l) * β l‖ ≤ (1 + 1 / 7) * ‖β (l + 1)‖ := by
      have : (1 - n l) * β l = β (l + 1) + e l := by rw [hb]; ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      have : ε l * ‖β (l + 1)‖ ≤ 1 / 7 * ‖β (l + 1)‖ :=
        mul_le_mul_of_nonneg_right hε' (norm_nonneg _)
      linarith
    have h4 : 7 / 8 * ‖β l‖ ≤ ‖(1 - n l) * β l‖ := by
      rw [norm_mul]
      have : 7 / 8 ≤ ‖1 - n l‖ := by
        have := norm_sub_norm_le (1 : ℂ) (n l)
        rw [norm_one] at this; linarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have : ‖β l‖ ≤ 8 / 7 * ((1 + 1 / 7) * ‖β (l + 1)‖) := by linarith
    simp only [ha]; linarith
  have rN : ∀ d i, j ≤ i → i + d ≤ M → ‖β i‖ ≤ a ^ d * ‖β (i + d)‖ := by
    intro d
    induction d with
    | zero => intro i _ _; simp
    | succ d ih =>
      intro i hi hid
      refine (ih i hi (by omega)).trans ?_
      rw [pow_succ, mul_assoc, show i + (d + 1) = i + d + 1 by omega]
      exact mul_le_mul_of_nonneg_left (r1 (i + d) (by omega) (by omega)) (by positivity)
  have ha1 : 1 ≤ a := by simp only [ha]; norm_num
  -- the kernels
  have hκ : ∀ k, j ≤ k → k < M → ∀ i ∈ Ico j k, ‖β i‖ * ‖t i k‖ ≤
      (a ^ (k + 1 - i) * (c * q ^ (k - i) * g i)) * ‖β (k + 1)‖ := by
    intro k hk hkM i hi
    have hi' := mem_Ico.1 hi
    have h1 := rN (k + 1 - i) i hi'.1 (by omega)
    rw [show i + (k + 1 - i) = k + 1 by omega] at h1
    have h2 := ht k hk hkM i hi'.2
    calc ‖β i‖ * ‖t i k‖ ≤ (a ^ (k + 1 - i) * ‖β (k + 1)‖) * (c * q ^ (k - i) * g i) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = _ := by ring
  have hμ : ∀ k, j ≤ k → k < M → ∀ i ∈ range j, ‖β k‖ * ‖t i k‖ ≤
      (a * q ^ (k - i)) * ‖β (k + 1)‖ := by
    intro k hk hkM i hi
    have hi' := mem_range.1 hi
    have h1 := r1 k hk hkM
    have h2 := ht k hk hkM i (by omega)
    have h3 : c * q ^ (k - i) * g i ≤ q ^ (k - i) := by
      have := hcg i (by omega)
      calc c * q ^ (k - i) * g i = q ^ (k - i) * (c * g i) := by ring
        _ ≤ q ^ (k - i) * 1 := mul_le_mul_of_nonneg_left this (pow_nonneg hq0 _)
        _ = _ := mul_one _
    calc ‖β k‖ * ‖t i k‖ ≤ (a * ‖β (k + 1)‖) * q ^ (k - i) :=
          mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hlam : ∀ k, j ≤ k → k < M → ∀ i ∈ Ico j k, ‖β i - β k‖ * ‖t i k‖ ≤
      (x ^ (k - i) * ∑ l ∈ Ico i k, h l) * ‖β (k + 1)‖ := by
    intro k hk hkM i hi
    have hi' := mem_Ico.1 hi
    -- increments of the vertex
    have hinc : ∀ l, i ≤ l → l < k → ‖β (l + 1) - β l‖ ≤
        (a * B' * g l + ε l) * a ^ (k - i) * ‖β (k + 1)‖ := by
      intro l hl1 hl2
      have hb := hβ l (by omega) (by omega)
      have e1 : β (l + 1) - β l = -(n l * β l) - e l := by rw [hb]; ring
      have h1 : ‖β (l + 1) - β l‖ ≤ ‖n l‖ * ‖β l‖ + ε l * ‖β (l + 1)‖ := by
        rw [e1]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul]
        exact add_le_add le_rfl (he l (by omega) (by omega))
      have h2 : ‖n l‖ * ‖β l‖ ≤ (B' * g l) * (a * ‖β (l + 1)‖) :=
        mul_le_mul (hnB l (by omega) (by omega)) (r1 l (by omega) (by omega)) (norm_nonneg _)
          (mul_nonneg hB' (hg0 l))
      have h3 : ‖β (l + 1)‖ ≤ a ^ (k - i) * ‖β (k + 1)‖ := by
        have := rN (k - l) (l + 1) (by omega) (by omega)
        rw [show l + 1 + (k - l) = k + 1 by omega] at this
        refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        exact pow_le_pow_right₀ ha1 (by omega)
      have h4 : 0 ≤ a * B' * g l + ε l :=
        add_nonneg (mul_nonneg (mul_nonneg (by positivity) hB') (hg0 l)) (hε0 l)
      calc ‖β (l + 1) - β l‖ ≤ (a * B' * g l + ε l) * ‖β (l + 1)‖ := by
            have := h1.trans (add_le_add h2 le_rfl); linarith
        _ ≤ (a * B' * g l + ε l) * (a ^ (k - i) * ‖β (k + 1)‖) :=
            mul_le_mul_of_nonneg_left h3 h4
        _ = _ := by ring
    have htel : ∀ k', i ≤ k' → k' ≤ k → ‖β i - β k'‖ ≤
        ∑ l ∈ Ico i k', (a * B' * g l + ε l) * a ^ (k - i) * ‖β (k + 1)‖ := by
      intro k' hk'
      induction k', hk' using Nat.le_induction with
      | base => intro _; rw [sub_self, norm_zero, Ico_self, sum_empty]
      | succ k' hk' ih =>
        intro hk'k
        rw [sum_Ico_succ_top hk']
        calc ‖β i - β (k' + 1)‖ = ‖(β i - β k') - (β (k' + 1) - β k')‖ := by congr 1; ring
          _ ≤ ‖β i - β k'‖ + ‖β (k' + 1) - β k'‖ := norm_sub_le _ _
          _ ≤ _ := add_le_add (ih (by omega)) (hinc k' hk' (by omega))
    have h5 := htel k hi'.2.le le_rfl
    have h6 := ht k hk hkM i hi'.2
    have hgi := hg0 i
    have hcgi := hcg i (by omega)
    calc ‖β i - β k‖ * ‖t i k‖
        ≤ (∑ l ∈ Ico i k, (a * B' * g l + ε l) * a ^ (k - i) * ‖β (k + 1)‖) *
            (c * q ^ (k - i) * g i) := mul_le_mul h5 h6 (norm_nonneg _) (le_trans (norm_nonneg _) h5)
      _ = x ^ (k - i) * (∑ l ∈ Ico i k, (a * B' * (c * g i) * g l + (c * g i) * ε l)) *
            ‖β (k + 1)‖ := by
          rw [sum_mul, mul_sum, sum_mul]
          refine sum_congr rfl fun l _ => ?_
          simp only [hxd, mul_pow]; ring
      _ ≤ x ^ (k - i) * (∑ l ∈ Ico i k, h l) * ‖β (k + 1)‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sum_le_sum fun l hl => ?_)
            (pow_nonneg hx0 _)) (norm_nonneg _)
          have hl' := mem_Ico.1 hl
          simp only [hhd, if_pos (show l + 1 < M by omega)]
          have hgl := hg0 l
          have hgil := hgm i l hl'.1 (by omega)
          have e1 : a * B' * (c * g i) * g l ≤ a * B' * c * g l ^ 2 := by
            have : c * g i ≤ c * g l := mul_le_mul_of_nonneg_left hgil hc
            have h0 : 0 ≤ a * B' := mul_nonneg (by positivity) hB'
            calc a * B' * (c * g i) * g l ≤ a * B' * (c * g l) * g l :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) hgl
              _ = _ := by ring
          have e2 : c * g i * ε l ≤ ε l := by
            have := mul_le_mul_of_nonneg_right hcgi (hε0 l); linarith
          linarith
  have hcol : ∀ l, j ≤ l → l < M → ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l,
      a ^ (k + 1 - i) * (c * q ^ (k - i) * g i) ≤ 1 / 2 := by
    intro l hl hlM
    have hb : ∀ k ∈ Ioo l M, ∀ i ∈ Icc j l, a ^ (k + 1 - i) * (c * q ^ (k - i) * g i) ≤
        a * x ^ (k - i) := by
      intro k hk i hi
      have hk' := mem_Ioo.1 hk
      have hi' := mem_Icc.1 hi
      have := hcg i (by omega)
      rw [show k + 1 - i = k - i + 1 by omega, pow_succ, hxd, mul_pow]
      calc a ^ (k - i) * a * (c * q ^ (k - i) * g i) =
            a * (a ^ (k - i) * q ^ (k - i)) * (c * g i) := by ring
        _ ≤ a * (a ^ (k - i) * q ^ (k - i)) * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    calc ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l, a ^ (k + 1 - i) * (c * q ^ (k - i) * g i)
        ≤ ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l, a * x ^ (k - i) :=
          sum_le_sum fun k hk => sum_le_sum fun i hi => hb k hk i hi
      _ = a * ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l, x ^ (k - i) := by simp only [mul_sum]
      _ ≤ a * (1 / 16) := mul_le_mul_of_nonneg_left (dsum_le hx0 hx j l M) (by positivity)
      _ ≤ 1 / 2 := by simp only [ha]; norm_num
  have hE' : ∀ k, j ≤ k → k < M → ‖E k‖ ≤ s k * ‖β (k + 1)‖ +
      (∑ i ∈ Icc j k, a ^ (k + 1 - i) * η i k * ‖r i / β i‖) * ‖β (k + 1)‖ := by
    intro k hk hkM
    have h2 : ∀ i ∈ Icc j k, η i k * ‖r i‖ ≤
        a ^ (k + 1 - i) * η i k * ‖r i / β i‖ * ‖β (k + 1)‖ := by
      intro i hi
      have hi' := mem_Icc.1 hi
      have hb : 0 < ‖β i‖ := norm_pos_iff.2 (hβ0 i hi'.1 (by omega))
      have h3 := rN (k + 1 - i) i hi'.1 (by omega)
      rw [show i + (k + 1 - i) = k + 1 by omega] at h3
      rw [norm_div]
      calc η i k * ‖r i‖ = η i k * (‖r i‖ / ‖β i‖ * ‖β i‖) := by
            rw [div_mul_cancel₀ _ hb.ne']
        _ ≤ η i k * (‖r i‖ / ‖β i‖ * (a ^ (k + 1 - i) * ‖β (k + 1)‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (hη0 i k)
        _ = _ := by ring
    refine (hE k hk hkM).trans ?_
    rw [sum_mul]
    have := sum_le_sum h2
    linarith
  have hG := rel_gronwall_memR r β n e E t s ε (fun i k => a ^ (k + 1 - i) * η i k) (fun i k => a ^ (k + 1 - i) * (c * q ^ (k - i) * g i))
    (fun i k => x ^ (k - i) * ∑ l ∈ Ico i k, h l) (fun i k => a * q ^ (k - i)) j M hr0 hs0 hε0
    (fun i k => mul_nonneg (by positivity) (hη0 i k))
    (fun i k => mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hc (pow_nonneg hq0 _)) (hg0 i)))
    (fun i k => mul_nonneg (pow_nonneg hx0 _) (sum_nonneg fun l _ => hh0 l))
    (fun i k => mul_nonneg (by positivity) (pow_nonneg hq0 _)) hr hβ hβ0 hE' he hκ hlam hμ hcol
  -- the weight
  have hW : ∑ k ∈ Ico j M, (ε k + ∑ i ∈ Icc j k, a ^ (k + 1 - i) * η i k +
      ∑ i ∈ Ico j k, x ^ (k - i) * ∑ l ∈ Ico i k, h l +
      ∑ i ∈ range j, a * q ^ (k - i)) ≤
      ∑ i ∈ Ico j M, ε i + ∑ k ∈ Ico j M, ∑ i ∈ Icc j k, a ^ (k + 1 - i) * η i k +
        1 / 16 * ∑ l ∈ Ico j M, h l + a / 16 := by
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    have h1 := triple_le hx0 hx h hh0 j M
    have h2 : ∑ k ∈ Ico j M, ∑ i ∈ range j, a * q ^ (k - i) ≤ a / 16 := by
      have hsub1 : Ico j M ⊆ Ioo (j - 1) M := by
        intro k hk; simp only [mem_Ico, mem_Ioo] at hk ⊢; omega
      have hsub2 : range j ⊆ Icc 0 (j - 1) := by
        intro i hi; simp only [mem_range, mem_Icc] at hi ⊢; omega
      calc ∑ k ∈ Ico j M, ∑ i ∈ range j, a * q ^ (k - i)
          ≤ ∑ k ∈ Ioo (j - 1) M, ∑ i ∈ Icc 0 (j - 1), a * q ^ (k - i) := by
            refine (sum_le_sum fun k _ => sum_le_sum_of_subset_of_nonneg hsub2
              fun i _ _ => by positivity).trans ?_
            exact sum_le_sum_of_subset_of_nonneg hsub1 fun k _ _ =>
              sum_nonneg fun i _ => by positivity
        _ = a * ∑ k ∈ Ioo (j - 1) M, ∑ i ∈ Icc 0 (j - 1), q ^ (k - i) := by simp only [mul_sum]
        _ ≤ a * (1 / 16) := mul_le_mul_of_nonneg_left (dsum_le hq0 hq18 0 (j - 1) M)
            (by positivity)
        _ = a / 16 := by ring
    linarith
  intro k hk hkM
  refine (hG k hk hkM).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hW (by norm_num)))
    (mul_nonneg (by norm_num) (sum_nonneg fun i _ => hs0 i))) (norm_nonneg _))



/-- **Summable weights of a geometric memory kernel.** If `0 ≤ a`, `0 ≤ θ`, `aθ ≤ 1/2` and
`w ≥ 0`, then `∑_{j≤k<M}∑_{j≤i<k}a^{k+1-i}θ^{k-1-i}w_i ≤ 2a²∑_{j≤i<M}w_i`. (With `a = 64/49` and
`θ` the contraction of the `K` recursion this bounds the `η`-weight of `rel_gronwall_geomR` produced
by the `r'`-proportional part of the activity sizes, `kseqF` being linear in the `V`-sizes.) -/
theorem geom_kernel_weight_le {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) (haθ : a * θ ≤ 1 / 2)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (j M : ℕ) :
    ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, a ^ (k + 1 - i) * θ ^ (k - 1 - i) * w i ≤
      2 * a ^ 2 * ∑ i ∈ Ico j M, w i := by
  have hswap : ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, a ^ (k + 1 - i) * θ ^ (k - 1 - i) * w i =
      ∑ i ∈ Ico j M, ∑ k ∈ Ioo i M, a ^ (k + 1 - i) * θ ^ (k - 1 - i) * w i := by
    refine Finset.sum_comm' fun k i => ?_
    simp only [mem_Ico, mem_Ioo]; omega
  rw [hswap, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hx0 : 0 ≤ a * θ := mul_nonneg ha hθ
  have hterm : ∀ k ∈ Ioo i M, a ^ (k + 1 - i) * θ ^ (k - 1 - i) * w i =
      a ^ 2 * w i * (a * θ) ^ (k - 1 - i) := by
    intro k hk
    have hk' := mem_Ioo.1 hk
    rw [show k + 1 - i = (k - 1 - i) + 2 by omega, pow_add, mul_pow]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hg : ∑ k ∈ Ioo i M, (a * θ) ^ (k - 1 - i) ≤ 2 := by
    have e : ∑ k ∈ Ioo i M, (a * θ) ^ (k - 1 - i) = ∑ d ∈ range (M - (i + 1)), (a * θ) ^ d := by
      rcases Nat.lt_or_ge (i + 1) M with h | h
      · rw [← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range]
        exact sum_congr rfl fun d _ => by congr 1; omega
      · rw [show M - (i + 1) = 0 by omega, range_zero, sum_empty]
        exact sum_eq_zero fun k hk => by have := mem_Ioo.1 hk; omega
    rw [e]
    have hlt : a * θ < 1 := by linarith
    have h1 := geom_sum_Ico_le_of_lt_one (n := M - (i + 1)) (m := 0) hx0 hlt
    rw [Nat.Ico_zero_eq_range] at h1
    have h2 : 1 / (1 - a * θ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    rw [pow_zero] at h1
    linarith
  have := mul_le_mul_of_nonneg_left hg (mul_nonneg (sq_nonneg a) (hw i))
  linarith

end Obs2
