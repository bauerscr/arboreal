import Obs2.Flow.MuChainAB

/-!
# Relative Gronwall bound with memory (the drift of the reduced `r` flow)

Pure estimates for the reduced pair coupling in the `𝔫^{(2)}` split
(`Obs2.MuChainAB.srcAB_eq`):
`r_{k+1} = (1 - n_k)r_k - ∑_{i<k}(r̂_i - r_k)t_{ik} - E_k` (`r̂_i = r_i` for `i ≥ j`, `0` below),
compared with the vertex `β_{k+1} = (1 - n_k)β_k - e_k`.

* `volterra_sum_le`: if `u_k ≤ w_kS_k + ∑_{j≤l<k}K_{lk}u_l + s_k` (`S_k = ∑_{j≤l<k}u_l`) and the
  columns of `K` sum to at most `1/2`, then `S_m ≤ 2(∑s)exp(2∑w)`.
* **`rel_gronwall_mem`**: with `ρ_k = r_k/β_k` one has
  `β_{k+1}(ρ_{k+1} - ρ_k) = ρ_ke_k - D_k - E_k`, and
  `r̂_i - r_k = (ρ_i - ρ_k)β_i + ρ_k(β_i - β_k)` (`i ≥ j`), `= -ρ_kβ_k` (`i < j`). Under kernel
  bounds `‖β_i‖‖t_{ik}‖ ≤ κ_{ik}‖β_{k+1}‖`, `‖β_i - β_k‖‖t_{ik}‖ ≤ λ_{ik}‖β_{k+1}‖`,
  `‖β_k‖‖t_{ik}‖ ≤ μ_{ik}‖β_{k+1}‖` this is a Volterra inequality for `u_k = |ρ_{k+1} - ρ_k|`:
  the increments `ρ_i - ρ_k` (the drift cancellation) are absorbed by the column condition on
  `κ`, the rest goes into the Gronwall weight `w_k = ε_k + ∑_iλ_{ik} + ∑_{i<j}μ_{ik}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

open Finset

theorem prod_one_add_le_exp_mem (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, (1 + f i) ≤ Real.exp (∑ i ∈ s, f i) := by
  rw [Real.exp_sum]
  refine prod_le_prod (fun i hi => by linarith [h i hi]) fun i _ => ?_
  have := Real.add_one_le_exp (f i)
  linarith

/-- **Volterra–Gronwall with column-summable memory.** -/
theorem volterra_sum_le (u w s : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (j M : ℕ)
    (hu0 : ∀ k, 0 ≤ u k) (hw0 : ∀ k, 0 ≤ w k) (hs0 : ∀ k, 0 ≤ s k) (hK0 : ∀ l k, 0 ≤ K l k)
    (hu : ∀ k, j ≤ k → k < M →
      u k ≤ w k * ∑ l ∈ Ico j k, u l + ∑ l ∈ Ico j k, K l k * u l + s k)
    (hcol : ∀ l, j ≤ l → l < M → ∑ k ∈ Ioo l M, K l k ≤ 1 / 2) :
    ∀ m, j ≤ m → m ≤ M → ∑ l ∈ Ico j m, u l ≤
      2 * (∑ k ∈ Ico j M, s k) * Real.exp (2 * ∑ k ∈ Ico j M, w k) := by
  set σ := ∑ k ∈ Ico j M, s k with hσ
  have hσ0 : 0 ≤ σ := sum_nonneg fun k _ => hs0 k
  have hA : ∀ m, j ≤ m → m ≤ M → ∑ l ∈ Ico j m, u l ≤
      2 * ∑ k ∈ Ico j m, w k * ∑ l ∈ Ico j k, u l + 2 * σ := by
    intro m hjm hmM
    have h1 : ∑ l ∈ Ico j m, u l ≤ ∑ k ∈ Ico j m,
        (w k * ∑ l ∈ Ico j k, u l + ∑ l ∈ Ico j k, K l k * u l + s k) :=
      sum_le_sum fun k hk => hu k (mem_Ico.1 hk).1 (by have := (mem_Ico.1 hk).2; omega)
    have h2 : ∑ k ∈ Ico j m, ∑ l ∈ Ico j k, K l k * u l =
        ∑ l ∈ Ico j m, ∑ k ∈ Ioo l m, K l k * u l := by
      refine Finset.sum_comm' fun k l => ?_
      simp only [mem_Ico, mem_Ioo]; omega
    have h3 : ∑ l ∈ Ico j m, ∑ k ∈ Ioo l m, K l k * u l ≤ ∑ l ∈ Ico j m, 1 / 2 * u l := by
      refine sum_le_sum fun l hl => ?_
      rw [← sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (hu0 l)
      refine le_trans (sum_le_sum_of_subset_of_nonneg (Ioo_subset_Ioo_right hmM)
        fun k _ _ => hK0 l k) ?_
      exact hcol l (mem_Ico.1 hl).1 (by have := (mem_Ico.1 hl).2; omega)
    have h4 : ∑ k ∈ Ico j m, s k ≤ σ :=
      sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hmM) fun k _ _ => hs0 k
    rw [sum_add_distrib, sum_add_distrib, h2] at h1
    have h5 : ∑ l ∈ Ico j m, 1 / 2 * u l = 1 / 2 * ∑ l ∈ Ico j m, u l := by rw [← mul_sum]
    linarith
  have hB : ∀ m, j ≤ m → m ≤ M → 2 * σ + 2 * ∑ k ∈ Ico j m, w k * ∑ l ∈ Ico j k, u l ≤
      2 * σ * ∏ k ∈ Ico j m, (1 + 2 * w k) := by
    intro m hjm
    induction m, hjm using Nat.le_induction with
    | base => intro _; simp
    | succ m hm ih =>
      intro hmM
      have ih' := ih (by omega)
      have hSm := hA m hm (by omega)
      rw [sum_Ico_succ_top hm, prod_Ico_succ_top hm]
      have hwm := hw0 m
      set Y := 2 * σ + 2 * ∑ k ∈ Ico j m, w k * ∑ l ∈ Ico j k, u l
      calc 2 * σ + 2 * (∑ k ∈ Ico j m, w k * ∑ l ∈ Ico j k, u l + w m * ∑ l ∈ Ico j m, u l)
          = Y + 2 * w m * ∑ l ∈ Ico j m, u l := by ring
        _ ≤ Y + 2 * w m * Y := by
            have := mul_le_mul_of_nonneg_left hSm (show 0 ≤ 2 * w m by linarith)
            linarith
        _ = Y * (1 + 2 * w m) := by ring
        _ ≤ (2 * σ * ∏ k ∈ Ico j m, (1 + 2 * w k)) * (1 + 2 * w m) :=
            mul_le_mul_of_nonneg_right ih' (show (0 : ℝ) ≤ 1 + 2 * w m by linarith)
        _ = _ := by ring
  intro m hjm hmM
  have h1 := hA m hjm hmM
  have h2 := hB m hjm hmM
  have h3 : ∏ k ∈ Ico j m, (1 + 2 * w k) ≤ Real.exp (2 * ∑ k ∈ Ico j M, w k) := by
    refine (prod_one_add_le_exp_mem _ (fun k => 2 * w k) fun k _ => by linarith [hw0 k]).trans
      (Real.exp_le_exp.2 ?_)
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hmM)
      fun k _ _ => hw0 k) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * σ by linarith)
  linarith

/-- **The relative Gronwall bound with memory.** -/
theorem rel_gronwall_mem (r β n e E : ℕ → ℂ) (t : ℕ → ℕ → ℂ) (s ε : ℕ → ℝ) (κ lam μ : ℕ → ℕ → ℝ) (j M : ℕ)
    (hr0 : r j = 0) (hs0 : ∀ k, 0 ≤ s k) (hε0 : ∀ k, 0 ≤ ε k) (hκ0 : ∀ i k, 0 ≤ κ i k)
    (hl0 : ∀ i k, 0 ≤ lam i k) (hμ0 : ∀ i k, 0 ≤ μ i k)
    (hr : ∀ k, j ≤ k → k < M → r (k + 1) = (1 - n k) * r k -
      ∑ i ∈ range k, ((if j ≤ i then r i else 0) - r k) * t i k - E k)
    (hβ : ∀ k, j ≤ k → k < M → β (k + 1) = (1 - n k) * β k - e k)
    (hβ0 : ∀ k, j ≤ k → k ≤ M → β k ≠ 0)
    (hE : ∀ k, j ≤ k → k < M → ‖E k‖ ≤ s k * ‖β (k + 1)‖)
    (he : ∀ k, j ≤ k → k < M → ‖e k‖ ≤ ε k * ‖β (k + 1)‖)
    (hκ : ∀ k, j ≤ k → k < M → ∀ i ∈ Ico j k, ‖β i‖ * ‖t i k‖ ≤ κ i k * ‖β (k + 1)‖)
    (hlam : ∀ k, j ≤ k → k < M → ∀ i ∈ Ico j k, ‖β i - β k‖ * ‖t i k‖ ≤ lam i k * ‖β (k + 1)‖)
    (hμ : ∀ k, j ≤ k → k < M → ∀ i ∈ range j, ‖β k‖ * ‖t i k‖ ≤ μ i k * ‖β (k + 1)‖)
    (hcol : ∀ l, j ≤ l → l < M → ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l, κ i k ≤ 1 / 2) :
    ∀ k, j ≤ k → k ≤ M → ‖r k‖ ≤ 2 * (∑ i ∈ Ico j M, s i) *
      Real.exp (2 * ∑ k ∈ Ico j M, (ε k + ∑ i ∈ Ico j k, lam i k + ∑ i ∈ range j, μ i k)) *
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
      (ε k + ∑ i ∈ Ico j k, lam i k + ∑ i ∈ range j, μ i k) * ∑ l ∈ Ico j k, u l +
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
    have hu1 : ‖β (k + 1)‖ * u k ≤ ‖β (k + 1)‖ * (‖ρ k‖ * ε k + ‖ρ k‖ * ∑ i ∈ range j, μ i k +
        ∑ i ∈ Ico j k, (‖ρ i - ρ k‖ * κ i k + ‖ρ k‖ * lam i k) + s k) := by
      have e2 : ‖β (k + 1)‖ * u k = ‖ρ k * e k - D - E k‖ := by
        simp only [hud]; rw [← norm_mul, hid]
      rw [e2]
      have h3 : ‖ρ k * e k - D - E k‖ ≤ ‖ρ k * e k‖ + ‖D‖ + ‖E k‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      have h4 := add_le_add (add_le_add h1 hDn) (hE k hk hkM)
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
    have hm2 : ‖ρ k‖ * ∑ i ∈ range j, μ i k ≤ (∑ l ∈ Ico j k, u l) * ∑ i ∈ range j, μ i k :=
      mul_le_mul_of_nonneg_right hS (sum_nonneg fun i _ => hμ0 i k)
    rw [sum_add_distrib] at hu2
    calc u k ≤ _ := hu2
      _ ≤ (∑ l ∈ Ico j k, u l) * ε k + (∑ l ∈ Ico j k, u l) * ∑ i ∈ range j, μ i k +
          (∑ l ∈ Ico j k, (∑ i ∈ Icc j l, κ i k) * u l +
            (∑ l ∈ Ico j k, u l) * ∑ i ∈ Ico j k, lam i k) + s k := by
          gcongr
      _ = _ := by ring
  have hV := volterra_sum_le u (fun k => ε k + ∑ i ∈ Ico j k, lam i k + ∑ i ∈ range j, μ i k) s
    (fun l k => ∑ i ∈ Icc j l, κ i k) j M (fun k => norm_nonneg _)
    (fun k => add_nonneg (add_nonneg (hε0 k) (sum_nonneg fun i _ => hl0 i k))
      (sum_nonneg fun i _ => hμ0 i k)) hs0 (fun l k => sum_nonneg fun i _ => hκ0 i k) F3 hcol
  intro k hk hkM
  rw [hrρ k hk hkM, norm_mul]
  exact mul_le_mul_of_nonneg_right ((F1 k hk).trans (hV k hk hkM)) (norm_nonneg _)

/-! ### Geometric kernels -/

theorem geom_tail_le_mem {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) (l M : ℕ) :
    ∑ k ∈ Ioo l M, x ^ (k - l) ≤ x / (1 - x) := by
  have hsub : Ioo l M ⊆ Ico (l + 1) (l + 1 + M) := by
    intro k hk; simp only [mem_Ioo, mem_Ico] at hk ⊢; omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => pow_nonneg hx0 _).trans ?_
  rw [sum_Ico_eq_sum_range, show l + 1 + M - (l + 1) = M by omega]
  have e : ∀ d ∈ range M, x ^ (l + 1 + d - l) = x * x ^ d := fun d _ => by
    rw [show l + 1 + d - l = d + 1 by omega, pow_succ]; ring
  rw [sum_congr rfl e, ← mul_sum]
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := M) hx0 hx
  rw [← range_eq_Ico, pow_zero] at hg
  calc x * ∑ d ∈ range M, x ^ d ≤ x * (1 / (1 - x)) := mul_le_mul_of_nonneg_left hg hx0
    _ = x / (1 - x) := by ring

theorem geom_head_le_mem {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) (j l : ℕ) :
    ∑ i ∈ Icc j l, x ^ (l - i) ≤ 1 / (1 - x) := by
  have hsub : Icc j l ⊆ range (l + 1) := by
    intro i hi; simp only [mem_Icc, mem_range] at hi ⊢; omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pow_nonneg hx0 _).trans ?_
  have e := sum_range_reflect (fun i => x ^ i) (l + 1)
  simp only [Nat.add_sub_cancel] at e
  rw [e]
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := l + 1) hx0 hx
  rwa [← range_eq_Ico, pow_zero] at hg

/-- `∑_{l<k<M}∑_{j≤i≤l}x^{k-i} ≤ 1/16` for `0 ≤ x ≤ 1/18`. -/
theorem dsum_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 18) (j l M : ℕ) :
    ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l, x ^ (k - i) ≤ 1 / 16 := by
  have hx1 : x < 1 := by linarith
  have h1 : ∀ k ∈ Ioo l M, ∑ i ∈ Icc j l, x ^ (k - i) ≤ x ^ (k - l) * (1 / (1 - x)) := by
    intro k hk
    have hlk := (mem_Ioo.1 hk).1
    have e : ∑ i ∈ Icc j l, x ^ (k - i) = x ^ (k - l) * ∑ i ∈ Icc j l, x ^ (l - i) := by
      rw [mul_sum]; refine sum_congr rfl fun i hi => ?_
      rw [← pow_add]; congr 1; have := (mem_Icc.1 hi).2; omega
    rw [e]
    exact mul_le_mul_of_nonneg_left (geom_head_le_mem hx0 hx1 j l) (pow_nonneg hx0 _)
  refine (sum_le_sum h1).trans ?_
  rw [← sum_mul]
  have h2 := geom_tail_le_mem hx0 hx1 l M
  have hpos : 0 < 1 - x := by linarith
  have h3 : x / (1 - x) * (1 / (1 - x)) ≤ 1 / 16 := by
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (mul_pos hpos hpos) (by norm_num)]
    nlinarith [sq_nonneg x]
  calc (∑ k ∈ Ioo l M, x ^ (k - l)) * (1 / (1 - x)) ≤ x / (1 - x) * (1 / (1 - x)) :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt (one_div_pos.2 hpos))
    _ ≤ 1 / 16 := h3

/-- The triple sum of the drift weights. -/
theorem triple_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 18) (h : ℕ → ℝ) (hh : ∀ l, 0 ≤ h l)
    (j M : ℕ) :
    ∑ k ∈ Ico j M, ∑ i ∈ Ico j k, x ^ (k - i) * ∑ l ∈ Ico i k, h l ≤
      1 / 16 * ∑ l ∈ Ico j M, h l := by
  have e1 : ∀ k, ∑ i ∈ Ico j k, x ^ (k - i) * ∑ l ∈ Ico i k, h l =
      ∑ l ∈ Ico j k, ∑ i ∈ Icc j l, x ^ (k - i) * h l := by
    intro k
    simp only [mul_sum]
    exact Finset.sum_comm' fun i l => by simp only [mem_Ico, mem_Icc]; omega
  simp only [e1]
  have e2 : ∑ k ∈ Ico j M, ∑ l ∈ Ico j k, ∑ i ∈ Icc j l, x ^ (k - i) * h l =
      ∑ l ∈ Ico j M, ∑ k ∈ Ioo l M, ∑ i ∈ Icc j l, x ^ (k - i) * h l :=
    Finset.sum_comm' fun k l => by simp only [mem_Ico, mem_Ioo]; omega
  rw [e2, mul_sum]
  refine sum_le_sum fun l _ => ?_
  simp only [← sum_mul]
  exact mul_le_mul_of_nonneg_right (dsum_le hx0 hx j l M) (hh l)

/-- **The relative Gronwall bound with memory, geometric kernels.** `a = 64/49`; the tadpoles
`‖t_{ik}‖ ≤ cq^{k-i}g_i` with `cg_i ≤ 1`, `g` nondecreasing, `q ≤ 2/49`; the vertex flow with
`‖n_k‖ ≤ 1/8`, `‖n_k‖ ≤ B'g_k` (`k + 1 < M`), `ε_k ≤ 1/7`. -/
theorem rel_gronwall_geom (r β n e E : ℕ → ℂ) (t : ℕ → ℕ → ℂ) (s ε g : ℕ → ℝ) (c B' q : ℝ)
    (j M : ℕ) (hj : 1 ≤ j) (hr0 : r j = 0) (hs0 : ∀ k, 0 ≤ s k) (hε0 : ∀ k, 0 ≤ ε k)
    (hc : 0 ≤ c) (hB' : 0 ≤ B') (hq0 : 0 ≤ q) (hq : q ≤ 2 / 49)
    (hr : ∀ k, j ≤ k → k < M → r (k + 1) = (1 - n k) * r k -
      ∑ i ∈ range k, ((if j ≤ i then r i else 0) - r k) * t i k - E k)
    (hβ : ∀ k, j ≤ k → k < M → β (k + 1) = (1 - n k) * β k - e k)
    (hβ0 : ∀ k, j ≤ k → k ≤ M → β k ≠ 0)
    (hE : ∀ k, j ≤ k → k < M → ‖E k‖ ≤ s k * ‖β (k + 1)‖)
    (he : ∀ k, j ≤ k → k < M → ‖e k‖ ≤ ε k * ‖β (k + 1)‖)
    (hε1 : ∀ k, j ≤ k → k < M → ε k ≤ 1 / 7)
    (hn8 : ∀ k, j ≤ k → k < M → ‖n k‖ ≤ 1 / 8)
    (hnB : ∀ k, j ≤ k → k + 1 < M → ‖n k‖ ≤ B' * g k)
    (ht : ∀ k, j ≤ k → k < M → ∀ i < k, ‖t i k‖ ≤ c * q ^ (k - i) * g i)
    (hg0 : ∀ i, 0 ≤ g i) (hcg : ∀ i < M, c * g i ≤ 1)
    (hgm : ∀ i l, i ≤ l → l < M → g i ≤ g l) :
    ∀ k, j ≤ k → k ≤ M → ‖r k‖ ≤ 2 * (∑ i ∈ Ico j M, s i) *
      Real.exp (2 * (∑ i ∈ Ico j M, ε i +
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
  have hG := rel_gronwall_mem r β n e E t s ε (fun i k => a ^ (k + 1 - i) * (c * q ^ (k - i) * g i))
    (fun i k => x ^ (k - i) * ∑ l ∈ Ico i k, h l) (fun i k => a * q ^ (k - i)) j M hr0 hs0 hε0
    (fun i k => mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hc (pow_nonneg hq0 _)) (hg0 i)))
    (fun i k => mul_nonneg (pow_nonneg hx0 _) (sum_nonneg fun l _ => hh0 l))
    (fun i k => mul_nonneg (by positivity) (pow_nonneg hq0 _)) hr hβ hβ0 hE he hκ hlam hμ hcol
  -- the weight
  have hW : ∑ k ∈ Ico j M, (ε k + ∑ i ∈ Ico j k, x ^ (k - i) * ∑ l ∈ Ico i k, h l +
      ∑ i ∈ range j, a * q ^ (k - i)) ≤
      ∑ i ∈ Ico j M, ε i + 1 / 16 * ∑ l ∈ Ico j M, h l + a / 16 := by
    rw [sum_add_distrib, sum_add_distrib]
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

end Obs2
