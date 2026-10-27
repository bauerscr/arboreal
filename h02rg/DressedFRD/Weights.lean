import DressedFRD.Series

/-!
# The weights `W_m` and `ω` (`e:mult`)

`W_m = θ^{-L^m/256}` and, at time `j`, `ω(ℓ) = θ^{-r̄(ℓ)/(128 L^j)}` for a letter with range
bound `r̄(ℓ)` (we store `2r̄` in `rbV`, so `ω = θ^{-rbV/(256 L^j)}`). Then
* `prod_omg`: `∏_i ω(w_i) = θ^{-2r̄(w)/(256 L^j)}`, so the weights are multiplicative;
* `Wt_le_prod_omg` is `e:mult`: `W_{s-1-j} ≤ ∏_i ω(w_i)` if `2r̄(w) ≥ L^{s-1}`;
* `omg_none_le`, `omg_some_le`: `ω(std) ≤ θ^{-3/256}`, `ω(tail_r) ≤ θ^{-2/256} W_{r-j}`.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

/-- `W_m = θ^{-L^m/256}`. -/
def Wt (θ L : ℝ) (m : ℕ) : ℝ := θ ^ (-(L ^ m) / 256)

theorem Wt_pos {θ : ℝ} (hθ : 0 < θ) (L : ℝ) (m : ℕ) : 0 < Wt θ L m := Real.rpow_pos_of_pos hθ _

theorem one_le_Wt {θ L : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 0 ≤ L) (m : ℕ) : 1 ≤ Wt θ L m :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hθ hθ1 (by have := pow_nonneg hL m; linarith)

/-- `W_m / W_{m+1} ≤ θ^{6/256}` for `L ≥ 7`. -/
theorem Wt_succ_ge {θ L : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 7 ≤ L) (m : ℕ) :
    Wt θ L m ≤ θ ^ ((6 : ℝ) / 256) * Wt θ L (m + 1) := by
  unfold Wt
  rw [← Real.rpow_add hθ]
  refine Real.rpow_le_rpow_of_exponent_ge hθ hθ1 ?_
  have h1 : (1 : ℝ) ≤ L ^ m := one_le_pow₀ (by linarith)
  rw [pow_succ]
  nlinarith

namespace Data

variable (D : Data d n)

/-- The letter weights `ω = θ^{-rbV/(256 L^j)}`. -/
def omg (θ : ℝ) (j : ℕ) (κ : Fin 3) (ℓ : Option ℕ) : ℝ :=
  θ ^ (-(D.rbV j κ ℓ : ℝ) / (256 * (D.L : ℝ) ^ j))

variable {D}

theorem omg_pos {θ : ℝ} (hθ : 0 < θ) (j : ℕ) (κ : Fin 3) (ℓ : Option ℕ) : 0 < D.omg θ j κ ℓ :=
  Real.rpow_pos_of_pos hθ _

theorem prod_omg {θ : ℝ} (hθ : 0 < θ) (j : ℕ) {k : ℕ} (w : Fin (k + 2) → Option ℕ) :
    ∏ i, D.omg θ j (kindOf i) (w i) = θ ^ (-(rbar (D.rbV j) w : ℝ) / (256 * (D.L : ℝ) ^ j)) := by
  unfold omg rbar
  rw [← Real.rpow_sum_of_pos hθ]
  congr 1
  push_cast
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- `e:mult`: `W_{s-1-j} ≤ ∏_i ω(w_i)` if `2 r̄(w) ≥ L^{s-1}` and `s ≥ j + 1`. -/
theorem Wt_le_prod_omg {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ D.L) {j s : ℕ}
    (hs : j + 1 ≤ s) {k : ℕ} (w : Fin (k + 2) → Option ℕ)
    (hw : D.L ^ (s - 1) ≤ rbar (D.rbV j) w) :
    Wt θ D.L (s - 1 - j) ≤ ∏ i, D.omg θ j (kindOf i) (w i) := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  rw [prod_omg hθ, Wt]
  refine Real.rpow_le_rpow_of_exponent_ge hθ hθ1 ?_
  have hLj : (0 : ℝ) < (D.L : ℝ) ^ j := pow_pos hL0 j
  have e : (D.L : ℝ) ^ (s - 1 - j) = (D.L : ℝ) ^ (s - 1) / (D.L : ℝ) ^ j := by
    rw [eq_div_iff hLj.ne', ← pow_add]; congr 1; omega
  have : ((D.L ^ (s - 1) : ℕ) : ℝ) ≤ (rbar (D.rbV j) w : ℝ) := by exact_mod_cast hw
  push_cast at this
  rw [e, neg_div, neg_div, neg_le_neg_iff, div_div, mul_comm ((D.L : ℝ) ^ j) 256]
  exact div_le_div_of_nonneg_right this (mul_pos (by norm_num) hLj).le

theorem omg_none_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ D.L) (j : ℕ) (κ : Fin 3) :
    D.omg θ j κ none ≤ θ ^ (-(3 : ℝ) / 256) := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hLj : (1 : ℝ) ≤ (D.L : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast hL)
  unfold omg
  refine Real.rpow_le_rpow_of_exponent_ge hθ hθ1 ?_
  have hrb : (D.rbV j κ none : ℝ) ≤ 3 * (D.L : ℝ) ^ j := by
    have : D.rbV j κ none ≤ D.L ^ j + 2 := by fin_cases κ <;> simp [rbV]
    have h2 : ((D.L ^ j + 2 : ℕ) : ℝ) ≤ 3 * (D.L : ℝ) ^ j := by push_cast; linarith
    exact (Nat.cast_le.2 this).trans h2
  rw [neg_div, neg_div, neg_le_neg_iff,
    div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hL0 j)) (by norm_num)]
  nlinarith

theorem omg_some_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ D.L) {j r : ℕ} (hjr : j ≤ r)
    (κ : Fin 3) : D.omg θ j κ (some r) ≤ θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) := by
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hLj : (1 : ℝ) ≤ (D.L : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast hL)
  unfold omg Wt
  rw [← Real.rpow_add hθ]
  refine Real.rpow_le_rpow_of_exponent_ge hθ hθ1 ?_
  have hrb : (D.rbV j κ (some r) : ℝ) ≤ (D.L : ℝ) ^ r + 2 := by
    have : D.rbV j κ (some r) ≤ D.L ^ r + 2 := by fin_cases κ <;> simp [rbV]
    exact_mod_cast this
  have e : (D.L : ℝ) ^ (r - j) = (D.L : ℝ) ^ r / (D.L : ℝ) ^ j := by
    rw [eq_div_iff (pow_pos hL0 j).ne', ← pow_add]; congr 1; omega
  rw [e]
  have hLj0 : (0 : ℝ) < (D.L : ℝ) ^ j := pow_pos hL0 j
  have key : (D.rbV j κ (some r) : ℝ) / (256 * (D.L : ℝ) ^ j) ≤
      2 / 256 + (D.L : ℝ) ^ r / (D.L : ℝ) ^ j / 256 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hLj0)]
    have : 2 / 256 * (256 * (D.L : ℝ) ^ j) ≥ 2 := by nlinarith
    have h2 : (D.L : ℝ) ^ r / (D.L : ℝ) ^ j / 256 * (256 * (D.L : ℝ) ^ j) = (D.L : ℝ) ^ r := by
      field_simp
    nlinarith
  have : -(D.rbV j κ (some r) : ℝ) / (256 * (D.L : ℝ) ^ j) =
      -((D.rbV j κ (some r) : ℝ) / (256 * (D.L : ℝ) ^ j)) := by ring
  rw [this]
  linarith

end Data

end

end DressedFRD
