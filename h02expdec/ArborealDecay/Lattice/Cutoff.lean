module

public import Mathlib
public import ArborealDecay.Lattice.Basic
public import ArborealDecay.Lattice.Ball

/-!
# The discrete logarithmic cutoff (`lem:log-cutoff`)

For `y : ℤ²` and real `R ≥ 4`, `v z = [1 - log r(z) / log R]_+` with `r(z) = max 1 ‖z - y‖∞`.
This vanishes as soon as `‖z - y‖∞ ≥ R`, so no modification of an outermost shell is needed.
-/

@[expose] public section

namespace ArborealDecay.Lattice

open Finset

/-- `r(z) = max 1 ‖z - y‖∞` as a real number. -/
noncomputable def logRadius (y z : ℤ × ℤ) : ℝ := max (supDist y z : ℝ) 1

/-- The logarithmic cutoff `v z = [1 - log r(z) / log R]_+`. -/
noncomputable def logCutoff (y : ℤ × ℤ) (R : ℝ) (z : ℤ × ℤ) : ℝ :=
  max (1 - Real.log (logRadius y z) / Real.log R) 0

theorem one_le_logRadius (y z : ℤ × ℤ) : 1 ≤ logRadius y z := le_max_right _ _

theorem logRadius_pos (y z : ℤ × ℤ) : 0 < logRadius y z :=
  lt_of_lt_of_le one_pos (one_le_logRadius y z)

theorem logRadius_self (y : ℤ × ℤ) : logRadius y y = 1 := by simp [logRadius, supDist_self]

theorem abs_logRadius_sub_le {i j : ℤ × ℤ} (y : ℤ × ℤ) (h : IsNN i j) :
    |logRadius y i - logRadius y j| ≤ 1 := by
  unfold logRadius
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have := abs_supDist_sub_le' h y
  have h2 : |((supDist y i : ℤ) : ℝ) - ((supDist y j : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_sub, ← Int.cast_abs]; exact_mod_cast this
  exact h2

theorem log_sub_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ a + 1) :
    Real.log b - Real.log a ≤ 1 / a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [← Real.log_div hb0.ne' ha0.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hb0 ha0)).trans ?_
  rw [div_sub_one ha0.ne', div_le_div_iff_of_pos_right ha0]
  linarith

theorem abs_log_sub_log_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : |a - b| ≤ 1) :
    |Real.log a - Real.log b| ≤ 2 / a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [abs_le] at hab
  rw [abs_le]
  rcases le_total a b with h | h
  · have := log_sub_log_le ha h (by linarith)
    have hmono := Real.log_le_log ha0 h
    have : 1 / a ≤ 2 / a := by gcongr; norm_num
    constructor <;> linarith [Real.log_le_log ha0 h]
  · have h1 := log_sub_log_le hb h (by linarith)
    have hmono := Real.log_le_log hb0 h
    have : 1 / b ≤ 2 / a := by
      rw [div_le_div_iff₀ hb0 ha0]; linarith
    constructor <;> linarith

section

variable {y : ℤ × ℤ} {R : ℝ}

theorem logCutoff_nonneg (z : ℤ × ℤ) : 0 ≤ logCutoff y R z := le_max_right _ _

theorem logCutoff_le_one (hR : 1 < R) (z : ℤ × ℤ) : logCutoff y R z ≤ 1 := by
  unfold logCutoff
  have hL : 0 < Real.log R := Real.log_pos hR
  have : 0 ≤ Real.log (logRadius y z) / Real.log R :=
    div_nonneg (Real.log_nonneg (one_le_logRadius y z)) hL.le
  exact max_le (by linarith) zero_le_one

theorem logCutoff_self (y : ℤ × ℤ) (R : ℝ) : logCutoff y R y = 1 := by
  simp [logCutoff, logRadius_self]

theorem logCutoff_eq_zero (hR : 1 < R) {z : ℤ × ℤ} (hz : R ≤ (supDist y z : ℝ)) :
    logCutoff y R z = 0 := by
  unfold logCutoff
  have hL : 0 < Real.log R := Real.log_pos hR
  have h1 : R ≤ logRadius y z := hz.trans (le_max_left _ _)
  have h2 : Real.log R ≤ Real.log (logRadius y z) := Real.log_le_log (by linarith) h1
  have : 1 ≤ Real.log (logRadius y z) / Real.log R := by
    rw [le_div_iff₀ hL]; linarith
  exact max_eq_right (by linarith)

/-- Pointwise gradient bound along an edge. -/
theorem abs_logCutoff_sub_le (hR : 1 < R) {i j : ℤ × ℤ} (h : IsNN i j) :
    |logCutoff y R i - logCutoff y R j| ≤ 2 / (logRadius y i * Real.log R) := by
  have hL : 0 < Real.log R := Real.log_pos hR
  unfold logCutoff
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have key := abs_log_sub_log_le (one_le_logRadius y i) (one_le_logRadius y j)
    (abs_logRadius_sub_le y h)
  have e : (1 - Real.log (logRadius y i) / Real.log R) -
      (1 - Real.log (logRadius y j) / Real.log R) =
      -(Real.log (logRadius y i) - Real.log (logRadius y j)) / Real.log R := by ring
  rw [e, abs_div, abs_neg, abs_of_pos hL, div_le_iff₀ hL]
  calc _ ≤ 2 / logRadius y i := key
    _ = _ := by field_simp

theorem abs_logCutoff_sub_le_div (hR : 1 < R) {i j : ℤ × ℤ} (h : IsNN i j) :
    |logCutoff y R i - logCutoff y R j| ≤ 2 / Real.log R := by
  have hL : 0 < Real.log R := Real.log_pos hR
  refine (abs_logCutoff_sub_le (y := y) hR h).trans ?_
  have := one_le_logRadius y i
  rw [div_le_div_iff₀ (by positivity) hL]
  nlinarith

theorem sq_logCutoff_sub_le (hR : 1 < R) {i j : ℤ × ℤ} (h : IsNN i j) :
    (logCutoff y R i - logCutoff y R j) ^ 2 ≤ 4 / (logRadius y i ^ 2 * Real.log R ^ 2) := by
  have hL : 0 < Real.log R := Real.log_pos hR
  have := abs_logCutoff_sub_le (y := y) hR h
  have h0 := logRadius_pos y i
  calc _ = |logCutoff y R i - logCutoff y R j| ^ 2 := (sq_abs _).symm
    _ ≤ (2 / (logRadius y i * Real.log R)) ^ 2 := by gcongr
    _ = _ := by field_simp; ring

end

/-! ### Summation over shells -/

theorem shell_succ (y : ℤ × ℤ) (N : ℕ) :
    shell y ((N + 1 : ℕ) : ℤ) = ball y ((N + 1 : ℕ) : ℤ) \ ball y (N : ℤ) := by
  unfold shell; congr 2; push_cast; ring

theorem sum_inv_logRadius_sq (y : ℤ × ℤ) (N : ℕ) :
    ∑ i ∈ ball y (N : ℤ), 1 / logRadius y i ^ 2 = 1 + 8 * (harmonic N : ℝ) := by
  induction N with
  | zero =>
    have : ball y ((0 : ℕ) : ℤ) = {y} := by
      ext z
      rw [mem_ball, Finset.mem_singleton]
      constructor
      · intro h; exact (supDist_eq_zero.mp (le_antisymm (by exact_mod_cast h)
          (supDist_nonneg y z))).symm
      · rintro rfl; simp [supDist_self]
    rw [this]; simp [logRadius_self]
  | succ N ih =>
    have hsub : ball y (N : ℤ) ⊆ ball y ((N + 1 : ℕ) : ℤ) :=
      ball_mono y (by push_cast; omega)
    rw [← Finset.sum_sdiff hsub, ih, ← shell_succ]
    have hc : ∀ i ∈ shell y ((N + 1 : ℕ) : ℤ), 1 / logRadius y i ^ 2 = 1 / ((N : ℝ) + 1) ^ 2 := by
      intro i hi
      rw [mem_shell] at hi
      have : (supDist y i : ℝ) = (N : ℝ) + 1 := by exact_mod_cast hi
      unfold logRadius
      rw [this, max_eq_left (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    have hcard := card_shell y (k := ((N + 1 : ℕ) : ℤ)) (by omega)
    have hcard' : ((shell y ((N + 1 : ℕ) : ℤ)).card : ℝ) = 8 * ((N : ℝ) + 1) := by
      have : ((shell y ((N + 1 : ℕ) : ℤ)).card : ℤ) = 8 * ((N : ℤ) + 1) := by
        rw [hcard]; push_cast; ring
      exact_mod_cast this
    rw [hcard', harmonic_succ]
    push_cast
    have : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem sum_inv_logRadius_sq_le (y : ℤ × ℤ) (N : ℕ) :
    ∑ i ∈ ball y (N : ℤ), 1 / logRadius y i ^ 2 ≤ 9 + 8 * Real.log N := by
  rw [sum_inv_logRadius_sq]
  have := harmonic_le_one_add_log N
  have h2 : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N := by exact_mod_cast this
  linarith

/-! ### The energy bound -/

/-- The finite set of ordered nearest-neighbour pairs inside the square of radius `N`. -/
def edgePairs (y : ℤ × ℤ) (N : ℤ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (ball y N ×ˢ ball y N).filter (fun p => IsNN p.1 p.2)

theorem mem_edgePairs {y : ℤ × ℤ} {N : ℤ} {p : (ℤ × ℤ) × (ℤ × ℤ)} :
    p ∈ edgePairs y N ↔ supDist y p.1 ≤ N ∧ supDist y p.2 ≤ N ∧ IsNN p.1 p.2 := by
  simp [edgePairs, mem_ball, and_assoc]

theorem energy_le_sum (y : ℤ × ℤ) {R : ℝ} (hR : 1 < R) (N : ℤ) :
    ∑ p ∈ edgePairs y N, (logCutoff y R p.1 - logCutoff y R p.2) ^ 2 ≤
      16 / Real.log R ^ 2 * ∑ i ∈ ball y N, 1 / logRadius y i ^ 2 := by
  have hL : 0 < Real.log R := Real.log_pos hR
  calc ∑ p ∈ edgePairs y N, (logCutoff y R p.1 - logCutoff y R p.2) ^ 2
      ≤ ∑ p ∈ edgePairs y N, 4 * (1 / logRadius y p.1 ^ 2) / Real.log R ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        have h := (mem_edgePairs.mp hp).2.2
        refine (sq_logCutoff_sub_le hR h).trans (le_of_eq ?_)
        field_simp
    _ = ∑ i ∈ ball y N, ∑ j ∈ ball y N,
          if IsNN i j then 4 * (1 / logRadius y i ^ 2) / Real.log R ^ 2 else 0 := by
        rw [edgePairs, Finset.sum_filter, Finset.sum_product]
    _ ≤ ∑ i ∈ ball y N, 4 * (4 * (1 / logRadius y i ^ 2) / Real.log R ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : ((ball y N).filter (IsNN i ·)).card ≤ 4 := by
          refine le_trans (Finset.card_le_card ?_) (card_nbrs_le i)
          intro j hj
          exact mem_nbrs.mpr (Finset.mem_filter.mp hj).2
        have hc' : (((ball y N).filter (IsNN i ·)).card : ℝ) ≤ 4 := by exact_mod_cast hc
        have : 0 ≤ 4 * (1 / logRadius y i ^ 2) / Real.log R ^ 2 := by positivity
        nlinarith
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring

theorem one_lt_log_of_four_le {R : ℝ} (hR : 4 ≤ R) : 1 < Real.log R := by
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have : Real.log 4 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  linarith

theorem energy_le_const (y : ℤ × ℤ) {R : ℝ} (hR : 4 ≤ R) (N : ℕ) (hN : (N : ℝ) ≤ R + 1) :
    ∑ p ∈ edgePairs y (N : ℤ), (logCutoff y R p.1 - logCutoff y R p.2) ^ 2 ≤
      400 / Real.log R := by
  have hL1 := one_lt_log_of_four_le hR
  have hR1 : 1 < R := by linarith
  have hL : 0 < Real.log R := by linarith
  have hlogN : Real.log N ≤ 2 * Real.log R := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp; linarith
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
      calc Real.log N ≤ Real.log (R ^ 2) :=
            Real.log_le_log hN0 (by nlinarith)
        _ = 2 * Real.log R := by rw [Real.log_pow]; norm_num
  refine (energy_le_sum y hR1 N).trans ?_
  have hs := sum_inv_logRadius_sq_le y N
  calc _ ≤ 16 / Real.log R ^ 2 * (9 + 8 * (2 * Real.log R)) := by
        gcongr; linarith
    _ ≤ 400 / Real.log R := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hL]
        nlinarith

theorem mem_ball_floor_iff {R : ℝ} (hR : 0 ≤ R) (d : ℤ) :
    d ≤ ((⌊R⌋₊ : ℤ) + 1) ↔ (d : ℝ) ≤ R + 1 := by
  rw [Int.natCast_floor_eq_floor hR]
  have : d ≤ ⌊R⌋ + 1 ↔ d - 1 ≤ ⌊R⌋ := by omega
  rw [this, Int.le_floor]; push_cast
  constructor <;> intro h <;> linarith

/-- Logarithmic cutoff (`lem:log-cutoff`).  The Dirichlet sum runs over `edgePairs y (⌊R⌋₊ + 1)`,
i.e. over ordered nearest-neighbour pairs with both endpoints at sup distance `≤ R + 1` from
`y` (see `mem_edgePairs_floor`). -/
theorem exists_log_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℤ × ℤ) (R : ℝ), 4 ≤ R →
      ∃ v : ℤ × ℤ → ℝ, (∀ z, 0 ≤ v z ∧ v z ≤ 1) ∧ v y = 1 ∧
        (∀ z, R ≤ (supDist y z : ℝ) → v z = 0) ∧
        (∀ i j, IsNN i j → |v i - v j| ≤ C / Real.log R) ∧
        ∑ p ∈ edgePairs y ((⌊R⌋₊ : ℤ) + 1), (v p.1 - v p.2) ^ 2 ≤ C / Real.log R := by
  refine ⟨400, by norm_num, fun y R hR => ⟨logCutoff y R, ?_, logCutoff_self y R, ?_, ?_, ?_⟩⟩
  · have hR1 : 1 < R := by linarith
    exact fun z => ⟨logCutoff_nonneg z, logCutoff_le_one hR1 z⟩
  · exact fun z hz => logCutoff_eq_zero (by linarith) hz
  · intro i j h
    have hL := one_lt_log_of_four_le hR
    refine (abs_logCutoff_sub_le_div (by linarith) h).trans ?_
    gcongr; norm_num
  · have := energy_le_const y hR (⌊R⌋₊ + 1) (by
      push_cast; linarith [Nat.floor_le (show 0 ≤ R by linarith)])
    simpa using this

theorem mem_edgePairs_floor {y : ℤ × ℤ} {R : ℝ} (hR : 0 ≤ R) {p : (ℤ × ℤ) × (ℤ × ℤ)} :
    p ∈ edgePairs y ((⌊R⌋₊ : ℤ) + 1) ↔
      (supDist y p.1 : ℝ) ≤ R + 1 ∧ (supDist y p.2 : ℝ) ≤ R + 1 ∧ IsNN p.1 p.2 := by
  rw [mem_edgePairs, mem_ball_floor_iff hR, mem_ball_floor_iff hR]

end ArborealDecay.Lattice
