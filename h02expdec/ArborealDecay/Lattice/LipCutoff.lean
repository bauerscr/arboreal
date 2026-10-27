module

public import Mathlib
public import ArborealDecay.Lattice.Basic
public import ArborealDecay.Lattice.Ball
public import ArborealDecay.Lattice.Cutoff

/-!
# Piecewise-linear cutoff in the sup norm

`lipCutoff r` equals `1` on `‖z‖∞ ≤ 5r/4`, `0` on `‖z‖∞ ≥ 7r/4`, and is affine in `‖z‖∞`
in between.  Its gradient is `≤ 2/r` on nearest-neighbour edges, and only `O(r²)` ordered edges
have non-zero gradient.
-/

@[expose] public section

namespace ArborealDecay.Lattice

open Finset

/-- Piecewise-linear cutoff `max 0 (min 1 ((7r/4 - ‖z‖∞) / (r/2)))`. -/
noncomputable def lipCutoff (r : ℝ) (z : ℤ × ℤ) : ℝ :=
  max 0 (min 1 ((7 * r / 4 - (supNorm z : ℝ)) / (r / 2)))

theorem supNorm_eq_supDist (z : ℤ × ℤ) : supNorm z = supDist z 0 := by
  simp [supDist_eq_supNorm]

theorem abs_supNorm_sub_le {i j : ℤ × ℤ} (h : IsNN i j) : |supNorm i - supNorm j| ≤ 1 := by
  rw [supNorm_eq_supDist, supNorm_eq_supDist]; exact abs_supDist_sub_le h 0

theorem abs_clamp_sub_le (a b : ℝ) :
    |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by
  have h1 : a - b ≤ |a - b| := le_abs_self _
  have h2 : b - a ≤ |a - b| := by rw [abs_sub_comm]; exact le_abs_self _
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

variable {r : ℝ}

theorem lipCutoff_nonneg (z : ℤ × ℤ) : 0 ≤ lipCutoff r z := le_max_left _ _

theorem lipCutoff_le_one (z : ℤ × ℤ) : lipCutoff r z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem lipCutoff_eq_one (hr : 0 < r) {z : ℤ × ℤ} (hz : (supNorm z : ℝ) ≤ 5 * r / 4) :
    lipCutoff r z = 1 := by
  unfold lipCutoff
  have : 1 ≤ (7 * r / 4 - (supNorm z : ℝ)) / (r / 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [min_eq_left this]; simp

theorem lipCutoff_eq_zero (hr : 0 < r) {z : ℤ × ℤ} (hz : 7 * r / 4 ≤ (supNorm z : ℝ)) :
    lipCutoff r z = 0 := by
  unfold lipCutoff
  have : (7 * r / 4 - (supNorm z : ℝ)) / (r / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [max_eq_left]; exact (min_le_right _ _).trans this

/-- Linear between the two square boundaries. -/
theorem lipCutoff_eq_linear (hr : 0 < r) {z : ℤ × ℤ} (h1 : 5 * r / 4 ≤ (supNorm z : ℝ))
    (h2 : (supNorm z : ℝ) ≤ 7 * r / 4) :
    lipCutoff r z = (7 * r / 4 - (supNorm z : ℝ)) / (r / 2) := by
  unfold lipCutoff
  have a : 1 ≥ (7 * r / 4 - (supNorm z : ℝ)) / (r / 2) := by
    rw [ge_iff_le, div_le_iff₀ (by positivity)]; linarith
  have b : 0 ≤ (7 * r / 4 - (supNorm z : ℝ)) / (r / 2) :=
    div_nonneg (by linarith) (by positivity)
  rw [min_eq_right a, max_eq_right b]

/-- Gradient bound on nearest-neighbour edges. -/
theorem abs_lipCutoff_sub_le (hr : 0 < r) {i j : ℤ × ℤ} (h : IsNN i j) :
    |lipCutoff r i - lipCutoff r j| ≤ 2 / r := by
  unfold lipCutoff
  refine (abs_clamp_sub_le _ _).trans ?_
  have e : (7 * r / 4 - (supNorm i : ℝ)) / (r / 2) - (7 * r / 4 - (supNorm j : ℝ)) / (r / 2) =
      ((supNorm j : ℝ) - (supNorm i : ℝ)) * (2 / r) := by field_simp; ring
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 / r)]
  have : |((supNorm j : ℤ) : ℝ) - ((supNorm i : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_sub, ← Int.cast_abs, abs_sub_comm]; exact_mod_cast abs_supNorm_sub_le h
  have h2 : 0 < 2 / r := by positivity
  nlinarith

/-- Ordered nearest-neighbour pairs inside the square of radius `N`. -/
theorem card_edgePairs_le (y : ℤ × ℤ) (N : ℤ) :
    (edgePairs y N).card ≤ 4 * (ball y N).card := by
  have hsub : edgePairs y N ⊆ (ball y N).biUnion (fun i => (nbrs i).image (fun j => (i, j))) := by
    intro p hp
    have := mem_edgePairs.mp hp
    simp only [Finset.mem_biUnion, Finset.mem_image]
    exact ⟨p.1, mem_ball.mpr this.1, p.2, mem_nbrs.mpr this.2.2, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  calc _ ≤ ∑ _i ∈ ball y N, 4 := Finset.sum_le_sum fun i _ =>
        Finset.card_image_le.trans (card_nbrs_le i)
    _ = _ := by simp [mul_comm]

/-- Edges (ordered) where `lipCutoff r` has non-zero gradient, among pairs in the square of
radius `⌈7r/4⌉`. -/
noncomputable def gradEdges (r : ℝ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  open Classical in
  (edgePairs 0 (⌈7 * r / 4⌉₊ : ℤ)).filter (fun p => lipCutoff r p.1 ≠ lipCutoff r p.2)

/-- Every nearest-neighbour edge with non-zero gradient lies in `gradEdges r`. -/
theorem mem_gradEdges_of_ne (hr : 0 < r) {i j : ℤ × ℤ} (h : IsNN i j)
    (hne : lipCutoff r i ≠ lipCutoff r j) : (i, j) ∈ gradEdges r := by
  classical
  have key : ∀ a b : ℤ × ℤ, IsNN a b → (supNorm a : ℝ) < 7 * r / 4 →
      supNorm a ≤ ⌈7 * r / 4⌉₊ - 1 ∧ supNorm b ≤ ⌈7 * r / 4⌉₊ := by
    intro a b hab ha
    have h1 : (supNorm a : ℝ) < ⌈7 * r / 4⌉₊ := lt_of_lt_of_le ha (Nat.le_ceil _)
    have h2 : supNorm a < ⌈7 * r / 4⌉₊ := by exact_mod_cast h1
    have := abs_supNorm_sub_le hab
    rw [abs_le] at this; omega
  have hs : ∀ z : ℤ × ℤ, supDist 0 z = supNorm z := by
    intro z; rw [supDist_comm, supNorm_eq_supDist]
  have : (supNorm i : ℝ) < 7 * r / 4 ∨ (supNorm j : ℝ) < 7 * r / 4 := by
    by_contra hc
    push Not at hc
    exact hne ((lipCutoff_eq_zero hr hc.1).trans (lipCutoff_eq_zero hr hc.2).symm)
  have hb : supNorm i ≤ ⌈7 * r / 4⌉₊ ∧ supNorm j ≤ ⌈7 * r / 4⌉₊ := by
    rcases this with h1 | h1
    · have := key i j h h1; exact ⟨by omega, this.2⟩
    · have := key j i h.symm h1; exact ⟨this.2, by omega⟩
  unfold gradEdges
  rw [Finset.mem_filter, mem_edgePairs]
  exact ⟨⟨by rw [hs]; exact hb.1, by rw [hs]; exact hb.2, h⟩, hne⟩

/-- At most `170 r²` ordered edges have non-zero gradient (for `r ≥ 1`). -/
theorem card_gradEdges_le (hr : 1 ≤ r) : ((gradEdges r).card : ℝ) ≤ 170 * r ^ 2 := by
  have hr0 : 0 < r := by linarith
  have h1 : (gradEdges r).card ≤ 4 * (ball 0 (⌈7 * r / 4⌉₊ : ℤ)).card :=
    (Finset.card_filter_le _ _).trans (card_edgePairs_le _ _)
  have h2 := card_ball (0 : ℤ × ℤ) (R := (⌈7 * r / 4⌉₊ : ℤ)) (by positivity)
  have h3 : ((ball 0 (⌈7 * r / 4⌉₊ : ℤ)).card : ℝ) = (2 * (⌈7 * r / 4⌉₊ : ℝ) + 1) ^ 2 := by
    have : ((ball 0 (⌈7 * r / 4⌉₊ : ℤ)).card : ℤ) = (2 * (⌈7 * r / 4⌉₊ : ℤ) + 1) ^ 2 := h2
    exact_mod_cast this
  have h4 : (⌈7 * r / 4⌉₊ : ℝ) ≤ 7 * r / 4 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h5 : (0 : ℝ) ≤ (⌈7 * r / 4⌉₊ : ℝ) := Nat.cast_nonneg _
  have h6 : ((gradEdges r).card : ℝ) ≤ 4 * ((ball 0 (⌈7 * r / 4⌉₊ : ℤ)).card : ℝ) := by
    exact_mod_cast h1
  rw [h3] at h6
  have : 2 * (⌈7 * r / 4⌉₊ : ℝ) + 1 ≤ 13 * r / 2 := by linarith
  have : (2 * (⌈7 * r / 4⌉₊ : ℝ) + 1) ^ 2 ≤ (13 * r / 2) ^ 2 := by gcongr
  nlinarith

end ArborealDecay.Lattice
