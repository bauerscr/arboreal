import DressedFRD.Std

/-!
# Words (Section `sec:proof`, "Words")

A word of length `k + 2` is a function `w : Fin (k+2) → Option ℕ`. Position `0` is the letter
`a`, position `1` the letter `b`, and positions `2, …, k+1` are the letters `c_1, …, c_k`.
The letter `none` is the standard letter, and `some r` is the tail letter of scale `r`.

* `kindOf i ∈ {0,1,2}` is the kind (`a`, `b` or `c`) of position `i`.
* `wordVal V w = ∏_i V (kindOf i) (w i)` is `O_w`; `rbar RB w = ∑_i RB (kindOf i) (w i)` is
  `2 r̄(w)` (twice the range bound, to stay in `ℕ`).
* `sum_words_prod` is the multinomial expansion `∑_w ∏_i f(i, w_i) = (∑ f_a)(∑ f_b)(∑ f_c)^k`.
* `scale L j N R` is the scale `s(w)` assigned to a word with `2 r̄(w) = R`.
-/

namespace DressedFRD

noncomputable section

open Finset

/-- The kind of a position: `0` for `a`, `1` for `b`, `2` for the `c`'s. -/
def kindOf {k : ℕ} (i : Fin (k + 2)) : Fin 3 :=
  if i.1 = 0 then 0 else if i.1 = 1 then 1 else 2

theorem kindOf_zero {k : ℕ} : kindOf (0 : Fin (k + 2)) = 0 := by simp [kindOf]
theorem kindOf_one {k : ℕ} : kindOf (1 : Fin (k + 2)) = 1 := by simp [kindOf]
theorem kindOf_succ_succ {k : ℕ} (i : Fin k) : kindOf (i.succ.succ : Fin (k + 2)) = 2 := by
  simp [kindOf]

/-- The alphabet at time `j`: the standard letter and the tail letters of scale `r ∈ (j, N]`. -/
def alph (j N : ℕ) : Finset (Option ℕ) := insert none ((Ioc j N).map ⟨some, Option.some_injective _⟩)

theorem none_mem_alph (j N : ℕ) : none ∈ alph j N := mem_insert_self _ _

theorem some_mem_alph {j N r : ℕ} : some r ∈ alph j N ↔ j < r ∧ r ≤ N := by
  simp [alph]

/-- Words of length `k + 2`. -/
def words (j N k : ℕ) : Finset (Fin (k + 2) → Option ℕ) :=
  Fintype.piFinset fun _ => alph j N

/-- `O_w = ∏_i V(kind i, w_i)`. -/
def wordVal {R : Type*} [CommMonoid R] {k : ℕ} (V : Fin 3 → Option ℕ → R)
    (w : Fin (k + 2) → Option ℕ) : R :=
  ∏ i, V (kindOf i) (w i)

/-- `2 r̄(w) = ∑_i RB(kind i, w_i)`. -/
def rbar {k : ℕ} (RB : Fin 3 → Option ℕ → ℕ) (w : Fin (k + 2) → Option ℕ) : ℕ :=
  ∑ i, RB (kindOf i) (w i)

/-- The multinomial expansion. -/
theorem sum_words_prod {R : Type*} [CommSemiring R] (j N k : ℕ) (f : Fin 3 → Option ℕ → R) :
    ∑ w ∈ words j N k, wordVal f w =
      (∑ ℓ ∈ alph j N, f 0 ℓ) * (∑ ℓ ∈ alph j N, f 1 ℓ) * (∑ ℓ ∈ alph j N, f 2 ℓ) ^ k := by
  unfold words wordVal
  rw [← Finset.prod_univ_sum (fun _ => alph j N) (fun i ℓ => f (kindOf i) ℓ)]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [kindOf_succ_succ, prod_const, card_univ, Fintype.card_fin]
  rw [← mul_assoc, kindOf_zero, show (Fin.succ (0 : Fin (k + 1)) : Fin (k + 2)) = 1 from rfl,
    kindOf_one]

/-! ### The scale of a word -/

theorem exists_scale (L j N R : ℕ) : ∃ s, j + 1 ≤ s ∧ (R < L ^ s ∨ N ≤ s) :=
  ⟨max (j + 1) N, le_max_left _ _, Or.inr (le_max_right _ _)⟩

/-- The scale `s(w)` of a word with `2 r̄(w) = R`: the least `s ≥ j+1` with `R < L^s`, capped at
`N`. -/
def scale (L j N R : ℕ) : ℕ := Nat.find (exists_scale L j N R)

variable {L j N R : ℕ}

theorem le_scale : j + 1 ≤ scale L j N R := (Nat.find_spec (exists_scale L j N R)).1

theorem scale_spec : R < L ^ scale L j N R ∨ N ≤ scale L j N R :=
  (Nat.find_spec (exists_scale L j N R)).2

theorem scale_le (hj : j + 1 ≤ N) : scale L j N R ≤ N :=
  Nat.find_min' _ ⟨hj, Or.inr le_rfl⟩

theorem lt_pow_scale (h : scale L j N R < N) : R < L ^ scale L j N R := by
  rcases scale_spec (L := L) (j := j) (N := N) (R := R) with h' | h'
  · exact h'
  · omega

/-- If `s(w) ≥ j + 2`, then `2 r̄(w) ≥ L^{s(w)-1}`. -/
theorem pow_pred_le_of_scale (h : j + 2 ≤ scale L j N R) : L ^ (scale L j N R - 1) ≤ R := by
  by_contra hlt
  push Not at hlt
  have hm : scale L j N R - 1 < scale L j N R := by omega
  have := Nat.find_min (exists_scale L j N R) hm
  apply this
  refine ⟨by omega, Or.inl hlt⟩

theorem scale_eq_iff {s : ℕ} (hj : j + 1 ≤ s) (hs : s < N) :
    scale L j N R = s ↔ R < L ^ s ∧ (s = j + 1 ∨ L ^ (s - 1) ≤ R) := by
  constructor
  · rintro rfl
    refine ⟨lt_pow_scale hs, ?_⟩
    by_cases h : scale L j N R = j + 1
    · exact Or.inl h
    · exact Or.inr (pow_pred_le_of_scale (by have := le_scale (L := L) (j := j) (N := N) (R := R); omega))
  · rintro ⟨h1, h2⟩
    refine le_antisymm (Nat.find_min' _ ⟨hj, Or.inl h1⟩) ?_
    by_contra hlt
    push Not at hlt
    rcases h2 with h2 | h2
    · have := le_scale (L := L) (j := j) (N := N) (R := R); omega
    · have hs' := Nat.find_spec (exists_scale L j N R)
      change j + 1 ≤ scale L j N R ∧ (R < L ^ scale L j N R ∨ N ≤ scale L j N R) at hs'
      rcases hs'.2 with h3 | h3
      · have hmono : L ^ scale L j N R ≤ L ^ (s - 1) := by
          rcases Nat.eq_zero_or_pos L with hL | hL
          · subst hL
            have : 1 ≤ s - 1 ∨ s - 1 = 0 := by omega
            rcases this with h4 | h4
            · have h5 : 1 ≤ scale 0 j N R := by have := le_scale (L := 0) (j := j) (N := N) (R := R); omega
              rw [zero_pow (by omega), zero_pow (by omega)]
            · omega
          · exact Nat.pow_le_pow_right hL (by omega)
        omega
      · omega

end

end DressedFRD
