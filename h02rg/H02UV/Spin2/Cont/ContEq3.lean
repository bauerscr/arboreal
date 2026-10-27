import Loc.Polymer

/-!
# B3, `r`-dependent form: general nearby pairs through one intermediate point

The pair bounds `fin_T6_mid`/`fin_conn_diff_top` need `blk m_s (y − x) = blk m_s 0`, i.e. every
coordinate of the `[0, L^N)` representative of `y − x` is `< L^{m_s}`. For a general pair with
`|y − x|_∞ ≤ D < L^{m_s}` go through `z = (y₀, x₁)`; each of the two steps changes one
coordinate, and in each step one of the two orders has the block property (`zabs d ≤ D` means
`d.val ≤ D` or `(−d).val ≤ D`).

* `eq_blk_of_val_lt`: the block property from coordinate bounds;
* `eq_val_or_neg_val_le`: `zabs d ≤ D → d.val ≤ D ∨ (−d).val ≤ D`;
* **`eq_pair_chain`**: the intermediate point and the four facts;
* **`eq_abs_sub_le_two`**: a bound `B` for all pairs with the block property (in a set `S`
  containing the `D`-ball of `x`) gives `|F x − F y| ≤ 2B`.
-/

set_option autoImplicit false

namespace Spin2

open Finset Grassmann

variable {L N : ℕ} [NeZero L]

set_option linter.unusedSectionVars false

/-- Block property from the coordinate bounds `(v i).val < L^j`. -/
theorem eq_blk_of_val_lt {j : ℕ} (v : Loc.Lam 2 L N) (h : ∀ i, (v i).val < L ^ j) :
    Loc.blk j v = Loc.blk j (0 : Loc.Lam 2 L N) := by
  funext i
  show (v i).val / L ^ j = ((0 : Fin 2 → ZMod (L ^ N)) i).val / L ^ j
  rw [Nat.div_eq_of_lt (h i)]
  simp

theorem eq_val_or_neg_val_le {n : ℕ} [NeZero n] (d : ZMod n) {D : ℕ} (h : zabs d ≤ D) :
    d.val ≤ D ∨ (-d).val ≤ D := by
  unfold zabs at h
  rcases le_total d.val (n - d.val) with h1 | h1
  · left; rw [min_eq_left h1] at h; exact h
  · rw [min_eq_right h1] at h
    by_cases h0 : d = 0
    · left; subst h0; simp
    · right
      rw [ZMod.neg_val, if_neg h0]
      exact h

theorem eq_zabs_le_supNorm (v : Loc.Lam 2 L N) (i : Fin 2) :
    zabs ((v : Fin 2 → ZMod (L ^ N)) i) ≤ supNorm v :=
  Finset.le_sup (f := fun i => zabs ((v : Fin 2 → ZMod (L ^ N)) i)) (Finset.mem_univ i)

theorem eq_supNorm_le {v : Loc.Lam 2 L N} {D : ℕ}
    (h : ∀ i, zabs ((v : Fin 2 → ZMod (L ^ N)) i) ≤ D) : supNorm v ≤ D :=
  Finset.sup_le fun i _ => h i

/-- The good-pair predicate of the pair bounds at scale `j` and distance `D`. -/
def EqGood (j D : ℕ) (p q : Loc.Lam 2 L N) : Prop :=
  Loc.blk j (q - p) = Loc.blk j (0 : Loc.Lam 2 L N) ∧ supNorm (q - p) ≤ D

/-- One-coordinate step: if `q − p` vanishes off one coordinate and `|q − p|_∞ ≤ D < L^j`,
one of the two orders is good. -/
theorem eq_good_one {j D : ℕ} (hD : D < L ^ j) (p q : Loc.Lam 2 L N) (k : Fin 2)
    (h0 : ∀ i, i ≠ k → (q - p) i = 0) (hs : supNorm (q - p) ≤ D) :
    EqGood j D p q ∨ EqGood j D q p := by
  have hk := (eq_zabs_le_supNorm (q - p) k).trans hs
  have hs' : supNorm (p - q) ≤ D := by rw [← neg_sub, supNorm_neg]; exact hs
  rcases eq_val_or_neg_val_le _ hk with h | h
  · left
    refine ⟨eq_blk_of_val_lt _ fun i => ?_, hs⟩
    by_cases hi : i = k
    · subst hi; exact lt_of_le_of_lt h hD
    · rw [h0 i hi]; simp; exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  · right
    refine ⟨eq_blk_of_val_lt _ fun i => ?_, hs'⟩
    by_cases hi : i = k
    · subst hi
      have : (p - q) i = -((q - p) i) := by
        show (p i - q i) = -(q i - p i); ring
      rw [this]; exact lt_of_le_of_lt h hD
    · have : (p - q) i = -((q - p) i) := by
        show (p i - q i) = -(q i - p i); ring
      rw [this, h0 i hi]; simp; exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _

/-- **The intermediate point** `z = (y₀, x₁)`. -/
theorem eq_pair_chain {j D : ℕ} (hD : D < L ^ j) (x y : Loc.Lam 2 L N)
    (h : supNorm (y - x) ≤ D) :
    ∃ z : Loc.Lam 2 L N, (EqGood j D x z ∨ EqGood j D z x) ∧ (EqGood j D z y ∨ EqGood j D y z) ∧
      supNorm (z - x) ≤ D := by
  let z : Loc.Lam 2 L N := fun i => if i = 0 then y i else x i
  have hzx : ∀ i, (z - x) i = if i = 0 then (y - x) i else 0 := fun i => by
    show z i - x i = _
    by_cases hi : i = 0
    · simp only [z, if_pos hi]; rfl
    · simp only [z, if_neg hi, sub_self]
  have hyz : ∀ i, (y - z) i = if i = 0 then 0 else (y - x) i := fun i => by
    show y i - z i = _
    by_cases hi : i = 0
    · simp only [z, if_pos hi, sub_self]
    · simp only [z, if_neg hi]; rfl
  have hs1 : supNorm (z - x) ≤ D := eq_supNorm_le fun i => by
    show zabs ((z - x) i) ≤ D
    rw [hzx i]; split_ifs
    · exact (eq_zabs_le_supNorm (y - x) i).trans h
    · simp [zabs]
  have hs2 : supNorm (y - z) ≤ D := eq_supNorm_le fun i => by
    show zabs ((y - z) i) ≤ D
    rw [hyz i]; split_ifs
    · simp [zabs]
    · exact (eq_zabs_le_supNorm (y - x) i).trans h
  refine ⟨z, eq_good_one hD x z 0 (fun i hi => by rw [hzx i, if_neg hi]) hs1,
    eq_good_one hD z y 1 (fun i hi => by
      rw [hyz i, if_pos (by fin_cases i <;> simp_all)]) hs2, hs1⟩

/-- **`|F x − F y| ≤ 2B`** from a bound for good pairs in a set containing the `D`-ball of `x`. -/
theorem eq_abs_sub_le_two {j D : ℕ} (hD : D < L ^ j) (S : Loc.Lam 2 L N → Prop)
    (F : Loc.Lam 2 L N → ℝ) (B : ℝ)
    (hB : ∀ p q, S p → S q → EqGood j D p q → |F p - F q| ≤ B)
    (x y : Loc.Lam 2 L N) (hS : ∀ z, supNorm (z - x) ≤ D → S z) (h : supNorm (y - x) ≤ D) :
    |F x - F y| ≤ 2 * B := by
  obtain ⟨z, h1, h2, hz⟩ := eq_pair_chain hD x y h
  have hSx : S x := hS x (by rw [sub_self, supNorm_zero]; exact Nat.zero_le D)
  have hSy : S y := hS y h
  have hSz : S z := hS z hz
  have e1 : |F x - F z| ≤ B := by
    rcases h1 with h1 | h1
    · exact hB x z hSx hSz h1
    · rw [abs_sub_comm]; exact hB z x hSz hSx h1
  have e2 : |F z - F y| ≤ B := by
    rcases h2 with h2 | h2
    · exact hB z y hSz hSy h2
    · rw [abs_sub_comm]; exact hB y z hSy hSz h2
  calc |F x - F y| = |(F x - F z) + (F z - F y)| := by ring_nf
    _ ≤ |F x - F z| + |F z - F y| := abs_add_le _ _
    _ ≤ 2 * B := by linarith

end Spin2
