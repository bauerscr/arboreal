import Grassmann.Torus

/-!
# The sup distance on the torus

`zabs z = |z|` on `ℤ/nℤ` and `supNorm x = |x|_∞` (defined in `Grassmann.Torus`) satisfy the
triangle inequality, and `|x|_∞ ≤ 1` for nearest neighbours.
-/

namespace FRD

open Finset Grassmann

variable {d n : ℕ} [NeZero n]

theorem zabs_le_natAbs (r : ℤ) : zabs (r : ZMod n) ≤ r.natAbs := by
  unfold zabs
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hv : (((r : ZMod n).val : ℕ) : ℤ) = r % n := ZMod.val_intCast r
  rcases le_or_gt 0 r with hr | hr
  · refine (min_le_left _ _).trans ?_
    have h1 := Int.emod_add_mul_ediv r n
    have h2 : 0 ≤ r / n := Int.ediv_nonneg hr hn.le
    have : r % n ≤ r := by nlinarith
    omega
  · refine (min_le_right _ _).trans ?_
    have h1 : r + n ≤ r % n := by
      have := Int.emod_add_mul_ediv r n
      have hq : r / n ≤ -1 := by
        rw [Int.ediv_le_iff_le_mul hn]; omega
      nlinarith
    have hlt := ZMod.val_lt (r : ZMod n)
    omega

theorem exists_natAbs_eq_zabs (z : ZMod n) : ∃ r : ℤ, (r : ZMod n) = z ∧ r.natAbs = zabs z := by
  unfold zabs
  have hlt := ZMod.val_lt z
  by_cases h : z.val ≤ n - z.val
  · refine ⟨((z.val : ℕ) : ℤ), by simp, ?_⟩
    rw [min_eq_left h, Int.natAbs_natCast]
  · refine ⟨((z.val : ℕ) : ℤ) - n, by simp, ?_⟩
    rw [min_eq_right (by omega)]; omega

theorem zabs_add_le (a b : ZMod n) : zabs (a + b) ≤ zabs a + zabs b := by
  obtain ⟨r, hr, hr'⟩ := exists_natAbs_eq_zabs a
  obtain ⟨s, hs, hs'⟩ := exists_natAbs_eq_zabs b
  have := zabs_le_natAbs (n := n) (r + s)
  push_cast at this
  rw [hr, hs] at this
  omega

theorem supNorm_add_le (x y : Torus d n) : supNorm (x + y) ≤ supNorm x + supNorm y := by
  unfold supNorm
  refine Finset.sup_le fun i _ => ?_
  refine (zabs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun i => zabs ((x : Fin d → ZMod n) i)) (mem_univ i)
  · exact Finset.le_sup (f := fun i => zabs ((y : Fin d → ZMod n) i)) (mem_univ i)

theorem supNorm_sub_comm (x y : Torus d n) : supNorm (x - y) = supNorm (y - x) := by
  rw [← neg_sub, supNorm_neg]

theorem zabs_one_le : zabs (1 : ZMod n) ≤ 1 := by
  simpa using zabs_le_natAbs (n := n) 1

theorem supNorm_le_iff (x : Torus d n) (k : ℕ) :
    supNorm x ≤ k ↔ ∀ i, zabs ((x : Fin d → ZMod n) i) ≤ k := by
  unfold supNorm; simp [Finset.sup_le_iff]

theorem supNorm_dirVec_le (e : Dir d) : supNorm (dirVec e : Torus d n) ≤ 1 := by
  have h1 : ∀ i : Fin d, supNorm (((Pi.single i 1 : Fin d → ZMod n)) : Torus d n) ≤ 1 := by
    intro i
    rw [supNorm_le_iff]
    intro j
    by_cases h : j = i
    · subst h; simpa using zabs_one_le (n := n)
    · simp [Pi.single_apply, h, zabs]
  rcases e with i | i
  · exact h1 i
  · have : (dirVec (Sum.inr i) : Torus d n) = -dirVec (Sum.inl i) := rfl
    rw [this, supNorm_neg]; exact h1 i

end FRD
