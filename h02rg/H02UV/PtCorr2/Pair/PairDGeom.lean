import PtCorr2.Pair.PairSectHist

/-!
# Existence of a covering polymer `D` (`DCov`)

For points `a`, `b` of the torus, the `j`-polymer `D` made of all `j`-blocks meeting the sup-ball
of radius `R = 2^{d+1} L^j + |b - a|_∞` around `a` is connected (the ball is connected under
nearest-neighbour steps, which move a point strictly closer to `a`), contains every `j`-block whose
small-set neighbourhood contains `a` or `b`, and lies within `R + L^j` of `a`.

* `isConn_ballPoly`, `ballPoly_cover`, `ballPoly_local` (general dimension);
* **`exists_dCov`**: `∃ D, DCov P j D ∧ ∀ y ∈ D, |y - a|_∞ ≤ 10 L^{j+1}` when
  `2 |a - b|_∞ < L^{j+1}`; `exists_dCov'`: the bound `4 L^{j+1}` when `3 ≤ L`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc Step FRD Obs2

/-! ### Nearest-neighbour steps towards the origin -/

theorem exists_step_toward {d n : ℕ} [NeZero n] (w : Torus d n) :
    ∃ w' : Torus d n, supNorm (w - w') ≤ 1 ∧ supNorm w' ≤ supNorm w - 1 := by
  choose r hr hr' using fun i => exists_natAbs_eq_zabs (n := n) ((w : Fin d → ZMod n) i)
  let s : Fin d → ℤ := fun i => if 0 < r i then 1 else if r i < 0 then -1 else 0
  let W : Torus d n := fun i => ((r i - s i : ℤ) : ZMod n)
  refine ⟨W, ?_, ?_⟩
  · rw [supNorm_le_iff]
    intro i
    have e : ((w - W : Torus d n) : Fin d → ZMod n) i = ((s i : ℤ) : ZMod n) := by
      show (w : Fin d → ZMod n) i - ((r i - s i : ℤ) : ZMod n) = _
      rw [← hr i]; push_cast; ring
    rw [e]
    refine (zabs_le_natAbs _).trans ?_
    simp only [s]; split_ifs <;> simp
  · rw [supNorm_le_iff]
    intro i
    show zabs ((r i - s i : ℤ) : ZMod n) ≤ _
    refine (zabs_le_natAbs _).trans ?_
    have hle : zabs ((w : Fin d → ZMod n) i) ≤ supNorm w := by
      unfold supNorm
      exact Finset.le_sup (f := fun i => zabs ((w : Fin d → ZMod n) i)) (mem_univ i)
    rw [← hr' i] at hle
    simp only [s]; split_ifs <;> omega

theorem eq_of_supNorm_sub_le_zero {d n : ℕ} [NeZero n] {x y : Torus d n}
    (h : supNorm (x - y) ≤ 0) : x = y := by
  rw [← sub_eq_zero]
  funext i
  have hi := (supNorm_le_iff _ 0).1 h i
  have hlt := ZMod.val_lt (((x - y : Torus d n) : Fin d → ZMod n) i)
  unfold zabs at hi
  exact (ZMod.val_eq_zero _).1 (by omega)

/-! ### The ball polymer -/

variable {d L N : ℕ} [NeZero L]

open Classical in
/-- All `j`-blocks meeting the sup-ball of radius `R` around `a`. -/
def ballPoly (j : ℕ) (a : Lam d L N) (R : ℕ) : Finset (Lam d L N) :=
  univ.filter fun y => ∃ z, blk j z = blk j y ∧ supNorm (z - a) ≤ R

theorem mem_ballPoly {j : ℕ} {a : Lam d L N} {R : ℕ} {y : Lam d L N} :
    y ∈ ballPoly j a R ↔ ∃ z, blk j z = blk j y ∧ supNorm (z - a) ≤ R := by
  simp [ballPoly]

theorem mem_ballPoly_of_le {j : ℕ} {a : Lam d L N} {R : ℕ} {y : Lam d L N}
    (h : supNorm (y - a) ≤ R) : y ∈ ballPoly j a R :=
  mem_ballPoly.2 ⟨y, rfl, h⟩

theorem reach_ballPoly (j : ℕ) (a : Lam d L N) (R : ℕ) :
    ∀ m (y : Lam d L N), supNorm (y - a) ≤ m → m ≤ R →
      Relation.ReflTransGen (BlockAdj j (ballPoly j a R)) (blk j y) (blk j a) := by
  intro m
  induction m with
  | zero =>
    intro y hy _
    rw [eq_of_supNorm_sub_le_zero hy]
  | succ m ih =>
    intro y hy hm
    obtain ⟨w', h1, h2⟩ := exists_step_toward (y - a)
    have e1 : a + w' - a = w' := by abel
    have e2 : y - (a + w') = (y - a) - w' := by abel
    have hy' : supNorm (a + w' - a) ≤ m := by rw [e1]; omega
    refine Relation.ReflTransGen.head ⟨blk_mem_blocks (mem_ballPoly_of_le (by omega)),
      blk_mem_blocks (mem_ballPoly_of_le (by omega)), ?_⟩ (ih _ hy' (by omega))
    exact ⟨y, mem_blockSet_blk j y, a + w', mem_blockSet_blk j _, by rwa [e2]⟩

theorem isConn_ballPoly (j : ℕ) (a : Lam d L N) (R : ℕ) : IsConn j (ballPoly j a R) := by
  have hsymm : Symmetric (BlockAdj (L := L) (N := N) j (ballPoly j a R)) := by
    rintro b b' ⟨hb, hb', x, hx, y, hy, hxy⟩
    exact ⟨hb', hb, y, hy, x, hx, by rwa [supNorm_sub_comm]⟩
  have key : ∀ b ∈ blocks j (ballPoly j a R),
      Relation.ReflTransGen (BlockAdj j (ballPoly j a R)) b (blk j a) := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hb
    obtain ⟨z, hz, hzR⟩ := mem_ballPoly.1 hy
    rw [← hz]
    exact reach_ballPoly j a R _ z le_rfl hzR
  refine ⟨?_, ⟨a, mem_ballPoly_of_le (by simp [supNorm_zero])⟩, ?_⟩
  · intro x y hxy hx
    obtain ⟨z, hz, hzR⟩ := mem_ballPoly.1 hx
    exact mem_ballPoly.2 ⟨z, hz.trans hxy, hzR⟩
  · intro b hb b' hb'
    exact (key b hb).trans (Relation.ReflTransGen.symmetric hsymm (key b' hb'))

/-- every block whose small-set neighbourhood contains `a` or `b` is a block of the ball polymer
of radius `2^{d+1} L^j + |b - a|_∞` around `a` -/
theorem ballPoly_cover (j : ℕ) (a b : Lam d L N) (c : Fin d → ℕ)
    (h : a ∈ nbhd j (blockSet (L := L) (N := N) j c) ∨
      b ∈ nbhd j (blockSet (L := L) (N := N) j c)) :
    c ∈ blocks j (ballPoly j a (2 ^ (d + 1) * L ^ j + supNorm (b - a))) := by
  have hne : ∃ x : Lam d L N, blk j x = c := by
    rcases h with h | h <;>
    · simp only [nbhd, mem_filter, mem_univ, true_and] at h
      obtain ⟨S, -, -, b', hb', -⟩ := h
      obtain ⟨x, hx, -⟩ := mem_image.1 hb'
      exact ⟨x, mem_blockSet.1 hx⟩
  obtain ⟨x, rfl⟩ := hne
  have hS := isSmall_blockSet (L := L) (N := N) j x
  refine blk_mem_blocks (mem_ballPoly_of_le ?_)
  rcases h with h | h
  · have := supNorm_le_of_mem_nbhd hS (mem_blockSet_blk j x) h
    rw [supNorm_sub_comm] at this
    omega
  · have h1 := supNorm_le_of_mem_nbhd hS (mem_blockSet_blk j x) h
    rw [supNorm_sub_comm] at h1
    have e : x - a = (x - b) + (b - a) := by abel
    have := supNorm_add_le (x - b) (b - a)
    rw [e]; omega

theorem ballPoly_local {j : ℕ} {a : Lam d L N} {R : ℕ} {y : Lam d L N}
    (hy : y ∈ ballPoly j a R) : supNorm (y - a) ≤ R + L ^ j := by
  obtain ⟨z, hz, hzR⟩ := mem_ballPoly.1 hy
  have h1 := supNorm_lt_of_blk_eq hz.symm
  have e : y - a = (y - z) + (z - a) := by abel
  have := supNorm_add_le (y - z) (z - a)
  rw [e]; omega

/-! ### The covering polymer -/

end

end PtCorr2
