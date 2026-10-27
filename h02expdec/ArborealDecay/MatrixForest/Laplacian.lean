module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.SetTheory.Ordinal.Rank

/-!
# The weighted Laplacian and its expansion over rooted forests

* `MatrixForest.lap w`: the weighted Laplacian of `w : V → V → R`, with
  `lap w i i = ∑_{k ≠ i} w i k` and `lap w i j = - w i j` for `i ≠ j`.
* `MatrixForest.IsRooted f`: a parent function `f : V → Option V` (`f i = none` means that `i`
  is a root, `f i = some j` that `j` is the parent of `i`) is well founded, i.e. following the
  parents always ends at a root.
* `MatrixForest.det_lap_add_diagonal_eq_sum_isRooted`: the directed matrix-forest theorem
  `det (lap w + diag x) = ∑_{f rooted} ∏_i c_i(f i)`, `c_i(none) = x i`, `c_i(some j) = w i j`.
  (No symmetry of `w` is needed here.)

The proof expands the determinant multilinearly in the rows
`row_i = x_i e_i + ∑_k w_ik (e_i - e_k)` and evaluates the determinant of the resulting
`{0, ±1}`-matrices `1 - P_f`: it is `1` for well-founded `f` (block triangular with respect to the
rank) and `0` otherwise (the indicator of the non-accessible vertices is in the kernel).
-/

@[expose] public section

namespace MatrixForest

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

/-- The weighted Laplacian of `w`: `lap w i i = ∑_{k ≠ i} w i k`, `lap w i j = - w i j` (`i ≠ j`).
The diagonal values `w i i` do not enter. -/
def lap (w : V → V → R) : Matrix V V R :=
  fun i j => if i = j then ∑ k ∈ univ.erase i, w i k else -w i j

theorem lap_apply_self (w : V → V → R) (i : V) : lap w i i = ∑ k ∈ univ.erase i, w i k := by
  simp [lap]

theorem lap_apply_of_ne (w : V → V → R) {i j : V} (h : i ≠ j) : lap w i j = -w i j := by
  simp [lap, h]

/-- A parent function `f : V → Option V` is *rooted* if the parent relation is well founded:
iterating `f` from any vertex reaches a root (`f i = none`) after finitely many steps. -/
def IsRooted (f : V → Option V) : Prop := WellFounded (fun b a : V => f a = some b)

/-- The integer matrix `1 - P_f` of a parent function `f`. -/
def parentMat (f : V → Option V) : Matrix V V ℤ :=
  fun i j => (if i = j then 1 else 0) - (if f i = some j then 1 else 0)

theorem det_parentMat_of_isRooted {f : V → Option V} (hf : IsRooted f) :
    (parentMat f).det = 1 := by
  let rk : V → Ordinal := fun i => (hf.apply i).rank
  have hrk : ∀ {i j : V}, f i = some j → rk j < rk i := fun {i j} h =>
    Acc.rank_lt_of_rel (hf.apply i) h
  let b : V → Ordinalᵒᵈ := fun i => OrderDual.toDual (rk i)
  have hb : (parentMat f).BlockTriangular b := by
    intro i j hij
    change rk i < rk j at hij
    have h1 : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    have h2 : f i ≠ some j := fun h => lt_asymm hij (hrk h)
    simp [parentMat, h1, h2]
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (parentMat f).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [toSquareBlock_def, parentMat, one_apply, Subtype.mk.injEq]
    have h2 : f i ≠ some j := fun h => by
      have := hrk h
      have hij : rk i = rk j := by
        have := hi.trans hj.symm
        exact OrderDual.toDual.injective this
      exact lt_irrefl _ (hij ▸ this)
    simp [h2]
  rw [this, det_one]

theorem det_parentMat_of_not_isRooted {f : V → Option V} (hf : ¬IsRooted f) :
    (parentMat f).det = 0 := by
  classical
  let r : V → V → Prop := fun b a => f a = some b
  obtain ⟨a, ha⟩ : ∃ a, ¬Acc r a := by
    by_contra h
    push Not at h
    exact hf ⟨h⟩
  have hnone : ∀ i, f i = none → Acc r i := fun i h =>
    Acc.intro _ fun y hy => by simp [r, h] at hy
  have hsome : ∀ i k, f i = some k → (Acc r i ↔ Acc r k) := fun i k h =>
    ⟨fun hi => hi.inv h, fun hk => Acc.intro _ fun y hy => by
      have : y = k := by simpa [r, h] using hy.symm
      exact this ▸ hk⟩
  let u : V → ℤ := fun i => if Acc r i then 0 else 1
  refine exists_mulVec_eq_zero_iff.mp ⟨u, fun h => ?_, ?_⟩
  · have := congrFun h a
    simp [u, ha] at this
  · ext i
    simp only [mulVec, dotProduct, parentMat, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply]
    rcases h : f i with _ | k
    · simp [u, hnone i h]
    · simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      simp [u, hsome i k h]

/-- The coefficient attached to vertex `i` choosing `o : Option V`: `x i` for a root
(`o = none`), `w i j` for the parent `o = some j`. -/
def coef (w : V → V → R) (x : V → R) (i : V) : Option V → R
  | none => x i
  | some j => w i j

/-- The row vector attached to vertex `i` choosing `o`: `e_i` for `o = none`, `e_i - e_j` for
`o = some j`. -/
def rowVec (i : V) : Option V → V → R
  | none => Pi.single i 1
  | some j => Pi.single i 1 - Pi.single j 1

theorem lap_add_diagonal_eq_sum (w : V → V → R) (x : V → R) :
    (lap w + diagonal x) = Matrix.of fun i => ∑ o : Option V, coef w x i o • rowVec i o := by
  ext i j
  rw [Matrix.add_apply, of_apply]
  simp only [Fintype.sum_option, coef, rowVec, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · subst hij
    rw [lap_apply_self, diagonal_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true, add_sub_cancel_left]
    ring
  · rw [lap_apply_of_ne w hij, diagonal_apply_ne _ hij]
    simp [Ne.symm hij]

omit [Fintype V] in
theorem rowVec_eq_map (f : V → Option V) :
    (fun i => rowVec (R := R) i (f i)) = (parentMat f).map (Int.castRingHom R) := by
  ext i j
  rcases h : f i with _ | k
  · simp [rowVec, parentMat, h, Pi.single_apply, eq_comm]
  · simp [rowVec, parentMat, h, Pi.single_apply, eq_comm]

open Classical in
/-- **Directed matrix-forest theorem** (rooted form): `det (lap w + diag x)` is the sum over the
rooted parent functions `f` of `∏_i c_i(f i)`, where `c_i(none) = x i`, `c_i(some j) = w i j`. -/
theorem det_lap_add_diagonal_eq_sum_isRooted (w : V → V → R) (x : V → R) :
    (lap w + diagonal x).det =
      ∑ f : V → Option V, if IsRooted f then ∏ i, coef w x i (f i) else 0 := by
  have hdet : ∀ M : Matrix V V R, M.det = detRowAlternating M := fun M => rfl
  rw [lap_add_diagonal_eq_sum, hdet]
  change detRowAlternating (fun i => ∑ o : Option V, coef w x i o • rowVec i o) = _
  have hsum := (detRowAlternating (n := V) (R := R)).toMultilinearMap.map_sum
    (fun i (o : Option V) => coef w x i o • rowVec i o)
  rw [AlternatingMap.coe_multilinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [AlternatingMap.map_smul_univ, rowVec_eq_map, ← hdet,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, smul_eq_mul]
  split_ifs with hf
  · rw [det_parentMat_of_isRooted hf]; simp
  · rw [det_parentMat_of_not_isRooted hf]; simp

end MatrixForest
