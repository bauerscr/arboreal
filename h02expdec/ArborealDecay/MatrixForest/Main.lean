module

public import ArborealDecay.MatrixForest.Forest
public import Mathlib.Basic.Real.Basic

/-!
# The weighted matrix-forest theorem

* `MatrixForest.det_lap_add_diagonal`: for symmetric weights `w : V → V → R` over a commutative
  ring `R` and any `x : V → R`,
  `det (lap w + diag x) = ∑_{F acyclic} ∏_{e ∈ F} w_e ∏_{T ∈ comp F} ∑_{i ∈ T} x_i`.
* `MatrixForest.det_lap_add_diagonal_real`: the case `R = ℝ`.
* `MatrixForest.det_lap_submatrix_ne`: the grounded matrix-tree theorem: the principal minor of
  `lap w` on `{i // i ≠ ρ}` is the sum over spanning trees `F` of `∏_{e ∈ F} w_e`.
-/

@[expose] public section

namespace MatrixForest

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

open Classical in
/-- **Weighted matrix-forest theorem.** For symmetric weights `w` (diagonal values irrelevant)
and arbitrary vertex weights `x`,
`det (lap w + diag x) = ∑_{F forest} ∏_{e ∈ F} w_e ∏_{T ∈ comp F} ∑_{i ∈ T} x_i`. -/
theorem det_lap_add_diagonal (w : V → V → R) (hw : ∀ i j, w i j = w j i) (x : V → R) :
    (lap w + diagonal x).det =
      ∑ F : SimpleGraph V with F.IsAcyclic,
        (∏ e ∈ F.edgeFinset, Sym2.lift ⟨w, hw⟩ e) *
          ∏ T : F.ConnectedComponent, (∑ i with F.connectedComponentMk i = T, x i) := by
  rw [det_lap_add_diagonal_eq_sum_isRooted, sum_isRooted_eq_sum_isAcyclic]

open Classical in
/-- The weighted matrix-forest theorem for real weights. -/
theorem det_lap_add_diagonal_real (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) (x : V → ℝ) :
    (lap w + diagonal x).det =
      ∑ F : SimpleGraph V with F.IsAcyclic,
        (∏ e ∈ F.edgeFinset, Sym2.lift ⟨w, hw⟩ e) *
          ∏ T : F.ConnectedComponent, (∑ i with F.connectedComponentMk i = T, x i) :=
  det_lap_add_diagonal w hw x

/-- The Laplacian is singular (for nonempty `V`). -/
theorem det_lap_eq_zero [Nonempty V] (w : V → V → R) (hw : ∀ i j, w i j = w j i) :
    (lap w).det = 0 := by
  classical
  have := det_lap_add_diagonal w hw (fun _ => 0)
  rw [diagonal_zero, add_zero] at this
  rw [this]
  refine Finset.sum_eq_zero fun F _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ (F.connectedComponentMk (Classical.arbitrary V)))
    (by simp), mul_zero]

/-- The principal minor on `{i // i ≠ ρ}` is the determinant after replacing row `ρ` by `e_ρ`. -/
theorem det_updateRow_single_eq_det_submatrix (M : Matrix V V R) (ρ : V) :
    (M.updateRow ρ (Pi.single ρ 1)).det =
      (M.submatrix (fun i : {i // i ≠ ρ} => (i : V)) (fun i : {i // i ≠ ρ} => (i : V))).det := by
  rw [twoBlockTriangular_det _ (fun i => i ≠ ρ)]
  · have h1 : toSquareBlockProp (M.updateRow ρ (Pi.single ρ 1)) (fun i => i ≠ ρ) =
        M.submatrix (fun i : {i // i ≠ ρ} => (i : V)) (fun i : {i // i ≠ ρ} => (i : V)) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp [toSquareBlockProp_def, updateRow_ne hi]
    have h2 : toSquareBlockProp (M.updateRow ρ (Pi.single ρ 1)) (fun i => ¬i ≠ ρ) = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [not_not] at hi hj
      subst hi hj
      simp [toSquareBlockProp_def]
    rw [h1, h2, det_one, mul_one]
  · intro i hi j hj
    simp only [not_not] at hi
    subst hi
    simp [hj]

open Classical in
/-- **Grounded weighted matrix-tree theorem.** The principal minor of `lap w` on the vertices
`≠ ρ` is the sum over the spanning trees `F` of `∏_{e ∈ F} w_e`. -/
theorem det_lap_submatrix_ne (w : V → V → R) (hw : ∀ i j, w i j = w j i) (ρ : V) :
    ((lap w).submatrix (fun i : {i // i ≠ ρ} => (i : V)) (fun i : {i // i ≠ ρ} => (i : V))).det =
      ∑ F : SimpleGraph V with F.IsTree, ∏ e ∈ F.edgeFinset, Sym2.lift ⟨w, hw⟩ e := by
  have : Nonempty V := ⟨ρ⟩
  have hrow : lap w + diagonal (Pi.single ρ 1) =
      (lap w).updateRow ρ (lap w ρ + Pi.single ρ 1) := by
    ext i j
    by_cases hi : i = ρ
    · subst hi; simp [diagonal_apply, Pi.single_apply, eq_comm]
    · simp [diagonal_apply, hi]
  have hdet := det_lap_add_diagonal w hw (Pi.single ρ 1)
  rw [hrow, det_updateRow_add, updateRow_eq_self, det_lap_eq_zero w hw, zero_add,
    det_updateRow_single_eq_det_submatrix] at hdet
  rw [hdet, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  have hprod : ∏ T : F.ConnectedComponent,
      (∑ i with F.connectedComponentMk i = T, (Pi.single ρ (1 : R) : V → R) i) =
        if F.Connected then 1 else 0 := by
    have : ∀ T : F.ConnectedComponent,
        (∑ i with F.connectedComponentMk i = T, (Pi.single ρ (1 : R) : V → R) i) =
          if F.connectedComponentMk ρ = T then 1 else 0 := fun T => by
      rw [Finset.sum_pi_single']
      simp
    simp_rw [this, Fintype.prod_boole]
    congr 1
    apply propext
    rw [connected_iff_exists_forall_reachable]
    constructor
    · intro h
      exact ⟨ρ, fun v => ConnectedComponent.exact (h _)⟩
    · rintro ⟨v, hv⟩ T
      obtain ⟨u, rfl⟩ := T.exists_rep
      exact ConnectedComponent.sound ((hv ρ).symm.trans (hv u))
  rw [hprod, isTree_iff]
  by_cases hc : F.Connected <;> by_cases ha : F.IsAcyclic <;> simp [hc, ha]

end MatrixForest
