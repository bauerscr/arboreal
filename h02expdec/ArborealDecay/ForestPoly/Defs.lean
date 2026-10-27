module

public import Mathlib
public import ArborealDecay.MatrixForest.Laplacian
public import ArborealDecay.Stability.Basic

/-!
# The forest polynomial `P_G`, the determinant polynomial `D_G`, and the edge operators

* `forestPolynomial β hβ = P_G(h) = ∑_{F forest} (∏_{ij ∈ F} β_ij) ∏_{T ∈ F} (1 + ∑_{i ∈ T} h_i)`
  (note eq:PG-def, with the forest convention of the `H02` library).
* `detPoly β = D_G(h) = det (L_β + diag (1 + h))` (note eq:det-poly).
* `edgeOp β hβ s(i, j) = 1 - β_ij ∂_{h_i} ∂_{h_j}`, and `edgeOpProd β hβ` is the product of these
  commuting operators over all unordered pairs `{i, j}`, `i ≠ j`.
-/

@[expose] public section

namespace ArborealDecay.ForestPoly

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial

variable {V : Type*} [Fintype V]

open Classical in
/-- The vertex-field forest polynomial `P_G(h)` (note eq:PG-def). -/
noncomputable def forestPolynomial (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) :
    MvPolynomial V ℝ :=
  ∑ F : SimpleGraph V with F.IsAcyclic, MvPolynomial.C (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
    ∏ T : F.ConnectedComponent, (1 + ∑ i with F.connectedComponentMk i = T, MvPolynomial.X i)

variable [DecidableEq V]

/-- The determinant polynomial `D_G(h) = det (L_β + diag (1 + h))` (note eq:det-poly). -/
noncomputable def detPoly (β : V → V → ℝ) : MvPolynomial V ℝ :=
  ((MatrixForest.lap β).map MvPolynomial.C + Matrix.diagonal fun i => 1 + MvPolynomial.X i).det

/-- The operator `∂_{h_i} ∂_{h_j}`. -/
noncomputable def dd (i j : V) : Module.End ℝ (MvPolynomial V ℝ) :=
  (pderiv i).toLinearMap ∘ₗ (pderiv j).toLinearMap

@[simp] theorem dd_apply (i j : V) (p : MvPolynomial V ℝ) : dd i j p = pderiv i (pderiv j p) :=
  rfl

theorem dd_comm (i j : V) : dd i j = dd j i :=
  LinearMap.ext fun p => by simp only [dd_apply]; exact ArborealDecay.Stability.pderiv_comm i j p

theorem dd_commute (i j k l : V) : Commute (dd i j) (dd k l) := by
  refine LinearMap.ext fun p => ?_
  simp only [Module.End.mul_apply, dd_apply]
  rw [ArborealDecay.Stability.pderiv_comm j k, ArborealDecay.Stability.pderiv_comm i k,
    ArborealDecay.Stability.pderiv_comm j l, ArborealDecay.Stability.pderiv_comm i l]

/-- The edge operator `1 - β_ij ∂_{h_i} ∂_{h_j}` of the unordered pair `e = s(i, j)`. -/
noncomputable def edgeOp (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) :
    Sym2 V → Module.End ℝ (MvPolynomial V ℝ) :=
  Sym2.lift ⟨fun i j => 1 - β i j • dd i j, fun i j => by
    show 1 - β i j • dd i j = 1 - β j i • dd j i
    rw [hβ, dd_comm]⟩

@[simp] theorem edgeOp_mk (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (i j : V) :
    edgeOp β hβ s(i, j) = 1 - β i j • dd i j := rfl

theorem edgeOp_commute (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (e f : Sym2 V) :
    Commute (edgeOp β hβ e) (edgeOp β hβ f) := by
  induction e using Sym2.ind with
  | h i j =>
  induction f using Sym2.ind with
  | h k l =>
  rw [edgeOp_mk, edgeOp_mk]
  have hs : Commute (β i j • dd i j) (β k l • dd k l) :=
    ((dd_commute i j k l).smul_left _).smul_right _
  exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right hs)

theorem edgeOp_pairwise (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (s : Finset (Sym2 V)) :
    (s : Set (Sym2 V)).Pairwise (Function.onFun Commute (edgeOp β hβ)) :=
  fun e _ f _ _ => edgeOp_commute β hβ e f

/-- The product `∏_{{i,j}, i ≠ j} (1 - β_ij ∂_{h_i} ∂_{h_j})` of the (commuting) edge
operators over all unordered pairs of distinct vertices. -/
noncomputable def edgeOpProd (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) :
    Module.End ℝ (MvPolynomial V ℝ) :=
  (⊤ : SimpleGraph V).edgeFinset.noncommProd (edgeOp β hβ) (edgeOp_pairwise β hβ _)

end

end ArborealDecay.ForestPoly

end
