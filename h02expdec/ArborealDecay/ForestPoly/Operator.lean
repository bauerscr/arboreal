module

public import ArborealDecay.ForestPoly.Defs
public import ArborealDecay.ForestPoly.Gaussian
public import ArborealDecay.Stability.Decomp

/-!
# The differential-operator identity `lem:operator-identity`

`P_G(h) = ∏_{ij} (1 - β_ij ∂_{h_i} ∂_{h_j}) D_G(h)`, proved by the Grassmann calculation of the
note (author ruling R7):

* `expect_eq_Ih`: the `H02` partition function `[1]_{β,h}` equals
  `[exp(ξᵀ (L_β + diag h) η) ∏_{ij} (1 - β_ij q_i q_j)]_0` with `q_i = ξ_i η_i`
  (note eq:grassmann-operator; the factor `exp(∑ q_i)` is part of `H02.int0`).
* `Ih_one`: the fermionic Gaussian integral gives `[exp(ξᵀ (L_β + diag h) η)]_0 = D_G(h)`.
* `Ih_shift`: shifting `h_k ↦ h_k + 1` inserts `1 + q_k`, so inserting `q_k` is the derivative
  `∂_{h_k}` of the (multi-affine) polynomial (`Rel.pc_mul`).
* `H02.thm_H02forest` identifies `[1]_{β,h}` with `P_G(h)`.
-/

@[expose] public section

namespace ArborealDecay.ForestPoly

noncomputable section

set_option linter.unusedSectionVars false

open H02 MvPolynomial Finset ArborealDecay.Stability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Multi-affinity of `D_G` -/

theorem degreeOf_detMat_le (β : V → V → ℝ) (k a b : V) :
    degreeOf k (((MatrixForest.lap β).map MvPolynomial.C + Matrix.diagonal fun i => 1 + X i :
      Matrix V V (MvPolynomial V ℝ)) a b) ≤
      if b = k then 1 else 0 := by
  have h1 : degreeOf k (1 + X b : MvPolynomial V ℝ) ≤ if b = k then 1 else 0 := by
    refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · rw [← MvPolynomial.C_1, degreeOf_C]; exact Nat.zero_le _
    · rw [degreeOf_X]
      by_cases hb : b = k
      · simp [hb]
      · simp [hb, Ne.symm hb]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.diagonal_apply]
  refine (degreeOf_add_le _ _ _).trans (max_le (by rw [degreeOf_C]; exact Nat.zero_le _) ?_)
  by_cases hab : a = b
  · subst hab; simpa using h1
  · simp [hab]

/-- `D_G` is multi-affine (supplement lem:DG, step MA). -/
theorem detPoly_isMultiAffine (β : V → V → ℝ) : IsMultiAffine (detPoly β) := by
  intro k
  rw [detPoly, Matrix.det_apply']
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [← map_intCast (MvPolynomial.C : ℝ →+* MvPolynomial V ℝ), degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc _ ≤ ∑ i, if i = k then 1 else 0 :=
        Finset.sum_le_sum fun i _ => degreeOf_detMat_le β k (σ i) i
    _ = 1 := by simp

/-! ### Evaluation of a polynomial of degree `≤ 1` along a coordinate shift -/

theorem eval_add_single_of_degreeOf_le_one {p : MvPolynomial V ℝ} {k : V}
    (hp : degreeOf k p ≤ 1) (h : V → ℝ) :
    eval (h + Pi.single k 1) p = eval h p + eval h (pderiv k p) := by
  have hq0 := degreeOf_sub_X_mul_pderiv_self hp
  have hq1 := degreeOf_pderiv_self_of_le_one hp
  have hsplit : p = (p - X k * pderiv k p) + X k * pderiv k p := by ring
  have key : ∀ g : V → ℝ, eval g p =
      eval g (p - X k * pderiv k p) + g k * eval g (pderiv k p) := fun g => by
    conv_lhs => rw [hsplit]
    rw [map_add, map_mul, eval_X]
  have hupd : h + Pi.single k 1 = Function.update h k (h k + 1) := by
    funext x
    by_cases hx : x = k
    · subst hx; simp
    · simp [hx]
  rw [key, key h, hupd, eval_update_of_degreeOf_eq_zero hq0, eval_update_of_degreeOf_eq_zero hq1,
    Function.update_self]
  ring

/-! ### The Grassmann side -/

/-- The quadratic form `ξᵀ (L_β + diag h) η` in the center of the Grassmann algebra. -/
def Rq (β : V → V → ℝ) (h : V → ℝ) : C V :=
  ∑ i, ∑ j, (MatrixForest.lap β + Matrix.diagonal h) i j • pc i j

theorem isNilpotent_Rq (β : V → V → ℝ) (h : V → ℝ) : IsNilpotent (Rq β h) :=
  isNilpotent_quad _

/-- The functional `Y ↦ [exp(ξᵀ (L_β + diag h) η) Y]_0`. -/
def Ih (β : V → V → ℝ) (h : V → ℝ) (Y : C V) : ℝ :=
  int0 (cv (IsNilpotent.exp (Rq β h) * Y))

theorem Ih_add (β : V → V → ℝ) (h : V → ℝ) (Y Y' : C V) :
    Ih β h (Y + Y') = Ih β h Y + Ih β h Y' := by
  simp only [Ih, mul_add, map_add, int0]

theorem Ih_sub_smul (β : V → V → ℝ) (h : V → ℝ) (Y Y' : C V) (c : ℝ) :
    Ih β h (Y - c • Y') = Ih β h Y - c * Ih β h Y' := by
  simp only [Ih, mul_sub, mul_smul_comm, map_sub, map_smul, int0, smul_eq_mul]

/-- The fermionic Gaussian integral: `[exp(ξᵀ (L_β + diag h) η)]_0 = D_G(h)`. -/
theorem Ih_one (β : V → V → ℝ) (h : V → ℝ) : Ih β h 1 = eval h (detPoly β) := by
  rw [Ih, mul_one, Rq, int0_exp_quadratic, detPoly, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.add_apply]
    ring
  · simp [Matrix.add_apply, hij]

theorem Rq_shift (β : V → V → ℝ) (h : V → ℝ) (k : V) :
    Rq β (h + Pi.single k 1) = Rq β h + pc k k := by
  have hM : ∀ i j, (MatrixForest.lap β + Matrix.diagonal (h + Pi.single k 1) : Matrix V V ℝ) i j =
      (MatrixForest.lap β + Matrix.diagonal h : Matrix V V ℝ) i j +
        (Matrix.diagonal (Pi.single k 1) : Matrix V V ℝ) i j := by
    intro i j
    simp only [Matrix.add_apply, Matrix.diagonal_apply]
    split_ifs <;> simp; ring
  simp only [Rq, hM, add_smul, Finset.sum_add_distrib]
  congr 1
  simp [Matrix.diagonal_apply, ite_smul, Pi.single_apply]

/-- Shifting `h_k` by `1` inserts the factor `1 + q_k`. -/
theorem Ih_shift (β : V → V → ℝ) (h : V → ℝ) (k : V) (Y : C V) :
    Ih β (h + Pi.single k 1) Y = Ih β h Y + Ih β h (pc k k * Y) := by
  have e : IsNilpotent.exp (Rq β h) * (1 + pc k k) * Y =
      IsNilpotent.exp (Rq β h) * (Y + pc k k * Y) := by ring
  rw [← Ih_add]
  simp only [Ih]
  rw [Rq_shift, IsNilpotent.exp_add_of_commute (Commute.all _ _) (isNilpotent_Rq β h)
    (isNilpotent_of_mul_self (pc_sq k)), exp_eq_one_add (pc_sq k), e]

/-! ### Transfer between Grassmann insertions and derivatives -/

/-- `Y` and `p` correspond: `[exp(ξᵀ (L_β + diag h) η) Y]_0 = p(h)` for all `h`, and `p` is
multi-affine. -/
def Rel (β : V → V → ℝ) (Y : C V) (p : MvPolynomial V ℝ) : Prop :=
  (∀ h, Ih β h Y = eval h p) ∧ IsMultiAffine p

theorem rel_one (β : V → V → ℝ) : Rel β 1 (detPoly β) :=
  ⟨fun h => Ih_one β h, detPoly_isMultiAffine β⟩

/-- Inserting `q_k` corresponds to `∂_{h_k}`. -/
theorem Rel.pc_mul {β : V → V → ℝ} {Y : C V} {p : MvPolynomial V ℝ} (hR : Rel β Y p) (k : V) :
    Rel β (pc k k * Y) (pderiv k p) := by
  refine ⟨fun h => ?_, fun i => (degreeOf_pderiv_le _ _ _).trans (hR.2 i)⟩
  have := Ih_shift β h k Y
  rw [hR.1, hR.1, eval_add_single_of_degreeOf_le_one (hR.2 k)] at this
  linarith

theorem Rel.sub_smul {β : V → V → ℝ} {Y Y' : C V} {p p' : MvPolynomial V ℝ} (hR : Rel β Y p)
    (hR' : Rel β Y' p') (c : ℝ) : Rel β (Y - c • Y') (p - c • p') := by
  refine ⟨fun h => ?_, fun i => ?_⟩
  · rw [Ih_sub_smul, hR.1, hR'.1, map_sub, smul_eq_C_mul, map_mul, eval_C]
  · refine (degreeOf_sub_le _ _ _).trans (max_le (hR.2 i) ?_)
    rw [smul_eq_C_mul]
    exact (degreeOf_C_mul_le _ _ _).trans (hR'.2 i)

/-- `q_i q_j` as a function of the unordered pair `{i, j}`. -/
def Zs : Sym2 V → C V := Sym2.lift ⟨fun i j => pc i i * pc j j, fun _ _ => mul_comm _ _⟩

/-- The factor `1 - β_ij q_i q_j`. -/
def yfac (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (e : Sym2 V) : C V :=
  1 - Sym2.lift ⟨β, hβ⟩ e • Zs e

theorem Rel.edge {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {Y : C V} {p : MvPolynomial V ℝ}
    (hR : Rel β Y p) (e : Sym2 V) : Rel β (yfac β hβ e * Y) (edgeOp β hβ e p) := by
  induction e using Sym2.ind with
  | h i j =>
  have := hR.sub_smul ((hR.pc_mul j).pc_mul i) (β i j)
  convert this using 1
  · simp only [yfac, Zs, Sym2.lift_mk, sub_mul, one_mul, smul_mul_assoc, mul_assoc]
  · simp [edgeOp_mk]

theorem rel_prod (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (s : Finset (Sym2 V)) :
    Rel β (∏ e ∈ s, yfac β hβ e)
      (s.noncommProd (edgeOp β hβ) (edgeOp_pairwise β hβ s) (detPoly β)) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.noncommProd_empty]; exact rel_one β
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.prod_insert ha]
    exact ih.edge hβ a

/-! ### The Grassmann expression of `[1]_{β,h}` (note eq:grassmann-operator) -/

theorem sum_smul_sub_eq_sum_lap (β : V → V → ℝ) (i : V) :
    ∑ j, β i j • (pc i i - pc i j : C V) = ∑ j, MatrixForest.lap β i j • pc i j := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i),
    ← Finset.add_sum_erase _ (fun j => MatrixForest.lap β i j • pc i j) (mem_univ i),
    MatrixForest.lap_apply_self, sub_self, smul_zero, zero_add,
    Finset.sum_congr rfl (fun j hj => by
      rw [MatrixForest.lap_apply_of_ne β (Finset.ne_of_mem_erase hj).symm] :
      ∀ j ∈ univ.erase i, MatrixForest.lap β i j • pc i j = -β i j • pc i j)]
  rw [Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_sub, neg_smul, sub_eq_add_neg]

/-- `q_i + q_j - ξ_i η_j - ξ_j η_i` as a function of the unordered pair `{i, j}`. -/
def Ys : Sym2 V → C V :=
  Sym2.lift ⟨fun i j => pc i i + pc j j - pc i j - pc j i, fun i j => by
    show pc i i + pc j j - pc i j - pc j i = pc j j + pc i i - pc j i - pc i j; abel⟩

theorem Xs_eq (e : Sym2 V) : Xs e = Ys e - Zs e := by
  induction e using Sym2.ind with
  | h i j =>
  change Xc i j = (pc i i + pc j j - pc i j - pc j i) - pc i i * pc j j
  rw [Xc_eq]; ring

theorem sum_edge_Ys (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) :
    ∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, Sym2.lift ⟨β, hβ⟩ e • Ys e =
      ∑ i, ∑ j, MatrixForest.lap β i j • pc i j := by
  let g : V → V → C V := fun i j => β i j • (pc i i + pc j j - pc i j - pc j i)
  have hg : ∀ i j, g i j = g j i := fun i j => by
    simp only [g]; rw [hβ i j]; congr 1; abel
  have hd : ∀ i, g i i = 0 := fun i => by simp [g]
  have hsum := sum_sum_eq_two_nsmul g hg hd
  have hlift : ∀ e, Sym2.lift ⟨g, hg⟩ e = Sym2.lift ⟨β, hβ⟩ e • Ys e := fun e => by
    induction e using Sym2.ind with | h a b => rfl
  simp only [hlift] at hsum
  have hsplit : ∑ i, ∑ j, g i j = ∑ i, ∑ j, β i j • (pc i i - pc i j : C V) +
      ∑ i, ∑ j, β i j • (pc j j - pc j i : C V) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, ← smul_add]
    congr 1; abel
  have hswap : ∑ i, ∑ j, β i j • (pc j j - pc j i : C V) =
      ∑ i, ∑ j, β i j • (pc i i - pc i j : C V) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hβ]
  rw [hsplit, hswap, Finset.sum_congr rfl fun i _ => sum_smul_sub_eq_sum_lap β i, ← two_nsmul,
    two_nsmul, two_nsmul, ← two_smul ℝ, ← two_smul ℝ] at hsum
  exact (smul_right_injective _ two_ne_zero hsum).symm

theorem Rq_eq (β : V → V → ℝ) (h : V → ℝ) :
    Rq β h = ∑ i, ∑ j, MatrixForest.lap β i j • pc i j + ∑ i, h i • pc i i := by
  simp only [Rq, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.diagonal_apply,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem W_eq (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (h : V → ℝ) :
    W β hβ h = Rq β h + ∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, -(Sym2.lift ⟨β, hβ⟩ e • Zs e) := by
  rw [W, Rq_eq, E_eq, ← sum_edge_Ys β hβ]
  simp only [Xs_eq, smul_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

theorem Zs_sq (e : Sym2 V) : Zs e * Zs e = 0 := by
  induction e using Sym2.ind with
  | h i j =>
  change pc i i * pc j j * (pc i i * pc j j) = 0
  calc _ = (pc i i * pc i i) * (pc j j * pc j j) := by ring
    _ = 0 := by rw [pc_sq, zero_mul]

/-- **The Grassmann expression of the partition function** (note eq:grassmann-operator):
`[1]_{β,h} = [exp(ξᵀ (L_β + diag h) η) ∏_{ij} (1 - β_ij q_i q_j)]_0`. -/
theorem expect_eq_Ih (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (h : V → ℝ) :
    H02.expect β h 1 = Ih β h (∏ e ∈ (⊤ : SimpleGraph V).edgeFinset, yfac β hβ e) := by
  have hW := isNilpotent_W β hβ h
  have hn : ∀ e ∈ (⊤ : SimpleGraph V).edgeFinset,
      IsNilpotent (-(Sym2.lift ⟨β, hβ⟩ e • Zs e)) := fun e _ =>
    isNilpotent_of_mul_self (by rw [neg_mul_neg]; exact smul_mul_smul_self (Zs_sq e))
  rw [H02.expect, action_eq β hβ h, neg_neg, one_mul, ← IsNilpotent.map_exp hW, W_eq,
    IsNilpotent.exp_add_of_commute (Commute.all _ _) (isNilpotent_Rq β h) (isNilpotent_sum hn),
    exp_sum _ _ hn, Ih]
  congr 3
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [exp_eq_one_add (by rw [neg_mul_neg]; exact smul_mul_smul_self (Zs_sq e)), yfac,
    sub_eq_add_neg]

/-! ### The operator identity -/

theorem eval_forestPolynomial (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (h : V → ℝ) :
    eval h (forestPolynomial β hβ) = H02.expect β h 1 := by
  rw [thm_H02forest β hβ h, forestPolynomial]
  simp only [map_sum, map_mul, map_prod, eval_C, map_add, map_one, eval_X]
  convert rfl

/-- **Lemma `lem:operator-identity`** (note eq:operator-identity):
`P_G(h) = ∏_{{i,j}} (1 - β_ij ∂_{h_i} ∂_{h_j}) D_G(h)`, the product running over all unordered
pairs of distinct vertices. Proved by the Grassmann calculation (ruling R7). -/
theorem operator_identity (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) :
    forestPolynomial β hβ = edgeOpProd β hβ (detPoly β) :=
  MvPolynomial.funext fun h => by
    rw [eval_forestPolynomial, expect_eq_Ih β hβ, (rel_prod β hβ _).1 h]
    rfl

end

end ArborealDecay.ForestPoly

end
