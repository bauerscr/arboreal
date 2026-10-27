module

public import ArborealDecay.Horo.Diffeo
public import ArborealDecay.Grassmann.Algebra

/-!
# The `ℍ^{2|4}` inner product in horospherical coordinates

BCHS v2 (`refs/BCHS/src/h02.tex`), (2.73) at L1551–1563 and the action (2.59) at L1427–1433.
The `ℍ^{2|4}` inner product is (BCHS (2.40); `ArborealDecay.Super.H24.dotH`)
`u_i · u_j = x_i x_j + y_i y_j + ∑_γ (η^γ_i ξ^γ_j − ξ^γ_i η^γ_j) − z_i z_j`,
with `z_i² = 1 + x_i² + y_i² − 2 ∑_γ ξ^γ_i η^γ_i`.

**Bosonic part** (`neg_mdot_horo`): with `x, y` from `horo` and `z = √(1 + x² + y²)`,
`−u_i · u_j = cosh (t_i − t_j) + ½ e^{t_i + t_j} (s_i − s_j)²`.

**Full version** (`neg_udot`): the horospherical change of generators (2.73),
`x = sinh t − eᵗ (½ s² + ∑_γ ψ̄^γ ψ^γ)`, `y = eᵗ s`, `ξ^γ = eᵗ ψ^γ`, `η^γ = eᵗ ψ̄^γ`,
`z = cosh t + eᵗ (½ s² + ∑_γ ψ̄^γ ψ^γ)`, gives
`−u_i · u_j = cosh (t_i − t_j) + e^{t_i + t_j} (½ (s_i − s_j)² + ∑_γ (ψ̄^γ_i − ψ̄^γ_j)(ψ^γ_i − ψ^γ_j))`
and `z_i² = 1 + x_i² + y_i² − 2 ∑_γ ξ^γ_i η^γ_i` (`zS_sq`), `x_i + z_i = e^{t_i}` (`xS_add_zS`).
The fermion generators are arbitrary degree-one elements `ι (v)` of an exterior algebra; the
number of fermion pairs per vertex is an arbitrary finite type `C` (`C = Fin 2` in BCHS).

The quadratic part of the action: `actionQuad` (`sum_edge_field_eq`):
`½ ∑_{i,j} β_ij (cosh (t_i − t_j) + ½ e^{t_i+t_j}(s_i − s_j)² − 1) + ∑_i h_i (z_i − 1)
 = ½ ∑ β_ij (cosh (t_i − t_j) − 1) + ∑ h_i (cosh t_i − 1) + ½ sᵀ L(t) s`,
where `L(t)` is the positive matrix of supplement §10 (T3) (BCHS's "`−Δ_{β(t),h(t)}`", corrected
sign) and the field term carries `s_i²` (T1).
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open Real Finset

set_option linter.unusedSectionVars false

/-! ### Bosonic part -/

/-- `−(x x' + y y' − z z')` at two horospherical points equals
`cosh (t − t') + ½ e^{t + t'} (s − s')²`. -/
theorem neg_mdot_hxyz (t s t' s' : ℝ) :
    -(hx t s * hx t' s' + hy t s * hy t' s' - hz t s * hz t' s') =
      cosh (t - t') + exp (t + t') * (s - s') ^ 2 / 2 := by
  simp only [hx, hy, hz]
  rw [cosh_sub, exp_add, cosh_eq, sinh_eq, cosh_eq, sinh_eq]
  ring

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The Minkowski inner product `u_i · u_j = x_i x_j + y_i y_j − z_i z_j` on the hyperboloid,
`z = √(1 + x² + y²)`. -/
def mdot (q : N ⊕ N → ℝ) (i j : N) : ℝ :=
  q (.inl i) * q (.inl j) + q (.inr i) * q (.inr j) -
    zOf (q (.inl i)) (q (.inr i)) * zOf (q (.inl j)) (q (.inr j))

theorem zOf_horo_apply (p : N ⊕ N → ℝ) (i : N) :
    zOf (horo p (.inl i)) (horo p (.inr i)) = hz (p (.inl i)) (p (.inr i)) := by
  simp [zOf_horo]

/-- **BCHS horospherical inner product** (bosonic part). -/
theorem neg_mdot_horo (p : N ⊕ N → ℝ) (i j : N) :
    -mdot (horo p) i j = cosh (p (.inl i) - p (.inl j)) +
      exp (p (.inl i) + p (.inl j)) * (p (.inr i) - p (.inr j)) ^ 2 / 2 := by
  rw [mdot, zOf_horo_apply, zOf_horo_apply]
  exact neg_mdot_hxyz _ _ _ _

/-- `x_i + z_i = e^{t_i}`. -/
theorem horo_add_zOf (p : N ⊕ N → ℝ) (i : N) :
    horo p (.inl i) + zOf (horo p (.inl i)) (horo p (.inr i)) = exp (p (.inl i)) := by
  rw [zOf_horo_apply, horo_inl, hx_add_hz]

/-- `y_i = e^{t_i} s_i`. -/
theorem horo_inr_eq (p : N ⊕ N → ℝ) (i : N) :
    horo p (.inr i) = exp (p (.inl i)) * p (.inr i) := rfl

/-- `z_i − 1 = cosh t_i + ½ e^{t_i} s_i² − 1` (BCHS (2.59) field term with `s_i²`, typo T1). -/
theorem zOf_horo_sub_one (p : N ⊕ N → ℝ) (i : N) :
    zOf (horo p (.inl i)) (horo p (.inr i)) - 1 =
      cosh (p (.inl i)) + exp (p (.inl i)) * p (.inr i) ^ 2 / 2 - 1 := by
  rw [zOf_horo_apply, hz]

/-! ### The quadratic form in `s` -/

/-- The positive matrix `L(t)` (BCHS's "`−Δ_{β(t),h(t)}`" with the sign corrected, supplement
§10 (T3)): `L_ij = δ_ij (∑_k β_ik e^{t_i + t_k} + h_i e^{t_i}) − β_ij e^{t_i + t_j}`.
(The diagonal `β_ii` terms cancel.) -/
def lapT (β : N → N → ℝ) (h t : N → ℝ) : Matrix N N ℝ := fun i j =>
  (if i = j then ∑ k, β i k * exp (t i + t k) + h i * exp (t i) else 0) -
    β i j * exp (t i + t j)

theorem dotProduct_lapT (β : N → N → ℝ) (h t s : N → ℝ) :
    s ⬝ᵥ (lapT β h t).mulVec s =
      ∑ i, ∑ j, β i j * exp (t i + t j) * s i ^ 2 + ∑ i, h i * exp (t i) * s i ^ 2 -
        ∑ i, ∑ j, β i j * exp (t i + t j) * s i * s j := by
  simp only [lapT, Matrix.mulVec, dotProduct, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    add_mul, mul_add]
  congr 1; congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The `s`-dependent part of the horospherical action is `½ sᵀ L(t) s`. -/
theorem sum_edge_field_quad (β : N → N → ℝ) (hβ : ∀ i j, β i j = β j i) (h t s : N → ℝ) :
    (∑ i, ∑ j, β i j * (exp (t i + t j) * (s i - s j) ^ 2 / 2)) / 2 +
        ∑ i, h i * (exp (t i) * s i ^ 2 / 2) =
      (s ⬝ᵥ (lapT β h t).mulVec s) / 2 := by
  have hsym : ∑ i, ∑ j, β i j * exp (t i + t j) * s j ^ 2 =
      ∑ i, ∑ j, β i j * exp (t i + t j) * s i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hβ, add_comm (t j)]
  have e1 : ∑ i, ∑ j, β i j * (exp (t i + t j) * (s i - s j) ^ 2 / 2) =
      (∑ i, ∑ j, β i j * exp (t i + t j) * s i ^ 2 +
        ∑ i, ∑ j, β i j * exp (t i + t j) * s j ^ 2 -
        2 * ∑ i, ∑ j, β i j * exp (t i + t j) * s i * s j) / 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : ∑ i, h i * (exp (t i) * s i ^ 2 / 2) = (∑ i, h i * exp (t i) * s i ^ 2) / 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, hsym, e2, dotProduct_lapT]
  ring

/-! ### The full change of generators -/

section Super

variable {C M : Type*} [Fintype C] [AddCommGroup M] [Module ℝ M]

local notation "G" => ExteriorAlgebra ℝ M

open ExteriorAlgebra Grassmann

/-- Horospherical data at the vertices `N`: scalars `t, s`, and odd generators
`ψ^γ_i = ι (vψ γ i)`, `ψ̄^γ_i = ι (vψb γ i)`. -/
structure HData (N C M : Type*) where
  /-- `t_i`. -/
  t : N → ℝ
  /-- `s_i`. -/
  s : N → ℝ
  /-- `ψ^γ_i` as a vector. -/
  vψ : C → N → M
  /-- `ψ̄^γ_i` as a vector. -/
  vψb : C → N → M

variable (D : HData N C M)

/-- `ψ^γ_i`. -/
def HData.ψ (γ : C) (i : N) : G := ι ℝ (D.vψ γ i)
/-- `ψ̄^γ_i`. -/
def HData.ψb (γ : C) (i : N) : G := ι ℝ (D.vψb γ i)

/-- `n_i = ∑_γ ψ̄^γ_i ψ^γ_i`. -/
def HData.nn (i : N) : G := ∑ γ, D.ψb γ i * D.ψ γ i

/-- `x_i = sinh t_i − e^{t_i} (½ s_i² + n_i)`. -/
def HData.xS (i : N) : G := hx (D.t i) (D.s i) • (1 : G) - exp (D.t i) • D.nn i
/-- `y_i = e^{t_i} s_i`. -/
def HData.yS (i : N) : G := hy (D.t i) (D.s i) • (1 : G)
/-- `z_i = cosh t_i + e^{t_i} (½ s_i² + n_i)`. -/
def HData.zS (i : N) : G := hz (D.t i) (D.s i) • (1 : G) + exp (D.t i) • D.nn i
/-- `ξ^γ_i = e^{t_i} ψ^γ_i`. -/
def HData.ξS (γ : C) (i : N) : G := exp (D.t i) • D.ψ γ i
/-- `η^γ_i = e^{t_i} ψ̄^γ_i`. -/
def HData.ηS (γ : C) (i : N) : G := exp (D.t i) • D.ψb γ i

/-- `u_i · u_j = x_i x_j + y_i y_j + ∑_γ (η^γ_i ξ^γ_j − ξ^γ_i η^γ_j) − z_i z_j` (BCHS (2.40)). -/
def HData.udot (i j : N) : G :=
  D.xS i * D.xS j + D.yS i * D.yS j + ∑ γ, (D.ηS γ i * D.ξS γ j - D.ξS γ i * D.ηS γ j) -
    D.zS i * D.zS j

theorem HData.ψ_mul_ψb (γ : C) (i j : N) : D.ψ γ i * D.ψb γ j = -(D.ψb γ j * D.ψ γ i) :=
  ι_anticomm _ _

/-- **BCHS horospherical inner product** (full form):
`−u_i · u_j = cosh (t_i − t_j) + e^{t_i + t_j} (½ (s_i − s_j)² + ∑_γ (ψ̄^γ_i − ψ̄^γ_j)(ψ^γ_i − ψ^γ_j))`. -/
theorem HData.neg_udot (i j : N) :
    -D.udot i j = (cosh (D.t i - D.t j) + exp (D.t i + D.t j) * (D.s i - D.s j) ^ 2 / 2) • (1 : G) +
      exp (D.t i + D.t j) • ∑ γ, (D.ψb γ i - D.ψb γ j) * (D.ψ γ i - D.ψ γ j) := by
  have key := neg_mdot_hxyz (D.t i) (D.s i) (D.t j) (D.s j)
  have hxz := hx_add_hz (D.t i) (D.s i)
  have hxz' := hx_add_hz (D.t j) (D.s j)
  have hf : ∑ γ, (D.ηS γ i * D.ξS γ j - D.ξS γ i * D.ηS γ j) =
      exp (D.t i + D.t j) • (∑ γ, D.ψb γ i * D.ψ γ j + ∑ γ, D.ψb γ j * D.ψ γ i) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [HData.ηS, HData.ξS, smul_mul_smul, D.ψ_mul_ψb, exp_add]
    rw [smul_neg, sub_neg_eq_add, smul_add]
  have ht : ∑ γ, (D.ψb γ i - D.ψb γ j) * (D.ψ γ i - D.ψ γ j) =
      D.nn i + D.nn j - (∑ γ, D.ψb γ i * D.ψ γ j + ∑ γ, D.ψb γ j * D.ψ γ i) := by
    simp only [HData.nn, sub_mul, mul_sub, Finset.sum_sub_distrib]
    abel
  rw [HData.udot, hf, ht]
  simp only [HData.xS, HData.yS, HData.zS, sub_mul, mul_sub, add_mul, mul_add,
    one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  rw [exp_add]
  have e1 : (cosh (D.t i - D.t j) + exp (D.t i) * exp (D.t j) * (D.s i - D.s j) ^ 2 / 2) =
      -(hx (D.t i) (D.s i) * hx (D.t j) (D.s j) + hy (D.t i) (D.s i) * hy (D.t j) (D.s j) -
        hz (D.t i) (D.s i) * hz (D.t j) (D.s j)) := by rw [key, exp_add]
  rw [e1]
  have e2 : exp (D.t i) = hx (D.t i) (D.s i) + hz (D.t i) (D.s i) := hxz.symm
  have e3 : exp (D.t j) = hx (D.t j) (D.s j) + hz (D.t j) (D.s j) := hxz'.symm
  set a := hx (D.t i) (D.s i)
  set b := hx (D.t j) (D.s j)
  set c := hz (D.t i) (D.s i)
  set d := hz (D.t j) (D.s j)
  rw [e2, e3]
  module

/-- `x_i + z_i = e^{t_i}`. -/
theorem HData.xS_add_zS (i : N) : D.xS i + D.zS i = exp (D.t i) • (1 : G) := by
  rw [HData.xS, HData.zS, ← hx_add_hz (D.t i) (D.s i)]
  module

theorem HData.nn_comm (i : N) (a : G) : D.nn i * a = a * D.nn i := by
  refine mul_comm_of_even ?_ a
  simp only [HData.nn, map_sum, map_mul, HData.ψb, HData.ψ, inv'_ι, neg_mul_neg]

/-- **`z` is the hyperboloid coordinate**: `z_i² = 1 + x_i² + y_i² − 2 ∑_γ ξ^γ_i η^γ_i`. -/
theorem HData.zS_sq (i : N) :
    D.zS i * D.zS i =
      (1 : G) + D.xS i * D.xS i + D.yS i * D.yS i - (2 : ℝ) • ∑ γ, D.ξS γ i * D.ηS γ i := by
  have hq := hz_sq (D.t i) (D.s i)
  have hxz := hx_add_hz (D.t i) (D.s i)
  have hf : ∑ γ, D.ξS γ i * D.ηS γ i = -(exp (D.t i) * exp (D.t i)) • D.nn i := by
    rw [HData.nn, Finset.smul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [HData.ξS, HData.ηS, smul_mul_smul, D.ψ_mul_ψb, smul_neg, neg_smul]
  rw [hf]
  simp only [HData.xS, HData.yS, HData.zS, sub_mul, mul_sub, add_mul, mul_add,
    one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  have e2 : exp (D.t i) = hx (D.t i) (D.s i) + hz (D.t i) (D.s i) := hxz.symm
  set a := hx (D.t i) (D.s i)
  set c := hz (D.t i) (D.s i)
  set y := hy (D.t i) (D.s i)
  rw [e2]
  have hq' : c * c = 1 + a * a + y * y := by rw [← sq, hq]; ring
  linear_combination (norm := module) hq' • (1 : G)

end Super

end

end ArborealDecay.Horo

end
