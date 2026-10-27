module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import ArborealDecay.MatrixForest.Laplacian

/-!
# Effective conductance: definitions and the energy form

Conventions. `c : V → V → ℝ` is symmetric and nonnegative; the diagonal `c i i` plays no role.
The Dirichlet energy is the ordered-pair form `energy c v = ½ ∑_{i,j} c i j (v i - v j)^2`
(= the sum over unordered edges `{i,j}` of `c i j (v i - v j)^2`).
A potential `v` is *admissible* (for terminals `a ≠ b`) if `v a = 1` and `v b = 0`.

* `effCond c a b := ⨅ v admissible, energy c v` (variational definition).
* `Interior a b = {v // v ≠ a ∧ v ≠ b}`; `lapII c a b` is the block of `MatrixForest.lap c` on it.
-/

@[expose] public section

namespace ArborealDecay.Conductance

set_option linter.unusedSectionVars false

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The interior vertices (all but the two terminals). -/
abbrev Interior (a b : V) : Type _ := {v : V // v ≠ a ∧ v ≠ b}

/-- Polarised Dirichlet form `½ ∑_{i,j} c i j (v i - v j)(w i - w j)`. -/
noncomputable def energyForm (c : V → V → ℝ) (v w : V → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, c i j * ((v i - v j) * (w i - w j))

/-- The Dirichlet energy `½ ∑_{i,j} c i j (v i - v j)^2`. -/
noncomputable def energy (c : V → V → ℝ) (v : V → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, c i j * (v i - v j) ^ 2

/-- Admissible potentials: `v a = 1`, `v b = 0`. -/
def Admissible (a b : V) (v : V → ℝ) : Prop := v a = 1 ∧ v b = 0

/-- Effective conductance between `a` and `b`: the infimum of the Dirichlet energy over admissible
potentials (the variational / Dirichlet-principle definition). -/
noncomputable def effCond (c : V → V → ℝ) (a b : V) : ℝ :=
  ⨅ v : {v : V → ℝ // Admissible a b v}, energy c v.1

/-- The interior block `L_II` of the Laplacian of `c`. -/
def lapII (c : V → V → ℝ) (a b : V) : Matrix (Interior a b) (Interior a b) ℝ :=
  (MatrixForest.lap c).submatrix Subtype.val Subtype.val

/-- Potential equal to `α` at `a`, `β` at `b` and `x` on the interior. -/
def glue (a b : V) (α β : ℝ) (x : Interior a b → ℝ) (v : V) : ℝ :=
  if h : v ≠ a ∧ v ≠ b then x ⟨v, h⟩ else if v = a then α else β

/-- The net current `∑_j c i j (v i - v j)` out of `i` for the potential `v`. -/
def flow (c : V → V → ℝ) (v : V → ℝ) (i : V) : ℝ := ∑ j, c i j * (v i - v j)

theorem energy_eq_form (c : V → V → ℝ) (v : V → ℝ) : energy c v = energyForm c v v := by
  simp [energy, energyForm, sq]

theorem energyForm_comm (c : V → V → ℝ) (v w : V → ℝ) :
    energyForm c v w = energyForm c w v := by
  unfold energyForm
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem energyForm_add_left (c : V → V → ℝ) (v v' w : V → ℝ) :
    energyForm c (v + v') w = energyForm c v w + energyForm c v' w := by
  unfold energyForm
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]; ring

theorem energyForm_add_right (c : V → V → ℝ) (v w w' : V → ℝ) :
    energyForm c v (w + w') = energyForm c v w + energyForm c v w' := by
  rw [energyForm_comm, energyForm_add_left, energyForm_comm c w, energyForm_comm c w']

theorem energyForm_nonneg {c : V → V → ℝ} (hc : ∀ i j, 0 ≤ c i j) (v : V → ℝ) :
    0 ≤ energyForm c v v := by
  rw [← energy_eq_form]
  unfold energy
  exact mul_nonneg (by norm_num)
    (sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hc i j) (sq_nonneg _))

/-- Summation by parts: for symmetric `c`, `½ ∑ c (v i - v j)(w i - w j) = ∑ w i (flow v i)`. -/
theorem energyForm_eq_sum_flow {c : V → V → ℝ} (hs : ∀ i j, c i j = c j i) (v w : V → ℝ) :
    energyForm c v w = ∑ i, w i * flow c v i := by
  have h1 : ∑ i, ∑ j, c i j * ((v i - v j) * (w i - w j))
      = ∑ i, ∑ j, c i j * (v i - v j) * w i - ∑ i, ∑ j, c i j * (v i - v j) * w j := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∑ i, ∑ j, c i j * (v i - v j) * w j = - ∑ i, ∑ j, c i j * (v i - v j) * w i := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [hs j i]; ring
  have h3 : ∑ i, w i * flow c v i = ∑ i, ∑ j, c i j * (v i - v j) * w i := by
    refine sum_congr rfl fun i _ => ?_
    unfold flow
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  unfold energyForm
  rw [h1, h2, ← h3]; ring

/-- `lap c` acts as the net current. -/
theorem lap_mulVec_apply (c : V → V → ℝ) (v : V → ℝ) (i : V) :
    (MatrixForest.lap c *ᵥ v) i = flow c v i := by
  unfold flow
  simp only [mulVec, dotProduct]
  rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
  rw [MatrixForest.lap_apply_self]
  simp only [sub_self, mul_zero, zero_add]
  have : ∀ j ∈ univ.erase i, MatrixForest.lap c i j * v j = - (c i j * v j) := fun j hj => by
    rw [MatrixForest.lap_apply_of_ne c (Ne.symm (ne_of_mem_erase hj))]; ring
  rw [sum_congr rfl this, sum_mul, sum_neg_distrib, ← sub_eq_add_neg, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- Splitting a sum over `V` into the terminals and the interior. -/
theorem sum_split {a b : V} (hab : a ≠ b) (f : V → ℝ) :
    ∑ j, f j = f a + f b + ∑ j : Interior a b, f j.1 := by
  have h := Finset.sum_filter_add_sum_filter_not (univ : Finset V) (fun j => j ≠ a ∧ j ≠ b) f
  rw [← h]
  have e1 : ∑ j ∈ univ.filter (fun j => j ≠ a ∧ j ≠ b), f j = ∑ j : Interior a b, f j.1 := by
    rw [← Finset.sum_subtype (univ.filter (fun j => j ≠ a ∧ j ≠ b)) (p := fun j => j ≠ a ∧ j ≠ b)
      (by intro x; simp) f]
  have e2 : univ.filter (fun j => ¬ (j ≠ a ∧ j ≠ b)) = {a, b} := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]; tauto
  rw [e1, e2, sum_pair hab]; ring

@[simp] theorem glue_interior (a b : V) (α β : ℝ) (x : Interior a b → ℝ) (i : Interior a b) :
    glue a b α β x i.1 = x i := by
  simp [glue, i.2]

@[simp] theorem glue_a {a b : V} (hab : a ≠ b) (α β : ℝ) (x : Interior a b → ℝ) :
    glue a b α β x a = α := by
  simp [glue]

@[simp] theorem glue_b {a b : V} (hab : a ≠ b) (α β : ℝ) (x : Interior a b → ℝ) :
    glue a b α β x b = β := by
  simp [glue, hab.symm]

/-- The interior block of the Laplacian: `(L_II x)_i = flow(glue 0 0 x) i`. -/
theorem lapII_mulVec_apply {a b : V} (hab : a ≠ b) (c : V → V → ℝ) (x : Interior a b → ℝ)
    (i : Interior a b) :
    (lapII c a b *ᵥ x) i = flow c (glue a b 0 0 x) i.1 := by
  rw [← lap_mulVec_apply]
  simp only [mulVec, dotProduct, lapII, submatrix_apply]
  rw [sum_split hab (fun j => MatrixForest.lap c i.1 j * glue a b 0 0 x j)]
  simp [glue_a hab, glue_b hab]

/-- General form: for any potential `v` and interior `i`,
`flow v i = (L_II v_I) i - c i a * v a - c i b * v b`. -/
theorem flow_interior {a b : V} (hab : a ≠ b) (c : V → V → ℝ) (v : V → ℝ) (i : Interior a b) :
    flow c v i.1 = (lapII c a b *ᵥ (fun j => v j.1)) i - c i.1 a * v a - c i.1 b * v b := by
  rw [lapII_mulVec_apply hab, flow, flow, sum_split hab, sum_split hab]
  simp only [glue_a hab, glue_b hab, glue_interior]
  have := i.2.1
  have := i.2.2
  simp only [sub_zero]
  ring
