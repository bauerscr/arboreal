module

public import ArborealDecay.Conductance.Minimiser

/-!
# The rescaled form used in the note

Conductances `c i j = w i j * U i * U j` with `U a = U b = 1` (`U` is given on the interior and
extended by `1` at the terminals), `A = lapII c a b`, `H = D_U⁻¹ A D_U⁻¹`:

* `Hmat_mulVec_U` : `H U_I = w_{Ia} + w_{Ib}` (eq:H-U);
* `effCond_rescaled` : `K = w a b + w_{aI} H⁻¹ w_{Ib}` (eq:K-Schur).
-/

@[expose] public section

namespace ArborealDecay.Conductance

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rescaled conductances `w i j * U i * U j`, with `U` extended by `1` to the terminals. -/
def rescaled (w : V → V → ℝ) {a b : V} (U : Interior a b → ℝ) : V → V → ℝ :=
  fun i j => w i j * glue a b 1 1 U i * glue a b 1 1 U j

/-- `H = D_U⁻¹ A D_U⁻¹` with `A = L_II` of the rescaled conductances. -/
noncomputable def Hmat (w : V → V → ℝ) (a b : V) (U : Interior a b → ℝ) :
    Matrix (Interior a b) (Interior a b) ℝ :=
  diagonal (fun i => (U i)⁻¹) * lapII (rescaled w U) a b * diagonal (fun i => (U i)⁻¹)

/-- Column `(w i a)_{i ∈ I}`. -/
def wToA (w : V → V → ℝ) (a b : V) : Interior a b → ℝ := fun i => w i.1 a

/-- Column `(w i b)_{i ∈ I}`. -/
def wToB (w : V → V → ℝ) (a b : V) : Interior a b → ℝ := fun i => w i.1 b

/-- Row `(w a i)_{i ∈ I}`. -/
def wFromA (w : V → V → ℝ) (a b : V) : Interior a b → ℝ := fun i => w a i.1

variable {a b : V} {w : V → V → ℝ} {U : Interior a b → ℝ}

theorem glueOne_nonneg (hU : ∀ i, 0 < U i) (v : V) : 0 ≤ glue a b 1 1 U v := by
  unfold glue
  split_ifs with h
  · exact (hU _).le
  · exact zero_le_one
  · exact zero_le_one

theorem rescaled_symm (hs : ∀ i j, w i j = w j i) (i j : V) :
    rescaled w U i j = rescaled w U j i := by
  unfold rescaled; rw [hs i j]; ring

theorem rescaled_nonneg (hw : ∀ i j, 0 ≤ w i j) (hU : ∀ i, 0 < U i) (i j : V) :
    0 ≤ rescaled w U i j :=
  mul_nonneg (mul_nonneg (hw i j) (glueOne_nonneg hU i)) (glueOne_nonneg hU j)

/-- eq:H-U: `H U_I = w_{Ia} + w_{Ib}`. -/
theorem Hmat_mulVec_U (hab : a ≠ b) (hU : ∀ i, 0 < U i) :
    Hmat w a b U *ᵥ U = wToA w a b + wToB w a b := by
  unfold Hmat
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  have h1 : (diagonal (fun i => (U i)⁻¹)) *ᵥ U = fun _ => (1 : ℝ) := by
    funext i; rw [mulVec_diagonal]; exact inv_mul_cancel₀ (hU i).ne'
  rw [h1, lapII_mulVec_one hab]
  funext i
  rw [mulVec_diagonal]
  simp only [Pi.add_apply, condToA, condToB, wToA, wToB, rescaled, glue_a hab, glue_b hab,
    glue_interior]
  have := (hU i).ne'
  field_simp

theorem Hmat_inv (hab : a ≠ b) (hU : ∀ i, 0 < U i) (hA : (lapII (rescaled w U) a b).PosDef) :
    (Hmat w a b U)⁻¹ =
      diagonal U * (lapII (rescaled w U) a b)⁻¹ * diagonal U := by
  have hu : IsUnit (lapII (rescaled w U) a b).det := (isUnit_iff_isUnit_det _).1 hA.isUnit
  have hDiD : diagonal (fun i => (U i)⁻¹) * diagonal U = (1 : Matrix _ _ ℝ) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hU i).ne'
  have hDDi : diagonal U * diagonal (fun i => (U i)⁻¹) = (1 : Matrix _ _ ℝ) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hU i).ne'
  apply Matrix.inv_eq_right_inv
  unfold Hmat
  set A := lapII (rescaled w U) a b
  set D := diagonal U
  set Di := diagonal (fun i => (U i)⁻¹)
  have e : ∀ X : Matrix (Interior a b) (Interior a b) ℝ, Di * (D * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hDiD, Matrix.one_mul]
  simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mul_assoc A, mul_nonsing_inv _ hu, Matrix.one_mul, hDiD]

/-- eq:K-Schur: `K = w a b + w_{aI} H⁻¹ w_{Ib}` for the rescaled conductances. -/
theorem effCond_rescaled (hab : a ≠ b) (hs : ∀ i j, w i j = w j i) (hw : ∀ i j, 0 ≤ w i j)
    (hU : ∀ i, 0 < U i) (hA : (lapII (rescaled w U) a b).PosDef) :
    effCond (rescaled w U) a b =
      w a b + wFromA w a b ⬝ᵥ ((Hmat w a b U)⁻¹ *ᵥ wToB w a b) := by
  rw [effCond_eq_schur hab (rescaled_symm hs) (rescaled_nonneg hw hU) hA,
    Hmat_inv hab hU hA, ← mulVec_mulVec, ← mulVec_mulVec]
  have hB : diagonal U *ᵥ wToB w a b = condToB (rescaled w U) a b := by
    funext i
    rw [mulVec_diagonal]
    simp only [wToB, condToB, rescaled, glue_b hab, glue_interior]; ring
  have hc : ∀ y : Interior a b → ℝ,
      wFromA w a b ⬝ᵥ (diagonal U *ᵥ y) = condFromA (rescaled w U) a b ⬝ᵥ y := by
    intro y
    simp only [dotProduct, mulVec_diagonal]
    refine sum_congr rfl fun i _ => ?_
    simp only [wFromA, condFromA, rescaled, glue_a hab, glue_interior]; ring
  rw [hB, hc]
  simp only [rescaled, glue_a hab, glue_b hab]
  ring

end ArborealDecay.Conductance
