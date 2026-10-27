module

public import ArborealDecay.ExpDecay.Main

/-!
# Euclidean-distance formulation on the torus

For the uniform weight `β` on toroidal nearest-neighbour pairs, the bound in the toroidal
sup-distance implies the bound in the Euclidean norm of the representative in the fundamental
box, since `d₂ ≤ √2 d_∞`.
-/

@[expose] public section

namespace ArborealDecay.ExpDecay

open Finset ArborealDecay.Lattice

/-- Uniform weight `B` on toroidal nearest-neighbour pairs, `0` elsewhere. -/
noncomputable def torusUniformWeight (L : ℕ) (B : ℝ) (u v : ZMod L × ZMod L) : ℝ :=
  open Classical in if IsTorusNN L u v then B else 0

theorem torusUniformWeight_symm (L : ℕ) (B : ℝ) (i j : ZMod L × ZMod L) :
    torusUniformWeight L B i j = torusUniformWeight L B j i := by
  unfold torusUniformWeight
  classical
  by_cases h : IsTorusNN L i j
  · simp [h, h.symm]
  · have : ¬ IsTorusNN L j i := fun h' => h h'.symm
    simp [h, this]

theorem torusUniformWeight_nonneg {B : ℝ} (hB : 0 ≤ B) (L : ℕ) (i j : ZMod L × ZMod L) :
    0 ≤ torusUniformWeight L B i j := by
  unfold torusUniformWeight; split_ifs <;> simp [hB]

theorem torusUniformWeight_supp (L : ℕ) (B : ℝ) (i j : ZMod L × ZMod L)
    (h : torusUniformWeight L B i j ≠ 0) : IsTorusNN L i j := by
  unfold torusUniformWeight at h; by_contra h'; simp [h'] at h

theorem torusUniformWeight_le {B : ℝ} (hB : 0 ≤ B) (L : ℕ) (i j : ZMod L × ZMod L) :
    torusUniformWeight L B i j ≤ B := by
  unfold torusUniformWeight; split_ifs <;> simp [hB]

/-- Euclidean formulation of `thm:main` on the torus for the uniform weight `β`. -/
theorem expDecay_torus_eucl_of_inputs
    (hSL : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j) (D : Finset V) (x z : V),
      x ∈ D → z ∉ D →
      connProb β hβ x z ≤ ∑ u ∈ D, ∑ v ∈ Dᶜ,
        (if u ≠ v ∧ β u v ≠ 0 then
          adjProb β hβ u v * connProb β hβ x u * connProb β hβ v z else 0))
    (hSP : ∀ B : ℝ, 0 ≤ B → ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (L : ℕ) [NeZero L] (β : ZMod L × ZMod L → ZMod L × ZMod L → ℝ)
        (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j)
        (_ : ∀ i j, β i j ≠ 0 → IsTorusNN L i j) (_ : ∀ i j, β i j ≤ B)
        (x z : ZMod L × ZMod L),
        connProb β hβ x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + (torusSupDist L x z : ℝ)) ^ 2)))
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (x : ZMod L × ZMod L),
        H02.arborealProb (torusUniformWeight L B) (torusUniformWeight_symm L B)
            (fun F => F.Reachable (0 : ZMod L × ZMod L) x)
          ≤ C * Real.exp (-c * Real.sqrt (((x.1.valMinAbs : ℤ) : ℝ) ^ 2 +
              ((x.2.valMinAbs : ℤ) : ℝ) ^ 2)) := by
  obtain ⟨c, hc, h⟩ := expDecay_torus_of_inputs hSL hSP B hB
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨2, c / Real.sqrt 2, by norm_num, by positivity, ?_⟩
  intro L _ x
  refine (h L (torusUniformWeight L B) (torusUniformWeight_symm L B)
    (torusUniformWeight_nonneg hB L) (torusUniformWeight_supp L B)
    (torusUniformWeight_le hB L) 0 x).trans ?_
  set d : ℝ := (torusSupDist L 0 x : ℝ) with hd
  have e1 : |((x.1.valMinAbs : ℤ) : ℝ)| ≤ d := by
    rw [hd, torusSupDist]; simp only [Nat.cast_max]
    refine le_max_of_le_left ?_
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  have e2 : |((x.2.valMinAbs : ℤ) : ℝ)| ≤ d := by
    rw [hd, torusSupDist]; simp only [Nat.cast_max]
    refine le_max_of_le_right ?_
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hsq : Real.sqrt (((x.1.valMinAbs : ℤ) : ℝ) ^ 2 + ((x.2.valMinAbs : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt 2 * d := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by norm_num)]
    have a1 := sq_le_sq' (abs_le.mp e1).1 (abs_le.mp e1).2
    have a2 := sq_le_sq' (abs_le.mp e2).1 (abs_le.mp e2).2
    linarith
  have key : c / Real.sqrt 2 * Real.sqrt (((x.1.valMinAbs : ℤ) : ℝ) ^ 2 +
      ((x.2.valMinAbs : ℤ) : ℝ) ^ 2) ≤ c * d := by
    calc _ ≤ c / Real.sqrt 2 * (Real.sqrt 2 * d) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = c * d := by field_simp
  have := Real.exp_le_exp.mpr (show -c * d ≤ -(c / Real.sqrt 2) * Real.sqrt
    (((x.1.valMinAbs : ℤ) : ℝ) ^ 2 + ((x.2.valMinAbs : ℤ) : ℝ) ^ 2) by linarith)
  linarith

end ArborealDecay.ExpDecay
