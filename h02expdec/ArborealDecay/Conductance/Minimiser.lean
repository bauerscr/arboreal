module

public import ArborealDecay.Conductance.PosDef

/-!
# The harmonic extension, the Dirichlet principle and the Schur formulas

With `A = lapII c a b` positive definite, the voltage `harmonic c a b`
(`h a = 1`, `h b = 0`, `h_I = A⁻¹ c_{Ia}`) minimises the energy among admissible potentials, and
`effCond c a b = c a b + ∑_{i ∈ I} c a i (1 - h i) = c a b + c_{aI} · A⁻¹ · c_{Ib}`.
-/

@[expose] public section

namespace ArborealDecay.Conductance

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Column `(c i a)_{i ∈ I}`. -/
def condToA (c : V → V → ℝ) (a b : V) : Interior a b → ℝ := fun i => c i.1 a

/-- Column `(c i b)_{i ∈ I}`. -/
def condToB (c : V → V → ℝ) (a b : V) : Interior a b → ℝ := fun i => c i.1 b

/-- Row `(c a i)_{i ∈ I}`. -/
def condFromA (c : V → V → ℝ) (a b : V) : Interior a b → ℝ := fun i => c a i.1

/-- The harmonic extension: `h a = 1`, `h b = 0`, `h_I = (L_II)⁻¹ c_{Ia}`. -/
noncomputable def harmonic (c : V → V → ℝ) (a b : V) : V → ℝ :=
  glue a b 1 0 ((lapII c a b)⁻¹ *ᵥ condToA c a b)

/-- Dirichlet principle (eq:Dirichlet-K): the effective conductance is at most the energy of any
admissible potential. -/
theorem effCond_le_energy {c : V → V → ℝ} (hc : ∀ i j, 0 ≤ c i j) {a b : V} {f : V → ℝ}
    (hf : Admissible a b f) : effCond c a b ≤ energy c f := by
  refine ciInf_le ⟨0, ?_⟩ (⟨f, hf⟩ : {v : V → ℝ // Admissible a b v})
  rintro _ ⟨v, rfl⟩
  show 0 ≤ energy c v.1
  rw [energy_eq_form]; exact energyForm_nonneg hc _

theorem harmonic_admissible {a b : V} (hab : a ≠ b) (c : V → V → ℝ) :
    Admissible a b (harmonic c a b) := ⟨glue_a hab _ _ _, glue_b hab _ _ _⟩

variable {a b : V} {c : V → V → ℝ}

theorem lapII_mulVec_harmonic (hab : a ≠ b) (hL : (lapII c a b).PosDef) :
    lapII c a b *ᵥ (fun j => harmonic c a b j.1) = condToA c a b := by
  have hu : IsUnit (lapII c a b).det := (isUnit_iff_isUnit_det _).1 hL.isUnit
  have : (fun j : Interior a b => harmonic c a b j.1) = (lapII c a b)⁻¹ *ᵥ condToA c a b := by
    funext j; simp [harmonic]
  rw [this, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

theorem flow_harmonic_interior (hab : a ≠ b) (hL : (lapII c a b).PosDef) (i : Interior a b) :
    flow c (harmonic c a b) i.1 = 0 := by
  rw [flow_interior hab, lapII_mulVec_harmonic hab hL, (harmonic_admissible hab c).1,
    (harmonic_admissible hab c).2]
  simp [condToA]

/-- `form(h, u) = 0` for `u` vanishing at the terminals and `h` harmonic. -/
theorem energyForm_harmonic_vanishing (hab : a ≠ b) (hs : ∀ i j, c i j = c j i)
    (hL : (lapII c a b).PosDef) {u : V → ℝ} (ha : u a = 0) (hb : u b = 0) :
    energyForm c (harmonic c a b) u = 0 := by
  rw [energyForm_eq_sum_flow hs, sum_split hab, ha, hb]
  simp [flow_harmonic_interior hab hL]

/-- The harmonic extension minimises the energy among admissible potentials. -/
theorem energy_harmonic_le (hab : a ≠ b) (hs : ∀ i j, c i j = c j i) (hc : ∀ i j, 0 ≤ c i j)
    (hL : (lapII c a b).PosDef) {v : V → ℝ} (hv : Admissible a b v) :
    energy c (harmonic c a b) ≤ energy c v := by
  set h := harmonic c a b with hh
  have hha : Admissible a b h := harmonic_admissible hab c
  have hu : v = h + (v - h) := by abel
  have ha : (v - h) a = 0 := by simp [hv.1, hha.1]
  have hb : (v - h) b = 0 := by simp [hv.2, hha.2]
  rw [energy_eq_form, energy_eq_form]
  conv_rhs => rw [hu]
  rw [energyForm_add_left, energyForm_add_right, energyForm_add_right,
    energyForm_harmonic_vanishing hab hs hL ha hb, energyForm_comm c (v - h) h,
    energyForm_harmonic_vanishing hab hs hL ha hb]
  linarith [energyForm_nonneg hc (v - h)]

/-- The infimum defining `effCond` is attained at the harmonic extension. -/
theorem effCond_eq_energy_harmonic (hab : a ≠ b) (hs : ∀ i j, c i j = c j i)
    (hc : ∀ i j, 0 ≤ c i j) (hL : (lapII c a b).PosDef) :
    effCond c a b = energy c (harmonic c a b) := by
  refine le_antisymm (effCond_le_energy hc (harmonic_admissible hab c)) ?_
  haveI : Nonempty {v : V → ℝ // Admissible a b v} := ⟨⟨_, harmonic_admissible hab c⟩⟩
  exact le_ciInf fun v => energy_harmonic_le hab hs hc hL v.2

/-- Effective conductance as the current out of `a`. -/
theorem effCond_eq_current (hab : a ≠ b) (hs : ∀ i j, c i j = c j i) (hc : ∀ i j, 0 ≤ c i j)
    (hL : (lapII c a b).PosDef) :
    effCond c a b = c a b + ∑ i : Interior a b, c a i.1 * (1 - harmonic c a b i.1) := by
  rw [effCond_eq_energy_harmonic hab hs hc hL, energy_eq_form, energyForm_eq_sum_flow hs,
    sum_split hab]
  have hha := harmonic_admissible hab c
  simp only [flow_harmonic_interior hab hL, mul_zero, sum_const_zero, add_zero, hha.1, hha.2,
    zero_mul, one_mul]
  unfold flow
  rw [sum_split hab]
  simp [hha.1, hha.2]

theorem lapII_mulVec_one (hab : a ≠ b) :
    lapII c a b *ᵥ (fun _ => (1 : ℝ)) = condToA c a b + condToB c a b := by
  funext i
  have := flow_interior hab c (fun _ => (1 : ℝ)) i
  simp only [flow, sub_self, mul_zero, sum_const_zero, mul_one] at this
  simp only [Pi.add_apply, condToA, condToB]
  linarith

/-- Unscaled `eq:H-U`: `L_II⁻¹ (c_{Ia} + c_{Ib}) = 1`. -/
theorem lapII_inv_mulVec_add (hab : a ≠ b) (hL : (lapII c a b).PosDef) :
    (lapII c a b)⁻¹ *ᵥ (condToA c a b + condToB c a b) = fun _ => 1 := by
  have hu : IsUnit (lapII c a b).det := (isUnit_iff_isUnit_det _).1 hL.isUnit
  rw [← lapII_mulVec_one hab, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- The Schur-complement form of the effective conductance (eq:K-Schur, unscaled):
`K = c a b + c_{aI} · L_II⁻¹ · c_{Ib}`. -/
theorem effCond_eq_schur (hab : a ≠ b) (hs : ∀ i j, c i j = c j i) (hc : ∀ i j, 0 ≤ c i j)
    (hL : (lapII c a b).PosDef) :
    effCond c a b =
      c a b + condFromA c a b ⬝ᵥ ((lapII c a b)⁻¹ *ᵥ condToB c a b) := by
  rw [effCond_eq_current hab hs hc hL]
  have h1 := lapII_inv_mulVec_add hab hL
  rw [mulVec_add] at h1
  have h2 : condFromA c a b ⬝ᵥ (fun _ => (1 : ℝ)) =
      condFromA c a b ⬝ᵥ ((lapII c a b)⁻¹ *ᵥ condToA c a b)
        + condFromA c a b ⬝ᵥ ((lapII c a b)⁻¹ *ᵥ condToB c a b) := by
    rw [← dotProduct_add, h1]
  have h3 : ∑ i : Interior a b, c a i.1 * (1 - harmonic c a b i.1)
      = condFromA c a b ⬝ᵥ (fun _ => (1 : ℝ))
        - condFromA c a b ⬝ᵥ ((lapII c a b)⁻¹ *ᵥ condToA c a b) := by
    simp only [dotProduct, harmonic, glue_interior, condFromA, mul_one, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [h3]; linarith

end ArborealDecay.Conductance
