module

public import ArborealDecay.Surgery
public import ArborealDecay.Stability

/-!
# The vertex-field forest polynomial and the Rayleigh inequality

* `forestPolynomial β hβ = ∑_F w(F) ∏_{T ∈ comp F} (1 + ∑_{i ∈ T} X_i)` (the polynomial `P_H`
  of the note), defined locally with the body fixed by the orchestrator.
* `forestPolynomial_isMultiAffine`: it is multi-affine.
* `eval_forestPolynomial`: its evaluation.
* `rayleigh_forestPolynomial_of_stable`: assuming real stability of all forest polynomials with
  nonnegative weights (the conditional input `hstab`), the Rayleigh difference of the
  two-variable decomposition is nonnegative.
-/

@[expose] public section

namespace ArborealDecay.SimonLieb

universe u

noncomputable section

open Finset MvPolynomial

open Classical in
/-- The vertex-field forest polynomial `P_U(X) = ∑_F w(F) ∏_{T ∈ comp F} (1 + ∑_{i ∈ T} X_i)`. -/
def forestPolynomial {U : Type u} [Fintype U] [DecidableEq U] (β : U → U → ℝ)
    (hβ : ∀ i j, β i j = β j i) : MvPolynomial U ℝ :=
  ∑ F : SimpleGraph U with F.IsAcyclic, C (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
    ∏ T : F.ConnectedComponent, (1 + ∑ i with F.connectedComponentMk i = T, X i)

variable {U : Type u} [Fintype U] [DecidableEq U]

theorem forestPolynomial_isMultiAffine (β : U → U → ℝ) (hβ : ∀ i j, β i j = β j i) :
    Stability.IsMultiAffine (forestPolynomial β hβ) := by
  classical
  intro k
  unfold forestPolynomial
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun F _ => ?_)
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  refine (degreeOf_prod_le _ _ _).trans ?_
  have hT : ∀ T : F.ConnectedComponent,
      (1 + ∑ i with F.connectedComponentMk i = T, (X i : MvPolynomial U ℝ)).degreeOf k ≤
        if F.connectedComponentMk k = T then 1 else 0 := by
    intro T
    refine (degreeOf_add_le _ _ _).trans (max_le (by simp [degreeOf_one]) ?_)
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun i hi => ?_)
    simp only [mem_filter, mem_univ, true_and] at hi
    by_cases hik : i = k
    · subst hik; simp [hi]
    · rw [degreeOf_X_of_ne (Ne.symm hik)]; exact Nat.zero_le _
  refine (Finset.sum_le_sum fun T _ => hT T).trans ?_
  rw [Finset.sum_ite_eq]
  simp

open Classical in
theorem eval_forestPolynomial (β : U → U → ℝ) (hβ : ∀ i j, β i j = β j i) (x : U → ℝ) :
    eval x (forestPolynomial β hβ) =
      ∑ F : SimpleGraph U with F.IsAcyclic, H02.forestWeight β hβ F *
        ∏ T : F.ConnectedComponent, (1 + ∑ i with F.connectedComponentMk i = T, x i) := by
  unfold forestPolynomial H02.forestWeight
  simp only [map_sum, map_mul, map_prod, map_add, map_one, eval_C, eval_X]

/-- Real stability of the forest polynomial, from the conditional input `hstab`. -/
theorem isRealStable_forestPolynomial_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    (β : U → U → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) :
    Stability.IsRealStable (forestPolynomial β hβ) :=
  (Stability.isRealStable_iff_aeval _).2 (hstab U β hβ hβ0)

/-- **Rayleigh inequality for the forest polynomial** (conditional on `hstab`): in the
two-variable decomposition `P = p₀₀ + X_a p₁₀ + X_b p₀₁ + X_a X_b p₁₁`,
`p₀₀(x) p₁₁(x) ≤ p₁₀(x) p₀₁(x)` at every real point. -/
theorem rayleigh_forestPolynomial_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    (β : U → U → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) {a b : U}
    (hab : a ≠ b) (x : U → ℝ) :
    ∃ c₀₀ c₁₀ c₀₁ c₁₁ : ℝ, c₀₀ * c₁₁ ≤ c₁₀ * c₀₁ ∧ ∀ s t : ℝ,
      eval (Function.update (Function.update x a s) b t) (forestPolynomial β hβ) =
        c₀₀ + c₁₀ * s + c₀₁ * t + c₁₁ * s * t := by
  have hMA := forestPolynomial_isMultiAffine β hβ
  obtain ⟨p₀₀, p₁₀, p₀₁, p₁₁, hdec, -⟩ := Stability.exists_isTwoVarDecomp hab (hMA a) (hMA b)
  have hR := Stability.IsRealStable.rayleighForm_nonneg hMA
    (isRealStable_forestPolynomial_of_stable hstab β hβ hβ0) hab x
  unfold Stability.rayleighForm at hR
  rw [hdec.rayleigh_eq hab] at hR
  exact ⟨eval x p₀₀, eval x p₁₀, eval x p₀₁, eval x p₁₁, by linarith,
    fun s t => hdec.eval_update hab x s t⟩

end

end ArborealDecay.SimonLieb
