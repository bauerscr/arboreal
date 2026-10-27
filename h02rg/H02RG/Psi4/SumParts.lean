import Step.Defs

/-!
# Summation by parts on the torus (Section `sec:proofs`, proof of `thm:psi4-full` (ii))

On the torus `Λ_N`,
`∑_x (-Δψ)_x ψ̄_x = ∑_x ψ_x (-Δψ̄)_x = ∑_x (∇ψ)_x (∇ψ̄)_x` (`sum_negLapPsi_mul`,
`sum_mul_negLapPsibar`), hence
`y₀ (∇ψ, ∇ψ̄) + (z₀/2)((-Δψ, ψ̄) + (ψ, -Δψ̄)) = (y₀ + z₀)(∇ψ, ∇ψ̄)`, i.e.
`V(Λ)` with couplings `(z, y, a, b)` equals `V(Λ)` with couplings `(0, y + z, a, b)`
(`eval_univ_sumParts`, `VE_univ_sumParts`).  The order of the Grassmann factors is preserved
throughout (`∇ψ` to the left of `∇ψ̄`), so no signs from anticommutation occur.
-/

namespace Psi4

noncomputable section

open Finset Grassmann Loc Step

variable {d L N : ℕ} [NeZero L]

/-- `∑_x (∇_e ψ)_{x - e} F_x = ∑_x (∇_e ψ)_x F_{x + e}` (translation invariance of the sum). -/
theorem sum_shift (e : Dir d) (f g : Lam d L N → Alg d L N) :
    ∑ x, f (x - dirVec e) * g x = ∑ x, f x * g (x + dirVec e) := by
  symm
  refine Fintype.sum_equiv (Equiv.addRight (dirVec e)) _ _ fun x => ?_
  simp

/-- `∑_x (-Δψ)_x ψ̄_x = ∑_x (∇ψ)_x (∇ψ̄)_x`. -/
theorem sum_negLapPsi_mul :
    ∑ x : Lam d L N, (-lapPsi x) * psibar x = ∑ x : Lam d L N, gradSq x := by
  have h : ∀ x : Lam d L N, (-lapPsi x) * psibar x =
      (1 / 2 : ℂ) • ∑ e : Dir d, (grad e (x - dirVec e) * psibar x - grad e x * psibar x) := by
    intro x
    rw [lapPsi, ← neg_smul, neg_neg, smul_mul_assoc, sum_mul]
    simp only [sub_mul]
  simp only [h, gradSq, ← smul_sum]
  congr 1
  rw [sum_comm, sum_comm (f := fun x e => grad e x * gradbar e x)]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_sub_distrib, sum_shift e (grad e) psibar, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [gradbar, mul_sub]

/-- `∑_x ψ_x (-Δψ̄)_x = ∑_x (∇ψ)_x (∇ψ̄)_x`. -/
theorem sum_mul_negLapPsibar :
    ∑ x : Lam d L N, psi x * (-lapPsibar x) = ∑ x : Lam d L N, gradSq x := by
  have h : ∀ x : Lam d L N, psi x * (-lapPsibar x) =
      (1 / 2 : ℂ) • ∑ e : Dir d, (psi x * gradbar e (x - dirVec e) - psi x * gradbar e x) := by
    intro x
    rw [lapPsibar, ← neg_smul, neg_neg, mul_smul_comm, mul_sum]
    simp only [mul_sub]
  simp only [h, gradSq, ← smul_sum]
  congr 1
  rw [sum_comm, sum_comm (f := fun x e => grad e x * gradbar e x)]
  refine sum_congr rfl fun e _ => ?_
  have hs : ∑ x : Lam d L N, psi x * gradbar e (x - dirVec e) =
      ∑ x : Lam d L N, psi (x + dirVec e) * gradbar e x := by
    refine Fintype.sum_equiv (Equiv.subRight (dirVec e)) _ _ fun x => ?_
    simp
  rw [sum_sub_distrib, hs, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [grad, sub_mul]

/-- **Summation by parts**: `V(Λ)` with couplings `(z, y, a, b)` equals `V(Λ)` with couplings
`(0, y + z, a, b)`. -/
theorem eval_univ_sumParts (z y a b : ℂ) :
    (⟨z, y, a, b⟩ : Vcoup).eval (univ : Finset (Lam d L N)) =
      (⟨0, y + z, a, b⟩ : Vcoup).eval (univ : Finset (Lam d L N)) := by
  simp only [Vcoup.eval, sum_add_distrib, ← smul_sum, sum_negLapPsi_mul, sum_mul_negLapPsibar,
    zero_div, zero_smul, add_zero, add_smul]
  rw [← two_smul ℂ (∑ x : Lam d L N, gradSq x), smul_smul, div_mul_cancel₀ _ two_ne_zero]

/-- **Summation by parts**, as elements of the even subalgebra (`VE`). -/
theorem VE_univ_sumParts (z y a b : ℂ) :
    VE (⟨z, y, a, b⟩ : Vcoup) (univ : Finset (Lam d L N)) =
      VE (⟨0, y + z, a, b⟩ : Vcoup) (univ : Finset (Lam d L N)) :=
  Subtype.ext (eval_univ_sumParts z y a b)

/-- **Summation by parts** for a general coupling `V`: `V(Λ) = V'(Λ)` with
`V' = (0, V.y + V.z, V.a, V.b)`. -/
theorem VE_univ_sumParts' (V : Vcoup) :
    VE V (univ : Finset (Lam d L N)) = VE (⟨0, V.y + V.z, V.a, V.b⟩ : Vcoup) univ :=
  VE_univ_sumParts V.z V.y V.a V.b

end

end Psi4
