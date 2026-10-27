import Obs2.Loc.Loc
import Obs2.Map.Coupling

/-!
# Reproduction properties of the barycentric two-point localisation (`lem:loc-obs2` (ii))

`Obs2.LocO2` uses, on the `ab` component, the barycentric operator `locABtXY` (`Obs2.Loc.Loc`,
`Obs2.Loc.LocABt`): `loc^{ab,t}_X F = ε(F) + M_{00} ψ̄_aψ_a + M_{10} δ̄ψ_a + M_{01} ψ̄_aδ + M_{11} δ̄δ
+ M_4 ψ̄_aψ_aδ̄δ`, with the barycentric weight `t` (`t(a) = 0`, `t(b) = 1`).

## Results
* `locABt_m4`: **`loc^{ab,t}_X (ψ̄_aψ_aψ̄_bψ_b) = ψ̄_aψ_aψ̄_bψ_b`** (for `a ∈ X`, `a ≠ b`). This was
  checked only by hand before. Proof: `ε`, `M_{00}` and the `M_{kl}` of length two vanish on a
  quartic monomial; in `M_4 = ∑ F_{x̄_0 x_1 x̄_2 x_3} t(x_0) t(x_1)` only `x = (b, b, a, a)`
  survives (`t(a) = 0`, and the coefficient vanishes off the four permutations of the support),
  with coefficient `+1` (an even permutation); finally `ψ̄_aψ_a δ̄ δ = ψ̄_aψ_aψ̄_bψ_b` by
  nilpotency.
* the reproduction of `1`, `ψ̄_uψ_v`, `ψ̄_aψ_aψ̄_bψ_b` by the operator with the base point switch,
  and of all observable couplings by `Loc_{X,X}`, are in `Obs2.Loc.LocRepro` (`LocO2_evalO`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step LocObs

/-! ### Coefficients of monomials -/

section Coeff

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `coeff (ψ^z) w = 0` if some entry of `w` does not occur in `z`. -/
theorem coeff_psiPow_of_not_mem {n : ℕ} (z w : Fin n → Sf Λ) {i : Fin n}
    (hi : ∀ k, w i ≠ z k) : coeff (psiPow z) w = 0 := by
  rw [coeff_psiPow]
  refine sum_eq_zero fun σ _ => ?_
  rw [if_neg, mul_zero]
  intro h
  exact hi (σ.symm i) (by rw [h]; simp)

/-- `coeff (ψ^z) z = 1` for injective `z`. -/
theorem coeff_psiPow_self {n : ℕ} (z : Fin n → Sf Λ) (hz : Function.Injective z) :
    coeff (psiPow z) z = 1 := by
  rw [coeff_psiPow, sum_eq_single 1]
  · simp
  · intro σ _ hσ
    rw [if_neg, mul_zero]
    intro h
    exact hσ (Equiv.ext fun i => by simpa using (hz (congrFun h i)).symm)
  · simp

theorem m4_eq_psiPow (a b : Λ) : m4 a b = psiPow ![(a, -1), (a, 1), (b, -1), (b, 1)] := by
  simp [m4, psiPow, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, psibar,
    psi, ψ, Matrix.vecTail, mul_assoc]

/-- The double transposition `(0 2)(1 3)` of `Fin 4`. -/
def sig4 : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3

theorem sign_sig4 : Equiv.Perm.sign sig4 = 1 := by
  rw [sig4, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  rfl

theorem perm4 (a b : Λ) : (![(b, -1), (b, 1), (a, -1), (a, 1)] : Fin 4 → Sf Λ) =
    ![(a, -1), (a, 1), (b, -1), (b, 1)] ∘ sig4 := by
  funext r
  fin_cases r <;> rfl

theorem m4_comm (a b : Λ) : m4 a b = m4 b a := by
  rw [m4_eq_psiPow, m4_eq_psiPow, perm4, psiPow_perm, sign_sig4]
  simp

theorem injective_m4 {a b : Λ} (hab : a ≠ b) :
    Function.Injective (![(a, -1), (a, 1), (b, -1), (b, 1)] : Fin 4 → Sf Λ) := by
  have hu : (-1 : ℤˣ) ≠ 1 := by decide
  intro i k h
  fin_cases i <;> fin_cases k <;> simp_all [Prod.ext_iff, Ne.symm hab]

end Coeff

/-! ### `loc^{ab,t}` on the quartic monomial -/

variable {d L N : ℕ} [NeZero L]

theorem eps_m4 (a b : Lam d L N) : ε (m4 a b) = 0 := by
  simp [m4, psibar, psi, ψ]

theorem mass2_m4 (a b : Lam d L N) : mass2 (m4 a b) = 0 := by
  simp only [mass2, m4_eq_psiPow, psiPow, coeff_ιMulti_of_ne _ _ (show (2 : ℕ) ≠ 4 by decide),
    sum_const_zero]

theorem Mw_m4_two (X : Finset (Lam d L N)) (a b : Lam d L N) (w : Fin 2 → Bool) :
    Mw X a b sg2 w (m4 a b) = 0 := by
  unfold Mw
  refine sum_eq_zero fun x _ => ?_
  rw [m4_eq_psiPow, psiPow, coeff_ιMulti_of_ne _ _ (by decide), zero_mul]

/-- `ψ̄_aψ_a δ̄ δ = ψ̄_aψ_aψ̄_bψ_b`. -/
theorem pbp_dbar_dlt (a b : Lam d L N) : pbp a * (dbar a b * dlt a b) = m4 a b := by
  have k : ∀ p q : Sf (Lam d L N), ψ p * (ψ q * ψ p) = 0 := by
    intro p q
    rw [ψ_anticomm q p, mul_neg, ← mul_assoc, ψ_mul_self, zero_mul, neg_zero]
  have e : pbp a * (dbar a b * dlt a b) =
      ψ (a, -1) * ψ (a, 1) * ψ (b, -1) * ψ (b, 1) -
        ψ (a, -1) * (ψ (a, 1) * (ψ (b, -1) * ψ (a, 1))) -
        ψ (a, -1) * ψ (a, 1) * ψ (a, -1) * ψ (b, 1) +
        ψ (a, -1) * ψ (a, 1) * ψ (a, -1) * ψ (a, 1) := by
    unfold pbp dbar dlt psibar psi; noncomm_ring
  have k1 : ψ (a, -1) * ψ (a, 1) * ψ (a, -1) = (0 : Alg d L N) := by
    rw [mul_assoc, k]
  rw [e, k, mul_zero, k1, zero_mul, zero_mul]
  simp only [sub_zero, add_zero, m4, psibar, psi, mul_assoc]

theorem Mw_m4_four {X : Finset (Lam d L N)} {a b : Lam d L N} (hab : a ≠ b) :
    Mw X a b sg4 ![true, true, false, false] (m4 a b) = 1 := by
  have ha0 := tW_a X a b
  have hb1 := tW_b X a b (eN2_ne_zero hab)
  have hu : (-1 : ℤˣ) ≠ 1 := by decide
  set z : Fin 4 → Sf (Lam d L N) := ![(a, -1), (a, 1), (b, -1), (b, 1)] with hz
  have hzi : Function.Injective z := injective_m4 hab
  unfold Mw
  rw [m4_eq_psiPow, sum_eq_single ![b, b, a, a]]
  · -- the surviving term
    have hperm : (fun r => ((![b, b, a, a] : Fin 4 → Lam d L N) r, sg4 r)) = z ∘ sig4 := by
      rw [hz, ← perm4]
      funext r
      fin_cases r <;> rfl
    rw [hperm, coeff_perm, coeff_psiPow_self z hzi, sign_sig4]
    simp [Fin.prod_univ_four, hb1]
  · intro x _ hx
    by_cases h0 : x 0 = a
    · simp [Fin.prod_univ_four, h0, ha0]
    by_cases h1 : x 1 = a
    · simp [Fin.prod_univ_four, h1, ha0]
    suffices hc : coeff (psiPow z) (fun r => (x r, sg4 r)) = 0 by rw [hc, zero_mul]
    by_cases hb0 : x 0 = b
    swap
    · refine coeff_psiPow_of_not_mem z _ (i := 0) fun k => ?_
      fin_cases k <;> simp [hz, sg4, Prod.ext_iff, h0, hb0, hu, hu.symm]
    by_cases hb1' : x 1 = b
    swap
    · refine coeff_psiPow_of_not_mem z _ (i := 1) fun k => ?_
      fin_cases k <;> simp [hz, sg4, Prod.ext_iff, h1, hb1', hu, hu.symm]
    by_cases h2 : x 2 = a
    · by_cases h3 : x 3 = a
      · exact absurd (funext fun r => by fin_cases r <;> simp [hb0, hb1', h2, h3]) hx
      by_cases h3b : x 3 = b
      · refine coeff_eq_zero_of_not_injective _ fun hinj => ?_
        have := hinj (a₁ := (1 : Fin 4)) (a₂ := 3) (by simp [sg4, hb1', h3b])
        exact absurd this (by decide)
      · refine coeff_psiPow_of_not_mem z _ (i := 3) fun k => ?_
        fin_cases k <;> simp [hz, sg4, Prod.ext_iff, h3, h3b, hu, hu.symm]
    by_cases h2b : x 2 = b
    · refine coeff_eq_zero_of_not_injective _ fun hinj => ?_
      have := hinj (a₁ := (0 : Fin 4)) (a₂ := 2) (by simp [sg4, hb0, h2b])
      exact absurd this (by decide)
    · refine coeff_psiPow_of_not_mem z _ (i := 2) fun k => ?_
      fin_cases k <;> simp [hz, sg4, Prod.ext_iff, h2, h2b, hu, hu.symm]
  · simp

/-- **`loc^{ab,t}` reproduces `ψ̄_aψ_aψ̄_bψ_b`** (for `a ∈ X`, `a ≠ b`): the coupling `χ` of
`V^{obs}` is in its image. -/
theorem locABt_m4 {X : Finset (Lam d L N)} {a b : Lam d L N} (ha : a ∈ X) (hab : a ≠ b) :
    locABt X a b (m4 a b) = m4 a b := by
  unfold locABt Dt
  rw [locEven_singleton_eq ha, eps_m4, mass2_m4, Mw_m4_two, Mw_m4_two, Mw_m4_two,
    Mw_m4_four hab, pbp_dbar_dlt]
  simp

end

end Obs2
