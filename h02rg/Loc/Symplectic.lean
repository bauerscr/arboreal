import Loc.AutGen

/-!
# The symplectic symmetry `ψ ↦ ψ̄`, `ψ̄ ↦ -ψ`

`Jsym` is the algebra automorphism with `J ψ_x = ψ̄_x`, `J ψ̄_x = -ψ_x`.  The `ℍ^{0|2}` model is
invariant under it.  It swaps the roles of `ψ` and `ψ̄` in the monomial basis (`swapM`), and the
localisation commutes with it (`LocXY_J`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- `J` on the generators. -/
def JV : V (Lam d L N) →ₗ[ℂ] V (Lam d L N) where
  toFun v a := if a.2 = -1 then v (a.1, 1) else -v (a.1, -1)
  map_add' v w := by ext a; by_cases h : a.2 = -1 <;> simp [h]; ring
  map_smul' c v := by ext a; by_cases h : a.2 = -1 <;> simp [h]

/-- The symplectic map `J ψ_x = ψ̄_x`, `J ψ̄_x = -ψ_x`. -/
def Jsym : Alg d L N →ₐ[ℂ] Alg d L N := ExteriorAlgebra.map JV

theorem units_ne : (1 : ℤˣ) ≠ -1 := by decide

theorem Jsym_psi (x : Lam d L N) : Jsym (psi x) = psibar x := by
  rw [Jsym, psi, ψ, ExteriorAlgebra.map_apply_ι, psibar, ψ]
  congr 1
  ext ⟨y, τ⟩
  rcases Int.units_eq_one_or τ with rfl | rfl <;>
    simp [JV, ev, Pi.single_apply, Prod.ext_iff, units_ne.symm]

theorem Jsym_psibar (x : Lam d L N) : Jsym (psibar x) = -psi x := by
  rw [Jsym, psibar, ψ, ExteriorAlgebra.map_apply_ι, psi, ψ, ← map_neg]
  congr 1
  ext ⟨y, τ⟩
  rcases Int.units_eq_one_or τ with rfl | rfl <;>
    simp [JV, ev, Pi.single_apply, Prod.ext_iff, units_ne.symm]

theorem coord_JV_plus (x : Lam d L N) : coord (x, 1) ∘ₗ JV = -coord (x, -1) := by
  ext v; simp [JV]

theorem coord_JV_minus (x : Lam d L N) : coord (x, -1) ∘ₗ JV = coord (x, 1) := by
  ext v; simp [JV]

theorem cf2_Jsym (F : Alg d L N) (x y : Lam d L N) : cf2 (Jsym F) x y = cf2 F y x := by
  rw [cf2, coeff, Dseq, Jsym, contr_map, algebraMapInv_map, cf2, coeff_two]
  simp only [contr_succ, contr_zero, LinearMap.id_apply, Fin.tail, Matrix.cons_val_zero,
    Matrix.cons_val_succ, coord_JV_plus, coord_JV_minus, map_neg, LinearMap.neg_apply]
  change -ε (D (y, 1) (D (x, -1) F)) = ε (D (x, -1) (D (y, 1) F))
  rw [D_comm (x, -1), map_neg]

/-- `J` on the monomial basis: exchange the roles of `ψ` and `ψ̄`. -/
def swapM : Mono d → Mono d
  | .c => .c
  | .a1 k => .b1 k
  | .b1 k => .a1 k
  | .a2 s => .b2 s
  | .b2 s => .a2 s
  | .m2 k l => .m2 l k

theorem swapM_swapM (M : Mono d) : swapM (swapM M) = M := by cases M <;> rfl

/-- `swapM` as an equivalence. -/
def swapEquiv : Mono d ≃ Mono d := ⟨swapM, swapM, swapM_swapM, swapM_swapM⟩

theorem Qpoly_swapM (β : Mono d) (u v : Fin d → ℝ) : Qpoly (swapM β) u v = Qpoly β v u := by
  cases β with
  | m2 k l => simp [swapM, Qpoly, mul_comm]
  | _ => rfl

theorem mu_Jsym (b : Lam d L N) (β : Mono d) (F : Alg d L N) :
    mu b β (Jsym F) = mu b (swapM β) F := by
  simp only [mu, cf2_Jsym, Qpoly_swapM]
  rw [Finset.sum_comm]

theorem Jsym_psi_psibar (u v : Lam d L N) : Jsym (psi u * psibar v) = psi v * psibar u := by
  rw [map_mul, Jsym_psi, Jsym_psibar, mul_neg, psibar, psi, ψ, ψ, ι_anticomm (ev (u, -1)), neg_neg]

theorem flatMap_single {α β : Type*} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp [*]

theorem specList_swap (M : Mono d) (y : Lam d L N) :
    specList ((stencil M).map fun p => (p.1, p.2.2, p.2.1)) y = specList (stencil (swapM M)) y := by
  cases M with
  | c => simp [specList, stencil, tens, id1, swapM]
  | a1 k => simp [specList, stencil, tens, id1, dpt, swapM]
  | b1 k => simp [specList, stencil, tens, id1, dpt, swapM]
  | a2 s => simp [specList, stencil, tens, id1, swapM, List.map_flatMap, flatMap_single,
      Function.comp_def]
  | b2 s => simp [specList, stencil, tens, id1, swapM, List.map_flatMap, flatMap_single,
      Function.comp_def]
  | m2 k l =>
    rcases eq_or_ne k l with rfl | hkl
    · simp [specList, stencil, tens, fw, sc, swapM]; abel
    · simp [specList, stencil, tens, dpt, swapM, hkl, Ne.symm hkl]; abel

theorem Jsym_monoAt (M : Mono d) (x : Lam d L N) : Jsym (monoAt M x) = monoAt (swapM M) x := by
  rw [monoAt_eq_specList, monoAt_eq_specList, ← specList_swap, specList, specList, map_list_sum,
    List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, map_smul, Jsym_psi_psibar]

theorem Jsym_monoSet (M : Mono d) (Z : Finset (Lam d L N)) :
    Jsym (monoSet M Z) = monoSet (swapM M) Z := by
  rw [monoSet, map_sum, monoSet]; simp [Jsym_monoAt]

theorem Jsym_sum_monoSet (c : Mono d → ℂ) (Z : Finset (Lam d L N)) :
    Jsym (∑ M, c M • monoSet M Z) = ∑ M, c (swapM M) • monoSet M Z := by
  rw [map_sum]
  simp only [map_smul, Jsym_monoSet]
  exact Fintype.sum_equiv swapEquiv _ _ fun M => by simp [swapEquiv, swapM_swapM]

theorem ε_Jsym (F : Alg d L N) : ε (Jsym F) = ε F := algebraMapInv_map _ F

/-- The coefficients are unique on a patch. -/
theorem coef_unique {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) {c c' : Mono d → ℂ}
    (h : ∀ β, mu (base X) β (∑ M, c M • monoSet M X) = mu (base X) β (∑ M, c' M • monoSet M X)) :
    c = c' := by
  have hz : (c - c') ᵥ* Amat X = 0 := by
    funext β
    have := h β
    rw [mu_monoSet_vecMul, mu_monoSet_vecMul] at this
    simp only [Pi.sub_apply, vecMul, dotProduct, Amat, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    exact sub_eq_zero.2 this
  have := (vecMul_injective_iff_isUnit.2 (Amat_isUnit hX hne))
    (show (c - c') ᵥ* Amat X = 0 ᵥ* Amat X by rw [hz, zero_vecMul])
  exact sub_eq_zero.1 this

theorem locCoef_Jsym {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (F : Alg d L N) :
    locCoef X (Jsym F) = fun M => locCoef X F (swapM M) := by
  refine coef_unique hX hne fun β => ?_
  have h1 : ∀ (β : Mono d) (G : Alg d L N),
      mu (base X) β (∑ M, locCoef X G M • monoSet M X) = mu (base X) β G := by
    intro β G
    have := mu_LocX hX hne G β
    rw [LocX, LocXY, mu_add, mu_smul, mu_one, mul_zero, zero_add] at this
    exact this
  rw [h1, ← Jsym_sum_monoSet]
  simp only [mu_Jsym]
  rw [h1]

/-- `Loc_{X,Y}` commutes with the symplectic symmetry. -/
theorem LocXY_Jsym {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    (Y : Finset (Lam d L N)) (F : Alg d L N) : LocXY X Y (Jsym F) = Jsym (LocXY X Y F) := by
  rw [LocXY, LocXY, map_add, map_smul, map_one, Jsym_sum_monoSet, locCoef_Jsym hX hne, ε_Jsym]

end

end Loc
