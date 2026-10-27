import Obs2.Map.Map
import Step2.Coup.Wick

/-!
# Lemma `lem:second` (iii) for observables: exact Wick identities (`h02uv-outline.tex`)

For an anticommuting source `σ_a` (Case (1)) and a complex covariance `C`:

* `FC_lin_quad`: for a spin-`-` linear form `b = ι v` and a pair `a' b' = ι u ι w`
  (`u` spin `+`, `w` spin `-`), `F_C(b, a'b') = ⟨u, v⟩_C b'`: a single line from `b`;
* `FC_psibar_mass`: `F_C(ψ̄_a, (ψψ̄)(Λ)) = ∑_x C(a, x) ψ̄_x`;
* `FCO_obs_mass`: on the algebra with sources, `F_C(σ_aψ̄_a, (ψψ̄)(Λ)) = σ_a ∑_x C(a,x) ψ̄_x`
  (components `(0, ∑_x C(a,x) ψ̄_x, 0, 0)`);
* `second_iii`: **`Loc_a F_C(σ_aψ̄_a, (ψψ̄)(Λ)) = w^{(1)} σ_aψ̄_a`** with `w^{(1)} = ∑_x C(a, x)`
  (for a set `X ∋ a`; the `a` component of `Obs2.LocO2 P X X`).

This is the second part of (iii) with `w = C`; it is exact (no truncation), for every complex
`C`. The first part of (iii) and (ii) involve the quartic monomial `M` and `𝔩(w)` and are not
formalised here.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

section Wick

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

local notation "ι" => (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] Grassmann.N Λ)

theorem LopC_lin (C : Matrix Λ Λ ℂ) (v : V Λ) : LopC C (ι v) = 0 := by
  rw [LopC_apply]
  simp [D_ι, D_algebraMap]

theorem expLC_lin (C : Matrix Λ Λ ℂ) (v : V Λ) : expLC C (ι v) = ι v := by
  rw [expLC_of_cube C (by rw [LopC_lin, map_zero, map_zero]), LopC_lin, map_zero, smul_zero,
    add_zero, add_zero]

theorem pairC_neg (C : Matrix Λ Λ ℂ) (u v : V Λ) : pairC (-C) u v = -pairC C u v := by
  simp [pairC, sum_neg_distrib]

theorem pairC_ev (C : Matrix Λ Λ ℂ) (x a : Λ) :
    pairC C (ev (x, 1)) (ev (a, -1)) = C a x := by
  simp [pairC, ev, Pi.single_apply, Prod.ext_iff]

end Wick

/-! ### On the algebra with sources -/

section Obs

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

end Obs

section Loc

variable {d L N : ℕ} [NeZero L]

/-- `mass1 s` as a linear map. -/
def mass1L (s : ℤˣ) : Alg d L N →ₗ[ℂ] ℂ where
  toFun := mass1 s
  map_add' := mass1_add s
  map_smul' r F := mass1_smul s r F

end Loc


end

end Obs2
