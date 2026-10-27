import Obs2.Flow.WickVcoup

/-!
# The one-loop identities on the algebra with sources

For the observable vertices `σ_aψ̄_a` (Case (1), anticommuting `σ_a`, `sigPsibar`) and
`σ_aψ̄_aψ_a` (Case (2), `sigPbp`) and a bulk element `V` (embedded by `emb`), the `a` component of
`F_C` is the bulk `F_C` of the `a` component (`FCO_a_obs_bulk`, `FCO_a_bulk_obs`, from
`Obs2.FCO_cmp`). With `V = V_κ(Λ)` (`VcE κ`) this gives the exact one-loop coefficients of the
`μ` recursion (`Obs2/Flow/FlowMu.lean`), for every complex covariance `C`:

* Case (1) (`mass1_FCO_sigPsibar_Vcoup`): `m₁ F_C(σ_aψ̄_a, V_κ(Λ))_a = ν ∑_x C(a, x)`;
* Case (2) (`mass2_FCO_sigPbp_Vcoup`):
  `m₂ F_C(σ_aψ̄_aψ_a, V_κ(Λ))_a = ν (∑_x C(a,x) + ∑_x C(x,a)) - g 𝔩_C(a)`;

and the same with the arguments of `F_C` exchanged (`*_swap`).

**Signs in the flow.** With `V^{obs}_a = -μ σ_a ψ̄_a` (Case 1) resp. `-μ σ_aψ̄_aψ_a`, the full
second-order term of the `μ` recursion contains `F_C(V'_a, V'_bulk(Λ))` (`= ½F_C(V'(Λ), V'(Λ))_a`,
the two orders), whose mass coefficient is `-μ ν' C^{(1)}` resp. `-μ (2ν' C^{(1)} - g 𝔩_C)` for a
symmetric `C` (`C^{(1)} = ∑_x C(a,x)`). Since `β_{j+1} = β_j - … - m(S)` with `β = -μ`, this is
`μ' = μ(1 - ν'C^{(1)}) + …` resp. `μ' = μ(1 + g 𝔩_C - 2ν'C^{(1)}) + …`: the `-𝔫`, `-2𝔫` and
`+g𝔩` of `lem:second`, with `ν' C^{(1)}` the current-scale part of `𝔫_j`.

**Per-block vs. total.** The second-order term of `Obs2.Map.Map` at the block `B ∋ a` is
`∑_{B' ⊆ B_+} ½F_C(V'_{B'}, V'(Λ))_a = ½F_C(V'_a, V'_bulk(Λ)) + ½F_C(V'_bulk(B_+), V'_a)`, which is
not symmetric: the part `½F_C(V'_bulk(Λ ∖ B_+), V'_a)` (`ν' ∑_{x ∉ B_+} C(a,x)/2` etc.) is not
localised into `V(B)_a` (`Loc` onto a `(j+1)`-block not containing `a` vanishes) but stays in
`𝒲^{obs}` of the neighbouring blocks and is re-localised at a later scale. The clean one-loop
identity therefore holds for the total `μ + ∑_B m(𝒲^{obs}(B)_a)`, whose second-order term is
`F_C(V'_a, V'_bulk(Λ))` exactly. (This total recursion is not formalised here.)
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

section Gen

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `F_C` is symmetric if the left argument is even. -/
theorem FC_comm_even (C : Matrix Λ Λ ℂ) {A : Grassmann.N Λ} (hA : inv' A = A)
    (B : Grassmann.N Λ) : FC C A B = FC C B A := by
  have hc : ∀ X : Grassmann.N Λ, inv' X = X → ∀ Y, X * Y = Y * X := fun X hX Y =>
    Grassmann.mul_comm_of_even hX Y
  rw [FC, FC, hc _ (expLC_even (-C) hA), hc _ hA]

end Gen

variable {d L N : ℕ} [NeZero L] (C : Matrix (Lam d L N) (Lam d L N) ℂ)

end

end Obs2
