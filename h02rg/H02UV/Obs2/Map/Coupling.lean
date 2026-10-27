import Obs2.Loc.Loc

/-!
# Observable coupling constants in `d = 2` (`h02uv-outline.tex`, Section `sec:obs-flow`)

In `d = 2` every source monomial times a derivative-free polynomial in the fields at `a, b` is
marginal, so the observable couplings of `def:cVobs` acquire a coupling `χ` of the quartic
monomial `ψ̄_aψ_aψ̄_bψ_b` (`Obs2.m4`):
* Case (1): `V^{obs} = -μ_a σ_aψ̄_a - μ_b ψ_bσ̄_b + σ_aσ̄_b (½r(ψ̄_aψ_a + ψ̄_bψ_b) + χ ψ̄_aψ_aψ̄_bψ_b)`,
  `u^{obs} = -σ_aσ̄_b q`;
* Case (2): `V^{obs} = -μ_a σ_aψ̄_aψ_a - μ_b σ_bψ̄_bψ_b - σ_aσ_b ½η(ψ̄_aψ_b + ψ̄_bψ_a)
  + σ_aσ_b (½r(ψ̄_aψ_a + ψ̄_bψ_b) + χ ψ̄_aψ_aψ̄_bψ_b)`,
  `u^{obs} = -σ_aγ_a - σ_bγ_b - σ_aσ_b q`;
localised as in `e:VobsX`: the `σ_a` terms carry `1_{a ∈ X}`, the `σ_b` terms `1_{b ∈ X}`, the
`σ_aσ_b` terms `1_{a, b ∈ X}`.

`OCoup c` are the coupling constants (`OCoup1 = (μ_a, μ_b, q, r, χ)`,
`OCoup2 = (μ_a, μ_b, γ_a, γ_b, q, η, r, χ)`), `evalS`/`evalO` the evaluation `(u^{obs} + V^{obs})(X)`
(components as in `Obs.Coupling`: `F_a = -μ_aψ̄_a`, `F_b = μ_bψ_b` in Case (1), since
`ψ_bσ̄_b = -σ̄_bψ_b`). The evaluation is observable (`bulk_evalO`), so its cube vanishes.

The flow itself (`Obs2.Flow.Hist`) carries `V^{obs}` as a block family; the localisation (`Obs2.Loc.Loc`)
produces the block-additive (split) form of these polynomials, with `q, r, χ` split between the
blocks of `a` and `b` (cf. the deviation in `Obs.Coupling`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA

/-- Case (1) observable couplings `(μ_a, μ_b, q, r, χ)`. -/
@[ext]
structure OCoup1 where
  mua : ℂ
  mub : ℂ
  q : ℂ
  r : ℂ
  chi : ℂ

/-- Case (2) observable couplings `(μ_a, μ_b, γ_a, γ_b, q, η, r, χ)`. -/
@[ext]
structure OCoup2 where
  mua : ℂ
  mub : ℂ
  ga : ℂ
  gb : ℂ
  q : ℂ
  eta : ℂ
  r : ℂ
  chi : ℂ

/-- The observable couplings of Case `c`. -/
def OCoup : Obs.Case → Type
  | .one => OCoup1
  | .two => OCoup2

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

namespace OCoup1

variable (V : OCoup1) (a b : Λ) (X : Finset Λ)

/-- `(u^{obs} + V^{obs})(X)` (Case (1)). -/
def evalS : SA .one Λ :=
  ⟨0, ind (a ∈ X) • (-V.mua • psibar a), ind (b ∈ X) • (V.mub • psi b),
    ind (a ∈ X ∧ b ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-V.q) + (V.r / 2) • nn a b + V.chi • m4 a b)⟩

theorem mem_OEv : V.evalS a b X ∈ OEv .one Λ := by
  refine Obs.mem_OEv.2 ⟨by simp [evalS], ?_, ?_, ?_⟩
  · simp [evalS, map_smul, isOdd_psibar']
  · simp [evalS, map_smul, isOdd_psi']
  · simp [evalS, map_add, map_smul, inv'_nn, inv'_m4]

end OCoup1

namespace OCoup2

variable (V : OCoup2) (a b : Λ) (X : Finset Λ)

/-- `(u^{obs} + V^{obs})(X)` (Case (2)). -/
def evalS : SA .two Λ :=
  ⟨0, ind (a ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-V.ga) - V.mua • (psibar a * psi a)),
    ind (b ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-V.gb) - V.mub • (psibar b * psi b)),
    ind (a ∈ X ∧ b ∈ X) • (algebraMap ℂ (Grassmann.N Λ) (-V.q) - (V.eta / 2) • nx a b +
      (V.r / 2) • nn a b + V.chi • m4 a b)⟩

theorem mem_OEv : V.evalS a b X ∈ OEv .two Λ := by
  refine Obs.mem_OEv.2 ⟨by simp [evalS], ?_, ?_, ?_⟩
  · simp [evalS, map_smul, map_sub, inv'_psibar_psi]
  · simp [evalS, map_smul, map_sub, inv'_psibar_psi]
  · simp [evalS, map_add, map_sub, map_smul, inv'_nn, inv'_nx, inv'_m4]

end OCoup2

/-- `(u^{obs} + V^{obs})(X)` for the couplings of Case `c`. -/
def evalS : (c : Obs.Case) → OCoup c → Λ → Λ → Finset Λ → SA c Λ
  | .one, V, a, b, X => OCoup1.evalS V a b X
  | .two, V, a, b, X => OCoup2.evalS V a b X

theorem evalS_mem (c : Obs.Case) (V : OCoup c) (a b : Λ) (X : Finset Λ) :
    evalS c V a b X ∈ OEv c Λ := by
  cases c
  · exact OCoup1.mem_OEv V a b X
  · exact OCoup2.mem_OEv V a b X

/-- **`(u^{obs} + V^{obs})(X)`** as an even element with sources. -/
def evalO (c : Obs.Case) (V : OCoup c) (a b : Λ) (X : Finset Λ) : OE c Λ :=
  ⟨evalS c V a b X, evalS_mem c V a b X⟩

@[simp] theorem evalS_e (c : Obs.Case) (V : OCoup c) (a b : Λ) (X : Finset Λ) :
    (evalS c V a b X).e = 0 := by
  cases c <;> rfl

theorem bulk_evalO (c : Obs.Case) (V : OCoup c) (a b : Λ) (X : Finset Λ) :
    bulk (evalO c V a b X) = 0 :=
  Subtype.ext (evalS_e c V a b X)

/-- The block family `B ↦ (u^{obs} + V^{obs})(B)` at scale `j`. -/
def evalFam {d L N : ℕ} [NeZero L] (c : Obs.Case) (V : OCoup c) (a b : Loc.Lam d L N) (j : ℕ) :
    (Fin d → ℕ) → OE c (Loc.Lam d L N) :=
  fun p => evalO c V a b (Loc.blockSet (L := L) (N := N) j p)

end

end Obs2
