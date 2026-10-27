import Obs.Ops

/-!
# Observable coupling constants (Definition `def:cVobs`, `e:VobsX`)

`Coup1 = (λ_a, λ_b, q_a, q_b, r_a, r_b) ∈ ℂ⁶` (Case (1)) and
`Coup2 = (λ_a, λ_b, γ_a, γ_b, q_a, q_b, η, r_a, r_b) ∈ ℂ⁹` (Case (2)); `Coup c` is the family.
For source points `a b : Λ` and `X ⊆ Λ`:

* Case (1) (`Coup1.VS`, `Coup1.uS`, `Coup1.evalS = uS + VS`):
  `(u^obs + V^obs)(X) = -λ_a σ_a ψ̄_a 1_{a∈X} - λ_b ψ_b σ̄_b 1_{b∈X} - σ_a σ̄_b q 1_{a,b∈X}
    + σ_a σ̄_b (r_a ψ̄_a ψ_a + r_b ψ̄_b ψ_b) 1_{a,b∈X}`, `q = q_a + q_b` (`Coup1.q`),
  with components `F_a = -λ_a ψ̄_a`, `F_b = λ_b ψ_b` (as `ψ_b σ̄_b = -σ̄_b ψ_b`),
  `F_ab = -q + r_a ψ̄_a ψ_a + r_b ψ̄_b ψ_b` (`Coup1.evalS_eq` checks the formula).
* Case (2) (`Coup2.VS`, `Coup2.uS`, `Coup2.evalS`):
  `V^obs = -σ_a λ_a ψ̄_a ψ_a - σ_b λ_b ψ̄_b ψ_b - σ_a σ_b (η/2)(ψ̄_a ψ_b + ψ̄_b ψ_a)
    + σ_a σ_b (r_a ψ̄_a ψ_a + r_b ψ̄_b ψ_b)`, `u^obs = -σ_a γ_a - σ_b γ_b - σ_a σ_b q`,
  `q = q_a + q_b` (`Coup2.q`), localised as in `e:VobsX`: the `σ_a` terms carry `1_{a∈X}`,
  the `σ_b` terms `1_{b∈X}` and the `σ_a σ_b` terms `1_{a∈X, b∈X}`.

**Deviation (split coupling constants).**  The text has a single `r` with the symmetric term
`σσ (r/2)(ψ̄_aψ_a + ψ̄_bψ_b)` and a single `q`.  We split `r` into `r_a, r_b` and `q` into
`q_a, q_b` (the text is `r_a = r_b = r/2`, `q = q_a + q_b`): the paper's symmetric form is not
preserved by `Loc^obs` on sets containing only one of `a, b` (for a small `X ∋ a`, `X ∌ b`,
`loc^{ab}_{X,B}` produces `u + r' ψ̄_aψ_a` in the block of `a` only).  On sets containing both
`a` and `b` only `q = q_a + q_b` enters; the split of `q` matters for the block-additive
evaluation `Obs.splitO` (`q_a`, `r_a` in the half at `a`, `q_b`, `r_b` in the half at `b`).

`evalO`, `VO`, `uO` are the same as even elements (`OE`).  They are observable
(`bulk = 0`), so `(u^obs + V^obs)(X)^3 = 0` (`evalO_pow_three`), they are `U(1)` invariant
(`isSymS_evalS`), and they only depend on `X ∩ {a, b}` (`evalS_congr`), with all components in
`𝒩(X ∩ {a, b})` (`evalS_mem_NX`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA

/-- Case (1) observable coupling constants `(λ_a, λ_b, q_a, q_b, r_a, r_b)`. -/
@[ext]
structure Coup1 where
  la : ℂ
  lb : ℂ
  qa : ℂ
  qb : ℂ
  ra : ℂ
  rb : ℂ

/-- Case (2) observable coupling constants `(λ_a, λ_b, γ_a, γ_b, q_a, q_b, η, r_a, r_b)`. -/
@[ext]
structure Coup2 where
  la : ℂ
  lb : ℂ
  ga : ℂ
  gb : ℂ
  qa : ℂ
  qb : ℂ
  eta : ℂ
  ra : ℂ
  rb : ℂ

/-- The total constant `q = q_a + q_b` of `u^obs` (Case (2)). -/
def Coup2.q (V : Coup2) : ℂ := V.qa + V.qb

/-- The observable coupling constants of Case `c`. -/
def Coup : Case → Type
  | .one => Coup1
  | .two => Coup2

variable {Λ : Type*} [DecidableEq Λ]

/-- `1_{x ∈ X}` as a complex number. -/
def ind (P : Prop) [Decidable P] : ℂ := if P then 1 else 0

@[simp] theorem ind_pos {P : Prop} [Decidable P] (h : P) : ind P = 1 := if_pos h
@[simp] theorem ind_neg {P : Prop} [Decidable P] (h : ¬P) : ind P = 0 := if_neg h

/-- `ψ̄_a ψ_a + ψ̄_b ψ_b`. -/
def nn (a b : Λ) : N Λ := psibar a * psi a + psibar b * psi b

/-- `r_a ψ̄_a ψ_a + r_b ψ̄_b ψ_b`. -/
def nr (ra rb : ℂ) (a b : Λ) : N Λ := ra • (psibar a * psi a) + rb • (psibar b * psi b)

@[simp] theorem nr_zero (a b : Λ) : nr 0 0 a b = 0 := by simp [nr]

/-- `ψ̄_a ψ_b + ψ̄_b ψ_a`. -/
def nx (a b : Λ) : N Λ := psibar a * psi b + psibar b * psi a

namespace Coup1

variable (V : Coup1) (a b : Λ) (X : Finset Λ)

/-- `V^obs(X)` (Case (1)). -/
def VS : SA .one Λ :=
  ⟨0, ind (a ∈ X) • (-V.la • psibar a), ind (b ∈ X) • (V.lb • psi b),
    ind (a ∈ X ∧ b ∈ X) • nr V.ra V.rb a b⟩

/-- `u^obs(X) = -σ_a σ̄_b q 1_{a,b∈X}` (Case (1)). -/
def uS : SA .one Λ := ⟨0, 0, 0, ind (a ∈ X ∧ b ∈ X) • algebraMap ℂ (N Λ) (-(V.qa + V.qb))⟩

/-- `(u^obs + V^obs)(X)` (Case (1), `e:VobsX`). -/
def evalS : SA .one Λ := V.uS a b X + V.VS a b X

@[simp] theorem evalS_e : (V.evalS a b X).e = 0 := by simp [evalS, uS, VS]
@[simp] theorem evalS_a : (V.evalS a b X).a = ind (a ∈ X) • (-V.la • psibar a) := by
  simp [evalS, uS, VS]
@[simp] theorem evalS_b : (V.evalS a b X).b = ind (b ∈ X) • (V.lb • psi b) := by
  simp [evalS, uS, VS]
@[simp] theorem evalS_ab : (V.evalS a b X).ab =
    ind (a ∈ X ∧ b ∈ X) • (algebraMap ℂ (N Λ) (-(V.qa + V.qb)) + nr V.ra V.rb a b) := by
  simp [evalS, uS, VS, smul_add]

end Coup1

namespace Coup2

variable (V : Coup2) (a b : Λ) (X : Finset Λ)

/-- `V^obs(X)` (Case (2)). -/
def VS : SA .two Λ :=
  ⟨0, ind (a ∈ X) • (-V.la • (psibar a * psi a)), ind (b ∈ X) • (-V.lb • (psibar b * psi b)),
    ind (a ∈ X ∧ b ∈ X) • (-(V.eta / 2) • nx a b + nr V.ra V.rb a b)⟩

/-- `u^obs(X) = -σ_a γ_a 1_{a∈X} - σ_b γ_b 1_{b∈X} - σ_a σ_b q 1_{a,b∈X}` (Case (2)). -/
def uS : SA .two Λ :=
  ⟨0, ind (a ∈ X) • algebraMap ℂ (N Λ) (-V.ga), ind (b ∈ X) • algebraMap ℂ (N Λ) (-V.gb),
    ind (a ∈ X ∧ b ∈ X) • algebraMap ℂ (N Λ) (-(V.qa + V.qb))⟩

/-- `(u^obs + V^obs)(X)` (Case (2), `e:VobsX`). -/
def evalS : SA .two Λ := V.uS a b X + V.VS a b X

@[simp] theorem evalS_e : (V.evalS a b X).e = 0 := by simp [evalS, uS, VS]
@[simp] theorem evalS_a : (V.evalS a b X).a =
    ind (a ∈ X) • (algebraMap ℂ (N Λ) (-V.ga) - V.la • (psibar a * psi a)) := by
  simp [evalS, uS, VS, smul_add, sub_eq_add_neg]
@[simp] theorem evalS_b : (V.evalS a b X).b =
    ind (b ∈ X) • (algebraMap ℂ (N Λ) (-V.gb) - V.lb • (psibar b * psi b)) := by
  simp [evalS, uS, VS, smul_add, sub_eq_add_neg]
@[simp] theorem evalS_ab : (V.evalS a b X).ab = ind (a ∈ X ∧ b ∈ X) •
    (algebraMap ℂ (N Λ) (-(V.qa + V.qb)) - (V.eta / 2) • nx a b + nr V.ra V.rb a b) := by
  simp only [evalS, uS, VS, add_ab]
  rw [← smul_add]; congr 1; simp only [neg_smul]; abel

end Coup2

/-! ### The family and even elements -/

/-- `(u^obs + V^obs)(X)` for the coupling constants of Case `c`. -/
def evalS : (c : Case) → Coup c → Λ → Λ → Finset Λ → SA c Λ
  | .one, V, a, b, X => Coup1.evalS V a b X
  | .two, V, a, b, X => Coup2.evalS V a b X

/-- `V^obs(X)`. -/
def VS : (c : Case) → Coup c → Λ → Λ → Finset Λ → SA c Λ
  | .one, V, a, b, X => Coup1.VS V a b X
  | .two, V, a, b, X => Coup2.VS V a b X

/-- `u^obs(X)`. -/
def uS : (c : Case) → Coup c → Λ → Λ → Finset Λ → SA c Λ
  | .one, V, a, b, X => Coup1.uS V a b X
  | .two, V, a, b, X => Coup2.uS V a b X

theorem evalS_eq_add (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    evalS c V a b X = uS c V a b X + VS c V a b X := by
  cases c <;> rfl

theorem isOdd_psibar' (x : Λ) : inv' (psibar x) = -psibar x := inv'_ι _
theorem isOdd_psi' (x : Λ) : inv' (psi x) = -psi x := inv'_ι _

theorem inv'_psibar_psi (x y : Λ) : inv' (psibar x * psi y) = psibar x * psi y := by
  rw [map_mul, isOdd_psibar', isOdd_psi', neg_mul_neg]

theorem inv'_nn (a b : Λ) : inv' (nn a b) = nn a b := by
  simp [nn, inv'_psibar_psi]

theorem inv'_nr (ra rb : ℂ) (a b : Λ) : inv' (nr ra rb a b) = nr ra rb a b := by
  simp [nr, inv'_psibar_psi, map_smul]

theorem inv'_nx (a b : Λ) : inv' (nx a b) = nx a b := by
  simp [nx, inv'_psibar_psi]

theorem mem_OEv_VS (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    VS c V a b X ∈ OEv c Λ := by
  cases c <;> refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [VS, Coup1.VS, Coup2.VS, isOdd_psibar', isOdd_psi', inv'_nx, inv'_nr,
      inv'_psibar_psi, map_smul]

theorem mem_OEv_uS (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    uS c V a b X ∈ OEv c Λ := by
  cases c <;> refine mem_OEv.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp [uS, Coup1.uS, Coup2.uS]

/-- `V^obs(X)` as an even element. -/
def VO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) : OE c Λ :=
  ⟨VS c V a b X, mem_OEv_VS c V a b X⟩

/-- `u^obs(X)` as an even element. -/
def uO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) : OE c Λ :=
  ⟨uS c V a b X, mem_OEv_uS c V a b X⟩

/-- `(u^obs + V^obs)(X)` as an even element. -/
def evalO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) : OE c Λ :=
  uO c V a b X + VO c V a b X

@[simp] theorem coe_evalO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    (evalO c V a b X : SA c Λ) = evalS c V a b X := (evalS_eq_add c V a b X).symm

@[simp] theorem coe_VO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    (VO c V a b X : SA c Λ) = VS c V a b X := rfl

@[simp] theorem coe_uO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    (uO c V a b X : SA c Λ) = uS c V a b X := rfl

theorem bulk_evalO (c : Case) (V : Coup c) (a b : Λ) (X : Finset Λ) :
    bulk (evalO c V a b X) = 0 := by
  refine Subtype.ext ?_
  rw [coe_bulk, coe_evalO]
  cases c
  · exact Coup1.evalS_e _ _ _ _
  · exact Coup2.evalS_e _ _ _ _

/-! ### `U(1)` invariance -/

theorem scal_psibar_psi (t : ℂ) (ht : t ≠ 0) (x y : Λ) :
    Step.scal Λ t (psibar x * psi y) = psibar x * psi y := by
  rw [map_mul, psibar, psi, Step.scal_ψ, Step.scal_ψ, if_neg Loc.units_ne.symm, if_pos rfl,
    smul_mul_smul_comm, inv_mul_cancel₀ ht, one_smul]

theorem scal_nn (a b : Λ) : Step.scal Λ 2 (nn a b) = nn a b := by
  simp [nn, scal_psibar_psi]

theorem scal_nx (a b : Λ) : Step.scal Λ 2 (nx a b) = nx a b := by
  simp [nx, scal_psibar_psi]

end

end Obs
