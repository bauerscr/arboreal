import Obs2.Flow.Wick2

/-!
# The total one-loop recursion of the single-point couplings

At the block `B ∋ a` the recursion of `Obs2/Flow/FlowMu.lean` has the second-order term
`m(S(B_+)_a)`, which is not symmetric in the two arguments of `F_C` (boundary terms of `B_+`
stay in `𝒲^{obs}` of the neighbouring blocks). Summing over **all** `j`-blocks, the localisation
cancels exactly between `V_{j+1}(B)` and `𝒲_{j+1}(B) = S(B) - Loc_{B_+,B} S(B_+)`:

`total_step`: for any linear `m` vanishing on constants (`m = mass1(-1)`, `mass2`),

  `∑_B [m(V_{j+1}(B)_a) - m(𝒲_{j+1}(B)_a)]
     = ∑_B m(V'_B,a) - ∑_B m((𝔼θ Q(B))_a) - m(F_C(V'(Λ)_a, V'(Λ)_∅)) - ∑_B m((𝔼θ 𝒲(B))_a)`,

where `F_C(V'(Λ)_a, V'(Λ)_∅) = ½ F_C(V'(Λ), V'(Λ))_a` is the **symmetric** one-loop term
(`FCO_self_a`). With the explicit Wick values (`Obs2/Flow/WickVcoup.lean`):

* Case (1) (`total_FC_one`): if `V'(Λ)_∅ = V_{κ'}(Λ) + r` and `V'(Λ)_a = β ψ̄_a`, the one-loop
  term is `m₁ = β ν' ∑_x C(a, x)`;
* Case (2) (`total_FC_two`): if `V'(Λ)_a = α + β ψ̄_aψ_a`, it is
  `m₂ = β (ν' (∑_x C(a,x) + ∑_x C(x,a)) - g' 𝔩_C(a))`.

So with `β = -μ` the total `μ + w`, `w = -∑_B m(𝒲^{obs}(B)_a)` (in the sign convention of
`total_step`), obeys `μ' + w' = μ(1 - ν'C^{(1)}) + w - …` (Case 1), resp.
`μ(1 + g'𝔩_C - ν'(C^{(1)} + C^{(1)ᵀ})) + …` (Case 2), with the remaining terms the activity
term `𝔼θQ` and the `𝒲` term `m((𝔼θ𝒲)_a)` (which contains the tadpole `-(ν'-ν)w^{(1)}` part of
`𝔫_j` and the second-order remainder).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

section Total

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

theorem SbO_sum :
    ∑ b ∈ blockIdx (L := L) (N := N) j, SbO j C V W b =
      (1 / 2 : ℂ) • FCO C (VprLO j C V) (VprLO j C V) +
        ∑ b ∈ blockIdx (L := L) (N := N) j, EthO C (W b) := by
  simp only [SbO, SFO, sum_add_distrib, sum_SCorO, add_zero, ← smul_sum, ← FCO_sum_left]
  rfl

/-- `F_C(X, X)_a = 2 F_C(X_a, X_∅)`. -/
theorem FCO_self_a {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ) (X : OE c Λ) :
    (FCO C X X : SA c Λ).a = (2 : ℂ) • FC C (X : SA c Λ).a (X : SA c Λ).e := by
  have h := FCO_cmp C true X X
  simp only [cmp_true] at h
  have he := (mem_OEv.1 X.2).1
  rw [h, Case.tau_of_even c he, FC_comm_even C he, two_smul]

/-- **The total one-loop recursion** (the localisation cancels). -/
theorem total_step (m : Alg d L N →ₗ[ℂ] ℂ) (hm : ∀ r : ℂ, m (algebraMap ℂ (Alg d L N) r) = 0) :
    ∑ b ∈ blockIdx (L := L) (N := N) j,
        (m (VpO P j C V W K b : SA c (Lam d L N)).a - m (WpO P j C V W b : SA c (Lam d L N)).a) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, m (VprO C V b : SA c (Lam d L N)).a -
        ∑ b ∈ blockIdx (L := L) (N := N) j, m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a -
        m (FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e) -
        ∑ b ∈ blockIdx (L := L) (N := N) j, m (EthO C (W b) : SA c (Lam d L N)).a := by
  have hb : ∀ b, m (VpO P j C V W K b : SA c (Lam d L N)).a -
      m (WpO P j C V W b : SA c (Lam d L N)).a =
      m (VprO C V b : SA c (Lam d L N)).a - m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a -
        m (SbO j C V W b : SA c (Lam d L N)).a := by
    intro b
    have hup : (upO P j C V W K b : SA c (Lam d L N)).a =
        algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA c (Lam d L N)).a) := by
      show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA c (Lam d L N)) = _
      rw [cmp_πobs]; rfl
    have halg : ((algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b) : OE c (Lam d L N)) :
        SA c (Lam d L N)).a = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
    have h1 : (VpO P j C V W K b : SA c (Lam d L N)).a =
        (uVpO P j C V W K b : SA c (Lam d L N)).a -
          ((algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b) : OE c (Lam d L N)) :
            SA c (Lam d L N)).a - (upO P j C V W K b : SA c (Lam d L N)).a := rfl
    have h2 : (uVpO P j C V W K b : SA c (Lam d L N)).a =
        (VprO C V b : SA c (Lam d L N)).a - (EthO C (Q2O P j K b) : SA c (Lam d L N)).a -
          (LSO P j C V W b : SA c (Lam d L N)).a := rfl
    have h3 : (WpO P j C V W b : SA c (Lam d L N)).a =
        (SbO j C V W b : SA c (Lam d L N)).a - (LSO P j C V W b : SA c (Lam d L N)).a := rfl
    rw [h1, h2, h3, halg, hup]
    simp only [map_sub, map_zero, hm, sub_zero]
    abel
  rw [sum_congr rfl fun b _ => hb b, sum_sub_distrib, sum_sub_distrib]
  have hS : ∑ b ∈ blockIdx (L := L) (N := N) j, m (SbO j C V W b : SA c (Lam d L N)).a =
      m (FC C (VprLO j C V : SA c (Lam d L N)).a (VprLO j C V : SA c (Lam d L N)).e) +
        ∑ b ∈ blockIdx (L := L) (N := N) j, m (EthO C (W b) : SA c (Lam d L N)).a := by
    rw [← map_sum, ← sum_a, ← AddSubmonoidClass.coe_finset_sum, SbO_sum, Subalgebra.coe_add,
      Subalgebra.coe_smul, add_a, smul_a, FCO_self_a, smul_smul, AddSubmonoidClass.coe_finset_sum,
      sum_a, map_add, map_sum]
    norm_num
  rw [hS]
  abel

end Total

/-! ### The one-loop term with the bulk polynomial -/

section Eval

variable (C : Matrix (Lam d L N) (Lam d L N) ℂ)

/-- **Case (1)**: `m₁ F_C(β ψ̄_a, V_{κ'}(Λ) + r) = β ν' ∑_x C(a, x)`. -/
theorem total_FC_one (a : Lam d L N) (κ : Step2.Coup) (r β : ℂ) :
    mass1 (-1) (FC C (β • psibar a) (Step2.Vcoup κ univ + r • (1 : Alg d L N))) =
      β * (κ.nu * ∑ x, C a x) := by
  rw [FC_smul_left, FC_add_right, FC_smul_right, FC_one_right, smul_zero, add_zero, mass1_smul,
    mass1_FC_psibar_Vcoup]

/-- **Case (2)**: `m₂ F_C(α + β ψ̄_aψ_a, V_{κ'}(Λ) + r) = β (ν'(∑_x C(a,x) + ∑_x C(x,a)) - g'𝔩_C(a))`. -/
theorem total_FC_two (a : Lam d L N) (κ : Step2.Coup) (r α β : ℂ) :
    mass2 (FC C (α • (1 : Alg d L N) + β • pbp a) (Step2.Vcoup κ univ + r • (1 : Alg d L N))) =
      β * (κ.nu * (∑ x, C a x + ∑ x, C x a) - κ.g * lfunC C a) := by
  rw [FC_add_left, Step2.FC_const_left, zero_add, FC_smul_left,
    FC_add_right, FC_smul_right, FC_one_right, smul_zero, add_zero, mass2_smul,
    mass2_FC_pbp_Vcoup]

end Eval

end

end Obs2
