import Obs2.Flow.MuTad1
import Obs2.Flow.Wick2
import Obs2.Flow.VObs1

/-!
# The per-block masses of the observable coupling (Case (1))

With the pointed `loc^a` the `σ_a` coupling is spread over the blocks: `V_j(B)_a = c_j(B) ψ̄_a`
(`Obs2.MuHist.obsHist_hform`) with total `β_j = ∑_B c_j(B)` (`betaTot`). This file computes the
exact one-step recursion of the **shares** `c_j(B)`:

* `share_step` (any `LocMass` functional `m`): for a `(j+1)`-block `B_+`,
  `m(V_{j+1}(B_+)_a) = ∑_{B ⊆ B_+} [m(V'_B{}_a) - m((𝔼θQ(B))_a) - m(S(B)_a)]`.
  The localisation `Loc_{B_+,B} S(B_+)` moves mass only inside `B_+`, so the second-order term
  enters each `(j+1)`-block with its own `S(B)`'s; the activity term `Q(B)` spreads `K(X)` over
  the blocks of `X` (weights `|B|/|X|` for `a ∉ X`).
* `mass_SbO_a_one`: with `V(B)_a = c(B) ψ̄_a` and the sharp splitting `S^♯` of `Obs2.Map.Map`,
  `m₁(S^♯(B)_a) = c(B) ν̄ + m₁((𝔼θ𝒲(B))_a)`, `ν̄ = m₁ F_C(ψ̄_a, V'(Λ)_∅)`; also
  `ν(B) = m₁ F_C(V'_{B,∅}, ψ̄_a)` with `∑_B ν(B) = ν̄` (`sum_nuBlk`).
* `share_step_one`: the combination,
  `c_{j+1}(B_+) = ∑_{B ⊆ B_+} [c(B)(1 - ν̄) - m₁((𝔼θ𝒲(B))_a) - m₁((𝔼θQ(B))_a)]`:
  every share carries the full one-loop decay `1 - ν̄`; only `𝒲` and `Q` remain.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

/-- **`∑_{B ⊆ B_+} m(Loc_{B_+,B} S(B_+))_a = ∑_{B ⊆ B_+} m(S(B)_a)`** for every `(j+1)`-block. -/
theorem blk_LS (m : Alg d L N →ₗ[ℂ] ℂ) (hm : LocMass c P.a m) {c' : Fin d → ℕ}
    (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        m (LSO P j C V W b : SA c (Lam d L N)).a =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        m (SbO j C V W b : SA c (Lam d L N)).a := by
  have hne : (blockSet (L := L) (N := N) (j + 1) c').Nonempty := mem_blockIdx.1 hc'
  have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      m (LSO P j C V W b : SA c (Lam d L N)).a =
        m (locAp c P.a (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
          (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA c (Lam d L N)).a) := by
    intro b hb
    show m (locAp c P.a (Step2.Bp (L := L) (N := N) j b) (blockSet j b)
      (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)).a) = _
    rw [Bp_eq_of_mem hb]
  rw [sum_congr rfl e, hm.sum_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hne,
    SXO, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum]

/-- **The one-step recursion of the per-block masses** (any `LocMass` functional vanishing on
constants): `m(V_{j+1}(B_+)_a) = ∑_{B ⊆ B_+} [m(V'_B{}_a) - m((𝔼θQ(B))_a) - m(S(B)_a)]`. -/
theorem share_step (m : Alg d L N →ₗ[ℂ] ℂ) (hm0 : ∀ r : ℂ, m (algebraMap ℂ (Alg d L N) r) = 0)
    (hm : LocMass c P.a m) {c' : Fin d → ℕ} (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    m (Vnext2O P j C V W K c' : SA c (Lam d L N)).a =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        (m (VprO C V b : SA c (Lam d L N)).a - m (EthO C (Q2O P j K b) : SA c (Lam d L N)).a -
          m (SbO j C V W b : SA c (Lam d L N)).a) := by
  rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum]
  simp only [m_VpO_a P j C V W K m hm0, sum_sub_distrib]
  rw [blk_LS P j C V W m hm hc']

end Step

/-! ### Case (1): the half split of the one-loop term -/

section One

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .one d L N) (K : OAct .one d L N)

/-- The total one-loop coefficient `ν̄ = m₁ F_C(ψ̄_a, V'(Λ)_∅)`. -/
def nuTot : ℂ := mass1 (-1) (FC C (psibar P.a) (VprLO j C V : SA .one (Lam d L N)).e)

variable {P C V}

/-- With `V(B)_a = c(B) ψ̄_a`: `V'_B{}_a = c(B) ψ̄_a`. -/
theorem VprO_a_of_form {cs : (Fin d → ℕ) → ℂ}
    (hβ : ∀ b, (V b : SA .one (Lam d L N)).a = cs b • psibar P.a) (b : Fin d → ℕ) :
    (VprO C V b : SA .one (Lam d L N)).a = cs b • psibar P.a := by
  rw [VprO, EthO_a_eq, hβ b, map_smul, expLC_psibar]

/-- **The sharp split**: `m₁(S^♯(B)_a) = c(B) ν̄ + m₁((𝔼θ𝒲(B))_a)`: the whole one-loop term of the
`σ_a` component stays with the block carrying the share. -/
theorem mass_SbO_a_one {cs : (Fin d → ℕ) → ℂ}
    (hβ : ∀ b, (V b : SA .one (Lam d L N)).a = cs b • psibar P.a) (b : Fin d → ℕ) :
    mass1 (-1) (SbO j C V W b : SA .one (Lam d L N)).a =
      cs b * nuTot P j C V + mass1 (-1) (EthO C (W b) : SA .one (Lam d L N)).a := by
  have h := SFO_cmp j C V true b
  simp only [cmp_true] at h
  have hS : (SbO j C V W b : SA .one (Lam d L N)).a =
      (SFO j C V b : SA .one (Lam d L N)).a + (EthO C (W b) : SA .one (Lam d L N)).a := by
    rw [SbO, Subalgebra.coe_add, add_a]
  rw [hS, h, VprO_a_of_form hβ b, FC_smul_left, mass1_add, mass1_smul, nuTot]

/-- **The share recursion (Case (1), sharp splitting)**: for a `(j+1)`-block `B_+`,
`c_{j+1}(B_+) = ∑_{B ⊆ B_+} [c(B)(1 - ν̄) - m₁((𝔼θ𝒲(B))_a) - m₁((𝔼θQ(B))_a)]`. -/
theorem share_step_one {cs : (Fin d → ℕ) → ℂ}
    (hβ : ∀ b, (V b : SA .one (Lam d L N)).a = cs b • psibar P.a) {c' : Fin d → ℕ}
    (hc' : c' ∈ blockIdx (L := L) (N := N) (j + 1)) :
    mass1 (-1) (Vnext2O P j C V W K c' : SA .one (Lam d L N)).a =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        (cs b * (1 - nuTot P j C V) -
          mass1 (-1) (EthO C (W b) : SA .one (Lam d L N)).a -
          mass1 (-1) (EthO C (Q2O P j K b) : SA .one (Lam d L N)).a) := by
  have h := share_step P j C V W K (mass1L (-1)) (fun r => mass1_algebraMap _ r)
    (locMass_one P.a) hc'
  refine h.trans (sum_congr rfl fun b _ => ?_)
  show mass1 (-1) _ - mass1 (-1) _ - mass1 (-1) _ = _
  rw [mass_SbO_a_one j W hβ b, VprO_a_of_form hβ b, mass1_smul, mass1_psibar]
  ring

end One

end

end Obs2
