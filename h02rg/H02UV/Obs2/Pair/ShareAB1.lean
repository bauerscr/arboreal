import Obs2.Flow.MuChainAB2
import Obs2.Flow.BlockFlow

/-!
# The per-region `r'` flow of the `ab` sector (the masses of the blocks of `a` and `b`)

The exact `r'` flow of `Obs2.MuChainAB` / `MuChainAB2` controls the total pair mass
`r'_k = ∑_Bm₂(V'_k(B)_{ab})`. If `a`, `b` lie in different `k`-blocks the blocks `B_{a,k}`,
`B_{b,k}` carry separate masses, and the block bounds need each of them. Here the whole derivation
of `MuChainAB.srcAB_eq2` is run for a **region** `X` (a union of blocks of the coarsest scale
involved), with every block sum restricted to the blocks of `X` — as `MuChain2.share2_flow_exact`
does for the `σ_a` sector:

* `rABX k V X = ∑_{B ∈ 𝓑_k(X)} m₂(V(B)_{ab})` (`rABX_univ`: `X = Λ` is `rAB2`;
  `rABX_blockSet`: for a `k`-block, the mass of that block);
* `SFO_ab_red`: without `σ_a` parts, `S^{(2)}(B)_{ab} = F_C(V'_{B,ab}, V'(Λ)_∅)` **per block**
  (sharp splitting);
* `mass2_LSO_sumX_ab`: `∑_{B ∈ 𝓑_j(X)} m₂(Loc S(B)_{ab}) = ∑_{B ∈ 𝓑_j(X)} m₂(S(B)_{ab}) − f(X)`
  for a `(j+1)`-polymer `X` (`loc^{ab}_{B_+,·}` keeps the mass inside `B_+`);
* **`rABX_next_red`**: `r'_{j+1}(X) = (1 − n_a)r'_j(X) − d_r(X) + 𝔡₂(X) − e_{ab}(X) + f(X)`
  (the region copy of `rAB_next_red`; the vertex factor `n_a` is the global one);
* **`wTadABX_step`**, `MuChainAB.wTadABX_unroll`, `wTadABX_zero_succ` (the region copies of the
  tadpole recursion);
* **`MuChainAB.srcABX_eq2`** and **`MuChainAB.rABX_flow`**: for an `n`-polymer `X` and
  `j₀ ≤ k < n`,
  `r'_{k+1}(X) = (1 − 𝔫^{(2)}_k)r'_k(X) − ∑_{i<k}(r̂'_i(X) − r'_k(X))tadInc2 i k − err_k(X)`,
  with the same `𝔫^{(2)}`, the same tadpole increments as the total flow, and the region error
  `errABX2` (activity, product mass of `𝒲`, Pauli and gradient terms, memory, all restricted to
  `X`).

So `k ↦ r'_k(X)` obeys the *same* relative recursion as the total `r'` (no `ℓ¹` coupling, the
leading factor is `1 − 𝔫^{(2)}_k`), and a Gronwall bound for it holds uniformly in `X`. Applied to
`X = B_{a,M}` (an `M`-polymer) at `k = M` this bounds the mass of the block of `a` at scale `M`;
at a merge the region simply contains both blocks.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

variable {d L N : ℕ} [NeZero L]

/-! ### The region functionals -/

section Defs

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N) (X : Finset (Lam d L N))

/-- The pair mass of the region `X`: `r_j(X) = ∑_{B ∈ 𝓑_j(X)} m₂(V(B)_{ab})`. -/
def rABX : ℂ := ∑ b ∈ blocks j X, mass2 (V b : SA .two (Lam d L N)).ab

/-- The `ab` tadpole functional of the region `X`. -/
def wTadABX (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ b ∈ blocks j X, mass2 (expLC Γ (W b : SA .two (Lam d L N)).ab)

/-- The `ab` product part of the region `X`. -/
def wProdABX (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ c' ∈ blocks (j + 1) X,
    mass2 (expLC Γ ((Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      WpO P j C V W b : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab)

/-- The tadpoles of the localised parts in the region `X`. -/
def pdefLSX (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ b ∈ blocks j X,
    (mass2 (expLC Γ (LSO P j C V W b : SA .two (Lam d L N)).ab) -
      mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab)

/-- The far term of the region `X` (its `(j+1)`-blocks not meeting `{a,b}`). -/
def farABmX : ℂ :=
  ∑ c' ∈ blocks (j + 1) X,
    if (blockSet (L := L) (N := N) (j + 1) c' ∩ P.pts).Nonempty then 0 else
      mass2 (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).ab

/-- The `m₂` Pauli defect of the region `X`. -/
def pdefM2X : ℂ := ∑ b ∈ blocks j X, pauliDef2 C (V b : SA .two (Lam d L N)).ab

/-- The activity part of `e_{ab}` in the region `X`. -/
def qABX : ℂ := ∑ b ∈ blocks j X, mass2 (expLC C (Q2O P j K b : SA .two (Lam d L N)).ab)

/-- `e_{ab}(X) = q(X) + G_j(X; C)`. -/
def eABX2 : ℂ := qABX P j C K X + wTadABX j W X C

/-- `V'(X) = ∑_{B ∈ 𝓑_j(X)} V'_B`. -/
def VprXO : OE .two (Lam d L N) := ∑ b ∈ blocks j X, VprO C V b

/-- `s_j(X) = ∑_{B ∈ 𝓑_j(X)} S^{(2)}(B)_{ab}`. -/
def sfABX : Alg d L N := ∑ b ∈ blocks j X, (SFO j C V b : SA .two (Lam d L N)).ab

/-- The one-loop tadpole of the region: `m₂(e^{ℒ_Γ}s_j(X)) − m₂(s_j(X))`. -/
def tauABX (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  mass2 (expLC Γ (sfABX j C V X)) - mass2 (sfABX j C V X)

/-- The gradient part of `V'(X)_{ab}`: `V'(X)_{ab} − ε − m₂(V'(X)_{ab})ψ̄_aψ_a`. -/
def dABX : Alg d L N :=
  (VprXO j C V X : SA .two (Lam d L N)).ab -
    (ε (VprXO j C V X : SA .two (Lam d L N)).ab • (1 : Alg d L N) +
      mass2 (VprXO j C V X : SA .two (Lam d L N)).ab • pbp P.a)

/-- The tadpole of the gradient part of the region. -/
def dTauABX (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  mass2 (expLC Γ (FC C (dABX P j C V X) (VprLO j C V : SA .two (Lam d L N)).e)) -
    mass2 (FC C (dABX P j C V X) (VprLO j C V : SA .two (Lam d L N)).e)

/-- The non-local part of the vertex correction of the region:
`m₂F_C(V'(X)_{ab}, V'(Λ)_∅) − r(X)n_a`. -/
def dRX2 : ℂ :=
  mass2 (FC C (VprXO j C V X : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e) -
    rABX j V X * nA2 P j C V

end Defs

/-- For a `k`-block `B`, the region mass is the mass of `B`. -/
theorem rABX_blockSet (k : ℕ) (V : OFam .two d L N) {c : Fin d → ℕ}
    (hne : (blockSet (L := L) (N := N) k c).Nonempty) :
    rABX k V (blockSet (L := L) (N := N) k c) = mass2 (V c : SA .two (Lam d L N)).ab := by
  rw [rABX, blocks_blockSet_self hne, sum_singleton]

/-! ### One step in a region -/

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N) (X : Finset (Lam d L N))

/-- **The sharp second-order `ab` part of a block without `σ_a` parts**:
`S^{(2)}(B)_{ab} = F_C(V'_{B,ab}, V'(Λ)_∅)`. -/
theorem SFO_ab_red (hVa : ∀ b, (V b : SA .two (Lam d L N)).a = 0) (b : Fin d → ℕ) :
    (SFO j C V b : SA .two (Lam d L N)).ab =
      FC C (VprO C V b : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e := by
  have ha : (VprO C V b : SA .two (Lam d L N)).a = 0 := by rw [VprO, EthO_a_eq, hVa b, map_zero]
  have hL := VprLO_a_zero j C V hVa
  have e : (SFO j C V b : SA .two (Lam d L N)).ab =
      (1 / 2 : ℂ) • (FCO C (VprO C V b) (VprLO j C V) : SA .two (Lam d L N)).ab +
        (SCorO j C V b : SA .two (Lam d L N)).ab := by
    rw [SFO, Subalgebra.coe_add, add_ab, Subalgebra.coe_smul, smul_ab]
  rw [e, SCorO_ab, FCO_ab, ha, hL]
  simp only [Case.s, one_smul, Case.tau_two, FC_zero_left, FC_zero_right, add_zero, smul_add,
    smul_sub]
  set x := FC C (VprO C V b : SA .two (Lam d L N)).e (VprLO j C V : SA .two (Lam d L N)).ab
  set y := FC C (VprO C V b : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e
  rw [show (1 / 2 : ℂ) • x + (1 / 2 : ℂ) • y + ((1 / 2 : ℂ) • y - (1 / 2 : ℂ) • x) =
    ((1 / 2 : ℂ) + 1 / 2) • y by rw [add_smul]; abel]
  norm_num

/-- `m₂(V'(X)_{ab}) = r(X) + 𝔡₂(X)`. -/
theorem mass2_VprXO_ab :
    mass2 (VprXO j C V X : SA .two (Lam d L N)).ab = rABX j V X + pdefM2X j C V X := by
  rw [VprXO, AddSubmonoidClass.coe_finsetSum, sum_ab, mass2_sum, rABX, pdefM2X,
    ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [VprO, (EthO_comp C (V b)).2.2, pauliDef2]
  ring

/-- **`s_j(X) = F_C(V'(X)_{ab}, V'(Λ)_∅)`** without `σ_a` parts. -/
theorem sfABX_red (hVa : ∀ b, (V b : SA .two (Lam d L N)).a = 0) :
    sfABX j C V X =
      FC C (VprXO j C V X : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e := by
  rw [sfABX, sum_congr rfl fun b _ => SFO_ab_red j C V hVa b, VprXO,
    AddSubmonoidClass.coe_finsetSum, sum_ab, Grassmann.FC_sum_left]

theorem FC_VprXO_ab_split (Y : Alg d L N) :
    FC C (VprXO j C V X : SA .two (Lam d L N)).ab Y =
      mass2 (VprXO j C V X : SA .two (Lam d L N)).ab • FC C (pbp P.a) Y +
        FC C (dABX P j C V X) Y := by
  have e : (VprXO j C V X : SA .two (Lam d L N)).ab =
      (ε (VprXO j C V X : SA .two (Lam d L N)).ab • (1 : Alg d L N) +
        mass2 (VprXO j C V X : SA .two (Lam d L N)).ab • pbp P.a) + dABX P j C V X := by
    rw [dABX, add_sub_cancel]
  conv_lhs => rw [e]
  rw [FC_add_left, FC_loc2]

/-- **The one-loop tadpole of the region**: `τ_j(X) = (r(X) + 𝔡₂(X))τ₂ + τ^D_j(X)`. -/
theorem tauABX_split (hVa : ∀ b, (V b : SA .two (Lam d L N)).a = 0)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    tauABX j C V X Γ = (rABX j V X + pdefM2X j C V X) *
        tau2 C Γ P.a (VprLO j C V : SA .two (Lam d L N)).e + dTauABX P j C V X Γ := by
  rw [tauABX, sfABX_red j C V X hVa, FC_VprXO_ab_split P j C V X, map_add, map_smul, mass2_add,
    mass2_add, mass2_smul, mass2_smul, mass2_VprXO_ab, tau2, dTauABX]
  ring

/-- **`d_r(X) = 𝔡₂(X)n_a + m₂F_C(D_j(X), V'_∅)`.** -/
theorem dRX2_split :
    dRX2 P j C V X = pdefM2X j C V X * nA2 P j C V +
      mass2 (FC C (dABX P j C V X) (VprLO j C V : SA .two (Lam d L N)).e) := by
  rw [dRX2, FC_VprXO_ab_split P j C V X, mass2_add, mass2_smul, mass2_VprXO_ab, nA2]
  ring

variable {X}

/-- `∑_{B ∈ 𝓑_j(X)} m₂(Loc S(B)_{ab}) = ∑_{B ∈ 𝓑_j(X)} m₂(S(B)_{ab}) − f(X)` for a
`(j+1)`-polymer `X`. -/
theorem mass2_LSO_sumX_ab (hX : IsPolymer (j + 1) X) :
    ∑ b ∈ blocks j X, mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab =
      ∑ b ∈ blocks j X, mass2 (SbO j C V W b : SA .two (Lam d L N)).ab -
        farABmX P j C V W X := by
  rw [← Step2.sum_blocks_succ hX, ← Step2.sum_blocks_succ hX, farABmX, ← sum_sub_distrib]
  refine sum_congr rfl fun c' _ => ?_
  have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab =
        mass2 (locABtXY P (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
          (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).ab) := by
    intro b hb
    show mass2 (locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
      (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab) = _
    rw [Bp_eq_of_mem hb]
  rw [sum_congr rfl e, mass2_sum_blocks_ab P (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c'))]
  have hS : mass2 (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') :
      SA .two (Lam d L N)).ab = ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        mass2 (SbO j C V W b : SA .two (Lam d L N)).ab := by
    rw [SXO, AddSubmonoidClass.coe_finsetSum, sum_ab, mass2_sum]
  split_ifs <;> rw [hS] <;> ring

variable (X)

theorem mass2_SbO_sumX_ab :
    ∑ b ∈ blocks j X, mass2 (SbO j C V W b : SA .two (Lam d L N)).ab =
      mass2 (sfABX j C V X) + wTadABX j W X C := by
  rw [sfABX, mass2_sum, wTadABX, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [SbO, Subalgebra.coe_add, add_ab, (EthO_comp C (W b)).2.2, mass2_add]

theorem mass2_sfABX_exp (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    ∑ b ∈ blocks j X, mass2 (expLC Γ (SFO j C V b : SA .two (Lam d L N)).ab) =
      mass2 (expLC Γ (sfABX j C V X)) := by
  rw [sfABX, map_sum, mass2_sum]

variable {X}

/-- **The `ab` tadpole recursion of one step in a region** (a `(j+1)`-polymer `X`). -/
theorem wTadABX_step (hX : IsPolymer (j + 1) X) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadABX (j + 1) (Wnext2O P j C V W) X Γ =
      tauABX j C V X Γ + (wTadABX j W X (Γ + C) - wTadABX j W X C) + farABmX P j C V W X -
        pdefLSX P j C V W X Γ + wProdABX P j C V W X Γ := by
  have h1 : ∀ c', mass2 (expLC Γ (Wnext2O P j C V W c' : SA .two (Lam d L N)).ab) =
      mass2 (expLC Γ ((Wnext2O P j C V W c' -
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), WpO P j C V W b :
          OE .two (Lam d L N)) : SA .two (Lam d L N)).ab) +
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        mass2 (expLC Γ (WpO P j C V W b : SA .two (Lam d L N)).ab) := by
    intro c'
    rw [AddSubgroupClass.coe_sub, sub_ab, map_sub, mass2_sub, AddSubmonoidClass.coe_finsetSum,
      sum_ab, map_sum, mass2_sum]
    ring
  have h2 : ∀ b, mass2 (expLC Γ (WpO P j C V W b : SA .two (Lam d L N)).ab) =
      mass2 (expLC Γ (SFO j C V b : SA .two (Lam d L N)).ab) +
        mass2 (expLC (Γ + C) (W b : SA .two (Lam d L N)).ab) -
        mass2 (expLC Γ (LSO P j C V W b : SA .two (Lam d L N)).ab) := by
    intro b
    have e : (WpO P j C V W b : SA .two (Lam d L N)).ab =
        (SFO j C V b : SA .two (Lam d L N)).ab + expLC C (W b : SA .two (Lam d L N)).ab -
          (LSO P j C V W b : SA .two (Lam d L N)).ab := by
      rw [WpO, AddSubgroupClass.coe_sub, sub_ab, SbO, Subalgebra.coe_add, add_ab,
        (EthO_comp C (W b)).2.2]
    rw [e, map_sub, map_add, mass2_sub, mass2_add, ← expLC_add]
  have hL := mass2_LSO_sumX_ab P j C V W hX
  have hSb := mass2_SbO_sumX_ab j C V W X
  have hW : wTadABX (j + 1) (Wnext2O P j C V W) X Γ =
      wProdABX P j C V W X Γ + ∑ b ∈ blocks j X,
        mass2 (expLC Γ (WpO P j C V W b : SA .two (Lam d L N)).ab) := by
    unfold wTadABX
    rw [sum_congr rfl fun c' _ => h1 c', sum_add_distrib, Step2.sum_blocks_succ hX]
    rfl
  rw [hW]
  simp only [h2, sum_sub_distrib, sum_add_distrib]
  rw [mass2_sfABX_exp]
  have hP : ∑ b ∈ blocks j X, mass2 (expLC Γ (LSO P j C V W b : SA .two (Lam d L N)).ab) =
      pdefLSX P j C V W X Γ + ∑ b ∈ blocks j X, mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab := by
    rw [pdefLSX, sum_sub_distrib]; ring
  rw [hP, hL, hSb]
  unfold tauABX wTadABX
  ring

/-- **The reduced `r` flow of a region** (a `(j+1)`-polymer `X`, no `σ_a` parts):
`r_{j+1}(X) = (1 − n_a)r_j(X) − d_r(X) + 𝔡₂(X) − e_{ab}(X) + f(X)`. -/
theorem rABX_next_red (hX : IsPolymer (j + 1) X) (hVa : ∀ b, (V b : SA .two (Lam d L N)).a = 0) :
    rABX (j + 1) (Vnext2O P j C V W K) X =
      (1 - nA2 P j C V) * rABX j V X - dRX2 P j C V X + pdefM2X j C V X -
        eABX2 P j C W K X + farABmX P j C V W X := by
  have e1 : rABX (j + 1) (Vnext2O P j C V W K) X =
      ∑ b ∈ blocks j X, mass2 (VpO P j C V W K b : SA .two (Lam d L N)).ab := by
    rw [rABX, ← Step2.sum_blocks_succ hX]
    refine sum_congr rfl fun c' _ => ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_ab, mass2_sum]
  have hb : ∀ b, mass2 (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      (mass2 (V b : SA .two (Lam d L N)).ab + pauliDef2 C (V b : SA .two (Lam d L N)).ab) -
        mass2 (expLC C (Q2O P j K b : SA .two (Lam d L N)).ab) -
        mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab := by
    intro b
    have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).ab = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
    have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).ab =
        (uVpO P j C V W K b : SA .two (Lam d L N)).ab -
          ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
            SA .two (Lam d L N)).ab - (upO P j C V W K b : SA .two (Lam d L N)).ab := rfl
    have hLS : (LSO P j C V W b : SA .two (Lam d L N)).ab =
        locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab := rfl
    rw [h1, halg, upO_ab_eq, sub_zero, mass2_sub, mass2_algebraMap, sub_zero, uVpO_ab, mass2_sub,
      mass2_sub, pauliDef2, hLS]
    ring
  rw [e1, sum_congr rfl fun b _ => hb b, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
    mass2_LSO_sumX_ab P j C V W hX, mass2_SbO_sumX_ab, sfABX_red j C V X hVa]
  unfold dRX2 eABX2 qABX
  unfold rABX pdefM2X
  ring

theorem tauABX_zero : tauABX j C V X 0 = 0 := by
  rw [tauABX, expLC_zero, sub_self]

theorem pdefLSX_zero : pdefLSX P j C V W X 0 = 0 := by
  unfold pdefLSX
  exact sum_eq_zero fun b _ => by rw [expLC_zero, sub_self]

/-- **The mass of the new `𝒲` in a region is its product part** (plus the far term). -/
theorem wTadABX_zero_succ (hX : IsPolymer (j + 1) X) :
    wTadABX (j + 1) (Wnext2O P j C V W) X 0 = farABmX P j C V W X + wProdABX P j C V W X 0 := by
  rw [wTadABX_step P j C V W hX, tauABX_zero, pdefLSX_zero, zero_add, zero_add]
  ring

end Step

/-! ### Along a chain -/

/-- The source of the reduced `r` flow of a region. -/
def srcABX (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (X : Finset (Lam d L N)) (k : ℕ) : ℂ :=
  (pdefM2X k (C k) (V k) X - dRX2 P k (C k) (V k) X) - eABX2 P k (C k) (W k) (K k) X +
    farABmX P k (C k) (V k) (W k) X

/-- The drift of a region: `∑_{i<k}(r̂_i(X) − r_k(X))tadInc2 i k`. -/
def driftABX (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (X : Finset (Lam d L N)) (j0 k : ℕ) : ℂ :=
  ∑ i ∈ range k, ((if j0 ≤ i then rABX i (V i) X else 0) - rABX k (V k) X) * tadInc2 P C V i k

/-- The memory terms of step `i` seen at step `k`, in a region. -/
def memABX (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (X : Finset (Lam d L N)) (i k : ℕ) : ℂ :=
  pdefM2X i (C i) (V i) X * tadInc2 P C V i k +
    (dTauABX P i (C i) (V i) X (C k + cumBetween C i k) -
      dTauABX P i (C i) (V i) X (cumBetween C i k)) -
    (pdefLSX P i (C i) (V i) (W i) X (C k + cumBetween C i k) -
      pdefLSX P i (C i) (V i) (W i) X (cumBetween C i k)) +
    (wProdABX P i (C i) (V i) (W i) X (C k + cumBetween C i k) -
      wProdABX P i (C i) (V i) (W i) X (cumBetween C i k))

/-- The mass of `𝒲_k` in a region along a chain from `j₀`. -/
def wMassABX (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (X : Finset (Lam d L N)) (j0 k : ℕ) : ℂ :=
  if j0 < k then farABmX P (k - 1) (C (k - 1)) (V (k - 1)) (W (k - 1)) X +
    wProdABX P (k - 1) (C (k - 1)) (V (k - 1)) (W (k - 1)) X 0 else 0

/-- **The error of the reduced `r` flow of a region** (the region copy of `errAB2`). -/
def errABX2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (X : Finset (Lam d L N))
    (j0 k : ℕ) : ℂ :=
  qABX P k (C k) (K k) X + wMassABX P C V W X j0 k -
    pdefM2X k (C k) (V k) X * (1 - nA2 P k (C k) (V k)) +
    mass2 (FC (C k) (dABX P k (C k) (V k) X) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e) -
    farABmX P k (C k) (V k) (W k) X + ∑ i ∈ Ico j0 k, memABX P C V W X i k

namespace MuChainAB

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {j0 n : ℕ} (H : MuChainAB P C V W j0 n)
include H

/-- **The unrolled `ab` tadpole functional of a region** (an `m`-polymer `X`). -/
theorem wTadABX_unroll {m : ℕ} (hm : j0 ≤ m) (hmn : m ≤ n) {X : Finset (Lam d L N)}
    (hX : IsPolymer m X) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadABX m (W m) X Γ = wTadABX m (W m) X 0 +
      ∑ i ∈ Ico j0 m, ((tauABX i (C i) (V i) X (Γ + cumBetween C i m) -
            tauABX i (C i) (V i) X (cumBetween C i m)) -
          (pdefLSX P i (C i) (V i) (W i) X (Γ + cumBetween C i m) -
            pdefLSX P i (C i) (V i) (W i) X (cumBetween C i m)) +
          (wProdABX P i (C i) (V i) (W i) X (Γ + cumBetween C i m) -
            wProdABX P i (C i) (V i) (W i) X (cumBetween C i m))) := by
  classical
  let G : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k ≤ m then wTadABX k (W k) X Γ else 0
  let T : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k < m then tauABX k (C k) (V k) X Γ + farABmX P k (C k) (V k) (W k) X -
      pdefLSX P k (C k) (V k) (W k) X Γ + wProdABX P k (C k) (V k) (W k) X Γ
    else -(G k (Γ + C k) - G k (C k))
  have hz : ∀ Γ, wTadABX j0 (W j0) X Γ = 0 := fun Γ => by
    unfold wTadABX
    exact sum_eq_zero fun b _ => by rw [H.hW0 b, map_zero, mass2_zero]
  have h0 : ∀ Γ, G j0 Γ = G j0 0 := fun Γ => by
    show (if j0 ≤ m then _ else _) = (if j0 ≤ m then _ else _)
    rw [if_pos hm, if_pos hm, hz, hz]
  have hs : ∀ k, j0 ≤ k → ∀ Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k)) := by
    intro k hk Γ
    by_cases hkm : k < m
    · simp only [G, T, if_pos hkm, if_pos (show k + 1 ≤ m by omega), if_pos hkm.le]
      have e : wTadABX (k + 1) (W (k + 1)) X Γ =
          wTadABX (k + 1) (Wnext2O P k (C k) (V k) (W k)) X Γ := by
        unfold wTadABX
        exact sum_congr rfl fun c' _ => by rw [H.hW k hk (by omega) c']
      rw [e, wTadABX_step P k (C k) (V k) (W k) (Step2.isPolymer_of_le hX (k + 1) (by omega))]
      ring
    · simp only [T, if_neg hkm]
      simp only [G, if_neg (show ¬ k + 1 ≤ m by omega)]
      ring
  have hu := tad_unroll_from G T C j0 h0 hs m hm Γ
  simp only [G, if_pos le_rfl] at hu
  rw [hu]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < m := (mem_Ico.1 hk).2
  simp only [T, if_pos hk']
  ring

/-- **`G_k(X; 0) = wMassABX_k(X)`** along the chain (a `k`-polymer `X`). -/
theorem wTadABX_zero_eq {k : ℕ} (hk : j0 ≤ k) (hkn : k ≤ n) {X : Finset (Lam d L N)}
    (hX : IsPolymer k X) : wTadABX k (W k) X 0 = wMassABX P C V W X j0 k := by
  unfold wMassABX
  split_ifs with h
  · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [show i + 1 - 1 = i by omega, ← wTadABX_zero_succ P i (C i) (V i) (W i) hX]
    unfold wTadABX
    exact sum_congr rfl fun c' _ => by rw [H.hW i (by omega) (by omega) c']
  · obtain rfl : k = j0 := by omega
    unfold wTadABX
    exact sum_eq_zero fun b _ => by rw [H.hW0 b, map_zero, mass2_zero]

/-- **The reduced `r` source of a region in the `𝔫^{(2)}` split** (exact; a `k`-polymer `X`). -/
theorem srcABX_eq2 (K : ℕ → OAct .two d L N) {k : ℕ} (hk : j0 ≤ k) (hkn : k ≤ n)
    {X : Finset (Lam d L N)} (hX : IsPolymer k X) :
    srcABX P C V W K X k + (∑ i ∈ range k, tadInc2 P C V i k) * rABX k (V k) X =
      -(driftABX P C V X j0 k + errABX2 P C V W K X j0 k) := by
  have hU := H.wTadABX_unroll hk hkn hX (C k)
  have hτ : ∀ i ∈ Ico j0 k, tauABX i (C i) (V i) X (C k + cumBetween C i k) -
      tauABX i (C i) (V i) X (cumBetween C i k) =
        (rABX i (V i) X + pdefM2X i (C i) (V i) X) * tadInc2 P C V i k +
          (dTauABX P i (C i) (V i) X (C k + cumBetween C i k) -
            dTauABX P i (C i) (V i) X (cumBetween C i k)) := by
    intro i hi
    have hi' := mem_Ico.1 hi
    rw [tauABX_split P i (C i) (V i) X (H.hVa i hi'.1 (by omega)),
      tauABX_split P i (C i) (V i) X (H.hVa i hi'.1 (by omega)), tadInc2, bulkE2]
    ring
  have hU' : wTadABX k (W k) X (C k) = wTadABX k (W k) X 0 +
      ∑ i ∈ Ico j0 k, (rABX i (V i) X * tadInc2 P C V i k + memABX P C V W X i k) := by
    rw [hU]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [hτ i hi, memABX]
    ring
  have hD : driftABX P C V X j0 k = ∑ i ∈ Ico j0 k, rABX i (V i) X * tadInc2 P C V i k -
      (∑ i ∈ range k, tadInc2 P C V i k) * rABX k (V k) X := by
    have e1 : ∑ i ∈ range k, (if j0 ≤ i then rABX i (V i) X else 0) * tadInc2 P C V i k =
        ∑ i ∈ Ico j0 k, rABX i (V i) X * tadInc2 P C V i k := by
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le j0) hk,
        sum_eq_zero fun i hi => by rw [if_neg (by have := (mem_Ico.1 hi).2; omega), zero_mul],
        zero_add]
      exact sum_congr rfl fun i hi => by rw [if_pos (mem_Ico.1 hi).1]
    rw [driftABX, ← e1, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  unfold srcABX errABX2
  rw [← H.wTadABX_zero_eq hk hkn hX, dRX2_split, eABX2, hU', hD, sum_add_distrib]
  ring

/-- **The exact relative recursion of the pair mass of a region** (an `n`-polymer `X`,
`j₀ ≤ k < n`, the `ab` parts of `V` follow the map):
`r_{k+1}(X) = (1 − 𝔫^{(2)}_k)r_k(X) − drift_k(X) − err_k(X)`. -/
theorem rABX_flow (K : ℕ → OAct .two d L N)
    (hV : ∀ k, j0 ≤ k → k < n → ∀ c', (V (k + 1) c' : SA .two (Lam d L N)).ab =
      (Vnext2O P k (C k) (V k) (W k) (K k) c' : SA .two (Lam d L N)).ab)
    {X : Finset (Lam d L N)} (hX : IsPolymer n X) {k : ℕ} (hk : j0 ≤ k) (hkn : k < n) :
    rABX (k + 1) (V (k + 1)) X =
      (1 - frakN2 P C V k) * rABX k (V k) X - driftABX P C V X j0 k -
        errABX2 P C V W K X j0 k := by
  have hX1 : IsPolymer (k + 1) X := Step2.isPolymer_of_le hX (k + 1) (by omega)
  have hX0 : IsPolymer k X := Step2.isPolymer_of_le hX k (by omega)
  have e : rABX (k + 1) (V (k + 1)) X =
      rABX (k + 1) (Vnext2O P k (C k) (V k) (W k) (K k)) X := by
    unfold rABX
    exact sum_congr rfl fun c' _ => by rw [hV k hk hkn c']
  have h1 := rABX_next_red P k (C k) (V k) (W k) (K k) hX1 (H.hVa k hk hkn.le)
  have h2 := H.srcABX_eq2 K hk hkn.le hX0
  have hn : nA2 P k (C k) (V k) = nuBar2 P C V k := rfl
  rw [e, h1]
  unfold srcABX at h2
  rw [frakN2, ← hn]
  linear_combination h2

end MuChainAB

end

end Obs2
