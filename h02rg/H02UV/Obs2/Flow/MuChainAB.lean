import Obs2.Pair.PairRed

/-!
# The `σ_aσ_b` analogue of `MuChain2`: the exact `r` flow in the `𝔫^{(2)}` split

Case (2), the `σ_aσ_b` sector with the marginal pair coupling `r_k = ∑_Bm₂(V_k(B)_{ab})`
(`rAB2`). Along a chain without one-point parts (`V_a = V_b = 0`) the one-step `r` flow
(`rAB_next_red`) reads `r_{k+1} = (1 - n_{a,k})r_k + σ_k`, `σ_k = 𝔡₂ - d_r - e_{ab} + f`
(`srcAB`, the source `srcR` of `Spin2/Pair/PairRed3`). Here `σ_k` is unrolled in the `𝒲` history as
`MuChain2.share2_flow_exact` does for `β_a`:

* `wTadAB k W Γ = ∑_Bm₂(e^{ℒ_Γ}W(B)_{ab})`, the `ab` tadpole functional; **`wTadAB_step`**:
  `wTadAB_{j+1}(Γ) = τ^{ab}_j(Γ) + (wTadAB_j(Γ + C_j) - wTadAB_j(C_j)) + f_j - 𝔭_j(Γ) + P_j(Γ)`
  with `τ^{ab}_j(Γ) = m₂(e^{ℒ_Γ}s_j) - m₂(s_j)`, `s_j = (∑_BS^{(2)}(B))_{ab}` (`sfAB`),
  the far term `f_j = farABm`, the tadpoles of the localised parts `𝔭_j(Γ)` (`pdefLS`; these are
  Pauli defects: `m₂∘e^{ℒ_Γ}` and `m₂` differ on `loc^{ab}` only through `ψ̄_aψ_aδ̄δ`), and the
  product part `P_j(Γ)` (`wProdAB`).
* `tad_unroll_from`: `tad_unroll` started at `j₀` (the history of the reduced state starts at
  `j_x` with `𝒲' = 0`); `MuChainAB.wTadAB_unroll`.
* Without one-point parts `s_j = F_C(V'(Λ)_{ab}, V'(Λ)_∅)` (`sfAB_red`). Splitting
  `V'(Λ)_{ab} = ε + m₂(V'(Λ)_{ab})ψ̄_aψ_a + D_j` (`dAB`; `D_j` collects the gradient monomials
  `δ̄ψ_a, ψ̄_aδ, δ̄δ, ψ̄_aψ_aδ̄δ` of `loc^{ab}`, which have no `m₂`), with
  `m₂(V'(Λ)_{ab}) = r_j + 𝔡₂_j` (`mass2_VprLO_ab`):
  `τ^{ab}_j(Γ) = (r_j + 𝔡₂_j)τ₂(C_j, Γ) + τ^D_j(Γ)` (`tauAB_split`) and
  `d_r = 𝔡₂n_a + m₂F_C(D_j, V'_∅)` (`dR2_split`).
* **`MuChainAB.srcAB_eq`**: `σ_k + (𝔫^{(2)}_k - n_{a,k})r_k = -(drift_k + err_k)` with
  `drift_k = ∑_{i<k}(r̂_i - r_k)tadInc2 i k` (`r̂_i = r_i` for `i ≥ j₀`, `0` below; `driftAB`)
  and `err_k` (`errAB`) = activity `+ wTadAB_k(0) - 𝔡₂_k(1 - n_{a,k}) + m₂F_C(D_k, V'_∅) - f_k
  + ∑_{j₀≤i<k}(𝔡₂_i tadInc2 i k + ΔτD_i - Δ𝔭_i + ΔP_i)`. This is the exact `ab` analogue of
  `share2_flow_exact` (`err2 = muQX2 + muDriftX2 + G(0) + muProdIncX2`), with the extra Pauli/gradient
  terms `𝔡₂`, `D`, `𝔭` of the pair sector.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

variable {d L N : ℕ} [NeZero L]

/-- **Unrolling the tadpole recursion from `j₀`.** -/
theorem tad_unroll_from {M : Type*} [AddCommMonoid M] (G T : ℕ → M → ℂ) (C : ℕ → M) (j0 : ℕ)
    (h0 : ∀ Γ, G j0 Γ = G j0 0)
    (hs : ∀ k, j0 ≤ k → ∀ Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k))) :
    ∀ j, j0 ≤ j → ∀ Γ, G j Γ = G j 0 +
      ∑ k ∈ Ico j0 j, (T k (Γ + cumBetween C k j) - T k (cumBetween C k j)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro Γ; rw [h0 Γ, Ico_self, sum_empty, add_zero]
  | succ j hj ih =>
    intro Γ
    have hG0 : G (j + 1) 0 = T j 0 := by rw [hs j hj 0, zero_add, sub_self, add_zero]
    rw [hs j hj Γ, hG0, ih (Γ + C j), ih (C j), sum_Ico_succ_top hj, cumBetween_self_succ,
      add_zero]
    have e : ∀ k ∈ Ico j0 j, T k (Γ + cumBetween C k (j + 1)) - T k (cumBetween C k (j + 1)) =
        T k (Γ + C j + cumBetween C k j) - T k (C j + cumBetween C k j) := by
      intro k hk
      rw [cumBetween_succ C (mem_Ico.1 hk).2, add_comm (cumBetween C k j) (C j), add_assoc]
    rw [sum_congr rfl e]
    have hsum : ∑ k ∈ Ico j0 j, (T k (Γ + C j + cumBetween C k j) - T k (cumBetween C k j)) -
        ∑ k ∈ Ico j0 j, (T k (C j + cumBetween C k j) - T k (cumBetween C k j)) =
        ∑ k ∈ Ico j0 j, (T k (Γ + C j + cumBetween C k j) - T k (C j + cumBetween C k j)) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    linear_combination hsum

/-! ### The functionals of one step -/

/-- The `ab` tadpole functional `∑_Bm₂(e^{ℒ_Γ}W(B)_{ab})`. -/
def wTadAB (k : ℕ) (W : OFam .two d L N) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k, mass2 (expLC Γ (W b : SA .two (Lam d L N)).ab)

/-- The `ab` product part `∑_{B_+}m₂(e^{ℒ_Γ}(𝒲_{j+1}(B_+) - ∑_{B⊆B_+}𝒲'(B))_{ab})`. -/
def wProdAB (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    mass2 (expLC Γ ((Wnext2O P j C V W c' - ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      WpO P j C V W b : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab)

/-- The tadpoles of the localised parts: `∑_B(m₂(e^{ℒ_Γ}Loc S(B)_{ab}) - m₂(Loc S(B)_{ab}))`. -/
def pdefLS (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j,
    (mass2 (expLC Γ (LSO P j C V W b : SA .two (Lam d L N)).ab) -
      mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab)

/-- `s_j = (∑_BS^{(2)}(B))_{ab}`. -/
def sfAB (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam .two d L N) : Alg d L N :=
  ((∑ b ∈ blockIdx (L := L) (N := N) j, SFO j C V b : OE .two (Lam d L N)) :
    SA .two (Lam d L N)).ab

/-- The one-loop tadpole of the pair sector: `m₂(e^{ℒ_Γ}s_j) - m₂(s_j)`. -/
def tauAB (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam .two d L N)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  mass2 (expLC Γ (sfAB j C V)) - mass2 (sfAB j C V)

/-- The gradient part `D_j = V'(Λ)_{ab} - ε - m₂(V'(Λ)_{ab})ψ̄_aψ_a`. -/
def dAB (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam .two d L N) :
    Alg d L N :=
  (VprLO j C V : SA .two (Lam d L N)).ab -
    (ε (VprLO j C V : SA .two (Lam d L N)).ab • (1 : Alg d L N) +
      mass2 (VprLO j C V : SA .two (Lam d L N)).ab • pbp P.a)

/-- The tadpole of the gradient part: `m₂(e^{ℒ_Γ}F_C(D_j, V'_∅)) - m₂(F_C(D_j, V'_∅))`. -/
def dTauAB (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam .two d L N)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  mass2 (expLC Γ (FC C (dAB P j C V) (VprLO j C V : SA .two (Lam d L N)).e)) -
    mass2 (FC C (dAB P j C V) (VprLO j C V : SA .two (Lam d L N)).e)

/-- The activity part of `e_{ab}`: `∑_Bm₂(e^{ℒ_C}Q(B)_{ab})`. -/
def qAB (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : OAct .two d L N) :
    ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (expLC C (Q2O P j K b : SA .two (Lam d L N)).ab)

section Step

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

/-- `∑_Bm₂(Loc S(B)_{ab}) = ∑_Bm₂(S(B)_{ab}) - f` (the `(j+1)`-blocks not meeting `{a,b}`). -/
theorem mass2_LSO_sum_ab :
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab =
      ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (SbO j C V W b : SA .two (Lam d L N)).ab -
        farABm P j C V W := by
  rw [← sum_blockIdx_succ j, ← sum_blockIdx_succ j, farABm, ← sum_sub_distrib]
  refine sum_congr rfl fun c' hc' => ?_
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

theorem mass2_sfAB_sum (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (expLC Γ (SFO j C V b : SA .two (Lam d L N)).ab) =
      mass2 (expLC Γ (sfAB j C V)) := by
  rw [sfAB, AddSubmonoidClass.coe_finsetSum, sum_ab, map_sum, mass2_sum]

/-- **The `ab` tadpole recursion of one step.** -/
theorem wTadAB_step (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadAB (j + 1) (Wnext2O P j C V W) Γ =
      tauAB j C V Γ + (wTadAB j W (Γ + C) - wTadAB j W C) + farABm P j C V W -
        pdefLS P j C V W Γ + wProdAB P j C V W Γ := by
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
  have hL := mass2_LSO_sum_ab P j C V W
  have hSb : ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (SbO j C V W b : SA .two (Lam d L N)).ab =
      mass2 (sfAB j C V) + wTadAB j W C := by
    have h0 := mass2_sfAB_sum j C V 0
    simp only [expLC_zero] at h0
    rw [← h0, wTadAB, ← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [SbO, Subalgebra.coe_add, add_ab, (EthO_comp C (W b)).2.2, mass2_add]
  have hW : wTadAB (j + 1) (Wnext2O P j C V W) Γ =
      wProdAB P j C V W Γ + ∑ b ∈ blockIdx (L := L) (N := N) j,
        mass2 (expLC Γ (WpO P j C V W b : SA .two (Lam d L N)).ab) := by
    unfold wTadAB
    rw [sum_congr rfl fun c' _ => h1 c', sum_add_distrib, sum_blockIdx_succ j]
    rfl
  rw [hW]
  simp only [h2, sum_sub_distrib, sum_add_distrib]
  rw [mass2_sfAB_sum]
  have hP : ∑ b ∈ blockIdx (L := L) (N := N) j,
      mass2 (expLC Γ (LSO P j C V W b : SA .two (Lam d L N)).ab) =
        pdefLS P j C V W Γ + ∑ b ∈ blockIdx (L := L) (N := N) j,
          mass2 (LSO P j C V W b : SA .two (Lam d L N)).ab := by
    rw [pdefLS, sum_sub_distrib]; ring
  rw [hP, hL, hSb]
  unfold tauAB wTadAB
  ring

/-! ### Without one-point parts -/

theorem VprLO_a_zero (hVa : ∀ b, (V b : SA .two (Lam d L N)).a = 0) :
    (VprLO j C V : SA .two (Lam d L N)).a = 0 := by
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_a]
  exact sum_eq_zero fun b _ => by rw [VprO, EthO_a_eq, hVa b, map_zero]

theorem sumSFO_eq :
    ∑ b ∈ blockIdx (L := L) (N := N) j, SFO j C V b =
      (1 / 2 : ℂ) • FCO C (VprLO j C V) (VprLO j C V) := by
  have h := SbO_sum j C V V
  simp only [SbO, sum_add_distrib] at h
  exact add_right_cancel h

/-- **`s_j = F_C(V'(Λ)_{ab}, V'(Λ)_∅)`** without one-point parts. -/
theorem sfAB_red (hVa : ∀ b, (V b : SA .two (Lam d L N)).a = 0) :
    sfAB j C V = FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e := by
  rw [sfAB, sumSFO_eq j C V, Subalgebra.coe_smul, smul_ab, FCO_self_ab, VprLO_a_zero j C V hVa,
    FC_zero_left, smul_zero, add_zero, smul_smul]
  norm_num

/-- `m₂(V'(Λ)_{ab}) = r + 𝔡₂`. -/
theorem mass2_VprLO_ab :
    mass2 (VprLO j C V : SA .two (Lam d L N)).ab = rAB2 j V + pdefM2 j C V := by
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_ab, mass2_sum, rAB2, pdefM2, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [VprO, (EthO_comp C (V b)).2.2, pauliDef2]
  ring

theorem FC_VprLO_ab_split (Y : Alg d L N) :
    FC C (VprLO j C V : SA .two (Lam d L N)).ab Y =
      mass2 (VprLO j C V : SA .two (Lam d L N)).ab • FC C (pbp P.a) Y + FC C (dAB P j C V) Y := by
  have e : (VprLO j C V : SA .two (Lam d L N)).ab =
      (ε (VprLO j C V : SA .two (Lam d L N)).ab • (1 : Alg d L N) +
        mass2 (VprLO j C V : SA .two (Lam d L N)).ab • pbp P.a) + dAB P j C V := by
    rw [dAB, add_sub_cancel]
  conv_lhs => rw [e]
  rw [FC_add_left, FC_loc2]

/-- **The one-loop tadpole of the pair sector**: `τ^{ab}_j = (r_j + 𝔡₂_j)τ₂ + τ^D_j`. -/
theorem tauAB_split (hVa : ∀ b, (V b : SA .two (Lam d L N)).a = 0)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    tauAB j C V Γ = (rAB2 j V + pdefM2 j C V) *
        tau2 C Γ P.a (VprLO j C V : SA .two (Lam d L N)).e + dTauAB P j C V Γ := by
  rw [tauAB, sfAB_red j C V hVa, FC_VprLO_ab_split P j C V, map_add, map_smul, mass2_add,
    mass2_add, mass2_smul, mass2_smul, mass2_VprLO_ab, tau2, dTauAB]
  ring

/-- **`d_r = 𝔡₂n_a + m₂F_C(D_j, V'_∅)`.** -/
theorem dR2_split :
    dR2 P j C V = pdefM2 j C V * nA2 P j C V +
      mass2 (FC C (dAB P j C V) (VprLO j C V : SA .two (Lam d L N)).e) := by
  rw [dR2, FC_VprLO_ab_split P j C V, mass2_add, mass2_smul, mass2_VprLO_ab, nA2]
  ring

theorem eAB2_eq :
    eAB2 P j C W K = qAB P j C K + wTadAB j W C := by
  rw [eAB2, qAB, wTadAB]
  congr 1
  exact sum_congr rfl fun b _ => by rw [(EthO_comp C (W b)).2.2]

end Step

/-! ### Along a chain -/

/-- **The hypothesis bundle of the reduced `ab` chain from `j₀`**: `𝒲_{j₀,ab} = 0`, the `ab`
parts of `𝒲` follow the map, and there are no `σ_a` parts. -/
structure MuChainAB (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (j0 n : ℕ) : Prop where
  hW0 : ∀ b, (W j0 b : SA .two (Lam d L N)).ab = 0
  hW : ∀ k, j0 ≤ k → k < n → ∀ c', (W (k + 1) c' : SA .two (Lam d L N)).ab =
    (Wnext2O P k (C k) (V k) (W k) c' : SA .two (Lam d L N)).ab
  hVa : ∀ k, j0 ≤ k → k ≤ n → ∀ b, (V k b : SA .two (Lam d L N)).a = 0

/-- The source of the reduced `r` flow: `σ_k = (𝔡₂ - d_r) - e_{ab} + f` (as `Spin2.srcR`). -/
def srcAB (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (k : ℕ) : ℂ :=
  (pdefM2 k (C k) (V k) - dR2 P k (C k) (V k)) - eAB2 P k (C k) (W k) (K k) +
    farABm P k (C k) (V k) (W k)

/-- The drift of the pair coupling: `∑_{i<k}(r̂_i - r_k)tadInc2 i k`, `r̂_i = r_i` (`i ≥ j₀`),
`r̂_i = 0` (`i < j₀`). -/
def driftAB (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) (j0 k : ℕ) : ℂ :=
  ∑ i ∈ range k, ((if j0 ≤ i then rAB2 i (V i) else 0) - rAB2 k (V k)) * tadInc2 P C V i k

/-- The memory terms of step `i` seen at step `k`: Pauli defect times tadpole, gradient tadpoles,
tadpoles of the localised parts, product increments. -/
def memAB (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (i k : ℕ) : ℂ :=
  pdefM2 i (C i) (V i) * tadInc2 P C V i k +
    (dTauAB P i (C i) (V i) (C k + cumBetween C i k) - dTauAB P i (C i) (V i) (cumBetween C i k)) -
    (pdefLS P i (C i) (V i) (W i) (C k + cumBetween C i k) -
      pdefLS P i (C i) (V i) (W i) (cumBetween C i k)) +
    (wProdAB P i (C i) (V i) (W i) (C k + cumBetween C i k) -
      wProdAB P i (C i) (V i) (W i) (cumBetween C i k))

/-- **The error of the reduced `r` flow** (the `ab` analogue of `shareErr2` without the drift). -/
def errAB (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (j0 k : ℕ) : ℂ :=
  qAB P k (C k) (K k) + wTadAB k (W k) 0 -
    pdefM2 k (C k) (V k) * (1 - nA2 P k (C k) (V k)) +
    mass2 (FC (C k) (dAB P k (C k) (V k)) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e) -
    farABm P k (C k) (V k) (W k) + ∑ i ∈ Ico j0 k, memAB P C V W i k

namespace MuChainAB

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {j0 n : ℕ} (H : MuChainAB P C V W j0 n)
include H

/-- **The unrolled `ab` tadpole functional.** -/
theorem wTadAB_unroll {m : ℕ} (hm : j0 ≤ m) (hmn : m ≤ n) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wTadAB m (W m) Γ = wTadAB m (W m) 0 +
      ∑ i ∈ Ico j0 m, ((tauAB i (C i) (V i) (Γ + cumBetween C i m) -
            tauAB i (C i) (V i) (cumBetween C i m)) -
          (pdefLS P i (C i) (V i) (W i) (Γ + cumBetween C i m) -
            pdefLS P i (C i) (V i) (W i) (cumBetween C i m)) +
          (wProdAB P i (C i) (V i) (W i) (Γ + cumBetween C i m) -
            wProdAB P i (C i) (V i) (W i) (cumBetween C i m))) := by
  classical
  let G : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k ≤ m then wTadAB k (W k) Γ else 0
  let T : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ → ℂ := fun k Γ =>
    if k < m then tauAB k (C k) (V k) Γ + farABm P k (C k) (V k) (W k) -
      pdefLS P k (C k) (V k) (W k) Γ + wProdAB P k (C k) (V k) (W k) Γ
    else -(G k (Γ + C k) - G k (C k))
  have hz : ∀ Γ, wTadAB j0 (W j0) Γ = 0 := fun Γ => by
    unfold wTadAB
    exact sum_eq_zero fun b _ => by rw [H.hW0 b, map_zero, mass2_zero]
  have h0 : ∀ Γ, G j0 Γ = G j0 0 := fun Γ => by
    show (if j0 ≤ m then _ else _) = (if j0 ≤ m then _ else _)
    rw [if_pos hm, if_pos hm, hz, hz]
  have hs : ∀ k, j0 ≤ k → ∀ Γ, G (k + 1) Γ = T k Γ + (G k (Γ + C k) - G k (C k)) := by
    intro k hk Γ
    by_cases hkm : k < m
    · simp only [G, T, if_pos hkm, if_pos (show k + 1 ≤ m by omega), if_pos hkm.le]
      have e : wTadAB (k + 1) (W (k + 1)) Γ =
          wTadAB (k + 1) (Wnext2O P k (C k) (V k) (W k)) Γ := by
        unfold wTadAB
        exact sum_congr rfl fun c' _ => by rw [H.hW k hk (by omega) c']
      rw [e, wTadAB_step]
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

/-- **The reduced `r` source in the `𝔫^{(2)}` split** (exact):
`σ_k + (∑_{i<k}tadInc2 i k)r_k = -(drift_k + err_k)` for `j₀ ≤ k ≤ n`. -/
theorem srcAB_eq (K : ℕ → OAct .two d L N) {k : ℕ} (hk : j0 ≤ k) (hkn : k ≤ n) :
    srcAB P C V W K k + (∑ i ∈ range k, tadInc2 P C V i k) * rAB2 k (V k) =
      -(driftAB P C V j0 k + errAB P C V W K j0 k) := by
  have hU := H.wTadAB_unroll hk hkn (C k)
  have hτ : ∀ i ∈ Ico j0 k, tauAB i (C i) (V i) (C k + cumBetween C i k) -
      tauAB i (C i) (V i) (cumBetween C i k) =
        (rAB2 i (V i) + pdefM2 i (C i) (V i)) * tadInc2 P C V i k +
          (dTauAB P i (C i) (V i) (C k + cumBetween C i k) -
            dTauAB P i (C i) (V i) (cumBetween C i k)) := by
    intro i hi
    have hi' := mem_Ico.1 hi
    rw [tauAB_split P i (C i) (V i) (H.hVa i hi'.1 (by omega)),
      tauAB_split P i (C i) (V i) (H.hVa i hi'.1 (by omega)), tadInc2, bulkE2]
    ring
  have hU' : wTadAB k (W k) (C k) = wTadAB k (W k) 0 +
      ∑ i ∈ Ico j0 k, (rAB2 i (V i) * tadInc2 P C V i k + memAB P C V W i k) := by
    rw [hU]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [hτ i hi, memAB]
    ring
  have hD : driftAB P C V j0 k = ∑ i ∈ Ico j0 k, rAB2 i (V i) * tadInc2 P C V i k -
      (∑ i ∈ range k, tadInc2 P C V i k) * rAB2 k (V k) := by
    have e1 : ∑ i ∈ range k, (if j0 ≤ i then rAB2 i (V i) else 0) * tadInc2 P C V i k =
        ∑ i ∈ Ico j0 k, rAB2 i (V i) * tadInc2 P C V i k := by
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le j0) hk,
        sum_eq_zero fun i hi => by rw [if_neg (by have := (mem_Ico.1 hi).2; omega), zero_mul],
        zero_add]
      exact sum_congr rfl fun i hi => by rw [if_pos (mem_Ico.1 hi).1]
    rw [driftAB, ← e1, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [srcAB, errAB, dR2_split, eAB2_eq, hU', hD, sum_add_distrib]
  ring

end MuChainAB

end

end Obs2
