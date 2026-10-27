import Obs2.Loc.Loc
import Step2.Map.StepFinal
import Step2.Map.RawMap
import Step2.Map.XStep

/-!
# The second-order renormalisation group map with observables (new route)

The maps of `Step2.Map.Defs`, `Step2.Map.Gen`, `Step2.Map.Reapp`, `Step2.Map.Split`, `Step2.Map.Reblock` and
`Step2.Map.StepFinal` over the algebra with sources `OE c Λ` (Section `sec:obs-flow`: "the second-order
map of Section `sec:pt-map` applied to `V^♭ + V^{obs,♭}`, with remainder `W^{obs}`"). The inputs
are the full families `V, 𝒲 : OFam` and the full activity `K : OAct` (bulk plus observable
parts). The definitions copy those of `Step2` with
* `𝔼_C θ ↦ EthO C`, `F_C ↦ FCO C`, `𝔼_C ↦ ECCO C`, `θ ↦ thetaO`, the inclusion `↦ inclO`,
  `e^{·} ↦ oexp`, `Loc ↦ LocO2 P` (`Obs2.Map.Ops`, `Obs2.Loc.Loc`);
* the constant `u_{j+1}(B)` split into its bulk part `upB ∈ ℂ` (Step2's `up`) and its observable
  part `upO = π_obs ε(uVpO)` (a constant observable element: `-σ_aσ_b q`, `-σ_a γ_a`, ...), and
  `e^{±u} = e^{±upB} e^{±upO}` (`expU`). The observable constant is nilpotent, so `oexp` is
  meaningful on it.

## Results (bulk projection)
`bulk` is an algebra hom commuting with all primitives, so every map projects to the `Step2` map
of the bulk parts (`bulk_*`), e.g.
* `bulk_VpO : bulk (VpO …) = Step2.Vp j C (bulkF V) (bulkF W) (bulkF K) b`,
* `bulk_Knext2O`, `bulk_KplusO : bulk (KplusO … U) = Step2.Kplus j C (bulkF V) (bulkF W) (bulkF K) U`,
* `bulk_Vnext2O`, `bulk_Wnext2O`, `bulk_KflatO`, `bulk_KconnO`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD PolyAux

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- A family of even elements with sources indexed by the `j`-blocks. -/
abbrev OFam (c : Obs.Case) (d L N : ℕ) [NeZero L] := (Fin d → ℕ) → OE c (Lam d L N)

/-- A polymer activity with sources. -/
abbrev OAct (c : Obs.Case) (d L N : ℕ) [NeZero L] := Finset (Lam d L N) → OE c (Lam d L N)

/-! ### Products over blocks and components -/

section Prod

/-- `I^X = ∏_{B ∈ 𝓑_j(X)} I(B)`. -/
def bpowO (j : ℕ) (I : OFam c d L N) (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  ∏ b ∈ blocks j X, I b

/-- `K(X) = ∏_{Y ∈ Comp(X)} K(Y)`. -/
def KextO (j : ℕ) (K : OAct c d L N) (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  ∏ Y ∈ Comp j X, K Y

theorem bulk_bpowO (j : ℕ) (I : OFam c d L N) (X : Finset (Lam d L N)) :
    bulk (bpowO j I X) = Step2.bpow j (bulkF I) X := by
  rw [bpowO, map_prod]; rfl

theorem bulk_KextO (j : ℕ) (K : OAct c d L N) (X : Finset (Lam d L N)) :
    bulk (KextO j K X) = Kext j (bulkF K) X := by
  rw [KextO, map_prod]; rfl

end Prod

/-! ### `Q` and `J` -/

section QJ

variable (P : ObsPts d L N) (j : ℕ) (K : OAct c d L N)

/-- `Q(B) = ∑_{X ∈ 𝒮_j, X ⊇ B} Loc_{X,B} K(X)`, `Q = 0` if `j + 1 = N`. -/
def Q2O (b : Fin d → ℕ) : OE c (Lam d L N) :=
  open Classical in
  if j + 1 < N then
    ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X), LocO2 P X (blockSet j b) (K X)
  else 0

/-- `J(B, X)`, `J = 0` if `j + 1 = N`. -/
def J2O (b : Fin d → ℕ) (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  open Classical in
  if j + 1 < N ∧ IsSmall j X ∧ blockSet j b ⊆ X then
    if X = blockSet j b then
      -∑ Y ∈ (smallSets j).filter (fun Y => blockSet j b ⊆ Y ∧ Y ≠ blockSet j b),
        LocO2 P Y (blockSet j b) (K Y)
    else LocO2 P X (blockSet j b) (K X)
  else 0

theorem bulk_Q2O (b : Fin d → ℕ) : bulk (Q2O P j K b) = Step2.Q2 j (bulkF K) b := by
  unfold Q2O Step2.Q2
  split_ifs
  · rw [map_sum]; rfl
  · exact map_zero _

theorem bulk_J2O (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    bulk (J2O P j K b X) = Step2.J2 j (bulkF K) b X := by
  unfold J2O Step2.J2
  split_ifs
  · rw [map_neg, map_sum]; rfl
  · rfl
  · exact map_zero _

theorem J2O_of_not_small (b : Fin d → ℕ) (X : Finset (Lam d L N)) (hX : ¬ IsSmall j X) :
    J2O P j K b X = 0 := by
  rw [J2O, if_neg fun h => hX h.2.1]

end QJ

/-! ### The polymer formula with general block factors (`Step2.Map.Gen`) -/

section Gen

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (Ib Ip : OFam c d L N) (K : OAct c d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N))

/-- `δI(B) = θ I_j(B) - I_{j+1}(B)`. -/
def gdIO (b : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) := thetaO (Ib b) - inclO (Ip b)

/-- `(δI)^X`. -/
def gdIPowO (X : Finset (Lam d L N)) : OE c (Lam d L N ⊕ Lam d L N) :=
  ∏ b ∈ blocks j X, gdIO Ib Ip b

/-- `K̃(W) = ∑_{Y ∈ 𝒫_j(W)} θ K(W ∖ Y) (δI)^Y`. -/
def gKtilO (W : Finset (Lam d L N)) : OE c (Lam d L N ⊕ Lam d L N) :=
  ∑ Y ∈ Pj j W, thetaO (KextO j K (W \ Y)) * gdIPowO j Ib Ip Y

/-- `Ǩ(W) = K̃(W) - ∑_{B ∈ 𝓑_j(W)} θ J(B, W)` for connected `W`. -/
def gKchkCO (W : Finset (Lam d L N)) : OE c (Lam d L N ⊕ Lam d L N) :=
  gKtilO j Ib Ip K W - ∑ b ∈ blocks j W, thetaO (J b W)

/-- `Ǩ(X) = ∏_{W ∈ Comp(X)} Ǩ(W)`. -/
def gKchkO (X : Finset (Lam d L N)) : OE c (Lam d L N ⊕ Lam d L N) :=
  ∏ W ∈ Comp j X, gKchkCO j Ib Ip K J W

/-- `K_{j+1}(U)` without the normalisation `e^{u(U)}`. -/
def gKnextO (U : Finset (Lam d L N)) : OE c (Lam d L N) :=
  ∑ g ∈ Gset j U, bpowO j Ip (U \ (g.2 ∪ Xcal g.1)) *
    ECCO C (gKchkO j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaO (J p.1 p.2))

theorem bulk_gdIO (b : Fin d → ℕ) : bulk (gdIO Ib Ip b) = Step2.gdI (bulkF Ib) (bulkF Ip) b := by
  rw [gdIO, map_sub]; rfl

theorem bulk_gdIPowO (X : Finset (Lam d L N)) :
    bulk (gdIPowO j Ib Ip X) = Step2.gdIPow j (bulkF Ib) (bulkF Ip) X := by
  rw [gdIPowO, map_prod]
  exact prod_congr rfl fun b _ => bulk_gdIO Ib Ip b

theorem bulk_gKtilO (W : Finset (Lam d L N)) :
    bulk (gKtilO j Ib Ip K W) = Step2.gKtil j (bulkF Ib) (bulkF Ip) (bulkF K) W := by
  rw [gKtilO, map_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [map_mul, bulk_gdIPowO, bulk_thetaO, bulk_KextO]

theorem bulk_gKchkCO (W : Finset (Lam d L N)) :
    bulk (gKchkCO j Ib Ip K J W) =
      Step2.gKchkC j (bulkF Ib) (bulkF Ip) (bulkF K) (fun b X => bulk (J b X)) W := by
  rw [gKchkCO, map_sub, bulk_gKtilO, map_sum]; rfl

theorem bulk_gKchkO (X : Finset (Lam d L N)) :
    bulk (gKchkO j Ib Ip K J X) =
      Step2.gKchk j (bulkF Ib) (bulkF Ip) (bulkF K) (fun b X => bulk (J b X)) X := by
  rw [gKchkO, map_prod]
  exact prod_congr rfl fun W _ => bulk_gKchkCO j Ib Ip K J W

theorem bulk_gKnextO (U : Finset (Lam d L N)) :
    bulk (gKnextO j C Ib Ip K J U) =
      Step2.gKnext j C (bulkF Ib) (bulkF Ip) (bulkF K) (fun b X => bulk (J b X)) U := by
  rw [gKnextO, map_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [map_mul, bulk_bpowO, bulk_ECCO, map_mul, bulk_gKchkO, map_prod]
  rfl

end Gen

/-! ### The second-order map (`Step2.Map.Defs`) -/

section Map

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

/-- `V'_B = 𝔼_C θ V(B)`. -/
def VprO (b : Fin d → ℕ) : OE c (Lam d L N) := EthO C (V b)

/-- `V'(Λ) = ∑_B V'_B`. -/
def VprLO : OE c (Lam d L N) := ∑ b ∈ blockIdx (L := L) (N := N) j, VprO C V b

/-- The correction of the sharp splitting,
`½(F_C(π_obs V'_B, V'(Λ)) − F_C(V'_B, π_obs V'(Λ))) = ½(F_C(V'_B, ιV'(Λ)^∅) − F_C(ιV'^∅_B, V'(Λ)))`:
it assigns the observable part of the second-order term to the block carrying the observable. -/
def SCorO (b : Fin d → ℕ) : OE c (Lam d L N) :=
  (1 / 2 : ℂ) • (FCO C (πobs (VprO C V b)) (VprLO j C V) - FCO C (VprO C V b) (πobs (VprLO j C V)))

/-- The antisymmetric pair `G(B, B') = F_C(π_obs V'_B, V'_{B'}) − F_C(V'_B, π_obs V'_{B'})`:
`SCorO(B) = ½ ∑_{B'} G(B, B')` (`SCorO_eq_sum`). -/
def GO (b b' : Fin d → ℕ) : OE c (Lam d L N) :=
  FCO C (πobs (VprO C V b)) (VprO C V b') - FCO C (VprO C V b) (πobs (VprO C V b'))

theorem GO_antisymm (b b' : Fin d → ℕ) : GO C V b' b = -GO C V b b' := by
  rw [GO, GO, FCO_comm C (πobs (VprO C V b')), FCO_comm C (VprO C V b'), neg_sub]

theorem GO_self (b : Fin d → ℕ) : GO C V b b = 0 := by
  rw [GO, FCO_comm C (πobs (VprO C V b)), sub_self]

theorem sum_sum_GO (S : Finset (Fin d → ℕ)) : ∑ b ∈ S, ∑ b' ∈ S, GO C V b b' = 0 := by
  have h : ∑ b ∈ S, ∑ b' ∈ S, GO C V b b' = -∑ b ∈ S, ∑ b' ∈ S, GO C V b b' := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x _ => GO_antisymm C V y x
  have h2 : (2 : ℂ) • ∑ b ∈ S, ∑ b' ∈ S, GO C V b b' = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem sum_sum_GO_erase (S : Finset (Fin d → ℕ)) :
    ∑ b ∈ S, ∑ b' ∈ S.erase b, GO C V b b' = 0 := by
  rw [← sum_sum_GO C V S]
  refine sum_congr rfl fun b hb => ?_
  rw [← sum_erase_add _ _ hb, GO_self, add_zero]

theorem SCorO_eq_sum (b : Fin d → ℕ) :
    SCorO j C V b = (1 / 2 : ℂ) • ∑ b' ∈ blockIdx (L := L) (N := N) j, GO C V b b' := by
  simp only [SCorO, GO, VprLO, map_sum, FCO_sum_right, ← sum_sub_distrib]

/-- The (sharp) second-order part of `S(B)`: `½ F(V'_B, V'(Λ)) + SCorO`. -/
def SFO (b : Fin d → ℕ) : OE c (Lam d L N) :=
  (1 / 2 : ℂ) • FCO C (VprO C V b) (VprLO j C V) + SCorO j C V b

/-- **The sharp splitting** `S^♯(B) = S(B) + ½(F_C(V'_B, ιV'(Λ)^∅) − F_C(ιV'^∅_B, V'(Λ)))`,
`S(B) = ½ F(V'_B, V'(Λ)) + 𝔼_C θ 𝒲(B)`. Componentwise: `S^♯(B)^∅ = S(B)^∅`,
`S^♯(B)_a = F_C(V'_{B,a}, V'(Λ)_∅) + (𝔼θ𝒲(B))_a` (same for `b`). -/
def SbO (b : Fin d → ℕ) : OE c (Lam d L N) := SFO j C V b + EthO C (W b)

/-- `S(X) = ∑_{B ∈ 𝓑_j(X)} S(B)`. -/
def SXO (X : Finset (Lam d L N)) : OE c (Lam d L N) := ∑ b ∈ blocks j X, SbO j C V W b

/-- `Loc_{B_+, B} S(B_+)`. -/
def LSO (b : Fin d → ℕ) : OE c (Lam d L N) :=
  LocO2 P (Step2.Bp (L := L) (N := N) j b) (blockSet j b) (SXO j C V W (Step2.Bp j b))

/-- `(u+V)_{j+1}(B) = V'_B - 𝔼_C θ Q(B) - Loc_{B_+,B} S(B_+)`. -/
def uVpO (b : Fin d → ℕ) : OE c (Lam d L N) :=
  VprO C V b - EthO C (Q2O P j K b) - LSO P j C V W b

/-- The bulk constant `u^∅_{j+1}(B) = ε((u+V)^∅_{j+1}(B))`. -/
def upB (b : Fin d → ℕ) : ℂ := ε (bulk (uVpO P j C V W K b) : Alg d L N)

/-- The observable constant `u^{obs}_{j+1}(B) = π_obs ε((u+V)_{j+1}(B))`. -/
def upO (b : Fin d → ℕ) : OE c (Lam d L N) := πobs (epsO (uVpO P j C V W K b))

/-- `V_{j+1}(B) = (u+V)_{j+1}(B) - u^∅_{j+1}(B) - u^{obs}_{j+1}(B)`. -/
def VpO (b : Fin d → ℕ) : OE c (Lam d L N) :=
  uVpO P j C V W K b - algebraMap ℂ _ (upB P j C V W K b) - upO P j C V W K b

/-- `𝒲_{j+1}(B) = S(B) - Loc_{B_+,B} S(B_+)`. -/
def WpO (b : Fin d → ℕ) : OE c (Lam d L N) := SbO j C V W b - LSO P j C V W b

/-- `I_j(B) = e^{-V(B)} (1 + 𝒲(B))`. -/
def IbO (b : Fin d → ℕ) : OE c (Lam d L N) := oexp (-V b) * (1 + W b)

/-- `Ĩ_{j+1}(B) = e^{-V_{j+1}(B)}(1 + 𝒲_{j+1}(B))`. -/
def GpO (b : Fin d → ℕ) : OE c (Lam d L N) :=
  oexp (-VpO P j C V W K b) * (1 + WpO P j C V W b)

/-- `I_{j+1}(B) = e^{-u_{j+1}(B)} e^{-V_{j+1}(B)} (1 + 𝒲_{j+1}(B))`. -/
def IpO (b : Fin d → ℕ) : OE c (Lam d L N) :=
  expU (-upB P j C V W K b) (-upO P j C V W K b) * GpO P j C V W K b

/-- `u^∅_{j+1}(X)`. -/
def uXB (X : Finset (Lam d L N)) : ℂ := ∑ b ∈ blocks j X, upB P j C V W K b

/-- `u^{obs}_{j+1}(X)`. -/
def uXO (X : Finset (Lam d L N)) : OE c (Lam d L N) := ∑ b ∈ blocks j X, upO P j C V W K b

/-- **`K_{j+1}(U)`** of the second-order map with observables (polymer formula). -/
def Knext2O (U : Finset (Lam d L N)) : OE c (Lam d L N) :=
  expU (uXB P j C V W K U) (uXO P j C V W K U) *
    gKnextO j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U

/-- `V_{j+1}(B_+) = ∑_{B ⊆ B_+} V_{j+1}(B)`. -/
def Vnext2O (c' : Fin d → ℕ) : OE c (Lam d L N) :=
  ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), VpO P j C V W K b

/-- `𝒲_{j+1}(B_+) = ∏_{B ⊆ B_+} (1 + 𝒲_{j+1}(B)) - 1`. -/
def Wnext2O (c' : Fin d → ℕ) : OE c (Lam d L N) :=
  ∏ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), (1 + WpO P j C V W b) - 1

/-- The total observable constant `u^{obs}_{j+1}(Λ)` of the step. -/
def uObsTot : OE c (Lam d L N) := ∑ b ∈ blockIdx (L := L) (N := N) j, upO P j C V W K b

/-! #### The second-order part and the reapportionment (`Step2.Map.Reapp`, `Step2.Map.Split`) -/

/-- `k^{(2)}(X)`. -/
def k2O (X : Finset (Lam d L N)) : OE c (Lam d L N) :=
  if nb j X = 1 then
    ∑ b ∈ blocks j X, ((-(1 / 2 : ℂ)) • FCO C (VprO C V b) (VprLO j C V - VprO C V b) -
      SCorO j C V b)
  else if nb j X = 2 then
    (1 / 2 : ℂ) • ∑ b ∈ blocks j X, ∑ b' ∈ (blocks j X).erase b, FCO C (VprO C V b) (VprO C V b')
  else 0

/-- The single-block part of `k^{(2)}`: `-½F(V'_B, V'(Λ) - V'_B) - SCorO = ½F(V'_B, V'_B) - S^{(2)}(B)`,
so that `S^♯(B) + k^{(2)}(B) = ½F(V'_B, V'_B) + 𝔼θ𝒲(B)` as for the symmetric splitting. -/
theorem k2one_eq (b : Fin d → ℕ) :
    (-(1 / 2 : ℂ)) • FCO C (VprO C V b) (VprLO j C V - VprO C V b) - SCorO j C V b =
      (1 / 2 : ℂ) • FCO C (VprO C V b) (VprO C V b) - SFO j C V b := by
  rw [SFO, sub_eq_add_neg (VprLO j C V), FCO_add_right, ← neg_one_smul ℂ (VprO C V b),
    FCO_smul_right]
  module

/-- `K^{(2)}(U)`. -/
def K2O (U : Finset (Lam d L N)) : OE c (Lam d L N) :=
  open Classical in ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U), k2O j C V X

/-- `K^♯_{j+1}(U) = K_{j+1}(U) - Ĩ_{j+1}^U K^{(2)}(U)`. -/
def KnewO (U : Finset (Lam d L N)) : OE c (Lam d L N) :=
  Knext2O P j C V W K U - bpowO j (GpO P j C V W K) U * K2O j C V U

/-- `Ĩ_{j+1}(B_+) = ∏_{B ⊆ B_+} Ĩ_{j+1}(B)`. -/
def ItO (c' : Fin d → ℕ) : OE c (Lam d L N) :=
  bpowO j (GpO P j C V W K) (blockSet (L := L) (N := N) (j + 1) c')

/-- The part of `k^{(2)}(X)` from the `j`-blocks in `B(c')`. With the sharp splitting the
two-block part carries the antisymmetric pairs `G(B, B')` (they cancel in `∑_{c'}`), so that
`∑_X κ(X, B_+) = 0` still holds (`kapO_sum_zero`). -/
def kapO (X : Finset (Lam d L N)) (c' : Fin d → ℕ) : OE c (Lam d L N) :=
  if nb j X = 1 then
    ∑ b ∈ (blocks j X).filter (fun b => par L b = c'),
      ((-(1 / 2 : ℂ)) • FCO C (VprO C V b) (VprLO j C V - VprO C V b) - SCorO j C V b)
  else if nb j X = 2 then
    (1 / 2 : ℂ) • ∑ b ∈ (blocks j X).filter (fun b => par L b = c'),
      ∑ b' ∈ (blocks j X).erase b, (FCO C (VprO C V b) (VprO C V b') + GO C V b b')
  else 0

/-- The split `J(B_+, U)` of `K^{(2)}`. -/
def JhO (c' : Fin d → ℕ) (U : Finset (Lam d L N)) : OE c (Lam d L N) :=
  open Classical in
  if IsSmall (j + 1) U then ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U), kapO j C V X c'
  else 0

end Map

/-! ### The change of variables (`Step2.Map.Reblock`) -/

section Reblock

variable (k : ℕ) (I : OFam c d L N) (M : OAct c d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N))

/-- `J̄(B, U) = I^U J(B, U)`. -/
def JbarO (b : Fin d → ℕ) (U : Finset (Lam d L N)) : OE c (Lam d L N) := bpowO k I U * J b U

/-- The summand of `K_out(W)`. -/
def RtermO (W : Finset (Lam d L N)) (g : GT d L N) : OE c (Lam d L N) :=
  bpowO k I (W \ (g.2 ∪ Xcal g.1)) * (KextO k M g.2 * ∏ p ∈ g.1, JbarO k I J p.1 p.2)

/-- `K_out(W)` (Brydges–Slade (D.13)). -/
def KoutO (W : Finset (Lam d L N)) : OE c (Lam d L N) :=
  ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W), RtermO k I M J W g

theorem bulk_JbarO (b : Fin d → ℕ) (U : Finset (Lam d L N)) :
    bulk (JbarO k I J b U) = Step2.Jbar k (bulkF I) (fun b X => bulk (J b X)) b U := by
  rw [JbarO, map_mul, bulk_bpowO]; rfl

theorem bulk_RtermO (W : Finset (Lam d L N)) (g : GT d L N) :
    bulk (RtermO k I M J W g) = Step2.Rterm k (bulkF I) (bulkF M) (fun b X => bulk (J b X)) W g := by
  rw [RtermO, map_mul, map_mul, bulk_bpowO, bulk_KextO, map_prod]
  simp only [bulk_JbarO]
  rfl

theorem bulk_KoutO (W : Finset (Lam d L N)) :
    bulk (KoutO k I M J W) = Step2.Kout k (bulkF I) (bulkF M) (fun b X => bulk (J b X)) W := by
  rw [KoutO, map_sum]
  simp only [bulk_RtermO]
  rfl

end Reblock

/-! ### `K_{j+1}` and the auxiliary maps of the raw step -/

section Plus

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

/-- **`K_{j+1}`** with observables: the output of the change of variables (D.13). -/
def KplusO : OAct c d L N :=
  KoutO (j + 1) (ItO P j C V W K) (KnewO P j C V W K) (JhO j C V)

/-- An activity restricted to connected polymers. -/
def KconnO (k : ℕ) (K : OAct c d L N) : OAct c d L N :=
  open Classical in fun X => if IsConn k X then K X else 0

/-- `K♭(X) = ∏_{B ⊆ X} e^{Δ(B)} K(X)` for a bulk family `Δ`. -/
def KflatO (Δ : Step2.Fam d L N) (K : OAct c d L N) : OAct c d L N :=
  fun Y => emb (Step2.bpow j (fun b => gexp (Δ b)) Y) * K Y

end Plus

/-! ### Bulk projections -/

section Bulk

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) (K : OAct c d L N)

theorem bulk_VprO (b : Fin d → ℕ) : bulk (VprO C V b) = Step2.Vpr C (bulkF V) b := rfl

theorem bulk_VprLO : bulk (VprLO j C V) = Step2.VprL j C (bulkF V) := by
  rw [VprLO, map_sum]; rfl

theorem FCE_zero_leftO (B : Step.EvR (Lam d L N)) : Step2.FCE C 0 B = 0 :=
  Subtype.ext (by simp [FC])

theorem FCE_zero_rightO (B : Step.EvR (Lam d L N)) : Step2.FCE C B 0 = 0 :=
  Subtype.ext (by simp [FC])

theorem bulk_SCorO (b : Fin d → ℕ) : bulk (SCorO j C V b) = 0 := by
  rw [SCorO, map_smul, map_sub, bulk_FCO, bulk_FCO, bulk_πobs, bulk_πobs, FCE_zero_leftO,
    FCE_zero_rightO, sub_zero, smul_zero]

theorem bulk_GO (b b' : Fin d → ℕ) : bulk (GO C V b b') = 0 := by
  rw [GO, map_sub, bulk_FCO, bulk_FCO, bulk_πobs, bulk_πobs, FCE_zero_leftO, FCE_zero_rightO,
    sub_zero]

theorem bulk_SbO (b : Fin d → ℕ) : bulk (SbO j C V W b) = Step2.Sb j C (bulkF V) (bulkF W) b := by
  rw [SbO, SFO, map_add, map_add, bulk_SCorO, add_zero, map_smul, bulk_FCO, bulk_VprLO]; rfl

theorem bulk_SXO (X : Finset (Lam d L N)) :
    bulk (SXO j C V W X) = Step2.SX j C (bulkF V) (bulkF W) X := by
  rw [SXO, map_sum]
  exact sum_congr rfl fun b _ => bulk_SbO j C V W b

theorem bulk_LSO (b : Fin d → ℕ) : bulk (LSO P j C V W b) = Step2.LS j C (bulkF V) (bulkF W) b := by
  rw [LSO, bulk_LocO2, bulk_SXO]; rfl

theorem bulk_uVpO (b : Fin d → ℕ) :
    bulk (uVpO P j C V W K b) = Step2.uVp j C (bulkF V) (bulkF W) (bulkF K) b := by
  rw [uVpO, map_sub, map_sub, bulk_LSO, bulk_EthO, bulk_Q2O]; rfl

theorem upB_eq (b : Fin d → ℕ) :
    upB P j C V W K b = Step2.up j C (bulkF V) (bulkF W) (bulkF K) b := by
  rw [upB, bulk_uVpO]; rfl

theorem bulk_upO (b : Fin d → ℕ) : bulk (upO P j C V W K b) = 0 := bulk_πobs _

theorem bulk_VpO (b : Fin d → ℕ) :
    bulk (VpO P j C V W K b) = Step2.Vp j C (bulkF V) (bulkF W) (bulkF K) b := by
  rw [VpO, map_sub, map_sub, bulk_upO, sub_zero, AlgHom.commutes, bulk_uVpO, upB_eq]; rfl

theorem bulk_WpO (b : Fin d → ℕ) : bulk (WpO P j C V W b) = Step2.Wp j C (bulkF V) (bulkF W) b := by
  rw [WpO, map_sub, bulk_SbO, bulk_LSO]; rfl

theorem bulk_IbO (b : Fin d → ℕ) : bulk (IbO V W b) = Step2.Ib (bulkF V) (bulkF W) b := by
  rw [IbO, map_mul, bulk_oexp', map_add, map_one, map_neg]; rfl

theorem bulk_GpO (b : Fin d → ℕ) :
    bulk (GpO P j C V W K b) = Step2.Gp j C (bulkF V) (bulkF W) (bulkF K) b := by
  rw [GpO, map_mul, bulk_oexp', map_add, map_one, map_neg, bulk_VpO, bulk_WpO]; rfl

theorem bulk_IpO (b : Fin d → ℕ) :
    bulk (IpO P j C V W K b) = Step2.Ip j C (bulkF V) (bulkF W) (bulkF K) b := by
  have h : bulk (-upO P j C V W K b) = 0 := by rw [map_neg, bulk_upO, neg_zero]
  rw [IpO, map_mul, bulk_expU_obs _ h, bulk_GpO, upB_eq, ← Algebra.smul_def]; rfl

theorem uXB_eq (X : Finset (Lam d L N)) :
    uXB P j C V W K X = Step2.uX j C (bulkF V) (bulkF W) (bulkF K) X := by
  rw [uXB, Step2.uX]; simp only [upB_eq]

theorem bulk_uXO (X : Finset (Lam d L N)) : bulk (uXO P j C V W K X) = 0 := by
  rw [uXO, map_sum]; simp [bulk_upO]

/-- **The bulk part of `K_{j+1}` (polymer formula) is Step2's `Knext2`.** -/
theorem bulk_Knext2O (U : Finset (Lam d L N)) :
    bulk (Knext2O P j C V W K U) = Step2.Knext2 j C (bulkF V) (bulkF W) (bulkF K) U := by
  rw [Knext2O, map_mul, bulk_expU_obs _ (bulk_uXO P j C V W K U), bulk_gKnextO, uXB_eq,
    ← Algebra.smul_def, Step2.Knext2]
  congr 2
  · funext b; exact bulk_IbO V W b
  · funext b; exact bulk_IpO P j C V W K b
  · funext b X; exact bulk_J2O P j K b X

theorem bulk_Vnext2O (c' : Fin d → ℕ) :
    bulk (Vnext2O P j C V W K c') = Step2.Vnext2 j C (bulkF V) (bulkF W) (bulkF K) c' := by
  rw [Vnext2O, map_sum]
  exact sum_congr rfl fun b _ => bulk_VpO P j C V W K b

theorem bulk_Wnext2O (c' : Fin d → ℕ) :
    bulk (Wnext2O P j C V W c') = Step2.Wnext2 j C (bulkF V) (bulkF W) c' := by
  rw [Wnext2O, map_sub, map_prod, map_one, Step2.Wnext2]
  congr 1
  exact prod_congr rfl fun b _ => by rw [map_add, map_one, bulk_WpO]

theorem bulk_k2O (X : Finset (Lam d L N)) : bulk (k2O j C V X) = Step2.k2 j C (bulkF V) X := by
  unfold k2O Step2.k2
  split_ifs
  · rw [map_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [map_sub, bulk_SCorO, sub_zero, map_smul, bulk_FCO, map_sub, bulk_VprLO]; rfl
  · rw [map_smul, map_sum]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [map_sum]; rfl
  · exact map_zero _

theorem bulk_K2O (U : Finset (Lam d L N)) : bulk (K2O j C V U) = Step2.K2 j C (bulkF V) U := by
  unfold K2O Step2.K2
  rw [map_sum]
  exact sum_congr rfl fun X _ => bulk_k2O j C V X

theorem bulk_KnewO (U : Finset (Lam d L N)) :
    bulk (KnewO P j C V W K U) = Step2.Knew j C (bulkF V) (bulkF W) (bulkF K) U := by
  rw [KnewO, map_sub, map_mul, bulk_Knext2O, bulk_bpowO, bulk_K2O, Step2.Knew]
  congr 3
  funext b; exact bulk_GpO P j C V W K b

theorem bulk_ItO (c' : Fin d → ℕ) :
    bulk (ItO P j C V W K c') = Step2.It j C (bulkF V) (bulkF W) (bulkF K) c' := by
  rw [ItO, bulk_bpowO, Step2.It]
  congr 1
  funext b; exact bulk_GpO P j C V W K b

theorem bulk_kapO (X : Finset (Lam d L N)) (c' : Fin d → ℕ) :
    bulk (kapO j C V X c') = Step2.kap j C (bulkF V) X c' := by
  unfold kapO Step2.kap
  split_ifs
  · rw [map_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [map_sub, bulk_SCorO, sub_zero, map_smul, bulk_FCO, map_sub, bulk_VprLO]; rfl
  · rw [map_smul, map_sum]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [map_sum]
    refine sum_congr rfl fun b' _ => ?_
    rw [map_add, bulk_GO, add_zero]; rfl
  · exact map_zero _

theorem bulk_JhO (c' : Fin d → ℕ) (U : Finset (Lam d L N)) :
    bulk (JhO j C V c' U) = Step2.Jh j C (bulkF V) c' U := by
  unfold JhO Step2.Jh
  split_ifs
  · rw [map_sum]
    exact sum_congr rfl fun X _ => bulk_kapO j C V X c'
  · exact map_zero _

/-- **The bulk part of `K_{j+1}` is Step2's `Kplus`.** -/
theorem bulk_KplusO (U : Finset (Lam d L N)) :
    bulk (KplusO P j C V W K U) = Step2.Kplus j C (bulkF V) (bulkF W) (bulkF K) U := by
  rw [KplusO, bulk_KoutO, Step2.Kplus]
  congr 1
  · funext c'; exact bulk_ItO P j C V W K c'
  · funext U'; exact bulk_KnewO P j C V W K U'
  · funext c' U'; exact bulk_JhO j C V c' U'

theorem bulk_KconnO (k : ℕ) (U : Finset (Lam d L N)) :
    bulk (KconnO k K U) = Step2.Kconn k (bulkF K) U := by
  unfold KconnO Step2.Kconn
  split_ifs
  · rfl
  · exact map_zero _

theorem bulk_KflatO (Δ : Step2.Fam d L N) (U : Finset (Lam d L N)) :
    bulk (KflatO j Δ K U) = Step2.Kflat j Δ (bulkF K) U := by
  rw [KflatO, map_mul, bulk_emb]; rfl

end Bulk

end

end Obs2
