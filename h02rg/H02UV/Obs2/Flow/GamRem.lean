import Obs2.Flow.GamChain2
import Obs2.Flow.WickTotal
import Obs2.Flow.Tau2Hist

/-!
# The remainder `ρ_k` of the Case-(2) `γ` flow: exact split into bulk and observable parts

`ρ_k = gamRem2 k = ∑_B (ε(e^{ℒ_{C_k}}Q_k(B)_a) + ε(loc^a S(B_+)_a))` (`Obs2/Flow/GamChain2`). The
localisation preserves `ε` (`eps_locA_two_mem`, `eps_locA_two_pt`) and `loc^a_{X,·}` distributes
`ε` over the blocks of `X` with total weight one (`eps_sum_blocks`), so the localisation cancels
in the sum over all blocks (`eps_total_LS`). With the sharp splitting
`∑_B S(B)_a = F_C(V'(Λ)_a, V'(Λ)_∅) + ∑_B(𝔼θ𝒲(B))_a` (`eps_SbO_sum`) and
`V'(Λ)_a = α + β_kψ̄_aψ_a` (`β_k = betaTot2`; `eps_FC_loc2`):

  **`ρ_k = ∑_B ε(e^{ℒ_{C_k}}Q_k(B)_a) + ∑_B ε((𝔼θ𝒲_k(B))_a) + β_k·ε(F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅))`**
  (`gamRem2_split`).

The last factor is a **bulk** quantity: along the history (`ValidAt` below `n`, `Bulk2`)
`V'_k(Λ)_∅ = V_{κ'_k}(Λ) + r` (`kapH`), and `ε(F_C(ψ̄_aψ_a, 1)) = 0`, so it is
`ε(F_{C_k}(ψ̄_aψ_a, V_{κ'_k}(Λ)))` (`gamRem2_split_hist`). By the Wick formula
(`eps_FC_pbp`) it is the double contraction of `ψ̄_aψ_a` with the quadratic part of `V_{κ'}`:
`ε F_C(ψ̄_aψ_a, B) = ½∑_{x,y}C(x,a)C(a,y)(ε(∂_{ψ̄_x}∂_{ψ_y}B) - ε(∂_{ψ_y}∂_{ψ̄_x}B))`
(`ν'`- and gradient lines; the quartic part does not contribute).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

section Pure

variable {d L N : ℕ} [NeZero L]

/-- `loc^a_{X,Y}` preserves `ε` (`a ∈ Y ⊆ X`). -/
theorem eps_locA_two_mem {a : Lam d L N} {X Y : Finset (Lam d L N)} (hYX : Y ⊆ X) (haY : a ∈ Y)
    (F : Alg d L N) : ε (locA Obs.Case.two.toObs a X Y F) = ε F := by
  show ε (locEven {a} X Y F) = ε F
  rw [locEven_single_eq' haY hYX]
  simp [eps_pbp]

theorem eps_locA_two_pt (a : Lam d L N) (F : Alg d L N) :
    ε (locA Obs.Case.two.toObs a {a} {a} F) = ε F := by
  show ε (locEven {a} {a} {a} F) = ε F
  exact eps_locEven ⟨a, by simp⟩ F

/-- **`∑_{B ∈ 𝓑_j(X)} ε(loc^a_{X,B}F) = ε(F)`** for every nonempty `j`-polymer `X`. -/
theorem eps_sum_blocks {a : Lam d L N} {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hne : X.Nonempty) (F : Alg d L N) :
    ∑ b ∈ blocks j X, ε (locAp Obs.Case.two a X (blockSet j b) F) = ε F := by
  by_cases ha : a ∈ X
  · have h : ∀ b ∈ blocks j X, ε (locAp Obs.Case.two a X (blockSet j b) F) =
        if blk j a = b then ε F else 0 := by
      intro b hb
      rw [locAp_of_mem _ ha]
      split_ifs with h
      · exact eps_locA_two_mem (blockSet_subset_of_mem_blocks hX hb) (mem_blockSet.2 h) F
      · rw [locA_eq_zero _ (fun h' => h (mem_blockSet.1 h')), map_zero]
    rw [sum_congr rfl h, sum_ite_eq, if_pos (blk_mem_blocks ha)]
  · have h : ∀ b ∈ blocks j X, ε (locAp Obs.Case.two a X (blockSet j b) F) =
        ((blockSet (L := L) (N := N) j b).card : ℂ) / (X.card : ℂ) * ε F := by
      intro b _
      rw [locAp_of_not_mem _ ha, map_smul, eps_locA_two_pt, smul_eq_mul]
    rw [sum_congr rfl h, ← sum_mul, ← sum_div]
    have hc : ∑ b ∈ blocks j X, ((blockSet (L := L) (N := N) j b).card : ℂ) = (X.card : ℂ) := by
      rw [← Nat.cast_sum, ← card_biUnion (pairwiseDisjoint_blockSet j _), biUnion_blocks hX]
    rw [hc, div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 hne)), one_mul]

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N)

/-- **The localisation cancels in `ε`**: `∑_B ε(loc^a S(B_+)_a) = ∑_B ε(S(B)_a)`. -/
theorem eps_total_LS :
    ∑ b ∈ blockIdx (L := L) (N := N) j,
        ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam d L N)).a := by
  rw [← sum_blockIdx_succ j, ← sum_blockIdx_succ j]
  refine sum_congr rfl fun c' hc' => ?_
  have hne : (blockSet (L := L) (N := N) (j + 1) c').Nonempty := mem_blockIdx.1 hc'
  have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a) =
        ε (locAp Obs.Case.two P.a (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
          (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).a) := by
    intro b hb
    rw [Bp_eq_of_mem hb]
  rw [sum_congr rfl e, eps_sum_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hne,
    SXO, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum]

/-- `∑_B ε(S(B)_a) = ε(F_C(V'(Λ)_a, V'(Λ)_∅)) + ∑_B ε((𝔼θ𝒲(B))_a)`. -/
theorem eps_SbO_sum :
    ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam d L N)).a =
      ε (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).e) +
        ∑ b ∈ blockIdx (L := L) (N := N) j, ε (EthO C (W b) : SA .two (Lam d L N)).a := by
  rw [← map_sum, ← sum_a, ← AddSubmonoidClass.coe_finsetSum, SbO_sum, Subalgebra.coe_add,
    Subalgebra.coe_smul, add_a, smul_a, FCO_self_a, smul_smul, AddSubmonoidClass.coe_finsetSum,
    sum_a, map_add, map_sum]
  norm_num

/-- `ε(F_C(α + βψ̄_aψ_a, e)) = β·ε(F_C(ψ̄_aψ_a, e))`. -/
theorem eps_FC_loc2 {a : Lam d L N} {X : Alg d L N} (hX : Loc2Form a X) (e : Alg d L N) :
    ε (FC C X e) = mass2 X * ε (FC C (pbp a) e) := by
  obtain ⟨α, β, rfl⟩ := hX
  rw [mass2_loc, FC_add_left, Step2.FC_const_left, zero_add, FC_smul_left, map_smul, smul_eq_mul]

/-- **The second-order term**: `ε(F_C(V'(Λ)_a, e)) = β·ε(F_C(ψ̄_aψ_a, e))`, `β = ∑_Bm₂(V(B)_a)`. -/
theorem eps_FC_VprLO (hV : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) (e : Alg d L N) :
    ε (FC C (VprLO j C V : SA .two (Lam d L N)).a e) = betaTot2 j V * ε (FC C (pbp P.a) e) := by
  have hpr : ∀ b, (VprO C V b : SA .two (Lam d L N)).a = expLC C (V b : SA .two (Lam d L N)).a :=
    fun b => by
      have h0 := (EthO_comp C (V b)).2.1 true
      simp only [cmp_true] at h0
      rw [VprO, h0]
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_a, Step2.FC_sum_left, map_sum, betaTot2, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  rw [hpr b, eps_FC_loc2 C ((hV b).expLC C) e]
  obtain ⟨α, β, hb⟩ := hV b
  rw [hb, mass2_expLC_loc, mass2_loc]

/-- **The Wick formula for the `ε`-part**: `ε F_C(ψ̄_aψ_a, B)` is the double contraction of
`ψ̄_aψ_a` with the quadratic part of `B`. -/
theorem eps_FC_pbp (a : Lam d L N) (B : Alg d L N) :
    ε (FC C (pbp a) B) = (1 / 2 : ℂ) *
      (∑ y, C a y * ∑ x, C x a * ε (D (x, -1) (D (y, 1) B)) -
        ∑ x, C x a * ∑ y, C a y * ε (D (y, 1) (D (x, -1) B))) := by
  rw [pbp, FC_pbp', Xc_pbp, X2_pbp1]
  simp only [Xc_psi, Xc_psibar]
  simp only [map_add, map_sub, map_neg, map_sum, map_smul, map_mul,
    smul_eq_mul, eps_ψ, psibar, psi, zero_mul, mul_zero, sum_const_zero, neg_zero, sub_zero,
    zero_add, mul_neg, sum_neg_distrib, mul_sum]
  ring

end Pure

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- The observable (`K`, `𝒲`) part of `ρ_k`: `∑_Bε(e^{ℒ_C}Q_k(B)_a) + ∑_Bε((𝔼θ𝒲_k(B))_a)`. -/
def gamWK2 (k : ℕ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k,
      ε (expLC (histCovO R t k) (Q2O P k (histKO2 R P o₀ t k) b : SA .two (Lam 2 L N)).a) +
    ∑ b ∈ blockIdx (L := L) (N := N) k,
      ε (EthO (histCovO R t k) (histWO2 R P o₀ t k b) : SA .two (Lam 2 L N)).a

/-- **`ρ_k = (K, 𝒲 part) + β_k·ε(F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅))`** (exact). -/
theorem gamRem2_split (h0 : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a) (k : ℕ) :
    gamRem2 R P o₀ t k = gamWK2 R P o₀ t k +
      betaTot2 k (histVO2 R P o₀ t k) * ε (FC (histCovO R t k) (pbp P.a)
        (VprLO k (histCovO R t k) (histVO2 R P o₀ t k) : SA .two (Lam 2 L N)).e) := by
  unfold gamRem2 gamWK2
  rw [sum_add_distrib, eps_total_LS, eps_SbO_sum,
    eps_FC_VprLO P k _ _ (obsHist_hform2 R P o₀ t h0 k)]
  ring

/-- **Along the history**: the bulk factor is `ε(F_{C_k}(ψ̄_aψ_a, V_{κ'_k}(Λ)))` (`κ' = kapH`). -/
theorem gamRem2_split_hist {n : ℕ} (hV : ∀ i < n, ValidAt R i) (h₀ : o₀.IsObs)
    (h0 : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a) {k : ℕ} (hk : k < n) :
    gamRem2 R P o₀ t k = gamWK2 R P o₀ t k +
      betaTot2 k (histVO2 R P o₀ t k) *
        ε (FC (histCovO R t k) (pbp P.a) (Vcoup (kapH R t k) univ)) := by
  rw [gamRem2_split R P o₀ t h0]
  obtain ⟨r, hr⟩ := (bulk2_hist R P o₀ t hV h₀).he k hk
  have e : (VprLO k (histCovO R t k) (histVO2 R P o₀ t k) : SA .two (Lam 2 L N)).e =
      bulkE2 (histCovO R t) (histVO2 R P o₀ t) k := rfl
  rw [e, hr, FC_add_right, FC_smul_right, FC_one_right, smul_zero, add_zero]

end Hist

end

end Obs2
