import Obs2.Flow.MuChain2
import Obs2.Flow.MuHist

/-!
# The `μ^{(2)}` flow along the observable history: `MuChain2` instantiated (Case (2))

* `Loc2Form a F`: `F = α + βψ̄_aψ_a`; it is preserved by `e^{ℒ_C}`, `loc^a` (Case (2),
  `locAp_two_form`, every polymer), constants, sums: `VpO_a_two_form`, `Vnext2O_a_two_form`;
* `histVO2`, `histWO2`, `histKO2`: the full inputs of step `k` of the Case-(2) history;
* **`muChain2_obsHist`**: the bundle `MuChain2` holds along every history for `n < N`, for every
  initial state with `𝒲_0(B)_a = 0` and `V_0(B)_a` of the form `α + βψ̄_aψ_a` (no validity
  condition on the bulk flow is needed: `frakN2` is defined with the actual bulk part);
* `obsInit_two_form`, `obsInit_two_W`, **`betaTot2_obsInit`**: for the initial state
  `obsInit .two V P`, `β_0 = ∑_B m₂(V_0(B)_a) = -μ_a` (`V.mua`), so
  `betaTot2_k/betaTot2_0 = μ_{a,k}/μ_{a,0}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD Flow2

/-! ### The local form `α + βψ̄_aψ_a` is preserved (Case (2)) -/

section Form

variable {d L N : ℕ} [NeZero L] (P : ObsPts d L N) (j : ℕ)
  (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam .two d L N) (K : OAct .two d L N)

/-- `F = α + βψ̄_aψ_a`. -/
def Loc2Form (a : Lam d L N) (F : Alg d L N) : Prop :=
  ∃ α β : ℂ, F = α • (1 : Alg d L N) + β • pbp a

theorem Loc2Form.zero (a : Lam d L N) : Loc2Form a (0 : Alg d L N) := ⟨0, 0, by simp⟩

theorem Loc2Form.sub {a : Lam d L N} {F G : Alg d L N} (hF : Loc2Form a F) (hG : Loc2Form a G) :
    Loc2Form a (F - G) := by
  obtain ⟨α, β, rfl⟩ := hF
  obtain ⟨α', β', rfl⟩ := hG
  exact ⟨α - α', β - β', by rw [sub_smul, sub_smul]; abel⟩

theorem Loc2Form.add {a : Lam d L N} {F G : Alg d L N} (hF : Loc2Form a F) (hG : Loc2Form a G) :
    Loc2Form a (F + G) := by
  obtain ⟨α, β, rfl⟩ := hF
  obtain ⟨α', β', rfl⟩ := hG
  exact ⟨α + α', β + β', by rw [add_smul, add_smul]; abel⟩

theorem Loc2Form.sum {a : Lam d L N} {ι : Type*} (s : Finset ι) {F : ι → Alg d L N}
    (h : ∀ i ∈ s, Loc2Form a (F i)) : Loc2Form a (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Loc2Form.zero a
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun k hk => h k (mem_insert_of_mem hk))

theorem Loc2Form.expLC {a : Lam d L N} {F : Alg d L N} (hF : Loc2Form a F)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : Loc2Form a (Grassmann.expLC Γ F) := by
  obtain ⟨α, β, rfl⟩ := hF
  obtain ⟨α', h⟩ := expLC_loc2 Γ α β a
  exact ⟨α', β, h⟩

theorem Loc2Form.alg (a : Lam d L N) (r : ℂ) : Loc2Form a (algebraMap ℂ (Alg d L N) r) :=
  ⟨r, 0, by rw [Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]⟩

theorem Loc2Form.eq_mass2 {a : Lam d L N} {F : Alg d L N} (hF : Loc2Form a F) :
    ∃ α : ℂ, F = α • (1 : Alg d L N) + mass2 F • pbp a := by
  obtain ⟨α, β, rfl⟩ := hF
  exact ⟨α, by rw [mass2_loc]⟩

theorem locAp_two_loc2 (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Loc2Form P.a (locAp Obs.Case.two P.a X Y F) := by
  obtain ⟨r, s, hr⟩ := locAp_two_form P.a X Y F
  exact ⟨r, s, hr⟩

theorem Q2O_a_two_loc2 (b : Fin d → ℕ) :
    Loc2Form P.a (Q2O P j K b : SA .two (Lam d L N)).a := by
  classical
  unfold Q2O
  split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum, sum_a]
    exact Loc2Form.sum _ fun X _ => locAp_two_loc2 P X _ _
  · exact Loc2Form.zero _

/-- **`V_{j+1}(B)_a = α + βψ̄_aψ_a` for every block** (Case (2)). -/
theorem VpO_a_two_form (b : Fin d → ℕ) (hV : Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    Loc2Form P.a (VpO P j C V W K b : SA .two (Lam d L N)).a := by
  have e : (VpO P j C V W K b : SA .two (Lam d L N)).a =
      expLC C (V b : SA .two (Lam d L N)).a -
        expLC C (Q2O P j K b : SA .two (Lam d L N)).a -
        locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a -
        0 - algebraMap ℂ (Alg d L N)
          (ε (uVpO P j C V W K b : SA .two (Lam d L N)).a) := by
    have hup : (upO P j C V W K b : SA .two (Lam d L N)).a =
        algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .two (Lam d L N)).a) := by
      show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA .two (Lam d L N)) = _
      rw [cmp_πobs]; rfl
    have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).a = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
    have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).a =
        (uVpO P j C V W K b : SA .two (Lam d L N)).a -
          ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
            SA .two (Lam d L N)).a - (upO P j C V W K b : SA .two (Lam d L N)).a := rfl
    have h2 : (uVpO P j C V W K b : SA .two (Lam d L N)).a =
        (VprO C V b : SA .two (Lam d L N)).a - (EthO C (Q2O P j K b) : SA .two (Lam d L N)).a -
          (LSO P j C V W b : SA .two (Lam d L N)).a := rfl
    rw [h1, halg, hup, h2, VprO, EthO_eq_expO, EthO_eq_expO]; rfl
  rw [e]
  exact ((((hV.expLC C).sub ((Q2O_a_two_loc2 P j K b).expLC C)).sub
    (locAp_two_loc2 P _ _ _)).sub (Loc2Form.zero _)).sub (Loc2Form.alg _ _)

theorem Vnext2O_a_two_form (c' : Fin d → ℕ)
    (hV : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    Loc2Form P.a (Vnext2O P j C V W K c' : SA .two (Lam d L N)).a := by
  rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a]
  exact Loc2Form.sum _ fun b _ => VpO_a_two_form P j C V W K b (hV b)

end Form

/-! ### Along the history -/

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R)) {n : ℕ}

/-- The full `V♭_k + V^{obs}_k` along the Case-(2) history. -/
def histVO2 (k : ℕ) : OFam .two 2 L N :=
  fullV R k (rawHist R k t) (t k).1 (t k).2.1 (obsHist R P o₀ k t)

/-- The full `𝒲_k + 𝒲^{obs}_k` along the Case-(2) history. -/
def histWO2 (k : ℕ) : OFam .two 2 L N :=
  fullW (rawHist R k t) (rawD R (rawHist R k t).u (t k).2.2) (obsHist R P o₀ k t)

/-- The full `K♭_k + K^{obs,♭}_k` along the Case-(2) history. -/
def histKO2 (k : ℕ) : OAct .two 2 L N :=
  fullK R k (rawHist R k t) (rawK R (rawHist R k t).u (t k).2.2) (obsHist R P o₀ k t)

theorem histVO2_a (k : ℕ) (b : Fin 2 → ℕ) :
    (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).a =
      ((obsHist R P o₀ k t).V b : SA .two (Lam 2 L N)).a :=
  emb_add_cmp true _ _

theorem histWO2_a (k : ℕ) (b : Fin 2 → ℕ) :
    (histWO2 R P o₀ t k b : SA .two (Lam 2 L N)).a =
      ((obsHist R P o₀ k t).W b : SA .two (Lam 2 L N)).a :=
  emb_add_cmp true _ _

theorem histVO2_succ_a (k : ℕ) (c' : Fin 2 → ℕ) :
    (histVO2 R P o₀ t (k + 1) c' : SA .two (Lam 2 L N)).a =
      (Vnext2O P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
        (histKO2 R P o₀ t k) c' : SA .two (Lam 2 L N)).a := by
  rw [histVO2_a, obsHist_succ]
  exact piobs_cmp true _

theorem histWO2_succ_a (k : ℕ) (c' : Fin 2 → ℕ) :
    (histWO2 R P o₀ t (k + 1) c' : SA .two (Lam 2 L N)).a =
      (Wnext2O P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) c' :
        SA .two (Lam 2 L N)).a := by
  rw [histWO2_a, obsHist_succ]
  exact piobs_cmp true _

/-- **`V_k(B)_a = α + βψ̄_aψ_a` at every scale** of the Case-(2) history. -/
theorem obsHist_hform2 (h0 : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a) :
    ∀ k b, Loc2Form P.a (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).a
  | 0, b => by rw [histVO2_a]; exact h0 b
  | k + 1, b => by
    rw [histVO2_succ_a]
    exact Vnext2O_a_two_form P k _ _ _ _ b (obsHist_hform2 h0 k)

/-- **`MuChain2` along the history** (Case (2)). -/
theorem muChain2_obsHist (hN : n < N) (hW0 : ∀ b, (o₀.W b : SA .two (Lam 2 L N)).a = 0)
    (hV0 : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a) :
    MuChain2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) (histKO2 R P o₀ t) n where
  hN := hN
  hW0 b := by rw [histWO2_a]; exact hW0 b
  hW k _ c' := histWO2_succ_a R P o₀ t k c'
  hV k _ c' := histVO2_succ_a R P o₀ t k c'
  hform k _ b := (obsHist_hform2 R P o₀ t hV0 k b).eq_mass2

/-! ### The initial state `obsInit .two V P` -/

theorem obsInit_two_a (V : OCoup .two) (b : Fin 2 → ℕ) :
    ((obsInit .two V P).V b : SA .two (Lam 2 L N)).a =
      ind (P.a ∈ blockSet (L := L) (N := N) 0 b) •
        (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-OCoup2.ga V) -
          OCoup2.mua V • (psibar P.a * psi P.a)) := rfl

theorem obsInit_two_form (V : OCoup .two) (b : Fin 2 → ℕ) :
    Loc2Form P.a ((obsInit .two V P).V b : SA .two (Lam 2 L N)).a := by
  rw [obsInit_two_a]
  refine ⟨ind (P.a ∈ blockSet (L := L) (N := N) 0 b) * (-OCoup2.ga V),
    ind (P.a ∈ blockSet (L := L) (N := N) 0 b) * (-OCoup2.mua V), ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, pbp]
  module

theorem obsInit_two_W (V : OCoup .two) (b : Fin 2 → ℕ) :
    ((obsInit .two V P).W b : SA .two (Lam 2 L N)).a = 0 := rfl

/-- **`β_0 = -μ_a`** for the initial state `obsInit .two V P`. -/
theorem betaTot2_obsInit (V : OCoup .two) :
    betaTot2 (L := L) (N := N) 0 (histVO2 R P (obsInit .two V P) t 0) = -OCoup2.mua V := by
  classical
  unfold betaTot2
  have h : ∀ b, mass2 (histVO2 R P (obsInit .two V P) t 0 b : SA .two (Lam 2 L N)).a =
      if blk (L := L) (N := N) 0 P.a = b then -OCoup2.mua V else 0 := by
    intro b
    rw [histVO2_a]
    show mass2 (((obsInit .two V P).V b : SA .two (Lam 2 L N)).a) = _
    rw [obsInit_two_a, mass2_smul, mass2_sub, mass2_algebraMap, mass2_smul]
    have hp : mass2 (psibar P.a * psi P.a : Alg 2 L N) = 1 := mass2_pbp P.a
    rw [hp]
    by_cases hb : blk (L := L) (N := N) 0 P.a = b
    · rw [if_pos hb, ind_pos (mem_blockSet.2 hb)]; ring
    · rw [if_neg hb, ind_neg (fun h => hb (mem_blockSet.1 h))]; ring
  rw [sum_congr rfl fun b _ => h b, sum_ite_eq, if_pos]
  exact mem_blockIdx.2 ⟨P.a, mem_blockSet_blk 0 P.a⟩

end Hist

end

end Obs2
