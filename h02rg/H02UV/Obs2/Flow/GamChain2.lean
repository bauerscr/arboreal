import Obs2.Flow.MuHist2

/-!
# The Case-(2) `γ` flow: the accumulated observable constant `γ_{a,k} = -ε(u^{obs}_{k,a})`

Along the Case-(2) observable history (`σ_a` component, `V_k(B)_a = α_k(B) + c_k(B)ψ̄_aψ_a` by
`obsHist_hform2`), the observable constant of step `k` is
`u^{obs}_{k+1}(B)_a = ε(e^{ℒ_{C_k}}V_k(B)_a) - ε(e^{ℒ_{C_k}}Q_k(B)_a) - ε(loc^a S(B_+)_a)`, and
`ε(e^{ℒ_C}(α + βψ̄_aψ_a)) = α + βC(a,a)` (`eps_expLC_loc2`, from `expLC_pbp_eq`). Hence, exactly,

  **`γ_{a,k+1} = γ_{a,k} - ∑_Bε(V_k(B)_a) - β_k C_k(a,a) + ρ_k`** (`gamA_succ`),

with `β_k = betaTot2 = ∑_B m₂(V_k(B)_a) = -μ_{a,k}` (the coupling of `MuChain2`), and the remainder
`ρ_k = gamRem2 k = ∑_B (ε(e^{ℒ_{C_k}}Q_k(B)_a) + ε(loc^a S(B_+)_a))` (activity and second order:
`S(B)_a = F_C(V'_{B,a}, V'(Λ)_∅) + 𝔼θ𝒲(B)_a`). The constant parts vanish for `k ≥ 1`
(`epsTot2_succ`: `V_{k+1}` has no observable constant), and for `obsInit .two V P`
`∑_Bε(V_0(B)_a) = -γ_a` (`epsTot2_obsInit`).

The covariance `C_k = histCovO = stCov` is the dressed `Γ^{int}_{k+1}` itself (no `Z` factor,
`Step2.stCov_eq_dData`); the fields are not rescaled. So the linear term is exactly
`β_kΓ^{int}_{k+1}(a,a)` with `β_k = -μ_{a,k}`: the term `b_0λ̂_kΓ^{int}_{k+1}(0,0)` of `e:PM`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

section Pure

variable {d L N : ℕ} [NeZero L]

/-- `e^{ℒ_C}(ψ̄_aψ_a) = ψ̄_aψ_a + C(a,a)`. -/
theorem expLC_pbp_eq (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) :
    expLC C (pbp a) = pbp a + C a a • (1 : Alg d L N) := by
  have h : PM (ev ((a, 1) : Sf (Lam d L N))) (ev (a, -1)) :=
    ⟨fun y => by simp [ev, Prod.ext_iff], fun y => by simp [ev, Prod.ext_iff]⟩
  have e : pbp a = -(ψ (a, 1) * ψ (a, -1) : Alg d L N) := by
    unfold pbp psibar psi; exact ψ_anticomm _ _
  rw [e, map_neg]
  have := expLC_two C h
  simp only [ψ] at this ⊢
  rw [this, neg_add, neg_smul, neg_neg, pairC_ev]

/-- **`ε(e^{ℒ_C}F) = ε(F) + m₂(F)C(a,a)`** for `F = α + βψ̄_aψ_a`. -/
theorem eps_expLC_loc2 {a : Lam d L N} {F : Alg d L N} (hF : Loc2Form a F)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) :
    ε (expLC C F) = ε F + mass2 F * C a a := by
  obtain ⟨α, β, rfl⟩ := hF
  rw [mass2_loc, map_add, map_smul, map_smul, expLC_one', expLC_pbp_eq]
  simp only [map_add, map_smul, map_one, eps_pbp, smul_eq_mul]
  ring

/-- The `σ_a` part of the observable constant of a block: `ε((u+V)_{j+1}(B)_a)`. -/
theorem upO_a (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (K : OAct .two d L N) (b : Fin d → ℕ) :
    (upO P j C V W K b : SA .two (Lam d L N)).a =
      algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .two (Lam d L N)).a) := by
  show cmp true (πobs (epsO (uVpO P j C V W K b)) : SA .two (Lam d L N)) = _
  rw [cmp_πobs]; rfl

/-- `(u+V)_{j+1}(B)_a = e^{ℒ_C}V(B)_a - e^{ℒ_C}Q(B)_a - loc^a S(B_+)_a`. -/
theorem uVpO_a (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (K : OAct .two d L N) (b : Fin d → ℕ) :
    (uVpO P j C V W K b : SA .two (Lam d L N)).a =
      expLC C (V b : SA .two (Lam d L N)).a - expLC C (Q2O P j K b : SA .two (Lam d L N)).a -
        locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a := by
  have h2 : (uVpO P j C V W K b : SA .two (Lam d L N)).a =
      (VprO C V b : SA .two (Lam d L N)).a - (EthO C (Q2O P j K b) : SA .two (Lam d L N)).a -
        (LSO P j C V W b : SA .two (Lam d L N)).a := rfl
  rw [h2, VprO, EthO_eq_expO, EthO_eq_expO]; rfl

/-- **`V_{j+1}(B)` has no observable constant**: `ε(V_{j+1}(B)_a) = 0`. -/
theorem eps_VpO_a (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (K : OAct .two d L N) (b : Fin d → ℕ) :
    ε (VpO P j C V W K b : SA .two (Lam d L N)).a = 0 := by
  have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).a = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
  have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).a =
      (uVpO P j C V W K b : SA .two (Lam d L N)).a -
        ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).a - (upO P j C V W K b : SA .two (Lam d L N)).a := rfl
  rw [h1, halg, upO_a, sub_zero, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, sub_self]

end Pure

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- `γ_{a,k} = -ε(u^{obs}_{k,a})`, the accumulated observable constant. -/
def gamA (k : ℕ) : ℂ := -ε ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).a

/-- The observable constant part of `V_k`: `∑_Bε(V_k(B)_a)`. -/
def epsTot2 (k : ℕ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k, ε (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).a

/-- **The remainder of the `γ` flow**: `ρ_k = ∑_B (ε(e^{ℒ_{C_k}}Q_k(B)_a) + ε(loc^a S(B_+)_a))`. -/
def gamRem2 (k : ℕ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k,
    (ε (expLC (histCovO R t k) (Q2O P k (histKO2 R P o₀ t k) b : SA .two (Lam 2 L N)).a) +
      ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) k b)
        (blockSet (L := L) (N := N) k b)
        (SXO k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
          (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).a))

/-- **The exact `γ` flow**: `γ_{k+1} = γ_k - ∑_Bε(V_k(B)_a) - β_kC_k(a,a) + ρ_k`. -/
theorem gamA_succ (h0 : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a) (k : ℕ) :
    gamA R P o₀ t (k + 1) = gamA R P o₀ t k - epsTot2 R P o₀ t k -
      betaTot2 k (histVO2 R P o₀ t k) * histCovO R t k P.a P.a + gamRem2 R P o₀ t k := by
  have hu : ((obsHist R P o₀ (k + 1) t).u : SA .two (Lam 2 L N)).a =
      ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).a +
        ∑ b ∈ blockIdx (L := L) (N := N) k, (upO P k (histCovO R t k) (histVO2 R P o₀ t k)
          (histWO2 R P o₀ t k) (histKO2 R P o₀ t k) b : SA .two (Lam 2 L N)).a := by
    rw [obsHist_succ]
    show ((obsHist R P o₀ k t).u + uObsTot P k (histCovO R t k) (histVO2 R P o₀ t k)
      (histWO2 R P o₀ t k) (histKO2 R P o₀ t k) : SA .two (Lam 2 L N)).a = _
    rw [uObsTot, add_a, AddSubmonoidClass.coe_finsetSum, sum_a]
  unfold gamA epsTot2 gamRem2 betaTot2
  rw [hu, map_add, map_sum]
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      ε (upO P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
        (histKO2 R P o₀ t k) b : SA .two (Lam 2 L N)).a =
      ε (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).a +
        mass2 (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).a * histCovO R t k P.a P.a -
        (ε (expLC (histCovO R t k) (Q2O P k (histKO2 R P o₀ t k) b : SA .two (Lam 2 L N)).a) +
          ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) k b)
            (blockSet (L := L) (N := N) k b)
            (SXO k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
              (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).a)) := by
    intro b _
    rw [upO_a, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, uVpO_a, map_sub,
      map_sub, eps_expLC_loc2 (obsHist_hform2 R P o₀ t h0 k b)]
    ring
  rw [sum_congr rfl hb, sum_sub_distrib, sum_add_distrib, ← sum_mul]
  ring

/-- `∑_Bε(V_{k+1}(B)_a) = 0`. -/
theorem epsTot2_succ (k : ℕ) : epsTot2 R P o₀ t (k + 1) = 0 := by
  unfold epsTot2
  refine sum_eq_zero fun c' _ => ?_
  rw [histVO2_succ_a, Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum]
  exact sum_eq_zero fun b _ => eps_VpO_a _ _ _ _ _ _ _

/-- `γ_{a,0} = 0` for `obsInit`. -/
theorem gamA_obsInit_zero (V : OCoup .two) : gamA R P (obsInit .two V P) t 0 = 0 := by
  unfold gamA
  show -ε ((0 : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = 0
  simp

/-- **`∑_Bε(V_0(B)_a) = -γ_a`** for the initial state `obsInit .two V P`. -/
theorem epsTot2_obsInit (V : OCoup .two) :
    epsTot2 R P (obsInit .two V P) t 0 = -OCoup2.ga V := by
  classical
  unfold epsTot2
  have h : ∀ b, ε (histVO2 R P (obsInit .two V P) t 0 b : SA .two (Lam 2 L N)).a =
      if blk (L := L) (N := N) 0 P.a = b then -OCoup2.ga V else 0 := by
    intro b
    rw [histVO2_a]
    show ε (((obsInit .two V P).V b : SA .two (Lam 2 L N)).a) = _
    rw [obsInit_two_a, map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, map_smul, show ε (psibar P.a * psi P.a : Alg 2 L N) = 0 from eps_pbp P.a]
    by_cases hb : blk (L := L) (N := N) 0 P.a = b
    · rw [if_pos hb, ind_pos (mem_blockSet.2 hb)]; simp
    · rw [if_neg hb, ind_neg (fun h => hb (mem_blockSet.1 h))]; simp
  rw [sum_congr rfl fun b _ => h b, sum_ite_eq, if_pos]
  exact mem_blockIdx.2 ⟨P.a, mem_blockSet_blk 0 P.a⟩

end Hist

end

end Obs2
