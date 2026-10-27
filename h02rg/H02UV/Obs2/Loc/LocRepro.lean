import Obs2.Loc.LocT

/-!
# `Loc_{X,X}` reproduces the observable couplings (`lem:loc-obs2`, last sentence)

* `locABtX_one`, `locABtX_m2`, `locABtX_m4`: the barycentric two-point operator with the base
  point switch (`Obs2.locABtX`) reproduces `1`, `ψ̄_uψ_v` (`u, v ∈ {a, b}`) and
  `ψ̄_aψ_aψ̄_bψ_b` if `a ∈ X` or `b ∈ X` (and `a ≠ b`);
* **`LocO2_evalO`**: for `a, b ∈ X`, `a ≠ b`, `Loc_{X,X}(u^{obs} + V^{obs})(X) = (u^{obs} + V^{obs})(X)`
  for the couplings of both cases (`Obs2.evalO`): the observable couplings
  `μ, γ, q, η, r, χ` are fixed points of the localisation.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step LocObs

variable {d L N : ℕ} [NeZero L]

theorem locABtX_one {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X) :
    locABtX X a b (1 : Alg d L N) = 1 := by
  by_cases ha : a ∈ X
  · rw [locABtX_of_mem b ha, locABt_one ha]
  · rw [locABtX_of_not_mem b ha, locABt_one (h.resolve_left ha)]

theorem locABtX_m2 {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X) (hab : a ≠ b)
    {u v : Lam d L N} (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) :
    locABtX X a b (psibar u * psi v) = psibar u * psi v := by
  by_cases ha : a ∈ X
  · rw [locABtX_of_mem b ha, locABt_m2 ha hab hu hv]
  · rw [locABtX_of_not_mem b ha, locABt_m2 (h.resolve_left ha) (Ne.symm hab) hu.symm hv.symm]

theorem locABtX_m4 {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X)
    (hab : a ≠ b) : locABtX X a b (m4 a b) = m4 a b := by
  by_cases ha : a ∈ X
  · rw [locABtX_of_mem b ha, locABt_m4 ha hab]
  · rw [locABtX_of_not_mem b ha, m4_comm, locABt_m4 (h.resolve_left ha) (Ne.symm hab)]

theorem locABtX_algebraMap {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X)
    (r : ℂ) : locABtX X a b (algebraMap ℂ (Alg d L N) r) = algebraMap ℂ (Alg d L N) r := by
  rw [Algebra.algebraMap_eq_smul_one, locABtX_smul, locABtX_one h]

theorem locABtX_nn {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X) (hab : a ≠ b) :
    locABtX X a b (nn a b) = nn a b := by
  rw [nn, locABtX_add, locABtX_m2 h hab (Or.inl rfl) (Or.inl rfl),
    locABtX_m2 h hab (Or.inr rfl) (Or.inr rfl)]

theorem locABtX_nx {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X) (hab : a ≠ b) :
    locABtX X a b (nx a b) = nx a b := by
  rw [nx, locABtX_add, locABtX_m2 h hab (Or.inl rfl) (Or.inr rfl),
    locABtX_m2 h hab (Or.inr rfl) (Or.inl rfl)]

theorem locABtX_sub (X : Finset (Lam d L N)) (a b : Lam d L N) (F G : Alg d L N) :
    locABtX X a b (F - G) = locABtX X a b F - locABtX X a b G := by
  rw [sub_eq_add_neg, locABtX_add, ← neg_one_smul ℂ G, locABtX_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem eps_pbp (z : Lam d L N) : ε (pbp z) = 0 := by simp [pbp, psibar, psi, ψ]

theorem locEven_loc_self {a : Lam d L N} {X : Finset (Lam d L N)} (ha : a ∈ X) (α β : ℂ) :
    locEven {a} X X (algebraMap ℂ (Alg d L N) α - β • (psibar a * psi a)) =
      algebraMap ℂ (Alg d L N) α - β • (psibar a * psi a) := by
  rw [locEven_singleton_eq ha]
  have e : (algebraMap ℂ (Alg d L N) α - β • (psibar a * psi a)) =
      α • (1 : Alg d L N) + (-β) • pbp a := by
    rw [Algebra.algebraMap_eq_smul_one, pbp, neg_smul, sub_eq_add_neg]
  rw [e, map_add, map_smul, map_smul, map_one, eps_pbp, mass2_add, mass2_smul, mass2_smul,
    mass2_one, mass2_pbp]
  simp

/-- **`Loc_{X,X}` reproduces the observable couplings** (`a, b ∈ X`, `a ≠ b`). -/
theorem LocO2_evalO (c : Obs.Case) (P : ObsPts d L N) {X : Finset (Lam d L N)} (ha : P.a ∈ X)
    (hb : P.b ∈ X) (hab : P.a ≠ P.b) (V : OCoup c) :
    LocO2 P X X (evalO c V P.a P.b X) = evalO c V P.a P.b X := by
  have hne : (X ∩ P.pts).Nonempty := ⟨P.a, mem_inter.2 ⟨ha, by simp [ObsPts.pts]⟩⟩
  have hX : P.a ∈ X ∨ P.b ∈ X := Or.inl ha
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · show ((Step2.Loc2E X X (bulk (evalO c V P.a P.b X)) : Alg d L N)) = (evalS c V P.a P.b X).e
    rw [bulk_evalO, evalS_e]
    simpa using congrArg Subtype.val (Step2.Loc2E_smul X X 0 0)
  · show locAp c P.a X X (evalS c V P.a P.b X).a = (evalS c V P.a P.b X).a
    rw [locAp_of_mem X ha]
    cases c
    · show locOdd (-1) {P.a} X X (ind (P.a ∈ X) • (-OCoup1.mua V • psibar P.a)) = _
      rw [locOdd_single_self, if_pos ha, ind_pos ha, one_smul, mass1_smul, mass1_psibar, mul_one]
      show _ = ind (P.a ∈ X) • _
      rw [ind_pos ha, one_smul]; rfl
    · show locEven {P.a} X X (ind (P.a ∈ X) • (algebraMap ℂ (Grassmann.N (Lam d L N)) (-OCoup2.ga V) -
        OCoup2.mua V • (psibar P.a * psi P.a))) = _
      rw [ind_pos ha, one_smul, locEven_loc_self ha]
      show _ = ind (P.a ∈ X) • _
      rw [ind_pos ha, one_smul]
  · show locBp c P.b X X (evalS c V P.a P.b X).b = (evalS c V P.a P.b X).b
    rw [locBp_of_mem X hb]
    cases c
    · show locOdd 1 {P.b} X X (ind (P.b ∈ X) • (OCoup1.mub V • psi P.b)) = _
      rw [locOdd_single_self, if_pos hb, ind_pos hb, one_smul, mass1_smul, mass1_psi, mul_one]
      show _ = ind (P.b ∈ X) • _
      rw [ind_pos hb, one_smul]; rfl
    · show locEven {P.b} X X (ind (P.b ∈ X) • (algebraMap ℂ (Grassmann.N (Lam d L N)) (-OCoup2.gb V) -
        OCoup2.mub V • (psibar P.b * psi P.b))) = _
      rw [ind_pos hb, one_smul, locEven_loc_self hb]
      show _ = ind (P.b ∈ X) • _
      rw [ind_pos hb, one_smul]
  · show locABtXY P X X (evalS c V P.a P.b X).ab = (evalS c V P.a P.b X).ab
    rw [locABtXY_self P X hne]
    cases c
    · show locABtX X P.a P.b (ind (P.a ∈ X ∧ P.b ∈ X) • (algebraMap ℂ (Grassmann.N (Lam d L N))
        (-OCoup1.q V) + (OCoup1.r V / 2) • nn P.a P.b + OCoup1.chi V • m4 P.a P.b)) = _
      rw [locABtX_smul, locABtX_add, locABtX_add, locABtX_smul, locABtX_smul,
        locABtX_algebraMap hX, locABtX_nn hX hab, locABtX_m4 hX hab]
      rfl
    · show locABtX X P.a P.b (ind (P.a ∈ X ∧ P.b ∈ X) • (algebraMap ℂ (Grassmann.N (Lam d L N))
        (-OCoup2.q V) - (OCoup2.eta V / 2) • nx P.a P.b + (OCoup2.r V / 2) • nn P.a P.b +
          OCoup2.chi V • m4 P.a P.b)) = _
      rw [locABtX_smul, locABtX_add, locABtX_add, locABtX_sub, locABtX_smul, locABtX_smul,
        locABtX_smul, locABtX_algebraMap hX, locABtX_nx hX hab, locABtX_nn hX hab,
        locABtX_m4 hX hab]
      rfl

end

end Obs2
