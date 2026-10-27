import Obs2.Map.Supp

/-!
# The one-source projections `F ↦ F_∅ + σ_a F_i` commute with the map (Case (2))

In Case (2) (`τ = id`, `s = 1`) the products of the `σ_a`- and `σ_b`-components have the same form:
`(FG)_i = F_∅G_i + F_iG_∅`. Hence, for `i ∈ {a, b}`,

  `prjO i : F_∅ + σ_aF_a + σ_bF_b + σ_aσ_bF_{ab} ↦ F_∅ + σ_aF_i`

is an algebra endomorphism of `OE .two Λ` (`prjS`, `prjO`). It commutes with every primitive of the
map with sources (`θ`, the inclusion, `𝔼_C`, `e^{ℒ_C}`, `ε`, `π_obs`, `e^{·}`, `emb`, `bulk`), and
**`prjO_LocO2`**: `prjO i ∘ Loc^P_{X,Y} = Loc^{P'}_{X,Y} ∘ prjO i` whenever `P'.a = P.pt i` (in Case
(2) the pointed `loc^a` and `loc^b` are the same operator `locEven {·}`, `locBp_two_eq_locAp`; the
`b`, `ab` components of `prjO i F` vanish, so `loc^b`, `loc^{ab}` of `P'` play no role).

Consequently (`prj_*`) every map of `Obs2.Map.Map` commutes with `prjO i`, with the observable points
changed from `P` to any `P'` with `P'.a = P.pt i` (for `i = true`, `P' = P`). For `i = false` this
is the `a ↔ b` mirror: the `σ_b` part of the flow with points `(a, b)` is the `σ_a` part of the flow
with points `(b, ·)`. The step and the history are in `Obs2/Map/SwapHist.lean`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux

/-! ### The projection -/

section Alg

variable {Λ : Type*} [DecidableEq Λ]

/-- `F ↦ F_∅ + σ_aF_i` on the Case-(2) algebra with sources. -/
def prjS (i : Bool) : SA .two Λ →ₐ[ℂ] SA .two Λ where
  toFun F := ⟨F.e, cmp i F, 0, 0⟩
  map_one' := by cases i <;> rfl
  map_mul' F G := by
    cases i <;> refine SA.ext ?_ ?_ ?_ ?_ <;> simp [cmp, Obs.Case.tau]
  map_zero' := by cases i <;> rfl
  map_add' F G := by cases i <;> refine SA.ext ?_ ?_ ?_ ?_ <;> simp [cmp]
  commutes' r := by cases i <;> refine SA.ext ?_ ?_ ?_ ?_ <;> simp [cmp]

@[simp] theorem prjS_e (i : Bool) (F : SA .two Λ) : (prjS i F).e = F.e := rfl
@[simp] theorem prjS_a (i : Bool) (F : SA .two Λ) : (prjS i F).a = cmp i F := rfl
@[simp] theorem prjS_b (i : Bool) (F : SA .two Λ) : (prjS i F).b = 0 := rfl
@[simp] theorem prjS_ab (i : Bool) (F : SA .two Λ) : (prjS i F).ab = 0 := rfl

theorem prjS_mem (i : Bool) (F : OE .two Λ) : prjS i (F : SA .two Λ) ∈ OEv .two Λ := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_OEv.1 F.2
  refine mem_OEv.2 ⟨h1, ?_, ?_, ?_⟩
  · cases i
    · exact h3
    · exact h2
  · simp
  · simp

/-- `F ↦ F_∅ + σ_aF_i` on even elements. -/
def prjO (i : Bool) : OE .two Λ →ₐ[ℂ] OE .two Λ :=
  ((prjS i).comp (OEv .two Λ).val).codRestrict (OEv .two Λ) fun F => prjS_mem i F

@[simp] theorem coe_prjO (i : Bool) (F : OE .two Λ) :
    (prjO i F : SA .two Λ) = prjS i (F : SA .two Λ) := rfl

theorem bulk_prjO (i : Bool) (F : OE .two Λ) : bulk (prjO i F) = bulk F := rfl

theorem prjO_emb (i : Bool) (x : Step.EvR Λ) : prjO i (emb x : OE .two Λ) = emb x := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> cases i <;> simp [cmp]

theorem prjO_πobs (i : Bool) (F : OE .two Λ) : prjO i (πobs F) = πobs (prjO i F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> cases i <;> simp [cmp, piobs_apply]

theorem prjO_epsO (i : Bool) (F : OE .two Λ) : prjO i (epsO F) = epsO (prjO i F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> cases i <;> simp [cmp]

theorem prjO_thetaO (i : Bool) (F : OE .two Λ) : prjO i (thetaO F) = thetaO (prjO i F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> cases i <;> simp [cmp]

theorem prjO_inclO (i : Bool) (F : OE .two Λ) : prjO i (inclO F) = inclO (prjO i F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> cases i <;> simp [cmp]

variable [Fintype Λ]

theorem prjO_isNilpotent_iff (i : Bool) (F : OE .two Λ) :
    IsNilpotent (prjO i F) ↔ IsNilpotent F := by
  constructor
  · intro h
    exact isNilpotent_of_bulk (by rw [← bulk_prjO i F]; exact h.map bulk)
  · intro h; exact h.map _

theorem prjO_oexp (i : Bool) (F : OE .two Λ) : prjO i (oexp F) = oexp (prjO i F) := by
  by_cases h : IsNilpotent F
  · unfold oexp; exact IsNilpotent.map_exp h (prjO i)
  · have h' : ¬ IsNilpotent (prjO i F) := fun h'' => h ((prjO_isNilpotent_iff i F).1 h'')
    rw [oexp, oexp, nilExp_of_not h, nilExp_of_not h', map_zero]

theorem prjO_expU (i : Bool) (x : ℂ) (F : OE .two Λ) : prjO i (expU x F) = expU x (prjO i F) := by
  rw [expU, expU, map_smul, prjO_oexp]


theorem prjO_ECCO (i : Bool) (C : Matrix Λ Λ ℂ) (F : OE .two (Λ ⊕ Λ)) :
    prjO i (ECCO C F) = ECCO C (prjO i F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> cases i <;> simp [cmp]

theorem prjO_expO (i : Bool) (C : Matrix Λ Λ ℂ) (F : OE .two Λ) :
    prjO i (expO C F) = expO C (prjO i F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> cases i <;> simp [cmp]

theorem prjO_EthO (i : Bool) (C : Matrix Λ Λ ℂ) (F : OE .two Λ) :
    prjO i (EthO C F) = EthO C (prjO i F) := by
  rw [EthO, EthO, prjO_ECCO, prjO_thetaO]

theorem prjO_FCO (i : Bool) (C : Matrix Λ Λ ℂ) (A B : OE .two Λ) :
    prjO i (FCO C A B) = FCO C (prjO i A) (prjO i B) := by
  simp only [FCO, map_sub, map_mul, prjO_expO]

end Alg

/-- The projection of a family. -/
def prjF {Λ ι : Type*} [DecidableEq Λ] (i : Bool) (F : ι → OE .two Λ) : ι → OE .two Λ :=
  fun x => prjO i (F x)

@[simp] theorem prjF_apply {Λ ι : Type*} [DecidableEq Λ] (i : Bool) (F : ι → OE .two Λ) (x : ι) :
    prjF i F x = prjO i (F x) := rfl

/-! ### `Loc` -/

section LocSw

variable {d L N : ℕ} [NeZero L]

theorem locBp_two_eq_locAp (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locBp Obs.Case.two b X Y F = locAp Obs.Case.two b X Y F := by
  by_cases h : b ∈ X
  · rw [locBp_two_of_mem Y h, locAp_two_of_mem Y h]
  · rw [locBp_of_not_mem Y h, locAp_two_of_not_mem Y h,
      ← locBp_of_mem (c := Obs.Case.two) {b} (mem_singleton_self b),
      locBp_two_of_mem _ (mem_singleton_self b)]

/-- **`prjO i ∘ Loc^P = Loc^{P'} ∘ prjO i`** for `P'.a = P.pt i`. -/
theorem prjO_LocO2 (i : Bool) {P P' : ObsPts d L N} (hP : P'.a = P.pt i)
    (X Y : Finset (Lam d L N)) (F : OE .two (Lam d L N)) :
    prjO i (LocO2 P X Y F) = LocO2 P' X Y (prjO i F) := by
  apply Subtype.ext
  simp only [coe_prjO, coe_LocO2]
  refine SA.ext ?_ ?_ ?_ ?_
  · simp only [prjS_e, LocS2, bulk_prjO]
  · simp only [prjS_a, LocS2, coe_prjO, hP]
    cases i
    · exact locBp_two_eq_locAp _ _ _ _
    · rfl
  · simp only [prjS_b, LocS2, coe_prjO, locBp_zero]
  · simp only [prjS_ab, LocS2, coe_prjO, locABtXY_zero]

end LocSw

/-! ### The maps -/

section MapSw

variable {d L N : ℕ} [NeZero L] (i : Bool)

theorem prj_bpowO (j : ℕ) (I : OFam .two d L N) (X : Finset (Lam d L N)) :
    prjO i (bpowO j I X) = bpowO j (prjF i I) X := by
  rw [bpowO, map_prod]; rfl

theorem prj_KextO (j : ℕ) (K : OAct .two d L N) (X : Finset (Lam d L N)) :
    prjO i (KextO j K X) = KextO j (prjF i K) X := by
  rw [KextO, map_prod]; rfl

section Gen

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (Ib Ip : OFam .two d L N)
  (K : OAct .two d L N) (J : (Fin d → ℕ) → Finset (Lam d L N) → OE .two (Lam d L N))

theorem prj_gdIO (b : Fin d → ℕ) : prjO i (gdIO Ib Ip b) = gdIO (prjF i Ib) (prjF i Ip) b := by
  simp only [gdIO, map_sub, prjO_thetaO, prjO_inclO, prjF_apply]

theorem prj_gdIPowO (X : Finset (Lam d L N)) :
    prjO i (gdIPowO j Ib Ip X) = gdIPowO j (prjF i Ib) (prjF i Ip) X := by
  rw [gdIPowO, map_prod]
  exact prod_congr rfl fun b _ => prj_gdIO i Ib Ip b

theorem prj_gKtilO (W : Finset (Lam d L N)) :
    prjO i (gKtilO j Ib Ip K W) = gKtilO j (prjF i Ib) (prjF i Ip) (prjF i K) W := by
  rw [gKtilO, map_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [map_mul, prjO_thetaO, prj_KextO, prj_gdIPowO]

theorem prj_gKchkCO (W : Finset (Lam d L N)) :
    prjO i (gKchkCO j Ib Ip K J W) =
      gKchkCO j (prjF i Ib) (prjF i Ip) (prjF i K) (fun b X => prjO i (J b X)) W := by
  rw [gKchkCO, map_sub, prj_gKtilO, map_sum]
  simp only [prjO_thetaO]
  rfl

theorem prj_gKchkO (X : Finset (Lam d L N)) :
    prjO i (gKchkO j Ib Ip K J X) =
      gKchkO j (prjF i Ib) (prjF i Ip) (prjF i K) (fun b X => prjO i (J b X)) X := by
  rw [gKchkO, map_prod]
  exact prod_congr rfl fun W _ => prj_gKchkCO i j Ib Ip K J W

theorem prj_gKnextO (U : Finset (Lam d L N)) :
    prjO i (gKnextO j C Ib Ip K J U) =
      gKnextO j C (prjF i Ib) (prjF i Ip) (prjF i K) (fun b X => prjO i (J b X)) U := by
  rw [gKnextO, map_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [map_mul, prj_bpowO, prjO_ECCO, map_mul, prj_gKchkO, map_prod]
  simp only [prjO_thetaO]

end Gen

section Reblock

variable (k : ℕ) (I : OFam .two d L N) (M : OAct .two d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → OE .two (Lam d L N))

theorem prj_JbarO (b : Fin d → ℕ) (U : Finset (Lam d L N)) :
    prjO i (JbarO k I J b U) = JbarO k (prjF i I) (fun b X => prjO i (J b X)) b U := by
  rw [JbarO, map_mul, prj_bpowO]; rfl

theorem prj_RtermO (W : Finset (Lam d L N)) (g : GT d L N) :
    prjO i (RtermO k I M J W g) =
      RtermO k (prjF i I) (prjF i M) (fun b X => prjO i (J b X)) W g := by
  rw [RtermO, map_mul, map_mul, prj_bpowO, prj_KextO, map_prod]
  simp only [prj_JbarO]
  rfl

theorem prj_KoutO (W : Finset (Lam d L N)) :
    prjO i (KoutO k I M J W) = KoutO k (prjF i I) (prjF i M) (fun b X => prjO i (J b X)) W := by
  rw [KoutO, map_sum]
  simp only [prj_RtermO]
  rfl

end Reblock

section Map

variable {P P' : ObsPts d L N} (hP : P'.a = P.pt i) (j : ℕ)
  (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam .two d L N) (K : OAct .two d L N)

include hP

theorem prj_Q2O (b : Fin d → ℕ) : prjO i (Q2O P j K b) = Q2O P' j (prjF i K) b := by
  unfold Q2O
  split_ifs
  · rw [map_sum]; exact sum_congr rfl fun X _ => prjO_LocO2 i hP _ _ _
  · exact map_zero _

theorem prj_J2O (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    prjO i (J2O P j K b X) = J2O P' j (prjF i K) b X := by
  unfold J2O
  split_ifs
  · rw [map_neg, map_sum]
    simp only [prjO_LocO2 i hP]
    rfl
  · exact prjO_LocO2 i hP _ _ _
  · exact map_zero _

omit hP in
theorem prj_VprO (b : Fin d → ℕ) : prjO i (VprO C V b) = VprO C (prjF i V) b :=
  prjO_EthO i C (V b)

omit hP in
theorem prj_VprLO : prjO i (VprLO j C V) = VprLO j C (prjF i V) := by
  rw [VprLO, map_sum]; simp only [prj_VprO]; rfl

omit hP in
theorem prj_SCorO (b : Fin d → ℕ) : prjO i (SCorO j C V b) = SCorO j C (prjF i V) b := by
  simp only [SCorO, map_smul, map_sub, prjO_FCO, prjO_πobs, prj_VprO, prj_VprLO]

omit hP in
theorem prj_GO (b b' : Fin d → ℕ) : prjO i (GO C V b b') = GO C (prjF i V) b b' := by
  simp only [GO, map_sub, prjO_FCO, prjO_πobs, prj_VprO]

omit hP in
theorem prj_SFO (b : Fin d → ℕ) : prjO i (SFO j C V b) = SFO j C (prjF i V) b := by
  simp only [SFO, map_add, map_smul, prjO_FCO, prj_VprO, prj_VprLO, prj_SCorO]

omit hP in
theorem prj_SbO (b : Fin d → ℕ) : prjO i (SbO j C V W b) = SbO j C (prjF i V) (prjF i W) b := by
  simp only [SbO, map_add, prj_SFO, prjO_EthO, prjF_apply]

omit hP in
theorem prj_SXO (X : Finset (Lam d L N)) :
    prjO i (SXO j C V W X) = SXO j C (prjF i V) (prjF i W) X := by
  rw [SXO, map_sum]; simp only [prj_SbO]; rfl

theorem prj_LSO (b : Fin d → ℕ) :
    prjO i (LSO P j C V W b) = LSO P' j C (prjF i V) (prjF i W) b := by
  rw [LSO, prjO_LocO2 i hP, prj_SXO]; rfl

theorem prj_uVpO (b : Fin d → ℕ) :
    prjO i (uVpO P j C V W K b) = uVpO P' j C (prjF i V) (prjF i W) (prjF i K) b := by
  simp only [uVpO, map_sub, prj_VprO, prjO_EthO, prj_Q2O i hP, prj_LSO i hP]

theorem prj_upB (b : Fin d → ℕ) :
    upB P' j C (prjF i V) (prjF i W) (prjF i K) b = upB P j C V W K b := by
  unfold upB; rw [← prj_uVpO i hP, bulk_prjO]

theorem prj_upO (b : Fin d → ℕ) :
    prjO i (upO P j C V W K b) = upO P' j C (prjF i V) (prjF i W) (prjF i K) b := by
  simp only [upO, prjO_πobs, prjO_epsO, prj_uVpO i hP]

theorem prj_VpO (b : Fin d → ℕ) :
    prjO i (VpO P j C V W K b) = VpO P' j C (prjF i V) (prjF i W) (prjF i K) b := by
  simp only [VpO, map_sub, AlgHom.commutes, prj_uVpO i hP, prj_upO i hP, prj_upB i hP]

theorem prj_WpO (b : Fin d → ℕ) :
    prjO i (WpO P j C V W b) = WpO P' j C (prjF i V) (prjF i W) b := by
  simp only [WpO, map_sub, prj_SbO, prj_LSO i hP]

omit hP in
theorem prj_IbO (b : Fin d → ℕ) : prjO i (IbO V W b) = IbO (prjF i V) (prjF i W) b := by
  simp only [IbO, map_mul, map_neg, map_add, map_one, prjO_oexp, prjF_apply]

theorem prj_GpO (b : Fin d → ℕ) :
    prjO i (GpO P j C V W K b) = GpO P' j C (prjF i V) (prjF i W) (prjF i K) b := by
  simp only [GpO, map_mul, map_neg, map_add, map_one, prjO_oexp, prj_VpO i hP, prj_WpO i hP]

theorem prj_IpO (b : Fin d → ℕ) :
    prjO i (IpO P j C V W K b) = IpO P' j C (prjF i V) (prjF i W) (prjF i K) b := by
  simp only [IpO, map_mul, map_neg, prjO_expU, prj_upO i hP, prj_upB i hP, prj_GpO i hP]

theorem prj_uXB (X : Finset (Lam d L N)) :
    uXB P' j C (prjF i V) (prjF i W) (prjF i K) X = uXB P j C V W K X := by
  simp only [uXB, prj_upB i hP]

theorem prj_uXO (X : Finset (Lam d L N)) :
    prjO i (uXO P j C V W K X) = uXO P' j C (prjF i V) (prjF i W) (prjF i K) X := by
  simp only [uXO, map_sum, prj_upO i hP]

theorem prj_Knext2O (U : Finset (Lam d L N)) :
    prjO i (Knext2O P j C V W K U) = Knext2O P' j C (prjF i V) (prjF i W) (prjF i K) U := by
  rw [Knext2O, Knext2O, map_mul, prjO_expU, prj_uXO i hP, prj_uXB i hP, prj_gKnextO]
  have h1 : prjF i (IbO V W) = IbO (prjF i V) (prjF i W) := funext fun b => prj_IbO i V W b
  have h2 : prjF i (IpO P j C V W K) = IpO P' j C (prjF i V) (prjF i W) (prjF i K) :=
    funext fun b => prj_IpO i hP j C V W K b
  have h3 : (fun b X => prjO i (J2O P j K b X)) = J2O P' j (prjF i K) :=
    funext fun b => funext fun X => prj_J2O i hP j K b X
  rw [h1, h2, h3]

theorem prj_Vnext2O (c' : Fin d → ℕ) :
    prjO i (Vnext2O P j C V W K c') = Vnext2O P' j C (prjF i V) (prjF i W) (prjF i K) c' := by
  simp only [Vnext2O, map_sum, prj_VpO i hP]

theorem prj_Wnext2O (c' : Fin d → ℕ) :
    prjO i (Wnext2O P j C V W c') = Wnext2O P' j C (prjF i V) (prjF i W) c' := by
  simp only [Wnext2O, map_sub, map_prod, map_add, map_one, prj_WpO i hP]

theorem prj_uObsTot :
    prjO i (uObsTot P j C V W K) = uObsTot P' j C (prjF i V) (prjF i W) (prjF i K) := by
  simp only [uObsTot, map_sum, prj_upO i hP]

omit hP in
theorem prj_k2O (X : Finset (Lam d L N)) : prjO i (k2O j C V X) = k2O j C (prjF i V) X := by
  unfold k2O
  split_ifs
  · simp only [map_sum, map_sub, map_smul, prjO_FCO, prj_VprO, prj_VprLO, prj_SCorO]
  · simp only [map_sum, map_smul, prjO_FCO, prj_VprO]
  · exact map_zero _

omit hP in
theorem prj_K2O (U : Finset (Lam d L N)) : prjO i (K2O j C V U) = K2O j C (prjF i V) U := by
  simp only [K2O, map_sum, prj_k2O]

theorem prj_ItO (c' : Fin d → ℕ) :
    prjO i (ItO P j C V W K c') = ItO P' j C (prjF i V) (prjF i W) (prjF i K) c' := by
  rw [ItO, ItO, prj_bpowO,
    show prjF i (GpO P j C V W K) = GpO P' j C (prjF i V) (prjF i W) (prjF i K) from
      funext fun b => prj_GpO i hP j C V W K b]

theorem prj_KnewO (U : Finset (Lam d L N)) :
    prjO i (KnewO P j C V W K U) = KnewO P' j C (prjF i V) (prjF i W) (prjF i K) U := by
  rw [KnewO, KnewO, map_sub, map_mul, prj_Knext2O i hP, prj_bpowO, prj_K2O,
    show prjF i (GpO P j C V W K) = GpO P' j C (prjF i V) (prjF i W) (prjF i K) from
      funext fun b => prj_GpO i hP j C V W K b]

omit hP in
theorem prj_kapO (X : Finset (Lam d L N)) (c' : Fin d → ℕ) :
    prjO i (kapO j C V X c') = kapO j C (prjF i V) X c' := by
  unfold kapO
  split_ifs
  · simp only [map_sum, map_sub, map_smul, prjO_FCO, prj_VprO, prj_VprLO, prj_SCorO]
  · simp only [map_sum, map_smul, map_add, prjO_FCO, prj_VprO, prj_GO]
  · exact map_zero _

omit hP in
theorem prj_JhO (c' : Fin d → ℕ) (U : Finset (Lam d L N)) :
    prjO i (JhO j C V c' U) = JhO j C (prjF i V) c' U := by
  unfold JhO
  split_ifs
  · simp only [map_sum, prj_kapO]
  · exact map_zero _

theorem prj_KplusO (U : Finset (Lam d L N)) :
    prjO i (KplusO P j C V W K U) = KplusO P' j C (prjF i V) (prjF i W) (prjF i K) U := by
  rw [KplusO, KplusO, prj_KoutO,
    show prjF i (ItO P j C V W K) = ItO P' j C (prjF i V) (prjF i W) (prjF i K) from
      funext fun c' => prj_ItO i hP j C V W K c',
    show prjF i (KnewO P j C V W K) = KnewO P' j C (prjF i V) (prjF i W) (prjF i K) from
      funext fun U' => prj_KnewO i hP j C V W K U',
    show (fun c' U' => prjO i (JhO j C V c' U')) = JhO j C (prjF i V) from
      funext fun c' => funext fun U' => prj_JhO i j C V c' U']

end Map

theorem prj_KconnO (k : ℕ) (K : OAct .two d L N) (U : Finset (Lam d L N)) :
    prjO i (KconnO k K U) = KconnO k (prjF i K) U := by
  unfold KconnO
  split_ifs
  · rfl
  · exact map_zero _

theorem prj_KflatO (j : ℕ) (Δ : Step2.Fam d L N) (K : OAct .two d L N) (U : Finset (Lam d L N)) :
    prjO i (KflatO j Δ K U) = KflatO j Δ (prjF i K) U := by
  rw [KflatO, KflatO, map_mul, prjO_emb]; rfl

end MapSw

end

end Obs2
