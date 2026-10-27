import Obs2.Map.SwapO

/-!
# The merge `σ_a, σ_b ↦ σ_a` commutes with the map (Case (2)); linearity in the `σ_a` datum

In Case (2) (`τ = id`, `s = 1`) the `σ_a`- and `σ_b`-components multiply alike,
`(FG)_i = F_∅G_i + F_iG_∅`, so

  `mrgO : F_∅ + σ_aF_a + σ_bF_b + σ_aσ_bF_{ab} ↦ F_∅ + σ_a(F_a + F_b)`

(the substitution `σ_b ↦ σ_a`, using `σ_a² = 0`) is an algebra endomorphism of `OE .two Λ`. It is
componentwise, so it commutes with `θ`, the inclusion, `𝔼_C`, `e^{ℒ_C}`, `ε`, `π_obs`, `e^{·}`,
`emb`, `bulk`, and **`mrgO_LocO2`**: `mrgO ∘ Loc^P = Loc^{P'} ∘ mrgO` whenever
`P.b = P.a = P'.a` (in Case (2) `loc^b = loc^a`, `locBp_two_eq_locAp`).

Consequently (`mrg_*`, copies of `Obs2/Map/SwapO.lean`) every map of `Obs2.Map.Map` commutes with `mrgO`,
with the observable points `P = (a, a)` changed to any `P'` with `P'.a = a`. Together with the
one-source projections `prjO i` this gives the **additivity of the `σ_a` part** of the step and of
the history in the `σ_a` datum (`Obs2/Map/LinearStep.lean`, `PtCorr2/Obs/LinearHist.lean`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux

/-! ### The merge -/

section Alg

variable {Λ : Type*} [DecidableEq Λ]

/-- `F ↦ F_∅ + σ_a(F_a + F_b)` on the Case-(2) algebra with sources. -/
def mrgS : SA .two Λ →ₐ[ℂ] SA .two Λ where
  toFun F := ⟨F.e, F.a + F.b, 0, 0⟩
  map_one' := by refine SA.ext ?_ ?_ ?_ ?_ <;> simp
  map_mul' F G := by
    refine SA.ext ?_ ?_ ?_ ?_ <;> simp [Obs.Case.tau, mul_add, add_mul] <;> abel
  map_zero' := by refine SA.ext ?_ ?_ ?_ ?_ <;> simp
  map_add' F G := by refine SA.ext ?_ ?_ ?_ ?_ <;> simp <;> abel
  commutes' r := by refine SA.ext ?_ ?_ ?_ ?_ <;> simp

@[simp] theorem mrgS_e (F : SA .two Λ) : (mrgS F).e = F.e := rfl
@[simp] theorem mrgS_a (F : SA .two Λ) : (mrgS F).a = F.a + F.b := rfl
@[simp] theorem mrgS_b (F : SA .two Λ) : (mrgS F).b = 0 := rfl
@[simp] theorem mrgS_ab (F : SA .two Λ) : (mrgS F).ab = 0 := rfl

theorem mrgS_mem (F : OE .two Λ) : mrgS (F : SA .two Λ) ∈ OEv .two Λ := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_OEv.1 F.2
  refine mem_OEv.2 ⟨h1, ?_, ?_, ?_⟩
  · simp only [mrgS_a, map_add, h2, h3, smul_add]
  · simp
  · simp

/-- **The merge** `F ↦ F_∅ + σ_a(F_a + F_b)` on even elements. -/
def mrgO : OE .two Λ →ₐ[ℂ] OE .two Λ :=
  ((mrgS).comp (OEv .two Λ).val).codRestrict (OEv .two Λ) fun F => mrgS_mem F

@[simp] theorem coe_mrgO (F : OE .two Λ) :
    (mrgO F : SA .two Λ) = mrgS (F : SA .two Λ) := rfl

theorem bulk_mrgO (F : OE .two Λ) : bulk (mrgO F) = bulk F := rfl

theorem mrgO_emb (x : Step.EvR Λ) : mrgO (emb x : OE .two Λ) = emb x := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

theorem mrgO_πobs (F : OE .two Λ) : mrgO (πobs F) = πobs (mrgO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

theorem mrgO_epsO (F : OE .two Λ) : mrgO (epsO F) = epsO (mrgO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

theorem mrgO_thetaO (F : OE .two Λ) : mrgO (thetaO F) = thetaO (mrgO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

theorem mrgO_inclO (F : OE .two Λ) : mrgO (inclO F) = inclO (mrgO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

variable [Fintype Λ]

theorem mrgO_isNilpotent_iff (F : OE .two Λ) : IsNilpotent (mrgO F) ↔ IsNilpotent F := by
  constructor
  · intro h
    exact isNilpotent_of_bulk (by rw [← bulk_mrgO F]; exact h.map bulk)
  · intro h; exact h.map _

theorem mrgO_oexp (F : OE .two Λ) : mrgO (oexp F) = oexp (mrgO F) := by
  by_cases h : IsNilpotent F
  · unfold oexp; exact IsNilpotent.map_exp h mrgO
  · have h' : ¬ IsNilpotent (mrgO F) := fun h'' => h ((mrgO_isNilpotent_iff F).1 h'')
    rw [oexp, oexp, nilExp_of_not h, nilExp_of_not h', map_zero]

theorem mrgO_expU (x : ℂ) (F : OE .two Λ) : mrgO (expU x F) = expU x (mrgO F) := by
  rw [expU, expU, map_smul, mrgO_oexp]

theorem mrgO_ECCO (C : Matrix Λ Λ ℂ) (F : OE .two (Λ ⊕ Λ)) :
    mrgO (ECCO C F) = ECCO C (mrgO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

theorem mrgO_expO (C : Matrix Λ Λ ℂ) (F : OE .two Λ) :
    mrgO (expO C F) = expO C (mrgO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp

theorem mrgO_EthO (C : Matrix Λ Λ ℂ) (F : OE .two Λ) :
    mrgO (EthO C F) = EthO C (mrgO F) := by
  rw [EthO, EthO, mrgO_ECCO, mrgO_thetaO]

theorem mrgO_FCO (C : Matrix Λ Λ ℂ) (A B : OE .two Λ) :
    mrgO (FCO C A B) = FCO C (mrgO A) (mrgO B) := by
  simp only [FCO, map_sub, map_mul, mrgO_expO]

end Alg

/-- The merge of a family. -/
def mrgF {Λ ι : Type*} [DecidableEq Λ] (F : ι → OE .two Λ) : ι → OE .two Λ :=
  fun x => mrgO (F x)

@[simp] theorem mrgF_apply {Λ ι : Type*} [DecidableEq Λ] (F : ι → OE .two Λ) (x : ι) :
    mrgF F x = mrgO (F x) := rfl

/-! ### `Loc` -/

section LocMrg

variable {d L N : ℕ} [NeZero L]

/-- **`mrgO ∘ Loc^P = Loc^{P'} ∘ mrgO`** for `P.b = P.a = P'.a`. -/
theorem mrgO_LocO2 {P P' : ObsPts d L N} (hP : P'.a = P.a ∧ P.b = P.a)
    (X Y : Finset (Lam d L N)) (F : OE .two (Lam d L N)) :
    mrgO (LocO2 P X Y F) = LocO2 P' X Y (mrgO F) := by
  apply Subtype.ext
  simp only [coe_mrgO, coe_LocO2]
  refine SA.ext ?_ ?_ ?_ ?_
  · simp only [mrgS_e, LocS2, bulk_mrgO]
  · simp only [mrgS_a, LocS2, coe_mrgO, hP.1, hP.2, locBp_two_eq_locAp, locAp_add]
  · simp only [mrgS_b, LocS2, coe_mrgO, locBp_zero]
  · simp only [mrgS_ab, LocS2, coe_mrgO, locABtXY_zero]

end LocMrg

/-! ### The maps -/

section MapMrg

variable {d L N : ℕ} [NeZero L] 

theorem mrg_bpowO (j : ℕ) (I : OFam .two d L N) (X : Finset (Lam d L N)) :
    mrgO (bpowO j I X) = bpowO j (mrgF I) X := by
  rw [bpowO, map_prod]; rfl

theorem mrg_KextO (j : ℕ) (K : OAct .two d L N) (X : Finset (Lam d L N)) :
    mrgO (KextO j K X) = KextO j (mrgF K) X := by
  rw [KextO, map_prod]; rfl

section Gen

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (Ib Ip : OFam .two d L N)
  (K : OAct .two d L N) (J : (Fin d → ℕ) → Finset (Lam d L N) → OE .two (Lam d L N))

theorem mrg_gdIO (b : Fin d → ℕ) : mrgO (gdIO Ib Ip b) = gdIO (mrgF Ib) (mrgF Ip) b := by
  simp only [gdIO, map_sub, mrgO_thetaO, mrgO_inclO, mrgF_apply]

theorem mrg_gdIPowO (X : Finset (Lam d L N)) :
    mrgO (gdIPowO j Ib Ip X) = gdIPowO j (mrgF Ib) (mrgF Ip) X := by
  rw [gdIPowO, map_prod]
  exact prod_congr rfl fun b _ => mrg_gdIO Ib Ip b

theorem mrg_gKtilO (W : Finset (Lam d L N)) :
    mrgO (gKtilO j Ib Ip K W) = gKtilO j (mrgF Ib) (mrgF Ip) (mrgF K) W := by
  rw [gKtilO, map_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [map_mul, mrgO_thetaO, mrg_KextO, mrg_gdIPowO]

theorem mrg_gKchkCO (W : Finset (Lam d L N)) :
    mrgO (gKchkCO j Ib Ip K J W) =
      gKchkCO j (mrgF Ib) (mrgF Ip) (mrgF K) (fun b X => mrgO (J b X)) W := by
  rw [gKchkCO, map_sub, mrg_gKtilO, map_sum]
  simp only [mrgO_thetaO]
  rfl

theorem mrg_gKchkO (X : Finset (Lam d L N)) :
    mrgO (gKchkO j Ib Ip K J X) =
      gKchkO j (mrgF Ib) (mrgF Ip) (mrgF K) (fun b X => mrgO (J b X)) X := by
  rw [gKchkO, map_prod]
  exact prod_congr rfl fun W _ => mrg_gKchkCO j Ib Ip K J W

theorem mrg_gKnextO (U : Finset (Lam d L N)) :
    mrgO (gKnextO j C Ib Ip K J U) =
      gKnextO j C (mrgF Ib) (mrgF Ip) (mrgF K) (fun b X => mrgO (J b X)) U := by
  rw [gKnextO, map_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [map_mul, mrg_bpowO, mrgO_ECCO, map_mul, mrg_gKchkO, map_prod]
  simp only [mrgO_thetaO]

end Gen

section Reblock

variable (k : ℕ) (I : OFam .two d L N) (M : OAct .two d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → OE .two (Lam d L N))

theorem mrg_JbarO (b : Fin d → ℕ) (U : Finset (Lam d L N)) :
    mrgO (JbarO k I J b U) = JbarO k (mrgF I) (fun b X => mrgO (J b X)) b U := by
  rw [JbarO, map_mul, mrg_bpowO]; rfl

theorem mrg_RtermO (W : Finset (Lam d L N)) (g : GT d L N) :
    mrgO (RtermO k I M J W g) =
      RtermO k (mrgF I) (mrgF M) (fun b X => mrgO (J b X)) W g := by
  rw [RtermO, map_mul, map_mul, mrg_bpowO, mrg_KextO, map_prod]
  simp only [mrg_JbarO]
  rfl

theorem mrg_KoutO (W : Finset (Lam d L N)) :
    mrgO (KoutO k I M J W) = KoutO k (mrgF I) (mrgF M) (fun b X => mrgO (J b X)) W := by
  rw [KoutO, map_sum]
  simp only [mrg_RtermO]
  rfl

end Reblock

section Map

variable {P P' : ObsPts d L N} (hP : P'.a = P.a ∧ P.b = P.a) (j : ℕ)
  (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam .two d L N) (K : OAct .two d L N)

include hP

theorem mrg_Q2O (b : Fin d → ℕ) : mrgO (Q2O P j K b) = Q2O P' j (mrgF K) b := by
  unfold Q2O
  split_ifs
  · rw [map_sum]; exact sum_congr rfl fun X _ => mrgO_LocO2 hP _ _ _
  · exact map_zero _

theorem mrg_J2O (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    mrgO (J2O P j K b X) = J2O P' j (mrgF K) b X := by
  unfold J2O
  split_ifs
  · rw [map_neg, map_sum]
    simp only [mrgO_LocO2 hP]
    rfl
  · exact mrgO_LocO2 hP _ _ _
  · exact map_zero _

omit hP in
theorem mrg_VprO (b : Fin d → ℕ) : mrgO (VprO C V b) = VprO C (mrgF V) b :=
  mrgO_EthO C (V b)

omit hP in
theorem mrg_VprLO : mrgO (VprLO j C V) = VprLO j C (mrgF V) := by
  rw [VprLO, map_sum]; simp only [mrg_VprO]; rfl

omit hP in
theorem mrg_SCorO (b : Fin d → ℕ) : mrgO (SCorO j C V b) = SCorO j C (mrgF V) b := by
  simp only [SCorO, map_smul, map_sub, mrgO_FCO, mrgO_πobs, mrg_VprO, mrg_VprLO]

omit hP in
theorem mrg_GO (b b' : Fin d → ℕ) : mrgO (GO C V b b') = GO C (mrgF V) b b' := by
  simp only [GO, map_sub, mrgO_FCO, mrgO_πobs, mrg_VprO]

omit hP in
theorem mrg_SFO (b : Fin d → ℕ) : mrgO (SFO j C V b) = SFO j C (mrgF V) b := by
  simp only [SFO, map_add, map_smul, mrgO_FCO, mrg_VprO, mrg_VprLO, mrg_SCorO]

omit hP in
theorem mrg_SbO (b : Fin d → ℕ) : mrgO (SbO j C V W b) = SbO j C (mrgF V) (mrgF W) b := by
  simp only [SbO, map_add, mrg_SFO, mrgO_EthO, mrgF_apply]

omit hP in
theorem mrg_SXO (X : Finset (Lam d L N)) :
    mrgO (SXO j C V W X) = SXO j C (mrgF V) (mrgF W) X := by
  rw [SXO, map_sum]; simp only [mrg_SbO]; rfl

theorem mrg_LSO (b : Fin d → ℕ) :
    mrgO (LSO P j C V W b) = LSO P' j C (mrgF V) (mrgF W) b := by
  rw [LSO, mrgO_LocO2 hP, mrg_SXO]; rfl

theorem mrg_uVpO (b : Fin d → ℕ) :
    mrgO (uVpO P j C V W K b) = uVpO P' j C (mrgF V) (mrgF W) (mrgF K) b := by
  simp only [uVpO, map_sub, mrg_VprO, mrgO_EthO, mrg_Q2O hP, mrg_LSO hP]

theorem mrg_upB (b : Fin d → ℕ) :
    upB P' j C (mrgF V) (mrgF W) (mrgF K) b = upB P j C V W K b := by
  unfold upB; rw [← mrg_uVpO hP, bulk_mrgO]

theorem mrg_upO (b : Fin d → ℕ) :
    mrgO (upO P j C V W K b) = upO P' j C (mrgF V) (mrgF W) (mrgF K) b := by
  simp only [upO, mrgO_πobs, mrgO_epsO, mrg_uVpO hP]

theorem mrg_VpO (b : Fin d → ℕ) :
    mrgO (VpO P j C V W K b) = VpO P' j C (mrgF V) (mrgF W) (mrgF K) b := by
  simp only [VpO, map_sub, AlgHom.commutes, mrg_uVpO hP, mrg_upO hP, mrg_upB hP]

theorem mrg_WpO (b : Fin d → ℕ) :
    mrgO (WpO P j C V W b) = WpO P' j C (mrgF V) (mrgF W) b := by
  simp only [WpO, map_sub, mrg_SbO, mrg_LSO hP]

omit hP in
theorem mrg_IbO (b : Fin d → ℕ) : mrgO (IbO V W b) = IbO (mrgF V) (mrgF W) b := by
  simp only [IbO, map_mul, map_neg, map_add, map_one, mrgO_oexp, mrgF_apply]

theorem mrg_GpO (b : Fin d → ℕ) :
    mrgO (GpO P j C V W K b) = GpO P' j C (mrgF V) (mrgF W) (mrgF K) b := by
  simp only [GpO, map_mul, map_neg, map_add, map_one, mrgO_oexp, mrg_VpO hP, mrg_WpO hP]

theorem mrg_IpO (b : Fin d → ℕ) :
    mrgO (IpO P j C V W K b) = IpO P' j C (mrgF V) (mrgF W) (mrgF K) b := by
  simp only [IpO, map_mul, map_neg, mrgO_expU, mrg_upO hP, mrg_upB hP, mrg_GpO hP]

theorem mrg_uXB (X : Finset (Lam d L N)) :
    uXB P' j C (mrgF V) (mrgF W) (mrgF K) X = uXB P j C V W K X := by
  simp only [uXB, mrg_upB hP]

theorem mrg_uXO (X : Finset (Lam d L N)) :
    mrgO (uXO P j C V W K X) = uXO P' j C (mrgF V) (mrgF W) (mrgF K) X := by
  simp only [uXO, map_sum, mrg_upO hP]

theorem mrg_Knext2O (U : Finset (Lam d L N)) :
    mrgO (Knext2O P j C V W K U) = Knext2O P' j C (mrgF V) (mrgF W) (mrgF K) U := by
  rw [Knext2O, Knext2O, map_mul, mrgO_expU, mrg_uXO hP, mrg_uXB hP, mrg_gKnextO]
  have h1 : mrgF (IbO V W) = IbO (mrgF V) (mrgF W) := funext fun b => mrg_IbO V W b
  have h2 : mrgF (IpO P j C V W K) = IpO P' j C (mrgF V) (mrgF W) (mrgF K) :=
    funext fun b => mrg_IpO hP j C V W K b
  have h3 : (fun b X => mrgO (J2O P j K b X)) = J2O P' j (mrgF K) :=
    funext fun b => funext fun X => mrg_J2O hP j K b X
  rw [h1, h2, h3]

theorem mrg_Vnext2O (c' : Fin d → ℕ) :
    mrgO (Vnext2O P j C V W K c') = Vnext2O P' j C (mrgF V) (mrgF W) (mrgF K) c' := by
  simp only [Vnext2O, map_sum, mrg_VpO hP]

theorem mrg_Wnext2O (c' : Fin d → ℕ) :
    mrgO (Wnext2O P j C V W c') = Wnext2O P' j C (mrgF V) (mrgF W) c' := by
  simp only [Wnext2O, map_sub, map_prod, map_add, map_one, mrg_WpO hP]

theorem mrg_uObsTot :
    mrgO (uObsTot P j C V W K) = uObsTot P' j C (mrgF V) (mrgF W) (mrgF K) := by
  simp only [uObsTot, map_sum, mrg_upO hP]

omit hP in
theorem mrg_k2O (X : Finset (Lam d L N)) : mrgO (k2O j C V X) = k2O j C (mrgF V) X := by
  unfold k2O
  split_ifs
  · simp only [map_sum, map_sub, map_smul, mrgO_FCO, mrg_VprO, mrg_VprLO, mrg_SCorO]
  · simp only [map_sum, map_smul, mrgO_FCO, mrg_VprO]
  · exact map_zero _

omit hP in
theorem mrg_K2O (U : Finset (Lam d L N)) : mrgO (K2O j C V U) = K2O j C (mrgF V) U := by
  simp only [K2O, map_sum, mrg_k2O]

theorem mrg_ItO (c' : Fin d → ℕ) :
    mrgO (ItO P j C V W K c') = ItO P' j C (mrgF V) (mrgF W) (mrgF K) c' := by
  rw [ItO, ItO, mrg_bpowO,
    show mrgF (GpO P j C V W K) = GpO P' j C (mrgF V) (mrgF W) (mrgF K) from
      funext fun b => mrg_GpO hP j C V W K b]

theorem mrg_KnewO (U : Finset (Lam d L N)) :
    mrgO (KnewO P j C V W K U) = KnewO P' j C (mrgF V) (mrgF W) (mrgF K) U := by
  rw [KnewO, KnewO, map_sub, map_mul, mrg_Knext2O hP, mrg_bpowO, mrg_K2O,
    show mrgF (GpO P j C V W K) = GpO P' j C (mrgF V) (mrgF W) (mrgF K) from
      funext fun b => mrg_GpO hP j C V W K b]

omit hP in
theorem mrg_kapO (X : Finset (Lam d L N)) (c' : Fin d → ℕ) :
    mrgO (kapO j C V X c') = kapO j C (mrgF V) X c' := by
  unfold kapO
  split_ifs
  · simp only [map_sum, map_sub, map_smul, mrgO_FCO, mrg_VprO, mrg_VprLO, mrg_SCorO]
  · simp only [map_sum, map_smul, map_add, mrgO_FCO, mrg_VprO, mrg_GO]
  · exact map_zero _

omit hP in
theorem mrg_JhO (c' : Fin d → ℕ) (U : Finset (Lam d L N)) :
    mrgO (JhO j C V c' U) = JhO j C (mrgF V) c' U := by
  unfold JhO
  split_ifs
  · simp only [map_sum, mrg_kapO]
  · exact map_zero _

theorem mrg_KplusO (U : Finset (Lam d L N)) :
    mrgO (KplusO P j C V W K U) = KplusO P' j C (mrgF V) (mrgF W) (mrgF K) U := by
  rw [KplusO, KplusO, mrg_KoutO,
    show mrgF (ItO P j C V W K) = ItO P' j C (mrgF V) (mrgF W) (mrgF K) from
      funext fun c' => mrg_ItO hP j C V W K c',
    show mrgF (KnewO P j C V W K) = KnewO P' j C (mrgF V) (mrgF W) (mrgF K) from
      funext fun U' => mrg_KnewO hP j C V W K U',
    show (fun c' U' => mrgO (JhO j C V c' U')) = JhO j C (mrgF V) from
      funext fun c' => funext fun U' => mrg_JhO j C V c' U']

end Map

theorem mrg_KconnO (k : ℕ) (K : OAct .two d L N) (U : Finset (Lam d L N)) :
    mrgO (KconnO k K U) = KconnO k (mrgF K) U := by
  unfold KconnO
  split_ifs
  · rfl
  · exact map_zero _

theorem mrg_KflatO (j : ℕ) (Δ : Step2.Fam d L N) (K : OAct .two d L N) (U : Finset (Lam d L N)) :
    mrgO (KflatO j Δ K U) = KflatO j Δ (mrgF K) U := by
  rw [KflatO, KflatO, map_mul, mrgO_emb]; rfl

end MapMrg

end

end Obs2
