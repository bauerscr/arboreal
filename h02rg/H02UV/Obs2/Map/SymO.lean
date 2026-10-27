import Obs2.Map.Supp
import Obs2.Est.SplitO
import Obs.MapSupp
import Obs.Coupling

/-!
# `U(1)` invariance with sources along one step (`IsSymS` propagation)

The `U(1)`-invariant even elements with sources form a subalgebra (`Obs.symSub`). It is stable
under every operation of the map with sources (`Obs2.Map.Map`):

* `thetaO`, `inclO`, `𝔼_C` (`ECCO`, complex covariance: `Step2.ECC_scal`), `e^{ℒ_C}` (`expO`),
  hence `𝔼_C θ` (`EthO`) and `F_C` (`FCO`); `ε` (`epsO`), `π_obs`, `e^{·}` (`oexp`, `expU`);
* **`isSymS_LocO2`**: `Loc_{X,Y} F` is `U(1)` invariant for **every** `F` (the pointed `loc^a`,
  `loc^b` produce `ψ̄_a`, `ψ_b` times invariant polynomials; the barycentric `loc^{ab}` produces
  invariant monomials `ψ̄_xψ_y`).

**`OSymS.step`**: if `V(B)`, `𝒲(B)`, `K(X)` (`X` connected) are `U(1)` invariant, so are
`V_{j+1}`, `𝒲_{j+1}` and `K_{j+1}` (on connected polymers). No geometric hypothesis is needed.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD PolyAux

/-! ### Scaling identities -/

theorem eps_scal {Λ : Type*} [DecidableEq Λ] (t : ℂ) (x : Grassmann.N Λ) :
    ε (Step.scal Λ t x) = ε x := by
  have h : (ε : Grassmann.N Λ →ₐ[ℂ] ℂ).comp (Step.scal Λ t) = ε := by
    ext v
    simp [Step.scal, ExteriorAlgebra.map_apply_ι]
  exact DFunLike.congr_fun h x

section Gen

variable {c : Obs.Case} {Λ Λ' : Type*} [DecidableEq Λ] [DecidableEq Λ']

/-- A componentwise map commuting with the scaling preserves `U(1)` invariance. -/
theorem isSymS_mapL (f : Grassmann.N Λ →ₗ[ℂ] Grassmann.N Λ')
    (hf : ∀ x, f (Step.scal Λ 2 x) = Step.scal Λ' 2 (f x)) {F : SA c Λ} (hF : IsSymS F) :
    IsSymS (mapL f F : SA c Λ') := by
  unfold IsSymS at hF ⊢
  have he := congrArg SA.e hF
  have ha := congrArg SA.a hF
  have hb := congrArg SA.b hF
  have hab := congrArg SA.ab hF
  simp only [scalS_e, scalS_a, scalS_b, scalS_ab] at he ha hb hab
  refine SA.ext ?_ ?_ ?_ ?_
  · simp only [scalS_e, mapL_e]; rw [← hf, he]
  · simp only [scalS_a, mapL_a]; rw [← hf, ← map_smul, ha]
  · simp only [scalS_b, mapL_b]; rw [← hf, ← map_smul, hb]
  · simp only [scalS_ab, mapL_ab]; rw [← hf, ← map_smul, hab]

theorem isSymS_πobs [Fintype Λ] {F : OE c Λ} (hF : IsSymS (F : SA c Λ)) :
    IsSymS (πobs F : SA c Λ) := by
  unfold IsSymS at hF ⊢
  have ha := congrArg SA.a hF
  have hb := congrArg SA.b hF
  have hab := congrArg SA.ab hF
  simp only [scalS_a, scalS_b, scalS_ab] at ha hb hab
  rw [coe_πobs, piobs_apply]
  refine SA.ext ?_ ?_ ?_ ?_
  · simp
  · simp only [scalS_a]; exact ha
  · simp only [scalS_b]; exact hb
  · simp only [scalS_ab]; exact hab

end Gen

/-! ### The operations -/

section Ops

variable {c : Obs.Case} {d L N : ℕ} [NeZero L]

local notation "SY" => (symSub : Subalgebra ℂ (OE c (Lam d L N)))
local notation "SY2" => (symSub : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)))

theorem thetaO_mem_sym {F : OE c (Lam d L N)} (hF : F ∈ SY) : thetaO F ∈ SY2 := by
  refine mem_symSub.2 ?_
  show IsSymS (thetaS (F : SA c (Lam d L N)))
  rw [IsSymS, scalS_thetaS, (mem_symSub.1 hF : IsSymS _)]

theorem inclO_mem_sym {F : OE c (Lam d L N)} (hF : F ∈ SY) : inclO F ∈ SY2 := by
  refine mem_symSub.2 ?_
  show IsSymS (inclS (F : SA c (Lam d L N)))
  rw [IsSymS, scalS_inclS, (mem_symSub.1 hF : IsSymS _)]

theorem ECCO_mem_sym (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N ⊕ Lam d L N)}
    (hF : F ∈ SY2) : ECCO C F ∈ SY :=
  mem_symSub.2 (isSymS_mapL (ECC C) (fun x => ECC_scal C two_ne_zero x) (mem_symSub.1 hF))

theorem expO_mem_sym (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ SY) : expO C F ∈ SY :=
  mem_symSub.2 (isSymS_mapL (expLC C) (fun x => expLC_scal C two_ne_zero x) (mem_symSub.1 hF))

theorem EthO_mem_sym (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ SY) : EthO C F ∈ SY :=
  ECCO_mem_sym C (thetaO_mem_sym hF)

theorem FCO_mem_sym (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : OE c (Lam d L N)}
    (hA : A ∈ SY) (hB : B ∈ SY) : FCO C A B ∈ SY :=
  sub_mem (expO_mem_sym C (mul_mem (expO_mem_sym _ hA) (expO_mem_sym _ hB))) (mul_mem hA hB)

theorem epsO_mem_sym {F : OE c (Lam d L N)} (hF : F ∈ SY) : epsO F ∈ SY := by
  refine mem_symSub.2 ?_
  show IsSymS (mapL epsN.toLinearMap (F : SA c (Lam d L N)))
  refine isSymS_mapL _ (fun x => ?_) (mem_symSub.1 hF)
  simp only [AlgHom.toLinearMap_apply, epsN, AlgHom.comp_apply, Algebra.ofId_apply,
    AlgHom.commutes, eps_scal]

theorem πobs_mem_sym {F : OE c (Lam d L N)} (hF : F ∈ SY) : πobs F ∈ SY :=
  mem_symSub.2 (isSymS_πobs (mem_symSub.1 hF))

theorem emb_mem_sym {x : EvR (Lam d L N)} (hx : (x : Alg d L N) ∈ SymS (Lam d L N)) :
    (emb x : OE c (Lam d L N)) ∈ SY := by
  refine mem_symSub.2 (SA.ext ?_ ?_ ?_ ?_)
  · exact mem_SymS.1 hx
  all_goals simp [emb]

end Ops

/-! ### `Loc` is `U(1)` invariant -/

section LocSym

variable {d L N : ℕ} [NeZero L]

theorem pp_mem_SymS (x y : Lam d L N) : psibar x * psi y ∈ SymS (Lam d L N) :=
  mem_SymS.2 (Obs.scal_psibar_psi 2 two_ne_zero x y)

theorem Dt_mem_SymS (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    Dt X a b F ∈ SymS (Lam d L N) := by
  have h1 : dbar a b * psi a ∈ SymS (Lam d L N) := by
    rw [dbar, sub_mul]; exact sub_mem (pp_mem_SymS _ _) (pp_mem_SymS _ _)
  have h2 : psibar a * dlt a b ∈ SymS (Lam d L N) := by
    rw [dlt, mul_sub]; exact sub_mem (pp_mem_SymS _ _) (pp_mem_SymS _ _)
  have h3 : dbar a b * dlt a b ∈ SymS (Lam d L N) := by
    rw [dbar, dlt, sub_mul, mul_sub, mul_sub]
    exact sub_mem (sub_mem (pp_mem_SymS _ _) (pp_mem_SymS _ _))
      (sub_mem (pp_mem_SymS _ _) (pp_mem_SymS _ _))
  have h4 : pbp a * (dbar a b * dlt a b) ∈ SymS (Lam d L N) :=
    mul_mem (pp_mem_SymS _ _) h3
  unfold Dt
  exact add_mem (add_mem (add_mem (Subalgebra.smul_mem _ h1 _) (Subalgebra.smul_mem _ h2 _))
    (Subalgebra.smul_mem _ h3 _)) (Subalgebra.smul_mem _ h4 _)

theorem locABtXY_scal (P : ObsPts d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Step.scal _ 2 (locABtXY P X Y F) = locABtXY P X Y F := by
  have hab : ∀ a b : Lam d L N, Step.scal _ 2 (locABt X a b F) = locABt X a b F := fun a b => by
    rw [locABt, map_add, scal_locEven, mem_SymS.1 (Dt_mem_SymS X a b F)]
  rw [locABtXY, map_smul, locABtX]
  split_ifs <;> rw [hab]

theorem locAp_scal_one (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Step.scal _ 2 (locAp .one a X Y F) = (2⁻¹ : ℂ) • locAp .one a X Y F := by
  unfold locAp
  split_ifs
  · show Step.scal _ 2 (locOdd (-1) {a} X Y F) = (2⁻¹ : ℂ) • locOdd (-1) {a} X Y F
    rw [scal_locOdd, if_neg units_ne.symm]
  · show Step.scal _ 2 (_ • locOdd (-1) {a} {a} {a} F) = (2⁻¹ : ℂ) • (_ • locOdd (-1) {a} {a} {a} F)
    rw [map_smul, scal_locOdd, if_neg units_ne.symm, smul_comm]

theorem locBp_scal_one (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Step.scal _ 2 (locBp .one b X Y F) = (2 : ℂ) • locBp .one b X Y F := by
  unfold locBp
  split_ifs
  · show Step.scal _ 2 (locOdd 1 {b} X Y F) = (2 : ℂ) • locOdd 1 {b} X Y F
    rw [scal_locOdd, if_pos rfl]
  · show Step.scal _ 2 (_ • locOdd 1 {b} {b} {b} F) = (2 : ℂ) • (_ • locOdd 1 {b} {b} {b} F)
    rw [map_smul, scal_locOdd, if_pos rfl, smul_comm]

theorem locAp_scal_two (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Step.scal _ 2 (locAp .two a X Y F) = locAp .two a X Y F := by
  unfold locAp
  split_ifs
  · show Step.scal _ 2 (locEven {a} X Y F) = locEven {a} X Y F
    rw [scal_locEven]
  · show Step.scal _ 2 (_ • locEven {a} {a} {a} F) = _ • locEven {a} {a} {a} F
    rw [map_smul, scal_locEven]

theorem locBp_scal_two (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Step.scal _ 2 (locBp .two b X Y F) = locBp .two b X Y F := by
  unfold locBp
  split_ifs
  · show Step.scal _ 2 (locEven {b} X Y F) = locEven {b} X Y F
    rw [scal_locEven]
  · show Step.scal _ 2 (_ • locEven {b} {b} {b} F) = _ • locEven {b} {b} {b} F
    rw [map_smul, scal_locEven]

/-- **`Loc_{X,Y}` with sources is `U(1)` invariant** (for every `F`). -/
theorem isSymS_LocO2 {c : Obs.Case} (P : ObsPts d L N) (X Y : Finset (Lam d L N))
    (F : OE c (Lam d L N)) : IsSymS (LocO2 P X Y F : SA c (Lam d L N)) := by
  have he : Step.scal _ 2 ((Step2.Loc2E X Y (bulk F) : EvR (Lam d L N)) : Alg d L N) =
      (Step2.Loc2E X Y (bulk F) : Alg d L N) := mem_SymS.1 (Loc2E_sym X Y (bulk F))
  cases c
  · rw [isSymS_iff_one]
    exact ⟨he, locAp_scal_one _ _ _ _, locBp_scal_one _ _ _ _, locABtXY_scal _ _ _ _⟩
  · rw [isSymS_iff_two]
    exact ⟨he, locAp_scal_two _ _ _ _, locBp_scal_two _ _ _ _, locABtXY_scal _ _ _ _⟩

theorem LocO2_mem_sym {c : Obs.Case} (P : ObsPts d L N) (X Y : Finset (Lam d L N))
    (F : OE c (Lam d L N)) : LocO2 P X Y F ∈ (symSub : Subalgebra ℂ (OE c (Lam d L N))) :=
  mem_symSub.2 (isSymS_LocO2 P X Y F)

end LocSym

/-! ### One step -/

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **`U(1)` invariance of the input of one step with sources.** -/
structure OSymS (j : ℕ) (V W : OFam c d L N) (K : OAct c d L N) : Prop where
  hV : ∀ b, V b ∈ (symSub : Subalgebra ℂ (OE c (Lam d L N)))
  hW : ∀ b, W b ∈ (symSub : Subalgebra ℂ (OE c (Lam d L N)))
  hK : ∀ Y, IsConn j Y → K Y ∈ (symSub : Subalgebra ℂ (OE c (Lam d L N)))

namespace OSymS

variable {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} (H : OSymS j V W K)
include H

local notation "SY" => (symSub : Subalgebra ℂ (OE c (Lam d L N)))

theorem Vpr_sym (b : Fin d → ℕ) : VprO C V b ∈ SY := EthO_mem_sym C (H.hV b)

theorem Q2O_sym (b : Fin d → ℕ) : Q2O P j K b ∈ SY := by
  unfold Q2O; split_ifs
  · exact Subalgebra.sum_mem _ fun X _ => LocO2_mem_sym P _ _ _
  · exact zero_mem _

omit H in
theorem J2O_sym (b : Fin d → ℕ) (X : Finset (Lam d L N)) : J2O P j K b X ∈ SY := by
  unfold J2O; split_ifs
  · exact neg_mem (Subalgebra.sum_mem _ fun Y _ => LocO2_mem_sym P _ _ _)
  · exact LocO2_mem_sym P _ _ _
  · exact zero_mem _

theorem VprL_sym : VprLO j C V ∈ SY := Subalgebra.sum_mem _ fun b _ => H.Vpr_sym b

theorem SCor_sym (b : Fin d → ℕ) : SCorO j C V b ∈ SY :=
  Subalgebra.smul_mem _ (sub_mem (FCO_mem_sym C (πobs_mem_sym (H.Vpr_sym b)) H.VprL_sym)
    (FCO_mem_sym C (H.Vpr_sym b) (πobs_mem_sym H.VprL_sym))) _

theorem GO_sym (b b' : Fin d → ℕ) : GO C V b b' ∈ SY :=
  sub_mem (FCO_mem_sym C (πobs_mem_sym (H.Vpr_sym b)) (H.Vpr_sym b'))
    (FCO_mem_sym C (H.Vpr_sym b) (πobs_mem_sym (H.Vpr_sym b')))

theorem Sb_sym (b : Fin d → ℕ) : SbO j C V W b ∈ SY :=
  add_mem (add_mem (Subalgebra.smul_mem _ (FCO_mem_sym C (H.Vpr_sym b) H.VprL_sym) _)
    (H.SCor_sym b)) (EthO_mem_sym C (H.hW b))

omit H in
theorem LS_sym (b : Fin d → ℕ) : LSO P j C V W b ∈ SY := LocO2_mem_sym P _ _ _

theorem uVp_sym (b : Fin d → ℕ) : uVpO P j C V W K b ∈ SY :=
  sub_mem (sub_mem (H.Vpr_sym b) (EthO_mem_sym C (H.Q2O_sym b))) (LS_sym b)

theorem up_sym (b : Fin d → ℕ) : upO P j C V W K b ∈ SY :=
  πobs_mem_sym (epsO_mem_sym (H.uVp_sym b))

theorem Vp_sym (b : Fin d → ℕ) : VpO P j C V W K b ∈ SY :=
  sub_mem (sub_mem (H.uVp_sym b) (Subalgebra.algebraMap_mem _ _)) (H.up_sym b)

theorem Wp_sym (b : Fin d → ℕ) : WpO P j C V W b ∈ SY := sub_mem (H.Sb_sym b) (LS_sym b)

theorem Gp_sym (b : Fin d → ℕ) : GpO P j C V W K b ∈ SY :=
  mul_mem (oexp_mem (neg_mem (H.Vp_sym b))) (add_mem (one_mem _) (H.Wp_sym b))

theorem Ip_sym (b : Fin d → ℕ) : IpO P j C V W K b ∈ SY :=
  mul_mem (expU_mem _ (neg_mem (H.up_sym b))) (H.Gp_sym b)

theorem Ib_sym (b : Fin d → ℕ) : IbO V W b ∈ SY :=
  mul_mem (oexp_mem (neg_mem (H.hV b))) (add_mem (one_mem _) (H.hW b))

theorem ogmem (U : Finset (Lam d L N)) :
    OGMem j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U SY
      (symSub : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) where
  hθ _ hF := thetaO_mem_sym hF
  hι _ hF := inclO_mem_sym hF
  hE _ hF := ECCO_mem_sym C hF
  hK Y hY _ := H.hK Y hY
  hJ b X _ _ := J2O_sym b X
  hIb b _ _ := H.Ib_sym b
  hIp b _ _ := H.Ip_sym b

theorem Knext2_sym {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    Knext2O P j C V W K U ∈ SY :=
  mul_mem (expU_mem _ (Subalgebra.sum_mem _ fun b _ => H.up_sym b))
    ((H.ogmem (P := P) (C := C) U).gKnextO_mem hU)

theorem k2_sym (X : Finset (Lam d L N)) : k2O j C V X ∈ SY := by
  unfold k2O; split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => sub_mem (Subalgebra.smul_mem _
      (FCO_mem_sym C (H.Vpr_sym b) (sub_mem H.VprL_sym (H.Vpr_sym b))) _) (H.SCor_sym b)
  · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => Subalgebra.sum_mem _
      fun b' _ => FCO_mem_sym C (H.Vpr_sym b) (H.Vpr_sym b')) _
  · exact zero_mem _

theorem K2_sym (U : Finset (Lam d L N)) : K2O j C V U ∈ SY := by
  classical
  unfold K2O
  exact Subalgebra.sum_mem _ fun X _ => H.k2_sym X

theorem Knew_sym {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnewO P j C V W K U ∈ SY :=
  sub_mem (H.Knext2_sym hU) (mul_mem (prod_mem fun b _ => H.Gp_sym b) (H.K2_sym U))

theorem kap_sym (X : Finset (Lam d L N)) (c' : Fin d → ℕ) : kapO j C V X c' ∈ SY := by
  unfold kapO; split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => sub_mem (Subalgebra.smul_mem _
      (FCO_mem_sym C (H.Vpr_sym b) (sub_mem H.VprL_sym (H.Vpr_sym b))) _) (H.SCor_sym b)
  · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => Subalgebra.sum_mem _
      fun b' _ => add_mem (FCO_mem_sym C (H.Vpr_sym b) (H.Vpr_sym b')) (H.GO_sym b b')) _
  · exact zero_mem _

theorem Jh_sym (c' : Fin d → ℕ) (U : Finset (Lam d L N)) : JhO j C V c' U ∈ SY := by
  classical
  unfold JhO; split_ifs
  · exact Subalgebra.sum_mem _ fun X _ => H.kap_sym X c'
  · exact zero_mem _

/-- **`U(1)` invariance of `K_{j+1}` with sources.** -/
theorem Kplus_sym (U : Finset (Lam d L N)) : KplusO P j C V W K U ∈ SY := by
  refine KoutO_mem (S := SY) ?_ ?_ ?_
  · intro X _ _
    exact prod_mem fun c' _ => prod_mem fun b _ => H.Gp_sym b
  · intro Y hY _
    exact H.Knew_sym hY.1
  · intro p _ _
    exact H.Jh_sym p.1 p.2

theorem Vnext_sym (c' : Fin d → ℕ) : Vnext2O P j C V W K c' ∈ SY :=
  Subalgebra.sum_mem _ fun b _ => H.Vp_sym b

theorem Wnext_sym (c' : Fin d → ℕ) : Wnext2O P j C V W c' ∈ SY :=
  sub_mem (prod_mem fun b _ => add_mem (one_mem _) (H.Wp_sym b)) (one_mem _)

/-- **Propagation of `U(1)` invariance by one step of the map with sources.** -/
theorem step :
    OSymS (j + 1) (Vnext2O P j C V W K) (Wnext2O P j C V W)
      (KconnO (j + 1) (KplusO P j C V W K)) where
  hV c' := H.Vnext_sym c'
  hW c' := H.Wnext_sym c'
  hK Y hY := by
    unfold KconnO
    rw [if_pos hY]
    exact H.Kplus_sym Y

end OSymS

end

end Obs2
