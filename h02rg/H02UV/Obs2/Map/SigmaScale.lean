import Obs2.Map.SymO

/-!
# The `σ_a`, `σ_b` scaling: zero one-point sectors are preserved by the map with sources

The scaling `σ_a ↦ tσ_a`, `σ_b ↦ t⁻¹σ_b` (`t ≠ 0`, `t² ≠ 1`) acts on `F = F_∅ + σ_aF_a + σ_bF_b +
σ_aσ_bF_{ab}` by `F_a ↦ tF_a`, `F_b ↦ t⁻¹F_b`; it is an algebra automorphism, and every operation of
the map with sources (`Obs2.Map.Map`) is componentwise, so it commutes with it (the analogue of the
`U(1)` invariance `Obs2.Map.SymO`). Its fixed points are the elements with **no `σ_a`, `σ_b` parts**,
the subalgebra `abSub` (`F_a = F_b = 0`). We use the fixed-point form directly:

* `abSub`: the subalgebra `{F | F_a = F_b = 0}` (closed under products since `σ_a² = σ_b² = 0` play
  no role: `(FG)_a = F_eG_a + F_aG_e`);
* stability under `θ`, `ι`, `𝔼_C`, `e^{ℒ_C}`, `𝔼_Cθ`, `F_C`, `ε`, `π_obs`, `emb`, `e^{·}` and
  `Loc_{X,Y}` (`LocO2_mem_ab`, componentwise linear);
* **`OAbS.step`**: if `V(B)`, `𝒲(B)`, `K(X)` (`X` connected) have no `σ_a`, `σ_b` parts, neither do
  `V_{j+1}`, `𝒲_{j+1}`, `K_{j+1}` (connected polymers), nor `u^{obs}_{j+1}` (`uObsTot_mem_ab`).

This is step PR2 of the Pauli-reduced pair observable: a history started from a state without
one-point parts keeps none.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD PolyAux

section Sub

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ]

/-- **The elements without `σ_a`, `σ_b` parts** (fixed points of the `σ` scaling). -/
def abSub : Subalgebra ℂ (OE c Λ) where
  carrier := {F | (F : SA c Λ).a = 0 ∧ (F : SA c Λ).b = 0}
  mul_mem' := by
    rintro F G ⟨fa, fb⟩ ⟨ga, gb⟩
    refine ⟨?_, ?_⟩
    · rw [OE.mul_a, fa, ga]; simp
    · rw [OE.mul_b, fb, gb]; simp
  add_mem' := by
    rintro F G ⟨fa, fb⟩ ⟨ga, gb⟩
    exact ⟨by simp [fa, ga], by simp [fb, gb]⟩
  algebraMap_mem' r := ⟨by simp, by simp⟩

theorem mem_abSub {F : OE c Λ} :
    F ∈ (abSub : Subalgebra ℂ (OE c Λ)) ↔ (F : SA c Λ).a = 0 ∧ (F : SA c Λ).b = 0 := Iff.rfl

end Sub

section Ops

variable {c : Obs.Case} {d L N : ℕ} [NeZero L]

local notation "AB" => (abSub : Subalgebra ℂ (OE c (Lam d L N)))
local notation "AB2" => (abSub : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)))

theorem thetaO_mem_ab {F : OE c (Lam d L N)} (hF : F ∈ AB) : thetaO F ∈ AB2 := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_⟩
  · show (thetaS (F : SA c (Lam d L N))).a = 0; rw [thetaS_a, ha, map_zero]
  · show (thetaS (F : SA c (Lam d L N))).b = 0; rw [thetaS_b, hb, map_zero]

theorem inclO_mem_ab {F : OE c (Lam d L N)} (hF : F ∈ AB) : inclO F ∈ AB2 := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_⟩
  · show (inclS (F : SA c (Lam d L N))).a = 0; rw [inclS_a, ha, map_zero]
  · show (inclS (F : SA c (Lam d L N))).b = 0; rw [inclS_b, hb, map_zero]

theorem ECCO_mem_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N ⊕ Lam d L N)}
    (hF : F ∈ AB2) : ECCO C F ∈ AB := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_⟩
  · rw [coe_ECCO, ECCS_a, ha, map_zero]
  · rw [coe_ECCO, ECCS_b, hb, map_zero]

theorem expO_mem_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ AB) : expO C F ∈ AB := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_⟩
  · rw [coe_expO, expS_a, ha, map_zero]
  · rw [coe_expO, expS_b, hb, map_zero]

theorem EthO_mem_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ AB) : EthO C F ∈ AB :=
  ECCO_mem_ab C (thetaO_mem_ab hF)

theorem FCO_mem_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : OE c (Lam d L N)}
    (hA : A ∈ AB) (hB : B ∈ AB) : FCO C A B ∈ AB :=
  sub_mem (expO_mem_ab C (mul_mem (expO_mem_ab _ hA) (expO_mem_ab _ hB))) (mul_mem hA hB)

theorem epsO_mem_ab {F : OE c (Lam d L N)} (hF : F ∈ AB) : epsO F ∈ AB := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_⟩
  · show (epsS (F : SA c (Lam d L N))).a = 0; rw [epsS, mapS_a, ha, map_zero]
  · show (epsS (F : SA c (Lam d L N))).b = 0; rw [epsS, mapS_b, hb, map_zero]

theorem πobs_mem_ab {F : OE c (Lam d L N)} (hF : F ∈ AB) : πobs F ∈ AB := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_⟩
  · rw [coe_πobs, piobs_apply]; exact ha
  · rw [coe_πobs, piobs_apply]; exact hb

theorem emb_mem_ab (x : EvR (Lam d L N)) : (emb x : OE c (Lam d L N)) ∈ AB :=
  ⟨by simp [emb], by simp [emb]⟩

theorem LocO2_mem_ab (P : ObsPts d L N) (X Y : Finset (Lam d L N)) {F : OE c (Lam d L N)}
    (hF : F ∈ AB) : LocO2 P X Y F ∈ AB := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_⟩
  · show locAp c P.a X Y (F : SA c (Lam d L N)).a = 0
    rw [ha]; simpa using locAp_smul (c := c) P.a X Y (0 : ℂ) (0 : Alg d L N)
  · show locBp c P.b X Y (F : SA c (Lam d L N)).b = 0
    rw [hb]; simpa using locBp_smul (c := c) P.b X Y (0 : ℂ) (0 : Alg d L N)

end Ops

/-! ### One step -/

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **No `σ_a`, `σ_b` parts in the input of one step with sources.** -/
structure OAbS (j : ℕ) (V W : OFam c d L N) (K : OAct c d L N) : Prop where
  hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))
  hW : ∀ b, W b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))
  hK : ∀ Y, IsConn j Y → K Y ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))

namespace OAbS

variable {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} (H : OAbS j V W K)
include H

local notation "AB" => (abSub : Subalgebra ℂ (OE c (Lam d L N)))

theorem Vpr_ab (b : Fin d → ℕ) : VprO C V b ∈ AB := EthO_mem_ab C (H.hV b)

theorem Q2O_ab (b : Fin d → ℕ) : Q2O P j K b ∈ AB := by
  unfold Q2O; split_ifs
  · refine Subalgebra.sum_mem _ fun X hX => LocO2_mem_ab P _ _ (H.hK X ?_)
    have hs := mem_smallSets.1 (mem_filter.1 hX).1
    exact ⟨hs.1, hs.2.1⟩
  · exact zero_mem _

theorem J2O_ab (b : Fin d → ℕ) (X : Finset (Lam d L N)) : J2O P j K b X ∈ AB := by
  unfold J2O; split_ifs with h1 h2
  · refine neg_mem (Subalgebra.sum_mem _ fun Y hY => LocO2_mem_ab P _ _ (H.hK Y ?_))
    have hs := mem_smallSets.1 (mem_filter.1 hY).1
    exact ⟨hs.1, hs.2.1⟩
  · exact LocO2_mem_ab P _ _ (H.hK X ⟨h1.2.1.1, h1.2.1.2.1⟩)
  · exact zero_mem _

theorem VprL_ab : VprLO j C V ∈ AB := Subalgebra.sum_mem _ fun b _ => H.Vpr_ab b

theorem SCor_ab (b : Fin d → ℕ) : SCorO j C V b ∈ AB :=
  Subalgebra.smul_mem _ (sub_mem (FCO_mem_ab C (πobs_mem_ab (H.Vpr_ab b)) H.VprL_ab)
    (FCO_mem_ab C (H.Vpr_ab b) (πobs_mem_ab H.VprL_ab))) _

theorem GO_ab (b b' : Fin d → ℕ) : GO C V b b' ∈ AB :=
  sub_mem (FCO_mem_ab C (πobs_mem_ab (H.Vpr_ab b)) (H.Vpr_ab b'))
    (FCO_mem_ab C (H.Vpr_ab b) (πobs_mem_ab (H.Vpr_ab b')))

theorem Sb_ab (b : Fin d → ℕ) : SbO j C V W b ∈ AB :=
  add_mem (add_mem (Subalgebra.smul_mem _ (FCO_mem_ab C (H.Vpr_ab b) H.VprL_ab) _)
    (H.SCor_ab b)) (EthO_mem_ab C (H.hW b))

theorem LS_ab (b : Fin d → ℕ) : LSO P j C V W b ∈ AB :=
  LocO2_mem_ab P _ _ (Subalgebra.sum_mem _ fun b' _ => H.Sb_ab b')

theorem uVp_ab (b : Fin d → ℕ) : uVpO P j C V W K b ∈ AB :=
  sub_mem (sub_mem (H.Vpr_ab b) (EthO_mem_ab C (H.Q2O_ab b))) (H.LS_ab b)

theorem up_ab (b : Fin d → ℕ) : upO P j C V W K b ∈ AB :=
  πobs_mem_ab (epsO_mem_ab (H.uVp_ab b))

theorem Vp_ab (b : Fin d → ℕ) : VpO P j C V W K b ∈ AB :=
  sub_mem (sub_mem (H.uVp_ab b) (Subalgebra.algebraMap_mem _ _)) (H.up_ab b)

theorem Wp_ab (b : Fin d → ℕ) : WpO P j C V W b ∈ AB := sub_mem (H.Sb_ab b) (H.LS_ab b)

theorem Gp_ab (b : Fin d → ℕ) : GpO P j C V W K b ∈ AB :=
  mul_mem (oexp_mem (neg_mem (H.Vp_ab b))) (add_mem (one_mem _) (H.Wp_ab b))

theorem Ip_ab (b : Fin d → ℕ) : IpO P j C V W K b ∈ AB :=
  mul_mem (expU_mem _ (neg_mem (H.up_ab b))) (H.Gp_ab b)

theorem Ib_ab (b : Fin d → ℕ) : IbO V W b ∈ AB :=
  mul_mem (oexp_mem (neg_mem (H.hV b))) (add_mem (one_mem _) (H.hW b))

theorem ogmem (U : Finset (Lam d L N)) :
    OGMem j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U AB
      (abSub : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) where
  hθ _ hF := thetaO_mem_ab hF
  hι _ hF := inclO_mem_ab hF
  hE _ hF := ECCO_mem_ab C hF
  hK Y hY _ := H.hK Y hY
  hJ b X _ _ := H.J2O_ab b X
  hIb b _ _ := H.Ib_ab b
  hIp b _ _ := H.Ip_ab b

theorem Knext2_ab {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    Knext2O P j C V W K U ∈ AB :=
  mul_mem (expU_mem _ (Subalgebra.sum_mem _ fun b _ => H.up_ab b))
    ((H.ogmem (P := P) (C := C) U).gKnextO_mem hU)

theorem k2_ab (X : Finset (Lam d L N)) : k2O j C V X ∈ AB := by
  unfold k2O; split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => sub_mem (Subalgebra.smul_mem _
      (FCO_mem_ab C (H.Vpr_ab b) (sub_mem H.VprL_ab (H.Vpr_ab b))) _) (H.SCor_ab b)
  · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => Subalgebra.sum_mem _
      fun b' _ => FCO_mem_ab C (H.Vpr_ab b) (H.Vpr_ab b')) _
  · exact zero_mem _

theorem K2_ab (U : Finset (Lam d L N)) : K2O j C V U ∈ AB := by
  classical
  unfold K2O
  exact Subalgebra.sum_mem _ fun X _ => H.k2_ab X

theorem Knew_ab {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnewO P j C V W K U ∈ AB :=
  sub_mem (H.Knext2_ab hU) (mul_mem (prod_mem fun b _ => H.Gp_ab b) (H.K2_ab U))

theorem kap_ab (X : Finset (Lam d L N)) (c' : Fin d → ℕ) : kapO j C V X c' ∈ AB := by
  unfold kapO; split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => sub_mem (Subalgebra.smul_mem _
      (FCO_mem_ab C (H.Vpr_ab b) (sub_mem H.VprL_ab (H.Vpr_ab b))) _) (H.SCor_ab b)
  · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => Subalgebra.sum_mem _
      fun b' _ => add_mem (FCO_mem_ab C (H.Vpr_ab b) (H.Vpr_ab b')) (H.GO_ab b b')) _
  · exact zero_mem _

theorem Jh_ab (c' : Fin d → ℕ) (U : Finset (Lam d L N)) : JhO j C V c' U ∈ AB := by
  classical
  unfold JhO; split_ifs
  · exact Subalgebra.sum_mem _ fun X _ => H.kap_ab X c'
  · exact zero_mem _

/-- **No `σ_a`, `σ_b` parts in `K_{j+1}` with sources.** -/
theorem Kplus_ab (U : Finset (Lam d L N)) : KplusO P j C V W K U ∈ AB := by
  refine KoutO_mem (S := AB) ?_ ?_ ?_
  · intro X _ _
    exact prod_mem fun c' _ => prod_mem fun b _ => H.Gp_ab b
  · intro Y hY _
    exact H.Knew_ab hY.1
  · intro p _ _
    exact H.Jh_ab p.1 p.2

theorem Vnext_ab (c' : Fin d → ℕ) : Vnext2O P j C V W K c' ∈ AB :=
  Subalgebra.sum_mem _ fun b _ => H.Vp_ab b

theorem Wnext_ab (c' : Fin d → ℕ) : Wnext2O P j C V W c' ∈ AB :=
  sub_mem (prod_mem fun b _ => add_mem (one_mem _) (H.Wp_ab b)) (one_mem _)

theorem uXO_ab (X : Finset (Lam d L N)) : uXO P j C V W K X ∈ AB :=
  Subalgebra.sum_mem _ fun b _ => H.up_ab b

/-- **The zero one-point sectors are preserved by one step of the map with sources.** -/
theorem step :
    OAbS (j + 1) (Vnext2O P j C V W K) (Wnext2O P j C V W)
      (KconnO (j + 1) (KplusO P j C V W K)) where
  hV c' := H.Vnext_ab c'
  hW c' := H.Wnext_ab c'
  hK Y hY := by
    unfold KconnO
    rw [if_pos hY]
    exact H.Kplus_ab Y

end OAbS

end

end Obs2
