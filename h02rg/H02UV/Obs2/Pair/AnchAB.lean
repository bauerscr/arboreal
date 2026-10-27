import Obs2.Map.SigmaScale
import Obs2.Loc.LocFlow

/-!
# Anchoring of the `σ_aσ_b` sector: `ab` parts only on polymers meeting `{a, b}`

On the reduced history (no one-point parts, `Obs2.abSub`) the `σ_aσ_b` components of the
activities are produced linearly from `σ_aσ_b` components (`π_{ab}(FG) = F_∅G_{ab} + F_{ab}G_∅`).
The barycentric `loc^{ab}_{X,Y}` (`Obs2.locABtXY`) vanishes for `X ∩ {a, b} = ∅`, so the
contraction `(1 - loc^{ab})` (`exists_locABt_contract`, based at a point of `X`) is available only
on polymers meeting `{a, b}`. This file shows that on `abSub` nothing else occurs: **the `ab` part
of `V(B)`, `𝒲(B)`, `K(Y)` vanishes unless `B` (resp. `Y`) meets `{a, b}`**, and this is preserved
by one step of the map with sources.

* `anchSub p`: `{F | F_a = F_b = 0, ¬p → F_{ab} = 0}` (a subalgebra; `anchSub True = abSub`,
  `anchSub False` = bulk elements);
* stability under `θ`, `ι`, `𝔼_C`, `e^{ℒ_C}`, `𝔼_Cθ`, `F_C`, `ε`, `π_obs`, `emb`, `e^·`;
  `Loc_{X,Y}` maps `abSub` into `anchSub (Y ∩ {a,b} ≠ ∅)` (`LocO2_mem_anch`, the barycentric
  `loc^{ab}` carries the factor `|Y ∩ {a,b}|`);
* `SFO_mem_anch`: the sharp splitting `S^♯(B)` is anchored at `B`
  (`S^♯(B) = ½F_C(V'_B, V'(Λ)^∅) + ½F_C(π_{obs}V'_B, V'(Λ))`);
* **`OAnchS.step`**: if `V(B)`, `𝒲(B)` are anchored at `B` and `K(Y)` at `Y`, the outputs
  `V_{j+1}`, `𝒲_{j+1}`, `K_{j+1}` (connected polymers) are anchored at scale `j + 1`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD PolyAux

section Sub

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ]

/-- **Anchored elements**: no one-point parts, and no `σ_aσ_b` part unless `p`. -/
def anchSub (p : Prop) : Subalgebra ℂ (OE c Λ) where
  carrier := {F | (F : SA c Λ).a = 0 ∧ (F : SA c Λ).b = 0 ∧ (¬p → (F : SA c Λ).ab = 0)}
  mul_mem' := by
    rintro F G ⟨fa, fb, fab⟩ ⟨ga, gb, gab⟩
    refine ⟨?_, ?_, fun hp => ?_⟩
    · rw [OE.mul_a, fa, ga]; simp
    · rw [OE.mul_b, fb, gb]; simp
    · rw [OE.mul_ab, fa, fb, ga, fab hp, gab hp]; simp
  add_mem' := by
    rintro F G ⟨fa, fb, fab⟩ ⟨ga, gb, gab⟩
    exact ⟨by simp [fa, ga], by simp [fb, gb], fun hp => by simp [fab hp, gab hp]⟩
  algebraMap_mem' r := ⟨by simp, by simp, fun _ => by simp⟩

theorem anchSub_mono {p q : Prop} (h : p → q) {F : OE c Λ}
    (hF : F ∈ (anchSub p : Subalgebra ℂ (OE c Λ))) : F ∈ (anchSub q : Subalgebra ℂ (OE c Λ)) :=
  ⟨hF.1, hF.2.1, fun hq => hF.2.2 (fun hp => hq (h hp))⟩

theorem anchSub_ab {p : Prop} {F : OE c Λ} (hF : F ∈ (anchSub p : Subalgebra ℂ (OE c Λ))) :
    F ∈ (abSub : Subalgebra ℂ (OE c Λ)) := ⟨hF.1, hF.2.1⟩

theorem anchSub_of_ab {p : Prop} (hp : p) {F : OE c Λ}
    (hF : F ∈ (abSub : Subalgebra ℂ (OE c Λ))) : F ∈ (anchSub p : Subalgebra ℂ (OE c Λ)) :=
  ⟨hF.1, hF.2, fun h => absurd hp h⟩

/-- Without the anchor, an anchored element is bulk. -/
theorem πobs_eq_zero_of_anch {p : Prop} (hp : ¬p) {F : OE c Λ}
    (hF : F ∈ (anchSub p : Subalgebra ℂ (OE c Λ))) : πobs F = 0 := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [coe_πobs, piobs_apply]; rfl
  · rw [coe_πobs, piobs_apply]; exact hF.1
  · rw [coe_πobs, piobs_apply]; exact hF.2.1
  · rw [coe_πobs, piobs_apply]; exact hF.2.2 hp

end Sub

section Ops

variable {c : Obs.Case} {d L N : ℕ} [NeZero L] {p : Prop}

local notation "AN" => (anchSub p : Subalgebra ℂ (OE c (Lam d L N)))
local notation "AN2" => (anchSub p : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)))

theorem thetaO_mem_anch {F : OE c (Lam d L N)} (hF : F ∈ AN) : thetaO F ∈ AN2 := by
  obtain ⟨ha, hb, hab⟩ := hF
  refine ⟨?_, ?_, fun hp => ?_⟩
  · show (thetaS (F : SA c (Lam d L N))).a = 0; rw [thetaS_a, ha, map_zero]
  · show (thetaS (F : SA c (Lam d L N))).b = 0; rw [thetaS_b, hb, map_zero]
  · show (thetaS (F : SA c (Lam d L N))).ab = 0; rw [thetaS_ab, hab hp, map_zero]

theorem inclO_mem_anch {F : OE c (Lam d L N)} (hF : F ∈ AN) : inclO F ∈ AN2 := by
  obtain ⟨ha, hb, hab⟩ := hF
  refine ⟨?_, ?_, fun hp => ?_⟩
  · show (inclS (F : SA c (Lam d L N))).a = 0; rw [inclS_a, ha, map_zero]
  · show (inclS (F : SA c (Lam d L N))).b = 0; rw [inclS_b, hb, map_zero]
  · show (inclS (F : SA c (Lam d L N))).ab = 0; rw [inclS_ab, hab hp, map_zero]

theorem ECCO_mem_anch (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N ⊕ Lam d L N)}
    (hF : F ∈ AN2) : ECCO C F ∈ AN := by
  obtain ⟨ha, hb, hab⟩ := hF
  refine ⟨?_, ?_, fun hp => ?_⟩
  · rw [coe_ECCO, ECCS_a, ha, map_zero]
  · rw [coe_ECCO, ECCS_b, hb, map_zero]
  · rw [coe_ECCO, ECCS_ab, hab hp, map_zero]

theorem expO_mem_anch (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ AN) : expO C F ∈ AN := by
  obtain ⟨ha, hb, hab⟩ := hF
  refine ⟨?_, ?_, fun hp => ?_⟩
  · rw [coe_expO, expS_a, ha, map_zero]
  · rw [coe_expO, expS_b, hb, map_zero]
  · rw [coe_expO, expS_ab, hab hp, map_zero]

theorem EthO_mem_anch (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ AN) : EthO C F ∈ AN :=
  ECCO_mem_anch C (thetaO_mem_anch hF)

theorem FCO_mem_anch (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : OE c (Lam d L N)}
    (hA : A ∈ AN) (hB : B ∈ AN) : FCO C A B ∈ AN :=
  sub_mem (expO_mem_anch C (mul_mem (expO_mem_anch _ hA) (expO_mem_anch _ hB))) (mul_mem hA hB)

theorem epsO_mem_anch {F : OE c (Lam d L N)} (hF : F ∈ AN) : epsO F ∈ AN := by
  obtain ⟨ha, hb, hab⟩ := hF
  refine ⟨?_, ?_, fun hp => ?_⟩
  · show (epsS (F : SA c (Lam d L N))).a = 0; rw [epsS, mapS_a, ha, map_zero]
  · show (epsS (F : SA c (Lam d L N))).b = 0; rw [epsS, mapS_b, hb, map_zero]
  · show (epsS (F : SA c (Lam d L N))).ab = 0; rw [epsS, mapS_ab, hab hp, map_zero]

theorem πobs_mem_anch {F : OE c (Lam d L N)} (hF : F ∈ AN) : πobs F ∈ AN := by
  obtain ⟨ha, hb, hab⟩ := hF
  refine ⟨?_, ?_, fun hp => ?_⟩
  · rw [coe_πobs, piobs_apply]; exact ha
  · rw [coe_πobs, piobs_apply]; exact hb
  · rw [coe_πobs, piobs_apply]; exact hab hp

theorem emb_mem_anch (x : EvR (Lam d L N)) : (emb x : OE c (Lam d L N)) ∈ AN :=
  ⟨by simp [emb], by simp [emb], fun _ => by simp [emb]⟩

/-- **`Loc_{X,Y}` anchors at `Y`**: the barycentric `loc^{ab}_{X,Y}` carries `|Y ∩ {a,b}|`. -/
theorem LocO2_mem_anch (P : ObsPts d L N) (X Y : Finset (Lam d L N)) {F : OE c (Lam d L N)}
    (hF : F ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) :
    LocO2 P X Y F ∈ (anchSub (Y ∩ P.pts).Nonempty : Subalgebra ℂ (OE c (Lam d L N))) := by
  obtain ⟨ha, hb⟩ := hF
  refine ⟨?_, ?_, fun hY => ?_⟩
  · show locAp c P.a X Y (F : SA c (Lam d L N)).a = 0
    rw [ha]; simpa using locAp_smul (c := c) P.a X Y (0 : ℂ) (0 : Alg d L N)
  · show locBp c P.b X Y (F : SA c (Lam d L N)).b = 0
    rw [hb]; simpa using locBp_smul (c := c) P.b X Y (0 : ℂ) (0 : Alg d L N)
  · show locABtXY P X Y (F : SA c (Lam d L N)).ab = 0
    rw [locABtXY, Finset.not_nonempty_iff_eq_empty.1 hY, card_empty, Nat.cast_zero, zero_div,
      zero_smul]

end Ops

/-! ### The sharp splitting is anchored at its block -/

section SF

variable {c : Obs.Case} {d L N : ℕ} [NeZero L]

theorem FCO_mem_anch_of_obs {p : Prop} (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    {A B : OE c (Lam d L N)} (hA : A ∈ (anchSub p : Subalgebra ℂ (OE c (Lam d L N))))
    (hB : B ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) :
    FCO C (πobs A) B ∈ (anchSub p : Subalgebra ℂ (OE c (Lam d L N))) := by
  by_cases hp : p
  · exact anchSub_of_ab hp (FCO_mem_ab C (πobs_mem_ab (anchSub_ab hA)) hB)
  · have h0 : FCO C (0 : OE c (Lam d L N)) B = 0 := by
      rw [FCO_comm, ← zero_smul ℂ (0 : OE c (Lam d L N)), FCO_smul_right, zero_smul, zero_smul]
    rw [πobs_eq_zero_of_anch hp hA, h0]; exact zero_mem _

/-- `S^♯(B) = ½F_C(V'_B, V'(Λ)^∅) + ½F_C(π_{obs}V'_B, V'(Λ))`. -/
theorem SFO_eq_anch (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : OFam c d L N)
    (b : Fin d → ℕ) :
    SFO j C V b = (1 / 2 : ℂ) • FCO C (VprO C V b) (emb (bulk (VprLO j C V))) +
      (1 / 2 : ℂ) • FCO C (πobs (VprO C V b)) (VprLO j C V) := by
  have h : emb (bulk (VprLO j C V)) = VprLO j C V - πobs (VprLO j C V) := by
    nth_rewrite 2 [eq_emb_add_πobs (VprLO j C V)]; abel
  rw [SFO, SCorO, h, FCO_sub_right', smul_sub, smul_sub]
  abel

theorem SFO_mem_anch {p : Prop} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : OFam c d L N) (b : Fin d → ℕ)
    (hb : VprO C V b ∈ (anchSub p : Subalgebra ℂ (OE c (Lam d L N))))
    (hL : VprLO j C V ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) :
    SFO j C V b ∈ (anchSub p : Subalgebra ℂ (OE c (Lam d L N))) := by
  rw [SFO_eq_anch]
  exact add_mem (Subalgebra.smul_mem _ (FCO_mem_anch C hb (emb_mem_anch _)) _)
    (Subalgebra.smul_mem _ (FCO_mem_anch_of_obs C hb hL) _)

end SF

/-! ### One step -/

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The anchor of a set: it meets `{a, b}`. -/
abbrev anc (P : ObsPts d L N) (S : Finset (Lam d L N)) : Subalgebra ℂ (OE c (Lam d L N)) :=
  anchSub (S ∩ P.pts).Nonempty

theorem anc_mono {P : ObsPts d L N} {S T : Finset (Lam d L N)} (h : S ⊆ T)
    {F : OE c (Lam d L N)} (hF : F ∈ (anc P S : Subalgebra ℂ (OE c (Lam d L N)))) :
    F ∈ (anc P T : Subalgebra ℂ (OE c (Lam d L N))) :=
  anchSub_mono (fun hS => hS.mono (inter_subset_inter_right h)) hF

/-- **Anchored input of one step with sources.** -/
structure OAnchS (P : ObsPts d L N) (j : ℕ) (V W : OFam c d L N) (K : OAct c d L N) : Prop where
  hV : ∀ b, V b ∈ (anc P (blockSet (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam d L N)))
  hW : ∀ b, W b ∈ (anc P (blockSet (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam d L N)))
  hK : ∀ Y, IsConn j Y → K Y ∈ (anc P Y : Subalgebra ℂ (OE c (Lam d L N)))

namespace OAnchS

variable {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} (H : OAnchS P j V W K)
include H

/-- Anchored inputs have no one-point parts. -/
theorem toAb : OAbS j V W K :=
  ⟨fun b => anchSub_ab (H.hV b), fun b => anchSub_ab (H.hW b),
    fun Y hY => anchSub_ab (H.hK Y hY)⟩

local notation "AC" S => (anc P S : Subalgebra ℂ (OE c (Lam d L N)))

theorem Vpr_anch (b : Fin d → ℕ) : VprO C V b ∈ AC (blockSet (L := L) (N := N) j b) :=
  EthO_mem_anch C (H.hV b)

theorem Q2O_anch (b : Fin d → ℕ) : Q2O P j K b ∈ AC (blockSet (L := L) (N := N) j b) := by
  unfold Q2O; split_ifs
  · refine Subalgebra.sum_mem _ fun X hX => LocO2_mem_anch P _ _ (H.toAb.hK X ?_)
    have hs := mem_smallSets.1 (mem_filter.1 hX).1
    exact ⟨hs.1, hs.2.1⟩
  · exact zero_mem _

theorem J2O_anch (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    J2O P j K b X ∈ AC (blockSet (L := L) (N := N) j b) := by
  unfold J2O; split_ifs with h1 h2
  · refine neg_mem (Subalgebra.sum_mem _ fun Y hY => LocO2_mem_anch P _ _ (H.toAb.hK Y ?_))
    have hs := mem_smallSets.1 (mem_filter.1 hY).1
    exact ⟨hs.1, hs.2.1⟩
  · exact LocO2_mem_anch P _ _ (H.toAb.hK X ⟨h1.2.1.1, h1.2.1.2.1⟩)
  · exact zero_mem _

theorem SF_anch (b : Fin d → ℕ) : SFO j C V b ∈ AC (blockSet (L := L) (N := N) j b) :=
  SFO_mem_anch j C V b (H.Vpr_anch b) (H.toAb.VprL_ab)

theorem Sb_anch (b : Fin d → ℕ) : SbO j C V W b ∈ AC (blockSet (L := L) (N := N) j b) :=
  add_mem (H.SF_anch b) (EthO_mem_anch C (H.hW b))

theorem LS_anch (b : Fin d → ℕ) : LSO P j C V W b ∈ AC (blockSet (L := L) (N := N) j b) :=
  LocO2_mem_anch P _ _ (Subalgebra.sum_mem _ fun b' _ => H.toAb.Sb_ab b')

theorem uVp_anch (b : Fin d → ℕ) : uVpO P j C V W K b ∈ AC (blockSet (L := L) (N := N) j b) :=
  sub_mem (sub_mem (H.Vpr_anch b) (EthO_mem_anch C (H.Q2O_anch b))) (H.LS_anch b)

theorem up_anch (b : Fin d → ℕ) : upO P j C V W K b ∈ AC (blockSet (L := L) (N := N) j b) :=
  πobs_mem_anch (epsO_mem_anch (H.uVp_anch b))

theorem Vp_anch (b : Fin d → ℕ) : VpO P j C V W K b ∈ AC (blockSet (L := L) (N := N) j b) :=
  sub_mem (sub_mem (H.uVp_anch b) (Subalgebra.algebraMap_mem _ _)) (H.up_anch b)

theorem Wp_anch (b : Fin d → ℕ) : WpO P j C V W b ∈ AC (blockSet (L := L) (N := N) j b) :=
  sub_mem (H.Sb_anch b) (H.LS_anch b)

theorem Gp_anch (b : Fin d → ℕ) : GpO P j C V W K b ∈ AC (blockSet (L := L) (N := N) j b) :=
  mul_mem (oexp_mem (neg_mem (H.Vp_anch b))) (add_mem (one_mem _) (H.Wp_anch b))

theorem Ip_anch (b : Fin d → ℕ) : IpO P j C V W K b ∈ AC (blockSet (L := L) (N := N) j b) :=
  mul_mem (expU_mem _ (neg_mem (H.up_anch b))) (H.Gp_anch b)

theorem Ib_anch (b : Fin d → ℕ) : IbO V W b ∈ AC (blockSet (L := L) (N := N) j b) :=
  mul_mem (oexp_mem (neg_mem (H.hV b))) (add_mem (one_mem _) (H.hW b))

theorem ogmem (U : Finset (Lam d L N)) :
    OGMem j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U (AC U)
      (anchSub (U ∩ P.pts).Nonempty : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N))) where
  hθ _ hF := thetaO_mem_anch hF
  hι _ hF := inclO_mem_anch hF
  hE _ hF := ECCO_mem_anch C hF
  hK Y hY hYU := anc_mono hYU (H.hK Y hY)
  hJ b X _ hbU := anc_mono hbU (H.J2O_anch b X)
  hIb b _ hbU := anc_mono hbU (H.Ib_anch b)
  hIp b _ hbU := anc_mono hbU (H.Ip_anch b)

theorem uXO_anch {U : Finset (Lam d L N)} (hU : IsPolymer j U) : uXO P j C V W K U ∈ AC U :=
  Subalgebra.sum_mem _ fun b hb => anc_mono (blockSet_subset hU hb) (H.up_anch b)

theorem Knext2_anch {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    Knext2O P j C V W K U ∈ AC U :=
  mul_mem (expU_mem _ (H.uXO_anch (IsPolymer.of_succ hU)))
    ((H.ogmem (C := C) U).gKnextO_mem hU)

theorem k2_anch (X : Finset (Lam d L N)) : k2O j C V X ∈ AC (clo j X) := by
  have hbX : ∀ b ∈ blocks j X, blockSet (L := L) (N := N) j b ⊆ clo j X := fun b hb =>
    blockSet_subset (IsPolymer.of_succ (isPolymer_clo j X)) (blocks_mono (subset_clo j X) hb)
  unfold k2O; split_ifs with h1 h2
  · refine Subalgebra.sum_mem _ fun b hb => ?_
    rw [k2one_eq]
    exact anc_mono (hbX b hb) (sub_mem (Subalgebra.smul_mem _
      (FCO_mem_anch C (H.Vpr_anch b) (H.Vpr_anch b)) _) (H.SF_anch b))
  · refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb => ?_) _
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    exact FCO_mem_anch C (anc_mono (hbX b hb) (H.Vpr_anch b))
      (anc_mono (hbX b' (mem_of_mem_erase hb')) (H.Vpr_anch b'))
  · exact zero_mem _

theorem K2_anch (U : Finset (Lam d L N)) : K2O j C V U ∈ AC U := by
  classical
  unfold K2O
  exact Subalgebra.sum_mem _ fun X hX => (mem_filter.1 hX).2 ▸ H.k2_anch X

theorem Knew_anch {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnewO P j C V W K U ∈ AC U := by
  refine sub_mem (H.Knext2_anch hU) (mul_mem ?_ (H.K2_anch U))
  exact prod_mem fun b hb => anc_mono (blockSet_subset (IsPolymer.of_succ hU) hb) (H.Gp_anch b)

theorem kap_anch (X : Finset (Lam d L N)) (c' : Fin d → ℕ) : kapO j C V X c' ∈ AC (clo j X) := by
  have hbX : ∀ b ∈ blocks j X, blockSet (L := L) (N := N) j b ⊆ clo j X := fun b hb =>
    blockSet_subset (IsPolymer.of_succ (isPolymer_clo j X)) (blocks_mono (subset_clo j X) hb)
  unfold kapO; split_ifs with h1 h2
  · refine Subalgebra.sum_mem _ fun b hb => ?_
    replace hb := (mem_filter.1 hb).1
    rw [k2one_eq]
    exact anc_mono (hbX b hb) (sub_mem (Subalgebra.smul_mem _
      (FCO_mem_anch C (H.Vpr_anch b) (H.Vpr_anch b)) _) (H.SF_anch b))
  · refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb => ?_) _
    replace hb := (mem_filter.1 hb).1
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    have h1 := anc_mono (hbX b hb) (H.Vpr_anch (C := C) b)
    have h2 := anc_mono (hbX b' (mem_of_mem_erase hb')) (H.Vpr_anch (C := C) b')
    exact add_mem (FCO_mem_anch C h1 h2) (sub_mem (FCO_mem_anch C (πobs_mem_anch h1) h2)
      (FCO_mem_anch C h1 (πobs_mem_anch h2)))
  · exact zero_mem _

theorem Jh_anch (c' : Fin d → ℕ) (U : Finset (Lam d L N)) : JhO j C V c' U ∈ AC U := by
  classical
  unfold JhO; split_ifs
  · exact Subalgebra.sum_mem _ fun X hX => (mem_filter.1 hX).2 ▸ H.kap_anch X c'
  · exact zero_mem _

/-- **`K_{j+1}(U)` is anchored at `U`.** -/
theorem Kplus_anch {U : Finset (Lam d L N)} : KplusO P j C V W K U ∈ AC U := by
  refine KoutO_mem (S := AC U) ?_ ?_ ?_
  · intro X hX hXU
    rw [bpow_ItO P j C V W K hX]
    exact prod_mem fun b hb => anc_mono ((blockSet_subset (IsPolymer.of_succ hX) hb).trans hXU)
      (H.Gp_anch b)
  · intro Y hY hYU
    exact anc_mono hYU (H.Knew_anch hY.1)
  · intro q _ hqU
    exact anc_mono hqU (H.Jh_anch q.1 q.2)

theorem Vnext_anch (c' : Fin d → ℕ) :
    Vnext2O P j C V W K c' ∈ AC (blockSet (L := L) (N := N) (j + 1) c') :=
  Subalgebra.sum_mem _ fun b hb => anc_mono
    (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb) (H.Vp_anch b)

theorem Wnext_anch (c' : Fin d → ℕ) :
    Wnext2O P j C V W c' ∈ AC (blockSet (L := L) (N := N) (j + 1) c') :=
  sub_mem (prod_mem fun b hb => add_mem (one_mem _) (anc_mono
    (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb) (H.Wp_anch b)))
    (one_mem _)

/-- **Anchoring is preserved by one step of the map with sources.** -/
theorem step :
    OAnchS P (j + 1) (Vnext2O P j C V W K) (Wnext2O P j C V W)
      (KconnO (j + 1) (KplusO P j C V W K)) where
  hV c' := H.Vnext_anch c'
  hW c' := H.Wnext_anch c'
  hK Y hY := by
    unfold KconnO
    rw [if_pos hY]
    exact H.Kplus_anch

end OAnchS

end

end Obs2
