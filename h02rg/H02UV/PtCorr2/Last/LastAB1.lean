import PtCorr2.Last.LastObsK2
import Obs2.Map.SwapO
import Obs2.Map.SigmaScale

/-!
# The `σ_aσ_b ↦ σ_a` swap on elements without one-point parts (Case 2)

On the subalgebra `abSub = {F | F_a = F_b = 0}` the map

  `swO : F_∅ + σ_aσ_bF_{ab} ↦ F_∅ + σ_aF_{ab}`

is multiplicative (`(FG)_{ab} = F_∅G_{ab} + F_{ab}G_∅` once `F_a = F_b = 0`, Case 2: `τ = id`,
`s = 1`), and it is componentwise, so it commutes with `θ`, the inclusion, `𝔼_C`, `e^{ℒ_C}`,
`ε`, `π_obs`, `e^{·}`. Hence (`sw_*`) it commutes with every map of the reference map without
localisation (`Obs2.Est.LastKO1`) on inputs in `abSub`: `S(B)`, `G'(B)`, `u'(B)` and

* **`sw_KNO`**: `swO K'(U) = K'_{swO V, swO 𝒲, swO K}(U)` (`U` a `(j+1)`-polymer).

The localisation `Loc^P` does not commute with `swO` (`loc^{ab}` versus `loc^a`); it enters `F_N`
only through `e^{u(Λ)}` (`PtCorr2.finG_eq`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen

/-! ### The swap -/

section Alg

variable {Λ : Type*} [DecidableEq Λ]

/-- `F ↦ F_∅ + σ_aF_{ab}` (as a function on `SA`). -/
def swS (F : SA .two Λ) : SA .two Λ := ⟨F.e, F.ab, 0, 0⟩

theorem swS_mem (F : OE .two Λ) : swS (F : SA .two Λ) ∈ OEv .two Λ := by
  obtain ⟨h1, -, -, h4⟩ := mem_OEv.1 F.2
  refine mem_OEv.2 ⟨h1, ?_, ?_, ?_⟩
  · show inv' (F : SA .two Λ).ab = Case.s .two • (F : SA .two Λ).ab
    rw [h4, Case.s_two, one_smul]
  · show inv' (0 : N Λ) = Case.s .two • (0 : N Λ); simp
  · show inv' (0 : N Λ) = (0 : N Λ); simp

/-- **The swap** `F_∅ + σ_aσ_bF_{ab} ↦ F_∅ + σ_aF_{ab}`. -/
def swO (F : OE .two Λ) : OE .two Λ := ⟨swS (F : SA .two Λ), swS_mem F⟩

theorem swO_add (F G : OE .two Λ) : swO (F + G) = swO F + swO G :=
  Subtype.ext (SA.ext rfl rfl (by simp [swS, swO]) (by simp [swS, swO]))

theorem swO_smul (r : ℂ) (F : OE .two Λ) : swO (r • F) = r • swO F :=
  Subtype.ext (SA.ext rfl rfl (by simp [swS, swO]) (by simp [swS, swO]))

theorem swO_zero : swO (0 : OE .two Λ) = 0 :=
  Subtype.ext (SA.ext rfl rfl rfl rfl)

theorem swO_neg (F : OE .two Λ) : swO (-F) = -swO F :=
  Subtype.ext (SA.ext rfl rfl (by simp [swS, swO]) (by simp [swS, swO]))

theorem swO_sub (F G : OE .two Λ) : swO (F - G) = swO F - swO G :=
  Subtype.ext (SA.ext rfl rfl (by simp [swS, swO]) (by simp [swS, swO]))

theorem swO_sum {ι : Type*} (s : Finset ι) (F : ι → OE .two Λ) :
    swO (∑ i ∈ s, F i) = ∑ i ∈ s, swO (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, swO_zero]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, swO_add, ih]

@[simp] theorem swO_e (F : OE .two Λ) : ((swO F : OE .two Λ) : SA .two Λ).e = (F : SA .two Λ).e := rfl
@[simp] theorem swO_a (F : OE .two Λ) : ((swO F : OE .two Λ) : SA .two Λ).a = (F : SA .two Λ).ab :=
  rfl
@[simp] theorem swO_b (F : OE .two Λ) : ((swO F : OE .two Λ) : SA .two Λ).b = 0 := rfl
@[simp] theorem swO_ab (F : OE .two Λ) : ((swO F : OE .two Λ) : SA .two Λ).ab = 0 := rfl

local notation "ABΛ" => (abSub : Subalgebra ℂ (OE Obs.Case.two Λ))

theorem bulk_swO (F : OE .two Λ) : bulk (swO F) = bulk F := rfl

theorem swO_mul {F : OE .two Λ} (hF : F ∈ ABΛ) (G : OE .two Λ) :
    swO (F * G) = swO F * swO G := by
  obtain ⟨ha, hb⟩ := hF
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [swO_e, Subalgebra.coe_mul, Subalgebra.coe_mul, SA.mul_e, SA.mul_e, swO_e, swO_e]
  · rw [swO_a, Subalgebra.coe_mul, Subalgebra.coe_mul, SA.mul_ab, SA.mul_a, ha, hb, swO_e, swO_a,
      swO_a]
    simp only [Case.tau_two, zero_mul, smul_zero, add_zero, swO_e]
  · rw [swO_b, Subalgebra.coe_mul, SA.mul_b, swO_b, swO_b, mul_zero, zero_mul, add_zero]
  · rw [swO_ab, Subalgebra.coe_mul, SA.mul_ab, swO_b, swO_ab, swO_ab, swO_b]
    simp only [mul_zero, zero_mul, smul_zero, add_zero, Case.tau_two, map_zero]

theorem swO_one : swO (1 : OE .two Λ) = 1 := Subtype.ext (SA.ext rfl rfl rfl rfl)

theorem swO_algebraMap (r : ℂ) : swO (algebraMap ℂ (OE .two Λ) r) = algebraMap ℂ (OE .two Λ) r := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [swS, swO]

theorem swO_pow {F : OE .two Λ} (hF : F ∈ ABΛ) (n : ℕ) : swO (F ^ n) = swO F ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, swO_one]
  | succ n ih => rw [pow_succ', pow_succ', swO_mul hF, ih]

theorem swO_prod {ι : Type*} (s : Finset ι) (F : ι → OE .two Λ) (hF : ∀ i ∈ s, F i ∈ ABΛ) :
    swO (∏ i ∈ s, F i) = ∏ i ∈ s, swO (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, prod_empty, swO_one]
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, swO_mul (hF i (mem_insert_self i s)),
      ih fun k hk => hF k (mem_insert_of_mem hk)]

theorem swO_πobs (F : OE .two Λ) : swO (πobs F) = πobs (swO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [swS, piobs_apply, swO]

theorem swO_epsO (F : OE .two Λ) : swO (epsO F) = epsO (swO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [swS, swO]

theorem swO_thetaO (F : OE .two Λ) : swO (thetaO F) = thetaO (swO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [swS, swO]

theorem swO_inclO (F : OE .two Λ) : swO (inclO F) = inclO (swO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [swS, swO]

variable [Fintype Λ]

theorem swO_ECCO (C : Matrix Λ Λ ℂ) (F : OE .two (Λ ⊕ Λ)) :
    swO (ECCO C F) = ECCO C (swO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [swS, swO]

theorem swO_expO (C : Matrix Λ Λ ℂ) (F : OE .two Λ) : swO (expO C F) = expO C (swO F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [swS, swO]

theorem swO_EthO (C : Matrix Λ Λ ℂ) (F : OE .two Λ) : swO (EthO C F) = EthO C (swO F) := by
  rw [EthO, EthO, swO_ECCO, swO_thetaO]

theorem expO_mem_abΛ (C : Matrix Λ Λ ℂ) {F : OE .two Λ} (hF : F ∈ ABΛ) : expO C F ∈ ABΛ := by
  obtain ⟨ha, hb⟩ := hF
  exact ⟨by rw [coe_expO, expS_a, ha, map_zero], by rw [coe_expO, expS_b, hb, map_zero]⟩

theorem swO_FCO (C : Matrix Λ Λ ℂ) {A B : OE .two Λ} (hA : A ∈ ABΛ) (hB : B ∈ ABΛ) :
    swO (FCO C A B) = FCO C (swO A) (swO B) := by
  rw [FCO, FCO, swO_sub, swO_expO, swO_mul (expO_mem_abΛ _ hA), swO_mul hA, swO_expO, swO_expO]

theorem oexp_mem_abΛ {F : OE .two Λ} (hF : F ∈ ABΛ) : oexp F ∈ ABΛ := by
  by_cases h : IsNilpotent F
  · obtain ⟨n, hn⟩ := h
    rw [coe_oexp hn]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (pow_mem hF i) _
  · rw [oexp, nilExp_of_not h]; exact zero_mem _

theorem swO_oexp {F : OE .two Λ} (hF : F ∈ ABΛ) : swO (oexp F) = oexp (swO F) := by
  by_cases h : IsNilpotent F
  · obtain ⟨n, hn⟩ := h
    have hn' : swO F ^ n = 0 := by rw [← swO_pow hF, hn, swO_zero]
    rw [coe_oexp hn, coe_oexp hn', swO_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [swO_smul, swO_pow hF]
  · have h' : ¬ IsNilpotent (swO F) := fun h'' =>
      h (isNilpotent_of_bulk (by rw [← bulk_swO F]; exact h''.map bulk))
    rw [oexp, oexp, nilExp_of_not h, nilExp_of_not h', swO_zero]

theorem swO_expU (x : ℂ) {F : OE .two Λ} (hF : F ∈ ABΛ) : swO (expU x F) = expU x (swO F) := by
  rw [expU, expU, swO_smul, swO_oexp hF]

theorem expU_mem_abΛ (x : ℂ) {F : OE .two Λ} (hF : F ∈ ABΛ) : expU x F ∈ ABΛ :=
  Subalgebra.smul_mem _ (oexp_mem_abΛ hF) _

end Alg

/-- The swap of a family. -/
def swF {Λ ι : Type*} [DecidableEq Λ] (F : ι → OE .two Λ) : ι → OE .two Λ := fun x => swO (F x)

@[simp] theorem swF_apply {Λ ι : Type*} [DecidableEq Λ] (F : ι → OE .two Λ) (x : ι) :
    swF F x = swO (F x) := rfl

/-! ### The maps on inputs without one-point parts -/

section MapSw

variable {L N : ℕ} [NeZero L]


theorem sw_bpowO (j : ℕ) (I : OFam .two 2 L N) (X : Finset (Lam 2 L N))
    (hI : ∀ b ∈ blocks j X, I b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) : swO (bpowO j I X) = bpowO j (swF I) X := by
  rw [bpowO, swO_prod _ _ hI]; rfl

theorem sw_KextO (j : ℕ) (K : OAct .two 2 L N) (X : Finset (Lam 2 L N))
    (hK : ∀ Y ∈ Comp j X, K Y ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) : swO (KextO j K X) = KextO j (swF K) X := by
  rw [KextO, swO_prod _ _ hK]; rfl

section Gen

variable (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (Ib Ip : OFam .two 2 L N)
  (K : OAct .two 2 L N) (J : (Fin 2 → ℕ) → Finset (Lam 2 L N) → OE .two (Lam 2 L N))
  {U : Finset (Lam 2 L N)} (h : OGMem j C Ib Ip K J U (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) (abSub : Subalgebra ℂ (OE .two (Lam 2 L N ⊕ Lam 2 L N))))
include h

theorem sw_gdIO (b : Fin 2 → ℕ) : swO (gdIO Ib Ip b) = gdIO (swF Ib) (swF Ip) b := by
  rw [gdIO, gdIO, swO_sub, swO_thetaO, swO_inclO]; rfl

theorem sw_gdIPowO (hU : IsPolymer j U) {X : Finset (Lam 2 L N)} (hX : X ⊆ U) :
    swO (gdIPowO j Ib Ip X) = gdIPowO j (swF Ib) (swF Ip) X := by
  rw [gdIPowO, swO_prod]
  · exact prod_congr rfl fun b _ => sw_gdIO j C Ib Ip K J h b
  · intro b hb
    exact sub_mem (h.hθ _ (h.hIb b (mem_blockIdx_of_mem_blocks hb)
      (blockSet_subset hU (blocks_mono hX hb))))
      (h.hι _ (h.hIp b (mem_blockIdx_of_mem_blocks hb) (blockSet_subset hU (blocks_mono hX hb))))

theorem sw_gKtilO (hU : IsPolymer j U) {W : Finset (Lam 2 L N)} (hW : IsPolymer j W)
    (hWU : W ⊆ U) : swO (gKtilO j Ib Ip K W) = gKtilO j (swF Ib) (swF Ip) (swF K) W := by
  rw [gKtilO, gKtilO, swO_sum]
  refine sum_congr rfl fun Y hY => ?_
  have hP := IsPolymer.sdiff hW (mem_Pj.1 hY).2
  have hS : W \ Y ⊆ U := sdiff_subset.trans hWU
  rw [swO_mul (h.hθ _ (h.KextO_mem hP hS)), swO_thetaO,
    sw_KextO j K _ fun Z hZ => h.hK Z (isConn_of_mem_comp hP hZ) ((subset_of_mem_comp hZ).trans hS),
    sw_gdIPowO j C Ib Ip K J h hU ((mem_Pj.1 hY).1.trans hWU)]

theorem sw_gKchkCO (hU : IsPolymer j U) {W : Finset (Lam 2 L N)} (hW : IsPolymer j W)
    (hWU : W ⊆ U) :
    swO (gKchkCO j Ib Ip K J W) =
      gKchkCO j (swF Ib) (swF Ip) (swF K) (fun b X => swO (J b X)) W := by
  rw [gKchkCO, gKchkCO, swO_sub, sw_gKtilO j C Ib Ip K J h hU hW hWU, swO_sum]
  simp only [swO_thetaO]

theorem sw_gKchkO (hU : IsPolymer j U) {X : Finset (Lam 2 L N)} (hX : IsPolymer j X)
    (hXU : X ⊆ U) :
    swO (gKchkO j Ib Ip K J X) =
      gKchkO j (swF Ib) (swF Ip) (swF K) (fun b X => swO (J b X)) X := by
  rw [gKchkO, gKchkO, swO_prod]
  · exact prod_congr rfl fun W hW => sw_gKchkCO j C Ib Ip K J h hU
      (isPolymer_of_mem_comp hX hW) ((subset_of_mem_comp hW).trans hXU)
  · intro W hW
    exact sub_mem (h.gKtilO_mem hU (isPolymer_of_mem_comp hX hW)
      ((subset_of_mem_comp hW).trans hXU)) (Subalgebra.sum_mem _ fun b hb =>
        h.hθ _ (h.hJ b W (mem_blockIdx_of_mem_blocks hb) (blockSet_subset hU (blocks_mono
          ((subset_of_mem_comp hW).trans hXU) hb))))

theorem sw_gKnextO (hU : IsPolymer (j + 1) U) :
    swO (gKnextO j C Ib Ip K J U) =
      gKnextO j C (swF Ib) (swF Ip) (swF K) (fun b X => swO (J b X)) U := by
  rw [gKnextO, gKnextO, swO_sum]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨h1, h2, -, h4⟩ := Gset_facts hg
  have hUj := IsPolymer.of_succ hU
  have hJp : ∀ p ∈ g.1, thetaO (J p.1 p.2) ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N ⊕ Lam 2 L N))) := fun p hp =>
    h.hθ _ (h.hJ p.1 p.2 (mem_pairsU.1 (h4 p hp).1).1 (h4 p hp).2.2.1)
  rw [swO_mul (h.bpowO_mem hUj sdiff_subset), swO_ECCO, swO_mul (h.gKchkO_mem hUj h1 h2),
    swO_prod _ _ hJp, sw_gKchkO j C Ib Ip K J h hUj h1 h2]
  congr 1
  · rw [bpowO, bpowO, swO_prod]
    · rfl
    · intro b hb
      exact h.hIp b (mem_blockIdx_of_mem_blocks hb)
        (blockSet_subset hUj (blocks_mono sdiff_subset hb))
  · simp only [swO_thetaO]

end Gen

section Ref

variable (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam .two 2 L N)
  (K : OAct .two 2 L N)

theorem sw_VprO (b : Fin 2 → ℕ) : swO (VprO C V b) = VprO C (swF V) b := swO_EthO C (V b)

theorem sw_VprLO : swO (VprLO j C V) = VprLO j C (swF V) := by
  rw [VprLO, VprLO, swO_sum]
  exact sum_congr rfl fun b _ => sw_VprO C V b

variable {V W}

theorem VprO_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) : VprO C V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) := EthO_mem_ab C (hV b)

theorem VprLO_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) : VprLO j C V ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  Subalgebra.sum_mem _ fun b _ => VprO_mem C hV b

theorem sw_SCorO (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) :
    swO (SCorO j C V b) = SCorO j C (swF V) b := by
  rw [SCorO, SCorO, swO_smul, swO_sub,
    swO_FCO C (πobs_mem_ab (VprO_mem C hV b)) (VprLO_mem j C hV),
    swO_FCO C (VprO_mem C hV b) (πobs_mem_ab (VprLO_mem j C hV)), swO_πobs, swO_πobs,
    sw_VprO, sw_VprLO]

theorem sw_SFO (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) :
    swO (SFO j C V b) = SFO j C (swF V) b := by
  rw [SFO, SFO, swO_add, swO_smul, swO_FCO C (VprO_mem C hV b) (VprLO_mem j C hV), sw_VprO,
    sw_VprLO, sw_SCorO j C hV]

theorem sw_SbO (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) :
    swO (SbO j C V W b) = SbO j C (swF V) (swF W) b := by
  rw [SbO, SbO, swO_add, sw_SFO j C hV, swO_EthO]; rfl

theorem sw_SXO (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (X : Finset (Lam 2 L N)) :
    swO (SXO j C V W X) = SXO j C (swF V) (swF W) X := by
  rw [SXO, SXO, swO_sum]
  exact sum_congr rfl fun b _ => sw_SbO j C hV b

variable (V)

theorem sw_upBN (b : Fin 2 → ℕ) : upBN C (swF V) b = upBN C V b := by
  unfold upBN; rw [← sw_VprO, bulk_swO]

theorem sw_upON (b : Fin 2 → ℕ) : swO (upON C V b) = upON C (swF V) b := by
  unfold upON; rw [swO_πobs, swO_epsO, sw_VprO]

theorem sw_YpN (b : Fin 2 → ℕ) : swO (YpN C V b) = YpN C (swF V) b := by
  unfold YpN; rw [swO_sub, swO_sub, swO_algebraMap, sw_VprO, sw_upON, sw_upBN]

variable {V}

theorem upON_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) : upON C V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  πobs_mem_ab (epsO_mem_ab (VprO_mem C hV b))

theorem YpN_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) : YpN C V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  sub_mem (sub_mem (VprO_mem C hV b) (Subalgebra.algebraMap_mem _ _)) (upON_mem C hV b)

theorem SbO_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (hW : ∀ b, W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) : SbO j C V W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  OAbS.Sb_ab (K := (0 : OAct .two 2 L N)) ⟨hV, hW, fun _ _ => zero_mem _⟩ b

theorem GpN_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (hW : ∀ b, W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) : GpN j C V W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  mul_mem (oexp_mem_abΛ (neg_mem (YpN_mem C hV b))) (add_mem (one_mem _) (SbO_mem j C hV hW b))

theorem sw_GpN (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) :
    swO (GpN j C V W b) = GpN j C (swF V) (swF W) b := by
  unfold GpN
  rw [swO_mul (oexp_mem_abΛ (neg_mem (YpN_mem C hV b))), swO_oexp (neg_mem (YpN_mem C hV b)),
    swO_neg, sw_YpN, swO_add, swO_one, sw_SbO j C hV]

theorem IbO_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (hW : ∀ b, W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) : IbO V W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  mul_mem (oexp_mem_abΛ (neg_mem (hV b))) (add_mem (one_mem _) (hW b))

theorem sw_IbO (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (b : Fin 2 → ℕ) :
    swO (IbO V W b) = IbO (swF V) (swF W) b := by
  unfold IbO
  rw [swO_mul (oexp_mem_abΛ (neg_mem (hV b))), swO_oexp (neg_mem (hV b)), swO_neg, swO_add,
    swO_one]; rfl

theorem sw_uXBN (X : Finset (Lam 2 L N)) : uXBN j C (swF V) X = uXBN j C V X := by
  unfold uXBN; exact sum_congr rfl fun b _ => sw_upBN C V b

theorem sw_uXON (X : Finset (Lam 2 L N)) : swO (uXON j C V X) = uXON j C (swF V) X := by
  unfold uXON; rw [swO_sum]; exact sum_congr rfl fun b _ => sw_upON C V b

theorem uXON_mem (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (X : Finset (Lam 2 L N)) : uXON j C V X ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
  Subalgebra.sum_mem _ fun b _ => upON_mem C hV b

set_option maxHeartbeats 1000000 in
/-- **The reference activity commutes with the swap** (inputs in `abSub`, `U` a polymer). -/
theorem sw_KNO (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (hW : ∀ b, W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) (hK : ∀ Y, IsConn j Y → K Y ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    {U : Finset (Lam 2 L N)} (hU : IsPolymer (j + 1) U) :
    swO (KNO j C V W K U) = KNO j C (swF V) (swF W) (swF K) U := by
  have hEm : ∀ b, expU (-upBN C V b) (-upON C V b) * GpN j C V W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) := fun b =>
    mul_mem (expU_mem_abΛ _ (neg_mem (upON_mem C hV b))) (GpN_mem j C hV hW b)
  have hG : OGMem j C (IbO V W) (fun b => expU (-upBN C V b) (-upON C V b) * GpN j C V W b) K
      (fun _ _ => 0) U (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) (abSub : Subalgebra ℂ (OE .two (Lam 2 L N ⊕ Lam 2 L N))) :=
    { hθ := fun _ hF => thetaO_mem_ab hF
      hι := fun _ hF => inclO_mem_ab hF
      hE := fun _ hF => ECCO_mem_ab C hF
      hK := fun Y hY _ => hK Y hY
      hJ := fun _ _ _ _ => zero_mem _
      hIb := fun b _ _ => IbO_mem hV hW b
      hIp := fun b _ _ => hEm b }
  rw [KNO_eq, KNO_eq, swO_mul (expU_mem_abΛ _ (uXON_mem j C hV U)), swO_expU _ (uXON_mem j C hV U),
    sw_uXON, sw_uXBN, sw_gKnextO j C _ _ K _ hG hU]
  congr 1
  have e1 : swF (IbO V W) = IbO (swF V) (swF W) := funext fun b => sw_IbO hV b
  have e2 : swF (fun b => expU (-upBN C V b) (-upON C V b) * GpN j C V W b) =
      fun b => expU (-upBN C (swF V) b) (-upON C (swF V) b) * GpN j C (swF V) (swF W) b := by
    funext b
    rw [swF_apply, swO_mul (expU_mem_abΛ _ (neg_mem (upON_mem C hV b))),
      swO_expU _ (neg_mem (upON_mem C hV b)), swO_neg, sw_upON, sw_upBN, sw_GpN j C hV b]
  have e3 : (fun (_ : Fin 2 → ℕ) (_ : Finset (Lam 2 L N)) => swO (0 : OE .two (Lam 2 L N))) =
      fun _ _ => 0 := by funext _ _; exact swO_zero
  rw [e1, e2, e3]

end Ref

section Last

variable (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
  (V W : OFam .two 2 L N) (K : OAct .two 2 L N)

/-- At the last scale every `(j+1)`-block contains the points: no far part. -/
theorem farAB_last (hj : j + 1 = N) : farAB P j C V W = 0 := by
  unfold farAB
  refine sum_eq_zero fun c' hc' => if_pos ?_
  obtain ⟨x, hx⟩ := mem_blockIdx.1 hc'
  refine ⟨P.a, mem_inter.2 ⟨?_, ?_⟩⟩
  · rw [mem_blockSet] at hx ⊢
    rw [← hx, hj, LastN.blk_top, LastN.blk_top]
  · simp [ObsPts.pts]

variable {V W K}

theorem bulk_uVpO_sw (hj : j + 1 = N) (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (b : Fin 2 → ℕ) :
    bulk (uVpO P j C (swF V) (swF W) (swF K) b) = bulk (uVpO P j C V W K b) := by
  have hL : bulk (LSO P j C (swF V) (swF W) b) = bulk (LSO P j C V W b) := by
    unfold LSO
    rw [bulk_LocO2, bulk_LocO2, ← sw_SXO j C hV, bulk_swO]
  unfold uVpO
  rw [Q2O_last P hj, Q2O_last P hj, map_sub, map_sub, map_sub, map_sub, ← sw_VprO, bulk_swO, hL]

theorem sw_uXB_last (hj : j + 1 = N) (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (X : Finset (Lam 2 L N)) :
    uXB P j C (swF V) (swF W) (swF K) X = uXB P j C V W K X := by
  unfold uXB upB
  exact sum_congr rfl fun b _ => by rw [bulk_uVpO_sw P j C hj hV b]

set_option maxHeartbeats 1000000 in
theorem sw_uXO_last (hj : j + 1 = N) (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) :
    swO (uXO P j C V W K univ) = uXO P j C (swF V) (swF W) (swF K) univ := by
  have hQ : ∀ (K' : OAct .two 2 L N) b, EthO C (Q2O P j K' b) = 0 := fun K' b => by
    rw [Q2O_last P hj]; exact (EthOL C).map_zero
  -- the components of `uXO`
  have hcomp : ∀ (V' W' : OFam .two 2 L N) (K' : OAct .two 2 L N),
      (uXO P j C V' W' K' univ : SA .two (Lam 2 L N)) =
        ⟨0, algebraMap ℂ (Alg 2 L N)
            (∑ b ∈ blocks j (univ : Finset (Lam 2 L N)), ε (uVpO P j C V' W' K' b : SA .two (Lam 2 L N)).a),
          algebraMap ℂ (Alg 2 L N)
            (∑ b ∈ blocks j (univ : Finset (Lam 2 L N)), ε (uVpO P j C V' W' K' b : SA .two (Lam 2 L N)).b),
          algebraMap ℂ (Alg 2 L N)
            (∑ b ∈ blocks j (univ : Finset (Lam 2 L N)), ε (uVpO P j C V' W' K' b : SA .two (Lam 2 L N)).ab)⟩ := by
    intro V' W' K'
    unfold uXO upO
    rw [AddSubmonoidClass.coe_finsetSum]
    refine SA.ext ?_ ?_ ?_ ?_
    · simp only [SA.sum_e, coe_πobs, piobs_apply, sum_const_zero]
    · simp only [SA.sum_a, coe_πobs, piobs_apply, coe_epsO, epsS_a, map_sum]
    · simp only [SA.sum_b, coe_πobs, piobs_apply, coe_epsO, epsS_b, map_sum]
    · simp only [SA.sum_ab, coe_πobs, piobs_apply, coe_epsO, epsS_ab, map_sum]
  -- `uVpO` componentwise at the last scale
  have hU : ∀ (V' W' : OFam .two 2 L N) (K' : OAct .two 2 L N) b,
      (uVpO P j C V' W' K' b : SA .two (Lam 2 L N)) =
        (VprO C V' b : SA .two (Lam 2 L N)) - (LSO P j C V' W' b : SA .two (Lam 2 L N)) := by
    intro V' W' K' b
    unfold uVpO; rw [hQ, sub_zero, Subalgebra.coe_sub]
  have hSXb : ∀ X, (SXO j C (swF V) (swF W) X : SA .two (Lam 2 L N)).b = 0 := fun X => by
    rw [← sw_SXO j C hV]; rfl
  have hSXab : ∀ X, (SXO j C (swF V) (swF W) X : SA .two (Lam 2 L N)).ab = 0 := fun X => by
    rw [← sw_SXO j C hV]; rfl
  have hLb : ∀ b, (LSO P j C (swF V) (swF W) b : SA .two (Lam 2 L N)).b = 0 := fun b => by
    show locBp Obs.Case.two P.b _ _ (SXO j C (swF V) (swF W) _ : SA .two (Lam 2 L N)).b = 0
    rw [hSXb]; exact locBp_zero P.b _ _
  have hLab : ∀ b, (LSO P j C (swF V) (swF W) b : SA .two (Lam 2 L N)).ab = 0 := fun b => by
    show locABtXY P _ _ (SXO j C (swF V) (swF W) _ : SA .two (Lam 2 L N)).ab = 0
    rw [hSXab]; exact locABtXY_zero P _ _
  -- the totals
  have hLa : ∑ b ∈ blocks j (univ : Finset (Lam 2 L N)), ε (LSO P j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a =
      ∑ b ∈ blocks j (univ : Finset (Lam 2 L N)), ε (LSO P j C V W b : SA .two (Lam 2 L N)).ab := by
    have h1 := eps_total_LS P j C (swF V) (swF W)
    have h2 := eps_total_LS_ab P j C V W
    rw [farAB_last P j C V W hj, sub_zero] at h2
    have e : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a =
        ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam 2 L N)).ab :=
      sum_congr rfl fun b _ => by rw [← sw_SbO j C hV]; rfl
    exact h1.trans (e.trans h2.symm)
  refine Subtype.ext ?_
  rw [hcomp]
  refine SA.ext ?_ ?_ ?_ ?_
  · show ((uXO P j C V W K univ : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e = 0
    rw [hcomp]
  · show ((uXO P j C V W K univ : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = _
    rw [hcomp]
    show algebraMap ℂ (Alg 2 L N) (∑ b ∈ blocks j (univ : Finset (Lam 2 L N)), ε (uVpO P j C V W K b : SA .two (Lam 2 L N)).ab) =
      algebraMap ℂ (Alg 2 L N) (∑ b ∈ blocks j (univ : Finset (Lam 2 L N)),
        ε (uVpO P j C (swF V) (swF W) (swF K) b : SA .two (Lam 2 L N)).a)
    congr 1
    simp only [hU, SA.sub_ab, SA.sub_a, map_sub, sum_sub_distrib, hLa]
    congr 1
  · show (0 : Alg 2 L N) = algebraMap ℂ (Alg 2 L N) (∑ b ∈ blocks j (univ : Finset (Lam 2 L N)),
      ε (uVpO P j C (swF V) (swF W) (swF K) b : SA .two (Lam 2 L N)).b)
    simp only [hU, SA.sub_b, hLb, sub_zero]
    rw [sum_eq_zero fun b _ => by rw [← sw_VprO]; exact map_zero ε, map_zero]
  · show (0 : Alg 2 L N) = algebraMap ℂ (Alg 2 L N) (∑ b ∈ blocks j (univ : Finset (Lam 2 L N)),
      ε (uVpO P j C (swF V) (swF W) (swF K) b : SA .two (Lam 2 L N)).ab)
    simp only [hU, SA.sub_ab, hLab, sub_zero]
    rw [sum_eq_zero fun b _ => by rw [← sw_VprO]; exact map_zero ε, map_zero]

set_option maxHeartbeats 2000000 in
/-- **The final object of the last step commutes with the swap** (inputs in `abSub`, `j + 1 = N`):
`swO F_N = F_N[swO V, swO 𝒲, swO K]`. -/
theorem sw_finG (hj : j + 1 = N) (hV : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (hW : ∀ b, W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (hK : ∀ Y, IsConn j Y → K Y ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) :
    swO (finG P j C V W K) = finG P j C (swF V) (swF W) (swF K) := by
  have H : OAbS j V W K := ⟨hV, hW, hK⟩
  have hO := H.uXO_ab (P := P) (C := C) (univ : Finset (Lam 2 L N))
  have hN := uXON_mem j C hV (univ : Finset (Lam 2 L N))
  rw [finG_eq P j C V W K hj, finG_eq P j C (swF V) (swF W) (swF K) hj]
  have hE1 := expU_mem_abΛ (uXB P j C V W K univ) hO
  have hE2 := expU_mem_abΛ (-uXBN j C V univ) (neg_mem hN)
  rw [swO_mul (mul_mem hE1 hE2), swO_mul hE1, swO_expU _ hO, swO_expU _ (neg_mem hN), swO_neg,
    sw_uXO_last P j C hj hV, sw_uXON, sw_uXB_last P j C hj hV, sw_uXBN, swO_add,
    sw_bpowO j _ univ fun b _ => GpN_mem j C hV hW b, sw_KNO j C K hV hW hK (isPolymer_univ _)]
  congr 3
  funext b
  exact sw_GpN j C hV b

end Last

end MapSw

end

end PtCorr2
