import Step2.Map.Reapp

/-!
# Locality and `U(1)` invariance of the second-order map (Expected result `thm:closure`(a),(b))

* Complex covariances: `𝔼_C` maps `𝒩(X ⊔ X)` to `𝒩(X)` (`ECC_mem_NX`) and commutes with the
  `U(1)` scaling (`ECC_scal`), hence preserves `U(1)` invariance (`ECC_mem_SymS`); the same
  holds for `F_C` (`FC_mem_SymS`).
* The membership principle for the general map (`GMem.gKnext_mem`): if all building blocks of
  `K_{j+1}(U)` lie in subalgebras `S`, `S₂` stable under `θ`, the inclusion and `𝔼_C`, then so
  does `K_{j+1}(U)`.
* For the second-order map: `Knext2_loc` (`K_{j+1}(U) ∈ 𝒩(U^□)` at scale `j + 1`),
  `Knext2_sym`, and the same for `K^♯_{j+1}` (`Knew_loc`, `Knew_sym`).
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step

section Complex

variable {d L N : ℕ} [NeZero L]

theorem ECC_comm_of {C : Matrix (Lam d L N) (Lam d L N) ℂ} (g : Alg2 d L N →ₐ[ℂ] Alg2 d L N)
    (g' : Alg d L N →ₐ[ℂ] Alg d L N)
    (hL : ∀ G, LζC C (g G) = g (LζC C G)) (hp : ∀ G, proj (g G) = g' (proj G)) (F : Alg2 d L N) :
    ECC C (g F) = g' (ECC C F) := by
  have hc : LζC C ∘ₗ g.toLinearMap = g.toLinearMap ∘ₗ LζC C := LinearMap.ext fun G => hL G
  have h := Module.End.commute_exp_left_of_commute (LζC_isNilpotent C) (LζC_isNilpotent C) hc
  have h2 := LinearMap.congr_fun h F
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h2
  rw [ECC, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h2,
    AlgHom.toLinearMap_apply, hp]

theorem D_scal {Λ : Type*} [DecidableEq Λ] {t : ℂ} (a : Sf Λ) (H : Grassmann.N Λ) :
    D a (scal _ t H) = (if a.2 = 1 then t else t⁻¹) • scal _ t (D a H) := by
  rw [scal, D_map, ← map_smul]
  have : coord a ∘ₗ scalV _ t = (if a.2 = 1 then t else t⁻¹) • coord a := by
    refine LinearMap.ext fun v => ?_
    by_cases h : a.2 = 1 <;> simp [scalV, h]
  rw [this, map_smul, LinearMap.smul_apply]; rfl

theorem ECC_scal (C : Matrix (Lam d L N) (Lam d L N) ℂ) {t : ℂ} (ht : t ≠ 0) (F : Alg2 d L N) :
    ECC C (scal _ t F) = scal _ t (ECC C F) := by
  refine ECC_comm_of _ _ (fun G => ?_) (fun G => ?_) F
  · simp only [LζC_apply, D_scal, map_sum, map_smul, smul_smul]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    simp [units_ne.symm, ht]
  · simp only [proj, scal, map_map_apply]
    exact map_congr_apply (fun v b => rfl) G

theorem ECC_mem_SymS {C : Matrix (Lam d L N) (Lam d L N) ℂ} {F : Alg2 d L N}
    (hF : F ∈ SymS (Lam d L N ⊕ Lam d L N)) : ECC C F ∈ SymS (Lam d L N) :=
  mem_SymS.2 (by rw [← ECC_scal C two_ne_zero, mem_SymS.1 hF])

theorem LopC_scal {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ) {t : ℂ}
    (ht : t ≠ 0) (G : Grassmann.N Λ) : LopC C (scal _ t G) = scal _ t (LopC C G) := by
  simp only [LopC_apply, D_scal, map_sum, map_smul, smul_smul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp [units_ne.symm, ht]

theorem expLC_scal {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ) {t : ℂ}
    (ht : t ≠ 0) (G : Grassmann.N Λ) : expLC C (scal _ t G) = scal _ t (expLC C G) := by
  have hc : LopC C ∘ₗ (scal Λ t).toLinearMap = (scal Λ t).toLinearMap ∘ₗ LopC C :=
    LinearMap.ext fun G => LopC_scal C ht G
  have h := Module.End.commute_exp_left_of_commute (LopC_isNilpotent C) (LopC_isNilpotent C) hc
  exact LinearMap.congr_fun h G

theorem expLC_mem_SymS {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    {G : Grassmann.N Λ} (hG : G ∈ SymS Λ) : expLC C G ∈ SymS Λ :=
  mem_SymS.2 (by rw [← expLC_scal C two_ne_zero, mem_SymS.1 hG])

theorem FC_mem_SymS {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    {A B : Grassmann.N Λ} (hA : A ∈ SymS Λ) (hB : B ∈ SymS Λ) : FC C A B ∈ SymS Λ :=
  sub_mem (expLC_mem_SymS _ (mul_mem (expLC_mem_SymS _ hA) (expLC_mem_SymS _ hB)))
    (mul_mem hA hB)

theorem ECC_mem_NX (C : Matrix (Lam d L N) (Lam d L N) ℂ) {X : Set (Lam d L N)}
    {F : Alg2 d L N} (hF : F ∈ NX2 X) : ECC C F ∈ NX X := by
  have hL : ∀ G ∈ NX2 X, LζC C G ∈ NX2 X := fun G hG => by
    rw [LζC_apply]
    exact Subalgebra.sum_mem _ fun x _ => Subalgebra.sum_mem _ fun y _ =>
      Subalgebra.smul_mem _ (D_mem_NX (D_mem_NX hG _) _) _
  have hLk : ∀ k, ∀ G ∈ NX2 X, (LζC C ^ k) G ∈ NX2 X := by
    intro k
    induction k with
    | zero => exact fun G hG => hG
    | succ k ih => intro G hG; rw [pow_succ', Module.End.mul_apply]; exact hL _ (ih G hG)
  obtain ⟨n, hn⟩ := LζC_isNilpotent C
  have hexp : IsNilpotent.exp (LζC C) F ∈ NX2 X := by
    rw [IsNilpotent.exp_eq_sum hn, LinearMap.sum_apply]
    refine Subalgebra.sum_mem _ fun k _ => ?_
    rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ]
    exact Subalgebra.smul_mem _ (hLk k F hF) _
  rw [ECC, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  refine algHom_mem_of_mem_NX _ (fun a ha => ?_) hexp
  rcases a with ⟨b | b, σ⟩
  · have hb : b ∈ X := by simpa using ha
    exact (proj_ψ₁ (b, σ)).symm ▸ ψ_mem_NX hb
  · exact (proj_ζ (b, σ)).symm ▸ zero_mem _

theorem isSym_Loc2XY (X Y : Finset (Lam d L N)) (F : Alg d L N) : IsSym (Loc2sXY X Y F) := by
  rw [isSym_iff_mem_SymS]
  exact add_mem ((isSym_iff_mem_SymS _).1 (isSym_LocXY X Y F))
    ((isSym_iff_mem_SymS _).1 (isSym_Loc4sXY X Y F))

end Complex

/-! ### The membership principle for the general map -/

section GMem

variable {d L N : ℕ} [NeZero L]

/-- The hypotheses of the membership principle for `gKnext`. -/
structure GMem (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)) (K : Act d L N)
    (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)) (U : Finset (Lam d L N))
    (S : Subalgebra ℂ (Alg d L N)) (S2 : Subalgebra ℂ (Alg2 d L N)) : Prop where
  hθ : ∀ F ∈ S, theta F ∈ S2
  hι : ∀ F ∈ S, incl F ∈ S2
  hE : ∀ F ∈ S2, ECC C F ∈ S
  hK : ∀ Y, IsConn j Y → Y ⊆ U → (K Y : Alg d L N) ∈ S
  hJ : ∀ (b : Fin d → ℕ) (X : Finset (Lam d L N)), b ∈ blockIdx (L := L) (N := N) j →
    blockSet j b ⊆ U → (J b X : Alg d L N) ∈ S
  hIb : ∀ b : Fin d → ℕ, b ∈ blockIdx (L := L) (N := N) j → blockSet j b ⊆ U →
    (Ib b : Alg d L N) ∈ S
  hIp : ∀ b : Fin d → ℕ, b ∈ blockIdx (L := L) (N := N) j → blockSet j b ⊆ U →
    (Ip b : Alg d L N) ∈ S

namespace GMem

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)}
  {K : Act d L N} {J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)}
  {U : Finset (Lam d L N)} {S : Subalgebra ℂ (Alg d L N)} {S2 : Subalgebra ℂ (Alg2 d L N)}
  (h : GMem j C Ib Ip K J U S S2)
include h

theorem thetaE' {x : EvR (Lam d L N)} (hx : x ∈ SE S) : thetaE x ∈ SE S2 := h.hθ _ hx

theorem inclE' {x : EvR (Lam d L N)} (hx : x ∈ SE S) : inclE x ∈ SE S2 := h.hι _ hx

theorem Kext_mem {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) :
    Kext j K W ∈ SE S :=
  prod_mem fun Y hY => h.hK Y (isConn_of_mem_comp hW hY) ((subset_of_mem_comp hY).trans hWU)

theorem bpow_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    bpow j Ip X ∈ SE S :=
  prod_mem fun b hb => h.hIp b (mem_blockIdx_of_mem_blocks hb)
    (blockSet_subset hU (blocks_mono hX hb))

theorem dIPow_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : X ⊆ U) :
    gdIPow j Ib Ip X ∈ SE S2 :=
  prod_mem fun b hb => sub_mem (h.thetaE' (h.hIb b (mem_blockIdx_of_mem_blocks hb)
    (blockSet_subset hU (blocks_mono hX hb))))
    (h.inclE' (h.hIp b (mem_blockIdx_of_mem_blocks hb) (blockSet_subset hU (blocks_mono hX hb))))

theorem Ktil_mem (hU : IsPolymer j U) {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    (hWU : W ⊆ U) : gKtil j Ib Ip K W ∈ SE S2 :=
  Subalgebra.sum_mem _ fun Y hY => mul_mem
    (h.thetaE' (h.Kext_mem (IsPolymer.sdiff hW (mem_Pj.1 hY).2) (sdiff_subset.trans hWU)))
    (h.dIPow_mem hU ((mem_Pj.1 hY).1.trans hWU))

theorem Kchk_mem (hU : IsPolymer j U) {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hXU : X ⊆ U) : gKchk j Ib Ip K J X ∈ SE S2 :=
  prod_mem fun W hW => sub_mem (h.Ktil_mem hU (isPolymer_of_mem_comp hX hW)
    ((subset_of_mem_comp hW).trans hXU)) (Subalgebra.sum_mem _ fun b hb =>
      h.thetaE' (h.hJ b W (mem_blockIdx_of_mem_blocks hb) (blockSet_subset hU (blocks_mono
        ((subset_of_mem_comp hW).trans hXU) hb))))

/-- **The membership principle**: `K_{j+1}(U) ∈ S`. -/
theorem gKnext_mem (hU : IsPolymer (j + 1) U) : gKnext j C Ib Ip K J U ∈ SE S := by
  refine Subalgebra.sum_mem _ fun g hg => ?_
  obtain ⟨h1, h2, -, h4⟩ := Gset_facts hg
  have hUj := IsPolymer.of_succ hU
  have hin : gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2) ∈ SE S2 :=
    mul_mem (h.Kchk_mem hUj h1 h2)
      (prod_mem fun p hp => h.thetaE' (h.hJ p.1 p.2 (mem_pairsU.1 (h4 p hp).1).1
        (h4 p hp).2.2.1))
  have hE : ECCE C (gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2)) ∈ SE S := by
    show ECC C _ ∈ S
    exact h.hE _ hin
  exact mul_mem (h.bpow_mem hUj sdiff_subset) hE

end GMem

end GMem

/-! ### Locality and symmetry of the building blocks of the second-order map -/

section Blocks

variable {d L N : ℕ} [NeZero L] {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : Fam d L N} {K : Act d L N}

/-- `𝒩(B^□)` at scale `j` for the `j`-block `B = B(b)`. -/
abbrev NB (j : ℕ) (b : Fin d → ℕ) : Subalgebra ℂ (Alg d L N) :=
  NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))

/-- `𝒩((B_+)^□)` at scale `j + 1`. -/
abbrev NBp (j : ℕ) (b : Fin d → ℕ) : Subalgebra ℂ (Alg d L N) :=
  NX (nbhd (j + 1) (Bp (L := L) (N := N) j b) : Set (Lam d L N))

theorem NB_le_NBp (j : ℕ) (b : Fin d → ℕ) : NB (L := L) (N := N) j b ≤ NBp j b :=
  NX_mono (coe_subset.2 ((nbhd_subset_nbhd_succ _).trans (nbhd_mono (subset_clo j _))))

theorem Loc2E_mem_NB (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) (F : EvR (Lam d L N)) :
    (Loc2E X (blockSet j b) F : Alg d L N) ∈ NB (L := L) (N := N) j b :=
  Loc2XY_mem' hd (isSmall_blockSet_of_mem hb).1 _ _

theorem Q2_mem_NB (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Q2 j K b : Alg d L N) ∈ NB (L := L) (N := N) j b := by
  unfold Q2; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun X _ => Loc2E_mem_NB hd hb _ _
  · exact zero_mem _

theorem J2_mem_NB (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) : (J2 j K b X : Alg d L N) ∈ NB (L := L) (N := N) j b := by
  unfold J2; split_ifs
  · rw [NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum]
    exact neg_mem (Subalgebra.sum_mem _ fun Y _ => Loc2E_mem_NB hd hb _ _)
  · exact Loc2E_mem_NB hd hb _ _
  · exact zero_mem _

theorem EthE_mem_NB {b : Fin d → ℕ} {F : EvR (Lam d L N)}
    (hF : (F : Alg d L N) ∈ NB (L := L) (N := N) j b) :
    (EthE C F : Alg d L N) ∈ NB (L := L) (N := N) j b := by
  rw [coe_EthE]; exact expLC_mem_NX _ hF

theorem Sb_mem' (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Sb j C V W b : Alg d L N) ∈ NBp (L := L) (N := N) j b := by
  rw [Sb, FCE_VprL_eq hjN hC hV b]
  have hsub : ∀ b', b' ∈ nearSet (L := L) (N := N) j b →
      (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) ⊆
        (nbhd (j + 1) (Bp (L := L) (N := N) j b) : Set (Lam d L N)) :=
    fun b' hb' _ hy => mem_nbhd_succ_of_near hd hL hjN.le hb' hy
  have hs := hsub b (mem_nearSet_self hb)
  refine add_mem (Subalgebra.smul_mem _ ?_ _) ?_
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    rw [coe_FCE]
    exact FC_mem_NX C (NX_mono hs (Vpr_mem hV b)) (NX_mono (hsub b' hb') (Vpr_mem hV b'))
  · rw [coe_EthE]; exact NX_mono hs (expLC_mem_NX _ (hW.loc b))

theorem SX_mem' (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) (b : Fin d → ℕ) :
    (SX j C V W (Bp (L := L) (N := N) j b) : Alg d L N) ∈ NBp (L := L) (N := N) j b := by
  rw [SX, AddSubmonoidClass.coe_finsetSum]
  refine Subalgebra.sum_mem _ fun b'' hb'' => ?_
  exact NX_mono (coe_subset.2 (nbhd_mono (BH.Bp_sub hb'')))
    (Sb_mem' hd hL hjN hC hV hW (mem_blockIdx_of_mem_blocks hb''))

theorem LS_mem_NB (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (LS j C V W b : Alg d L N) ∈ NB (L := L) (N := N) j b :=
  Loc2E_mem_NB hd hb _ _

theorem uVp_mem (hd : 1 ≤ d) (hV : InF j V) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (uVp j C V W K b : Alg d L N) ∈ NB (L := L) (N := N) j b := by
  rw [uVp, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub]
  exact sub_mem (sub_mem (Vpr_mem hV b) (EthE_mem_NB (Q2_mem_NB hd hb))) (LS_mem_NB hd hb)

theorem Vp_mem (hd : 1 ≤ d) (hV : InF j V) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Vp j C V W K b : Alg d L N) ∈ NB (L := L) (N := N) j b := by
  rw [Vp, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap]
  exact sub_mem (uVp_mem hd hV hb) (Subalgebra.algebraMap_mem _ _)

theorem Wp_mem (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Wp j C V W b : Alg d L N) ∈ NBp (L := L) (N := N) j b := by
  rw [Wp, AddSubgroupClass.coe_sub]
  exact sub_mem (Sb_mem' hd hL hjN hC hV hW hb) (NB_le_NBp j b (LS_mem_NB hd hb))

theorem Gp_mem (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Gp j C V W K b : Alg d L N) ∈ NBp (L := L) (N := N) j b := by
  have hε : ε ((-Vp j C V W K b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, ε_Vp, neg_zero]
  rw [Gp, MulMemClass.coe_mul, AddMemClass.coe_add, OneMemClass.coe_one]
  refine mul_mem (gexp_mem_NX hε ?_) (add_mem (one_mem _) (Wp_mem hd hL hjN hC hV hW hb))
  rw [NegMemClass.coe_neg]; exact neg_mem (NB_le_NBp j b (Vp_mem hd hV hb))

theorem Ip_mem (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Ip j C V W K b : Alg d L N) ∈ NBp (L := L) (N := N) j b := by
  have : Ip j C V W K b = Complex.exp (-up j C V W K b) • Gp j C V W K b := rfl
  rw [this, Subalgebra.coe_smul]
  exact Subalgebra.smul_mem _ (Gp_mem hd hL hjN hC hV hW hb) _

theorem Ib_mem (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hV : InF j V) (hW : InF j W)
    (b : Fin d → ℕ) : (Ib V W b : Alg d L N) ∈ NB (L := L) (N := N) j b := by
  have hε : ε ((-V b : EvR (Lam d L N)) : Alg d L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, hV0 b, neg_zero]
  rw [Ib, MulMemClass.coe_mul, AddMemClass.coe_add, OneMemClass.coe_one]
  refine mul_mem (gexp_mem_NX hε ?_) (add_mem (one_mem _) (hW.loc b))
  rw [NegMemClass.coe_neg]; exact neg_mem (hV.loc b)

/-! #### `U(1)` invariance -/

theorem Vpr_sym (hV : InF j V) (b : Fin d → ℕ) : (Vpr C V b : Alg d L N) ∈ SymS (Lam d L N) := by
  rw [Vpr, coe_EthE]; exact expLC_mem_SymS _ ((isSym_iff_mem_SymS _).1 (hV.sym b))

theorem EthE_sym {F : EvR (Lam d L N)} (hF : (F : Alg d L N) ∈ SymS (Lam d L N)) :
    (EthE C F : Alg d L N) ∈ SymS (Lam d L N) := by
  rw [coe_EthE]; exact expLC_mem_SymS _ hF

theorem Loc2E_sym (X Y : Finset (Lam d L N)) (F : EvR (Lam d L N)) :
    (Loc2E X Y F : Alg d L N) ∈ SymS (Lam d L N) :=
  (isSym_iff_mem_SymS _).1 (isSym_Loc2XY _ _ _)

theorem FCE_sym {A B : EvR (Lam d L N)} (hA : (A : Alg d L N) ∈ SymS (Lam d L N))
    (hB : (B : Alg d L N) ∈ SymS (Lam d L N)) :
    (FCE C A B : Alg d L N) ∈ SymS (Lam d L N) := by
  rw [coe_FCE]; exact FC_mem_SymS C hA hB

theorem VprL_sym (hV : InF j V) : (VprL j C V : Alg d L N) ∈ SymS (Lam d L N) := by
  rw [VprL, AddSubmonoidClass.coe_finsetSum]; exact Subalgebra.sum_mem _ fun b _ => Vpr_sym hV b

theorem Sb_sym (hV : InF j V) (hW : InF j W) (b : Fin d → ℕ) :
    (Sb j C V W b : Alg d L N) ∈ SymS (Lam d L N) := by
  rw [Sb, AddMemClass.coe_add, Subalgebra.coe_smul]
  exact add_mem (Subalgebra.smul_mem _ (FCE_sym (Vpr_sym hV b) (VprL_sym hV)) _)
    (EthE_sym ((isSym_iff_mem_SymS _).1 (hW.sym b)))

theorem Q2_sym (b : Fin d → ℕ) : (Q2 j K b : Alg d L N) ∈ SymS (Lam d L N) := by
  unfold Q2; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]; exact Subalgebra.sum_mem _ fun X _ => Loc2E_sym _ _ _
  · exact zero_mem _

theorem J2_sym (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    (J2 j K b X : Alg d L N) ∈ SymS (Lam d L N) := by
  unfold J2; split_ifs
  · rw [NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum]
    exact neg_mem (Subalgebra.sum_mem _ fun Y _ => Loc2E_sym _ _ _)
  · exact Loc2E_sym _ _ _
  · exact zero_mem _

theorem Vp_sym (hV : InF j V) (b : Fin d → ℕ) :
    (Vp j C V W K b : Alg d L N) ∈ SymS (Lam d L N) := by
  rw [Vp, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap, uVp, AddSubgroupClass.coe_sub,
    AddSubgroupClass.coe_sub]
  exact sub_mem (sub_mem (sub_mem (Vpr_sym hV b) (EthE_sym (Q2_sym b))) (Loc2E_sym _ _ _))
    (Subalgebra.algebraMap_mem _ _)

theorem Wp_sym (hV : InF j V) (hW : InF j W) (b : Fin d → ℕ) :
    (Wp j C V W b : Alg d L N) ∈ SymS (Lam d L N) := by
  rw [Wp, AddSubgroupClass.coe_sub]; exact sub_mem (Sb_sym hV hW b) (Loc2E_sym _ _ _)

theorem Gp_sym (hV : InF j V) (hW : InF j W) (b : Fin d → ℕ) :
    Gp j C V W K b ∈ SE (SymS (Lam d L N)) :=
  mul_mem (gexp_mem_SE (neg_mem (Vp_sym hV b))) (add_mem (one_mem _) (Wp_sym hV hW b))

theorem Ip_sym (hV : InF j V) (hW : InF j W) (b : Fin d → ℕ) :
    Ip j C V W K b ∈ SE (SymS (Lam d L N)) :=
  Subalgebra.smul_mem _ (Gp_sym hV hW b) _

theorem Ib_sym (hV : InF j V) (hW : InF j W) (b : Fin d → ℕ) :
    Ib V W b ∈ SE (SymS (Lam d L N)) :=
  mul_mem (gexp_mem_SE (neg_mem ((isSym_iff_mem_SymS _).1 (hV.sym b))))
    (add_mem (one_mem _) ((isSym_iff_mem_SymS _).1 (hW.sym b)))

theorem k2_sym (hV : InF j V) (X : Finset (Lam d L N)) :
    (k2 j C V X : Alg d L N) ∈ SymS (Lam d L N) := by
  unfold k2; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    rw [Subalgebra.coe_smul]
    refine Subalgebra.smul_mem _ (FCE_sym (Vpr_sym hV b) ?_) _
    rw [AddSubgroupClass.coe_sub]; exact sub_mem (VprL_sym hV) (Vpr_sym hV b)
  · rw [Subalgebra.coe_smul, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => ?_) _
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b' _ => FCE_sym (Vpr_sym hV b) (Vpr_sym hV b')
  · exact zero_mem _

theorem K2_sym (hV : InF j V) (U : Finset (Lam d L N)) :
    (K2 j C V U : Alg d L N) ∈ SymS (Lam d L N) := by
  unfold K2; rw [AddSubmonoidClass.coe_finsetSum]
  exact Subalgebra.sum_mem _ fun X _ => k2_sym hV X

end Blocks

/-! ### `K_{j+1}` is local and `U(1)`-invariant -/

section Main

variable {d L N : ℕ} [NeZero L] {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : Fam d L N} {K : Act d L N}

theorem nbhd_sub_of_block {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) {b : Fin d → ℕ}
    (hbU : blockSet (L := L) (N := N) j b ⊆ U) :
    (NBp (L := L) (N := N) j b) ≤ NX (nbhd (j + 1) U : Set (Lam d L N)) :=
  NX_mono (coe_subset.2 (nbhd_mono (clo_subset hU hbU)))

theorem gmem_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    GMem j C (Ib V W) (Ip j C V W K) K (J2 j K) U (NX (nbhd (j + 1) U : Set (Lam d L N)))
      (NX2 (nbhd (j + 1) U : Set (Lam d L N))) where
  hθ _ hF := theta_mem_NX2 hF
  hι _ hF := incl_mem_NX2 hF
  hE _ hF := ECC_mem_NX C hF
  hK Y hY hYU := NX_mono (coe_subset.2 ((nbhd_subset_nbhd_succ _).trans (nbhd_mono hYU)))
    (hK.loc Y hY)
  hJ b X hb hbU := nbhd_sub_of_block hU hbU (NB_le_NBp j b (J2_mem_NB hd hb X))
  hIb b _ hbU := nbhd_sub_of_block hU hbU (NB_le_NBp j b (Ib_mem hV0 hV hW b))
  hIp b hb hbU := nbhd_sub_of_block hU hbU (Ip_mem hd hL hjN hC hV hW hb)

theorem gmem_sym (hV : InF j V) (hW : InF j W) (hK : InK2 j K) (U : Finset (Lam d L N)) :
    GMem j C (Ib V W) (Ip j C V W K) K (J2 j K) U (SymS (Lam d L N))
      (SymS (Lam d L N ⊕ Lam d L N)) where
  hθ F hF := mem_SymS.2 (by rw [← theta_scal, mem_SymS.1 hF])
  hι F hF := mem_SymS.2 (by rw [← incl_scal, mem_SymS.1 hF])
  hE _ hF := ECC_mem_SymS hF
  hK Y hY _ := (isSym_iff_mem_SymS _).1 (hK.sym Y hY)
  hJ b X _ _ := J2_sym b X
  hIb b _ _ := Ib_sym hV hW b
  hIp b _ _ := Ip_sym hV hW b

/-- **Locality of `K^{pf}_{j+1}`**: `K^{pf}_{j+1}(U) ∈ 𝒩(U^□)` at scale `j + 1`. -/
theorem Knext2_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    (Knext2 j C V W K U : Alg d L N) ∈ NX (nbhd (j + 1) U : Set (Lam d L N)) :=
  Subalgebra.smul_mem _ ((gmem_loc hd hL hjN hC hV hW hV0 hK hU).gKnext_mem hU) _

/-- **`U(1)` invariance of `K^{pf}_{j+1}`.** -/
theorem Knext2_sym (hV : InF j V) (hW : InF j W) (hK : InK2 j K) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) : IsSym (Knext2 j C V W K U : Alg d L N) :=
  (isSym_iff_mem_SymS _).2
    (Subalgebra.smul_mem _ ((gmem_sym (C := C) hV hW hK U).gKnext_mem hU) _)

theorem k2_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) {U X : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) (hXU : clo j X = U) :
    (k2 j C V X : Alg d L N) ∈ NX (nbhd (j + 1) U : Set (Lam d L N)) := by
  have hbU : ∀ b ∈ blocks j X, blockSet (L := L) (N := N) j b ⊆ U := fun b hb =>
    (blockSet_subset (IsPolymer.of_succ (isPolymer_clo j X)) (blocks_mono (subset_clo j X) hb)).trans
      (hXU ▸ subset_rfl)
  have hsub : ∀ b ∈ blocks j X, ∀ b' ∈ nearSet (L := L) (N := N) j b,
      (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) ⊆
        (nbhd (j + 1) U : Set (Lam d L N)) := fun b hb b' hb' _ hy =>
    nbhd_mono (clo_subset hU (hbU b hb)) (mem_nbhd_succ_of_near hd hL hjN.le hb' hy)
  have hself : ∀ b ∈ blocks j X, (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) ⊆
      (nbhd (j + 1) U : Set (Lam d L N)) := fun b hb =>
    hsub b hb b (mem_nearSet_self (mem_blockIdx_of_mem_blocks hb))
  unfold k2; split_ifs with h1 h2
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b hb => ?_
    rw [Subalgebra.coe_smul, FCE_sub_right, AddSubgroupClass.coe_sub, FCE_VprL_eq hjN hC hV b,
      AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (sub_mem (Subalgebra.sum_mem _ fun b' hb' => ?_) ?_) _
    · rw [coe_FCE]
      exact FC_mem_NX C (NX_mono (hself b hb) (Vpr_mem hV b))
        (NX_mono (hsub b hb b' hb') (Vpr_mem hV b'))
    · rw [coe_FCE]
      exact FC_mem_NX C (NX_mono (hself b hb) (Vpr_mem hV b)) (NX_mono (hself b hb) (Vpr_mem hV b))
  · rw [Subalgebra.coe_smul, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb => ?_) _
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    rw [coe_FCE]
    exact FC_mem_NX C (NX_mono (hself b hb) (Vpr_mem hV b))
      (NX_mono (hself b' (mem_of_mem_erase hb')) (Vpr_mem hV b'))
  · exact zero_mem _

theorem K2_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    (K2 j C V U : Alg d L N) ∈ NX (nbhd (j + 1) U : Set (Lam d L N)) := by
  classical
  unfold K2; rw [AddSubmonoidClass.coe_finsetSum]
  exact Subalgebra.sum_mem _ fun X hX => k2_loc hd hL hjN hC hV hU (mem_filter.1 hX).2

/-- **Locality of `K_{j+1}`.** -/
theorem Knew_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ C)
    (hV : InF j V) (hW : InF j W) (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (hK : InK2 j K)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    (Knew j C V W K U : Alg d L N) ∈ NX (nbhd (j + 1) U : Set (Lam d L N)) := by
  rw [Knew, AddSubgroupClass.coe_sub, MulMemClass.coe_mul]
  refine sub_mem (Knext2_loc hd hL hjN hC hV hW hV0 hK hU) (mul_mem ?_ (K2_loc hd hL hjN hC hV hU))
  exact (prod_mem fun b hb => nbhd_sub_of_block hU
    (blockSet_subset (IsPolymer.of_succ hU) hb) (Gp_mem hd hL hjN hC hV hW (mem_blockIdx_of_mem_blocks hb)) :
    bpow j (Gp j C V W K) U ∈ SE (NX (nbhd (j + 1) U : Set (Lam d L N))))

/-- **`U(1)` invariance of `K_{j+1}`.** -/
theorem Knew_sym (hV : InF j V) (hW : InF j W) (hK : InK2 j K) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) : IsSym (Knew j C V W K U : Alg d L N) := by
  rw [isSym_iff_mem_SymS, Knew, AddSubgroupClass.coe_sub, MulMemClass.coe_mul]
  refine sub_mem ((isSym_iff_mem_SymS _).1 (Knext2_sym hV hW hK hU)) (mul_mem ?_ (K2_sym hV U))
  exact (prod_mem fun b _ => Gp_sym hV hW b : bpow j (Gp j C V W K) U ∈ SE (SymS (Lam d L N)))

end Main


end

end Step2
