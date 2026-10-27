import Step2.Coup.JSym

/-!
# `J`-invariance of the step (`h02uv-outline.tex`, Proposition `prop:C2`)

If `C` is symmetric and `V`, `𝒲`, `K` are invariant under the symplectic involution `J`, so are
`V_{j+1}`, `𝒲_{j+1}` and `K_{j+1}` (`Vnext2_J`, `Wnext2_J`, `Kplus_J`). The proof is the
membership principle (`GMem.gKnext_mem`, `Kout_mem`) with the `J`-equaliser `JS`, as for the
`U(1)` invariance in `Step2.Map.Mem`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- The `J`-invariant elements. -/
abbrev JS (d L N : ℕ) [NeZero L] : Subalgebra ℂ (Alg d L N) :=
  AlgHom.equalizer Jsym (AlgHom.id ℂ (Alg d L N))

/-- The `J`-invariant elements of the doubled algebra. -/
abbrev JS2 (d L N : ℕ) [NeZero L] : Subalgebra ℂ (Alg2 d L N) :=
  AlgHom.equalizer Jsym2 (AlgHom.id ℂ (Alg2 d L N))

theorem mem_JS {F : Alg d L N} : F ∈ JS d L N ↔ Jsym F = F := by
  rw [AlgHom.mem_equalizer, AlgHom.id_apply]

theorem mem_JS2 {F : Alg2 d L N} : F ∈ JS2 d L N ↔ Jsym2 F = F := by
  rw [AlgHom.mem_equalizer, AlgHom.id_apply]

/-- `J`-invariance of a block family. -/
def FamJ (F : Fam d L N) : Prop := ∀ b, (F b : Alg d L N) ∈ JS d L N

/-- `J`-invariance of a polymer activity on connected polymers. -/
def KJ (j : ℕ) (K : Act d L N) : Prop := ∀ X, IsConn j X → (K X : Alg d L N) ∈ JS d L N

section Blocks

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N} {K : Act d L N}
  (hCs : ∀ x y, C x y = C y x)

include hCs in
theorem EthE_J {F : EvR (Lam d L N)} (hF : (F : Alg d L N) ∈ JS d L N) :
    (EthE C F : Alg d L N) ∈ JS d L N := by
  rw [mem_JS, coe_EthE, ← expLC_Jsym hCs, mem_JS.1 hF]

include hCs in
theorem FCE_J {A B : EvR (Lam d L N)} (hA : (A : Alg d L N) ∈ JS d L N)
    (hB : (B : Alg d L N) ∈ JS d L N) : (FCE C A B : Alg d L N) ∈ JS d L N := by
  rw [mem_JS, coe_FCE, FC_Jsym hCs, mem_JS.1 hA, mem_JS.1 hB]

theorem Loc2E_J {X Y : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    {F : EvR (Lam d L N)} (hF : (F : Alg d L N) ∈ JS d L N) :
    (Loc2E X Y F : Alg d L N) ∈ JS d L N := by
  rw [mem_JS, coe_Loc2E, ← Loc2sXY_Jsym hX hne, mem_JS.1 hF]

include hCs in
theorem Vpr_J (hVJ : FamJ V) (b : Fin d → ℕ) : (Vpr C V b : Alg d L N) ∈ JS d L N :=
  EthE_J hCs (hVJ b)

include hCs in
theorem VprL_J (hVJ : FamJ V) : (VprL j C V : Alg d L N) ∈ JS d L N := by
  rw [VprL, AddSubmonoidClass.coe_finsetSum]
  exact Subalgebra.sum_mem _ fun b _ => Vpr_J hCs hVJ b

include hCs in
theorem Sb_J (hVJ : FamJ V) (hWJ : FamJ W) (b : Fin d → ℕ) :
    (Sb j C V W b : Alg d L N) ∈ JS d L N := by
  rw [Sb, AddMemClass.coe_add, Subalgebra.coe_smul]
  exact add_mem (Subalgebra.smul_mem _ (FCE_J hCs (Vpr_J hCs hVJ b) (VprL_J hCs hVJ)) _)
    (EthE_J hCs (hWJ b))

include hCs in
theorem SX_J (hVJ : FamJ V) (hWJ : FamJ W) (X : Finset (Lam d L N)) :
    (SX j C V W X : Alg d L N) ∈ JS d L N := by
  rw [SX, AddSubmonoidClass.coe_finsetSum]
  exact Subalgebra.sum_mem _ fun b _ => Sb_J hCs hVJ hWJ b

theorem patch_Bp (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Patch (Bp (L := L) (N := N) j b) ∧ (Bp (L := L) (N := N) j b).Nonempty := by
  have hsm : IsSmall (j + 1) (Bp (L := L) (N := N) j b) := isSmall_clo (isSmall_blockSet_of_mem hb)
  exact ⟨patch_of_small hL hjN hsm, hsm.2.1.1⟩

include hCs in
theorem LS_J (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N) (hVJ : FamJ V) (hWJ : FamJ W)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (LS j C V W b : Alg d L N) ∈ JS d L N := by
  obtain ⟨hp, hne⟩ := patch_Bp hL hjN hb
  exact Loc2E_J hp hne (SX_J hCs hVJ hWJ _)

include hCs in
theorem Wp_J (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N) (hVJ : FamJ V) (hWJ : FamJ W)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Wp j C V W b : Alg d L N) ∈ JS d L N := by
  rw [Wp, AddSubgroupClass.coe_sub]
  exact sub_mem (Sb_J hCs hVJ hWJ b) (LS_J hCs hL hjN hVJ hWJ hb)

theorem Q2_J (hL : 2 ^ (d + 3) + 8 * d < L) (hKJ : KJ j K) (b : Fin d → ℕ) :
    (Q2 j K b : Alg d L N) ∈ JS d L N := by
  classical
  unfold Q2; split_ifs with hjN
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun X hX => ?_
    have hs := mem_smallSets.1 (mem_filter.1 hX).1
    exact Loc2E_J (patch_of_small hL (by omega) hs) hs.2.1.1 (hKJ X ⟨hs.1, hs.2.1⟩)
  · exact zero_mem _

theorem J2_J (hL : 2 ^ (d + 3) + 8 * d < L) (hKJ : KJ j K) (b : Fin d → ℕ)
    (X : Finset (Lam d L N)) : (J2 j K b X : Alg d L N) ∈ JS d L N := by
  classical
  unfold J2; split_ifs with h1 h2
  · rw [NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum]
    refine neg_mem (Subalgebra.sum_mem _ fun Y hY => ?_)
    have hs := mem_smallSets.1 (mem_filter.1 hY).1
    exact Loc2E_J (patch_of_small hL (by omega) hs) hs.2.1.1 (hKJ Y ⟨hs.1, hs.2.1⟩)
  · exact Loc2E_J (patch_of_small hL (by omega) h1.2.1) h1.2.1.2.1.1
      (hKJ X ⟨h1.2.1.1, h1.2.1.2.1⟩)
  · exact zero_mem _

include hCs in
theorem Vp_J (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N) (hVJ : FamJ V) (hWJ : FamJ W)
    (hKJ : KJ j K) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (Vp j C V W K b : Alg d L N) ∈ JS d L N := by
  rw [Vp, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap, uVp, AddSubgroupClass.coe_sub,
    AddSubgroupClass.coe_sub]
  exact sub_mem (sub_mem (sub_mem (Vpr_J hCs hVJ b) (EthE_J hCs (Q2_J hL hKJ b)))
    (LS_J hCs hL hjN hVJ hWJ hb)) (Subalgebra.algebraMap_mem _ _)

include hCs in
theorem Gp_J (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N) (hVJ : FamJ V) (hWJ : FamJ W)
    (hKJ : KJ j K) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Gp j C V W K b ∈ SE (JS d L N) :=
  mul_mem (gexp_mem_SE (neg_mem (Vp_J hCs hL hjN hVJ hWJ hKJ hb)))
    (add_mem (one_mem _) (Wp_J hCs hL hjN hVJ hWJ hb))

include hCs in
theorem Ip_J (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N) (hVJ : FamJ V) (hWJ : FamJ W)
    (hKJ : KJ j K) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Ip j C V W K b ∈ SE (JS d L N) :=
  Subalgebra.smul_mem _ (Gp_J hCs hL hjN hVJ hWJ hKJ hb) _

theorem Ib_J (hVJ : FamJ V) (hWJ : FamJ W) (b : Fin d → ℕ) : Ib V W b ∈ SE (JS d L N) :=
  mul_mem (gexp_mem_SE (neg_mem (hVJ b))) (add_mem (one_mem _) (hWJ b))

include hCs in
theorem k2_J (hVJ : FamJ V) (X : Finset (Lam d L N)) : (k2 j C V X : Alg d L N) ∈ JS d L N := by
  unfold k2; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    rw [Subalgebra.coe_smul]
    refine Subalgebra.smul_mem _ (FCE_J hCs (Vpr_J hCs hVJ b) ?_) _
    rw [AddSubgroupClass.coe_sub]; exact sub_mem (VprL_J hCs hVJ) (Vpr_J hCs hVJ b)
  · rw [Subalgebra.coe_smul, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => ?_) _
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b' _ => FCE_J hCs (Vpr_J hCs hVJ b) (Vpr_J hCs hVJ b')
  · exact zero_mem _

include hCs in
theorem K2_J (hVJ : FamJ V) (U : Finset (Lam d L N)) : (K2 j C V U : Alg d L N) ∈ JS d L N := by
  unfold K2; rw [AddSubmonoidClass.coe_finsetSum]
  exact Subalgebra.sum_mem _ fun X _ => k2_J hCs hVJ X

include hCs in
theorem kap_J (hVJ : FamJ V) (X : Finset (Lam d L N)) (c : Fin d → ℕ) :
    (kap j C V X c : Alg d L N) ∈ JS d L N := by
  unfold kap; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    rw [Subalgebra.coe_smul]
    refine Subalgebra.smul_mem _ (FCE_J hCs (Vpr_J hCs hVJ b) ?_) _
    rw [AddSubgroupClass.coe_sub]; exact sub_mem (VprL_J hCs hVJ) (Vpr_J hCs hVJ b)
  · rw [Subalgebra.coe_smul, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b _ => ?_) _
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b' _ => FCE_J hCs (Vpr_J hCs hVJ b) (Vpr_J hCs hVJ b')
  · exact zero_mem _

include hCs in
theorem Jh_J (hVJ : FamJ V) (c : Fin d → ℕ) (U : Finset (Lam d L N)) :
    (Jh j C V c U : Alg d L N) ∈ JS d L N := by
  classical
  unfold Jh; split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun X _ => kap_J hCs hVJ X c
  · exact zero_mem _

end Blocks

/-! ### The outputs -/

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N} {K : Act d L N}

theorem gmem_J (hCs : ∀ x y, C x y = C y x) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N)
    (hVJ : FamJ V) (hWJ : FamJ W) (hKJ : KJ j K) (U : Finset (Lam d L N)) :
    GMem j C (Ib V W) (Ip j C V W K) K (J2 j K) U (JS d L N) (JS2 d L N) where
  hθ F hF := mem_JS2.2 (by rw [← theta_Jsym, mem_JS.1 hF])
  hι F hF := mem_JS2.2 (by rw [← incl_Jsym, mem_JS.1 hF])
  hE F hF := mem_JS.2 (by rw [← ECC_Jsym2 hCs, mem_JS2.1 hF])
  hK Y hY _ := hKJ Y hY
  hJ b X _ _ := J2_J hL hKJ b X
  hIb b _ _ := Ib_J hVJ hWJ b
  hIp b hb _ := Ip_J hCs hL hjN hVJ hWJ hKJ hb

theorem Knext2_J (hCs : ∀ x y, C x y = C y x) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N)
    (hVJ : FamJ V) (hWJ : FamJ W) (hKJ : KJ j K) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) : (Knext2 j C V W K U : Alg d L N) ∈ JS d L N :=
  Subalgebra.smul_mem _ ((gmem_J hCs hL hjN hVJ hWJ hKJ U).gKnext_mem hU) _

theorem Knew_J (hCs : ∀ x y, C x y = C y x) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N)
    (hVJ : FamJ V) (hWJ : FamJ W) (hKJ : KJ j K) {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) : (Knew j C V W K U : Alg d L N) ∈ JS d L N := by
  rw [Knew, AddSubgroupClass.coe_sub, MulMemClass.coe_mul]
  refine sub_mem (Knext2_J hCs hL hjN hVJ hWJ hKJ hU) (mul_mem ?_ (K2_J hCs hVJ U))
  exact (prod_mem fun b hb => Gp_J hCs hL hjN hVJ hWJ hKJ (mem_blockIdx_of_mem_blocks hb) :
    bpow j (Gp j C V W K) U ∈ SE (JS d L N))

/-- **`J`-invariance of `K_{j+1}`.** -/
theorem Kplus_J (hCs : ∀ x y, C x y = C y x) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N)
    (hVJ : FamJ V) (hWJ : FamJ W) (hKJ : KJ j K) : KJ (j + 1) (Kplus j C V W K) := by
  intro U _
  refine mem_SE.1 (Kout_mem (S := JS d L N) ?_ ?_ ?_)
  · intro X hX _
    rw [bpow_It j C V W K hX]
    exact prod_mem fun b hb => Gp_J hCs hL hjN hVJ hWJ hKJ (mem_blockIdx_of_mem_blocks hb)
  · intro Y hY _
    exact Knew_J hCs hL hjN hVJ hWJ hKJ hY.1
  · intro p _ _
    exact Jh_J hCs hVJ p.1 p.2

/-- **`J`-invariance of `V_{j+1}`.** -/
theorem Vnext2_J (hCs : ∀ x y, C x y = C y x) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N)
    (hVJ : FamJ V) (hWJ : FamJ W) (hKJ : KJ j K) : FamJ (Vnext2 j C V W K) := by
  intro c
  rw [Vnext2, AddSubmonoidClass.coe_finsetSum]
  exact Subalgebra.sum_mem _ fun b hb =>
    Vp_J hCs hL hjN hVJ hWJ hKJ (mem_blockIdx_of_mem_blocks hb)

/-- **`J`-invariance of `𝒲_{j+1}`.** -/
theorem Wnext2_J (hCs : ∀ x y, C x y = C y x) (hL : 2 ^ (d + 3) + 8 * d < L) (hjN : j + 1 < N)
    (hVJ : FamJ V) (hWJ : FamJ W) : FamJ (Wnext2 j C V W) := by
  intro c
  refine mem_SE.1 ?_
  rw [Wnext2]
  exact sub_mem (prod_mem fun b hb => add_mem (one_mem _)
    (Wp_J hCs hL hjN hVJ hWJ (mem_blockIdx_of_mem_blocks hb))) (one_mem _)

end

end Step2
