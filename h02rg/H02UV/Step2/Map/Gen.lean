import Step.ZVK
import Grassmann.Truncated
import Grassmann.IBPC

/-!
# The renormalisation group map with general block factors (`h02uv-outline.tex`, (C), (D))

The polymer formula of Definition `def:K+` only uses the block factors through
`δI(B) = θ I_j(B) - I_{j+1}(B)`. Here `I_j = Ib` and `I_{j+1} = Ip` are arbitrary even block
factors, the covariance `C` is complex (`ECC`), and `J` is any function with `J(B, X) = 0`
unless `X` is small. Then (`gZVK`)

  `𝔼_C θ ∑_{X ∈ 𝒫_j} I_j^{Λ∖X} K(X) = ∑_{U ∈ 𝒫_{j+1}} I_{j+1}^{Λ∖U} K_{j+1}(U)`,

with `K_{j+1} = gKnext` given by the formula of `def:K+`. The proof is that of
Proposition `prop:ZVK` (`Step.ZVK`), which never uses the form `I = e^{-V}`.

The second-order map of `h02uv-outline.tex` (block factors `e^{-V(B)}(1 + 𝒲(B))`) is an
instance (`Step2.Map.Defs`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

/-! ### `𝔼_C` on even elements for a complex covariance -/

section Even

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem proj_inv' (F : N (Λ ⊕ Λ)) : proj (inv' F) = inv' (proj F) := by
  rw [proj, inv'_map]

theorem ECC_inv' (C : Matrix Λ Λ ℂ) (F : N (Λ ⊕ Λ)) : ECC C (inv' F) = inv' (ECC C F) := by
  rw [ECC_eq, ECC_eq, expLC_inv', proj_inv']

/-- `𝔼_C` on even elements, complex covariance. -/
def ECCE (C : Matrix Λ Λ ℂ) : EvR (Λ ⊕ Λ) →ₗ[ℂ] EvR Λ where
  toFun F := ⟨ECC C (F : N (Λ ⊕ Λ)), mem_Ev.2 (by rw [← ECC_inv', mem_Ev.1 F.2])⟩
  map_add' F G := Subtype.ext (map_add _ _ _)
  map_smul' r F := Subtype.ext (map_smul _ _ _)

@[simp] theorem coe_ECCE (C : Matrix Λ Λ ℂ) (F : EvR (Λ ⊕ Λ)) :
    (ECCE C F : N Λ) = ECC C (F : N (Λ ⊕ Λ)) := rfl

/-- `𝔼_C (A G) = A 𝔼_C G` for even `A` in the `ψ` variables only. -/
theorem ECCE_inclE_mul (C : Matrix Λ Λ ℂ) (A : EvR Λ) (G : EvR (Λ ⊕ Λ)) :
    ECCE C (inclE A * G) = A * ECCE C G :=
  Subtype.ext (by simp [ECC_incl_mul])

theorem ECCE_inclE (C : Matrix Λ Λ ℂ) (A : EvR Λ) : ECCE C (inclE A) = A := by
  have := ECCE_inclE_mul C A 1
  rwa [mul_one, show ECCE C (1 : EvR (Λ ⊕ Λ)) = 1 from Subtype.ext (by simp [ECC_one]),
    mul_one] at this

end Even

variable {d L N : ℕ} [NeZero L]

/-! ### The general map -/

section Gen

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)) (K : Act d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N))

/-- `I^X = ∏_{B ∈ 𝓑_j(X)} I(B)`. -/
def bpow (I : (Fin d → ℕ) → EvR (Lam d L N)) (X : Finset (Lam d L N)) : EvR (Lam d L N) :=
  ∏ b ∈ blocks j X, I b

/-- `δI(B) = θ I_j(B) - I_{j+1}(B)`. -/
def gdI (b : Fin d → ℕ) : EvR (Lam d L N ⊕ Lam d L N) := thetaE (Ib b) - inclE (Ip b)

/-- `(δI)^X`. -/
def gdIPow (X : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  ∏ b ∈ blocks j X, gdI Ib Ip b

/-- `K̃(W) = ∑_{Y ∈ 𝒫_j(W)} θ K(W ∖ Y) (δI)^Y`. -/
def gKtil (W : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  ∑ Y ∈ Pj j W, thetaE (Kext j K (W \ Y)) * gdIPow j Ib Ip Y

/-- `Ǩ(W) = K̃(W) - ∑_{B ∈ 𝓑_j(W)} θ J(B, W)` for connected `W`. -/
def gKchkC (W : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  gKtil j Ib Ip K W - ∑ b ∈ blocks j W, thetaE (J b W)

/-- `Ǩ(X) = ∏_{W ∈ Comp(X)} Ǩ(W)`. -/
def gKchk (X : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  ∏ W ∈ Comp j X, gKchkC j Ib Ip K J W

/-- `K_{j+1}(U)` (`e:K+-def` without the normalisation `e^{u|U|}`). -/
def gKnext (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  ∑ g ∈ Gset j U, bpow j Ip (U \ (g.2 ∪ Xcal g.1)) *
    ECCE C (gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2))

/-- `Z = ∑_{X ∈ 𝒫_j} I^{Λ∖X} K(X)`. -/
def gZ (I : (Fin d → ℕ) → EvR (Lam d L N)) (K : Act d L N) : EvR (Lam d L N) :=
  ∑ X ∈ Pj j univ, bpow j I (univ \ X) * Kext j K X

theorem bpow_union (I : (Fin d → ℕ) → EvR (Lam d L N)) {A B : Finset (Lam d L N)}
    (hA : IsPolymer j A) (hB : IsPolymer j B) (h : Disjoint A B) :
    bpow j I (A ∪ B) = bpow j I A * bpow j I B :=
  prod_blocks_union _ hA hB h

/-! ### Step 1 -/

theorem thetaE_Ib (b : Fin d → ℕ) : thetaE (Ib b) = inclE (Ip b) + gdI Ib Ip b := by
  rw [gdI]; abel

theorem thetaE_bpow_sdiff {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    thetaE (bpow j Ib (univ \ X)) =
      ∑ Y ∈ Pj j (univ \ X), inclE (bpow j Ip ((univ \ X) \ Y)) * gdIPow j Ib Ip Y := by
  have hS : IsPolymer j (univ \ X) := IsPolymer.sdiff (isPolymer_univ j) hX
  rw [bpow, map_prod, prod_congr rfl fun b _ => thetaE_Ib Ib Ip b, prod_add_blocks hS]
  refine sum_congr rfl fun Y _ => ?_
  rw [bpow, map_prod, gdIPow]

theorem thetaE_gZ :
    thetaE (gZ j Ib K) =
      ∑ W ∈ Pj j univ, inclE (bpow j Ip (univ \ W)) * gKtil j Ib Ip K W := by
  rw [gZ, map_sum]
  have h1 : ∀ X ∈ Pj (L := L) (N := N) j univ, thetaE (bpow j Ib (univ \ X) * Kext j K X) =
      ∑ Y ∈ Pj j (univ \ X), inclE (bpow j Ip (univ \ (X ∪ Y))) *
        (thetaE (Kext j K X) * gdIPow j Ib Ip Y) := by
    intro X hX
    rw [map_mul, thetaE_bpow_sdiff j Ib Ip (mem_Pj.1 hX).2, sum_mul]
    refine sum_congr rfl fun Y _ => ?_
    rw [sdiff_sdiff_left, sup_eq_union]
    ring
  rw [sum_congr rfl h1]
  simp_rw [gKtil, mul_sum]
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun p => ⟨p.1 ∪ p.2, p.2⟩) (fun p => ⟨p.1 \ p.2, p.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨X, Y⟩ h
    obtain ⟨hX, hY⟩ := mem_sigma.1 h
    obtain ⟨-, hXp⟩ := mem_Pj.1 hX
    obtain ⟨-, hYp⟩ := mem_Pj.1 hY
    exact mem_sigma.2 ⟨mem_Pj.2 ⟨subset_univ _, IsPolymer.union hXp hYp⟩,
      mem_Pj.2 ⟨subset_union_right, hYp⟩⟩
  · rintro ⟨W, Y⟩ h
    obtain ⟨hW, hY⟩ := mem_sigma.1 h
    obtain ⟨-, hWp⟩ := mem_Pj.1 hW
    obtain ⟨hYW, hYp⟩ := mem_Pj.1 hY
    refine mem_sigma.2 ⟨mem_Pj.2 ⟨subset_univ _, IsPolymer.sdiff hWp hYp⟩, mem_Pj.2 ⟨?_, hYp⟩⟩
    intro y hy
    simp only [mem_sdiff, mem_univ, true_and, not_and, not_not]
    exact fun _ => hy
  · rintro ⟨X, Y⟩ h
    obtain ⟨-, hY⟩ := mem_sigma.1 h
    have hd : Disjoint X Y :=
      (disjoint_sdiff : Disjoint X (univ \ X)).mono_right (mem_Pj.1 hY).1
    simp only [union_sdiff_cancel_right hd]
  · rintro ⟨W, Y⟩ h
    obtain ⟨-, hY⟩ := mem_sigma.1 h
    simp only [sdiff_union_of_subset (mem_Pj.1 hY).1]
  · rintro ⟨X, Y⟩ h
    obtain ⟨-, hY⟩ := mem_sigma.1 h
    have hd : Disjoint X Y :=
      (disjoint_sdiff : Disjoint X (univ \ X)).mono_right (mem_Pj.1 hY).1
    simp only [union_sdiff_cancel_right hd]

/-! ### Step 2 -/

theorem gdIPow_empty : gdIPow j Ib Ip (∅ : Finset (Lam d L N)) = 1 := by
  simp [gdIPow, blocks]

theorem gKtil_empty : gKtil j Ib Ip K ∅ = 1 := by
  rw [gKtil, Pj_empty, sum_singleton, empty_sdiff, Kext_empty, map_one, gdIPow_empty, one_mul]

theorem gKtil_union {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B)
    (h : ¬ Touch A B) : gKtil j Ib Ip K (A ∪ B) = gKtil j Ib Ip K A * gKtil j Ib Ip K B := by
  have hd := disjoint_of_not_touch h
  rw [gKtil, gKtil, gKtil, sum_mul_sum, ← sum_product']
  refine sum_nbij' (fun Y => (Y ∩ A, Y ∩ B)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro Y hY
    obtain ⟨-, hY2⟩ := mem_Pj.1 hY
    exact mem_product.2 ⟨mem_Pj.2 ⟨inter_subset_right, IsPolymer.inter hY2 hA⟩,
      mem_Pj.2 ⟨inter_subset_right, IsPolymer.inter hY2 hB⟩⟩
  · rintro ⟨Y1, Y2⟩ hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    obtain ⟨h1s, h1p⟩ := mem_Pj.1 h1
    obtain ⟨h2s, h2p⟩ := mem_Pj.1 h2
    exact mem_Pj.2 ⟨union_subset_union h1s h2s, IsPolymer.union h1p h2p⟩
  · intro Y hY
    have hY1 := (mem_Pj.1 hY).1
    ext x
    have := @hY1 x
    simp only [mem_union, mem_inter] at this ⊢
    tauto
  · rintro ⟨Y1, Y2⟩ hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    have h1s := (mem_Pj.1 h1).1
    have h2s := (mem_Pj.1 h2).1
    refine Prod.ext ?_ ?_ <;> ext x <;>
      have := @h1s x <;> have := @h2s x <;>
      have := fun h => Finset.disjoint_left.1 hd (show x ∈ A from h) <;>
      simp only [mem_union, mem_inter] at * <;> tauto
  · intro Y hY
    obtain ⟨hY1, hY2⟩ := mem_Pj.1 hY
    have e1 : (A ∪ B) \ Y = (A \ (Y ∩ A)) ∪ (B \ (Y ∩ B)) := by
      ext x
      have := fun h => Finset.disjoint_left.1 hd (show x ∈ A from h)
      simp only [mem_union, mem_sdiff, mem_inter] at this ⊢
      tauto
    have e2 : Y = (Y ∩ A) ∪ (Y ∩ B) := by
      ext x
      have := @hY1 x
      simp only [mem_union, mem_inter] at this ⊢
      tauto
    have e3 : gdIPow j Ib Ip Y = gdIPow j Ib Ip (Y ∩ A) * gdIPow j Ib Ip (Y ∩ B) := by
      conv_lhs => rw [e2]
      unfold gdIPow
      exact prod_blocks_union _ (IsPolymer.inter hY2 hA) (IsPolymer.inter hY2 hB)
        (hd.mono inter_subset_right inter_subset_right)
    show thetaE (Kext j K ((A ∪ B) \ Y)) * gdIPow j Ib Ip Y =
      thetaE (Kext j K (A \ (Y ∩ A))) * gdIPow j Ib Ip (Y ∩ A) *
        (thetaE (Kext j K (B \ (Y ∩ B))) * gdIPow j Ib Ip (Y ∩ B))
    rw [e1, Kext_union K (IsPolymer.sdiff hA (IsPolymer.inter hY2 hA))
      (IsPolymer.sdiff hB (IsPolymer.inter hY2 hB))
      (not_touch_mono h sdiff_subset sdiff_subset), map_mul, e3]
    ring

theorem gKtil_eq_prod_comp {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    gKtil j Ib Ip K W = ∏ c ∈ Comp j W, gKtil j Ib Ip K c :=
  eq_prod_comp_of_mul _ (gKtil_empty j Ib Ip K)
    (fun _ _ hA hB h => gKtil_union j Ib Ip K hA hB h) hW

/-! ### Step 3 -/

variable {J} (hJ : ∀ b c, ¬ IsSmall j c → J b c = 0)
include hJ

theorem gKtil_eq_KchkC_add (c : Finset (Lam d L N)) :
    gKtil j Ib Ip K c = gKchkC j Ib Ip K J c + ∑ b ∈ tSmall j c, thetaE (J b c) := by
  have : ∑ b ∈ tSmall j c, thetaE (J b c) = ∑ b ∈ blocks j c, thetaE (J b c) := by
    by_cases hs : IsSmall j c
    · rw [tSmall, if_pos hs]
    · rw [tSmall, if_neg hs, sum_empty]
      refine (sum_eq_zero fun b _ => ?_).symm
      rw [hJ b c hs, map_zero]
  rw [this, gKchkC, sub_add_cancel]

omit hJ in
theorem gsum_Sec_eq_sum_G0 {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    ∑ 𝒳 ∈ Sec (Comp j W) (tSmall j), (∏ c ∈ Comp j W \ 𝒳.image Prod.snd,
        gKchkC j Ib Ip K J c) * ∏ p ∈ 𝒳, thetaE (J p.1 p.2) =
      ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
        gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2) := by
  refine sum_nbij' (fun 𝒳 => (𝒳, W \ Xcal 𝒳)) (fun g => g.1) ?_ ?_ ?_ ?_ ?_
  · intro 𝒳 h𝒳
    have hS : 𝒳.image Prod.snd ⊆ Comp j W := fun c hc => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
      exact (mem_Sec_comp j h𝒳 hp).1
    have hsub : 𝒳 ⊆ pairsU j := fun p hp => by
      obtain ⟨-, hs, hb⟩ := mem_Sec_comp j h𝒳 hp
      exact mem_pairsU.2 ⟨blocks_mono (subset_univ _) hb, hs,
        blockSet_subset_of_mem_blocks hs.1 hb⟩
    have hXW : Xcal 𝒳 ⊆ W := biUnion_subset.2 fun p hp =>
      subset_of_mem_comp (mem_Sec_comp j h𝒳 hp).1
    refine mem_filter.2 ⟨(mem_G0 j).2 ⟨IsPolymer.sdiff hW (isPolymer_Xcal hsub), hsub,
      (mem_Sec.1 h𝒳).2, fun p hp q hq hne => not_touch_of_mem_comp hW
        (mem_Sec_comp j h𝒳 hp).1 (mem_Sec_comp j h𝒳 hq).1 hne, ?_⟩,
      sdiff_union_of_subset hXW⟩
    show ¬ Touch (Xcal 𝒳) (W \ Xcal 𝒳)
    rw [Xcal_eq_biUnion_image, ← biUnion_comp_sdiff hW hS]
    rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨c, hc, hx⟩ := mem_biUnion.1 hx
    obtain ⟨c', hc', hy⟩ := mem_biUnion.1 hy
    have hc'' := mem_sdiff.1 hc'
    exact not_touch_of_mem_comp hW (hS hc) hc''.1 (fun h => hc''.2 (h ▸ hc))
      ⟨x, hx, y, hy, hxy⟩
  · intro g hg
    obtain ⟨hg, hgW⟩ := mem_filter.1 hg
    obtain ⟨-, hsub, hinj, htouch, hX⟩ := (mem_G0 j).1 hg
    refine mem_Sec.2 ⟨fun p hp => ?_, hinj⟩
    have hp' := mem_pairsU.1 (hsub hp)
    have hpX : p.2 ⊆ Xcal g.1 := subset_biUnion_of_mem Prod.snd hp
    have hpW : p.2 ⊆ W := by rw [← hgW]; exact hpX.trans subset_union_right
    refine ⟨?_, by rw [tSmall, if_pos hp'.2.1]; exact mem_blocks_of_mem_pairsU (hsub hp)⟩
    have hnt : ¬ Touch p.2 (W \ p.2) := by
      rintro ⟨x, hx, y, hy, hxy⟩
      obtain ⟨hyW, hyp⟩ := mem_sdiff.1 hy
      rw [← hgW] at hyW
      rcases mem_union.1 hyW with hy2 | hy2
      · exact hX ⟨x, hpX hx, y, hy2, hxy⟩
      · obtain ⟨q, hq, hyq⟩ := mem_biUnion.1 hy2
        exact htouch p hp q hq (fun h => hyp (h ▸ hyq)) ⟨x, hx, y, hyq, hxy⟩
    have := comp_union hp'.2.1.1 (IsPolymer.sdiff hW hp'.2.1.1) hnt
    rw [union_sdiff_of_subset hpW, comp_of_isConn ⟨hp'.2.1.1, hp'.2.1.2.1⟩] at this
    rw [this]
    exact mem_union_left _ (mem_singleton_self _)
  · intro 𝒳 _
    rfl
  · intro g hg
    obtain ⟨hg, hgW⟩ := mem_filter.1 hg
    obtain ⟨-, -, -, -, hX⟩ := (mem_G0 j).1 hg
    refine Prod.ext rfl ?_
    show W \ Xcal g.1 = g.2
    rw [← hgW, union_sdiff_cancel_right (disjoint_of_not_touch hX).symm]
  · intro 𝒳 h𝒳
    have hS : 𝒳.image Prod.snd ⊆ Comp j W := fun c hc => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
      exact (mem_Sec_comp j h𝒳 hp).1
    show _ = gKchk j Ib Ip K J (W \ Xcal 𝒳) * _
    rw [gKchk, Xcal_eq_biUnion_image, comp_sdiff_biUnion hW hS]

theorem gKtil_eq_sum_G0 {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    gKtil j Ib Ip K W = ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
      gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2) := by
  have h := prod_add_sum_eq (Comp j W) (tSmall j) (gKchkC j Ib Ip K J)
    (fun p => thetaE (J p.1 p.2))
  simp only at h
  rw [gKtil_eq_prod_comp j Ib Ip K hW, ← gsum_Sec_eq_sum_G0 j Ib Ip K hW, ← h]
  exact prod_congr rfl fun c _ => gKtil_eq_KchkC_add j Ib Ip K hJ c

/-! ### Step 4 -/

/-- **Proposition `prop:ZVK` for general block factors.** -/
theorem gZVK : ECCE C (thetaE (gZ j Ib K)) =
    ∑ U ∈ Pj (j + 1) univ, bpow j Ip (univ \ U) * gKnext j C Ib Ip K J U := by
  have hL : ∀ W ∈ Pj j univ, ECCE C (inclE (bpow j Ip (univ \ W)) * gKtil j Ib Ip K W) =
      ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
        bpow j Ip (univ \ (g.2 ∪ Xcal g.1)) *
          ECCE C (gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2)) := by
    intro W hW
    rw [ECCE_inclE_mul, gKtil_eq_sum_G0 j Ib Ip K hJ (mem_Pj.1 hW).2, map_sum, mul_sum]
    refine sum_congr rfl fun g hg => ?_
    rw [(mem_filter.1 hg).2]
  rw [thetaE_gZ j Ib Ip K, map_sum, sum_congr rfl hL,
    sum_fiberwise_of_maps_to (s := G0 j) (t := Pj j univ) (g := fun g => g.2 ∪ Xcal g.1)
      fun g hg => mem_Pj.2 ⟨subset_univ _, isPolymer_of_mem_G0 j hg⟩,
    ← sum_fiberwise_of_maps_to (s := G0 j) (t := Pj (j + 1) univ)
      (g := fun g => clo j (g.2 ∪ Bbox j g.1))
      fun g _ => mem_Pj.2 ⟨subset_univ _, isPolymer_clo j _⟩]
  refine sum_congr rfl fun U hU => ?_
  have hUp : IsPolymer j U := IsPolymer.of_succ (mem_Pj.1 hU).2
  rw [gKnext, Gset_eq, mul_sum]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨hg, hgU⟩ := mem_filter.1 hg
  have hZ := isPolymer_of_mem_G0 j hg
  have hZU : g.2 ∪ Xcal g.1 ⊆ U := by
    rw [← hgU]
    exact (union_subset_union subset_rfl (Xcal_subset_Bbox ((mem_G0 j).1 hg).2.1)).trans
      (subset_clo j _)
  rw [← mul_assoc, ← bpow_union j Ip (IsPolymer.sdiff (isPolymer_univ j) hUp)
    (IsPolymer.sdiff hUp hZ)
    (disjoint_sdiff_self_left.mono_right sdiff_subset),
    sdiff_union_sdiff_cancel (subset_univ U) hZU]

end Gen

end

end Step2
