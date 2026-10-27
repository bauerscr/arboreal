import Step.ZVKAux

/-!
# Proposition `prop:ZVK`: the renormalisation group map preserves `Z`

`𝔼_{C} θ Z_j = e^{-u_{j+1}|Λ|} ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)` (`ZVK`).

The identity holds for any covariance `C`, any `V_j` and any `K_j` (extended to all polymers by
`Kext`), and any choice of `V_{j+1}` and `J`; the specific choices only matter for the estimates.

The proof follows the proof of Proposition `prop:ZVK` in the paper:

1. *Change of coupling constants* (`thetaE_Zj`): the binomial expansion
   `θ e^{-V_j(Λ∖X)} = ∑_Y Ĩ^{Λ∖(X∪Y)} (δI)^Y` (`e:thetaI`, `thetaE_gexp_sdiff`) and the change of
   summation index `(X, Y) ↦ (X ∪ Y, Y)` give `θ Z_j = ∑_W Ĩ^{Λ∖W} K̃(W)` (`e:ZtildeItildeK`).
2. *Factorisation* (`Ktil_eq_prod_comp`): `K̃` is multiplicative over non-touching polymers
   (`Ktil_union`), hence factors over connected components.
3. *Cancellation of small sets* (`Ktil_eq_sum_G0`): inserting `K̃(W) = Ǩ(W) + ∑_B θ J(B, W)`
   (`e:tildeK-checkK`) and expanding the product over components gives
   `K̃(W) = ∑_{(𝒳, X̌)} Ǩ(X̌) ∏_{(B, X) ∈ 𝒳} θ J(B, X)` (`eq:tildeK`), the sum being over the pairs
   `(𝒳, X̌)` satisfying the conditions of `𝒢` other than the closure condition, with
   `X̌ ∪ X_𝒳 = W` (`G0`).
4. *Reblocking* (`ZVK`): pulling the `ψ`-only factors `Ĩ^{Λ∖W}` out of `𝔼_C` (`ECE_inclE_mul`),
   and inserting the partition of unity `1 = ∑_U 1_{\overline{X̌ ∪ ⋃ B^□} = U}`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Generalities -/

/-- `𝔼_C (A G) = A 𝔼_C G` for even `A` in the `ψ` variables only. -/
theorem ECE_inclE_mul {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℝ) (A : EvR Λ)
    (G : EvR (Λ ⊕ Λ)) : ECE C (inclE A * G) = A * ECE C G :=
  Subtype.ext (by simp [EC_incl_mul])

theorem blockSet_disjoint {j : ℕ} {b b' : Fin d → ℕ} (h : b ≠ b') :
    Disjoint (blockSet (L := L) (N := N) j b) (blockSet j b') :=
  Finset.disjoint_left.2 fun _ hx hx' =>
    h ((mem_blockSet.1 hx).symm.trans (mem_blockSet.1 hx'))

theorem Pj_empty (j : ℕ) : Pj j (∅ : Finset (Lam d L N)) = {∅} := by
  ext Y
  rw [mem_Pj, mem_singleton, subset_empty]
  exact ⟨And.left, fun h => ⟨h, h ▸ isPolymer_empty j⟩⟩

theorem mem_pairsU {j : ℕ} {p : (Fin d → ℕ) × Finset (Lam d L N)} :
    p ∈ pairsU j ↔ p.1 ∈ blockIdx (L := L) (N := N) j ∧ IsSmall j p.2 ∧ blockSet j p.1 ⊆ p.2 := by
  simp [pairsU, smallSets, and_assoc]

theorem mem_blocks_of_mem_pairsU {j : ℕ} {p : (Fin d → ℕ) × Finset (Lam d L N)}
    (hp : p ∈ pairsU j) : p.1 ∈ blocks j p.2 :=
  mem_blocks_of_blockSet_subset (blockSet_nonempty_of_mem_blocks (X := univ)
    (mem_pairsU.1 hp).1) (mem_pairsU.1 hp).2.2

theorem isPolymer_Xcal {j : ℕ} {𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))}
    (h : 𝒳 ⊆ pairsU j) : IsPolymer j (Xcal 𝒳) :=
  isPolymer_biUnion _ _ fun _ hp => (mem_pairsU.1 (h hp)).2.1.1

/-- `X_𝒳 ⊆ ⋃_{(B, X) ∈ 𝒳} B^□`. -/
theorem Xcal_subset_Bbox {j : ℕ} {𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))}
    (h : 𝒳 ⊆ pairsU j) : Xcal 𝒳 ⊆ Bbox j 𝒳 := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 hx
  obtain ⟨h1, h2, h3⟩ := mem_pairsU.1 (h hp)
  have hne : (blockSet (L := L) (N := N) j p.1).Nonempty :=
    blockSet_nonempty_of_mem_blocks (X := univ) h1
  exact mem_biUnion.2 ⟨p, hp, subset_nbhd_of_small h2 h3 hne hxp⟩

/-! ### Components -/

section Comp

variable {j : ℕ}

/-- Removing some components from a polymer leaves the union of the other components. -/
theorem biUnion_comp_sdiff {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    {S : Finset (Finset (Lam d L N))} (hS : S ⊆ Comp j W) :
    (Comp j W \ S).biUnion id = W \ S.biUnion id := by
  ext x
  simp only [mem_biUnion, mem_sdiff, id]
  constructor
  · rintro ⟨c, ⟨hc, hcS⟩, hx⟩
    refine ⟨subset_of_mem_comp hc hx, ?_⟩
    rintro ⟨c', hc', hx'⟩
    have : c = c' := by
      by_contra hne
      exact Finset.disjoint_left.1
        (disjoint_of_not_touch (not_touch_of_mem_comp hW hc (hS hc') hne)) hx hx'
    exact hcS (this ▸ hc')
  · rintro ⟨hxW, hxS⟩
    rw [← biUnion_comp hW] at hxW
    obtain ⟨c, hc, hx⟩ := mem_biUnion.1 hxW
    exact ⟨c, ⟨hc, fun hcS => hxS ⟨c, hcS, hx⟩⟩, hx⟩

/-- The components of `W ∖ ⋃ S` for a set `S` of components of `W`. -/
theorem comp_sdiff_biUnion {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    {S : Finset (Finset (Lam d L N))} (hS : S ⊆ Comp j W) :
    Comp j (W \ S.biUnion id) = Comp j W \ S := by
  rw [← biUnion_comp_sdiff hW hS]
  exact comp_eq_of_partition _ (fun c hc => isConn_of_mem_comp hW (mem_sdiff.1 hc).1)
    (fun c hc c' hc' hne => not_touch_of_mem_comp hW (mem_sdiff.1 hc).1 (mem_sdiff.1 hc').1 hne)
    rfl

end Comp

/-! ### Step 1: change of coupling constants (`e:thetaI`, `e:ZtildeItildeK`) -/

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)

/-- `θ e^{-V_j(B)} = e^{-(u+V)_{j+1}(B)} + δI(B)`. -/
theorem thetaE_I (b : Fin d → ℕ) :
    thetaE (gexp (-VE V (blockSet (L := L) (N := N) j b))) =
      inclE (Inext j C V K b) + dI j C V K b := by
  rw [dI]
  abel

/-- The binomial expansion `e:thetaI`:
`θ e^{-V_j(Λ ∖ X)} = ∑_{Y ∈ 𝒫_j(Λ ∖ X)} e^{-(u+V)_{j+1}(Λ ∖ X ∖ Y)} (δI)^Y`. -/
theorem thetaE_gexp_sdiff {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    thetaE (gexp (-VE V (univ \ X))) =
      ∑ Y ∈ Pj j (univ \ X), inclE (InextPow j C V K ((univ \ X) \ Y)) * dIPow j C V K Y := by
  have hS : IsPolymer j (univ \ X) := IsPolymer.sdiff (isPolymer_univ j) hX
  rw [gexp_neg_VE V hS, map_prod, prod_congr rfl fun b _ => thetaE_I j C V K b,
    prod_add_blocks hS]
  refine sum_congr rfl fun Y _ => ?_
  rw [InextPow, map_prod, dIPow]

/-- **`e:ZtildeItildeK`**: `θ Z_j = ∑_{W ∈ 𝒫_j} e^{-(u+V)_{j+1}(Λ ∖ W)} K̃(W)`. -/
theorem thetaE_Zj :
    thetaE (Zj j V K) =
      ∑ W ∈ Pj j univ, inclE (InextPow j C V K (univ \ W)) * Ktil j C V K W := by
  rw [Zj, map_sum]
  have h1 : ∀ X ∈ Pj (L := L) (N := N) j univ, thetaE (gexp (-VE V (univ \ X)) * Kext j K X) =
      ∑ Y ∈ Pj j (univ \ X), inclE (InextPow j C V K (univ \ (X ∪ Y))) *
        (thetaE (Kext j K X) * dIPow j C V K Y) := by
    intro X hX
    rw [map_mul, thetaE_gexp_sdiff j C V K (mem_Pj.1 hX).2, sum_mul]
    refine sum_congr rfl fun Y _ => ?_
    rw [sdiff_sdiff_left, sup_eq_union]
    ring
  rw [sum_congr rfl h1]
  simp_rw [Ktil, mul_sum]
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

/-! ### Step 2: factorisation of `K̃` over components -/

theorem dIPow_empty : dIPow j C V K ∅ = 1 := by
  simp [dIPow, blocks]

theorem Ktil_empty : Ktil j C V K ∅ = 1 := by
  rw [Ktil, Pj_empty, sum_singleton, empty_sdiff, Kext_empty, map_one, dIPow_empty, one_mul]

/-- `K̃` is multiplicative over non-touching polymers. -/
theorem Ktil_union {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B)
    (h : ¬ Touch A B) : Ktil j C V K (A ∪ B) = Ktil j C V K A * Ktil j C V K B := by
  have hd := disjoint_of_not_touch h
  rw [Ktil, Ktil, Ktil, sum_mul_sum, ← sum_product']
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
    have e3 : dIPow j C V K Y = dIPow j C V K (Y ∩ A) * dIPow j C V K (Y ∩ B) := by
      conv_lhs => rw [e2]
      unfold dIPow
      exact prod_blocks_union _ (IsPolymer.inter hY2 hA) (IsPolymer.inter hY2 hB)
        (hd.mono inter_subset_right inter_subset_right)
    show thetaE (Kext j K ((A ∪ B) \ Y)) * dIPow j C V K Y =
      thetaE (Kext j K (A \ (Y ∩ A))) * dIPow j C V K (Y ∩ A) *
        (thetaE (Kext j K (B \ (Y ∩ B))) * dIPow j C V K (Y ∩ B))
    rw [e1, Kext_union K (IsPolymer.sdiff hA (IsPolymer.inter hY2 hA))
      (IsPolymer.sdiff hB (IsPolymer.inter hY2 hB))
      (not_touch_mono h sdiff_subset sdiff_subset), map_mul, e3]
    ring

/-- `K̃(W) = ∏_{W' ∈ Comp(W)} K̃(W')`. -/
theorem Ktil_eq_prod_comp {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    Ktil j C V K W = ∏ c ∈ Comp j W, Ktil j C V K c :=
  eq_prod_comp_of_mul _ (Ktil_empty j C V K) (fun _ _ hA hB h => Ktil_union j C V K hA hB h) hW

/-! ### Step 3: cancellation of small sets (`e:tildeK-checkK`, `eq:tildeK`) -/

/-- The blocks of `c` if `c` is a small set, and `∅` otherwise: `J(B, c) = 0` unless `c` is
small. -/
def tSmall (j : ℕ) (c : Finset (Lam d L N)) : Finset (Fin d → ℕ) :=
  open Classical in if IsSmall j c then blocks j c else ∅

/-- `K̃(W) = Ǩ(W) + ∑_{B ∈ 𝓑_j(W)} θ J(B, W)`, where only small `W` contribute to the sum. -/
theorem Ktil_eq_KchkC_add (c : Finset (Lam d L N)) :
    Ktil j C V K c = KchkC j C V K c + ∑ b ∈ tSmall j c, thetaE (Jb j K b c) := by
  have : ∑ b ∈ tSmall j c, thetaE (Jb j K b c) = ∑ b ∈ blocks j c, thetaE (Jb j K b c) := by
    by_cases hs : IsSmall j c
    · rw [tSmall, if_pos hs]
    · rw [tSmall, if_neg hs, sum_empty]
      refine (sum_eq_zero fun b _ => ?_).symm
      rw [Jb, if_neg fun h => hs h.2.1, map_zero]
  rw [this, KchkC, sub_add_cancel]

/-- The pairs `(𝒳, X̌)` satisfying the conditions of `𝒢(U)` except the closure condition. -/
def GCond0 (j : ℕ)
    (g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)) : Prop :=
  IsPolymer j g.2 ∧ g.1 ⊆ pairsU j ∧
  (∀ p ∈ g.1, ∀ q ∈ g.1, p.2 = q.2 → p = q) ∧
  (∀ p ∈ g.1, ∀ q ∈ g.1, p.2 ≠ q.2 → ¬ Touch p.2 q.2) ∧
  ¬ Touch (Xcal g.1) g.2

/-- The set of pairs `(𝒳, X̌)` satisfying `GCond0`; `𝒢(U)` is its subset with closure `U`. -/
def G0 (j : ℕ) :
    Finset (Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)) :=
  open Classical in ((pairsU j).powerset ×ˢ Pj j univ).filter (GCond0 j)

theorem mem_G0 {g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)} :
    g ∈ G0 j ↔ GCond0 j g := by
  simp only [G0, mem_filter, mem_product, mem_powerset, mem_Pj, subset_univ, true_and]
  exact ⟨And.right, fun h => ⟨⟨h.2.1, h.1⟩, h⟩⟩

theorem Gset_eq (U : Finset (Lam d L N)) :
    Gset j U = (G0 j).filter (fun g => clo j (g.2 ∪ Bbox j g.1) = U) := by
  ext g
  simp only [Gset, G0, mem_filter, GCond, GCond0, and_assoc]

theorem isPolymer_of_mem_G0
    {g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)} (hg : g ∈ G0 j) :
    IsPolymer j (g.2 ∪ Xcal g.1) :=
  IsPolymer.union (mem_G0 j |>.1 hg).1 (isPolymer_Xcal (mem_G0 j |>.1 hg).2.1)

theorem mem_Sec_comp {W : Finset (Lam d L N)} {𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))}
    (h𝒳 : 𝒳 ∈ Sec (Comp j W) (tSmall j)) {p : (Fin d → ℕ) × Finset (Lam d L N)} (hp : p ∈ 𝒳) :
    p.2 ∈ Comp j W ∧ IsSmall j p.2 ∧ p.1 ∈ blocks j p.2 := by
  obtain ⟨h1, h2⟩ := (mem_Sec.1 h𝒳).1 p hp
  by_cases hs : IsSmall j p.2
  · rw [tSmall, if_pos hs] at h2
    exact ⟨h1, hs, h2⟩
  · rw [tSmall, if_neg hs] at h2
    simp at h2

theorem Xcal_eq_biUnion_image (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    Xcal 𝒳 = (𝒳.image Prod.snd).biUnion id := by
  rw [image_biUnion]
  rfl

/-- **Reindexing** the expansion of `∏_{W' ∈ Comp(W)} (Ǩ(W') + ∑_B θ J(B, W'))` as a sum over
the pairs `(𝒳, X̌)` with `X̌ ∪ X_𝒳 = W`. -/
theorem sum_Sec_eq_sum_G0 {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    ∑ 𝒳 ∈ Sec (Comp j W) (tSmall j), (∏ c ∈ Comp j W \ 𝒳.image Prod.snd, KchkC j C V K c) *
        ∏ p ∈ 𝒳, thetaE (Jb j K p.1 p.2) =
      ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
        Kchk j C V K g.2 * ∏ p ∈ g.1, thetaE (Jb j K p.1 p.2) := by
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
    show _ = Kchk j C V K (W \ Xcal 𝒳) * _
    rw [Kchk, Xcal_eq_biUnion_image, comp_sdiff_biUnion hW hS]

/-- **`eq:tildeK`**: `K̃(W) = ∑_{(𝒳, X̌), X̌ ∪ X_𝒳 = W} Ǩ(X̌) ∏_{(B, X) ∈ 𝒳} θ J(B, X)`. -/
theorem Ktil_eq_sum_G0 {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    Ktil j C V K W = ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
      Kchk j C V K g.2 * ∏ p ∈ g.1, thetaE (Jb j K p.1 p.2) := by
  have h := prod_add_sum_eq (Comp j W) (tSmall j) (KchkC j C V K)
    (fun p => thetaE (Jb j K p.1 p.2))
  simp only at h
  rw [Ktil_eq_prod_comp j C V K hW, ← sum_Sec_eq_sum_G0 j C V K hW, ← h]
  exact prod_congr rfl fun c _ => Ktil_eq_KchkC_add j C V K c

/-! ### Step 4: reblocking -/

/-- `e^{-(u+V)_{j+1}(X)}` is multiplicative over disjoint polymers. -/
theorem InextPow_union {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B)
    (h : Disjoint A B) :
    InextPow j C V K (A ∪ B) = InextPow j C V K A * InextPow j C V K B :=
  prod_blocks_union _ hA hB h

/-- `e^{-(u+V)_{j+1}(S)} = e^{-u_{j+1}|S|} e^{-V_{j+1}(S)}` for a polymer `S`. -/
theorem InextPow_eq {S : Finset (Lam d L N)} (hS : IsPolymer j S) :
    InextPow j C V K S = Complex.exp (-((uVnext j C V K).1 * S.card)) •
      gexp (-VE (uVnext j C V K).2 S) := by
  rw [InextPow]
  simp only [Inext]
  rw [prod_smul, ← gexp_neg_VE _ hS, ← Complex.exp_sum, sum_neg_distrib, ← mul_sum]
  congr 4
  conv_rhs => rw [← biUnion_blocks hS]
  rw [card_biUnion fun b _ b' _ hne => blockSet_disjoint hne, Nat.cast_sum]

end Map

/-- **Proposition `prop:ZVK`** (the identity `Z_{j+1} = 𝔼_{C_{j+1}} θ Z_j`). -/
theorem ZVK {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup)
    (K : Act d L N) : ECE C (thetaE (Zj j V K)) = Znext j C V K := by
  -- `𝔼_C θ Z_j = ∑_{(𝒳, X̌)} Ĩ^{Λ ∖ (X̌ ∪ X_𝒳)} 𝔼_C[Ǩ(X̌) ∏ θ J]` (`e:EcthetaZ1`)
  have hL : ∀ W ∈ Pj j univ, ECE C (inclE (InextPow j C V K (univ \ W)) * Ktil j C V K W) =
      ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
        InextPow j C V K (univ \ (g.2 ∪ Xcal g.1)) *
          ECE C (Kchk j C V K g.2 * ∏ p ∈ g.1, thetaE (Jb j K p.1 p.2)) := by
    intro W hW
    rw [ECE_inclE_mul, Ktil_eq_sum_G0 j C V K (mem_Pj.1 hW).2, map_sum, mul_sum]
    refine sum_congr rfl fun g hg => ?_
    rw [(mem_filter.1 hg).2]
  rw [thetaE_Zj j C V K, map_sum, sum_congr rfl hL,
    sum_fiberwise_of_maps_to (s := G0 j) (t := Pj j univ) (g := fun g => g.2 ∪ Xcal g.1)
      fun g hg => mem_Pj.2 ⟨subset_univ _, isPolymer_of_mem_G0 j hg⟩,
    ← sum_fiberwise_of_maps_to (s := G0 j) (t := Pj (j + 1) univ)
      (g := fun g => clo j (g.2 ∪ Bbox j g.1))
      fun g _ => mem_Pj.2 ⟨subset_univ _, isPolymer_clo j _⟩, Znext, smul_sum]
  -- reblocking: the sum over `U ∈ 𝒫_{j+1}`
  refine sum_congr rfl fun U hU => ?_
  have hUp : IsPolymer j U := IsPolymer.of_succ (mem_Pj.1 hU).2
  have hIP : (Complex.exp (-((uVnext j C V K).1 * (univ : Finset (Lam d L N)).card)) *
      Complex.exp ((uVnext j C V K).1 * U.card)) •
        gexp (-VE (uVnext j C V K).2 (univ \ U)) = InextPow j C V K (univ \ U) := by
    rw [InextPow_eq j C V K (IsPolymer.sdiff (isPolymer_univ j) hUp), ← Complex.exp_add]
    congr 2
    have := card_sdiff_add_card_eq_card (subset_univ U)
    have h' : ((univ \ U).card : ℂ) = (univ : Finset (Lam d L N)).card - U.card := by
      rw [eq_sub_iff_add_eq]
      exact_mod_cast this
    rw [h']
    ring
  rw [Knext, Gset_eq, mul_smul_comm, smul_smul, ← smul_mul_assoc, hIP, mul_sum]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨hg, hgU⟩ := mem_filter.1 hg
  have hZ := isPolymer_of_mem_G0 j hg
  have hZU : g.2 ∪ Xcal g.1 ⊆ U := by
    rw [← hgU]
    exact (union_subset_union subset_rfl (Xcal_subset_Bbox ((mem_G0 j).1 hg).2.1)).trans
      (subset_clo j _)
  rw [← mul_assoc, ← InextPow_union j C V K (IsPolymer.sdiff (isPolymer_univ j) hUp)
    (IsPolymer.sdiff hUp hZ)
    (disjoint_sdiff_self_left.mono_right sdiff_subset),
    sdiff_union_sdiff_cancel (subset_univ U) hZU]

end

end Step
