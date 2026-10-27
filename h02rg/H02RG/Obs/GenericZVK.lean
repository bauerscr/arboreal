import Obs.GenericDefs

/-!
# Proposition `prop:ZVK` for the generic renormalisation group map

`E θ Z_j = e^{-u_{j+1}(Λ)} ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)` (`ZVK_G`).

The proof is that of `Step.ZVK`; it only uses the ring axioms, that `θ` and `ι` are ring
homomorphisms, `E (ι a g) = a E g` (`hE`), `J(B, X) = 0` unless `X` is small (`hJ`),
`e^{u_{j+1}(B)} e^{-u_{j+1}(B)} = 1` (`hu`), and the polymer combinatorics of `Step`.
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

/-! ### Generalities -/

section Gen

variable {M : Type*} [CommMonoid M] {j : ℕ}

theorem KextG_empty (K : Finset (Lam d L N) → M) : KextG j K ∅ = 1 := by
  simp [KextG, comp_empty]

/-- `KextG` is multiplicative over non-touching polymers. -/
theorem KextG_union (K : Finset (Lam d L N) → M) {A B : Finset (Lam d L N)} (hA : IsPolymer j A)
    (hB : IsPolymer j B) (h : ¬ Touch A B) : KextG j K (A ∪ B) = KextG j K A * KextG j K B := by
  rw [KextG, comp_union hA hB h, prod_union (disjoint_comp hA h), KextG, KextG]

theorem bpow_empty (f : (Fin d → ℕ) → M) : bpow j f (∅ : Finset (Lam d L N)) = 1 := by
  simp [bpow, blocks]

/-- A product over blocks is multiplicative over disjoint polymers. -/
theorem bpow_union (f : (Fin d → ℕ) → M) {A B : Finset (Lam d L N)} (hA : IsPolymer j A)
    (hB : IsPolymer j B) (h : Disjoint A B) : bpow j f (A ∪ B) = bpow j f A * bpow j f B :=
  prod_blocks_union _ hA hB h

end Gen

section Map

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]
  (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)

/-! ### Step 1: change of coupling constants -/

/-- `θ e^{-V_j(B)} = e^{-(u+V)_{j+1}(B)} + δI(B)`. -/
theorem theta_I0 (b : Fin d → ℕ) : A.θ (F.I0 b) = A.ι (It F b) + dIG A F b := by
  rw [dIG]; abel

/-- The binomial expansion `e:thetaI`. -/
theorem theta_bpow_sdiff {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    A.θ (bpow j F.I0 (univ \ X)) =
      ∑ Y ∈ Pj j (univ \ X), A.ι (ItPow j F ((univ \ X) \ Y)) * dIPowG A j F Y := by
  have hS : IsPolymer j (univ \ X) := IsPolymer.sdiff (isPolymer_univ j) hX
  rw [bpow, map_prod, prod_congr rfl fun b _ => theta_I0 A F b, prod_add_blocks hS]
  refine sum_congr rfl fun Y _ => ?_
  rw [ItPow, bpow, map_prod, dIPowG, bpow]

/-- **`e:ZtildeItildeK`**: `θ Z_j = ∑_{W ∈ 𝒫_j} e^{-(u+V)_{j+1}(Λ ∖ W)} K̃(W)`. -/
theorem theta_ZjG :
    A.θ (ZjG j F) = ∑ W ∈ Pj j univ, A.ι (ItPow j F (univ \ W)) * KtilG A j F W := by
  rw [ZjG, map_sum]
  have h1 : ∀ X ∈ Pj (L := L) (N := N) j univ,
      A.θ (bpow j F.I0 (univ \ X) * KextG j F.K X) =
      ∑ Y ∈ Pj j (univ \ X), A.ι (ItPow j F (univ \ (X ∪ Y))) *
        (A.θ (KextG j F.K X) * dIPowG A j F Y) := by
    intro X hX
    rw [map_mul, theta_bpow_sdiff A j F (mem_Pj.1 hX).2, sum_mul]
    refine sum_congr rfl fun Y _ => ?_
    rw [sdiff_sdiff_left, sup_eq_union]
    ring
  rw [sum_congr rfl h1]
  simp_rw [KtilG, mul_sum]
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

theorem dIPowG_empty : dIPowG A j F ∅ = 1 := bpow_empty _

theorem KtilG_empty : KtilG A j F ∅ = 1 := by
  rw [KtilG, Pj_empty, sum_singleton, empty_sdiff, KextG_empty, map_one, dIPowG_empty, one_mul]

/-- `K̃` is multiplicative over non-touching polymers. -/
theorem KtilG_union {X Y : Finset (Lam d L N)} (hA : IsPolymer j X) (hB : IsPolymer j Y)
    (h : ¬ Touch X Y) : KtilG A j F (X ∪ Y) = KtilG A j F X * KtilG A j F Y := by
  have hd := disjoint_of_not_touch h
  rw [KtilG, KtilG, KtilG, sum_mul_sum, ← sum_product']
  refine sum_nbij' (fun Z => (Z ∩ X, Z ∩ Y)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro Z hZ
    obtain ⟨-, hZ2⟩ := mem_Pj.1 hZ
    exact mem_product.2 ⟨mem_Pj.2 ⟨inter_subset_right, IsPolymer.inter hZ2 hA⟩,
      mem_Pj.2 ⟨inter_subset_right, IsPolymer.inter hZ2 hB⟩⟩
  · rintro ⟨Y1, Y2⟩ hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    obtain ⟨h1s, h1p⟩ := mem_Pj.1 h1
    obtain ⟨h2s, h2p⟩ := mem_Pj.1 h2
    exact mem_Pj.2 ⟨union_subset_union h1s h2s, IsPolymer.union h1p h2p⟩
  · intro Z hZ
    have hY1 := (mem_Pj.1 hZ).1
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
      have := fun h => Finset.disjoint_left.1 hd (show x ∈ X from h) <;>
      simp only [mem_union, mem_inter] at * <;> tauto
  · intro Z hZ
    obtain ⟨hY1, hY2⟩ := mem_Pj.1 hZ
    have e1 : (X ∪ Y) \ Z = (X \ (Z ∩ X)) ∪ (Y \ (Z ∩ Y)) := by
      ext x
      have := fun h => Finset.disjoint_left.1 hd (show x ∈ X from h)
      simp only [mem_union, mem_sdiff, mem_inter] at this ⊢
      tauto
    have e2 : Z = (Z ∩ X) ∪ (Z ∩ Y) := by
      ext x
      have := @hY1 x
      simp only [mem_union, mem_inter] at this ⊢
      tauto
    have e3 : dIPowG A j F Z = dIPowG A j F (Z ∩ X) * dIPowG A j F (Z ∩ Y) := by
      conv_lhs => rw [e2]
      exact bpow_union _ (IsPolymer.inter hY2 hA) (IsPolymer.inter hY2 hB)
        (hd.mono inter_subset_right inter_subset_right)
    show A.θ (KextG j F.K ((X ∪ Y) \ Z)) * dIPowG A j F Z =
      A.θ (KextG j F.K (X \ (Z ∩ X))) * dIPowG A j F (Z ∩ X) *
        (A.θ (KextG j F.K (Y \ (Z ∩ Y))) * dIPowG A j F (Z ∩ Y))
    rw [e1, KextG_union F.K (IsPolymer.sdiff hA (IsPolymer.inter hY2 hA))
      (IsPolymer.sdiff hB (IsPolymer.inter hY2 hB))
      (not_touch_mono h sdiff_subset sdiff_subset), map_mul, e3]
    ring

/-- `K̃(W) = ∏_{W' ∈ Comp(W)} K̃(W')`. -/
theorem KtilG_eq_prod_comp {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    KtilG A j F W = ∏ c ∈ Comp j W, KtilG A j F c :=
  eq_prod_comp_of_mul _ (KtilG_empty A j F) (fun _ _ hA hB h => KtilG_union A j F hA hB h) hW

/-! ### Step 3: cancellation of small sets -/

variable {A j F}

/-- `K̃(W) = Ǩ(W) + ∑_{B ∈ 𝓑_j(W)} θ J(B, W)`, where only small `W` contribute to the sum. -/
theorem KtilG_eq_KchkCG_add (hJ : ∀ b X, ¬ IsSmall j X → F.J b X = 0)
    (c : Finset (Lam d L N)) :
    KtilG A j F c = KchkCG A j F c + ∑ b ∈ tSmall j c, A.θ (F.J b c) := by
  have : ∑ b ∈ tSmall j c, A.θ (F.J b c) = ∑ b ∈ blocks j c, A.θ (F.J b c) := by
    by_cases hs : IsSmall j c
    · rw [tSmall, if_pos hs]
    · rw [tSmall, if_neg hs, sum_empty]
      refine (sum_eq_zero fun b _ => ?_).symm
      rw [hJ b c hs, map_zero]
  rw [this, KchkCG, sub_add_cancel]

variable (A j F)

/-- Reindexing the expansion of `∏_{W' ∈ Comp(W)} (Ǩ(W') + ∑_B θ J(B, W'))`. -/
theorem sum_Sec_eq_sum_G0_G {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    ∑ 𝒳 ∈ Sec (Comp j W) (tSmall j), (∏ c ∈ Comp j W \ 𝒳.image Prod.snd, KchkCG A j F c) *
        ∏ p ∈ 𝒳, A.θ (F.J p.1 p.2) =
      ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
        KchkG A j F g.2 * JprodG A F g.1 := by
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
    show _ = KchkG A j F (W \ Xcal 𝒳) * _
    rw [KchkG, Xcal_eq_biUnion_image, comp_sdiff_biUnion hW hS]
    rfl

variable {A j F}

/-- **`eq:tildeK`**: `K̃(W) = ∑_{(𝒳, X̌), X̌ ∪ X_𝒳 = W} Ǩ(X̌) ∏_{(B, X) ∈ 𝒳} θ J(B, X)`. -/
theorem KtilG_eq_sum_G0 (hJ : ∀ b X, ¬ IsSmall j X → F.J b X = 0) {W : Finset (Lam d L N)}
    (hW : IsPolymer j W) :
    KtilG A j F W = ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
      KchkG A j F g.2 * JprodG A F g.1 := by
  have h := prod_add_sum_eq (Comp j W) (tSmall j) (KchkCG A j F)
    (fun p => A.θ (F.J p.1 p.2))
  simp only at h
  rw [KtilG_eq_prod_comp A j F hW, ← sum_Sec_eq_sum_G0_G A j F hW, ← h]
  exact prod_congr rfl fun c _ => KtilG_eq_KchkCG_add hJ c

variable (A j F)

/-! ### Step 4: reblocking -/

/-- `e^{-(u+V)_{j+1}(X)}` is multiplicative over disjoint polymers. -/
theorem ItPow_union {X Y : Finset (Lam d L N)} (hA : IsPolymer j X) (hB : IsPolymer j Y)
    (h : Disjoint X Y) : ItPow j F (X ∪ Y) = ItPow j F X * ItPow j F Y :=
  bpow_union _ hA hB h

theorem PrefG_union {X Y : Finset (Lam d L N)} (hA : IsPolymer j X) (hB : IsPolymer j Y)
    (h : Disjoint X Y) : PrefG j F (X ∪ Y) = PrefG j F X * PrefG j F Y :=
  bpow_union _ hA hB h

theorem PrefG_empty : PrefG j F ∅ = 1 := bpow_empty _

/-- `e^{-u(Λ)} e^{-V(Λ ∖ U)} e^{u(U)} = e^{-(u+V)(Λ ∖ U)}`. -/
theorem bpow_eum_mul (hu : ∀ b ∈ blocks j (univ : Finset (Lam d L N)), F.eu b * F.eum b = 1)
    {U : Finset (Lam d L N)} (hU : IsPolymer j U) :
    bpow j F.eum (univ : Finset (Lam d L N)) * (bpow j F.eV (univ \ U) * PrefG j F U) =
      ItPow j F (univ \ U) := by
  have hS : IsPolymer j (univ \ U) := IsPolymer.sdiff (isPolymer_univ j) hU
  have e : (univ : Finset (Lam d L N)) = (univ \ U) ∪ U := (sdiff_union_of_subset (subset_univ U)).symm
  have h1 : bpow j F.eum U * PrefG j F U = 1 := by
    rw [PrefG, bpow, bpow, ← prod_mul_distrib]
    exact prod_eq_one fun b hb => by
      rw [mul_comm]; exact hu b (blocks_mono (subset_univ _) hb)
  rw [e, bpow_union _ hS hU disjoint_sdiff_self_left, ← e]
  calc bpow j F.eum (univ \ U) * bpow j F.eum U * (bpow j F.eV (univ \ U) * PrefG j F U)
      = (bpow j F.eum (univ \ U) * bpow j F.eV (univ \ U)) * (bpow j F.eum U * PrefG j F U) := by
        ring
    _ = _ := by rw [h1, mul_one, ItPow, bpow, bpow, bpow, ← prod_mul_distrib]; rfl

end Map

/-- **Proposition `prop:ZVK`** for the generic renormalisation group map:
`E θ Z_j = e^{-u_{j+1}(Λ)} ∑_{U ∈ 𝒫_{j+1}} e^{-V_{j+1}(Λ ∖ U)} K_{j+1}(U)`. -/
theorem ZVK_G {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]
    (A : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)
    (hE : ∀ a g, A.E (A.ι a * g) = a * A.E g)
    (hJ : ∀ b X, ¬ IsSmall j X → F.J b X = 0)
    (hu : ∀ b ∈ blocks j (univ : Finset (Lam d L N)), F.eu b * F.eum b = 1) :
    A.E (A.θ (ZjG j F)) = ZnextG A j F := by
  have hL : ∀ W ∈ Pj j univ, A.E (A.ι (ItPow j F (univ \ W)) * KtilG A j F W) =
      ∑ g ∈ (G0 j).filter (fun g => g.2 ∪ Xcal g.1 = W),
        ItPow j F (univ \ (g.2 ∪ Xcal g.1)) * A.E (KchkG A j F g.2 * JprodG A F g.1) := by
    intro W hW
    rw [hE, KtilG_eq_sum_G0 hJ (mem_Pj.1 hW).2, map_sum, mul_sum]
    refine sum_congr rfl fun g hg => ?_
    rw [(mem_filter.1 hg).2]
  rw [theta_ZjG A j F, map_sum, sum_congr rfl hL,
    sum_fiberwise_of_maps_to (s := G0 j) (t := Pj j univ) (g := fun g => g.2 ∪ Xcal g.1)
      fun g hg => mem_Pj.2 ⟨subset_univ _, isPolymer_of_mem_G0 j hg⟩,
    ← sum_fiberwise_of_maps_to (s := G0 j) (t := Pj (j + 1) univ)
      (g := fun g => clo j (g.2 ∪ Bbox j g.1))
      fun g _ => mem_Pj.2 ⟨subset_univ _, isPolymer_clo j _⟩, ZnextG, mul_sum]
  refine sum_congr rfl fun U hU => ?_
  have hUp : IsPolymer j U := IsPolymer.of_succ (mem_Pj.1 hU).2
  rw [KnextG, Gset_eq, ← mul_assoc, ← mul_assoc, mul_assoc (bpow j F.eum _),
    bpow_eum_mul j F hu hUp, mul_sum]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨hg, hgU⟩ := mem_filter.1 hg
  have hZ := isPolymer_of_mem_G0 j hg
  have hZU : g.2 ∪ Xcal g.1 ⊆ U := by
    rw [← hgU]
    exact (union_subset_union subset_rfl (Xcal_subset_Bbox ((mem_G0 j).1 hg).2.1)).trans
      (subset_clo j _)
  rw [KtermG, ← mul_assoc, ← ItPow_union j F (IsPolymer.sdiff (isPolymer_univ j) hUp)
    (IsPolymer.sdiff hUp hZ)
    (disjoint_sdiff_self_left.mono_right sdiff_subset),
    sdiff_union_sdiff_cancel (subset_univ U) hZU]

end

end Obs.Gen
