import Step2.Map.Lambda

/-!
# The change of variables of Brydges–Slade (Proposition 4.1, (D.13))

At a fixed scale `k`, let `I` be block factors, `I^X = ∏_{B ∈ 𝓑_k(X)} I(B)`, let `J(B, U)` vanish
unless `U` is small, and let `M` be given on connected polymers. Put `J̄(B, U) = I^U J(B, U)` and
suppose that `K_in(Y) = M(Y) + ∑_{B ∈ 𝓑(Y)} J̄(B, Y)` for connected `Y`. Define (`Kout`)

  `K_out(W) = ∑_{(𝒳, U_M)} I^{W ∖ (U_M ∪ X_𝒳)} M^{U_M} ∏_{(B, U) ∈ 𝒳} J̄(B, U)`,

the sum over `(𝒳, U_M) ∈ 𝒢₀` with `U_M ∪ ⋃_{(B,U) ∈ 𝒳} B^□ = W`, where `M^{U_M}` is the product of
`M` over the components of `U_M` (`Kext`). Then (`reblock_ZVK`)

  `∑_U I^{Λ∖U} ∏_{Y ∈ Comp(U)} K_in(Y) = ∑_W I^{Λ∖W} K_out(W)`,

and `K_out` factorises over non-touching polymers (`Kout_union`).
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

section Expand

variable (k : ℕ) {R : Type*} [CommRing R]

/-- **The expansion of `∏_{c ∈ Comp(W)} (a(c) + ∑_{B} f(B, c))` over `𝒢₀`.** -/
theorem prod_comp_add_eq_sum_G0 {W : Finset (Lam d L N)} (hW : IsPolymer k W)
    (a : Finset (Lam d L N) → R) (f : (Fin d → ℕ) × Finset (Lam d L N) → R) :
    ∏ c ∈ Comp k W, (a c + ∑ b ∈ tSmall k c, f (b, c)) =
      ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Xcal g.1 = W),
        (∏ c ∈ Comp k g.2, a c) * ∏ p ∈ g.1, f p := by
  rw [prod_add_sum_eq (Comp k W) (tSmall k) a f]
  refine sum_nbij' (fun 𝒳 => (𝒳, W \ Xcal 𝒳)) (fun g => g.1) ?_ ?_ ?_ ?_ ?_
  · intro 𝒳 h𝒳
    have hS : 𝒳.image Prod.snd ⊆ Comp k W := fun c hc => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
      exact (mem_Sec_comp k h𝒳 hp).1
    have hsub : 𝒳 ⊆ pairsU k := fun p hp => by
      obtain ⟨-, hs, hb⟩ := mem_Sec_comp k h𝒳 hp
      exact mem_pairsU.2 ⟨blocks_mono (subset_univ _) hb, hs,
        blockSet_subset_of_mem_blocks hs.1 hb⟩
    have hXW : Xcal 𝒳 ⊆ W := biUnion_subset.2 fun p hp =>
      subset_of_mem_comp (mem_Sec_comp k h𝒳 hp).1
    refine mem_filter.2 ⟨(mem_G0 k).2 ⟨IsPolymer.sdiff hW (isPolymer_Xcal hsub), hsub,
      (mem_Sec.1 h𝒳).2, fun p hp q hq hne => not_touch_of_mem_comp hW
        (mem_Sec_comp k h𝒳 hp).1 (mem_Sec_comp k h𝒳 hq).1 hne, ?_⟩,
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
    obtain ⟨-, hsub, hinj, htouch, hX⟩ := (mem_G0 k).1 hg
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
    obtain ⟨-, -, -, -, hX⟩ := (mem_G0 k).1 hg
    refine Prod.ext rfl ?_
    show W \ Xcal g.1 = g.2
    rw [← hgW, union_sdiff_cancel_right (disjoint_of_not_touch hX).symm]
  · intro 𝒳 h𝒳
    have hS : 𝒳.image Prod.snd ⊆ Comp k W := fun c hc => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
      exact (mem_Sec_comp k h𝒳 hp).1
    show _ = (∏ c ∈ Comp k (W \ Xcal 𝒳), a c) * _
    rw [Xcal_eq_biUnion_image, comp_sdiff_biUnion hW hS]

end Expand

/-! ### The change of variables -/

section Reblock

variable (k : ℕ) (I : (Fin d → ℕ) → EvR (Lam d L N)) (M : Act d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N))

/-- `J̄(B, U) = I^U J(B, U)`. -/
def Jbar (b : Fin d → ℕ) (U : Finset (Lam d L N)) : EvR (Lam d L N) := bpow k I U * J b U

/-- The summand of `K_out(W)`. -/
def Rterm (W : Finset (Lam d L N)) (g : GT d L N) : EvR (Lam d L N) :=
  bpow k I (W \ (g.2 ∪ Xcal g.1)) * (Kext k M g.2 * ∏ p ∈ g.1, Jbar k I J p.1 p.2)

/-- **`K_out(W)`** (Brydges–Slade (D.13)). -/
def Kout (W : Finset (Lam d L N)) : EvR (Lam d L N) :=
  ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W), Rterm k I M J W g

theorem Xcal_subset_Bbox {𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))} (h : 𝒳 ⊆ pairsU k) :
    Xcal 𝒳 ⊆ Bbox k 𝒳 := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 hx
  obtain ⟨hb, hs, hbs⟩ := mem_pairsU.1 (h hp)
  exact mem_biUnion.2 ⟨p, hp, subset_nbhd_of_small hs hbs (mem_blockIdx.1 hb) hxp⟩

theorem isPolymer_Bbox (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    IsPolymer k (Bbox k 𝒳) := by
  intro x y h hx
  obtain ⟨p, hp, hx⟩ := mem_biUnion.1 hx
  exact mem_biUnion.2 ⟨p, hp, isPolymer_nbhd k _ x y h hx⟩

theorem bpow_sdiff_mul {A B : Finset (Lam d L N)} (hA : IsPolymer k A) (hB : IsPolymer k B)
    (hBA : B ⊆ A) :
    bpow k I (univ \ A) * bpow k I (A \ B) = bpow k I (univ \ B) := by
  rw [← bpow_union k I (IsPolymer.sdiff (isPolymer_univ k) hA) (IsPolymer.sdiff hA hB)
    (disjoint_sdiff_self_left.mono_right sdiff_subset)]
  congr 1
  ext x; simp only [mem_union, mem_sdiff, mem_univ, true_and]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact fun hB' => h (hBA hB')
    · exact h
  · intro h
    by_cases hx : x ∈ A
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl hx

variable {k I M J}

/-- **The identity (D.4).** -/
theorem reblock_ZVK (hJs : ∀ b c, ¬ IsSmall k c → J b c = 0) (Kin : Act d L N)
    (hKin : ∀ c, IsConn k c → Kin c = M c + ∑ b ∈ blocks k c, Jbar k I J b c) :
    ∑ U ∈ Pj k univ, bpow k I (univ \ U) * Kext k Kin U =
      ∑ W ∈ Pj k univ, bpow k I (univ \ W) * Kout k I M J W := by
  classical
  -- expand each `K_in^U`
  have hU : ∀ U ∈ Pj (L := L) (N := N) k univ, Kext k Kin U =
      ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Xcal g.1 = U),
        Kext k M g.2 * ∏ p ∈ g.1, Jbar k I J p.1 p.2 := by
    intro U hU'
    have hUp := (mem_Pj.1 hU').2
    simp only [Kext]
    rw [← prod_comp_add_eq_sum_G0 k hUp M (fun p => Jbar k I J p.1 p.2)]
    refine prod_congr rfl fun c hc => ?_
    rw [hKin c (isConn_of_mem_comp hUp hc)]
    congr 1
    by_cases hs : IsSmall k c
    · rw [tSmall, if_pos hs]
    · rw [tSmall, if_neg hs, sum_empty]
      exact sum_eq_zero fun b _ => by rw [Jbar, hJs b c hs, mul_zero]
  have e1 : ∀ U ∈ Pj (L := L) (N := N) k univ, bpow k I (univ \ U) * Kext k Kin U =
      ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Xcal g.1 = U),
        bpow k I (univ \ (g.2 ∪ Xcal g.1)) * (Kext k M g.2 * ∏ p ∈ g.1, Jbar k I J p.1 p.2) := by
    intro U hU'
    rw [hU U hU', mul_sum]
    refine sum_congr rfl fun g hg => ?_
    rw [(mem_filter.1 hg).2]
  have e2 : ∀ W ∈ Pj (L := L) (N := N) k univ, bpow k I (univ \ W) * Kout k I M J W =
      ∑ g ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W),
        bpow k I (univ \ (g.2 ∪ Bbox k g.1)) * Rterm k I M J (g.2 ∪ Bbox k g.1) g := by
    intro W _
    rw [Kout, mul_sum]
    refine sum_congr rfl fun g hg => ?_
    rw [(mem_filter.1 hg).2]
  have hmem : ∀ g ∈ G0 (d := d) (L := L) (N := N) k, g.2 ∪ Xcal g.1 ∈ Pj (L := L) (N := N) k univ ∧
      g.2 ∪ Bbox k g.1 ∈ Pj (L := L) (N := N) k univ := fun g hg => by
    obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 hg
    exact ⟨mem_Pj.2 ⟨subset_univ _, IsPolymer.union h1 (isPolymer_Xcal h2)⟩,
      mem_Pj.2 ⟨subset_univ _, IsPolymer.union h1 (isPolymer_Bbox k _)⟩⟩
  rw [sum_congr rfl e1, sum_congr rfl e2,
    sum_fiberwise_of_maps_to (fun g hg => (hmem g hg).1),
    sum_fiberwise_of_maps_to (fun g hg => (hmem g hg).2)]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 hg
  rw [Rterm, ← bpow_sdiff_mul k I (IsPolymer.union h1 (isPolymer_Bbox k _))
    (IsPolymer.union h1 (isPolymer_Xcal h2))
    (union_subset_union subset_rfl (Xcal_subset_Bbox k h2))]
  ring

end Reblock

/-! ### Factorisation of `K_out` -/

section Fact

variable {k : ℕ} {W₁ W₂ : Finset (Lam d L N)} (hW₁ : IsPolymer k W₁) (hW₂ : IsPolymer k W₂)
  (h : ¬ Touch W₁ W₂)
include hW₁ hW₂ h

/-- `B^□` lies on one side. -/
theorem nbhd_side {b : Fin d → ℕ} (hsub : nbhd k (blockSet (L := L) (N := N) k b) ⊆ W₁ ∪ W₂)
    {x : Lam d L N} (hx : x ∈ blockSet k b) (hx₁ : x ∈ W₁) :
    nbhd k (blockSet (L := L) (N := N) k b) ⊆ W₁ := by
  classical
  intro y hy
  have hy' := hy
  simp only [nbhd, mem_filter, mem_univ, true_and] at hy'
  obtain ⟨S, hS, hyS, c, hc, hcS⟩ := hy'
  have hSn : S ⊆ nbhd k (blockSet (L := L) (N := N) k b) := fun z hz => by
    simp only [nbhd, mem_filter, mem_univ, true_and]
    exact ⟨S, hS, hz, c, hc, hcS⟩
  have hcb : c = b := by
    obtain ⟨z, hz, rfl⟩ := mem_blocks.1 hc
    exact mem_blockSet.1 hz
  subst hcb
  exact subset_of_conn_aux ⟨hS.1, hS.2.1⟩ hW₁ hW₂ h (hSn.trans hsub) (hcS hx) hx₁ hyS

/-- Splitting an element of `𝒢₀` for `W₁ ∪ W₂`. -/
def gsplit0 (k : ℕ) (W₁ W₂ : Finset (Lam d L N)) (g : GT d L N) : GT d L N × GT d L N :=
  ((g.1.filter (fun p => blockSet k p.1 ⊆ W₁), g.2 ∩ W₁),
    (g.1.filter (fun p => ¬ blockSet k p.1 ⊆ W₁), g.2 ∩ W₂))

omit hW₁ hW₂ h in
theorem Bbox_subset {𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))} {W : Finset (Lam d L N)}
    (h𝒳 : Bbox k 𝒳 ⊆ W) {p : (Fin d → ℕ) × Finset (Lam d L N)} (hp : p ∈ 𝒳) :
    nbhd k (blockSet (L := L) (N := N) k p.1) ⊆ W := fun y hy =>
  h𝒳 (mem_biUnion.2 ⟨p, hp, hy⟩)

omit hW₁ hW₂ h in
theorem pair_sub_nbhd {p : (Fin d → ℕ) × Finset (Lam d L N)} (hp : p ∈ pairsU k) :
    blockSet (L := L) (N := N) k p.1 ⊆ nbhd k (blockSet k p.1) ∧
      p.2 ⊆ nbhd k (blockSet (L := L) (N := N) k p.1) := by
  obtain ⟨hb, hs, hbs⟩ := mem_pairsU.1 hp
  exact ⟨hbs.trans (subset_nbhd_of_small hs hbs (mem_blockIdx.1 hb)),
    subset_nbhd_of_small hs hbs (mem_blockIdx.1 hb)⟩

theorem gsplit0_mem {g : GT d L N} (hg : g ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁ ∪ W₂)) :
    (gsplit0 k W₁ W₂ g).1 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁) ∧
      (gsplit0 k W₁ W₂ g).2 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₂) := by
  classical
  obtain ⟨hg0, hgW⟩ := mem_filter.1 hg
  obtain ⟨h1, h2, h3, h4, h5⟩ := (mem_G0 k).1 hg0
  have hD := disjoint_of_not_touch h
  have hB : Bbox k g.1 ⊆ W₁ ∪ W₂ := hgW ▸ subset_union_right
  have hg2 : g.2 ⊆ W₁ ∪ W₂ := hgW ▸ subset_union_left
  have side1 : ∀ p ∈ g.1, blockSet k p.1 ⊆ W₁ → nbhd k (blockSet (L := L) (N := N) k p.1) ⊆ W₁ := by
    intro p hp hs
    obtain ⟨x, hx⟩ := mem_blockIdx.1 (mem_pairsU.1 (h2 hp)).1
    exact nbhd_side hW₁ hW₂ h (Bbox_subset hB hp) hx (hs hx)
  have side2 : ∀ p ∈ g.1, ¬ blockSet k p.1 ⊆ W₁ → nbhd k (blockSet (L := L) (N := N) k p.1) ⊆ W₂ := by
    intro p hp hs
    obtain ⟨x, hx, hx1⟩ := not_subset.1 hs
    have hx2 : x ∈ W₂ := (mem_union.1 ((pair_sub_nbhd (h2 hp)).1.trans (Bbox_subset hB hp) hx)).resolve_left hx1
    exact nbhd_side hW₂ hW₁ (fun t => h (touch_symm t)) (by rw [union_comm]; exact Bbox_subset hB hp)
      hx hx2
  set A₁ := g.1.filter (fun p => blockSet k p.1 ⊆ W₁)
  set A₂ := g.1.filter (fun p => ¬ blockSet k p.1 ⊆ W₁)
  have hA₁ : Bbox k A₁ ⊆ W₁ := biUnion_subset.2 fun p hp =>
    side1 p (mem_filter.1 hp).1 (mem_filter.1 hp).2
  have hA₂ : Bbox k A₂ ⊆ W₂ := biUnion_subset.2 fun p hp =>
    side2 p (mem_filter.1 hp).1 (mem_filter.1 hp).2
  have hunion : (g.2 ∩ W₁ ∪ Bbox k A₁) ∪ (g.2 ∩ W₂ ∪ Bbox k A₂) = W₁ ∪ W₂ := by
    rw [union_union_union_comm, ← inter_union_distrib_left, inter_eq_left.2 hg2, ← Bbox_union,
      filter_union_filter_not_eq, hgW]
  have e₁ : g.2 ∩ W₁ ∪ Bbox k A₁ = W₁ :=
    eq_left_of_union_eq (union_subset inter_subset_right hA₁)
      (union_subset inter_subset_right hA₂) hD hunion
  have e₂ : g.2 ∩ W₂ ∪ Bbox k A₂ = W₂ :=
    eq_left_of_union_eq (union_subset inter_subset_right hA₂)
      (union_subset inter_subset_right hA₁) hD.symm (by rw [union_comm, hunion, union_comm])
  refine ⟨mem_filter.2 ⟨(mem_G0 k).2 ⟨IsPolymer.inter h1 hW₁, (filter_subset _ _).trans h2,
    fun p hp q hq => h3 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    fun p hp q hq => h4 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    not_touch_mono h5 (Xcal_mono (filter_subset _ _)) inter_subset_left⟩, e₁⟩,
    mem_filter.2 ⟨(mem_G0 k).2 ⟨IsPolymer.inter h1 hW₂, (filter_subset _ _).trans h2,
    fun p hp q hq => h3 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    fun p hp q hq => h4 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    not_touch_mono h5 (Xcal_mono (filter_subset _ _)) inter_subset_left⟩, e₂⟩⟩

omit hW₁ hW₂ h in
/-- Facts on the parts. -/
theorem G0W_facts {W : Finset (Lam d L N)} {g : GT d L N}
    (hg : g ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W)) :
    g.2 ⊆ W ∧ Xcal g.1 ⊆ W ∧ ∀ p ∈ g.1, blockSet (L := L) (N := N) k p.1 ⊆ W ∧ p.2 ⊆ W := by
  obtain ⟨hg0, hgW⟩ := mem_filter.1 hg
  obtain ⟨-, h2, -, -, -⟩ := (mem_G0 k).1 hg0
  have hB : Bbox k g.1 ⊆ W := hgW ▸ subset_union_right
  refine ⟨hgW ▸ subset_union_left, (Xcal_subset_Bbox k h2).trans hB, fun p hp =>
    ⟨(pair_sub_nbhd (h2 hp)).1.trans (Bbox_subset hB hp),
      (pair_sub_nbhd (h2 hp)).2.trans (Bbox_subset hB hp)⟩⟩

theorem gjoin0_mem {x : GT d L N × GT d L N}
    (h₁ : x.1 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁))
    (h₂ : x.2 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₂)) :
    gjoin x ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁ ∪ W₂) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := (mem_G0 k).1 (mem_filter.1 h₁).1
  obtain ⟨b1, b2, b3, b4, b5⟩ := (mem_G0 k).1 (mem_filter.1 h₂).1
  obtain ⟨fa2, fa3, fa4⟩ := G0W_facts h₁
  obtain ⟨fb2, fb3, fb4⟩ := G0W_facts h₂
  have hD := disjoint_of_not_touch h
  have cross : ∀ p ∈ x.1.1, ∀ q ∈ x.2.1, p.2 ≠ q.2 ∧ ¬ Touch p.2 q.2 ∧ ¬ Touch q.2 p.2 := by
    intro p hp q hq
    refine ⟨fun e => ?_, not_touch_mono h (fa4 p hp).2 (fb4 q hq).2,
      not_touch_mono (fun t => h (touch_symm t)) (fb4 q hq).2 (fa4 p hp).2⟩
    obtain ⟨z, hz⟩ := (nonempty_of_mem_pairsU (a2 hp)).mono (mem_pairsU.1 (a2 hp)).2.2
    exact Finset.disjoint_left.1 hD ((fa4 p hp).2 hz) ((fb4 q hq).2 (e ▸ hz))
  refine mem_filter.2 ⟨(mem_G0 k).2 ⟨IsPolymer.union a1 b1, union_subset a2 b2, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp q hq e
    rcases mem_union.1 hp with hp | hp <;> rcases mem_union.1 hq with hq | hq
    · exact a3 p hp q hq e
    · exact absurd e (cross p hp q hq).1
    · exact absurd e.symm (cross q hq p hp).1
    · exact b3 p hp q hq e
  · intro p hp q hq e
    rcases mem_union.1 hp with hp | hp <;> rcases mem_union.1 hq with hq | hq
    · exact a4 p hp q hq e
    · exact (cross p hp q hq).2.1
    · exact (cross q hq p hp).2.2
    · exact b4 p hp q hq e
  · rintro ⟨a, ha, c, hc, hac⟩
    simp only [gjoin] at ha hc
    rw [Xcal_union] at ha
    rcases mem_union.1 ha with ha | ha <;> rcases mem_union.1 hc with hc | hc
    · exact a5 ⟨a, ha, c, hc, hac⟩
    · exact h ⟨a, fa3 ha, c, fb2 hc, hac⟩
    · exact h ⟨c, fa2 hc, a, fb3 ha, by rwa [supNorm_sub_comm]⟩
    · exact b5 ⟨a, ha, c, hc, hac⟩
  · show x.1.2 ∪ x.2.2 ∪ Bbox k (x.1.1 ∪ x.2.1) = W₁ ∪ W₂
    rw [Bbox_union, union_union_union_comm, (mem_filter.1 h₁).2, (mem_filter.1 h₂).2]

theorem gsplit0_gjoin {x : GT d L N × GT d L N}
    (h₁ : x.1 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁))
    (h₂ : x.2 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₂)) :
    gsplit0 k W₁ W₂ (gjoin x) = x := by
  obtain ⟨fa2, -, fa4⟩ := G0W_facts h₁
  obtain ⟨fb2, -, fb4⟩ := G0W_facts h₂
  obtain ⟨-, b2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 h₂).1
  have hD := disjoint_of_not_touch h
  have hn : ∀ q ∈ x.2.1, ¬ blockSet k q.1 ⊆ W₁ := fun q hq hs => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (b2 hq)
    exact Finset.disjoint_left.1 hD (hs hz) ((fb4 q hq).1 hz)
  have e1 : (x.1.2 ∪ x.2.2) ∩ W₁ = x.1.2 := by
    rw [union_inter_distrib_right, inter_eq_left.2 fa2,
      disjoint_iff_inter_eq_empty.1 (hD.symm.mono_left fb2), union_empty]
  have e2 : (x.1.2 ∪ x.2.2) ∩ W₂ = x.2.2 := by
    rw [union_inter_distrib_right, inter_eq_left.2 fb2,
      disjoint_iff_inter_eq_empty.1 (hD.mono_left fa2), empty_union]
  simp only [gsplit0, gjoin, filter_union, e1, e2]
  rw [filter_true_of_mem fun p hp => (fa4 p hp).1, filter_false_of_mem hn, union_empty,
    filter_false_of_mem fun p hp hs => hs (fa4 p hp).1,
    filter_true_of_mem hn, empty_union]

omit hW₁ hW₂ h in
theorem gjoin_gsplit0 {g : GT d L N}
    (hg : g ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁ ∪ W₂)) :
    gjoin (gsplit0 k W₁ W₂ g) = g := by
  obtain ⟨f2, -, -⟩ := G0W_facts hg
  simp only [gsplit0, gjoin]
  rw [filter_union_filter_not_eq, ← inter_union_distrib_left, inter_eq_left.2 f2]

variable (I M J) in
theorem Rterm_gjoin {x : GT d L N × GT d L N}
    (h₁ : x.1 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₁))
    (h₂ : x.2 ∈ (G0 k).filter (fun g => g.2 ∪ Bbox k g.1 = W₂)) :
    Rterm k I M J (W₁ ∪ W₂) (gjoin x) = Rterm k I M J W₁ x.1 * Rterm k I M J W₂ x.2 := by
  obtain ⟨a1, a2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 h₁).1
  obtain ⟨b1, b2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 h₂).1
  obtain ⟨fa2, fa3, fa4⟩ := G0W_facts h₁
  obtain ⟨fb2, fb3, fb4⟩ := G0W_facts h₂
  have hD := disjoint_of_not_touch h
  have e1 : (W₁ ∪ W₂) \ (x.1.2 ∪ x.2.2 ∪ Xcal (x.1.1 ∪ x.2.1)) =
      (W₁ \ (x.1.2 ∪ Xcal x.1.1)) ∪ (W₂ \ (x.2.2 ∪ Xcal x.2.1)) := by
    rw [Xcal_union]
    ext z
    have i1 := @fa2 z
    have i2 := @fa3 z
    have i3 := @fb2 z
    have i4 := @fb3 z
    have i5 : z ∈ W₁ → z ∉ W₂ := fun hz => Finset.disjoint_left.1 hD hz
    simp only [mem_union, mem_sdiff]
    exact prop_aux i1 i2 i3 i4 i5
  have hI := bpow_union k I (IsPolymer.sdiff hW₁ (IsPolymer.union a1 (isPolymer_Xcal a2)))
    (IsPolymer.sdiff hW₂ (IsPolymer.union b1 (isPolymer_Xcal b2)))
    (hD.mono sdiff_subset sdiff_subset)
  have hdisj : Disjoint x.1.1 x.2.1 := Finset.disjoint_left.2 fun p hp hq => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (a2 hp)
    exact Finset.disjoint_left.1 hD ((fa4 p hp).1 hz) ((fb4 p hq).1 hz)
  simp only [Rterm, gjoin]
  rw [e1, hI, Kext_union M a1 b1 (not_touch_mono h fa2 fb2), prod_union hdisj]
  ring

variable (I M J) in
/-- **Factorisation of `K_out`.** -/
theorem Kout_union : Kout k I M J (W₁ ∪ W₂) = Kout k I M J W₁ * Kout k I M J W₂ := by
  rw [Kout, Kout, Kout, sum_mul_sum, ← sum_product']
  symm
  refine sum_nbij' gjoin (gsplit0 k W₁ W₂) (fun x hx => ?_) (fun g hg => ?_) (fun x hx => ?_)
    (fun g hg => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gjoin0_mem hW₁ hW₂ h h1 h2
  · exact mem_product.2 (gsplit0_mem hW₁ hW₂ h hg)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gsplit0_gjoin hW₁ hW₂ h h1 h2
  · exact gjoin_gsplit0 hg
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact (Rterm_gjoin hW₁ hW₂ h I M J h1 h2).symm

end Fact

end

end Step2
