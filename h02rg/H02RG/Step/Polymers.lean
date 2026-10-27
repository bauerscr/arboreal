import Step.PolymersAux

/-!
# Polymer combinatorics (Section `sec:polymers`, Lemma `lem:comb1`)

Basic facts on `j`-polymers, their connected components and closures, the combinatorial
Lemma `lem:comb1` (`comb1`, `comb2`), and counting bounds.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD PolyAux

variable {d L N : ℕ} [NeZero L]

/-! ### Auxiliary facts -/

theorem touch_symm {X Y : Finset (Lam d L N)} (h : Touch X Y) : Touch Y X := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨y, hy, x, hx, by rwa [supNorm_sub_comm]⟩

theorem touch_mono {X X' Y Y' : Finset (Lam d L N)} (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : Touch X Y) : Touch X' Y' := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨x, hX hx, y, hY hy, hxy⟩

theorem mem_of_blk_mem {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) {x : Lam d L N}
    (h : blk j x ∈ blocks j X) : x ∈ X := by
  obtain ⟨y, hy, e⟩ := mem_image.1 h
  exact hX y x e hy

theorem blockSet_subset {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) {b : Fin d → ℕ}
    (hb : b ∈ blocks j X) : blockSet j b ⊆ X := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hb
  exact hX y z (mem_blockSet.1 hz).symm hy

theorem mem_blocks_of_nonempty {j : ℕ} {b : Fin d → ℕ}
    (h : (blockSet (L := L) (N := N) j b).Nonempty) {X : Finset (Lam d L N)}
    (hsub : blockSet j b ⊆ X) : b ∈ blocks j X := by
  obtain ⟨x, hx⟩ := h
  rw [← mem_blockSet.1 hx]
  exact blk_mem_blocks (hsub hx)

/-- Touching of blocks. -/
def TB (j : ℕ) (b b' : Fin d → ℕ) : Prop := Touch (blockSet (L := L) (N := N) j b) (blockSet j b')

theorem tb_symm {j : ℕ} : Symmetric (TB (d := d) (L := L) (N := N) j) := fun _ _ h => touch_symm h

theorem blockAdj_eq {j : ℕ} {X : Finset (Lam d L N)} :
    BlockAdj j X = restr (blocks j X) (TB (L := L) (N := N) j) := rfl

theorem blockAdj_symm {j : ℕ} {X : Finset (Lam d L N)} : Symmetric (BlockAdj j X) := by
  rw [blockAdj_eq]; exact restr_symm tb_symm

theorem blockAdj_mono {j : ℕ} {X Y : Finset (Lam d L N)} (h : Y ⊆ X) {b b' : Fin d → ℕ}
    (hr : Relation.ReflTransGen (BlockAdj j Y) b b') : Relation.ReflTransGen (BlockAdj j X) b b' :=
  hr.mono fun _ _ huv => ⟨image_subset_image h huv.1, image_subset_image h huv.2.1, huv.2.2⟩

theorem conn_of_reach {α : Type*} {R : α → α → Prop} (hR : Symmetric R) {C K : Finset α} {u : α}
    (hK : ∀ z, z ∈ K ↔ z ∈ C ∧ Relation.ReflTransGen (restr C R) u z) : Conn R K := by
  have key : ∀ z, Relation.ReflTransGen (restr C R) u z →
      Relation.ReflTransGen (restr K R) u z := by
    intro z hz
    induction hz with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c e hc hce ih =>
      exact ih.tail ⟨(hK c).2 ⟨hce.1, hc⟩, (hK e).2 ⟨hce.2.1, hc.tail hce⟩, hce.2.2⟩
  intro z hz z' hz'
  exact (Relation.ReflTransGen.symmetric (restr_symm hR) (key z ((hK z).1 hz).2)).trans
    (key z' ((hK z').1 hz').2)

/-! ### Polymers -/

theorem mem_Pj {j : ℕ} {W Y : Finset (Lam d L N)} : Y ∈ Pj j W ↔ Y ⊆ W ∧ IsPolymer j Y := by
  classical
  unfold Pj; rw [mem_filter, mem_powerset]

theorem isPolymer_empty (j : ℕ) : IsPolymer j (∅ : Finset (Lam d L N)) := by
  intro x y _ hx; simp at hx

theorem isPolymer_univ (j : ℕ) : IsPolymer j (univ : Finset (Lam d L N)) := by
  intro _ y _ _; exact mem_univ y

theorem IsPolymer.union {j : ℕ} {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : IsPolymer j Y) : IsPolymer j (X ∪ Y) := by
  intro x y h hx
  rcases mem_union.1 hx with hx | hx
  · exact mem_union_left _ (hX x y h hx)
  · exact mem_union_right _ (hY x y h hx)

theorem IsPolymer.sdiff {j : ℕ} {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : IsPolymer j Y) : IsPolymer j (X \ Y) := by
  intro x y h hx
  rw [mem_sdiff] at hx ⊢
  exact ⟨hX x y h hx.1, fun hy => hx.2 (hY y x h.symm hy)⟩

theorem IsPolymer.inter {j : ℕ} {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : IsPolymer j Y) : IsPolymer j (X ∩ Y) := by
  intro x y h hx
  rw [mem_inter] at hx ⊢
  exact ⟨hX x y h hx.1, hY x y h hx.2⟩

theorem isPolymer_blockSet (j : ℕ) (b : Fin d → ℕ) :
    IsPolymer j (blockSet (L := L) (N := N) j b) := by
  intro x y h hx
  rw [mem_blockSet] at hx ⊢
  rw [← h]; exact hx

/-- A polymer is the disjoint union of its blocks. -/
theorem biUnion_blocks {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    (blocks j X).biUnion (blockSet j) = X := by
  ext x
  rw [mem_biUnion]
  constructor
  · rintro ⟨b, hb, hx⟩; exact blockSet_subset hX hb hx
  · intro hx; exact ⟨blk j x, blk_mem_blocks hx, mem_blockSet_blk j x⟩

theorem blocks_union (j : ℕ) (X Y : Finset (Lam d L N)) :
    blocks j (X ∪ Y) = blocks j X ∪ blocks j Y := by
  unfold blocks; exact image_union _ _

theorem blocks_sdiff {j : ℕ} {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : IsPolymer j Y) : blocks j (X \ Y) = blocks j X \ blocks j Y := by
  ext b
  rw [mem_sdiff]
  constructor
  · intro hb
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
    rw [mem_sdiff] at hx
    exact ⟨blk_mem_blocks hx.1, fun h => hx.2 (mem_of_blk_mem hY h)⟩
  · rintro ⟨hb, hb'⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
    exact blk_mem_blocks (mem_sdiff.2 ⟨hx, fun h => hb' (blk_mem_blocks h)⟩)

theorem disjoint_blocks {j : ℕ} {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : IsPolymer j Y) (h : Disjoint X Y) : Disjoint (blocks j X) (blocks j Y) := by
  rw [disjoint_left]
  intro b hbX hbY
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hbX
  exact disjoint_left.1 h hx (mem_of_blk_mem hY hbY)

/-- Polymers `Y ⊆ X` correspond to subsets of the blocks of `X`. -/
theorem card_Pj {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    (Pj j X).card = 2 ^ nb j X := by
  classical
  rw [nb, ← card_powerset]
  refine card_bij' (fun Y _ => blocks j Y) (fun S _ => S.biUnion (blockSet j)) ?_ ?_ ?_ ?_
  · intro Y hY
    rw [mem_Pj] at hY
    exact mem_powerset.2 (image_subset_image hY.1)
  · intro S hS
    rw [mem_powerset] at hS
    rw [mem_Pj]
    constructor
    · intro z hz
      obtain ⟨b, hb, hz⟩ := mem_biUnion.1 hz
      exact blockSet_subset hX (hS hb) hz
    · intro x y h hx
      obtain ⟨b, hb, hx⟩ := mem_biUnion.1 hx
      exact mem_biUnion.2 ⟨b, hb, (isPolymer_blockSet j b) x y h hx⟩
  · intro Y hY
    exact biUnion_blocks (mem_Pj.1 hY).2
  · intro S hS
    rw [mem_powerset] at hS
    ext b
    constructor
    · intro hb
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hb
      obtain ⟨b', hb', hz⟩ := mem_biUnion.1 hz
      rw [mem_blockSet.1 hz]; exact hb'
    · intro hb
      obtain ⟨x, hx, e⟩ := mem_image.1 (hS hb)
      exact mem_image.2 ⟨x, mem_biUnion.2 ⟨b, hb, mem_blockSet.2 e⟩, e⟩

/-! ### Connected components -/

theorem mem_blocks_compOf {j : ℕ} {X : Finset (Lam d L N)} {b c : Fin d → ℕ} :
    c ∈ blocks j (compOf j X b) ↔ c ∈ blocks j X ∧ Relation.ReflTransGen (BlockAdj j X) b c := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_image.1 h
    have := mem_filter.1 hx
    exact ⟨blk_mem_blocks this.1, this.2⟩
  · rintro ⟨hc, hr⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    exact blk_mem_blocks (mem_filter.2 ⟨hx, hr⟩)

theorem isPolymer_compOf {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (b : Fin d → ℕ) : IsPolymer j (compOf j X b) := by
  classical
  intro x y h hx
  have := mem_filter.1 hx
  exact mem_filter.2 ⟨hX x y h this.1, by rw [← h]; exact this.2⟩

theorem isConn_compOf {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) {b : Fin d → ℕ}
    (hb : b ∈ blocks j X) : IsConn j (compOf j X b) := by
  classical
  refine ⟨isPolymer_compOf hX b, ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
    exact ⟨x, mem_filter.2 ⟨hx, Relation.ReflTransGen.refl⟩⟩
  · exact conn_of_reach (R := TB j) tb_symm (C := blocks j X) (u := b)
      (fun z => mem_blocks_compOf)

theorem compOf_eq_of_rtg {j : ℕ} {X : Finset (Lam d L N)} {b c : Fin d → ℕ}
    (h : Relation.ReflTransGen (BlockAdj j X) b c) : compOf j X b = compOf j X c := by
  classical
  have h' := Relation.ReflTransGen.symmetric blockAdj_symm h
  ext x
  simp only [compOf, mem_filter]
  constructor
  · rintro ⟨hx, hr⟩; exact ⟨hx, h'.trans hr⟩
  · rintro ⟨hx, hr⟩; exact ⟨hx, h.trans hr⟩

theorem isConn_of_mem_comp {j : ℕ} {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : Y ∈ Comp j X) : IsConn j Y := by
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hY
  exact isConn_compOf hX hb

theorem subset_of_mem_comp {j : ℕ} {X Y : Finset (Lam d L N)} (hY : Y ∈ Comp j X) : Y ⊆ X := by
  classical
  obtain ⟨b, _, rfl⟩ := mem_image.1 hY
  exact filter_subset _ _

theorem biUnion_comp {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    (Comp j X).biUnion id = X := by
  classical
  ext x
  rw [mem_biUnion]
  constructor
  · rintro ⟨Y, hY, hx⟩; exact subset_of_mem_comp hY hx
  · intro hx
    exact ⟨compOf j X (blk j x), mem_image_of_mem _ (blk_mem_blocks hx),
      mem_filter.2 ⟨hx, Relation.ReflTransGen.refl⟩⟩

theorem not_touch_of_mem_comp {j : ℕ} {X Y Y' : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : Y ∈ Comp j X) (hY' : Y' ∈ Comp j X) (hne : Y ≠ Y') : ¬ Touch Y Y' := by
  classical
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hY
  obtain ⟨b', hb', rfl⟩ := mem_image.1 hY'
  rintro ⟨x, hx, y, hy, hxy⟩
  have hx' := mem_filter.1 hx
  have hy' := mem_filter.1 hy
  have hadj : BlockAdj j X (blk j x) (blk j y) :=
    ⟨blk_mem_blocks hx'.1, blk_mem_blocks hy'.1,
      ⟨x, mem_blockSet_blk j x, y, mem_blockSet_blk j y, hxy⟩⟩
  apply hne
  rw [compOf_eq_of_rtg hx'.2, compOf_eq_of_rtg (Relation.ReflTransGen.single hadj),
    ← compOf_eq_of_rtg hy'.2]

theorem comp_empty (j : ℕ) : Comp j (∅ : Finset (Lam d L N)) = ∅ := by
  simp [Comp, blocks]

/-- The components are characterised as a partition into connected, pairwise non-touching
polymers. -/
theorem comp_eq_of_partition {j : ℕ} {X : Finset (Lam d L N)} (𝒴 : Finset (Finset (Lam d L N)))
    (hconn : ∀ Y ∈ 𝒴, IsConn j Y) (htouch : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → ¬ Touch Y Y')
    (hunion : 𝒴.biUnion id = X) : Comp j X = 𝒴 := by
  classical
  have hsubX : ∀ Y ∈ 𝒴, Y ⊆ X := fun Y hY => by
    rw [← hunion]; exact subset_biUnion_of_mem id hY
  have hmemX : ∀ x ∈ X, ∃ Y ∈ 𝒴, x ∈ Y := fun x hx => by
    rw [← hunion] at hx
    obtain ⟨Y, hY, hxY⟩ := mem_biUnion.1 hx
    exact ⟨Y, hY, hxY⟩
  have key : ∀ Y ∈ 𝒴, ∀ c ∈ blocks j Y, compOf j X c = Y := by
    intro Y hY c hc
    have hYp := (hconn Y hY).1
    ext x
    simp only [compOf, mem_filter]
    constructor
    · rintro ⟨hx, hr⟩
      have : ∀ e, Relation.ReflTransGen (BlockAdj j X) c e → e ∈ blocks j Y := by
        intro e he
        induction he with
        | refl => exact hc
        | @tail u v _ huv ih =>
          obtain ⟨z, hz, hze⟩ := mem_image.1 huv.2.1
          obtain ⟨Y', hY', hzY'⟩ := hmemX z hz
          by_cases hYY : Y' = Y
          · rw [hYY] at hzY'; rw [← hze]; exact blk_mem_blocks hzY'
          · exfalso
            obtain ⟨p, hp, q, hq, hpq⟩ := huv.2.2
            apply htouch Y hY Y' hY' (Ne.symm hYY)
            refine ⟨p, blockSet_subset hYp ih hp, q, ?_, hpq⟩
            exact (hconn Y' hY').1 z q (hze.trans (mem_blockSet.1 hq).symm) hzY'
      exact mem_of_blk_mem hYp (this _ hr)
    · intro hx
      exact ⟨hsubX Y hY hx, blockAdj_mono (hsubX Y hY)
        ((hconn Y hY).2.2 c hc (blk j x) (blk_mem_blocks hx))⟩
  apply subset_antisymm
  · intro Y hY
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hY
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
    obtain ⟨Y, hY', hxY⟩ := hmemX x hx
    rw [key Y hY' _ (blk_mem_blocks hxY)]
    exact hY'
  · intro Y hY
    obtain ⟨y, hy⟩ := (hconn Y hY).2.1
    rw [← key Y hY _ (blk_mem_blocks hy)]
    exact mem_image_of_mem _ (image_subset_image (hsubX Y hY) (blk_mem_blocks hy))

theorem comp_of_isConn {j : ℕ} {X : Finset (Lam d L N)} (hX : IsConn j X) : Comp j X = {X} := by
  apply comp_eq_of_partition
  · intro Y hY; rw [mem_singleton.1 hY]; exact hX
  · intro Y hY Y' hY' hne
    exact absurd ((mem_singleton.1 hY).trans (mem_singleton.1 hY').symm) hne
  · simp

theorem comp_union {j : ℕ} {X Y : Finset (Lam d L N)} (hX : IsPolymer j X) (hY : IsPolymer j Y)
    (h : ¬ Touch X Y) : Comp j (X ∪ Y) = Comp j X ∪ Comp j Y := by
  apply comp_eq_of_partition
  · intro Z hZ
    rcases mem_union.1 hZ with hZ | hZ
    · exact isConn_of_mem_comp hX hZ
    · exact isConn_of_mem_comp hY hZ
  · intro Z hZ Z' hZ' hne
    rcases mem_union.1 hZ with hZ | hZ <;> rcases mem_union.1 hZ' with hZ' | hZ'
    · exact not_touch_of_mem_comp hX hZ hZ' hne
    · exact fun ht => h (touch_mono (subset_of_mem_comp hZ) (subset_of_mem_comp hZ') ht)
    · exact fun ht =>
        h (touch_symm (touch_mono (subset_of_mem_comp hZ) (subset_of_mem_comp hZ') ht))
    · exact not_touch_of_mem_comp hY hZ hZ' hne
  · rw [union_biUnion, biUnion_comp hX, biUnion_comp hY]

theorem card_comp_le {j : ℕ} {X : Finset (Lam d L N)} : (Comp j X).card ≤ nb j X :=
  card_image_le

theorem disjoint_of_not_touch {X Y : Finset (Lam d L N)} (h : ¬ Touch X Y) : Disjoint X Y := by
  rw [disjoint_left]
  intro x hx hy
  exact h ⟨x, hx, x, hy, by rw [sub_self, supNorm_zero]; exact Nat.zero_le 1⟩

/-! ### Closure -/

theorem blk_succ (j : ℕ) (x : Lam d L N) : blk (j + 1) x = par L (blk j x) := by
  funext i
  simp only [blk, par]
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

theorem mem_clo {j : ℕ} {X : Finset (Lam d L N)} {x : Lam d L N} :
    x ∈ clo j X ↔ blk (j + 1) x ∈ blocks (j + 1) X := by
  classical
  simp [clo]

theorem blocks_succ (j : ℕ) (Y : Finset (Lam d L N)) :
    blocks (j + 1) Y = (blocks j Y).image (par L) := by
  unfold blocks
  rw [image_image]
  congr 1
  funext x
  exact blk_succ j x

theorem isPolymer_clo (j : ℕ) (X : Finset (Lam d L N)) : IsPolymer (j + 1) (clo j X) := by
  intro x y h hx
  rw [mem_clo] at hx ⊢
  rw [← h]; exact hx

theorem subset_clo (j : ℕ) (X : Finset (Lam d L N)) : X ⊆ clo j X := by
  intro x hx
  exact mem_clo.2 (blk_mem_blocks hx)

theorem blocks_clo (j : ℕ) (X : Finset (Lam d L N)) : blocks (j + 1) (clo j X) = blocks (j + 1) X := by
  ext c
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_image.1 h
    exact mem_clo.1 hx
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_image.1 h
    exact blk_mem_blocks (subset_clo j X hx)

theorem clo_union (j : ℕ) (X Y : Finset (Lam d L N)) : clo j (X ∪ Y) = clo j X ∪ clo j Y := by
  ext x
  rw [mem_union, mem_clo, mem_clo, mem_clo, blocks_union, mem_union]

theorem clo_mono {j : ℕ} {X Y : Finset (Lam d L N)} (h : X ⊆ Y) : clo j X ⊆ clo j Y := by
  intro x hx
  rw [mem_clo] at hx ⊢
  exact image_subset_image h hx

theorem clo_empty (j : ℕ) : clo j (∅ : Finset (Lam d L N)) = ∅ := by
  ext x
  simp [mem_clo, blocks]

theorem clo_eq_self {j : ℕ} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) : clo j U = U := by
  ext x
  rw [mem_clo]
  exact ⟨mem_of_blk_mem hU, blk_mem_blocks⟩

/-- The smallest `(j+1)`-polymer containing `X`. -/
theorem clo_subset {j : ℕ} {X U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) (h : X ⊆ U) :
    clo j X ⊆ U := by
  rw [← clo_eq_self hU]; exact clo_mono h

/-- `(j+1)`-polymers are `j`-polymers. -/
theorem IsPolymer.of_succ {j : ℕ} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    IsPolymer j U := by
  intro x y h hx
  apply hU x y _ hx
  rw [blk_succ, blk_succ, h]

/-- `|𝓑_{j+1}(X̄)| ≤ |𝓑_j(X)|`. -/
theorem nb_clo_le (j : ℕ) (X : Finset (Lam d L N)) : nb (j + 1) (clo j X) ≤ nb j X := by
  rw [nb, nb, blocks_clo, blocks_succ]
  exact card_image_le

/-- A `(j+1)`-block contains at most `L^d` blocks of scale `j`. -/
theorem nb_le_of_succ {j : ℕ} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    nb j U ≤ L ^ d * nb (j + 1) U := by
  rw [nb, nb, blocks_succ]
  refine card_le_mul_card_image _ _ fun c _ => ?_
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  calc _ ≤ (univ : Finset (Fin d → Fin L)).card := by
        refine card_le_card_of_injOn (fun b i => ⟨b i % L, Nat.mod_lt _ hL⟩)
          (by intro a _; exact mem_univ _) ?_
        intro b hb b' hb' e
        have h1 := (mem_filter.1 (mem_coe.1 hb)).2
        have h2 := (mem_filter.1 (mem_coe.1 hb')).2
        funext i
        have e2 := congrFun e i
        simp only [Fin.mk.injEq] at e2
        have e1 := congrFun (h1.trans h2.symm) i
        simp only [par] at e1
        rw [← Nat.div_add_mod (b i) L, ← Nat.div_add_mod (b' i) L, e1, e2]
    _ = L ^ d := by simp

theorem isConn_clo {j : ℕ} {X : Finset (Lam d L N)} (hX : IsConn j X) :
    IsConn (j + 1) (clo j X) := by
  refine ⟨isPolymer_clo j X, ⟨?_, ?_⟩⟩
  · obtain ⟨x, hx⟩ := hX.2.1
    exact ⟨x, subset_clo j X hx⟩
  · rw [blocks_clo, blocks_succ]
    intro c hc c' hc'
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hc
    obtain ⟨b', hb', rfl⟩ := mem_image.1 hc'
    refine Relation.ReflTransGen.lift (par L) (fun u v huv => ?_) (hX.2.2 b hb b' hb')
    refine ⟨?_, ?_, ?_⟩
    · rw [blocks_clo, blocks_succ]; exact mem_image_of_mem _ huv.1
    · rw [blocks_clo, blocks_succ]; exact mem_image_of_mem _ huv.2.1
    · obtain ⟨p, hp, q, hq, hpq⟩ := huv.2.2
      refine ⟨p, ?_, q, ?_, hpq⟩
      · rw [mem_blockSet, blk_succ, mem_blockSet.1 hp]
      · rw [mem_blockSet, blk_succ, mem_blockSet.1 hq]

theorem isSmall_clo {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X) :
    IsSmall (j + 1) (clo j X) :=
  ⟨isPolymer_clo j X, (isConn_clo ⟨hX.1, hX.2.1⟩).2, (nb_clo_le j X).trans hX.2.2⟩

theorem subset_of_conn_aux {j : ℕ} {X U₁ U₂ : Finset (Lam d L N)} (hX : IsConn j X)
    (hU₁ : IsPolymer j U₁) (hU₂ : IsPolymer j U₂) (h : ¬ Touch U₁ U₂) (hXU : X ⊆ U₁ ∪ U₂)
    {x₀ : Lam d L N} (hx₀ : x₀ ∈ X) (h₀ : x₀ ∈ U₁) : X ⊆ U₁ := by
  have key : ∀ c, Relation.ReflTransGen (BlockAdj j X) (blk j x₀) c → blockSet j c ⊆ U₁ := by
    intro c hc
    induction hc with
    | refl => intro z hz; exact hU₁ x₀ z (mem_blockSet.1 hz).symm h₀
    | @tail u v _ huv ih =>
      obtain ⟨z, hz, rfl⟩ := mem_image.1 huv.2.1
      rcases mem_union.1 (hXU hz) with hz1 | hz2
      · intro w hw; exact hU₁ z w (mem_blockSet.1 hw).symm hz1
      · exfalso
        obtain ⟨p, hp, q, hq, hpq⟩ := huv.2.2
        exact h ⟨p, ih hp, q, hU₂ z q (mem_blockSet.1 hq).symm hz2, hpq⟩
  intro x hx
  exact key _ (hX.2.2 _ (blk_mem_blocks hx₀) _ (blk_mem_blocks hx)) (mem_blockSet_blk j x)

/-! ### Block indices and adjacency -/

theorem zabs_sub_le {n : ℕ} [NeZero n] {u v : ZMod n} {R : ℕ} (h : zabs (u - v) ≤ R) :
    (v.val ≤ u.val ∧ u.val ≤ v.val + R) ∨ (u.val ≤ v.val ∧ v.val ≤ u.val + R) ∨
    v.val + n ≤ u.val + R ∨ u.val + n ≤ v.val + R := by
  unfold zabs at h
  have hu := ZMod.val_lt u
  have hv := ZMod.val_lt v
  by_cases hvu : v.val ≤ u.val
  · rw [ZMod.val_sub hvu] at h
    rcases min_le_iff.1 h with h | h <;> omega
  · have e : u - v = -(v - u) := by ring
    have hvu' : u.val ≤ v.val := by omega
    have hne : v - u ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0] at hvu
      exact hvu le_rfl
    rw [e, ZMod.neg_val, if_neg hne, ZMod.val_sub hvu'] at h
    rcases min_le_iff.1 h with h | h <;> omega

theorem div_succ_cases (a P : ℕ) : (a + 1) / P = a / P ∨ (a + 1) / P = a / P + 1 := by
  rw [Nat.succ_div]; split_ifs <;> simp

theorem pow_pred_div (hL : 0 < L) (N j : ℕ) : (L ^ N - 1) / L ^ j = L ^ (N - j) - 1 := by
  by_cases hj : j ≤ N
  · obtain ⟨k, rfl⟩ : ∃ k, N = j + k := ⟨N - j, by omega⟩
    rw [pow_add, Nat.add_sub_cancel_left]
    exact (pred_div_mod (pow_pos hL j) (pow_pos hL k)).1
  · have h1 := Nat.pow_le_pow_right hL (by omega : N ≤ j)
    have h2 := pow_pos hL N
    rw [Nat.sub_eq_zero_of_le (by omega : N ≤ j), pow_zero, Nat.div_eq_of_lt (by omega)]
    norm_num

theorem cyc_blk {j : ℕ} {x y : Lam d L N} (h : supNorm (x - y) ≤ 1) (i : Fin d) :
    cyc (L ^ (N - j)) (blk j x i) (blk j y i) := by
  have hz : zabs (co x i - co y i) ≤ 1 := (supNorm_le_iff _ _).1 h i
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have ha := ZMod.val_lt (co x i)
  have hc := ZMod.val_lt (co y i)
  have key : (co y i).val = (co x i).val ∨ (co y i).val = (co x i).val + 1 ∨
      (co x i).val = (co y i).val + 1 ∨ ((co x i).val = 0 ∧ (co y i).val = L ^ N - 1) ∨
      ((co y i).val = 0 ∧ (co x i).val = L ^ N - 1) := by
    rcases zabs_sub_le hz with h | h | h | h <;> omega
  simp only [blk]
  generalize (co x i).val = a at key ha ⊢
  generalize (co y i).val = c at key hc ⊢
  unfold cyc
  rcases key with e | e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left; rw [e]
  · subst e
    rcases div_succ_cases a (L ^ j) with h | h
    · left; exact h
    · right; left; exact h
  · subst e
    rcases div_succ_cases c (L ^ j) with h | h
    · left; exact h.symm
    · right; right; left; exact h
  · subst e1 e2
    right; right; right; left; exact ⟨by simp, pow_pred_div hL N j⟩
  · subst e1 e2
    right; right; right; right; exact ⟨by simp, pow_pred_div hL N j⟩

theorem adj_of_touch {j : ℕ} {b b' : Fin d → ℕ} (h : TB (L := L) (N := N) j b b') :
    Adj (L ^ (N - j)) b b' := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  intro i
  have := cyc_blk (j := j) hxy i
  rwa [mem_blockSet.1 hx, mem_blockSet.1 hy] at this

theorem blk_lt {j : ℕ} (hj : j ≤ N) (x : Lam d L N) (i : Fin d) : blk j x i < L ^ (N - j) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [blk]
  rw [Nat.div_lt_iff_lt_mul (pow_pos hL j), ← pow_add, Nat.sub_add_cancel hj]
  exact ZMod.val_lt _

theorem conn_blocks {j : ℕ} {X : Finset (Lam d L N)} (hX : IsConnected j X) :
    Conn (Adj (L ^ (N - j))) (blocks j X) := fun c hc c' hc' =>
  rtg_restr_mono (subset_refl _) (fun _ _ h => adj_of_touch h) (hX.2 c hc c' hc')

/-! ### Lemma `lem:comb1` -/

theorem comb1_main (hL : 2 ^ d < L) {j : ℕ} {X : Finset (Lam d L N)} (hj : j < N)
    (hX : IsConn j X) (hbig : 2 ^ d < nb j X) :
    ∃ s t : ℕ, nb j X = s + t ∧ 2 * nb (j + 1) (clo j X) ≤ 2 * s + t ∧ s ≤ 10 ^ d * t := by
  classical
  set B := blocks j X with hB
  have hBn : nb j X = B.card := rfl
  have hM : L ^ (N - j) = L * L ^ (N - j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hadj : ∀ u v, BlockAdj j X u v → Adj (L * L ^ (N - j - 1)) u v := fun u v h => by
    have := adj_of_touch h.2.2; rwa [hM] at this
  have hlt : ∀ b ∈ B, ∀ i, b i < L * L ^ (N - j - 1) := by
    intro b hb i
    obtain ⟨x, _, rfl⟩ := mem_image.1 hb
    rw [← hM]; exact blk_lt hj.le x i
  let single : (Fin d → ℕ) → Prop := fun b => ∀ b' ∈ B, par L b' = par L b → b' = b
  set S := B.filter single with hS
  set T := B.filter (fun b => ¬ single b) with hT
  have hn : nb j X = S.card + T.card := by
    rw [hBn]; exact (card_filter_add_card_filter_not _).symm
  refine ⟨S.card, T.card, hn, ?_, ?_⟩
  · have hm : nb (j + 1) (clo j X) = (B.image (par L)).card := by rw [nb, blocks_clo, blocks_succ]
    have hBST : B = S ∪ T := (filter_union_filter_not_eq _ _).symm
    have h1 : (B.image (par L)).card ≤ S.card + (T.image (par L)).card := by
      rw [hBST, image_union]
      exact (card_union_le _ _).trans (Nat.add_le_add_right card_image_le _)
    have h2 : 2 * (T.image (par L)).card ≤ T.card := by
      rw [card_eq_sum_card_image (par L) T, mul_comm, ← smul_eq_mul]
      refine card_nsmul_le_sum _ _ _ fun c hc => ?_
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hc
      have ht' := mem_filter.1 ht
      obtain ⟨b', hb', hpar, hne⟩ : ∃ b' ∈ B, par L b' = par L t ∧ b' ≠ t := by
        by_contra hcon
        push Not at hcon
        exact ht'.2 (fun b' hb' hp => hcon b' hb' hp)
      have hb'T : b' ∈ T := mem_filter.2 ⟨hb', fun hs => hne (hs t ht'.1 hpar.symm).symm⟩
      calc 2 = ({t, b'} : Finset _).card := (card_pair (Ne.symm hne)).symm
        _ ≤ _ := card_le_card (by
          intro z hz
          rcases mem_insert.1 hz with rfl | hz
          · exact mem_filter.2 ⟨ht, rfl⟩
          · rw [mem_singleton.1 hz]; exact mem_filter.2 ⟨hb'T, hpar⟩)
    omega
  · set A := Adj (d := d) (L * L ^ (N - j - 1)) with hA
    let Cl : (Fin d → ℕ) → Finset (Fin d → ℕ) := fun u =>
      S.filter (Relation.ReflTransGen (restr S A) u)
    have hClS : ∀ u, Cl u ⊆ S := fun u => filter_subset _ _
    have hCl_card : ∀ u ∈ S, (Cl u).card ≤ 2 ^ d := by
      intro u _
      refine cluster hL (Cl u) (fun b hb => hlt b (mem_filter.1 (hClS u hb)).1) ?_ ?_
      · intro b1 hb1 b2 hb2 e
        have h1 := mem_filter.1 (hClS u (mem_coe.1 hb1))
        have h2 := mem_filter.1 (hClS u (mem_coe.1 hb2))
        exact (h1.2 b2 h2.1 e.symm).symm
      · exact conn_of_reach (R := A) adj_symm (fun z => mem_filter)
    have hcover : S ⊆ T.biUnion (fun t =>
        (S.filter (fun u => u ∈ Nbr (L * L ^ (N - j - 1)) t)).biUnion Cl) := by
      intro s hs
      have hsB := (mem_filter.1 hs).1
      obtain ⟨b, hbB, hbCl⟩ : ∃ b ∈ B, b ∉ Cl s := by
        by_contra hcon
        push Not at hcon
        have h1 := card_le_card (show B ⊆ Cl s from hcon)
        have h2 := hCl_card s hs
        omega
      have hr := hX.2.2 s hsB b hbB
      obtain ⟨u, huCl, v, hvCl, huv⟩ := exists_exit (P := fun z => z ∈ Cl s) hr
        (mem_filter.2 ⟨hs, Relation.ReflTransGen.refl⟩) hbCl
      have huS := hClS s huCl
      have hvT : v ∈ T := by
        refine mem_filter.2 ⟨huv.2.1, fun hvs => hvCl ?_⟩
        exact mem_filter.2 ⟨mem_filter.2 ⟨huv.2.1, hvs⟩,
          (mem_filter.1 huCl).2.tail ⟨huS, mem_filter.2 ⟨huv.2.1, hvs⟩, hadj u v huv⟩⟩
      refine mem_biUnion.2 ⟨v, hvT, mem_biUnion.2 ⟨u, mem_filter.2 ⟨huS,
        mem_Nbr (adj_symm (hadj u v huv))⟩, ?_⟩⟩
      exact mem_filter.2 ⟨hs, Relation.ReflTransGen.symmetric (restr_symm adj_symm)
        (mem_filter.1 huCl).2⟩
    calc S.card ≤ _ := card_le_card hcover
      _ ≤ ∑ t ∈ T, ((S.filter (fun u => u ∈ Nbr (L * L ^ (N - j - 1)) t)).biUnion Cl).card :=
          card_biUnion_le
      _ ≤ ∑ _t ∈ T, 10 ^ d := sum_le_sum fun t _ => by
          calc _ ≤ ∑ u ∈ S.filter (fun u => u ∈ Nbr (L * L ^ (N - j - 1)) t), (Cl u).card :=
                card_biUnion_le
            _ ≤ ∑ _u ∈ S.filter (fun u => u ∈ Nbr (L * L ^ (N - j - 1)) t), 2 ^ d :=
                sum_le_sum fun u hu => hCl_card u (mem_filter.1 hu).1
            _ = (S.filter (fun u => u ∈ Nbr (L * L ^ (N - j - 1)) t)).card * 2 ^ d := by
                rw [sum_const, smul_eq_mul]
            _ ≤ 5 ^ d * 2 ^ d := Nat.mul_le_mul_right _
                ((card_le_card (fun z hz => (mem_filter.1 hz).2)).trans (card_Nbr t))
            _ = 10 ^ d := by rw [← mul_pow]; norm_num
      _ = 10 ^ d * T.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **Lemma `lem:comb1`**, first part: for `L ≥ 2^d + 1` there is `η = η(d) > 0` with
`|𝓑_j(X)| ≥ (1 + 2η) |𝓑_{j+1}(X̄)|` for connected polymers `X` that are not small. -/
theorem comb1 (d : ℕ) : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ ∀ (L : ℕ) [NeZero L], 2 ^ d + 1 ≤ L →
    ∀ (N j : ℕ) (X : Finset (Lam d L N)), j < N → IsConn j X → ¬ IsSmall j X →
      (1 + 2 * η) * (nb (j + 1) (clo j X) : ℝ) ≤ nb j X := by
  have hK1 : (1 : ℝ) ≤ 10 ^ d := one_le_pow₀ (by norm_num)
  refine ⟨1 / (2 * (2 * 10 ^ d + 1)), by positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  intro L _ hL N j X hj hX hns
  have hbig : 2 ^ d < nb j X := by
    by_contra h
    push Not at h
    exact hns ⟨hX.1, hX.2, h⟩
  obtain ⟨s, t, hn, hm, hs⟩ := comb1_main (by omega) hj hX hbig
  rw [hn]
  have hm' : (2 : ℝ) * nb (j + 1) (clo j X) ≤ 2 * s + t := by exact_mod_cast hm
  have hs' : (s : ℝ) ≤ 10 ^ d * t := by exact_mod_cast hs
  push_cast
  set K : ℝ := 10 ^ d with hKdef
  set e : ℝ := 1 / (2 * (2 * K + 1)) with he
  set m : ℝ := (nb (j + 1) (clo j X) : ℝ)
  have hK0 : 0 < 2 * K + 1 := by linarith
  have he0 : 0 ≤ e := by positivity
  have h3 : e * (2 * K + 1) = 1 / 2 := by
    rw [he, div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]; ring
  have h4 : e * (2 * K + 1) * t = t / 2 := by rw [h3]; ring
  have h1 : 0 ≤ e * (K * t - s) := mul_nonneg he0 (by linarith)
  have h2 : 0 ≤ (1 + 2 * e) * (s + t / 2 - m) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem blocks_biUnion (k : ℕ) (𝒴 : Finset (Finset (Lam d L N))) :
    blocks k (𝒴.biUnion id) = 𝒴.biUnion (blocks k) := by
  unfold blocks; rw [biUnion_image]; rfl

/-- **Lemma `lem:comb1`**, second part, with the same `η`. -/
theorem comb2 (d : ℕ) : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ ∀ (L : ℕ) [NeZero L], 2 ^ d + 1 ≤ L →
    ∀ (N j : ℕ) (X : Finset (Lam d L N)), j < N → IsPolymer j X →
      (1 + 2 * η) * (nb (j + 1) (clo j X) : ℝ) ≤ nb j X + (1 + 2 * η) * 2 ^ d * (Comp j X).card ∧
      (1 + η) * (nb (j + 1) (clo j X) : ℝ) ≤
        nb j X + (1 + η) * 2 ^ (d + 1) * (Comp j X).card := by
  classical
  obtain ⟨η, hη0, hη1, h1⟩ := comb1 d
  refine ⟨η, hη0, hη1, ?_⟩
  intro L _ hL N j X hj hX
  have hcomp : ∀ Y ∈ Comp j X,
      (1 + 2 * η) * (nb (j + 1) (clo j Y) : ℝ) ≤ nb j Y + (1 + 2 * η) * 2 ^ d := by
    intro Y hY
    have hYc := isConn_of_mem_comp hX hY
    by_cases hs : IsSmall j Y
    · have h2 : (nb (j + 1) (clo j Y) : ℝ) ≤ 2 ^ d := by
        exact_mod_cast (nb_clo_le j Y).trans hs.2.2
      have h3 : (0 : ℝ) ≤ nb j Y := Nat.cast_nonneg _
      have h4 : (1 + 2 * η) * (nb (j + 1) (clo j Y) : ℝ) ≤ (1 + 2 * η) * 2 ^ d :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      linarith
    · have h2 := h1 L hL N j Y hj hYc hs
      have h3 : (0 : ℝ) ≤ (1 + 2 * η) * 2 ^ d := by positivity
      linarith
  have hbl : ∀ k, blocks k X = (Comp j X).biUnion (blocks k) := by
    intro k; rw [← blocks_biUnion, biUnion_comp hX]
  have hsum1 : nb (j + 1) (clo j X) ≤ ∑ Y ∈ Comp j X, nb (j + 1) (clo j Y) := by
    simp only [nb, blocks_clo]
    rw [hbl (j + 1)]
    exact card_biUnion_le
  have hsum2 : nb j X = ∑ Y ∈ Comp j X, nb j Y := by
    rw [nb, hbl j, card_biUnion]
    · rfl
    · intro Y hY Y' hY' hne
      exact disjoint_blocks (isConn_of_mem_comp hX (mem_coe.1 hY)).1
        (isConn_of_mem_comp hX (mem_coe.1 hY')).1
        (disjoint_of_not_touch (not_touch_of_mem_comp hX (mem_coe.1 hY) (mem_coe.1 hY') hne))
  have hA : (1 + 2 * η) * (nb (j + 1) (clo j X) : ℝ) ≤
      nb j X + (1 + 2 * η) * 2 ^ d * (Comp j X).card := by
    calc (1 + 2 * η) * (nb (j + 1) (clo j X) : ℝ)
        ≤ (1 + 2 * η) * ∑ Y ∈ Comp j X, (nb (j + 1) (clo j Y) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact_mod_cast hsum1
      _ = ∑ Y ∈ Comp j X, (1 + 2 * η) * (nb (j + 1) (clo j Y) : ℝ) := by rw [mul_sum]
      _ ≤ ∑ Y ∈ Comp j X, ((nb j Y : ℝ) + (1 + 2 * η) * 2 ^ d) := sum_le_sum hcomp
      _ = nb j X + (1 + 2 * η) * 2 ^ d * (Comp j X).card := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, hsum2, Nat.cast_sum]; ring
  refine ⟨hA, ?_⟩
  have hc : (0 : ℝ) ≤ (Comp j X).card := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ nb (j + 1) (clo j X) := Nat.cast_nonneg _
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have h5 : (1 + 2 * η) * 2 ^ d * (Comp j X).card ≤ (1 + η) * 2 ^ (d + 1) * (Comp j X).card := by
    rw [pow_succ]; nlinarith [mul_nonneg h2d hc, mul_nonneg (mul_nonneg hη0.le h2d) hc]
  nlinarith [mul_nonneg hη0.le hm]

/-! ### Counting -/

/-- The number of small sets containing a given block is bounded by a constant `c(d)`. -/
theorem card_small_containing (d : ℕ) : ∃ c : ℕ, ∀ (L : ℕ) [NeZero L] (N j : ℕ)
    (b : Fin d → ℕ), b ∈ blockIdx (L := L) (N := N) j →
      ((smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).card ≤ c := by
  classical
  refine ⟨2 ^ (5 ^ (d * 2 ^ d)), ?_⟩
  intro L _ N j b hb
  have hne : (blockSet (L := L) (N := N) j b).Nonempty := by
    obtain ⟨x, _, hx⟩ := mem_image.1 hb
    exact ⟨x, mem_blockSet.2 hx⟩
  calc _ ≤ (Ball (L ^ (N - j)) b (2 ^ d)).powerset.card := by
        refine card_le_card_of_injOn (blocks j) ?_ ?_
        · intro X hX
          have hX' := mem_filter.1 (mem_coe.1 hX)
          have hS : IsSmall j X := (mem_filter.1 hX'.1).2
          refine mem_coe.2 (mem_powerset.2 ?_)
          have hbX := mem_blocks_of_nonempty hne hX'.2
          exact (subset_Ball (conn_blocks hS.2.1) hbX).trans (Ball_mono b hS.2.2)
        · intro X hX Y hY e
          have hXp := (mem_filter.1 (mem_filter.1 (mem_coe.1 hX)).1).2.1
          have hYp := (mem_filter.1 (mem_filter.1 (mem_coe.1 hY)).1).2.1
          rw [← biUnion_blocks hXp, ← biUnion_blocks hYp]
          rw [e]
    _ = 2 ^ (Ball (L ^ (N - j)) b (2 ^ d)).card := card_powerset _
    _ ≤ 2 ^ (5 ^ (d * 2 ^ d)) := Nat.pow_le_pow_right (by norm_num) (card_Ball b _)

/-- The number of `X ∈ 𝒫_j` with `X̄ = U` is at most `2^{L^d |𝓑_{j+1}(U)|}`. -/
theorem card_clo_eq_le {j : ℕ} {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    ((Pj j univ).filter (fun X => clo j X = U)).card ≤ 2 ^ (L ^ d * nb (j + 1) U) := by
  classical
  calc _ ≤ (Pj j U).card := card_le_card (by
        intro X hX
        have hX' := mem_filter.1 hX
        rw [mem_Pj] at hX' ⊢
        exact ⟨hX'.2 ▸ subset_clo j X, hX'.1.2⟩)
    _ = 2 ^ nb j U := card_Pj (IsPolymer.of_succ hU)
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (nb_le_of_succ hU)

/-- The number of small sets `X ∈ 𝒮_j` with `X̄ = U` is `O(L^d)` for `U ∈ 𝒮_{j+1}`. -/
theorem card_small_clo_le (d : ℕ) : ∃ c : ℕ, ∀ (L : ℕ) [NeZero L] (N j : ℕ)
    (U : Finset (Lam d L N)), IsSmall (j + 1) U →
      ((smallSets j).filter (fun X => clo j X = U)).card ≤ c * L ^ d := by
  classical
  obtain ⟨c, hc⟩ := card_small_containing d
  refine ⟨2 ^ d * c, ?_⟩
  intro L _ N j U hU
  have hsub : (smallSets j).filter (fun X => clo j X = U) ⊆ (blocks j U).biUnion
      (fun b => (smallSets j).filter (fun X => blockSet j b ⊆ X)) := by
    intro X hX
    have hX' := mem_filter.1 hX
    have hS : IsSmall j X := (mem_filter.1 hX'.1).2
    obtain ⟨x, hx⟩ := hS.2.1.1
    refine mem_biUnion.2 ⟨blk j x, ?_, mem_filter.2 ⟨hX'.1,
      blockSet_subset hS.1 (blk_mem_blocks hx)⟩⟩
    rw [← hX'.2]
    exact blk_mem_blocks (subset_clo j X hx)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ b ∈ blocks j U, c := card_biUnion_le.trans (sum_le_sum fun b hb =>
          hc L N j b (image_subset_image (subset_univ U) hb))
    _ = nb j U * c := by rw [sum_const, smul_eq_mul, nb]
    _ ≤ (L ^ d * 2 ^ d) * c :=
        Nat.mul_le_mul_right _ ((nb_le_of_succ hU.1).trans (Nat.mul_le_mul_left _ hU.2.2))
    _ = 2 ^ d * c * L ^ d := by ring

/-! ### Small set neighbourhoods -/

theorem isPolymer_nbhd (j : ℕ) (X : Finset (Lam d L N)) : IsPolymer j (nbhd j X) := by
  classical
  intro x y h hx
  simp only [nbhd, mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨S, hS, hxS, rest⟩ := hx
  exact ⟨S, hS, hS.1 x y h hxS, rest⟩

theorem subset_nbhd_of_small {j : ℕ} {X : Finset (Lam d L N)} {b : Fin d → ℕ}
    (hX : IsSmall j X) (hb : blockSet j b ⊆ X) (hne : (blockSet (L := L) (N := N) j b).Nonempty) :
    X ⊆ nbhd j (blockSet (L := L) (N := N) j b) := by
  classical
  intro y hy
  simp only [nbhd, mem_filter, mem_univ, true_and]
  refine ⟨X, hX, hy, b, ?_, hb⟩
  obtain ⟨x, hx⟩ := hne
  rw [← mem_blockSet.1 hx]
  exact blk_mem_blocks (mem_blockSet_blk j x)

theorem two_vals {Q M' R x v : ℕ} (hQ : 0 < Q) (hM : 0 < M') (h2R : 2 * R ≤ Q)
    (hx : x < Q * M') (hv : v < Q * M')
    (hrel : (x ≤ v ∧ v ≤ x + R) ∨ (v ≤ x ∧ x ≤ v + R) ∨ x + Q * M' ≤ v + R ∨
      v + Q * M' ≤ x + R) :
    v / Q ∈ (if x < R ∨ Q * M' ≤ x + R then ({0, M' - 1} : Finset ℕ)
      else {(x - R) / Q, (x - R) / Q + 1}) := by
  have hQM : Q ≤ Q * M' := Nat.le_mul_of_pos_right Q hM
  have top : ∀ w, Q * M' - Q ≤ w → w < Q * M' → w / Q = M' - 1 := by
    intro w h1 h2
    refine (div_mod_of_eq hQ (r := w - (Q * M' - Q)) (by omega) ?_).1
    rw [Nat.mul_sub_one]; omega
  have bot : ∀ w, w < Q → w / Q = 0 := fun w h => Nat.div_eq_of_lt h
  split_ifs with hc
  · rcases hc with hc | hc
    · rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3 | h3
      · rw [bot v (by omega)]; simp
      · rw [bot v (by omega)]; simp
      · rw [top v (by omega) hv]; simp
      · omega
    · rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3 | h3
      · rw [top v (by omega) hv]; simp
      · rw [top v (by omega) hv]; simp
      · omega
      · rw [bot v (by omega)]; simp
  · push Not at hc
    have hv1 : x - R ≤ v ∧ v ≤ x - R + Q := by
      rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3 | h3 <;> omega
    have h1 : (x - R) / Q ≤ v / Q := Nat.div_le_div_right hv1.1
    have h3 : v / Q ≤ (x - R + Q) / Q := Nat.div_le_div_right hv1.2
    have h4 := Nat.add_div_right (x - R) hQ
    rcases (by omega : v / Q = (x - R) / Q ∨ v / Q = (x - R) / Q + 1) with e | e <;> simp [e]

/-- For `L ≥ 2^{d+2}` the closure of `B^□` is a small set at scale `j+1`. -/
theorem isSmall_clo_nbhd (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    (b : Fin d → ℕ) (hb : b ∈ blockIdx (L := L) (N := N) j) :
    IsSmall (j + 1) (clo j (nbhd j (blockSet (L := L) (N := N) j b))) := by
  classical
  obtain ⟨x₀, _, hx₀⟩ := mem_image.1 hb
  subst hx₀
  set B := blockSet (L := L) (N := N) j (blk j x₀) with hBdef
  have hBs : IsSmall j B := isSmall_blockSet j x₀
  have hx₀B : x₀ ∈ B := mem_blockSet_blk j x₀
  have hconn : IsConn j (nbhd j B) := by
    refine ⟨isPolymer_nbhd j B, ⟨⟨x₀, subset_nbhd hBs.1 hx₀B⟩, ?_⟩⟩
    have hreach : ∀ c ∈ blocks j (nbhd j B),
        Relation.ReflTransGen (BlockAdj j (nbhd j B)) (blk j x₀) c := by
      intro c hc
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
      have hy' := hy
      simp only [nbhd, mem_filter, mem_univ, true_and] at hy'
      obtain ⟨S, hS, hyS, b', hb', hbS⟩ := hy'
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hb'
      have hzb : blk j z = blk j x₀ := mem_blockSet.1 hz
      rw [hzb] at hbS
      have hSn : S ⊆ nbhd j B := fun w hw => by
        simp only [nbhd, mem_filter, mem_univ, true_and]
        exact ⟨S, hS, hw, blk j x₀, blk_mem_blocks hx₀B, hbS⟩
      exact blockAdj_mono hSn
        (hS.2.1.2 (blk j x₀) (blk_mem_blocks (hbS hx₀B)) (blk j y) (blk_mem_blocks hyS))
    intro c hc c' hc'
    exact (Relation.ReflTransGen.symmetric blockAdj_symm (hreach c hc)).trans (hreach c' hc')
  refine ⟨isPolymer_clo j _, (isConn_clo hconn).2, ?_⟩
  rw [blocks_clo]
  have hL0 : 0 < L := by have := Nat.one_le_two_pow (n := d + 2); omega
  have hn : L ^ N = L ^ (j + 1) * L ^ (N - (j + 1)) := by rw [← pow_add]; congr 1; omega
  have h2R : 2 * (2 ^ (d + 1) * L ^ j) ≤ L ^ (j + 1) := by
    calc 2 * (2 ^ (d + 1) * L ^ j) = 2 ^ (d + 2) * L ^ j := by ring
      _ ≤ L * L ^ j := Nat.mul_le_mul_right _ hL
      _ = L ^ (j + 1) := by ring
  let V : Fin d → Finset ℕ := fun i =>
    if (co x₀ i).val < 2 ^ (d + 1) * L ^ j ∨
        L ^ (j + 1) * L ^ (N - (j + 1)) ≤ (co x₀ i).val + 2 ^ (d + 1) * L ^ j then
      {0, L ^ (N - (j + 1)) - 1}
    else {((co x₀ i).val - 2 ^ (d + 1) * L ^ j) / L ^ (j + 1),
      ((co x₀ i).val - 2 ^ (d + 1) * L ^ j) / L ^ (j + 1) + 1}
  have hsub : blocks (j + 1) (nbhd j B) ⊆ Fintype.piFinset V := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    refine Fintype.mem_piFinset.2 fun i => ?_
    have hsn := supNorm_le_of_mem_nbhd hBs hx₀B hy
    have hz : zabs (co y i - co x₀ i) ≤ 2 ^ (d + 1) * L ^ j := (supNorm_le_iff _ _).1 hsn i
    have hrel := zabs_sub_le hz
    have hxl := ZMod.val_lt (co x₀ i)
    have hyl := ZMod.val_lt (co y i)
    have key : ∀ xv yv : ℕ, xv < L ^ N → yv < L ^ N →
        ((xv ≤ yv ∧ yv ≤ xv + 2 ^ (d + 1) * L ^ j) ∨ (yv ≤ xv ∧ xv ≤ yv + 2 ^ (d + 1) * L ^ j) ∨
          xv + L ^ N ≤ yv + 2 ^ (d + 1) * L ^ j ∨ yv + L ^ N ≤ xv + 2 ^ (d + 1) * L ^ j) →
        yv / L ^ (j + 1) ∈ (if xv < 2 ^ (d + 1) * L ^ j ∨
            L ^ (j + 1) * L ^ (N - (j + 1)) ≤ xv + 2 ^ (d + 1) * L ^ j then
          ({0, L ^ (N - (j + 1)) - 1} : Finset ℕ)
        else {(xv - 2 ^ (d + 1) * L ^ j) / L ^ (j + 1),
          (xv - 2 ^ (d + 1) * L ^ j) / L ^ (j + 1) + 1}) := by
      intro xv yv h1 h2 h3
      rw [hn] at h1 h2 h3
      exact two_vals (pow_pos hL0 _) (pow_pos hL0 _) h2R h1 h2 h3
    exact key _ _ hxl hyl hrel
  calc _ ≤ (Fintype.piFinset V).card := card_le_card hsub
    _ = ∏ i, (V i).card := Fintype.card_piFinset V
    _ ≤ ∏ _i : Fin d, 2 := prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => by
          simp only [V]; split_ifs <;> exact card_le_two
    _ = 2 ^ d := by simp

end

end Step
