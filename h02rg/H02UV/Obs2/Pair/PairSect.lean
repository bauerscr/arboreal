import Obs2.Map.ExactStep

/-!
# The sector reduction of the polymer gas at coalescence (PR1, generic part)

`Z = gZO j I K = ∑_{X ∈ 𝒫_j} I^{Λ∖X} K^X` with sources. Fix a connected polymer `D` and a point
`z₀ ∈ D`. For a polymer `X` let `Y = dComp X` be the component of `X ∪ D` containing `z₀` (the
**`D`-component**; it is connected, contains `D` and does not touch `X ∖ Y`). Then (`sum_dComp`)

  `∑_X G(Y, X ∩ Y, X ∖ Y) = ∑_Y ∑_{A ∈ 𝒮_Y} ∑_{B ∈ 𝒯_Y} G(Y, A, B)`,

`𝒮_Y = {A ∈ 𝒫_j(Y) : dComp A = Y}`, `𝒯_Y = {B ∈ 𝒫_j(Λ∖Y) : B does not touch Y}`, and
`I^{Λ∖X}K^X = (I^{Y∖A}K^A)·(I^{(Λ∖Y)∖B}K^B)` (`gZO_term_split`).

**The reduced activity.** `zLoc Y = ∑_{A ∈ 𝒮_Y} I^{Y∖A}K^A` (the configurations whose `D`-component
is `Y`), `kRed Y = π_{ab}(zLoc Y)` for `Y ⊇ D` (else `0`). If outside `D` the block factors and the
activities of connected polymers disjoint from `D` are bulk (`I = I'`, `K = K_b` there, with `I'`,
`K_b` bulk and of the same bulk part everywhere), then (**`gZO_sect`**)

  `Z_∅ = Z'_∅`, `Z_{ab} = Z'_{ab}`,  `Z' = gZO j I' (K_b + kRed)`.

So the `∅` and `σ_aσ_b` sectors of the input are reproduced by a state without `σ_a`, `σ_b` parts
whose only observable part is the `ab` activity `kRed` on connected polymers containing `D`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Components -/

section Geom

variable {j : ℕ}

theorem compOf_eq_of_mem_comp {X Z : Finset (Lam d L N)} (hZ : Z ∈ Comp j X) {x : Lam d L N}
    (hx : x ∈ Z) : compOf j X (blk j x) = Z := by
  classical
  obtain ⟨b, -, rfl⟩ := mem_image.1 hZ
  have h : x ∈ X ∧ Relation.ReflTransGen (BlockAdj j X) b (blk j x) := by
    unfold compOf at hx; exact mem_filter.1 hx
  exact (compOf_eq_of_rtg h.2).symm

theorem compOf_self_of_isConn {Y : Finset (Lam d L N)} (hY : IsConn j Y) {x : Lam d L N}
    (hx : x ∈ Y) : compOf j Y (blk j x) = Y :=
  compOf_eq_of_mem_comp (by rw [comp_of_isConn hY]; exact mem_singleton_self Y) hx

/-- **The `D`-component of `X`**: the component of `X ∪ D` containing `z₀`. -/
def dComp (j : ℕ) (D : Finset (Lam d L N)) (z0 : Lam d L N) (X : Finset (Lam d L N)) :
    Finset (Lam d L N) :=
  compOf j (X ∪ D) (blk j z0)

variable {D : Finset (Lam d L N)} {z0 : Lam d L N}

theorem mem_dComp {X : Finset (Lam d L N)} {x : Lam d L N} :
    x ∈ dComp j D z0 X ↔
      x ∈ X ∪ D ∧ Relation.ReflTransGen (BlockAdj j (X ∪ D)) (blk j z0) (blk j x) := by
  classical
  unfold dComp compOf; exact mem_filter

theorem dComp_subset (X : Finset (Lam d L N)) : dComp j D z0 X ⊆ X ∪ D := fun _ h =>
  (mem_dComp.1 h).1

theorem subset_dComp (hD : IsConn j D) (hz0 : z0 ∈ D) (X : Finset (Lam d L N)) :
    D ⊆ dComp j D z0 X := fun _z hz =>
  mem_dComp.2 ⟨mem_union_right _ hz, blockAdj_mono subset_union_right
    (hD.2.2 _ (blk_mem_blocks hz0) _ (blk_mem_blocks hz))⟩

theorem isConn_dComp (hD : IsConn j D) (hz0 : z0 ∈ D) {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) : IsConn j (dComp j D z0 X) :=
  isConn_compOf (IsPolymer.union hX hD.1) (blk_mem_blocks (mem_union_right _ hz0))

theorem not_touch_sdiff_dComp (X : Finset (Lam d L N)) :
    ¬ Touch (X \ dComp j D z0 X) (dComp j D z0 X) := by
  rintro ⟨x, hx, y, hy, hxy⟩
  rw [mem_sdiff] at hx
  have hy' := mem_dComp.1 hy
  apply hx.2
  refine mem_dComp.2 ⟨mem_union_left _ hx.1, hy'.2.tail ⟨blk_mem_blocks hy'.1,
    blk_mem_blocks (mem_union_left _ hx.1),
    ⟨y, mem_blockSet_blk j y, x, mem_blockSet_blk j x, ?_⟩⟩⟩
  rwa [supNorm_sub_comm]

theorem inter_dComp_union (hD : IsConn j D) (hz0 : z0 ∈ D) (X : Finset (Lam d L N)) :
    X ∩ dComp j D z0 X ∪ D = dComp j D z0 X := by
  ext x
  constructor
  · intro h
    rcases mem_union.1 h with h | h
    · exact (mem_inter.1 h).2
    · exact subset_dComp hD hz0 X h
  · intro h
    rcases mem_union.1 (dComp_subset X h) with h' | h'
    · exact mem_union_left _ (mem_inter.2 ⟨h', h⟩)
    · exact mem_union_right _ h'

theorem dComp_of_union_eq {Y : Finset (Lam d L N)} (hY : IsConn j Y) (hDY : D ⊆ Y) (hz0 : z0 ∈ D)
    {A : Finset (Lam d L N)} (hA : A ∪ D = Y) : dComp j D z0 A = Y := by
  unfold dComp; rw [hA]; exact compOf_self_of_isConn hY (hDY hz0)

theorem dComp_inter (hD : IsConn j D) (hz0 : z0 ∈ D) {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) : dComp j D z0 (X ∩ dComp j D z0 X) = dComp j D z0 X :=
  dComp_of_union_eq (isConn_dComp hD hz0 hX) (subset_dComp hD hz0 X) hz0
    (inter_dComp_union hD hz0 X)

theorem dComp_union (hD : IsConn j D) (hz0 : z0 ∈ D) {A B Y : Finset (Lam d L N)}
    (hA : IsPolymer j A) (hB : IsPolymer j B) (hAY : A ⊆ Y) (hdA : dComp j D z0 A = Y)
    (hBY : ¬ Touch B Y) : dComp j D z0 (A ∪ B) = Y := by
  have hDY : D ⊆ Y := hdA ▸ subset_dComp hD hz0 A
  have hP : IsPolymer j (A ∪ D) := IsPolymer.union hA hD.1
  have hT : ¬ Touch (A ∪ D) B := fun h =>
    hBY (touch_mono subset_rfl (union_subset hAY hDY) (touch_symm h))
  have hYc : Y ∈ Comp j (A ∪ D) := by
    rw [← hdA]; exact mem_image_of_mem _ (blk_mem_blocks (mem_union_right _ hz0))
  unfold dComp
  rw [show A ∪ B ∪ D = (A ∪ D) ∪ B by
    ext x; simp only [mem_union]; tauto]
  exact compOf_eq_of_mem_comp (by rw [comp_union hP hB hT]; exact mem_union_left _ hYc) (hDY hz0)

/-- `𝒮_Y`: the polymers `A ⊆ Y` with `D`-component `Y`. -/
def sY (j : ℕ) (D : Finset (Lam d L N)) (z0 : Lam d L N) (Y : Finset (Lam d L N)) :
    Finset (Finset (Lam d L N)) :=
  open Classical in (Pj j Y).filter fun A => dComp j D z0 A = Y

/-- `𝒯_Y`: the polymers in `Λ ∖ Y` not touching `Y`. -/
def tY (j : ℕ) (Y : Finset (Lam d L N)) : Finset (Finset (Lam d L N)) :=
  open Classical in (Pj j (univ \ Y)).filter fun B => ¬ Touch B Y

theorem mem_sY {Y A : Finset (Lam d L N)} :
    A ∈ sY j D z0 Y ↔ (A ⊆ Y ∧ IsPolymer j A) ∧ dComp j D z0 A = Y := by
  classical
  unfold sY; rw [mem_filter, mem_Pj]

theorem mem_tY {Y B : Finset (Lam d L N)} :
    B ∈ tY j Y ↔ (B ⊆ univ \ Y ∧ IsPolymer j B) ∧ ¬ Touch B Y := by
  classical
  unfold tY; rw [mem_filter, mem_Pj]

/-- **The regrouping by the `D`-component.** -/
theorem sum_dComp {M : Type*} [AddCommMonoid M] (hD : IsConn j D) (hz0 : z0 ∈ D)
    (G : Finset (Lam d L N) → Finset (Lam d L N) → Finset (Lam d L N) → M) :
    ∑ X ∈ Pj j (univ : Finset (Lam d L N)),
        G (dComp j D z0 X) (X ∩ dComp j D z0 X) (X \ dComp j D z0 X) =
      ∑ Y : Finset (Lam d L N), ∑ A ∈ sY j D z0 Y, ∑ B ∈ tY j Y, G Y A B := by
  classical
  rw [← Finset.sum_fiberwise (Pj j (univ : Finset (Lam d L N))) (dComp j D z0)]
  refine sum_congr rfl fun Y _ => ?_
  rw [← sum_product']
  refine sum_nbij' (fun X => (X ∩ Y, X \ Y)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    obtain ⟨hX1, hXY⟩ := mem_filter.1 hX
    have hXp := (mem_Pj.1 hX1).2
    subst hXY
    have hYp := (isConn_dComp hD hz0 hXp).1
    refine mem_product.2 ⟨mem_sY.2 ⟨⟨inter_subset_right, IsPolymer.inter hXp hYp⟩, dComp_inter hD hz0 hXp⟩,
      mem_tY.2 ⟨⟨fun x hx => mem_sdiff.2 ⟨mem_univ x, (mem_sdiff.1 hx).2⟩, IsPolymer.sdiff hXp hYp⟩,
        not_touch_sdiff_dComp X⟩⟩
  · rintro ⟨A, B⟩ hp
    obtain ⟨hA, hB⟩ := mem_product.1 hp
    obtain ⟨⟨hAY, hAp⟩, hdA⟩ := mem_sY.1 hA
    obtain ⟨⟨-, hBp⟩, hBY⟩ := mem_tY.1 hB
    exact mem_filter.2 ⟨mem_Pj.2 ⟨subset_univ _, IsPolymer.union hAp hBp⟩,
      dComp_union hD hz0 hAp hBp hAY hdA hBY⟩
  · intro X _
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  · rintro ⟨A, B⟩ hp
    obtain ⟨hA, hB⟩ := mem_product.1 hp
    have hAY := (mem_sY.1 hA).1.1
    have hBY := (mem_tY.1 hB).1.1
    refine Prod.ext ?_ ?_
    · ext x
      simp only [mem_union, mem_inter]
      constructor
      · rintro ⟨h | h, hy⟩
        · exact h
        · exact absurd hy (mem_sdiff.1 (hBY h)).2
      · intro h; exact ⟨Or.inl h, hAY h⟩
    · ext x
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro ⟨h | h, hy⟩
        · exact absurd (hAY h) hy
        · exact h
      · intro h; exact ⟨Or.inr h, (mem_sdiff.1 (hBY h)).2⟩
  · intro X hX
    rw [(mem_filter.1 hX).2]

end Geom

/-! ### The splitting of one configuration -/

section Split

variable {j : ℕ} {D : Finset (Lam d L N)} {z0 : Lam d L N}

/-- `I^{Λ∖X}K^X = (I^{Y∖(X∩Y)}K^{X∩Y})(I^{(Λ∖Y)∖(X∖Y)}K^{X∖Y})`, `Y = dComp X`. -/
theorem gZO_term_split (hD : IsConn j D) (hz0 : z0 ∈ D) (I : OFam c d L N) (K : OAct c d L N)
    {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    bpowO j I (univ \ X) * KextO j K X =
      (bpowO j I (dComp j D z0 X \ (X ∩ dComp j D z0 X)) * KextO j K (X ∩ dComp j D z0 X)) *
        (bpowO j I ((univ \ dComp j D z0 X) \ (X \ dComp j D z0 X)) *
          KextO j K (X \ dComp j D z0 X)) := by
  set Y := dComp j D z0 X with hYd
  have hYp : IsPolymer j Y := (isConn_dComp hD hz0 hX).1
  have hT : ¬ Touch (X ∩ Y) (X \ Y) := fun h =>
    not_touch_sdiff_dComp X (touch_mono subset_rfl inter_subset_right (touch_symm h))
  have hK : KextO j K X = KextO j K (X ∩ Y) * KextO j K (X \ Y) := by
    rw [← KextO_union j K (IsPolymer.inter hX hYp) (IsPolymer.sdiff hX hYp) hT]
    congr 1; ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have hB : bpowO j I (univ \ X) = bpowO j I (Y \ (X ∩ Y)) * bpowO j I ((univ \ Y) \ (X \ Y)) := by
    rw [← bpowO_union j I (IsPolymer.sdiff hYp (IsPolymer.inter hX hYp))
      (IsPolymer.sdiff (IsPolymer.sdiff (isPolymer_univ j) hYp) (IsPolymer.sdiff hX hYp))]
    · congr 1; ext x; simp only [mem_union, mem_inter, mem_sdiff, mem_univ, true_and]; tauto
    · rw [disjoint_left]
      intro x h1 h2
      exact (mem_sdiff.1 (mem_sdiff.1 h2).1).2 (mem_sdiff.1 h1).1
  rw [hK, hB]; ring

/-- **`Z` regrouped by the `D`-component.** -/
theorem gZO_dComp (hD : IsConn j D) (hz0 : z0 ∈ D) (I : OFam c d L N) (K : OAct c d L N) :
    gZO j I K = ∑ Y : Finset (Lam d L N), ∑ A ∈ sY j D z0 Y, ∑ B ∈ tY j Y,
      (bpowO j I (Y \ A) * KextO j K A) * (bpowO j I ((univ \ Y) \ B) * KextO j K B) := by
  rw [gZO, ← sum_dComp hD hz0
    (fun Y A B => (bpowO j I (Y \ A) * KextO j K A) * (bpowO j I ((univ \ Y) \ B) * KextO j K B))]
  exact sum_congr rfl fun X hX => gZO_term_split hD hz0 I K (mem_Pj.1 hX).2

end Split

/-! ### The reduced activity and the sector identity -/

section Sect

variable {j : ℕ} {D : Finset (Lam d L N)} {z0 : Lam d L N}

/-- `zLoc Y = ∑_{A ∈ 𝒮_Y} I^{Y∖A}K^A`: the configurations with `D`-component `Y`. -/
def zLoc (j : ℕ) (D : Finset (Lam d L N)) (z0 : Lam d L N) (I : OFam c d L N) (K : OAct c d L N)
    (Y : Finset (Lam d L N)) : OE c (Lam d L N) :=
  ∑ A ∈ sY j D z0 Y, bpowO j I (Y \ A) * KextO j K A

/-- **The reduced activity** `kRed Y = π_{ab}(zLoc Y)` for `Y ⊇ D`, `0` otherwise. -/
def kRed (j : ℕ) (D : Finset (Lam d L N)) (z0 : Lam d L N) (I : OFam c d L N)
    (K : OAct c d L N) : OAct c d L N :=
  open Classical in fun Y => if D ⊆ Y then πab (zLoc j D z0 I K Y) else 0

omit [NeZero L] in
/-- The bulk elements `emb(EvR)`. -/
abbrev PBsub (c : Obs.Case) (Λ : Type*) [DecidableEq Λ] : Subalgebra ℂ (OE c Λ) :=
  (emb : Step.EvR Λ →ₐ[ℂ] OE c Λ).range

local notation "PB" => PBsub c (Lam d L N)

theorem ab_of_pure {F : OE c (Lam d L N)} (hF : F ∈ PB) : (F : SA c (Lam d L N)).ab = 0 := by
  obtain ⟨x, rfl⟩ := hF; rfl

theorem ab_mul_pure (F : OE c (Lam d L N)) {G : OE c (Lam d L N)} (hG : G ∈ PB) :
    ((F * G : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      (F : SA c (Lam d L N)).ab * (G : SA c (Lam d L N)).e := by
  obtain ⟨x, rfl⟩ := hG
  rw [OE.mul_ab]
  simp [coe_emb]

theorem ab_sumO {ι : Type*} (s : Finset ι) (f : ι → OE c (Lam d L N)) :
    ((∑ i ∈ s, f i : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      ∑ i ∈ s, (f i : SA c (Lam d L N)).ab := by
  rw [AddSubmonoidClass.coe_finsetSum, SA.sum_ab]

theorem bulk_kRed (I : OFam c d L N) (K : OAct c d L N) (Y : Finset (Lam d L N)) :
    bulk (kRed j D z0 I K Y) = 0 := by
  classical
  unfold kRed
  split_ifs
  · exact Subtype.ext (by rw [coe_bulk, coe_πab, piab_apply]; rfl)
  · exact map_zero _

theorem kRed_mem_ab (I : OFam c d L N) (K : OAct c d L N) (Y : Finset (Lam d L N)) :
    (kRed j D z0 I K Y : SA c (Lam d L N)).a = 0 ∧ (kRed j D z0 I K Y : SA c (Lam d L N)).b = 0 := by
  classical
  unfold kRed
  split_ifs
  · rw [coe_πab, piab_apply]; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem kRed_of_not (I : OFam c d L N) (K : OAct c d L N) {Y : Finset (Lam d L N)}
    (h : ¬ D ⊆ Y) : kRed j D z0 I K Y = 0 := by
  classical
  unfold kRed; rw [if_neg h]

theorem kRed_of_sub (I : OFam c d L N) (K : OAct c d L N) {Y : Finset (Lam d L N)}
    (h : D ⊆ Y) : kRed j D z0 I K Y = πab (zLoc j D z0 I K Y) := by
  classical
  unfold kRed; rw [if_pos h]

/-- **The sector identity**: the `∅` and `σ_aσ_b` components of `Z = gZO j I K` are those of
`gZO j I' (K_b + kRed)`. -/
theorem gZO_sect (hD : IsConn j D) (hz0 : z0 ∈ D) (I I' : OFam c d L N) (K Kb : OAct c d L N)
    (hI' : ∀ b, I' b ∈ PB) (hII : ∀ b, bulk (I' b) = bulk (I b))
    (hIf : ∀ b, b ∉ blocks j D → I b = I' b)
    (hKb : ∀ Y, Kb Y ∈ PB) (hKK : ∀ Y, bulk (Kb Y) = bulk (K Y))
    (hKf : ∀ Y, IsConn j Y → Disjoint Y D → K Y = Kb Y) :
    ((gZO j I K : OE c (Lam d L N)) : SA c (Lam d L N)).e =
        ((gZO j I' (Kb + kRed j D z0 I K) : OE c (Lam d L N)) : SA c (Lam d L N)).e ∧
      ((gZO j I K : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
        ((gZO j I' (Kb + kRed j D z0 I K) : OE c (Lam d L N)) : SA c (Lam d L N)).ab := by
  set K' : OAct c d L N := Kb + kRed j D z0 I K with hK'd
  have hK'b : ∀ Y, bulk (K' Y) = bulk (K Y) := fun Y => by
    show bulk (Kb Y + kRed j D z0 I K Y) = _
    rw [map_add, bulk_kRed, add_zero, hKK]
  refine ⟨?_, ?_⟩
  · -- the bulk parts
    rw [← coe_bulk, ← coe_bulk]
    congr 1
    unfold gZO
    rw [map_sum, map_sum]
    refine sum_congr rfl fun X _ => ?_
    rw [map_mul, map_mul, bpowO, bpowO, KextO, KextO, map_prod, map_prod, map_prod, map_prod]
    congr 1
    · exact prod_congr rfl fun b _ => (hII b).symm
    · exact prod_congr rfl fun Y _ => (hK'b Y).symm
  · have hD0 : z0 ∈ D := hz0
    -- `Y ∈ 𝒮_Y`-facts
    have hSY : ∀ Y A, A ∈ sY j D z0 Y → IsConn j Y ∧ D ⊆ Y ∧ Y ∈ sY j D z0 Y := by
      intro Y A hA
      obtain ⟨⟨-, hAp⟩, hdA⟩ := mem_sY.1 hA
      have hYc : IsConn j Y := hdA ▸ isConn_dComp hD hz0 hAp
      have hDY : D ⊆ Y := hdA ▸ subset_dComp hD hz0 A
      exact ⟨hYc, hDY, mem_sY.2 ⟨⟨subset_rfl, hYc.1⟩,
        dComp_of_union_eq hYc hDY hz0 (union_eq_left.2 hDY)⟩⟩
    -- the far factors agree and are bulk
    have hfar : ∀ Y B, D ⊆ Y → IsPolymer j Y → B ∈ tY j Y →
        bpowO j I ((univ \ Y) \ B) * KextO j K B = bpowO j I' ((univ \ Y) \ B) * KextO j K' B ∧
        bpowO j I' ((univ \ Y) \ B) * KextO j K' B ∈ PB := by
      intro Y B hDY hYp hB
      obtain ⟨⟨hBY, hBp⟩, -⟩ := mem_tY.1 hB
      have hb : ∀ b ∈ blocks j ((univ \ Y) \ B), I b = I' b := by
        intro b hb
        refine hIf b fun hbD => ?_
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
        exact (mem_sdiff.1 (mem_sdiff.1 hx).1).2 (mem_of_blk_mem hYp (image_subset_image hDY hbD))
      have hk : ∀ Z ∈ Comp j B, K Z = K' Z ∧ K' Z = Kb Z := by
        intro Z hZ
        have hZB := subset_of_mem_comp hZ
        have hdis : Disjoint Z D := by
          rw [disjoint_left]
          intro x hxZ hxD
          exact (mem_sdiff.1 (hBY (hZB hxZ))).2 (hDY hxD)
        have hnD : ¬ D ⊆ Z := fun h => disjoint_left.1 hdis (h hz0) hz0
        have e2 : K' Z = Kb Z := by
          show Kb Z + kRed j D z0 I K Z = Kb Z
          rw [kRed_of_not I K hnD, add_zero]
        exact ⟨(hKf Z (isConn_of_mem_comp hBp hZ) hdis).trans e2.symm, e2⟩
      refine ⟨?_, mul_mem (prod_mem fun b _ => hI' b) (prod_mem fun Z hZ => ?_)⟩
      · rw [bpowO, bpowO, KextO, KextO, prod_congr rfl hb, prod_congr rfl fun Z hZ => (hk Z hZ).1]
      · rw [(hk Z hZ).2]; exact hKb Z
    -- the local factors of the reduced activity
    have hloc : ∀ Y, (∑ A ∈ sY j D z0 Y,
        ((bpowO j I' (Y \ A) * KextO j K' A : OE c (Lam d L N)) : SA c (Lam d L N)).ab) =
        ∑ A ∈ sY j D z0 Y, ((bpowO j I (Y \ A) * KextO j K A : OE c (Lam d L N)) :
          SA c (Lam d L N)).ab := by
      intro Y
      rw [← ab_sumO, ← ab_sumO]
      rcases (sY j D z0 Y).eq_empty_or_nonempty with h | ⟨A0, hA0⟩
      · rw [h, sum_empty, sum_empty]
      obtain ⟨hYc, hDY, hYY⟩ := hSY Y A0 hA0
      rw [ab_sumO, sum_eq_single_of_mem Y hYY]
      · have h1 : bpowO j I' (Y \ Y) = 1 := by simp [bpowO, blocks]
        rw [KextO, comp_of_isConn hYc, prod_singleton]
        rw [h1, one_mul]
        show ((Kb Y + kRed j D z0 I K Y : OE c (Lam d L N)) : SA c (Lam d L N)).ab = _
        rw [kRed_of_sub I K hDY, Subalgebra.coe_add, add_ab, ab_of_pure (hKb Y), zero_add,
          coe_πab, piab_apply]
        rfl
      · intro A hA hne
        obtain ⟨⟨hAY, hAp⟩, hdA⟩ := mem_sY.1 hA
        refine ab_of_pure (mul_mem (prod_mem fun b _ => hI' b) (prod_mem fun Z hZ => ?_))
        have hnD : ¬ D ⊆ Z := by
          intro hDZ
          apply hne
          have hZA := subset_of_mem_comp hZ
          have hAD : A ∪ D = A := union_eq_left.2 (hDZ.trans hZA)
          have : dComp j D z0 A = Z := by
            unfold dComp; rw [hAD]; exact compOf_eq_of_mem_comp hZ (hDZ hz0)
          exact subset_antisymm hAY (hdA ▸ this ▸ hZA)
        show Kb Z + kRed j D z0 I K Z ∈ PB
        rw [kRed_of_not I K hnD, add_zero]; exact hKb Z
    rw [gZO_dComp hD hz0 I K, gZO_dComp hD hz0 I' K', ab_sumO, ab_sumO]
    refine sum_congr rfl fun Y _ => ?_
    rcases (sY j D z0 Y).eq_empty_or_nonempty with h | ⟨A0, hA0⟩
    · rw [h, sum_empty, sum_empty]
    obtain ⟨hYc, hDY, -⟩ := hSY Y A0 hA0
    rw [ab_sumO, ab_sumO]
    have e1 : ∀ A ∈ sY j D z0 Y,
        ((∑ B ∈ tY j Y, (bpowO j I (Y \ A) * KextO j K A) *
          (bpowO j I ((univ \ Y) \ B) * KextO j K B) : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
        ((bpowO j I (Y \ A) * KextO j K A : OE c (Lam d L N)) : SA c (Lam d L N)).ab *
          ∑ B ∈ tY j Y, ((bpowO j I' ((univ \ Y) \ B) * KextO j K' B : OE c (Lam d L N)) :
            SA c (Lam d L N)).e := by
      intro A _
      rw [ab_sumO, mul_sum]
      refine sum_congr rfl fun B hB => ?_
      obtain ⟨hf1, hf2⟩ := hfar Y B hDY hYc.1 hB
      rw [hf1, ab_mul_pure _ hf2]
    have e2 : ∀ A ∈ sY j D z0 Y,
        ((∑ B ∈ tY j Y, (bpowO j I' (Y \ A) * KextO j K' A) *
          (bpowO j I' ((univ \ Y) \ B) * KextO j K' B) : OE c (Lam d L N)) :
            SA c (Lam d L N)).ab =
        ((bpowO j I' (Y \ A) * KextO j K' A : OE c (Lam d L N)) : SA c (Lam d L N)).ab *
          ∑ B ∈ tY j Y, ((bpowO j I' ((univ \ Y) \ B) * KextO j K' B : OE c (Lam d L N)) :
            SA c (Lam d L N)).e := by
      intro A _
      rw [ab_sumO, mul_sum]
      refine sum_congr rfl fun B hB => ?_
      rw [ab_mul_pure _ (hfar Y B hDY hYc.1 hB).2]
    rw [sum_congr rfl e1, sum_congr rfl e2, ← sum_mul, ← sum_mul, hloc Y]

end Sect

end

end Obs2
