import Flow.Embed

/-!
# Geometry of `emb` near the origin

For points of `Λ_N` with `16 |x|_∞ ≤ 5 L^N` (and scales with `16 L^j ≤ L^N`), `emb` preserves
`j`-blocks (`bemb`), polymers, touching, connectedness, small sets, components, `𝒫_j`,
closures and small set neighbourhoods.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L : ℕ} [NeZero L] {N M : ℕ}

/-- The induced map on block indices. -/
def bemb (L N M j : ℕ) [NeZero L] (b : Fin d → ℕ) : Fin d → ℕ :=
  open Classical in
  if hb : ∃ x : Lam d L N, blk j x = b then blk j (emb N M hb.choose) else b

/-- The inverse map on block indices. -/
def bpre (L N M j : ℕ) [NeZero L] (b : Fin d → ℕ) : Fin d → ℕ :=
  open Classical in
  if hb : ∃ y : Lam d L M, blk j y = b then blk j (emb M N hb.choose) else b

theorem emb_mem_image (hNM : N ≤ M) {X : Finset (Lam d L N)} {x : Lam d L N} :
    emb N M x ∈ X.image (emb N M) ↔ x ∈ X :=
  (emb_injective' hNM).mem_finset_image

theorem card_image_emb (hNM : N ≤ M) (X : Finset (Lam d L N)) :
    (X.image (emb N M)).card = X.card :=
  card_image_of_injective _ (emb_injective' hNM)

theorem image_emb_injective (hNM : N ≤ M) :
    Function.Injective fun X : Finset (Lam d L N) => X.image (emb N M) :=
  image_injective (emb_injective' hNM)

theorem image_emb_subset_iff (hNM : N ≤ M) {X Y : Finset (Lam d L N)} :
    X.image (emb N M) ⊆ Y.image (emb N M) ↔ X ⊆ Y :=
  image_subset_image_iff (emb_injective' hNM)

section Scale

variable (hNM : N ≤ M) {j : ℕ} (hj : j ≤ N) (hP : 16 * L ^ j ≤ L ^ N)
include hNM hj hP

theorem pos_pow : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j

/-- A point of `Λ_M` in the block of `emb x` is the image of a point in the block of `x`. -/
theorem pre_of_blk {x : Lam d L N} (hx : 16 * supNorm x ≤ 6 * L ^ N) {y : Lam d L M}
    (h : blk j y = blk j (emb N M x)) :
    emb N M (emb M N y) = y ∧ blk j (emb M N y) = blk j x ∧
      16 * supNorm (emb M N y) ≤ 7 * L ^ N := by
  have h1 := supNorm_le_of_blk_eq h.symm
  rw [supNorm_emb hNM] at h1
  have := pos_pow hNM hj hP
  have hy : 2 * supNorm y < L ^ N := by omega
  have e1 := emb_emb' (N := N) y hy
  have e2 := supNorm_emb' (N := N) y hy
  refine ⟨e1, ?_, by omega⟩
  rw [← blk_emb_iff hNM hj (by omega) (by omega) (by omega), e1, h]

theorem blk_emb_of_blk {x y : Lam d L N} (hx : 16 * supNorm x ≤ 6 * L ^ N)
    (h : blk j y = blk j x) : blk j (emb N M y) = blk j (emb N M x) := by
  have := supNorm_le_of_blk_eq h.symm
  exact (blk_emb_iff hNM hj (by omega) (by omega) (by omega)).2 h

theorem bemb_blk {x : Lam d L N} (hx : 16 * supNorm x ≤ 6 * L ^ N) :
    bemb L N M j (blk j x) = blk j (emb N M x) := by
  have hb : ∃ y : Lam d L N, blk j y = blk j x := ⟨x, rfl⟩
  rw [bemb, dif_pos hb]
  exact blk_emb_of_blk hNM hj hP hx hb.choose_spec

theorem bpre_blk {x : Lam d L N} (hx : 16 * supNorm x ≤ 6 * L ^ N) :
    bpre L N M j (blk j (emb N M x)) = blk j x := by
  have hb : ∃ y : Lam d L M, blk j y = blk j (emb N M x) := ⟨_, rfl⟩
  rw [bpre, dif_pos hb]
  exact (pre_of_blk hNM hj hP hx hb.choose_spec).2.1

theorem bpre_bemb {x : Lam d L N} (hx : 16 * supNorm x ≤ 6 * L ^ N) :
    bpre L N M j (bemb L N M j (blk j x)) = blk j x := by
  rw [bemb_blk hNM hj hP hx, bpre_blk hNM hj hP hx]

theorem blockSet_bemb {x : Lam d L N} (hx : 16 * supNorm x ≤ 6 * L ^ N) :
    blockSet j (bemb L N M j (blk j x)) = (blockSet (L := L) (N := N) j (blk j x)).image (emb N M) := by
  rw [bemb_blk hNM hj hP hx]
  ext y
  rw [Loc.mem_blockSet, mem_image]
  constructor
  · intro h
    obtain ⟨e1, e2, -⟩ := pre_of_blk hNM hj hP hx h
    exact ⟨_, Loc.mem_blockSet.2 e2, e1⟩
  · rintro ⟨z, hz, rfl⟩
    exact blk_emb_of_blk hNM hj hP hx (Loc.mem_blockSet.1 hz)

theorem isPolymer_image_iff {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N) :
    IsPolymer j (X.image (emb N M)) ↔ IsPolymer j X := by
  constructor
  · intro h x y hxy hx
    have := h _ (emb N M y) (blk_emb_of_blk hNM hj hP (hX x hx) hxy.symm).symm
      (mem_image_of_mem _ hx)
    exact (emb_mem_image hNM).1 this
  · intro h x' y' hxy hx'
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hx'
    obtain ⟨e1, e2, -⟩ := pre_of_blk hNM hj hP (hX x hx) hxy.symm
    rw [← e1]
    exact mem_image_of_mem _ (h x _ e2.symm hx)

theorem touch_image_iff {X Y : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N)
    (hY : ∀ y ∈ Y, 16 * supNorm y ≤ 6 * L ^ N) :
    Touch (X.image (emb N M)) (Y.image (emb N M)) ↔ Touch X Y := by
  have hn := pos_pow hNM hj hP
  constructor
  · rintro ⟨x', hx', y', hy', h⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hy'
    exact ⟨x, hx, y, hy, (supNorm_sub_le_emb hNM x y).trans h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    refine ⟨_, mem_image_of_mem _ hx, _, mem_image_of_mem _ hy, ?_⟩
    have := hX x hx
    have := hY y hy
    rw [supNorm_emb_sub hNM (by omega)]
    exact h

theorem blocks_image {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N) :
    blocks j (X.image (emb N M)) = (blocks j X).image (bemb L N M j) := by
  rw [blocks, blocks, image_image, image_image]
  exact image_congr fun x hx => (bemb_blk hNM hj hP (hX x hx)).symm

theorem bemb_injOn {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N) :
    Set.InjOn (bemb L N M j) (blocks j X : Set (Fin d → ℕ)) := by
  intro b hb b' hb' e
  obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hb)
  obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_coe.1 hb')
  rw [← bpre_bemb hNM hj hP (hX x hx), ← bpre_bemb hNM hj hP (hX y hy), e]

theorem nb_image {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N) :
    nb j (X.image (emb N M)) = nb j X := by
  rw [nb, nb, blocks_image hNM hj hP hX, card_image_of_injOn (bemb_injOn hNM hj hP hX)]

theorem blockAdj_image_iff {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N)
    {x y : Lam d L N} (hx : x ∈ X) (hy : y ∈ X) :
    BlockAdj j (X.image (emb N M)) (blk j (emb N M x)) (blk j (emb N M y)) ↔
      BlockAdj j X (blk j x) (blk j y) := by
  have hbx : ∀ z ∈ blockSet (L := L) (N := N) j (blk j x), 16 * supNorm z ≤ 6 * L ^ N :=
    fun z hz => by
      have := supNorm_le_of_blk_eq (Loc.mem_blockSet.1 hz).symm
      have := hX x hx
      omega
  have hby : ∀ z ∈ blockSet (L := L) (N := N) j (blk j y), 16 * supNorm z ≤ 6 * L ^ N :=
    fun z hz => by
      have := supNorm_le_of_blk_eq (Loc.mem_blockSet.1 hz).symm
      have := hX y hy
      omega
  have ex : 16 * supNorm x ≤ 6 * L ^ N := by have := hX x hx; omega
  have ey : 16 * supNorm y ≤ 6 * L ^ N := by have := hX y hy; omega
  have h1 : blk j (emb N M x) ∈ blocks j (X.image (emb N M)) :=
    blk_mem_blocks (mem_image_of_mem _ hx)
  have h2 : blk j (emb N M y) ∈ blocks j (X.image (emb N M)) :=
    blk_mem_blocks (mem_image_of_mem _ hy)
  unfold BlockAdj
  rw [← bemb_blk hNM hj hP ex, ← bemb_blk hNM hj hP ey, blockSet_bemb hNM hj hP ex,
    blockSet_bemb hNM hj hP ey, touch_image_iff hNM hj hP hbx hby,
    bemb_blk hNM hj hP ex, bemb_blk hNM hj hP ey]
  simp only [h1, h2, blk_mem_blocks hx, blk_mem_blocks hy, true_and]

theorem rtg_image_iff {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N)
    {x y : Lam d L N} (hx : x ∈ X) (hy : y ∈ X) :
    Relation.ReflTransGen (BlockAdj j (X.image (emb N M))) (blk j (emb N M x))
      (blk j (emb N M y)) ↔ Relation.ReflTransGen (BlockAdj j X) (blk j x) (blk j y) := by
  have hX6 : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N := fun x hx => by have := hX x hx; omega
  constructor
  · intro h
    have := Relation.ReflTransGen.lift (bpre L N M j) (fun a b hab => by
      have ha := hab.1
      have hb := hab.2.1
      rw [blocks_image hNM hj hP hX6] at ha hb
      obtain ⟨a₀, ha₀, rfl⟩ := mem_image.1 ha
      obtain ⟨b₀, hb₀, rfl⟩ := mem_image.1 hb
      obtain ⟨u, hu, rfl⟩ := mem_image.1 ha₀
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hb₀
      rw [bemb_blk hNM hj hP (hX6 u hu), bemb_blk hNM hj hP (hX6 v hv)] at hab ⊢
      rw [bpre_blk hNM hj hP (hX6 u hu), bpre_blk hNM hj hP (hX6 v hv)]
      exact (blockAdj_image_iff hNM hj hP hX hu hv).1 hab) h
    rwa [bpre_blk hNM hj hP (hX6 x hx), bpre_blk hNM hj hP (hX6 y hy)] at this
  · intro h
    have := Relation.ReflTransGen.lift (bemb L N M j) (fun a b hab => by
      have ha := hab.1
      have hb := hab.2.1
      obtain ⟨u, hu, rfl⟩ := mem_image.1 ha
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hb
      rw [bemb_blk hNM hj hP (hX6 u hu), bemb_blk hNM hj hP (hX6 v hv)]
      exact (blockAdj_image_iff hNM hj hP hX hu hv).2 hab) h
    rwa [bemb_blk hNM hj hP (hX6 x hx), bemb_blk hNM hj hP (hX6 y hy)] at this

theorem isConnected_image_iff {X : Finset (Lam d L N)}
    (hX : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N) :
    Loc.IsConnected j (X.image (emb N M)) ↔ Loc.IsConnected j X := by
  unfold Loc.IsConnected
  rw [image_nonempty]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h b hb b' hb'
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hb'
    exact (rtg_image_iff hNM hj hP hX hx hy).1
      (h _ (blk_mem_blocks (mem_image_of_mem _ hx)) _ (blk_mem_blocks (mem_image_of_mem _ hy)))
  · intro h b hb b' hb'
    obtain ⟨x', hx', rfl⟩ := mem_image.1 hb
    obtain ⟨y', hy', rfl⟩ := mem_image.1 hb'
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hy'
    exact (rtg_image_iff hNM hj hP hX hx hy).2 (h _ (blk_mem_blocks hx) _ (blk_mem_blocks hy))

theorem isSmall_image_iff {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N) :
    IsSmall j (X.image (emb N M)) ↔ IsSmall j X := by
  have hX6 : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N := fun x hx => by have := hX x hx; omega
  have := nb_image hNM hj hP hX6
  unfold nb at this
  unfold IsSmall
  rw [isPolymer_image_iff hNM hj hP hX6, isConnected_image_iff hNM hj hP hX, this]

theorem isConn_image_iff {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N) :
    IsConn j (X.image (emb N M)) ↔ IsConn j X := by
  have hX6 : ∀ x ∈ X, 16 * supNorm x ≤ 6 * L ^ N := fun x hx => by have := hX x hx; omega
  unfold IsConn
  rw [isPolymer_image_iff hNM hj hP hX6, isConnected_image_iff hNM hj hP hX]

theorem compOf_image {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N)
    {x : Lam d L N} (hx : x ∈ X) :
    compOf j (X.image (emb N M)) (blk j (emb N M x)) = (compOf j X (blk j x)).image (emb N M) := by
  classical
  ext y'
  simp only [compOf, mem_filter, mem_image]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    exact ⟨y, ⟨hy, (rtg_image_iff hNM hj hP hX hx hy).1 h⟩, rfl⟩
  · rintro ⟨y, ⟨hy, h⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, (rtg_image_iff hNM hj hP hX hx hy).2 h⟩

theorem comp_image {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N) :
    Comp j (X.image (emb N M)) = (Comp j X).image fun Y => Y.image (emb N M) := by
  rw [Comp, Comp, blocks, blocks, image_image, image_image, image_image, image_image]
  exact image_congr fun x hx => compOf_image hNM hj hP hX hx

theorem Pj_image {W : Finset (Lam d L N)} (hW : ∀ x ∈ W, 16 * supNorm x ≤ 5 * L ^ N) :
    Pj j (W.image (emb N M)) = (Pj j W).image fun Y => Y.image (emb N M) := by
  classical
  have hW6 : ∀ x ∈ W, 16 * supNorm x ≤ 6 * L ^ N := fun x hx => by have := hW x hx; omega
  ext Y'
  rw [mem_image]
  constructor
  · intro hY'
    obtain ⟨h1, h2⟩ := mem_Pj.1 hY'
    set Y := W.filter fun w => emb N M w ∈ Y'
    have hYW : Y ⊆ W := filter_subset _ _
    have e : Y.image (emb N M) = Y' := by
      ext z
      simp only [mem_image, mem_filter, Y]
      constructor
      · rintro ⟨w, ⟨-, hw⟩, rfl⟩; exact hw
      · intro hz
        obtain ⟨w, hw, rfl⟩ := mem_image.1 (h1 hz)
        exact ⟨w, ⟨hw, hz⟩, rfl⟩
    refine ⟨Y, mem_Pj.2 ⟨hYW, ?_⟩, e⟩
    rw [← isPolymer_image_iff hNM hj hP fun x hx => hW6 x (hYW hx), e]
    exact h2
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨h1, h2⟩ := mem_Pj.1 hY
    exact mem_Pj.2 ⟨image_subset_image h1,
      (isPolymer_image_iff hNM hj hP fun x hx => hW6 x (h1 hx)).2 h2⟩

theorem blkfilter_image {A : Finset (Lam d L N)} (hA : ∀ x ∈ A, 16 * supNorm x ≤ 6 * L ^ N) :
    (univ : Finset (Lam d L M)).filter (fun y => blk j y ∈ blocks j (A.image (emb N M))) =
      ((univ : Finset (Lam d L N)).filter fun y => blk j y ∈ blocks j A).image (emb N M) := by
  ext y'
  simp only [mem_filter, mem_univ, true_and, mem_image, blocks, image_image]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨e1, e2, -⟩ := pre_of_blk hNM hj hP (hA a ha) h.symm
    exact ⟨_, ⟨a, ha, e2.symm⟩, e1⟩
  · rintro ⟨y, ⟨a, ha, h⟩, rfl⟩
    exact ⟨a, ha, (blk_emb_of_blk hNM hj hP (hA a ha) h.symm).symm⟩

/-- Pulling back a small set containing the block of `emb x₀`. -/
theorem small_pullback (h2d : 16 * (2 ^ d * L ^ j) ≤ L ^ N) {x₀ : Lam d L N}
    (hx₀ : 16 * supNorm x₀ ≤ 5 * L ^ N)
    (hB : ∀ y : Lam d L N, supNorm (y - x₀) ≤ 2 ^ d * L ^ j → 16 * supNorm y ≤ 5 * L ^ N)
    {S' : Finset (Lam d L M)} (hS' : IsSmall j S') (hb : blockSet j (blk j (emb N M x₀)) ⊆ S') :
    ∃ T : Finset (Lam d L N), IsSmall j T ∧ T.image (emb N M) = S' ∧
      blockSet (L := L) (N := N) j (blk j x₀) ⊆ T ∧
      ∀ y ∈ T, supNorm (y - x₀) ≤ 2 ^ d * L ^ j := by
  have hS1 : ∀ z ∈ S', supNorm (z - emb N M x₀) ≤ 2 ^ d * L ^ j := fun z hz =>
    supNorm_le_of_isSmall hS' hz (hb (mem_blockSet_blk j _))
  have hS2 : ∀ z ∈ S', 2 * supNorm z < L ^ N := fun z hz => by
    have h1 := hS1 z hz
    have h2 := supNorm_add_le (z - emb N M x₀) (emb N M x₀)
    rw [sub_add_cancel, supNorm_emb hNM] at h2
    have := pos_pow hNM hj hP
    omega
  set T := S'.image (emb M N)
  have eT : T.image (emb N M) = S' := by
    rw [image_image]
    conv_rhs => rw [← image_id (s := S')]
    exact image_congr fun z hz => emb_emb' (N := N) z (hS2 z hz)
  have hT : ∀ y ∈ T, supNorm (y - x₀) ≤ 2 ^ d * L ^ j := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
    refine (supNorm_sub_le_emb hNM _ _).trans ?_
    rw [emb_emb' (N := N) z (hS2 z hz)]
    exact hS1 z hz
  refine ⟨T, ?_, eT, ?_, hT⟩
  · rw [← isSmall_image_iff hNM hj hP fun y hy => hB y (hT y hy), eT]; exact hS'
  · intro w hw
    have hw' : emb N M w ∈ S' := hb (Loc.mem_blockSet.2
      (blk_emb_of_blk hNM hj hP (by omega) (Loc.mem_blockSet.1 hw)))
    rw [← eT] at hw'
    exact (emb_mem_image hNM).1 hw'

theorem nbhd_image (h2d : 16 * (2 ^ d * L ^ j) ≤ L ^ N) {B : Finset (Lam d L N)}
    (hB : ∀ y : Lam d L N, (∃ x ∈ B, supNorm (y - x) ≤ 2 ^ d * L ^ j) →
      16 * supNorm y ≤ 5 * L ^ N) :
    nbhd j (B.image (emb N M)) = (nbhd j B).image (emb N M) := by
  have hB0 : ∀ x ∈ B, 16 * supNorm x ≤ 5 * L ^ N := fun x hx =>
    hB x ⟨x, hx, by rw [sub_self, supNorm_zero]; exact Nat.zero_le _⟩
  ext y'
  simp only [nbhd, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨S', hS', hyS', b', hb', hbS'⟩
    obtain ⟨x', hx', rfl⟩ := mem_image.1 hb'
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hx'
    obtain ⟨T, hT, eT, hbT, -⟩ := small_pullback hNM hj hP h2d (hB0 x₀ hx₀)
      (fun y hy => hB y ⟨x₀, hx₀, hy⟩) hS' hbS'
    rw [← eT] at hyS'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hyS'
    exact ⟨y, ⟨T, hT, hy, blk j x₀, blk_mem_blocks hx₀, hbT⟩, rfl⟩
  · rintro ⟨y, ⟨T, hT, hyT, b, hb, hbT⟩, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hb
    have hT' : ∀ z ∈ T, 16 * supNorm z ≤ 5 * L ^ N := fun z hz =>
      hB z ⟨x₀, hx₀, supNorm_le_of_isSmall hT hz (hbT (mem_blockSet_blk j x₀))⟩
    have ex : 16 * supNorm x₀ ≤ 6 * L ^ N := by have := hB0 x₀ hx₀; omega
    refine ⟨T.image (emb N M), (isSmall_image_iff hNM hj hP hT').2 hT, mem_image_of_mem _ hyT,
      blk j (emb N M x₀), blk_mem_blocks (mem_image_of_mem _ hx₀), ?_⟩
    rw [← bemb_blk hNM hj hP ex, blockSet_bemb hNM hj hP ex]
    exact image_subset_image hbT

end Scale

theorem clo_image (hNM : N ≤ M) {j : ℕ} (hj1 : j + 1 ≤ N) (hQ : 16 * L ^ (j + 1) ≤ L ^ N)
    {A : Finset (Lam d L N)} (hA : ∀ x ∈ A, 16 * supNorm x ≤ 6 * L ^ N) :
    clo j (A.image (emb N M)) = (clo j A).image (emb N M) := by
  have := blkfilter_image hNM hj1 hQ hA
  unfold clo
  convert this using 2

end

end Flow
