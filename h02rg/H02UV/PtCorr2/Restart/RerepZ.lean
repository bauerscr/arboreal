import Obs2.Map.ExactStep
import Obs2.Map.ConstSplit

/-!
# Re-representation of block factors in the polymer activity: an exact `Z`-identity

Let `I, I'` be two block families with `I(B) = I'(B) + δ(B)` for every `j`-block `B`, where the
corrections multiply to zero, `δ(B)δ(B') = 0` (e.g. `δ(B) = -Δ(B)I'(B)` with `Δ(B)` a pure `σ_a`
element, `σ_a² = 0`). Put (`rrK`)

  `K'(U) = K^U + ∑_{B ∈ 𝓑_j(U)} δ(B) K^{U∖B}`,   `K^U = ∏_{Y ∈ Comp(U)} K(Y)`.

Then **`rr_gZO`**: `Z_j = ∑_X I^{Λ∖X}K^X = ∑_U I'^{Λ∖U}K'^U` exactly. The proof: `K'` is
multiplicative on non-touching polymers (`rr_mul`, using `δδ = 0`), so `K'^U = K'(U)`
(`rr_KextO`); `I^S = I'^S + ∑_{B ⊆ S} δ(B) I'^{S∖B}` (`rr_bpowO_add`); the extra terms are matched
by the bijection `X ↦ X ∪ B` between polymers avoiding `B` and polymers containing `B`.

`rr_gZO_V`: the instance `I = e^{-V}(1 + 𝒲)`, `I' = e^{-V'}(1 + 𝒲)` with `V - V' = Δ` observable and
`ΔΔ = 0`; then `δ(B) = -Δ(B) I'(B)`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Products with square-zero corrections -/

theorem rr_prod_add {ι R : Type*} [CommRing R] [DecidableEq ι] (s : Finset ι) (x y : ι → R)
    (hy : ∀ i k, y i * y k = 0) :
    ∏ i ∈ s, (x i + y i) = ∏ i ∈ s, x i + ∑ i ∈ s, y i * ∏ k ∈ s.erase i, x k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h0 : y a * ∑ i ∈ s, y i * ∏ k ∈ s.erase i, x k = 0 := by
      rw [mul_sum]
      exact sum_eq_zero fun i _ => by rw [← mul_assoc, hy, zero_mul]
    have hs : ∑ i ∈ s, y i * ∏ k ∈ (insert a s).erase i, x k =
        x a * ∑ i ∈ s, y i * ∏ k ∈ s.erase i, x k := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hne : i ≠ a := fun h => ha (h ▸ hi)
      rw [erase_insert_of_ne hne.symm, prod_insert (fun h => ha (mem_of_mem_erase h))]
      ring
    rw [prod_insert ha, prod_insert ha, sum_insert ha, erase_insert ha, hs, ih]
    linear_combination h0

theorem rr_blocks_sdiff (j : ℕ) (S : Finset (Lam d L N)) (b : Fin d → ℕ) :
    blocks j (S \ blockSet j b) = (blocks j S).erase b := by
  ext b'
  simp only [mem_erase, mem_blocks, mem_sdiff, mem_blockSet]
  constructor
  · rintro ⟨x, ⟨hx, hxb⟩, rfl⟩
    exact ⟨hxb, x, hx, rfl⟩
  · rintro ⟨hne, x, hx, rfl⟩
    exact ⟨x, ⟨hx, hne⟩, rfl⟩

/-- **`I^S = I'^S + ∑_{B ⊆ S} δ(B) I'^{S∖B}`** for `I = I' + δ`, `δδ = 0`. -/
theorem rr_bpowO_add (j : ℕ) {I I' δ : OFam c d L N} (hI : ∀ b, I b = I' b + δ b)
    (hδ : ∀ b b', δ b * δ b' = 0) (S : Finset (Lam d L N)) :
    bpowO j I S = bpowO j I' S + ∑ b ∈ blocks j S, δ b * bpowO j I' (S \ blockSet j b) := by
  rw [bpowO, bpowO]
  simp only [hI]
  rw [rr_prod_add _ _ _ hδ]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  rw [bpowO, rr_blocks_sdiff]

/-! ### The re-represented activity -/

/-- **The re-represented activity** `K'(U) = K^U + ∑_{B ∈ 𝓑_j(U)} δ(B) K^{U∖B}`. -/
def rrK (j : ℕ) (δ : OFam c d L N) (K : OAct c d L N) : OAct c d L N :=
  fun U => KextO j K U + ∑ b ∈ blocks j U, δ b * KextO j K (U \ blockSet j b)

theorem rr_disjoint_of_not_touch {A B : Finset (Lam d L N)} (h : ¬ Touch A B) : Disjoint A B := by
  rw [disjoint_left]
  intro x hA hB
  exact h ⟨x, hA, x, hB, by rw [sub_self]; exact supNorm_zero'⟩

theorem rr_not_mem_blocks {j : ℕ} {A B : Finset (Lam d L N)} (hA : IsPolymer j A)
    (hAB : Disjoint A B) {b : Fin d → ℕ} (hb : b ∈ blocks j B) : b ∉ blocks j A := by
  intro hb'
  obtain ⟨y, hy, rfl⟩ := mem_blocks.1 hb
  exact disjoint_left.1 hAB (mem_of_blk_mem hA hb') hy

theorem rr_union_sdiff {j : ℕ} {A B : Finset (Lam d L N)}
    {b : Fin d → ℕ} (hb : b ∉ blocks j B) : (A ∪ B) \ blockSet j b = (A \ blockSet j b) ∪ B := by
  ext x
  simp only [mem_union, mem_sdiff, mem_blockSet]
  constructor
  · rintro ⟨h | h, hx⟩
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr h
  · rintro (⟨h, hx⟩ | h)
    · exact ⟨Or.inl h, hx⟩
    · exact ⟨Or.inr h, fun hx => hb (hx ▸ blk_mem_blocks h)⟩

/-- **`K'` is multiplicative on non-touching polymers** (`δδ = 0`). -/
theorem rr_mul (j : ℕ) {δ : OFam c d L N} (hδ : ∀ b b', δ b * δ b' = 0) (K : OAct c d L N)
    {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B) (h : ¬ Touch A B) :
    rrK j δ K (A ∪ B) = rrK j δ K A * rrK j δ K B := by
  have hAB := rr_disjoint_of_not_touch h
  have hbl : Disjoint (blocks j A) (blocks j B) :=
    disjoint_left.2 fun b hbA hbB => rr_not_mem_blocks hA hAB hbB hbA
  have hsA : ∀ b ∈ blocks j A, KextO j K ((A ∪ B) \ blockSet j b) =
      KextO j K (A \ blockSet j b) * KextO j K B := fun b hb => by
    rw [rr_union_sdiff fun hb' => disjoint_left.1 hbl hb hb',
      KextO_union j K (IsPolymer.sdiff hA (isPolymer_blockSet j b)) hB
        fun ht => h (touch_mono sdiff_subset (subset_refl B) ht)]
  have hsB : ∀ b ∈ blocks j B, KextO j K ((A ∪ B) \ blockSet j b) =
      KextO j K A * KextO j K (B \ blockSet j b) := fun b hb => by
    rw [union_comm, rr_union_sdiff fun hb' => disjoint_left.1 hbl hb' hb, union_comm,
      KextO_union j K hA (IsPolymer.sdiff hB (isPolymer_blockSet j b))
        fun ht => h (touch_mono (subset_refl A) sdiff_subset ht)]
  have h0 : (∑ b ∈ blocks j A, δ b * KextO j K (A \ blockSet j b)) *
      (∑ b ∈ blocks j B, δ b * KextO j K (B \ blockSet j b)) = 0 := by
    rw [sum_mul]
    refine sum_eq_zero fun b _ => ?_
    rw [mul_sum]
    refine sum_eq_zero fun b' _ => ?_
    linear_combination (KextO j K (A \ blockSet j b) * KextO j K (B \ blockSet j b')) * hδ b b'
  unfold rrK
  rw [KextO_union j K hA hB h, blocks_union, sum_union hbl,
    sum_congr rfl fun b hb => by rw [hsA b hb],
    sum_congr (s₁ := blocks j B) rfl fun b hb => by rw [hsB b hb]]
  have e1 : ∑ b ∈ blocks j A, δ b * (KextO j K (A \ blockSet j b) * KextO j K B) =
      (∑ b ∈ blocks j A, δ b * KextO j K (A \ blockSet j b)) * KextO j K B := by
    rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
  have e2 : ∑ b ∈ blocks j B, δ b * (KextO j K A * KextO j K (B \ blockSet j b)) =
      KextO j K A * ∑ b ∈ blocks j B, δ b * KextO j K (B \ blockSet j b) := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [e1, e2]
  linear_combination (-1 : OE c (Lam d L N)) * h0

/-- **`K'^U = K'(U)`** on polymers. -/
theorem rr_KextO (j : ℕ) {δ : OFam c d L N} (hδ : ∀ b b', δ b * δ b' = 0) (K : OAct c d L N)
    {U : Finset (Lam d L N)} (hU : IsPolymer j U) : KextO j (rrK j δ K) U = rrK j δ K U :=
  KextO_eq_of_union j _ (by simp [rrK, KextO_empty, blocks])
    (fun _ _ hA hB h => rr_mul j hδ K hA hB h) hU

/-- `K^U` only depends on the values of `K` on connected polymers. -/
theorem rr_KextO_congr (j : ℕ) {K K' : OAct c d L N} (h : ∀ Y, IsConn j Y → K Y = K' Y)
    {U : Finset (Lam d L N)} (hU : IsPolymer j U) : KextO j K U = KextO j K' U :=
  prod_congr rfl fun Y hY => h Y (isConn_of_mem_comp hU hY)

/-! ### The `Z`-identity -/

theorem rr_sum_blocks (j : ℕ) (S : Finset (Lam d L N)) (f : (Fin d → ℕ) → OE c (Lam d L N)) :
    ∑ b ∈ blocks j S, f b = ∑ b ∈ blockIdx (L := L) (N := N) j, if b ∈ blocks j S then f b else 0 := by
  rw [sum_ite_mem, blockIdx, inter_eq_right.2 (blocks_mono (subset_univ S))]

/-- **The exact re-representation**: `∑_X I^{Λ∖X}K^X = ∑_U I'^{Λ∖U}K'^U` for `I = I' + δ`,
`δδ = 0`, `K' = rrK j δ K`. -/
theorem rr_gZO (j : ℕ) {I I' δ : OFam c d L N} (hI : ∀ b, I b = I' b + δ b)
    (hδ : ∀ b b', δ b * δ b' = 0) (K : OAct c d L N) :
    gZO j I K = gZO j I' (rrK j δ K) := by
  classical
  have hL : gZO j I K = ∑ X ∈ Pj j (univ : Finset (Lam d L N)),
      (bpowO j I' (univ \ X) * KextO j K X + ∑ b ∈ blockIdx (L := L) (N := N) j,
        if b ∈ blocks j (univ \ X) then
          δ b * bpowO j I' (univ \ (X ∪ blockSet j b)) * KextO j K X else 0) := by
    refine sum_congr rfl fun X _ => ?_
    rw [rr_bpowO_add j hI hδ, add_mul, sum_mul, rr_sum_blocks]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [sdiff_sdiff_left]; rfl
    · rfl
  have hR : gZO j I' (rrK j δ K) = ∑ U ∈ Pj j (univ : Finset (Lam d L N)),
      (bpowO j I' (univ \ U) * KextO j K U + ∑ b ∈ blockIdx (L := L) (N := N) j,
        if b ∈ blocks j U then
          bpowO j I' (univ \ U) * (δ b * KextO j K (U \ blockSet j b)) else 0) := by
    refine sum_congr rfl fun U hU => ?_
    rw [rr_KextO j hδ K (mem_Pj.1 hU).2, rrK, mul_add, mul_sum, rr_sum_blocks]
  rw [hL, hR, sum_add_distrib, sum_add_distrib, sum_comm, sum_comm (s := Pj j univ)]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_filter, ← sum_filter]
  refine sum_nbij' (fun X => X ∪ blockSet j b) (fun U => U \ blockSet j b) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    obtain ⟨hXP, hb⟩ := mem_filter.1 hX
    have hXp := (mem_Pj.1 hXP).2
    obtain ⟨x, hx, hxb⟩ := mem_blocks.1 hb
    refine mem_filter.2 ⟨mem_Pj.2 ⟨subset_univ _, IsPolymer.union hXp (isPolymer_blockSet j b)⟩, ?_⟩
    exact mem_blocks.2 ⟨x, mem_union_right _ (mem_blockSet.2 hxb), hxb⟩
  · intro U hU
    obtain ⟨hUP, hb⟩ := mem_filter.1 hU
    have hUp := (mem_Pj.1 hUP).2
    obtain ⟨x, hx, hxb⟩ := mem_blocks.1 hb
    refine mem_filter.2 ⟨mem_Pj.2 ⟨subset_univ _, IsPolymer.sdiff hUp (isPolymer_blockSet j b)⟩, ?_⟩
    exact mem_blocks.2 ⟨x, by simp [mem_blockSet.2 hxb], hxb⟩
  · intro X hX
    obtain ⟨hXP, hb⟩ := mem_filter.1 hX
    have hXp := (mem_Pj.1 hXP).2
    obtain ⟨x, hx, hxb⟩ := mem_blocks.1 hb
    refine union_sdiff_cancel_right (disjoint_left.2 fun y hy hyb => ?_)
    exact (mem_sdiff.1 hx).2 (hXp y x ((mem_blockSet.1 hyb).trans hxb.symm) hy)
  · intro U hU
    obtain ⟨hUP, hb⟩ := mem_filter.1 hU
    exact sdiff_union_of_subset (blockSet_subset (mem_Pj.1 hUP).2 hb)
  · intro X hX
    obtain ⟨hXP, hb⟩ := mem_filter.1 hX
    have hXp := (mem_Pj.1 hXP).2
    obtain ⟨x, hx, hxb⟩ := mem_blocks.1 hb
    have hd : Disjoint X (blockSet j b) := disjoint_left.2 fun y hy hyb =>
      (mem_sdiff.1 hx).2 (hXp y x ((mem_blockSet.1 hyb).trans hxb.symm) hy)
    rw [union_sdiff_cancel_right hd]
    ring

/-! ### The instance `I = e^{-V}(1 + 𝒲)` -/

section Ib

/-- **Re-representation of a change of the block polynomial**: if `V - V' = Δ` is observable with
`ΔΔ = 0`, then `Z_j(V, 𝒲, K) = Z_j(V', 𝒲, K')`, `K' = rrK j δ K`, `δ(B) = -Δ(B) I'(B)`. -/
theorem rr_gZO_V (j : ℕ) {V V' : OFam c d L N} (W : OFam c d L N) (K : OAct c d L N)
    (hΔ : ∀ b, bulk (V b - V' b) = 0) (hΔ2 : ∀ b b', (V b - V' b) * (V b' - V' b') = 0) :
    gZO j (IbO V W) K =
      gZO j (IbO V' W) (rrK j (fun b => -(V b - V' b) * IbO V' W b) K) := by
  refine rr_gZO j (fun b => ?_) (fun b b' => ?_) K
  · have hV : -V b = -V' b + -(V b - V' b) := by abel
    have hn : bulk (-(V b - V' b)) = 0 := by rw [map_neg, hΔ b, neg_zero]
    rw [IbO, IbO, hV, oexp_add_right_obs _ hn, oexp_of_obs hn, neg_sq, sq, hΔ2 b b, smul_zero]
    ring
  · linear_combination (IbO V' W b * IbO V' W b') * hΔ2 b b'

end Ib

end

end PtCorr2
