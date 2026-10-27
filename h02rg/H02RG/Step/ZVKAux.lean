import Step.Polymers

/-!
# Auxiliary facts for Proposition `prop:ZVK`

* elementary facts on blocks and polymers (`blockSet_subset_of_mem_blocks`, `isPolymer_biUnion`,
  `blocks_biUnion_blockSet`, …);
* the binomial expansion over the blocks of a polymer (`prod_add_blocks`, `e:thetaI`);
* functions that are multiplicative over non-touching polymers factor over connected components
  (`eq_prod_comp_of_mul`), in particular `Kext` (`Kext_union`);
* the expansion of a product of sums `∏_c (a_c + ∑_{b ∈ t_c} f(b, c))` as a sum over
  *sections* `𝒳` (sets of pairs `(b, c)` containing each `c` at most once) (`prod_add_sum_eq`);
* `V(X)` is nilpotent (`isNilpotent_VE`) and `e^{-V(X)} = ∏_{B ∈ 𝓑_j(X)} e^{-V(B)}` for polymers
  `X` (`gexp_neg_VE`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

/-! ### Expansion of a product of sums over sections -/

section Expand

variable {α β R : Type*} [DecidableEq α] [DecidableEq β] [CommRing R]

/-- The *sections* over `s` with fibres `t`: sets `𝒳` of pairs `(b, c)` with `c ∈ s`, `b ∈ t c`,
in which each `c` occurs at most once. -/
def Sec (s : Finset α) (t : α → Finset β) : Finset (Finset (β × α)) :=
  (s.biUnion fun c => (t c).image fun b => (b, c)).powerset.filter
    fun 𝒳 => ∀ p ∈ 𝒳, ∀ q ∈ 𝒳, p.2 = q.2 → p = q

theorem mem_Sec {s : Finset α} {t : α → Finset β} {𝒳 : Finset (β × α)} :
    𝒳 ∈ Sec s t ↔ (∀ p ∈ 𝒳, p.2 ∈ s ∧ p.1 ∈ t p.2) ∧
      ∀ p ∈ 𝒳, ∀ q ∈ 𝒳, p.2 = q.2 → p = q := by
  simp only [Sec, mem_filter, mem_powerset]
  refine and_congr_left fun _ => ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · have := h hp
    simp only [mem_biUnion, mem_image] at this
    obtain ⟨c, hc, b, hb, rfl⟩ := this
    exact ⟨hc, hb⟩
  · simp only [mem_biUnion, mem_image]
    exact ⟨p.2, (h p hp).1, p.1, (h p hp).2, rfl⟩

theorem Sec_empty (t : α → Finset β) : Sec (∅ : Finset α) t = {∅} := by
  ext 𝒳
  rw [mem_Sec, mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    exact eq_empty_of_forall_notMem fun p hp => by simpa using (h p hp).1
  · rintro rfl; simp

theorem Sec_insert_filter_not {c : α} {s : Finset α} (hc : c ∉ s) (t : α → Finset β) :
    (Sec (insert c s) t).filter (fun 𝒳 => ¬ ∃ p ∈ 𝒳, p.2 = c) = Sec s t := by
  ext 𝒳
  simp only [mem_filter, mem_Sec, mem_insert, not_exists, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun p hp => ⟨(h1 p hp).1.resolve_left (h3 p hp), (h1 p hp).2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun p hp => ⟨Or.inr (h1 p hp).1, (h1 p hp).2⟩, h2⟩, fun p hp hpc => ?_⟩
    exact hc (hpc ▸ (h1 p hp).1)

theorem Sec_insert_filter {c : α} {s : Finset α} (hc : c ∉ s) (t : α → Finset β) :
    (Sec (insert c s) t).filter (fun 𝒳 => ∃ p ∈ 𝒳, p.2 = c) =
      (t c ×ˢ Sec s t).image fun q => insert (q.1, c) q.2 := by
  ext 𝒳
  simp only [mem_filter, mem_image, mem_product]
  constructor
  · rintro ⟨h𝒳, p, hp, hpc⟩
    obtain ⟨h1, h2⟩ := mem_Sec.1 h𝒳
    have hp' : (p.1, c) = p := Prod.ext rfl hpc.symm
    refine ⟨(p.1, 𝒳.erase p), ⟨by rw [← hpc]; exact (h1 p hp).2, ?_⟩,
      by rw [hp']; exact insert_erase hp⟩
    refine mem_Sec.2 ⟨fun q hq => ?_, fun q hq q' hq' => h2 q (mem_of_mem_erase hq) q'
      (mem_of_mem_erase hq')⟩
    obtain ⟨hq1, hq2⟩ := mem_erase.1 hq
    refine ⟨(mem_insert.1 (h1 q hq2).1).resolve_left fun h => hq1 ?_, (h1 q hq2).2⟩
    exact h2 q hq2 p hp (h.trans hpc.symm)
  · rintro ⟨⟨b, 𝒳'⟩, ⟨hb, h𝒳'⟩, rfl⟩
    obtain ⟨h1, h2⟩ := mem_Sec.1 h𝒳'
    refine ⟨mem_Sec.2 ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩, (b, c), mem_insert_self _ _, rfl⟩
    · rcases mem_insert.1 hp with rfl | hp
      · exact ⟨mem_insert_self _ _, hb⟩
      · exact ⟨mem_insert_of_mem (h1 p hp).1, (h1 p hp).2⟩
    · rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
      · rfl
      · exact (hc (by rw [show c = q.2 from hpq]; exact (h1 q hq).1)).elim
      · exact (hc (by rw [show c = p.2 from hpq.symm]; exact (h1 p hp).1)).elim
      · exact h2 p hp q hq hpq

/-- **Expansion of a product of sums.**
`∏_{c ∈ s} (a_c + ∑_{b ∈ t_c} f(b, c)) = ∑_{𝒳} ∏_{c ∈ s, c ∉ 𝒳} a_c ∏_{p ∈ 𝒳} f(p)`, the sum
being over the sections `𝒳 ∈ Sec s t`. -/
theorem prod_add_sum_eq (s : Finset α) (t : α → Finset β) (a : α → R) (f : β × α → R) :
    ∏ c ∈ s, (a c + ∑ b ∈ t c, f (b, c)) =
      ∑ 𝒳 ∈ Sec s t, (∏ c ∈ s \ 𝒳.image Prod.snd, a c) * ∏ p ∈ 𝒳, f p := by
  induction s using Finset.induction_on with
  | empty => simp [Sec_empty]
  | insert c s hc ih =>
    rw [prod_insert hc, ih, add_mul, ← sum_filter_add_sum_filter_not (Sec (insert c s) t)
      (fun 𝒳 => ∃ p ∈ 𝒳, p.2 = c), Sec_insert_filter hc, Sec_insert_filter_not hc, add_comm]
    have hnot : ∀ 𝒳 ∈ Sec s t, c ∉ 𝒳.image Prod.snd := fun 𝒳 h𝒳 hc' => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hc'
      exact hc ((mem_Sec.1 h𝒳).1 p hp).1
    congr 1
    · rw [sum_image, sum_product, sum_mul]
      · refine sum_congr rfl fun b _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun 𝒳 h𝒳 => ?_
        have hb : (b, c) ∉ 𝒳 := fun h => hnot 𝒳 h𝒳 (mem_image.2 ⟨_, h, rfl⟩)
        rw [image_insert, insert_sdiff_insert, sdiff_insert_of_notMem hc, prod_insert hb]
        ring
      · rintro ⟨b, 𝒳⟩ h ⟨b', 𝒳'⟩ h' heq
        simp only [coe_product, Set.mem_prod, mem_coe] at h h'
        simp only at heq
        have hb : (b, c) ∉ 𝒳 := fun hm => hnot 𝒳 h.2 (mem_image.2 ⟨_, hm, rfl⟩)
        have hb' : (b', c) ∉ 𝒳' := fun hm => hnot 𝒳' h'.2 (mem_image.2 ⟨_, hm, rfl⟩)
        have h1 : b = b' := by
          have := heq ▸ mem_insert_self (b, c) 𝒳
          rcases mem_insert.1 this with h | h
          · exact (Prod.ext_iff.1 h).1
          · exact absurd (mem_image.2 ⟨_, h, rfl⟩) (hnot 𝒳' h'.2)
        subst h1
        have h2 : 𝒳 = 𝒳' := by
          rw [← erase_insert hb, heq, erase_insert hb']
        rw [h2]
    · rw [mul_sum]
      refine sum_congr rfl fun 𝒳 h𝒳 => ?_
      rw [insert_sdiff_of_notMem _ (hnot 𝒳 h𝒳), prod_insert fun h => hc (mem_sdiff.1 h).1,
        mul_assoc]

end Expand

/-! ### Nilpotency of `V(X)` and `e^{-V(X)}` as a product over blocks -/

section Nil

variable {Λ : Type*} [DecidableEq Λ]

/-- `y` is (an element of the form) `ι v`, a linear combination of generators. -/
def IsGenLin (y : Grassmann.N Λ) : Prop := ∃ v : V Λ, y = ExteriorAlgebra.ι ℂ v

/-- `y` is even and nilpotent. -/
def IsEvNil (y : Grassmann.N Λ) : Prop := inv' y = y ∧ IsNilpotent y

theorem isGenLin_ψ (a : Sf Λ) : IsGenLin (ψ a) := ⟨_, rfl⟩

theorem IsGenLin.sub {x y : Grassmann.N Λ} (hx : IsGenLin x) (hy : IsGenLin y) :
    IsGenLin (x - y) := by
  obtain ⟨u, rfl⟩ := hx; obtain ⟨v, rfl⟩ := hy; exact ⟨u - v, (map_sub _ _ _).symm⟩

theorem IsGenLin.neg {x : Grassmann.N Λ} (hx : IsGenLin x) : IsGenLin (-x) := by
  obtain ⟨u, rfl⟩ := hx; exact ⟨-u, (map_neg _ _).symm⟩

theorem IsGenLin.smul {x : Grassmann.N Λ} (hx : IsGenLin x) (r : ℂ) : IsGenLin (r • x) := by
  obtain ⟨u, rfl⟩ := hx; exact ⟨r • u, (map_smul _ _ _).symm⟩

theorem IsGenLin.sum {ι : Type*} (s : Finset ι) {f : ι → Grassmann.N Λ}
    (hf : ∀ i ∈ s, IsGenLin (f i)) :
    IsGenLin (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [sum_insert ha]
    obtain ⟨u, hu⟩ := hf a (mem_insert_self a s)
    obtain ⟨v, hv⟩ := ih fun i hi => hf i (mem_insert_of_mem hi)
    exact ⟨u + v, by rw [map_add, hu, hv]⟩

theorem IsGenLin.mul {x y : Grassmann.N Λ} (hx : IsGenLin x) (hy : IsGenLin y) :
    IsEvNil (x * y) := by
  obtain ⟨u, rfl⟩ := hx; obtain ⟨v, rfl⟩ := hy
  refine ⟨by rw [map_mul, inv'_ι, inv'_ι, neg_mul_neg], 2, ?_⟩
  rw [pow_two, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι ℂ v), ι_anticomm v u]
  simp only [neg_mul, mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero]

theorem IsEvNil.add {x y : Grassmann.N Λ} (hx : IsEvNil x) (hy : IsEvNil y) : IsEvNil (x + y) :=
  ⟨by rw [map_add, hx.1, hy.1], Commute.isNilpotent_add (mul_comm_of_even hx.1 y) hx.2 hy.2⟩

theorem IsEvNil.smul {x : Grassmann.N Λ} (hx : IsEvNil x) (r : ℂ) : IsEvNil (r • x) :=
  ⟨by rw [map_smul, hx.1], hx.2.smul r⟩

theorem IsEvNil.mul {x y : Grassmann.N Λ} (hx : IsEvNil x) (hy : IsEvNil y) :
    IsEvNil (x * y) := by
  refine ⟨by rw [map_mul, hx.1, hy.1], ?_⟩
  obtain ⟨n, hn⟩ := hx.2
  exact ⟨n, by rw [Commute.mul_pow (mul_comm_of_even hx.1 y) n, hn, zero_mul]⟩

theorem IsEvNil.sum {ι : Type*} (s : Finset ι) {f : ι → Grassmann.N Λ}
    (hf : ∀ i ∈ s, IsEvNil (f i)) :
    IsEvNil (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, ⟨1, by simp⟩⟩
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

end Nil

variable {d L N : ℕ} [NeZero L]

/-! ### Blocks and polymers -/

section Blocks

variable {j : ℕ}

theorem mem_blocks {X : Finset (Lam d L N)} {b : Fin d → ℕ} :
    b ∈ blocks j X ↔ ∃ x ∈ X, blk j x = b := by
  simp [blocks]

theorem blocks_mono {X Y : Finset (Lam d L N)} (h : X ⊆ Y) : blocks j X ⊆ blocks j Y :=
  image_subset_image h

/-- The blocks of a polymer are contained in it. -/
theorem blockSet_subset_of_mem_blocks {X : Finset (Lam d L N)} {b : Fin d → ℕ}
    (hX : IsPolymer j X) (hb : b ∈ blocks j X) : blockSet j b ⊆ X := by
  obtain ⟨x, hx, rfl⟩ := mem_blocks.1 hb
  intro y hy
  exact hX x y (mem_blockSet.1 hy).symm hx

theorem blockSet_nonempty_of_mem_blocks {X : Finset (Lam d L N)} {b : Fin d → ℕ}
    (hb : b ∈ blocks j X) : (blockSet (L := L) (N := N) j b).Nonempty := by
  obtain ⟨x, -, rfl⟩ := mem_blocks.1 hb
  exact ⟨x, mem_blockSet.2 rfl⟩

theorem mem_blocks_of_blockSet_subset {X : Finset (Lam d L N)} {b : Fin d → ℕ}
    (hne : (blockSet (L := L) (N := N) j b).Nonempty) (h : blockSet j b ⊆ X) :
    b ∈ blocks j X := by
  obtain ⟨x, hx⟩ := hne
  exact mem_blocks.2 ⟨x, h hx, mem_blockSet.1 hx⟩

theorem isPolymer_biUnion {ι : Type*} (s : Finset ι) (f : ι → Finset (Lam d L N))
    (h : ∀ i ∈ s, IsPolymer j (f i)) : IsPolymer j (s.biUnion f) := by
  intro x y hxy hx
  obtain ⟨i, hi, hx⟩ := mem_biUnion.1 hx
  exact mem_biUnion.2 ⟨i, hi, h i hi x y hxy hx⟩

theorem blocks_biUnion_blockSet {X : Finset (Lam d L N)} {t : Finset (Fin d → ℕ)}
    (ht : t ⊆ blocks j X) : blocks j (t.biUnion (blockSet (L := L) (N := N) j)) = t := by
  ext b
  simp only [mem_blocks, mem_biUnion, mem_blockSet]
  constructor
  · rintro ⟨x, ⟨b', hb', hx⟩, rfl⟩
    rwa [hx]
  · intro hb
    obtain ⟨x, -, hx⟩ := mem_blocks.1 (ht hb)
    exact ⟨x, ⟨b, hb, hx⟩, hx⟩

/-- A product over blocks is multiplicative over disjoint polymers. -/
theorem prod_blocks_union {M : Type*} [CommMonoid M] (φ : (Fin d → ℕ) → M)
    {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B) (h : Disjoint A B) :
    ∏ b ∈ blocks j (A ∪ B), φ b = (∏ b ∈ blocks j A, φ b) * ∏ b ∈ blocks j B, φ b := by
  rw [blocks_union, prod_union (disjoint_blocks hA hB h)]

/-- Sets of blocks of a polymer `S` correspond to subpolymers of `S`. -/
theorem sum_powerset_blocks {M : Type*} [AddCommMonoid M] {S : Finset (Lam d L N)}
    (hS : IsPolymer j S) (F : Finset (Fin d → ℕ) → M) :
    ∑ t ∈ (blocks j S).powerset, F t = ∑ Y ∈ Pj j S, F (blocks j Y) := by
  refine sum_nbij' (fun t => t.biUnion (blockSet j)) (fun Y => blocks j Y) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have ht := mem_powerset.1 ht
    exact mem_Pj.2 ⟨biUnion_subset.2 fun b hb => blockSet_subset_of_mem_blocks hS (ht hb),
      isPolymer_biUnion _ _ fun b _ => isPolymer_blockSet j b⟩
  · intro Y hY
    exact mem_powerset.2 (blocks_mono (mem_Pj.1 hY).1)
  · intro t ht
    exact blocks_biUnion_blockSet (mem_powerset.1 ht)
  · intro Y hY
    exact biUnion_blocks (mem_Pj.1 hY).2
  · intro t ht
    rw [blocks_biUnion_blockSet (mem_powerset.1 ht)]

/-- **Binomial expansion over blocks** (`e:thetaI`): for a polymer `S`,
`∏_{B ∈ 𝓑(S)} (x_B + y_B) = ∑_{Y ∈ 𝒫(S)} x^{S ∖ Y} y^Y`. -/
theorem prod_add_blocks {R : Type*} [CommRing R] {S : Finset (Lam d L N)} (hS : IsPolymer j S)
    (x y : (Fin d → ℕ) → R) :
    ∏ b ∈ blocks j S, (x b + y b) =
      ∑ Y ∈ Pj j S, (∏ b ∈ blocks j (S \ Y), x b) * ∏ b ∈ blocks j Y, y b := by
  simp_rw [add_comm (x _)]
  rw [prod_add, sum_powerset_blocks hS (fun t => (∏ b ∈ t, y b) * ∏ b ∈ blocks j S \ t, x b)]
  refine sum_congr rfl fun Y hY => ?_
  rw [blocks_sdiff hS (mem_Pj.1 hY).2, mul_comm]

theorem not_touch_mono {X Y X' Y' : Finset (Lam d L N)} (h : ¬ Touch X Y) (hX : X' ⊆ X)
    (hY : Y' ⊆ Y) : ¬ Touch X' Y' := by
  rintro ⟨x, hx, y, hy, hxy⟩
  exact h ⟨x, hX hx, y, hY hy, hxy⟩

theorem nonempty_of_mem_comp {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : Y ∈ Comp j X) : Y.Nonempty :=
  (isConn_of_mem_comp hX hY).2.1

theorem isPolymer_of_mem_comp {X Y : Finset (Lam d L N)} (hX : IsPolymer j X)
    (hY : Y ∈ Comp j X) : IsPolymer j Y :=
  (isConn_of_mem_comp hX hY).1

/-- Components of non-touching polymers are distinct. -/
theorem disjoint_comp {X Y : Finset (Lam d L N)} (hX : IsPolymer j X) (h : ¬ Touch X Y) :
    Disjoint (Comp j X) (Comp j Y) := by
  rw [Finset.disjoint_left]
  intro c hcX hcY
  obtain ⟨x, hx⟩ := nonempty_of_mem_comp hX hcX
  exact Finset.disjoint_left.1 (disjoint_of_not_touch h) (subset_of_mem_comp hcX hx)
    (subset_of_mem_comp hcY hx)

/-- A function which is multiplicative over non-touching polymers factors over the connected
components. -/
theorem eq_prod_comp_of_mul {M : Type*} [CommMonoid M] (f : Finset (Lam d L N) → M)
    (h0 : f ∅ = 1)
    (hmul : ∀ A B, IsPolymer j A → IsPolymer j B → ¬ Touch A B → f (A ∪ B) = f A * f B)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) : f W = ∏ c ∈ Comp j W, f c := by
  suffices h : ∀ S ⊆ Comp j W, f (S.biUnion id) = ∏ c ∈ S, f c by
    rw [← h _ subset_rfl, biUnion_comp hW]
  intro S hS
  induction S using Finset.induction_on with
  | empty => simp [h0]
  | insert c S hc ih =>
    rw [biUnion_insert, prod_insert hc, ← ih ((subset_insert _ _).trans hS)]
    have hcW := hS (mem_insert_self c S)
    refine hmul _ _ (isPolymer_of_mem_comp hW hcW) (isPolymer_biUnion _ _ fun c' hc' =>
      isPolymer_of_mem_comp hW (hS (mem_insert_of_mem hc'))) ?_
    rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨c', hc', hy⟩ := mem_biUnion.1 hy
    exact not_touch_of_mem_comp hW hcW (hS (mem_insert_of_mem hc'))
      (by rintro rfl; exact hc hc') ⟨x, hx, y, hy, hxy⟩

theorem Kext_empty (K : Act d L N) : Kext j K ∅ = 1 := by
  simp [Kext, comp_empty]

/-- The extension `Kext` is multiplicative over non-touching polymers. -/
theorem Kext_union (K : Act d L N) {A B : Finset (Lam d L N)} (hA : IsPolymer j A)
    (hB : IsPolymer j B) (h : ¬ Touch A B) : Kext j K (A ∪ B) = Kext j K A * Kext j K B := by
  rw [Kext, comp_union hA hB h, prod_union (disjoint_comp hA h), Kext, Kext]

end Blocks


section NilV

variable {j : ℕ}

theorem isGenLin_grad (e : Dir d) (x : Lam d L N) : IsGenLin (grad e x) :=
  (isGenLin_ψ _).sub (isGenLin_ψ _)

theorem isGenLin_gradbar (e : Dir d) (x : Lam d L N) : IsGenLin (gradbar e x) :=
  (isGenLin_ψ _).sub (isGenLin_ψ _)

theorem isGenLin_lapPsi (x : Lam d L N) : IsGenLin (lapPsi x) :=
  (IsGenLin.sum _ fun e _ => (isGenLin_grad e _).sub (isGenLin_grad e _)).smul _

theorem isGenLin_lapPsibar (x : Lam d L N) : IsGenLin (lapPsibar x) :=
  (IsGenLin.sum _ fun e _ => (isGenLin_gradbar e _).sub (isGenLin_gradbar e _)).smul _

theorem isEvNil_gradSq (x : Lam d L N) : IsEvNil (gradSq x) :=
  (IsEvNil.sum _ fun e _ => (isGenLin_grad e x).mul (isGenLin_gradbar e x)).smul _

theorem isEvNil_eval (V : Vcoup) (X : Finset (Lam d L N)) : IsEvNil (V.eval X) := by
  refine IsEvNil.sum _ fun x _ => ?_
  have hpp : IsEvNil (psi x * psibar x) := (isGenLin_ψ _).mul (isGenLin_ψ _)
  refine (((isEvNil_gradSq x).smul _).add ?_).add ?_ |>.add ?_
  · exact (((isGenLin_lapPsi x).neg.mul (isGenLin_ψ _)).add
      ((isGenLin_ψ _).mul (isGenLin_lapPsibar x).neg)).smul _
  · exact hpp.smul _
  · exact (hpp.mul (isEvNil_gradSq x)).smul _

/-- `V(X)` is nilpotent. -/
theorem isNilpotent_VE (V : Vcoup) (X : Finset (Lam d L N)) : IsNilpotent (VE V X) := by
  obtain ⟨n, hn⟩ := (isEvNil_eval V X).2
  exact ⟨n, Subtype.ext (by simp [hn])⟩

theorem gexp_sum {Λ : Type*} [DecidableEq Λ] {ι : Type*} (s : Finset ι) (f : ι → EvR Λ)
    (hf : ∀ i ∈ s, IsNilpotent (f i)) : gexp (∑ i ∈ s, f i) = ∏ i ∈ s, gexp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gexp, IsNilpotent.exp_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha, gexp, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      (hf a (mem_insert_self a s)) (isNilpotent_sum fun i hi => hf i (mem_insert_of_mem hi)),
      ← gexp, ← gexp, ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- `V(X) = ∑_{B ∈ 𝓑_j(X)} V(B)` for a polymer `X`. -/
theorem VE_eq_sum_blocks (V : Vcoup) {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    VE V X = ∑ b ∈ blocks j X, VE V (blockSet j b) := by
  refine Subtype.ext ?_
  simp only [coe_VE, AddSubmonoidClass.coe_finsetSum]
  conv_lhs => rw [← biUnion_blocks hX]
  unfold Vcoup.eval
  rw [sum_biUnion]
  intro b _ b' _ hbb'
  exact Finset.disjoint_left.2 fun x hx hx' =>
    hbb' ((mem_blockSet.1 hx).symm.trans (mem_blockSet.1 hx'))

/-- `e^{-V(X)} = ∏_{B ∈ 𝓑_j(X)} e^{-V(B)}` for a polymer `X`. -/
theorem gexp_neg_VE (V : Vcoup) {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    gexp (-VE V X) = ∏ b ∈ blocks j X, gexp (-VE V (blockSet (L := L) (N := N) j b)) := by
  rw [VE_eq_sum_blocks V hX, ← sum_neg_distrib,
    gexp_sum _ _ fun b _ => (isNilpotent_VE V (blockSet (L := L) (N := N) j b)).neg]

end NilV

end

end Step
