import Step2.Map.Reblock

/-!
# The bound on the correction `E = K_out - M` (Brydges–Slade (D.17)–(D.20))

For a connected polymer `W`, the terms of `K_out(W)` (`Step2.Kout`) with `𝒳 = ∅` give `M(W)`, and
the terms with a single pair and `U_M = ∅` cancel because `∑_U J(B, U) = 0` (`Kout_split`).
Every remaining term contains at least two small factors (two `J̄`, or a `J̄` and an `M`), so
(`Kout_sub_le`)

  `A^{(|𝓑(W)| - 2^d)_+} ‖K_out(W) - M(W)‖ ≤ δ'' (δ'' + μ')`,

where `δ'' = (2 c₀ A)^{c_B} δ` with `‖J̄‖ ≤ δ`, and `μ' = μ (λA)^{2^d}` with
`(λA)^{(|𝓑(Y)| - 2^d)_+} ‖M(Y)‖ ≤ μ`, provided `‖I(B)‖ ≤ 2`, `λ ≥ 2 c₀` and `δ'', μ' ≤ 1`.
Here `c₀ = 2^{1 + c_S}` bounds the number of terms per block and `c_B = (2^{d+1}+3)^d` bounds
`|𝓑(B^□)|`. The stronger regulator `λA` on `M` absorbs the number of terms.
-/

namespace Step2

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L N : ℕ} [NeZero L]

section Count

variable {k : ℕ}

theorem card_G0W_le {c : ℕ}
    (hc : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) k,
      ((smallSets (d := d) (L := L) (N := N) k).filter (fun X => blockSet k b ⊆ X)).card ≤ c)
    {W : Finset (Lam d L N)} (hW : IsPolymer k W) :
    ((G0 (L := L) (N := N) k).filter (fun g => g.2 ∪ Bbox k g.1 = W)).card ≤
      2 ^ ((1 + c) * nb k W) := by
  classical
  set S := (blocks k W).biUnion (fun b =>
    ((smallSets (L := L) (N := N) k).filter (fun X => blockSet k b ⊆ X)).image (Prod.mk b))
  have hsub : (G0 (L := L) (N := N) k).filter (fun g => g.2 ∪ Bbox k g.1 = W) ⊆
      S.powerset ×ˢ Pj k W := by
    intro g hg
    obtain ⟨f2, -, f4⟩ := G0W_facts hg
    obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 hg).1
    rw [mem_product, mem_powerset, mem_Pj]
    refine ⟨fun p hp => ?_, f2, h1⟩
    obtain ⟨hb, hs, hbs⟩ := mem_pairsU.1 (h2 hp)
    exact mem_biUnion.2 ⟨p.1, mem_blocks_of_blockSet_subset (mem_blockIdx.1 hb) (f4 p hp).1,
      mem_image.2 ⟨p.2, mem_filter.2 ⟨mem_smallSets.2 hs, hbs⟩, rfl⟩⟩
  have hS : S.card ≤ c * nb k W := by
    refine card_biUnion_le.trans ?_
    calc ∑ b ∈ blocks k W, (((smallSets (L := L) (N := N) k).filter
          (fun X => blockSet k b ⊆ X)).image (Prod.mk b)).card
        ≤ ∑ _b ∈ blocks k W, c := sum_le_sum fun b hb =>
          card_image_le.trans (hc b (mem_blockIdx_of_mem_blocks hb))
      _ = c * nb k W := by rw [sum_const, smul_eq_mul, nb, mul_comm]
  calc _ ≤ (S.powerset ×ˢ Pj k W).card := card_le_card hsub
    _ = 2 ^ S.card * 2 ^ nb k W := by rw [card_product, card_powerset, card_Pj hW]
    _ ≤ 2 ^ (c * nb k W) * 2 ^ nb k W := by gcongr; norm_num
    _ = 2 ^ ((1 + c) * nb k W) := by rw [← pow_add]; ring_nf

theorem nb_union_le (A B : Finset (Lam d L N)) : nb k (A ∪ B) ≤ nb k A + nb k B := by
  rw [nb, nb, nb, blocks_union]; exact card_union_le _ _

theorem nb_Bbox_le (hk : k ≤ N) (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    nb k (Bbox k 𝒳) ≤ (2 ^ (d + 1) + 3) ^ d * 𝒳.card := by
  classical
  unfold Bbox
  induction 𝒳 using Finset.induction_on with
  | empty => simp [nb, blocks]
  | insert p s hp ih =>
    rw [biUnion_insert, card_insert_of_notMem hp]
    refine (nb_union_le _ _).trans ?_
    have := nb_nbhd_block_le (L := L) (N := N) hk p.1
    nlinarith

end Count

/-! ### Splitting off the trivial terms -/

section Split

variable (k : ℕ) (I : (Fin d → ℕ) → EvR (Lam d L N)) (M : Act d L N)
  (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N))

/-- The terms of `K_out(W)` which are bounded in `Kout_sub_le`. -/
def Rset (W : Finset (Lam d L N)) : Finset (GT d L N) :=
  ((G0 (L := L) (N := N) k).filter (fun g => g.2 ∪ Bbox k g.1 = W)).filter
    (fun g => g.1 ≠ ∅ ∧ ¬ (g.1.card = 1 ∧ g.2 = ∅))

variable {k I M J}

theorem Kout_split (hJ0 : ∀ b ∈ blockIdx (L := L) (N := N) k,
      ∑ U ∈ (smallSets (d := d) (L := L) (N := N) k).filter (fun U => blockSet k b ⊆ U), J b U = 0)
    {W : Finset (Lam d L N)} (hW : IsConn k W) :
    Kout k I M J W = M W + ∑ g ∈ Rset k W, Rterm k I M J W g := by
  classical
  set F := (G0 (L := L) (N := N) k).filter (fun g => g.2 ∪ Bbox k g.1 = W) with hF
  have hBbox0 : Bbox k (∅ : Finset ((Fin d → ℕ) × Finset (Lam d L N))) = ∅ := by simp [Bbox]
  -- the term `𝒳 = ∅`
  have hT0 : F.filter (fun g => g.1 = ∅) = {(∅, W)} := by
    ext g
    simp only [mem_filter, mem_singleton, hF]
    constructor
    · rintro ⟨⟨-, hgW⟩, h1⟩
      rw [h1, hBbox0, union_empty] at hgW
      exact Prod.ext h1 hgW
    · rintro rfl
      refine ⟨⟨(mem_G0 k).2 ⟨hW.1, empty_subset _, by simp, by simp, ?_⟩, ?_⟩, rfl⟩
      · rintro ⟨x, hx, -⟩; simp [Xcal] at hx
      · show W ∪ Bbox k ∅ = W; rw [hBbox0, union_empty]
  have hR0 : Rterm k I M J W (∅, W) = M W := by
    simp only [Rterm, Xcal, biUnion_empty, union_empty, sdiff_self, prod_empty, mul_one]
    rw [show (⊥ : Finset (Lam d L N)) = ∅ from rfl, Kext, comp_of_isConn hW, prod_singleton]
    simp [bpow, blocks]
  -- the terms with one pair and `U_M = ∅`
  have hT1 : ∑ g ∈ (F.filter fun g => g.1 ≠ ∅).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      Rterm k I M J W g = 0 := by
    set PW := (pairsU (L := L) (N := N) k).filter (fun p => nbhd k (blockSet k p.1) = W)
    have e : ∑ g ∈ (F.filter fun g => g.1 ≠ ∅).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
        Rterm k I M J W g = ∑ p ∈ PW, bpow k I W * J p.1 p.2 := by
      symm
      refine sum_bij (fun p _ => (({p} : Finset _), (∅ : Finset (Lam d L N)))) ?_ ?_ ?_ ?_
      · intro p hp
        obtain ⟨hp1, hpW⟩ := mem_filter.1 hp
        simp only [mem_filter, hF]
        refine ⟨⟨⟨(mem_G0 k).2 ⟨isPolymer_empty k, singleton_subset_iff.2 hp1, by simp, by simp,
          by rintro ⟨x, -, y, hy, -⟩; simp at hy⟩, ?_⟩, by simp⟩, by simp⟩
        show ∅ ∪ Bbox k {p} = W
        rw [empty_union, Bbox, singleton_biUnion, hpW]
      · intro p _ q _ h
        simpa using congrArg Prod.fst h
      · intro g hg
        simp only [mem_filter, hF] at hg
        obtain ⟨⟨⟨hg0, hgW⟩, -⟩, hc1, hg2⟩ := hg
        obtain ⟨p, hp⟩ := card_eq_one.1 hc1
        obtain ⟨-, h2, -, -, -⟩ := (mem_G0 k).1 hg0
        refine ⟨p, mem_filter.2 ⟨h2 (hp ▸ mem_singleton_self p), ?_⟩, ?_⟩
        · rw [hg2, hp, empty_union, Bbox, singleton_biUnion] at hgW; exact hgW
        · exact Prod.ext hp.symm hg2.symm
      · intro p hp
        obtain ⟨hp1, hpW⟩ := mem_filter.1 hp
        have hpsub : p.2 ⊆ W := hpW ▸ (pair_sub_nbhd hp1).2
        simp only [Rterm, Xcal, singleton_biUnion, empty_union, Kext_empty, one_mul,
          prod_singleton, Jbar]
        rw [← mul_assoc, ← bpow_union k I (IsPolymer.sdiff (hW.1) (mem_pairsU.1 hp1).2.1.1)
          (mem_pairsU.1 hp1).2.1.1 sdiff_disjoint, sdiff_union_of_subset hpsub]
    rw [e, ← mul_sum]
    have h2 : ∑ p ∈ PW, J p.1 p.2 = 0 := by
      rw [← sum_fiberwise_of_maps_to (s := PW) (t := (blockIdx (L := L) (N := N) k))
        (g := Prod.fst) (fun p hp => (mem_pairsU.1 (mem_filter.1 hp).1).1)]
      refine sum_eq_zero fun b hb => ?_
      by_cases hbW : nbhd k (blockSet (L := L) (N := N) k b) = W
      · rw [← hJ0 b hb]
        refine sum_nbij' (fun p => p.2) (fun U => (b, U)) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          obtain ⟨hp1, hpb⟩ := mem_filter.1 hp
          obtain ⟨-, hs, hbs⟩ := mem_pairsU.1 (mem_filter.1 hp1).1
          exact mem_smallSets_filter.2 ⟨hs, hpb ▸ hbs⟩
        · intro U hU
          obtain ⟨hs, hbU⟩ := mem_smallSets_filter.1 hU
          exact mem_filter.2 ⟨mem_filter.2 ⟨mem_pairsU.2 ⟨hb, hs, hbU⟩, hbW⟩, rfl⟩
        · intro p hp; exact Prod.ext (mem_filter.1 hp).2.symm rfl
        · intro U _; rfl
        · intro p hp; rw [(mem_filter.1 hp).2]
      · refine sum_eq_zero fun p hp => absurd ?_ hbW
        obtain ⟨hp1, hpb⟩ := mem_filter.1 hp
        rw [← hpb]; exact (mem_filter.1 hp1).2
    rw [h2, mul_zero]
  -- assemble
  rw [Kout, ← hF, ← sum_filter_add_sum_filter_not F (fun g => g.1 = ∅), hT0, sum_singleton, hR0,
    ← sum_filter_add_sum_filter_not (F.filter fun g => ¬ g.1 = ∅) (fun g => g.1.card = 1 ∧ g.2 = ∅),
    hT1, zero_add]
  congr 1
  unfold Rset
  rw [← hF, filter_filter]

end Split

/-! ### The bound -/

section Bound

variable {k : ℕ} {I : (Fin d → ℕ) → EvR (Lam d L N)} {M : Act d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)} {h ℓ : ℝ}

theorem real_term {n c : ℕ} {δ μ : ℝ} (hδ0 : 0 ≤ δ) (hμ0 : 0 ≤ μ) (hδ1 : δ ≤ 1) (hμ1 : μ ≤ 1)
    (hnc : 2 ≤ n ∨ (n = 1 ∧ 1 ≤ c)) : δ ^ n * μ ^ c ≤ δ * (δ + μ) := by
  rcases hnc with hn | ⟨rfl, hc⟩
  · have h1 : δ ^ n ≤ δ ^ 2 := pow_le_pow_of_le_one hδ0 hδ1 hn
    have h2 : μ ^ c ≤ 1 := pow_le_one₀ hμ0 hμ1
    nlinarith [pow_nonneg hδ0 n, sq_nonneg δ]
  · have h2 : μ ^ c ≤ μ := pow_le_of_le_one hμ0 hμ1 (by omega)
    rw [pow_one]; nlinarith

/-- **The bound on `K_out(W) - M(W)`.** -/
theorem Kout_sub_le (hk : k ≤ N) (hh : 0 < h) (hℓ : 0 < ℓ) {A lam δ μ : ℝ} {cS : ℕ}
    (hA : 1 ≤ A) (hlam : 1 ≤ lam) (hδ0 : 0 ≤ δ) (hμ0 : 0 ≤ μ)
    (hcS : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) k,
      ((smallSets (d := d) (L := L) (N := N) k).filter (fun X => blockSet k b ⊆ X)).card ≤ cS)
    (hlamc : 2 * (2 : ℝ) ^ (1 + cS) ≤ lam)
    (hI : ∀ b ∈ blockIdx (L := L) (N := N) k,
      tNorm (Dir d) (pPhi d) h ℓ (I b : Alg d L N) ≤ ENNReal.ofReal 2)
    (hJb : ∀ p ∈ pairsU (L := L) (N := N) k,
      tNorm (Dir d) (pPhi d) h ℓ (Jbar k I J p.1 p.2 : Alg d L N) ≤ ENNReal.ofReal δ)
    (hM : ∀ Y, IsConn k Y → ENNReal.ofReal ((lam * A) ^ (nb k Y - 2 ^ d)) *
      tNorm (Dir d) (pPhi d) h ℓ (M Y : Alg d L N) ≤ ENNReal.ofReal μ)
    (hδ1 : (2 * (2 : ℝ) ^ (1 + cS) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ ≤ 1)
    (hμ1 : μ * (lam * A) ^ 2 ^ d ≤ 1)
    {W : Finset (Lam d L N)} (hW : IsPolymer k W) :
    ENNReal.ofReal (A ^ (nb k W - 2 ^ d)) *
      tNorm (Dir d) (pPhi d) h ℓ ((∑ g ∈ Rset k W, Rterm k I M J W g : EvR (Lam d L N)) :
        Alg d L N) ≤
      ENNReal.ofReal (((2 * (2 : ℝ) ^ (1 + cS) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ) *
        ((2 * (2 : ℝ) ^ (1 + cS) * A) ^ ((2 ^ (d + 1) + 3) ^ d) * δ +
          μ * (lam * A) ^ 2 ^ d)) := by
  classical
  have hA0 : 0 < A := by linarith
  set c₀ : ℝ := (2 : ℝ) ^ (1 + cS) with hc₀
  have hc₀1 : 1 ≤ c₀ := one_le_pow₀ (by norm_num)
  set cB := (2 ^ (d + 1) + 3) ^ d
  set a : ℝ := 2 * c₀ * A with ha
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith
  set δ'' := a ^ cB * δ
  set μ' := μ * (lam * A) ^ 2 ^ d
  have hlA1 : 1 ≤ lam * A := by nlinarith
  refine wsum_bound _ _ (2 ^ ((1 + cS) * nb k W)) ((card_le_card (filter_subset _ _)).trans
    (card_G0W_le hcS hW)) (by positivity) fun g hg => ?_
  obtain ⟨hgF, hg1, hg2⟩ := mem_filter.1 hg
  obtain ⟨f2, -, f4⟩ := G0W_facts hgF
  obtain ⟨h1, h2, -, -, -⟩ := (mem_G0 k).1 (mem_filter.1 hgF).1
  have hgW := (mem_filter.1 hgF).2
  set n := g.1.card
  set c := (Comp k g.2).card
  -- the norm of the term
  have hbI : tNorm (Dir d) (pPhi d) h ℓ (bpow k I (W \ (g.2 ∪ Xcal g.1)) : Alg d L N) ≤
      ENNReal.ofReal (2 ^ nb k W) := by
    have := tn_prodE (E := Dir d) (p := pPhi d) hh hℓ (blocks k (W \ (g.2 ∪ Xcal g.1))) I
      (fun _ => 2) (fun _ _ => by norm_num) (fun b hb => hI b (mem_blockIdx_of_mem_blocks hb))
    rw [prod_const] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num)
      (card_le_card (blocks_mono sdiff_subset))))
  have hbM : tNorm (Dir d) (pPhi d) h ℓ (Kext k M g.2 : Alg d L N) ≤
      ENNReal.ofReal (∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) := by
    refine tn_prodE (E := Dir d) (p := pPhi d) hh hℓ _ _ _ (fun _ _ => by positivity)
      fun Y hY => ?_
    have := hM Y (isConn_of_mem_comp h1 hY)
    have hp : (0 : ℝ) < (lam * A) ^ (nb k Y - 2 ^ d) := by positivity
    rw [ENNReal.ofReal_div_of_pos hp, ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this
  have hbJ : tNorm (Dir d) (pPhi d) h ℓ ((∏ p ∈ g.1, Jbar k I J p.1 p.2 : EvR (Lam d L N)) :
      Alg d L N) ≤ ENNReal.ofReal (δ ^ n) := by
    have := tn_prodE (E := Dir d) (p := pPhi d) hh hℓ g.1 (fun p => Jbar k I J p.1 p.2)
      (fun _ => δ) (fun _ _ => hδ0) (fun p hp => hJb p (h2 hp))
    rwa [prod_const] at this
  have hterm := tn_mulE (E := Dir d) (p := pPhi d) hh hℓ (by positivity) hbI
    (tn_mulE (E := Dir d) (p := pPhi d) hh hℓ (by positivity) hbM hbJ)
  refine (mul_le_mul_left' hterm _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real inequality
  have hnbW : nb k W ≤ nb k g.2 + cB * n := by
    rw [← hgW]; exact (nb_union_le _ _).trans (Nat.add_le_add_left (nb_Bbox_le hk g.1) _)
  have hprod : ∏ Y ∈ Comp k g.2, a ^ nb k Y = a ^ nb k g.2 := prod_comp_pow h1 a
  have hY : ∀ Y ∈ Comp k g.2, a ^ nb k Y * (μ / (lam * A) ^ (nb k Y - 2 ^ d)) ≤ μ' := by
    intro Y _
    have hp : (0 : ℝ) < (lam * A) ^ (nb k Y - 2 ^ d) := by positivity
    rw [mul_div_assoc', div_le_iff₀ hp]
    have h3 : a ^ nb k Y ≤ (lam * A) ^ nb k Y := pow_le_pow_left₀ (by positivity)
      (by rw [ha]; nlinarith) _
    have h4 : (lam * A) ^ nb k Y ≤ (lam * A) ^ 2 ^ d * (lam * A) ^ (nb k Y - 2 ^ d) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hlA1 (by omega)
    calc a ^ nb k Y * μ ≤ (lam * A) ^ 2 ^ d * (lam * A) ^ (nb k Y - 2 ^ d) * μ :=
          mul_le_mul_of_nonneg_right (h3.trans h4) hμ0
      _ = μ' * (lam * A) ^ (nb k Y - 2 ^ d) := by simp only [μ']; ring
  have hprodμ : a ^ nb k g.2 * ∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d) ≤ μ' ^ c := by
    rw [← hprod, ← prod_mul_distrib, ← prod_const]
    exact prod_le_prod (fun Y _ => by positivity) hY
  have hnc : 2 ≤ n ∨ (n = 1 ∧ 1 ≤ c) := by
    have hn0 : n ≠ 0 := fun h0 => hg1 (card_eq_zero.1 h0)
    by_cases hn1 : n = 1
    · refine Or.inr ⟨hn1, ?_⟩
      have h2' : g.2 ≠ ∅ := fun he => hg2 ⟨hn1, he⟩
      exact Nat.one_le_iff_ne_zero.2 fun hc0 => h2' ((comp_card_eq_zero_iff h1).1 hc0)
    · exact Or.inl (by omega)
  have hδ''1 : δ'' ≤ 1 := hδ1
  have hμ'1 : μ' ≤ 1 := hμ1
  calc ((2 ^ ((1 + cS) * nb k W) : ℕ) : ℝ) * A ^ (nb k W - 2 ^ d) *
        (2 ^ nb k W * ((∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ n))
      ≤ a ^ nb k W * ((∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ n) := by
        have e : (((2 ^ ((1 + cS) * nb k W) : ℕ) : ℝ)) = c₀ ^ nb k W := by
          rw [hc₀, ← pow_mul]; push_cast; rfl
        rw [e]
        have hA' : A ^ (nb k W - 2 ^ d) ≤ A ^ nb k W := pow_le_pow_right₀ hA (Nat.sub_le _ _)
        have : c₀ ^ nb k W * A ^ (nb k W - 2 ^ d) * 2 ^ nb k W ≤ a ^ nb k W := by
          rw [ha, mul_pow, mul_pow]
          have : c₀ ^ nb k W * A ^ (nb k W - 2 ^ d) * 2 ^ nb k W ≤
              c₀ ^ nb k W * A ^ nb k W * 2 ^ nb k W := by gcongr
          linarith [show c₀ ^ nb k W * A ^ nb k W * 2 ^ nb k W =
            2 ^ nb k W * c₀ ^ nb k W * A ^ nb k W by ring]
        have h0 : 0 ≤ (∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ n := by positivity
        nlinarith
    _ ≤ (a ^ nb k g.2 * a ^ (cB * n)) *
          ((∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ ^ n) := by
        rw [← pow_add]; gcongr
    _ = (a ^ nb k g.2 * ∏ Y ∈ Comp k g.2, μ / (lam * A) ^ (nb k Y - 2 ^ d)) * δ'' ^ n := by
        have e3 : δ'' ^ n = a ^ (cB * n) * δ ^ n := by
          show (a ^ cB * δ) ^ n = _
          rw [mul_pow, ← pow_mul]
        rw [e3]; ring
    _ ≤ μ' ^ c * δ'' ^ n := by gcongr
    _ ≤ δ'' * (δ'' + μ') := by
        rw [mul_comm]; exact real_term (by positivity) (by positivity) hδ''1 hμ'1 hnc

end Bound

end

end Step2
