import Step.EstCoupling
import Step.StructureAux

/-!
# Auxiliary estimates for Section `sec:K-nonlinear`
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

section Gen

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

theorem tn_mulE (hh : 0 < h) (hℓ : 0 < ℓ) {F G : EvR X} {s t : ℝ} (hs : 0 ≤ s)
    (hF : tNorm E p h ℓ (F : Grassmann.N X) ≤ ENNReal.ofReal s)
    (hG : tNorm E p h ℓ (G : Grassmann.N X) ≤ ENNReal.ofReal t) :
    tNorm E p h ℓ ((F * G : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal (s * t) :=
  (tNorm_mul_le' hh hℓ F G).trans (by rw [ENNReal.ofReal_mul hs]; exact mul_le_mul' hF hG)

theorem tn_prodE (hh : 0 < h) (hℓ : 0 < ℓ) {ι : Type*} (s : Finset ι) (F : ι → EvR X)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hF : ∀ i ∈ s, tNorm E p h ℓ (F i : Grassmann.N X) ≤ ENNReal.ofReal (r i)) :
    tNorm E p h ℓ ((∏ i ∈ s, F i : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal (∏ i ∈ s, r i) :=
  (tNorm_prod_le hh hℓ s F).trans
    (by rw [ENNReal.ofReal_prod_of_nonneg hr]; exact prod_le_prod' hF)

theorem tn_sumE {ι : Type*} (s : Finset ι) (F : ι → EvR X) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hF : ∀ i ∈ s, tNorm E p h ℓ (F i : Grassmann.N X) ≤ ENNReal.ofReal (r i)) :
    tNorm E p h ℓ ((∑ i ∈ s, F i : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal (∑ i ∈ s, r i) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  exact (tNorm_sum_le _ _).trans
    (by rw [ENNReal.ofReal_sum_of_nonneg hr]; exact sum_le_sum hF)

theorem tn_sum_const {ι : Type*} (s : Finset ι) (F : ι → EvR X) {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ i ∈ s, tNorm E p h ℓ (F i : Grassmann.N X) ≤ ENNReal.ofReal r) :
    tNorm E p h ℓ ((∑ i ∈ s, F i : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal (s.card * r) := by
  have := tn_sumE s F (fun _ => r) (fun _ _ => hr) hF
  rwa [sum_const, nsmul_eq_mul] at this

theorem tn_subE {F G : EvR X} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : tNorm E p h ℓ (F : Grassmann.N X) ≤ ENNReal.ofReal s)
    (hG : tNorm E p h ℓ (G : Grassmann.N X) ≤ ENNReal.ofReal t) :
    tNorm E p h ℓ ((F - G : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal (s + t) := by
  rw [AddSubgroupClass.coe_sub]; exact tn_sub hs ht hF hG

theorem tn_addE {F G : EvR X} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : tNorm E p h ℓ (F : Grassmann.N X) ≤ ENNReal.ofReal s)
    (hG : tNorm E p h ℓ (G : Grassmann.N X) ≤ ENNReal.ofReal t) :
    tNorm E p h ℓ ((F + G : EvR X) : Grassmann.N X) ≤ ENNReal.ofReal (s + t) := by
  rw [AddMemClass.coe_add]; exact tn_add hs ht hF hG

/-- Telescoping: `‖∏ (a + c) - ∏ a‖ ≤ |s| κ β^{|s|-1} ∏ w`. -/
theorem tn_prod_sub_prod (hh : 0 < h) (hℓ : 0 < ℓ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a c : ι → EvR X) (w : ι → ℝ) {β κ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hκ : 0 ≤ κ)
    (hκβ : κ ≤ β)
    (ha : ∀ i ∈ s, tNorm E p h ℓ (a i : Grassmann.N X) ≤ ENNReal.ofReal (β * w i))
    (hac : ∀ i ∈ s, tNorm E p h ℓ ((a i + c i : EvR X) : Grassmann.N X) ≤
      ENNReal.ofReal (β * w i))
    (hc : ∀ i ∈ s, tNorm E p h ℓ (c i : Grassmann.N X) ≤ ENNReal.ofReal (κ * w i)) :
    tNorm E p h ℓ ((∏ i ∈ s, (a i + c i) - ∏ i ∈ s, a i : EvR X) : Grassmann.N X) ≤
      ENNReal.ofReal (s.card * κ * β ^ (s.card - 1) * ∏ i ∈ s, w i) := by
  have hβ : 0 ≤ β := hκ.trans hκβ
  induction s using Finset.induction_on with
  | empty =>
    have := tNorm_smul (E := E) (p := p) (h := h) (ℓ := ℓ) (0 : ℂ) (0 : Grassmann.N X)
    simp at this; simp [this]
  | insert i s hi ih =>
    have hw' : ∀ j ∈ s, 0 ≤ w j := fun j hj => hw j (mem_insert_of_mem hj)
    have ih' := ih hw' (fun j hj => ha j (mem_insert_of_mem hj))
      (fun j hj => hac j (mem_insert_of_mem hj)) (fun j hj => hc j (mem_insert_of_mem hj))
    have hQ : tNorm E p h ℓ ((∏ j ∈ s, a j : EvR X) : Grassmann.N X) ≤
        ENNReal.ofReal (β ^ s.card * ∏ j ∈ s, w j) := by
      have := tn_prodE hh hℓ s a (fun j => β * w j) (fun j hj => mul_nonneg hβ (hw' j hj))
        (fun j hj => ha j (mem_insert_of_mem hj))
      rwa [prod_mul_distrib, prod_const] at this
    have e : (∏ j ∈ insert i s, (a j + c j) - ∏ j ∈ insert i s, a j : EvR X) =
        (a i + c i) * (∏ j ∈ s, (a j + c j) - ∏ j ∈ s, a j) + c i * ∏ j ∈ s, a j := by
      rw [prod_insert hi, prod_insert hi]; ring
    have hwi := hw i (mem_insert_self i s)
    have hPw : 0 ≤ ∏ j ∈ s, w j := prod_nonneg hw'
    rw [e]
    refine (tn_addE (by positivity) (by positivity)
      (tn_mulE hh hℓ (by positivity) (hac i (mem_insert_self i s)) ih')
      (tn_mulE hh hℓ (by positivity) (hc i (mem_insert_self i s)) hQ)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [card_insert_of_notMem hi, prod_insert hi, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0]; push_cast; ring
    · obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := ⟨s.card - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel]; push_cast; ring

end Gen

end

end Step

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

section Blocks

variable {j : ℕ}

theorem nb_empty' (j : ℕ) : nb j (∅ : Finset (Lam d L N)) = 0 := by simp [nb, blocks]

theorem nb_union_of_disjoint {A B : Finset (Lam d L N)} (hA : IsPolymer j A)
    (hB : IsPolymer j B) (h : Disjoint A B) : nb j (A ∪ B) = nb j A + nb j B := by
  rw [nb, nb, nb, blocks_union, card_union_of_disjoint (disjoint_blocks hA hB h)]

theorem nb_sdiff_add {Y W : Finset (Lam d L N)} (hY : IsPolymer j Y) (hW : IsPolymer j W)
    (hWY : W ⊆ Y) : nb j (Y \ W) + nb j W = nb j Y := by
  rw [← nb_union_of_disjoint (IsPolymer.sdiff hY hW) hW sdiff_disjoint,
    sdiff_union_of_subset hWY]

theorem nb_eq_zero_iff {X : Finset (Lam d L N)} : nb j X = 0 ↔ X = ∅ := by
  rw [nb, blocks, card_eq_zero, image_eq_empty]

theorem prod_comp_pow {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) (r : ℝ) :
    ∏ W ∈ Comp j Z, r ^ nb j W = r ^ nb j Z :=
  (eq_prod_comp_of_mul (fun X => r ^ nb j X) (by simp [nb_empty'])
    (fun A B hA hB h => by
      rw [nb_union_of_disjoint hA hB (disjoint_of_not_touch h), pow_add]) hZ).symm

theorem dIPow_eq_prod_comp (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) :
    dIPow j C V K Z = ∏ Y ∈ Comp j Z, dIPow j C V K Y :=
  eq_prod_comp_of_mul _ (dIPow_empty j C V K)
    (fun _ _ hA hB h => prod_blocks_union _ hA hB (disjoint_of_not_touch h)) hZ

variable {C : Matrix (Lam d L N) (Lam d L N) ℝ} {V : Vcoup} {K : Act d L N}

/-- `‖e^{-(u+V)_{j+1}(B)}‖ ≤ e^{3a}`. -/
theorem Inext_le {h ℓ a : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (ha : 0 ≤ a) {b : Fin d → ℕ}
    (hu : ‖(uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card‖ ≤ a)
    (hV : tNorm (Dir d) (pPhi d) h ℓ
      ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤ ENNReal.ofReal (2 * a)) :
    tNorm (Dir d) (pPhi d) h ℓ ((Inext j C V K b : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp (3 * a)) := by
  have hεG : ε (((-(VE (uVnext j C V K).2 (blockSet (L := L) (N := N) j b))) :
      EvR (Lam d L N)) : Alg d L N) = 0 := by simp [ε_eval]
  have hGn : tNorm (Dir d) (pPhi d) h ℓ (((-(VE (uVnext j C V K).2
      (blockSet (L := L) (N := N) j b))) : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * a) := by
    simpa [tNorm_neg] using hV
  rw [Inext, SetLike.val_smul]
  refine (tn_smul _ (tNorm_gexp_le hh hℓ hεG (by positivity) hGn)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [Complex.norm_exp, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := neg_abs_le ((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card).re
  have := Complex.abs_re_le_norm ((uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card)
  rw [Complex.neg_re]
  linarith

/-- `‖e^{-(u+V)_{j+1}(B)} - 1‖ ≤ 10 a`. -/
theorem Inext_sub_one_le {h ℓ a : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    {b : Fin d → ℕ}
    (hu : ‖(uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card‖ ≤ a)
    (hV : tNorm (Dir d) (pPhi d) h ℓ
      ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤ ENNReal.ofReal (2 * a)) :
    tNorm (Dir d) (pPhi d) h ℓ ((Inext j C V K b - 1 : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (10 * a) := by
  set c := (uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card
  set G : EvR (Lam d L N) := VE (uVnext j C V K).2 (blockSet (L := L) (N := N) j b)
  have hcabs : ‖-c‖ ≤ 1 := by rw [norm_neg]; linarith
  have hE1 : ‖Complex.exp (-c) - 1‖ ≤ 2 * a :=
    (Complex.norm_exp_sub_one_le hcabs).trans (by rw [norm_neg]; linarith)
  have hE : ‖Complex.exp (-c)‖ ≤ 2 := by
    have := norm_sub_norm_le (Complex.exp (-c)) 1
    rw [norm_one] at this; linarith
  have hεG : ε ((-G : EvR (Lam d L N)) : Alg d L N) = 0 := by simp [G, ε_eval]
  have hGn : tNorm (Dir d) (pPhi d) h ℓ ((-G : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 * a) := by
    simpa [G, tNorm_neg] using hV
  have e : ((Inext j C V K b - 1 : EvR (Lam d L N)) : Alg d L N) =
      Complex.exp (-c) • ((gexp (-G) - 1 : EvR (Lam d L N)) : Alg d L N) +
        (Complex.exp (-c) - 1) • (1 : Alg d L N) := by
    rw [Inext]
    simp only [AddSubgroupClass.coe_sub, OneMemClass.coe_one, SetLike.val_smul]
    module
  rw [e]
  refine (tn_add (by positivity) (by positivity)
    ((tn_smul (Complex.exp (-c)) ((tNorm_gexp_sub_one_le hh hℓ hεG (by positivity) hGn).trans
      (ENNReal.ofReal_le_ofReal (exp_sub_one_le (by positivity) (by linarith))))).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hE (by positivity))))
    ((tn_smul (Complex.exp (-c) - 1) (tn_one hh hℓ)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hE1 (by norm_num))))).trans
    (ENNReal.ofReal_le_ofReal (by nlinarith))

/-- `‖1 - e^{-(u+V)_{j+1}(X)}‖ ≤ |𝓑(X)| 10 a (1 + 10 a)^{|𝓑(X)| - 1}`. -/
theorem one_sub_InextPow_le {h ℓ a : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (ha : 0 ≤ a)
    (ha1 : a ≤ 1 / 4) (X : Finset (Lam d L N))
    (hu : ∀ b ∈ blocks j X, ‖(uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card‖ ≤ a)
    (hV : ∀ b ∈ blocks j X, tNorm (Dir d) (pPhi d) h ℓ
      ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤ ENNReal.ofReal (2 * a)) :
    tNorm (Dir d) (pPhi d) h ℓ ((1 - InextPow j C V K X : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (nb j X * (10 * a) * (1 + 10 * a) ^ (nb j X - 1)) := by
  have key := tn_prod_sub_prod (E := Dir d) (p := pPhi d) hh hℓ (blocks j X)
    (fun _ => (1 : EvR (Lam d L N))) (fun b => Inext j C V K b - 1) (fun _ => 1)
    (β := 1 + 10 * a) (κ := 10 * a) (fun _ _ => zero_le_one) (by positivity) (by linarith)
    (fun b _ => by
      simp only [OneMemClass.coe_one, mul_one]
      refine (tNorm_one_le hh hℓ).trans ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith))
    (fun b hb => by
      simp only [add_sub_cancel, mul_one]
      have h1 := tn_one (X := Lam d L N) (E := Dir d) (p := pPhi d) hh hℓ
      have h2 := Inext_sub_one_le hh hℓ ha ha1 (hu b hb) (hV b hb)
      have := tn_add (by norm_num) (by positivity) h1 h2
      simpa using this)
    (fun b hb => by rw [mul_one]; exact Inext_sub_one_le hh hℓ ha ha1 (hu b hb) (hV b hb))
  simp only [add_sub_cancel, prod_const_one, mul_one] at key
  rw [← neg_sub, NegMemClass.coe_neg, tNorm_neg]
  exact key

/-- `‖e^{u_{j+1}|U|} e^{-(u+V)_{j+1}(U ∖ W)}‖ ≤ e^{4 a |𝓑_j(U)|}`. -/
theorem pref_le {h ℓ a : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (ha : 0 ≤ a) {U : Finset (Lam d L N)}
    (hU : IsPolymer j U) (W : Finset (Lam d L N))
    (hu : ∀ b ∈ blocks j U, ‖(uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card‖ ≤ a)
    (hV : ∀ b ∈ blocks j U, tNorm (Dir d) (pPhi d) h ℓ
      ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤ ENNReal.ofReal (2 * a)) :
    tNorm (Dir d) (pPhi d) h ℓ ((Complex.exp ((uVnext j C V K).1 * U.card) •
      InextPow j C V K (U \ W) : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp (4 * a * nb j U)) := by
  have hsub : blocks j (U \ W) ⊆ blocks j U := blocks_mono sdiff_subset
  have h1 : ((uVnext j C V K).1 * U.card).re ≤ a * nb j U := by
    rw [card_polymer hU]
    push_cast
    rw [mul_sum, Complex.re_sum]
    calc ∑ b ∈ blocks j U, ((uVnext j C V K).1 * ((blockSet (L := L) (N := N) j b).card : ℂ)).re
        ≤ ∑ _b ∈ blocks j U, a := sum_le_sum fun b hb => (Complex.re_le_norm _).trans (hu b hb)
      _ = a * nb j U := by rw [sum_const, nsmul_eq_mul, nb, mul_comm]
  have h2 : tNorm (Dir d) (pPhi d) h ℓ ((InextPow j C V K (U \ W) : EvR (Lam d L N)) :
      Alg d L N) ≤ ENNReal.ofReal (Real.exp (3 * a) ^ nb j (U \ W)) := by
    have := tn_prodE (E := Dir d) (p := pPhi d) hh hℓ (blocks j (U \ W)) (Inext j C V K)
      (fun _ => Real.exp (3 * a)) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => Inext_le hh hℓ ha (hu b (hsub hb)) (hV b (hsub hb)))
    rwa [prod_const] at this
  have hn : nb j (U \ W) ≤ nb j U := card_le_card hsub
  rw [SetLike.val_smul, tNorm_smul, Complex.norm_exp]
  calc ENNReal.ofReal (Real.exp ((uVnext j C V K).1 * U.card).re) *
        tNorm (Dir d) (pPhi d) h ℓ ((InextPow j C V K (U \ W) : EvR (Lam d L N)) : Alg d L N)
      ≤ ENNReal.ofReal (Real.exp (a * nb j U)) *
          ENNReal.ofReal (Real.exp (3 * a) ^ nb j U) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h1))
          (h2.trans (ENNReal.ofReal_le_ofReal
            (pow_le_pow_right₀ (Real.one_le_exp (by positivity)) hn)))
    _ = ENNReal.ofReal (Real.exp (4 * a * nb j U)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 2; ring

end Blocks

section Geom

variable {j : ℕ}

/-- The number of `(j+1)`-blocks of `U` is controlled by `X̌` and `|𝒳|`. -/
theorem nU_bound {η : ℝ}
    (hcomb : ∀ X : Finset (Lam d L N), IsPolymer j X →
      (1 + 2 * η) * (nb (j + 1) (clo j X) : ℝ) ≤ nb j X + (1 + 2 * η) * 2 ^ d * (Comp j X).card)
    (hsmall : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      nb (j + 1) (clo j (nbhd j (blockSet (L := L) (N := N) j b))) ≤ 2 ^ d)
    (hη : 0 ≤ η) {U : Finset (Lam d L N)} {g : GT d L N} (hg : g ∈ Gset j U) :
    (1 + 2 * η) * (nb (j + 1) U : ℝ) ≤
      nb j g.2 + (1 + 2 * η) * 2 ^ d * ((Comp j g.2).card + g.1.card) := by
  obtain ⟨h1, h2, -, -, -, h6⟩ := mem_Gset'.1 hg
  have e1 : nb (j + 1) U ≤ nb (j + 1) (clo j g.2) + 2 ^ d * g.1.card := by
    rw [← h6, nb, blocks_clo, blocks_union]
    refine (card_union_le _ _).trans (add_le_add (le_of_eq (by rw [nb, blocks_clo])) ?_)
    rw [Bbox, blocks, biUnion_image]
    refine card_biUnion_le.trans ?_
    calc ∑ p ∈ g.1, ((nbhd j (blockSet (L := L) (N := N) j p.1)).image (blk (j + 1))).card
        ≤ ∑ _p ∈ g.1, 2 ^ d := sum_le_sum fun p hp => by
          have := hsmall p.1 (mem_pairsU.1 (h2 hp)).1
          rwa [nb, blocks_clo] at this
      _ = 2 ^ d * g.1.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have e1' : (nb (j + 1) U : ℝ) ≤ nb (j + 1) (clo j g.2) + 2 ^ d * g.1.card := by
    exact_mod_cast e1
  have := hcomb g.2 h1
  nlinarith

/-- The number of elements of `𝒢(U)`. -/
theorem card_Gset_le {c : ℕ}
    (hc : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      ((smallSets (d := d) (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).card ≤ c)
    {U : Finset (Lam d L N)} (hU : IsPolymer j U) :
    (Gset j U).card ≤ 2 ^ ((1 + c) * nb j U) := by
  classical
  set S := (blocks j U).biUnion (fun b =>
    ((smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).image (Prod.mk b))
  have hsub : Gset j U ⊆ S.powerset ×ˢ Pj j U := by
    intro g hg
    obtain ⟨f1, f2, -, f4⟩ := Gset_facts hg
    rw [mem_product, mem_powerset, mem_Pj]
    refine ⟨fun p hp => ?_, f2, f1⟩
    obtain ⟨hpU, -, hbU, -⟩ := f4 p hp
    obtain ⟨hb, hs, hbs⟩ := mem_pairsU.1 hpU
    exact mem_biUnion.2 ⟨p.1, mem_blocks_of_blockSet_subset (mem_blockIdx.1 hb) hbU,
      mem_image.2 ⟨p.2, mem_filter.2 ⟨mem_smallSets.2 hs, hbs⟩, rfl⟩⟩
  have hS : S.card ≤ c * nb j U := by
    refine card_biUnion_le.trans ?_
    calc ∑ b ∈ blocks j U, (((smallSets (L := L) (N := N) j).filter
          (fun X => blockSet j b ⊆ X)).image (Prod.mk b)).card
        ≤ ∑ _b ∈ blocks j U, c := sum_le_sum fun b hb =>
          card_image_le.trans (hc b (mem_blockIdx_of_mem_blocks hb))
      _ = c * nb j U := by rw [sum_const, smul_eq_mul, nb, mul_comm]
  calc (Gset j U).card ≤ (S.powerset ×ˢ Pj j U).card := card_le_card hsub
    _ = 2 ^ S.card * 2 ^ nb j U := by rw [card_product, card_powerset, card_Pj hU]
    _ ≤ 2 ^ (c * nb j U) * 2 ^ nb j U := by gcongr; norm_num
    _ = 2 ^ ((1 + c) * nb j U) := by rw [← pow_add]; ring_nf

end Geom

end

end Step

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

theorem tn_zero' {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
    [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ} : tNorm E p h ℓ (0 : Grassmann.N X) = 0 := by
  have := tNorm_smul (E := E) (p := p) (h := h) (ℓ := ℓ) (0 : ℂ) (0 : Grassmann.N X)
  simpa using this

variable {d L N : ℕ} [NeZero L]

/-- The hypotheses for Lemma `lem:NonlinearCheckK`: `ρ = A⁻¹`, `‖K(W)‖ ≤ κ₀ ρ^{|𝓑(W)|}`,
`‖δI(B)‖ ≤ δ₁ ρ`, `‖θ J(B, X)‖ ≤ c_J κ₀ ρ^{2^d}`. -/
structure KHyp (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    (h ℓ h' ℓ' A κ₀ δ₁ cJ : ℝ) : Prop where
  hh : 0 < h
  hℓ : 0 < ℓ
  hh' : 0 < h'
  hℓ' : 0 < ℓ'
  hA : 1 ≤ A
  hκ₀ : 0 ≤ κ₀
  hκ₀1 : κ₀ ≤ 1
  hδ₁ : 0 ≤ δ₁
  hδ₁1 : δ₁ ≤ 1
  hcJ : 0 ≤ cJ
  hθ : ∀ F : Alg d L N, tNorm (Dir d) (pPhi d) h' ℓ' (theta F) ≤ tNorm (Dir d) (pPhi d) h ℓ F
  hK : ∀ W : Finset (Lam d L N), IsConn j W →
    tNorm (Dir d) (pPhi d) h ℓ (K W : Alg d L N) ≤ ENNReal.ofReal (κ₀ * A⁻¹ ^ nb j W)
  hdI : ∀ b ∈ blockIdx (L := L) (N := N) j,
    tNorm (Dir d) (pPhi d) h' ℓ' (dI j C V K b : Alg2 d L N) ≤ ENNReal.ofReal (δ₁ * A⁻¹)
  hJ : ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
    tNorm (Dir d) (pPhi d) h' ℓ' (theta (Jb j K b X : Alg d L N)) ≤
      ENNReal.ofReal (cJ * κ₀ * A⁻¹ ^ 2 ^ d)

namespace KHyp

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {V : Vcoup} {K : Act d L N}
  {h ℓ h' ℓ' A κ₀ δ₁ cJ : ℝ} (H : KHyp j C V K h ℓ h' ℓ' A κ₀ δ₁ cJ)
include H

theorem hρ0 : 0 < A⁻¹ := inv_pos.2 (by linarith [H.hA])

theorem hρ1 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ H.hA

theorem Kext_le {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) :
    tNorm (Dir d) (pPhi d) h' ℓ' (theta (Kext j K Z : Alg d L N)) ≤
      ENNReal.ofReal (κ₀ ^ (Comp j Z).card * A⁻¹ ^ nb j Z) := by
  refine (H.hθ _).trans ?_
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have := tn_prodE (E := Dir d) (p := pPhi d) H.hh H.hℓ (Comp j Z) K
    (fun W => κ₀ * A⁻¹ ^ nb j W) (fun W _ => by positivity)
    (fun W hW => H.hK W (isConn_of_mem_comp hZ hW))
  rwa [prod_mul_distrib, prod_const, prod_comp_pow hZ] at this

theorem dIPow_le (W : Finset (Lam d L N)) :
    tNorm (Dir d) (pPhi d) h' ℓ' (dIPow j C V K W : Alg2 d L N) ≤
      ENNReal.ofReal ((δ₁ * A⁻¹) ^ nb j W) := by
  have hρ := H.hρ0
  have hδ := H.hδ₁
  have := tn_prodE (E := Dir d) (p := pPhi d) H.hh' H.hℓ' (blocks j W) (dI j C V K)
    (fun _ => δ₁ * A⁻¹) (fun _ _ => by positivity)
    (fun b hb => H.hdI b (mem_blockIdx_of_mem_blocks hb))
  rwa [prod_const] at this

/-- A term of `K̃(Y)` with `W ≠ Y`. -/
theorem tterm_le {Y W : Finset (Lam d L N)} (hY : IsPolymer j Y) (hW : W ∈ Pj j Y)
    (hWY : W ≠ Y) :
    tNorm (Dir d) (pPhi d) h' ℓ'
      ((thetaE (Kext j K (Y \ W)) * dIPow j C V K W : EvR (Lam d L N ⊕ Lam d L N)) :
        Alg2 d L N) ≤ ENNReal.ofReal (κ₀ * δ₁ ^ nb j W * A⁻¹ ^ nb j Y) := by
  have hρ := H.hρ0
  have hδ := H.hδ₁
  have hκ := H.hκ₀
  obtain ⟨hWs, hWp⟩ := mem_Pj.1 hW
  have hYW : IsPolymer j (Y \ W) := IsPolymer.sdiff hY hWp
  have h1 := H.Kext_le hYW
  rw [← coe_thetaE] at h1
  refine (tn_mulE H.hh' H.hℓ' (by positivity) h1 (H.dIPow_le W)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hne : Y \ W ≠ ∅ := by
    intro he
    exact hWY (Subset.antisymm hWs (sdiff_eq_empty_iff_subset.1 he))
  have hc : (Comp j (Y \ W)).card ≠ 0 := fun h0 => hne ((comp_card_eq_zero_iff hYW).1 h0)
  have hk : κ₀ ^ (Comp j (Y \ W)).card ≤ κ₀ := pow_le_of_le_one hκ H.hκ₀1 hc
  have e : A⁻¹ ^ nb j (Y \ W) * A⁻¹ ^ nb j W = A⁻¹ ^ nb j Y := by
    rw [← pow_add, nb_sdiff_add hY hWp hWs]
  calc κ₀ ^ (Comp j (Y \ W)).card * A⁻¹ ^ nb j (Y \ W) * (δ₁ * A⁻¹) ^ nb j W
      = κ₀ ^ (Comp j (Y \ W)).card * δ₁ ^ nb j W * (A⁻¹ ^ nb j (Y \ W) * A⁻¹ ^ nb j W) := by
        rw [mul_pow]; ring
    _ ≤ κ₀ * δ₁ ^ nb j W * A⁻¹ ^ nb j Y := by rw [e]; gcongr

theorem Ktil_split {Y : Finset (Lam d L N)} (hY : IsPolymer j Y) :
    Ktil j C V K Y = dIPow j C V K Y +
      ∑ W ∈ (Pj j Y).erase Y, thetaE (Kext j K (Y \ W)) * dIPow j C V K W := by
  have hYm : Y ∈ Pj j Y := mem_Pj.2 ⟨subset_rfl, hY⟩
  rw [Ktil, ← add_sum_erase _ _ hYm, sdiff_self, bot_eq_empty, Kext_empty, map_one, one_mul]

theorem sum_erase_split {Y : Finset (Lam d L N)} (hY : IsConn j Y) :
    ∑ W ∈ (Pj j Y).erase Y, thetaE (Kext j K (Y \ W)) * dIPow j C V K W =
      thetaE (K Y) + ∑ W ∈ ((Pj j Y).erase Y).erase ∅,
        thetaE (Kext j K (Y \ W)) * dIPow j C V K W := by
  have hne : (∅ : Finset (Lam d L N)) ≠ Y := fun h => not_isConn_empty (h ▸ hY)
  have hm : (∅ : Finset (Lam d L N)) ∈ (Pj j Y).erase Y :=
    mem_erase.2 ⟨hne, mem_Pj.2 ⟨empty_subset _, isPolymer_empty j⟩⟩
  rw [← add_sum_erase _ _ hm, sdiff_empty, dIPow_empty, mul_one, Kext, comp_of_isConn hY,
    prod_singleton]

theorem Jsum_le {Y : Finset (Lam d L N)} :
    tNorm (Dir d) (pPhi d) h' ℓ'
      ((∑ b ∈ blocks j Y, thetaE (Jb j K b Y) : EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
      ENNReal.ofReal (2 ^ d * cJ * κ₀ * A⁻¹ ^ nb j Y) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  classical
  by_cases hs : IsSmall j Y
  · have := tn_sum_const (E := Dir d) (p := pPhi d) (blocks j Y) (fun b => thetaE (Jb j K b Y))
      (r := cJ * κ₀ * A⁻¹ ^ 2 ^ d) (by positivity)
      (fun b hb => by rw [coe_thetaE]; exact H.hJ b (mem_blockIdx_of_mem_blocks hb) Y)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have hn : ((blocks j Y).card : ℝ) ≤ 2 ^ d := by exact_mod_cast hs.2.2
    have hp : A⁻¹ ^ 2 ^ d ≤ A⁻¹ ^ nb j Y := pow_le_pow_of_le_one hρ.le H.hρ1 hs.2.2
    calc ((blocks j Y).card : ℝ) * (cJ * κ₀ * A⁻¹ ^ 2 ^ d)
        ≤ 2 ^ d * (cJ * κ₀ * A⁻¹ ^ nb j Y) := by gcongr
      _ = 2 ^ d * cJ * κ₀ * A⁻¹ ^ nb j Y := by ring
  · have h0 : (∑ b ∈ blocks j Y, thetaE (Jb j K b Y) : EvR (Lam d L N ⊕ Lam d L N)) = 0 := by
      refine sum_eq_zero fun b _ => ?_
      rw [Jb, if_neg (fun h => hs h.2.1), map_zero]
    rw [h0, ZeroMemClass.coe_zero, tn_zero']
    exact zero_le

theorem card_erase_Pj_le {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (s : Finset (Finset (Lam d L N))) (hs : s ⊆ Pj j Y) : (s.card : ℝ) ≤ 2 ^ nb j Y := by
  have := (card_le_card hs).trans (card_Pj hY).le
  exact_mod_cast this

/-- **Lemma `lem:NonlinearCheckK`** for a connected `Y`, with `β = (1 + 2^d c_J) κ₀ + δ₁` and
`κ = (1 + 2^d c_J) κ₀`. -/
theorem KchkC_bounds {Y : Finset (Lam d L N)} (hY : IsConn j Y) :
    tNorm (Dir d) (pPhi d) h' ℓ' (KchkC j C V K Y : Alg2 d L N) ≤
        ENNReal.ofReal (((1 + 2 ^ d * cJ) * κ₀ + δ₁) * (2 * A⁻¹) ^ nb j Y) ∧
      tNorm (Dir d) (pPhi d) h' ℓ' ((KchkC j C V K Y - dIPow j C V K Y :
        EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
        ENNReal.ofReal ((1 + 2 ^ d * cJ) * κ₀ * (2 * A⁻¹) ^ nb j Y) ∧
      tNorm (Dir d) (pPhi d) h' ℓ' (dIPow j C V K Y : Alg2 d L N) ≤
        ENNReal.ofReal (((1 + 2 ^ d * cJ) * κ₀ + δ₁) * (2 * A⁻¹) ^ nb j Y) ∧
      tNorm (Dir d) (pPhi d) h' ℓ' ((KchkC j C V K Y - thetaE (K Y) - dIPow j C V K Y +
        ∑ b ∈ blocks j Y, thetaE (Jb j K b Y) : EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
        ENNReal.ofReal (κ₀ * δ₁ * (2 * A⁻¹) ^ nb j Y) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  have hYp := hY.1
  have hnb : nb j Y ≠ 0 := fun h0 => (nonempty_iff_ne_empty.1 hY.2.1) (nb_eq_zero_iff.1 h0)
  have h2p : (2 * A⁻¹) ^ nb j Y = 2 ^ nb j Y * A⁻¹ ^ nb j Y := mul_pow _ _ _
  have hp1 : A⁻¹ ^ nb j Y ≤ (2 * A⁻¹) ^ nb j Y := by
    rw [h2p]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  set S1 := ∑ W ∈ (Pj j Y).erase Y, thetaE (Kext j K (Y \ W)) * dIPow j C V K W
  set S2 := ∑ W ∈ ((Pj j Y).erase Y).erase ∅, thetaE (Kext j K (Y \ W)) * dIPow j C V K W
  set SJ := ∑ b ∈ blocks j Y, thetaE (Jb j K b Y)
  have hsp := H.Ktil_split (C := C) (V := V) hYp
  have hsp2 := H.sum_erase_split (C := C) (V := V) hY
  have hS1 : tNorm (Dir d) (pPhi d) h' ℓ' (S1 : Alg2 d L N) ≤
      ENNReal.ofReal (κ₀ * (2 * A⁻¹) ^ nb j Y) := by
    refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := κ₀ * A⁻¹ ^ nb j Y) (by positivity)
      fun W hW => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · refine (H.tterm_le hYp (mem_of_mem_erase hW) (ne_of_mem_erase hW)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have : δ₁ ^ nb j W ≤ 1 := pow_le_one₀ hδ H.hδ₁1
      calc κ₀ * δ₁ ^ nb j W * A⁻¹ ^ nb j Y ≤ κ₀ * 1 * A⁻¹ ^ nb j Y := by gcongr
        _ = _ := by ring
    · have := H.card_erase_Pj_le hYp _ (erase_subset Y (Pj j Y))
      rw [h2p]
      calc (((Pj j Y).erase Y).card : ℝ) * (κ₀ * A⁻¹ ^ nb j Y)
          ≤ 2 ^ nb j Y * (κ₀ * A⁻¹ ^ nb j Y) := by gcongr
        _ = _ := by ring
  have hS2 : tNorm (Dir d) (pPhi d) h' ℓ' (S2 : Alg2 d L N) ≤
      ENNReal.ofReal (κ₀ * δ₁ * (2 * A⁻¹) ^ nb j Y) := by
    refine (tn_sum_const (E := Dir d) (p := pPhi d) _ _ (r := κ₀ * δ₁ * A⁻¹ ^ nb j Y)
      (by positivity) fun W hW => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · have hW1 := mem_of_mem_erase hW
      have hW0 : W ≠ ∅ := ne_of_mem_erase hW
      refine (H.tterm_le hYp (mem_of_mem_erase hW1) (ne_of_mem_erase hW1)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hn : nb j W ≠ 0 := fun h0 => hW0 (nb_eq_zero_iff.1 h0)
      have : δ₁ ^ nb j W ≤ δ₁ := pow_le_of_le_one hδ H.hδ₁1 hn
      gcongr
    · have := H.card_erase_Pj_le hYp _ ((erase_subset ∅ _).trans (erase_subset Y (Pj j Y)))
      rw [h2p]
      calc ((((Pj j Y).erase Y).erase ∅).card : ℝ) * (κ₀ * δ₁ * A⁻¹ ^ nb j Y)
          ≤ 2 ^ nb j Y * (κ₀ * δ₁ * A⁻¹ ^ nb j Y) := by gcongr
        _ = _ := by ring
  have hSJ : tNorm (Dir d) (pPhi d) h' ℓ' (SJ : Alg2 d L N) ≤
      ENNReal.ofReal (2 ^ d * cJ * κ₀ * (2 * A⁻¹) ^ nb j Y) :=
    H.Jsum_le.trans (ENNReal.ofReal_le_ofReal (by gcongr))
  have hdIY : tNorm (Dir d) (pPhi d) h' ℓ' (dIPow j C V K Y : Alg2 d L N) ≤
      ENNReal.ofReal (δ₁ * (2 * A⁻¹) ^ nb j Y) := by
    refine (H.dIPow_le Y).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_pow]
    have : δ₁ ^ nb j Y ≤ δ₁ := pow_le_of_le_one hδ H.hδ₁1 hnb
    gcongr
  have e2 : KchkC j C V K Y - dIPow j C V K Y = S1 - SJ := by
    rw [KchkC, hsp]; ring
  have hB2 : tNorm (Dir d) (pPhi d) h' ℓ' ((KchkC j C V K Y - dIPow j C V K Y :
      EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
      ENNReal.ofReal ((1 + 2 ^ d * cJ) * κ₀ * (2 * A⁻¹) ^ nb j Y) := by
    rw [e2]
    exact (tn_subE (by positivity) (by positivity) hS1 hSJ).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  refine ⟨?_, hB2, ?_, ?_⟩
  · have e1 : KchkC j C V K Y = dIPow j C V K Y + (KchkC j C V K Y - dIPow j C V K Y) := by
      ring
    rw [e1]
    exact (tn_addE (by positivity) (by positivity) hdIY hB2).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  · refine hdIY.trans (ENNReal.ofReal_le_ofReal ?_)
    have : δ₁ ≤ (1 + 2 ^ d * cJ) * κ₀ + δ₁ := by
      have : 0 ≤ (1 + 2 ^ d * cJ) * κ₀ := by positivity
      linarith
    gcongr
  · have e4 : KchkC j C V K Y - thetaE (K Y) - dIPow j C V K Y + SJ = S2 := by
      rw [KchkC, hsp, hsp2]; ring
    rw [e4]; exact hS2

end KHyp

end

end Step

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

/-! ### Real inequalities -/

/-- The geometric factor: `A^x P^x (4/A)^t ≤ (AP)^{2^d m}` if
`(1+2η) x ≤ t + (1+2η) 2^d m` and `4P ≤ A^{2η/(1+2η)}`. -/
theorem geom_real {d x t m : ℕ} {A P η : ℝ} (hA : 1 ≤ A) (hP : 1 ≤ P) (hη : 0 ≤ η)
    (hx : (1 + 2 * η) * (x : ℝ) ≤ t + (1 + 2 * η) * 2 ^ d * m)
    (hAP : 4 * P ≤ A ^ (2 * η / (1 + 2 * η))) :
    A ^ x * P ^ x * (4 * A⁻¹) ^ t ≤ (A * P) ^ (2 ^ d * m) := by
  have hA0 : 0 < A := by linarith
  have h1η : 0 < 1 + 2 * η := by linarith
  set s := 2 * η / (1 + 2 * η) with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs, div_le_one h1η]; linarith
  -- `x ≤ (1 - s) t + 2^d m`
  have hx' : (x : ℝ) ≤ (1 - s) * t + 2 ^ d * m := by
    have e : (1 - s) = 1 / (1 + 2 * η) := by rw [hs]; field_simp; ring
    rw [e]
    rw [← mul_le_mul_iff_of_pos_left h1η]
    have : (1 + 2 * η) * (1 / (1 + 2 * η) * t + 2 ^ d * m) = t + (1 + 2 * η) * 2 ^ d * m := by
      field_simp
    rw [this]; exact hx
  have hxn : x ≤ t + 2 ^ d * m := by
    have : (x : ℝ) ≤ t + 2 ^ d * m := by
      have : (1 - s) * (t : ℝ) ≤ t := by
        have := Nat.cast_nonneg (α := ℝ) t
        nlinarith
      linarith
    exact_mod_cast this
  have hPx : P ^ x ≤ P ^ t * P ^ (2 ^ d * m) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hP hxn
  have h4 : (4 * P) ^ t ≤ A ^ (s * t) := by
    rw [Real.rpow_mul hA0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hAP t
  have hexp : (x : ℝ) + -(t : ℝ) + s * t ≤ ((2 ^ d * m : ℕ) : ℝ) := by
    push_cast; nlinarith
  have hAx : A ^ x * A⁻¹ ^ t * A ^ (s * t) ≤ A ^ (2 ^ d * m) := by
    rw [← Real.rpow_natCast A x, inv_pow, ← Real.rpow_natCast A t, ← Real.rpow_neg hA0.le,
      ← Real.rpow_add hA0, ← Real.rpow_add hA0, ← Real.rpow_natCast A (2 ^ d * m)]
    exact Real.rpow_le_rpow_of_exponent_le hA hexp
  calc A ^ x * P ^ x * (4 * A⁻¹) ^ t = A ^ x * A⁻¹ ^ t * (P ^ x * 4 ^ t) := by
        rw [mul_pow]; ring
    _ ≤ A ^ x * A⁻¹ ^ t * (P ^ t * P ^ (2 ^ d * m) * 4 ^ t) := by gcongr
    _ = A ^ x * A⁻¹ ^ t * (4 * P) ^ t * P ^ (2 ^ d * m) := by rw [mul_pow]; ring
    _ ≤ A ^ x * A⁻¹ ^ t * A ^ (s * t) * P ^ (2 ^ d * m) := by gcongr
    _ ≤ A ^ (2 ^ d * m) * P ^ (2 ^ d * m) := by gcongr
    _ = (A * P) ^ (2 ^ d * m) := by rw [mul_pow]

/-- `D^m κ β^{m-1} ≤ D^2 κ β` for `m ≥ 2` and `D β ≤ 1`, with `D = (AP)^{2^d}`. -/
theorem pow_m_real {D κ β : ℝ} {m : ℕ} (hD : 0 ≤ D) (hκ : 0 ≤ κ) (hβ : 0 ≤ β)
    (hDβ : D * β ≤ 1) (hm : 2 ≤ m) : D ^ m * (κ * β ^ (m - 1)) ≤ D ^ 2 * (κ * β) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e : D ^ (k + 2) * (κ * β ^ (k + 2 - 1)) = D ^ 2 * (κ * β) * (D * β) ^ k := by
    rw [show k + 2 - 1 = k + 1 by omega, mul_pow]; ring
  rw [e]
  have : (D * β) ^ k ≤ 1 := pow_le_one₀ (by positivity) hDβ
  have : 0 ≤ D ^ 2 * (κ * β) := by positivity
  nlinarith

/-! ### Summation -/

theorem sum_le_of_card_mul {ι : Type*} (s : Finset ι) (f : ι → ENNReal) (Q : ENNReal) (M : ℕ)
    (hs : s.card ≤ M) (hf : ∀ i ∈ s, (M : ENNReal) * f i ≤ Q) : ∑ i ∈ s, f i ≤ Q := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    rw [card_eq_zero.1 (Nat.le_zero.1 hs), sum_empty]; exact zero_le
  · have hM0 : (M : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
    have hMt : (M : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top M
    refine (ENNReal.mul_le_mul_iff_right hM0 hMt).1 ?_
    calc (M : ENNReal) * ∑ i ∈ s, f i = ∑ i ∈ s, (M : ENNReal) * f i := mul_sum _ _ _
      _ ≤ ∑ _i ∈ s, Q := sum_le_sum hf
      _ = s.card * Q := by rw [sum_const, nsmul_eq_mul]
      _ ≤ M * Q := by gcongr

section

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-- Weighted sum bound: if `M ≥ |S|` and `M w ‖F_g‖ ≤ Q` for all `g`, then `w ‖∑ F_g‖ ≤ Q`. -/
theorem wsum_bound {ι : Type*} (S : Finset ι) (F : ι → EvR X) (M : ℕ) (hS : S.card ≤ M)
    {w Q : ℝ} (hw : 0 ≤ w)
    (hF : ∀ g ∈ S, ENNReal.ofReal (M * w) * tNorm E p h ℓ (F g : Grassmann.N X) ≤
      ENNReal.ofReal Q) :
    ENNReal.ofReal w * tNorm E p h ℓ ((∑ g ∈ S, F g : EvR X) : Grassmann.N X) ≤
      ENNReal.ofReal Q := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine (mul_le_mul_left' (tNorm_sum_le _ _) _).trans ?_
  rw [mul_sum]
  refine sum_le_of_card_mul S _ _ M hS fun g hg => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact hF g hg

end

variable {d L N : ℕ} [NeZero L]

/-! ### `𝓡^1`: the cancellation `∑_X J(B, X) = 0` (`e:J-zero`) -/

section R1

variable {j : ℕ}

theorem J_zero (K : Act d L N) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X), Jb j K b X = 0 := by
  classical
  by_cases hN : j + 1 < N
  · have hBs := isSmall_blockSet_of_mem hb
    have hBm : blockSet j b ∈ (smallSets (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X) := mem_filter.2 ⟨mem_smallSets.2 hBs, subset_rfl⟩
    rw [← add_sum_erase _ _ hBm, Jb, if_pos ⟨hN, hBs, subset_rfl⟩, if_pos rfl,
      neg_add_eq_zero]
    refine sum_congr ?_ fun Y hY => ?_
    · ext Y; simp only [mem_erase, mem_filter]; tauto
    · obtain ⟨hne, hY'⟩ := mem_erase.1 hY
      obtain ⟨hYs, hBY⟩ := mem_filter.1 hY'
      rw [Jb, if_pos ⟨hN, mem_smallSets.1 hYs, hBY⟩, if_neg hne]
  · exact sum_eq_zero fun X _ => by rw [Jb, if_neg (fun h => hN h.1)]

theorem Jprod_sum_R1 (K : Act d L N) (U : Finset (Lam d L N)) :
    ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅), Jprod j K g.1 = 0 := by
  classical
  set P1 := (pairsU (L := L) (N := N) j).filter
    (fun p => clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U)
  have hbij : ∑ p ∈ P1, thetaE (Jb j K p.1 p.2) =
      ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅), Jprod j K g.1 := by
    refine sum_bij (fun p _ => (({p} : Finset _), (∅ : Finset (Lam d L N)))) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      refine mem_filter.2 ⟨mem_Gset.2 ⟨isPolymer_empty j, singleton_subset_iff.2 hp1, ?_, ?_, ?_,
        ?_⟩, card_singleton p, rfl⟩
      · intro a ha b hb _; rw [mem_singleton.1 ha, mem_singleton.1 hb]
      · intro a ha b hb hne
        exact absurd (by rw [mem_singleton.1 ha, mem_singleton.1 hb]) hne
      · exact fun h => not_touch_empty_left _ (touch_symm h)
      · simpa [Bbox] using hp2
    · intro a _ b _ e
      simpa using congrArg Prod.fst e
    · intro g hg
      obtain ⟨hg, h1, h2⟩ := mem_filter.1 hg
      obtain ⟨p, hp⟩ := card_eq_one.1 h1
      obtain ⟨-, hsub, -, -, -, hclo⟩ := mem_Gset'.1 hg
      refine ⟨p, mem_filter.2 ⟨singleton_subset_iff.1 (hp ▸ hsub), ?_⟩, ?_⟩
      · rw [hp, h2] at hclo; simpa [Bbox] using hclo
      · exact Prod.ext hp.symm h2.symm
    · intro p _
      rw [Jprod, prod_singleton]
  rw [← hbij, ← map_sum]
  have h0 : ∑ p ∈ P1, Jb j K p.1 p.2 = 0 := by
    have eP : P1 = (blockIdx (L := L) (N := N) j ×ˢ smallSets (L := L) (N := N) j).filter
        (fun p => blockSet j p.1 ⊆ p.2 ∧
          clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U) := by
      ext p; simp [P1, pairsU, and_assoc]
    rw [eP, sum_filter, sum_product]
    refine sum_eq_zero fun b hb => ?_
    by_cases hc : clo j (nbhd j (blockSet (L := L) (N := N) j b)) = U
    · simp only [hc, and_true]
      rw [← sum_filter]
      exact J_zero K hb
    · simp [hc]
  rw [h0, map_zero]

theorem R1_eq (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    R1 j C V K U = ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      (Complex.exp ((uVnext j C V K).1 * U.card) • InextPow j C V K (U \ Xcal g.1)) *
        ((1 - InextPow j C V K (Xcal g.1)) * ECE C (Jprod j K g.1)) := by
  classical
  set S := (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅)
  have h0 : ∑ g ∈ S, InextPow j C V K U * ECE C (Jprod j K g.1) = 0 := by
    rw [← mul_sum, ← map_sum, Jprod_sum_R1, map_zero, mul_zero]
  rw [R1, ← sub_zero (∑ g ∈ S, InextPow j C V K (U \ Xcal g.1) * ECE C (Jprod j K g.1)), ← h0,
    ← sum_sub_distrib, smul_sum]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨-, -, hX, f4⟩ := Gset_facts (mem_filter.1 hg).1
  have hXp : IsPolymer j (Xcal g.1) := isPolymer_Xcal fun p hp => (f4 p hp).1
  have hUj : IsPolymer j U := IsPolymer.of_succ hU
  have eI : InextPow j C V K U = InextPow j C V K (U \ Xcal g.1) * InextPow j C V K (Xcal g.1) := by
    conv_lhs => rw [← sdiff_union_of_subset hX]
    exact InextPow_union j C V K (IsPolymer.sdiff hUj hXp) hXp sdiff_disjoint
  rw [eI, smul_mul_assoc]
  congr 1
  ring

end R1

end

end Step

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

namespace KHyp

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {V : Vcoup} {K : Act d L N}
  {h ℓ h' ℓ' A κ₀ δ₁ cJ : ℝ} (H : KHyp j C V K h ℓ h' ℓ' A κ₀ δ₁ cJ)
include H

theorem thetaJ_le_kappa {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) :
    tNorm (Dir d) (pPhi d) h' ℓ' (thetaE (Jb j K b X) : Alg2 d L N) ≤
      ENNReal.ofReal ((1 + 2 ^ d * cJ) * κ₀) := by
  rw [coe_thetaE]
  refine (H.hJ b hb X).trans (ENNReal.ofReal_le_ofReal ?_)
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  have h1 : A⁻¹ ^ 2 ^ d ≤ 1 := pow_le_one₀ hρ.le H.hρ1
  have h2 : cJ ≤ 1 + 2 ^ d * cJ := by
    have : cJ ≤ 2 ^ d * cJ := le_mul_of_one_le_left hc (one_le_pow₀ (by norm_num))
    linarith
  calc cJ * κ₀ * A⁻¹ ^ 2 ^ d ≤ cJ * κ₀ * 1 := by gcongr
    _ ≤ (1 + 2 ^ d * cJ) * κ₀ := by rw [mul_one]; gcongr

/-- The integrand of `𝓡^2`: `‖(Ǩ(X̌) - 1_{𝒳 = ∅} (δI)^{X̌}) ∏ θ J‖ ≤ κ β^{m-1} (4/A)^{|𝓑(X̌)|}`. -/
theorem R2_integrand_le {g : GT d L N} (hg2 : IsPolymer j g.2)
    (hg1 : ∀ p ∈ g.1, p.1 ∈ blockIdx (L := L) (N := N) j)
    (hm : 2 ≤ g.1.card + (Comp j g.2).card) :
    tNorm (Dir d) (pPhi d) h' ℓ' (((Kchk j C V K g.2 - if g.1 = ∅ then dIPow j C V K g.2 else 0) *
      Jprod j K g.1 : EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
      ENNReal.ofReal ((1 + 2 ^ d * cJ) * κ₀ *
        ((1 + 2 ^ d * cJ) * κ₀ + δ₁) ^ (g.1.card + (Comp j g.2).card - 1) *
          (4 * A⁻¹) ^ nb j g.2) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  set κ := (1 + 2 ^ d * cJ) * κ₀ with hκdef
  set β := (1 + 2 ^ d * cJ) * κ₀ + δ₁ with hβdef
  have hκ0 : 0 ≤ κ := by positivity
  have hκβ : κ ≤ β := by linarith
  have hβ0 : 0 ≤ β := hκ0.trans hκβ
  have hB := fun Y (hY : Y ∈ Comp j g.2) => H.KchkC_bounds (C := C) (V := V) (K := K)
    (isConn_of_mem_comp hg2 hY)
  have h4 : (4 * A⁻¹) ^ nb j g.2 = 2 ^ nb j g.2 * (2 * A⁻¹) ^ nb j g.2 := by
    rw [← mul_pow]; ring_nf
  have hw : ∏ Y ∈ Comp j g.2, (2 * A⁻¹) ^ nb j Y = (2 * A⁻¹) ^ nb j g.2 := prod_comp_pow hg2 _
  by_cases h1 : g.1 = ∅
  · have hJ1 : Jprod j K g.1 = 1 := by rw [h1, Jprod, prod_empty]
    rw [if_pos h1, hJ1, mul_one]
    have e : Kchk j C V K g.2 - dIPow j C V K g.2 =
        ∏ Y ∈ Comp j g.2, (dIPow j C V K Y + (KchkC j C V K Y - dIPow j C V K Y)) -
          ∏ Y ∈ Comp j g.2, dIPow j C V K Y := by
      rw [Kchk, dIPow_eq_prod_comp C V K hg2]; simp only [add_sub_cancel]
    rw [e]
    refine (tn_prod_sub_prod (E := Dir d) (p := pPhi d) H.hh' H.hℓ' (Comp j g.2)
      (dIPow j C V K) (fun Y => KchkC j C V K Y - dIPow j C V K Y) (fun Y => (2 * A⁻¹) ^ nb j Y)
      (β := β) (κ := κ) (fun _ _ => by positivity) hκ0 hκβ (fun Y hY => (hB Y hY).2.2.1)
      (fun Y hY => by simp only [add_sub_cancel]; exact (hB Y hY).1)
      (fun Y hY => (hB Y hY).2.1)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hw, h1, card_empty, zero_add, h4]
    have hn : ((Comp j g.2).card : ℝ) ≤ 2 ^ nb j g.2 := by
      have := (card_comp_le (j := j) (X := g.2)).trans (Nat.lt_two_pow_self).le
      exact_mod_cast this
    calc ((Comp j g.2).card : ℝ) * κ * β ^ ((Comp j g.2).card - 1) * (2 * A⁻¹) ^ nb j g.2
        ≤ 2 ^ nb j g.2 * κ * β ^ ((Comp j g.2).card - 1) * (2 * A⁻¹) ^ nb j g.2 := by gcongr
      _ = _ := by ring
  · rw [if_neg h1, sub_zero]
    have hK1 : tNorm (Dir d) (pPhi d) h' ℓ' (Kchk j C V K g.2 : Alg2 d L N) ≤
        ENNReal.ofReal (β ^ (Comp j g.2).card * (2 * A⁻¹) ^ nb j g.2) := by
      have := tn_prodE (E := Dir d) (p := pPhi d) H.hh' H.hℓ' (Comp j g.2) (KchkC j C V K)
        (fun Y => β * (2 * A⁻¹) ^ nb j Y) (fun _ _ => by positivity) (fun Y hY => (hB Y hY).1)
      rwa [prod_mul_distrib, prod_const, hw] at this
    have hJ : tNorm (Dir d) (pPhi d) h' ℓ' (Jprod j K g.1 : Alg2 d L N) ≤
        ENNReal.ofReal (κ ^ g.1.card) := by
      have := tn_prodE (E := Dir d) (p := pPhi d) H.hh' H.hℓ' g.1
        (fun p => thetaE (Jb j K p.1 p.2)) (fun _ => κ) (fun _ _ => hκ0)
        (fun p hp => H.thetaJ_le_kappa (hg1 p hp) p.2)
      rwa [prod_const] at this
    refine (tn_mulE H.hh' H.hℓ' (by positivity) hK1 hJ).trans (ENNReal.ofReal_le_ofReal ?_)
    have hk1 : 1 ≤ g.1.card := card_pos.2 (nonempty_iff_ne_empty.2 h1)
    obtain ⟨k, hk⟩ : ∃ k, g.1.card = k + 1 := ⟨g.1.card - 1, by omega⟩
    rw [hk, show k + 1 + (Comp j g.2).card - 1 = (Comp j g.2).card + k by omega, h4]
    have hkk : κ ^ k ≤ β ^ k := pow_le_pow_left₀ hκ0 hκβ k
    have h2 : (2 * A⁻¹) ^ nb j g.2 ≤ 2 ^ nb j g.2 * (2 * A⁻¹) ^ nb j g.2 :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    calc β ^ (Comp j g.2).card * (2 * A⁻¹) ^ nb j g.2 * κ ^ (k + 1)
        = κ * (β ^ (Comp j g.2).card * κ ^ k) * (2 * A⁻¹) ^ nb j g.2 := by ring
      _ ≤ κ * (β ^ (Comp j g.2).card * β ^ k) * (2 ^ nb j g.2 * (2 * A⁻¹) ^ nb j g.2) := by
        gcongr
      _ = κ * β ^ ((Comp j g.2).card + k) * (2 ^ nb j g.2 * (2 * A⁻¹) ^ nb j g.2) := by ring

/-- The integrand of `𝓡^3`. -/
theorem R3_integrand_le {Y : Finset (Lam d L N)} (hY : IsConn j Y) :
    tNorm (Dir d) (pPhi d) h' ℓ' ((Kchk j C V K Y - thetaE (K Y) - dIPow j C V K Y +
      ∑ b ∈ blocks j Y, thetaE (Jb j K b Y) : EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
      ENNReal.ofReal (κ₀ * δ₁ * (4 * A⁻¹) ^ nb j Y) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hδ := H.hδ₁
  rw [Kchk, comp_of_isConn hY, prod_singleton]
  refine (H.KchkC_bounds hY).2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  norm_num

end KHyp

end

end Step

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- The hypotheses for the bounds on `𝓡^1, 𝓡^2, 𝓡^3` at a fixed `U`. -/
structure RHyp (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    (U : Finset (Lam d L N)) (h ℓ h' ℓ' A κ₀ δ₁ cJ a η P : ℝ) (M : ℕ) : Prop
    extends KHyp j C V K h ℓ h' ℓ' A κ₀ δ₁ cJ where
  hE : ∀ F : Alg2 d L N, tNorm (Dir d) (pPhi d) h' ℓ' (EC C F) ≤ tNorm (Dir d) (pPhi d) h' ℓ' F
  hU : IsPolymer (j + 1) U
  ha : 0 ≤ a
  ha1 : a ≤ 1 / 40
  hu : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
    ‖(uVnext j C V K).1 * (blockSet (L := L) (N := N) j b).card‖ ≤ a
  hV : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, tNorm (Dir d) (pPhi d) h' ℓ'
    ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤ ENNReal.ofReal (2 * a)
  hpref : Real.exp (4 * a * nb j U) ≤ 2 ^ nb (j + 1) U
  hcount : (Gset j U).card ≤ M ^ nb (j + 1) U
  hη : 0 ≤ η
  hgeom : ∀ g ∈ Gset j U, (1 + 2 * η) * (nb (j + 1) U : ℝ) ≤
    nb j g.2 + (1 + 2 * η) * 2 ^ d * ((Comp j g.2).card + g.1.card)
  hP : P = 2 * M
  hM : 1 ≤ M
  hAP : 4 * P ≤ A ^ (2 * η / (1 + 2 * η))

namespace RHyp

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {V : Vcoup} {K : Act d L N}
  {U : Finset (Lam d L N)} {h ℓ h' ℓ' A κ₀ δ₁ cJ a η P : ℝ} {M : ℕ}
  (R : RHyp j C V K U h ℓ h' ℓ' A κ₀ δ₁ cJ a η P M)
include R

theorem hP1 : 1 ≤ P := by
  rw [R.hP]; have : (1 : ℝ) ≤ M := by exact_mod_cast R.hM
  linarith

theorem pref (W : Finset (Lam d L N)) :
    tNorm (Dir d) (pPhi d) h' ℓ' ((Complex.exp ((uVnext j C V K).1 * U.card) •
      InextPow j C V K (U \ W) : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 ^ nb (j + 1) U) :=
  (pref_le R.hh' R.hℓ' R.ha (IsPolymer.of_succ R.hU) W
    (fun b hb => R.hu b (mem_blockIdx_of_mem_blocks hb))
    (fun b hb => R.hV b (mem_blockIdx_of_mem_blocks hb))).trans
    (ENNReal.ofReal_le_ofReal R.hpref)

theorem term_le (W : Finset (Lam d L N)) (F : EvR (Lam d L N ⊕ Lam d L N)) {r : ℝ}
    (hr : 0 ≤ r) (hF : tNorm (Dir d) (pPhi d) h' ℓ' (F : Alg2 d L N) ≤ ENNReal.ofReal r) :
    tNorm (Dir d) (pPhi d) h' ℓ' (((Complex.exp ((uVnext j C V K).1 * U.card) •
      InextPow j C V K (U \ W)) * ECE C F : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (2 ^ nb (j + 1) U * r) :=
  tn_mulE R.hh' R.hℓ' (by positivity) (R.pref W) (by rw [coe_ECE]; exact (R.hE _).trans hF)

theorem R2_le (hDβ : (A * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * κ₀ + δ₁) ≤ 1) :
    ENNReal.ofReal (A ^ nb (j + 1) U) *
      tNorm (Dir d) (pPhi d) h' ℓ' (R2 j C V K U : Alg d L N) ≤
      ENNReal.ofReal (((A * P) ^ 2 ^ d) ^ 2 *
        ((1 + 2 ^ d * cJ) * κ₀ * ((1 + 2 ^ d * cJ) * κ₀ + δ₁))) := by
  classical
  have hA0 : 0 < A := by linarith [R.hA]
  have hP1 := R.hP1
  have hκ := R.hκ₀
  have hc := R.hcJ
  have hδ := R.hδ₁
  set x := nb (j + 1) U
  set κ := (1 + 2 ^ d * cJ) * κ₀ with hκdef
  set β := (1 + 2 ^ d * cJ) * κ₀ + δ₁ with hβdef
  have hκ0 : 0 ≤ κ := by positivity
  have hβ0 : 0 ≤ β := by positivity
  set S := (Gset j U).filter (fun g => 2 ≤ g.1.card + (Comp j g.2).card)
  have e : R2 j C V K U = ∑ g ∈ S, (Complex.exp ((uVnext j C V K).1 * U.card) •
      InextPow j C V K (U \ (g.2 ∪ Xcal g.1))) *
        ECE C ((Kchk j C V K g.2 - if g.1 = ∅ then dIPow j C V K g.2 else 0) * Jprod j K g.1) := by
    rw [R2, smul_sum]; exact sum_congr rfl fun g _ => (smul_mul_assoc _ _ _).symm
  rw [e]
  refine wsum_bound S _ (M ^ x) ((card_filter_le _ _).trans R.hcount) (by positivity)
    fun g hg => ?_
  obtain ⟨hgG, hm⟩ := mem_filter.1 hg
  obtain ⟨f1, -, -, f4⟩ := Gset_facts hgG
  have hI := R.toKHyp.R2_integrand_le f1 (fun p hp => (mem_pairsU.1 (f4 p hp).1).1) hm
  have hT := R.term_le (g.2 ∪ Xcal g.1) _ (by positivity) hI
  refine (mul_le_mul_left' hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set m := g.1.card + (Comp j g.2).card
  set t := nb j g.2
  have hgeo := geom_real (d := d) (x := x) (t := t) (m := m) R.hA hP1 R.hη
    (by
      rw [show ((m : ℕ) : ℝ) = ((Comp j g.2).card : ℝ) + g.1.card by push_cast [m]; ring]
      exact R.hgeom g hgG) R.hAP
  have hpm := pow_m_real (D := (A * P) ^ 2 ^ d) (κ := κ) (β := β) (m := m) (by positivity)
    hκ0 hβ0 hDβ hm
  have hkb : 0 ≤ κ * β ^ (m - 1) := by positivity
  calc ((M ^ x : ℕ) : ℝ) * A ^ x * (2 ^ x * (κ * β ^ (m - 1) * (4 * A⁻¹) ^ t))
      = (A ^ x * P ^ x * (4 * A⁻¹) ^ t) * (κ * β ^ (m - 1)) := by
        rw [R.hP, mul_pow]; push_cast; ring
    _ ≤ (A * P) ^ (2 ^ d * m) * (κ * β ^ (m - 1)) := by gcongr
    _ = ((A * P) ^ 2 ^ d) ^ m * (κ * β ^ (m - 1)) := by rw [pow_mul]
    _ ≤ _ := hpm

theorem R3_le :
    ENNReal.ofReal (A ^ nb (j + 1) U) *
      tNorm (Dir d) (pPhi d) h' ℓ' (R3 j C V K U : Alg d L N) ≤
      ENNReal.ofReal ((A * P) ^ 2 ^ d * (κ₀ * δ₁)) := by
  classical
  have hA0 : 0 < A := by linarith [R.hA]
  have hP1 := R.hP1
  have hκ := R.hκ₀
  have hδ := R.hδ₁
  set x := nb (j + 1) U
  set S := (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2)
  have e : R3 j C V K U = ∑ g ∈ S, (Complex.exp ((uVnext j C V K).1 * U.card) •
      InextPow j C V K (U \ g.2)) *
        ECE C (Kchk j C V K g.2 - thetaE (K g.2) - dIPow j C V K g.2 +
          ∑ b ∈ blocks j g.2, thetaE (Jb j K b g.2)) := by
    rw [R3, smul_sum]; exact sum_congr rfl fun g _ => (smul_mul_assoc _ _ _).symm
  rw [e]
  refine wsum_bound S _ (M ^ x) ((card_filter_le _ _).trans R.hcount) (by positivity)
    fun g hg => ?_
  obtain ⟨hgG, h1, hc⟩ := mem_filter.1 hg
  have hI := R.toKHyp.R3_integrand_le (C := C) (V := V) hc
  have hT := R.term_le g.2 _ (by positivity) hI
  refine (mul_le_mul_left' hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := nb j g.2
  have hgeo := geom_real (d := d) (x := x) (t := t) (m := 1) R.hA hP1 R.hη
    (by
      have := R.hgeom g hgG
      rw [comp_of_isConn hc, card_singleton, h1, card_empty] at this
      push_cast at this ⊢; linarith) R.hAP
  calc ((M ^ x : ℕ) : ℝ) * A ^ x * (2 ^ x * (κ₀ * δ₁ * (4 * A⁻¹) ^ t))
      = (A ^ x * P ^ x * (4 * A⁻¹) ^ t) * (κ₀ * δ₁) := by
        rw [R.hP, mul_pow]; push_cast; ring
    _ ≤ (A * P) ^ (2 ^ d * 1) * (κ₀ * δ₁) := by gcongr
    _ = _ := by rw [mul_one]

theorem R1_le :
    ENNReal.ofReal (A ^ nb (j + 1) U) *
      tNorm (Dir d) (pPhi d) h' ℓ' (R1 j C V K U : Alg d L N) ≤
      ENNReal.ofReal ((A * P) ^ 2 ^ d * (2 ^ d * (10 * a) * 2 ^ 2 ^ d) *
        (cJ * κ₀ * A⁻¹ ^ 2 ^ d)) := by
  classical
  have hA0 : 0 < A := by linarith [R.hA]
  have hP1 := R.hP1
  have hκ := R.hκ₀
  have hc := R.hcJ
  have ha := R.ha
  have hρ := R.hρ0
  set x := nb (j + 1) U
  rw [R1_eq C V K R.hU]
  refine wsum_bound _ _ (M ^ x) ((card_filter_le _ _).trans R.hcount) (by positivity)
    fun g hg => ?_
  obtain ⟨hgG, h1, h2⟩ := mem_filter.1 hg
  obtain ⟨p, hp⟩ := card_eq_one.1 h1
  obtain ⟨-, -, -, f4⟩ := Gset_facts hgG
  obtain ⟨hb, hs, -⟩ := mem_pairsU.1 (f4 p (by rw [hp]; exact mem_singleton_self p)).1
  have hX : Xcal g.1 = p.2 := by rw [hp, Xcal, singleton_biUnion]
  have hJ : tNorm (Dir d) (pPhi d) h' ℓ' ((ECE C (Jprod j K g.1) : EvR (Lam d L N)) :
      Alg d L N) ≤ ENNReal.ofReal (cJ * κ₀ * A⁻¹ ^ 2 ^ d) := by
    rw [coe_ECE, hp, Jprod, prod_singleton, coe_thetaE]
    exact (R.hE _).trans (R.hJ p.1 hb p.2)
  have hO := one_sub_InextPow_le (C := C) (V := V) (K := K) R.hh' R.hℓ' ha
    (R.ha1.trans (by norm_num)) (Xcal g.1)
    (fun b hb => R.hu b (mem_blockIdx_of_mem_blocks hb))
    (fun b hb => R.hV b (mem_blockIdx_of_mem_blocks hb))
  have hT := tn_mulE R.hh' R.hℓ' (by positivity) (R.pref (Xcal g.1))
    (tn_mulE R.hh' R.hℓ' (by positivity) hO hJ)
  refine (mul_le_mul_left' hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx : x ≤ 2 ^ d := by
    have := R.hgeom g hgG
    rw [h2, nb_empty', comp_empty, card_empty, h1] at this
    have hη := R.hη
    have : (x : ℝ) ≤ 2 ^ d := by
      push_cast at this
      nlinarith
    exact_mod_cast this
  have hnX : nb j (Xcal g.1) ≤ 2 ^ d := by rw [hX]; exact hs.2.2
  have hAP1 : 1 ≤ A * P := one_le_mul_of_one_le_of_one_le R.hA hP1
  have e1 : ((M ^ x : ℕ) : ℝ) * A ^ x * 2 ^ x = (A * P) ^ x := by
    rw [R.hP, mul_pow, mul_pow]; push_cast; ring
  have e2 : (A * P) ^ x ≤ (A * P) ^ 2 ^ d := pow_le_pow_right₀ hAP1 hx
  have e3 : (nb j (Xcal g.1) : ℝ) * (10 * a) * (1 + 10 * a) ^ (nb j (Xcal g.1) - 1) ≤
      2 ^ d * (10 * a) * 2 ^ 2 ^ d := by
    have hn : (nb j (Xcal g.1) : ℝ) ≤ 2 ^ d := by exact_mod_cast hnX
    have h10 : 1 + 10 * a ≤ 2 := by linarith [R.ha1]
    have : (1 + 10 * a) ^ (nb j (Xcal g.1) - 1) ≤ 2 ^ 2 ^ d :=
      (pow_le_pow_left₀ (by positivity) h10 _).trans
        (pow_le_pow_right₀ (by norm_num) (by omega))
    gcongr
  calc ((M ^ x : ℕ) : ℝ) * A ^ x * (2 ^ x * ((nb j (Xcal g.1) : ℝ) * (10 * a) *
        (1 + 10 * a) ^ (nb j (Xcal g.1) - 1) * (cJ * κ₀ * A⁻¹ ^ 2 ^ d)))
      = (((M ^ x : ℕ) : ℝ) * A ^ x * 2 ^ x) * ((nb j (Xcal g.1) : ℝ) * (10 * a) *
        (1 + 10 * a) ^ (nb j (Xcal g.1) - 1)) * (cJ * κ₀ * A⁻¹ ^ 2 ^ d) := by ring
    _ ≤ (A * P) ^ 2 ^ d * (2 ^ d * (10 * a) * 2 ^ 2 ^ d) * (cJ * κ₀ * A⁻¹ ^ 2 ^ d) := by
        rw [e1]; gcongr

end RHyp

end

end Step
