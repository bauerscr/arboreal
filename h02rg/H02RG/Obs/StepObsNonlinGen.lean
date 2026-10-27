import Obs.GenericDecomp
import Step.EstNonlin

/-!
# The non-linear part over a general normed algebra (Section `sec:K-nonlinear`, generic)

The proofs of Lemmas `lem:NonlinearCheckK` and `lem:Ri-bd` (`Step.EstNonlinAux`) only use:
* the product property and the triangle inequality of the norms on `R` and `R2`;
* the contraction `‖𝔼 F‖ ≤ ‖F‖`;
* the bounds `‖θ K(W)‖ ≤ κ₀ A^{-|𝓑(W)|}`, `‖δI(B)‖ ≤ δ₁ A⁻¹`, `‖θ J(B, X)‖ ≤ c_J κ₀ A^{-2^d}`,
  `‖e^{u(B)}‖ ≤ e^a`, `‖e^{-(u+V)(B)} - 1‖ ≤ 10 a`;
* `J(B, X) = 0` unless `X` is small, and `∑_X J(B, X) = 0` (`e:J-zero`);
* the combinatorics of `𝒢(U)` (`Gset`, `comb2`, `card_Gset_le`), which is that of `Step`.

This file proves them for the generic map of `Obs.GenericDefs` over a *submultiplicative
norm* (`SNorm`), so that they apply to the algebra with observables (`Obs.StepObsNonlin`).
The final bound is `RHypG.R_le` (the three terms of `Step.final_real`).
-/

namespace Obs.Gen

noncomputable section

open Finset Grassmann Loc FRD Step

/-- A submultiplicative seminorm with values in `ℝ≥0∞`. -/
structure SNorm (R : Type*) [Ring R] where
  /-- The norm. -/
  nrm : R → ENNReal
  zero : nrm 0 = 0
  add : ∀ x y, nrm (x + y) ≤ nrm x + nrm y
  neg : ∀ x, nrm (-x) = nrm x
  mul : ∀ x y, nrm (x * y) ≤ nrm x * nrm y
  one : nrm 1 ≤ 1

namespace SNorm

variable {R : Type*} [CommRing R] (n : SNorm R)

theorem sub_le (x y : R) : n.nrm (x - y) ≤ n.nrm x + n.nrm y := by
  rw [sub_eq_add_neg]; exact (n.add _ _).trans (by rw [n.neg])

theorem sum_le {ι : Type*} (s : Finset ι) (f : ι → R) :
    n.nrm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, n.nrm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [n.zero]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (n.add _ _).trans (add_le_add le_rfl ih)

theorem prod_le {ι : Type*} (s : Finset ι) (f : ι → R) :
    n.nrm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, n.nrm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using n.one
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (n.mul _ _).trans (mul_le_mul_right ih _)

theorem mulR {x y : R} {s t : ℝ} (hs : 0 ≤ s) (hx : n.nrm x ≤ ENNReal.ofReal s)
    (hy : n.nrm y ≤ ENNReal.ofReal t) : n.nrm (x * y) ≤ ENNReal.ofReal (s * t) :=
  (n.mul x y).trans (by rw [ENNReal.ofReal_mul hs]; exact mul_le_mul' hx hy)

theorem prodR {ι : Type*} (s : Finset ι) (F : ι → R) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hF : ∀ i ∈ s, n.nrm (F i) ≤ ENNReal.ofReal (r i)) :
    n.nrm (∏ i ∈ s, F i) ≤ ENNReal.ofReal (∏ i ∈ s, r i) :=
  (n.prod_le s F).trans (by rw [ENNReal.ofReal_prod_of_nonneg hr]; exact prod_le_prod' hF)

theorem sumR {ι : Type*} (s : Finset ι) (F : ι → R) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hF : ∀ i ∈ s, n.nrm (F i) ≤ ENNReal.ofReal (r i)) :
    n.nrm (∑ i ∈ s, F i) ≤ ENNReal.ofReal (∑ i ∈ s, r i) :=
  (n.sum_le s F).trans (by rw [ENNReal.ofReal_sum_of_nonneg hr]; exact sum_le_sum hF)

theorem sum_constR {ι : Type*} (s : Finset ι) (F : ι → R) {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ i ∈ s, n.nrm (F i) ≤ ENNReal.ofReal r) :
    n.nrm (∑ i ∈ s, F i) ≤ ENNReal.ofReal (s.card * r) := by
  have := n.sumR s F (fun _ => r) (fun _ _ => hr) hF
  rwa [sum_const, nsmul_eq_mul] at this

theorem addR {x y : R} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hx : n.nrm x ≤ ENNReal.ofReal s)
    (hy : n.nrm y ≤ ENNReal.ofReal t) : n.nrm (x + y) ≤ ENNReal.ofReal (s + t) :=
  (n.add x y).trans (by rw [ENNReal.ofReal_add hs ht]; exact add_le_add hx hy)

theorem subR {x y : R} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hx : n.nrm x ≤ ENNReal.ofReal s)
    (hy : n.nrm y ≤ ENNReal.ofReal t) : n.nrm (x - y) ≤ ENNReal.ofReal (s + t) :=
  (n.sub_le x y).trans (by rw [ENNReal.ofReal_add hs ht]; exact add_le_add hx hy)

theorem oneR : n.nrm 1 ≤ ENNReal.ofReal 1 := by rw [ENNReal.ofReal_one]; exact n.one

/-- `‖x y - 1‖ ≤ s + t + s t` if `‖x - 1‖ ≤ s`, `‖y - 1‖ ≤ t`. -/
theorem mul_sub_one_le {x y : R} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hx : n.nrm (x - 1) ≤ ENNReal.ofReal s) (hy : n.nrm (y - 1) ≤ ENNReal.ofReal t) :
    n.nrm (x * y - 1) ≤ ENNReal.ofReal (s + t + s * t) := by
  have e : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  rw [e]
  exact n.addR (by positivity) (by positivity) (n.addR hs ht hx hy) (n.mulR hs hx hy)

/-- Telescoping: `‖∏ (a + c) - ∏ a‖ ≤ |s| κ β^{|s|-1} ∏ w`. -/
theorem prod_sub_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a c : ι → R) (w : ι → ℝ)
    {β κ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hκ : 0 ≤ κ) (hκβ : κ ≤ β)
    (ha : ∀ i ∈ s, n.nrm (a i) ≤ ENNReal.ofReal (β * w i))
    (hac : ∀ i ∈ s, n.nrm (a i + c i) ≤ ENNReal.ofReal (β * w i))
    (hc : ∀ i ∈ s, n.nrm (c i) ≤ ENNReal.ofReal (κ * w i)) :
    n.nrm (∏ i ∈ s, (a i + c i) - ∏ i ∈ s, a i) ≤
      ENNReal.ofReal (s.card * κ * β ^ (s.card - 1) * ∏ i ∈ s, w i) := by
  have hβ : 0 ≤ β := hκ.trans hκβ
  induction s using Finset.induction_on with
  | empty => simp [n.zero]
  | insert i s hi ih =>
    have hw' : ∀ j ∈ s, 0 ≤ w j := fun j hj => hw j (mem_insert_of_mem hj)
    have ih' := ih hw' (fun j hj => ha j (mem_insert_of_mem hj))
      (fun j hj => hac j (mem_insert_of_mem hj)) (fun j hj => hc j (mem_insert_of_mem hj))
    have hQ : n.nrm (∏ j ∈ s, a j) ≤ ENNReal.ofReal (β ^ s.card * ∏ j ∈ s, w j) := by
      have := n.prodR s a (fun j => β * w j) (fun j hj => mul_nonneg hβ (hw' j hj))
        (fun j hj => ha j (mem_insert_of_mem hj))
      rwa [prod_mul_distrib, prod_const] at this
    have e : (∏ j ∈ insert i s, (a j + c j) - ∏ j ∈ insert i s, a j) =
        (a i + c i) * (∏ j ∈ s, (a j + c j) - ∏ j ∈ s, a j) + c i * ∏ j ∈ s, a j := by
      rw [prod_insert hi, prod_insert hi]; ring
    have hwi := hw i (mem_insert_self i s)
    have hPw : 0 ≤ ∏ j ∈ s, w j := prod_nonneg hw'
    rw [e]
    refine (n.addR (by positivity) (by positivity)
      (n.mulR (by positivity) (hac i (mem_insert_self i s)) ih')
      (n.mulR (by positivity) (hc i (mem_insert_self i s)) hQ)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [card_insert_of_notMem hi, prod_insert hi, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0]; push_cast; ring
    · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]; push_cast; ring

/-- Weighted sum bound: if `M ≥ |S|` and `M w ‖F_g‖ ≤ Q` for all `g`, then `w ‖∑ F_g‖ ≤ Q`. -/
theorem wsum_bound {ι : Type*} (S : Finset ι) (F : ι → R) (M : ℕ) (hS : S.card ≤ M)
    {w Q : ℝ} (hF : ∀ g ∈ S, ENNReal.ofReal (M * w) * n.nrm (F g) ≤ ENNReal.ofReal Q) :
    ENNReal.ofReal w * n.nrm (∑ g ∈ S, F g) ≤ ENNReal.ofReal Q := by
  refine (mul_le_mul_right (n.sum_le _ _) _).trans ?_
  rw [mul_sum]
  refine sum_le_of_card_mul S _ _ M hS fun g hg => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact hF g hg

end SNorm

variable {d L N : ℕ} [NeZero L]

variable {R R2 : Type*} [CommRing R] [CommRing R2] [Algebra ℂ R] [Algebra ℂ R2]

/-! ### Structural identities -/

section Struct

variable (Al : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R)

theorem dIPowG_eq_prod_comp {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) :
    dIPowG Al j F Z = ∏ Y ∈ Comp j Z, dIPowG Al j F Y :=
  eq_prod_comp_of_mul _ (bpow_empty _)
    (fun _ _ hA hB h => bpow_union _ hA hB (disjoint_of_not_touch h)) hZ

theorem KtilG_split {Y : Finset (Lam d L N)} (hY : IsPolymer j Y) :
    KtilG Al j F Y = dIPowG Al j F Y +
      ∑ W ∈ (Pj j Y).erase Y, Al.θ (KextG j F.K (Y \ W)) * dIPowG Al j F W := by
  have hYm : Y ∈ Pj j Y := mem_Pj.2 ⟨subset_rfl, hY⟩
  rw [KtilG, ← add_sum_erase _ _ hYm, sdiff_self, bot_eq_empty, KextG_empty, map_one, one_mul]

theorem sum_erase_splitG {Y : Finset (Lam d L N)} (hY : IsConn j Y) :
    ∑ W ∈ (Pj j Y).erase Y, Al.θ (KextG j F.K (Y \ W)) * dIPowG Al j F W =
      Al.θ (F.K Y) + ∑ W ∈ ((Pj j Y).erase Y).erase ∅,
        Al.θ (KextG j F.K (Y \ W)) * dIPowG Al j F W := by
  have hne : (∅ : Finset (Lam d L N)) ≠ Y := fun h => not_isConn_empty (h ▸ hY)
  have hm : (∅ : Finset (Lam d L N)) ∈ (Pj j Y).erase Y :=
    mem_erase.2 ⟨hne, mem_Pj.2 ⟨empty_subset _, isPolymer_empty j⟩⟩
  rw [← add_sum_erase _ _ hm, sdiff_empty, dIPowG_empty, mul_one, KextG, comp_of_isConn hY,
    prod_singleton]

theorem JprodG_sum_R1 (hJ0 : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X), F.J b X = 0)
    (U : Finset (Lam d L N)) :
    ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅), JprodG Al F g.1 = 0 := by
  classical
  set P1 := (pairsU (L := L) (N := N) j).filter
    (fun p => clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U)
  have hbij : ∑ p ∈ P1, Al.θ (F.J p.1 p.2) =
      ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅), JprodG Al F g.1 := by
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
      rw [JprodG, prod_singleton]
  rw [← hbij, ← map_sum]
  have h0 : ∑ p ∈ P1, F.J p.1 p.2 = 0 := by
    have eP : P1 = (blockIdx (L := L) (N := N) j ×ˢ smallSets (L := L) (N := N) j).filter
        (fun p => blockSet j p.1 ⊆ p.2 ∧
          clo j (nbhd j (blockSet (L := L) (N := N) j p.1)) = U) := by
      ext p; simp [P1, pairsU, and_assoc]
    rw [eP, sum_filter, sum_product]
    refine sum_eq_zero fun b hb => ?_
    by_cases hc : clo j (nbhd j (blockSet (L := L) (N := N) j b)) = U
    · simp only [hc, and_true]
      rw [← sum_filter]
      exact hJ0 b hb
    · simp [hc]
  rw [h0, map_zero]

theorem R1G_eq (hJ0 : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X), F.J b X = 0)
    {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    R1G Al j F U = ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      (PrefG j F U * ItPow j F (U \ Xcal g.1)) *
        ((1 - ItPow j F (Xcal g.1)) * Al.E (JprodG Al F g.1)) := by
  classical
  set S := (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅)
  have h0 : ∑ g ∈ S, ItPow j F U * Al.E (JprodG Al F g.1) = 0 := by
    rw [← mul_sum, ← map_sum, JprodG_sum_R1 Al j F hJ0, map_zero, mul_zero]
  rw [R1G, ← sub_zero (∑ g ∈ S, ItPow j F (U \ Xcal g.1) * Al.E (JprodG Al F g.1)), ← h0,
    ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨-, -, hX, f4⟩ := Gset_facts (mem_filter.1 hg).1
  have hXp : IsPolymer j (Xcal g.1) := isPolymer_Xcal fun p hp => (f4 p hp).1
  have hUj : IsPolymer j U := IsPolymer.of_succ hU
  have eI : ItPow j F U = ItPow j F (U \ Xcal g.1) * ItPow j F (Xcal g.1) := by
    conv_lhs => rw [← sdiff_union_of_subset hX]
    exact ItPow_union j F (IsPolymer.sdiff hUj hXp) hXp sdiff_disjoint
  rw [eI]
  ring

end Struct

/-! ### Lemma `lem:NonlinearCheckK` -/

/-- The hypotheses for Lemma `lem:NonlinearCheckK`: `ρ = A⁻¹`, `‖θ K(W)‖ ≤ κ₀ ρ^{|𝓑(W)|}`,
`‖δI(B)‖ ≤ δ₁ ρ`, `‖θ J(B, X)‖ ≤ c_J κ₀ ρ^{2^d}`. -/
structure KHypG (Al : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R) (n2 : SNorm R2)
    (A κ₀ δ₁ cJ : ℝ) : Prop where
  hA : 1 ≤ A
  hκ₀ : 0 ≤ κ₀
  hκ₀1 : κ₀ ≤ 1
  hδ₁ : 0 ≤ δ₁
  hδ₁1 : δ₁ ≤ 1
  hcJ : 0 ≤ cJ
  hK : ∀ W : Finset (Lam d L N), IsConn j W →
    n2.nrm (Al.θ (F.K W)) ≤ ENNReal.ofReal (κ₀ * A⁻¹ ^ nb j W)
  hdI : ∀ b ∈ blockIdx (L := L) (N := N) j, n2.nrm (dIG Al F b) ≤ ENNReal.ofReal (δ₁ * A⁻¹)
  hJ : ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
    n2.nrm (Al.θ (F.J b X)) ≤ ENNReal.ofReal (cJ * κ₀ * A⁻¹ ^ 2 ^ d)
  hJs : ∀ b X, ¬ IsSmall j X → F.J b X = 0

namespace KHypG

variable {Al : RGAlg R R2} {j : ℕ} {F : RGIngr d L N R} {n2 : SNorm R2}
  {A κ₀ δ₁ cJ : ℝ} (H : KHypG Al j F n2 A κ₀ δ₁ cJ)
include H

theorem hρ0 : 0 < A⁻¹ := inv_pos.2 (by linarith [H.hA])

theorem hρ1 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ H.hA

theorem Kext_le {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) :
    n2.nrm (Al.θ (KextG j F.K Z)) ≤ ENNReal.ofReal (κ₀ ^ (Comp j Z).card * A⁻¹ ^ nb j Z) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  rw [KextG, map_prod]
  have := n2.prodR (Comp j Z) (fun W => Al.θ (F.K W))
    (fun W => κ₀ * A⁻¹ ^ nb j W) (fun W _ => by positivity)
    (fun W hW => H.hK W (isConn_of_mem_comp hZ hW))
  rwa [prod_mul_distrib, prod_const, prod_comp_pow hZ] at this

theorem dIPow_le (W : Finset (Lam d L N)) :
    n2.nrm (dIPowG Al j F W) ≤ ENNReal.ofReal ((δ₁ * A⁻¹) ^ nb j W) := by
  have hρ := H.hρ0
  have hδ := H.hδ₁
  have := n2.prodR (blocks j W) (dIG Al F)
    (fun _ => δ₁ * A⁻¹) (fun _ _ => by positivity)
    (fun b hb => H.hdI b (mem_blockIdx_of_mem_blocks hb))
  rwa [prod_const] at this

theorem tterm_le {Y W : Finset (Lam d L N)} (hY : IsPolymer j Y) (hW : W ∈ Pj j Y)
    (hWY : W ≠ Y) :
    n2.nrm (Al.θ (KextG j F.K (Y \ W)) * dIPowG Al j F W) ≤
      ENNReal.ofReal (κ₀ * δ₁ ^ nb j W * A⁻¹ ^ nb j Y) := by
  have hρ := H.hρ0
  have hδ := H.hδ₁
  have hκ := H.hκ₀
  obtain ⟨hWs, hWp⟩ := mem_Pj.1 hW
  have hYW : IsPolymer j (Y \ W) := IsPolymer.sdiff hY hWp
  refine (n2.mulR (by positivity) (H.Kext_le hYW) (H.dIPow_le W)).trans
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

theorem Jsum_le {Y : Finset (Lam d L N)} :
    n2.nrm (∑ b ∈ blocks j Y, Al.θ (F.J b Y)) ≤
      ENNReal.ofReal (2 ^ d * cJ * κ₀ * A⁻¹ ^ nb j Y) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  classical
  by_cases hs : IsSmall j Y
  · have := n2.sum_constR (blocks j Y) (fun b => Al.θ (F.J b Y))
      (r := cJ * κ₀ * A⁻¹ ^ 2 ^ d) (by positivity)
      (fun b hb => H.hJ b (mem_blockIdx_of_mem_blocks hb) Y)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have hn : ((blocks j Y).card : ℝ) ≤ 2 ^ d := by exact_mod_cast hs.2.2
    have hp : A⁻¹ ^ 2 ^ d ≤ A⁻¹ ^ nb j Y := pow_le_pow_of_le_one hρ.le H.hρ1 hs.2.2
    calc ((blocks j Y).card : ℝ) * (cJ * κ₀ * A⁻¹ ^ 2 ^ d)
        ≤ 2 ^ d * (cJ * κ₀ * A⁻¹ ^ nb j Y) := by gcongr
      _ = 2 ^ d * cJ * κ₀ * A⁻¹ ^ nb j Y := by ring
  · have h0 : (∑ b ∈ blocks j Y, Al.θ (F.J b Y)) = 0 := by
      refine sum_eq_zero fun b _ => ?_
      rw [H.hJs b Y hs, map_zero]
    rw [h0, n2.zero]
    exact zero_le

theorem card_erase_Pj_le {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (s : Finset (Finset (Lam d L N))) (hs : s ⊆ Pj j Y) : (s.card : ℝ) ≤ 2 ^ nb j Y := by
  have := (card_le_card hs).trans (card_Pj hY).le
  exact_mod_cast this

/-- **Lemma `lem:NonlinearCheckK`** for a connected `Y`, with `β = (1 + 2^d c_J) κ₀ + δ₁` and
`κ = (1 + 2^d c_J) κ₀`. -/
theorem KchkC_bounds {Y : Finset (Lam d L N)} (hY : IsConn j Y) :
    n2.nrm (KchkCG Al j F Y) ≤
        ENNReal.ofReal (((1 + 2 ^ d * cJ) * κ₀ + δ₁) * (2 * A⁻¹) ^ nb j Y) ∧
      n2.nrm (KchkCG Al j F Y - dIPowG Al j F Y) ≤
        ENNReal.ofReal ((1 + 2 ^ d * cJ) * κ₀ * (2 * A⁻¹) ^ nb j Y) ∧
      n2.nrm (dIPowG Al j F Y) ≤
        ENNReal.ofReal (((1 + 2 ^ d * cJ) * κ₀ + δ₁) * (2 * A⁻¹) ^ nb j Y) ∧
      n2.nrm (KchkCG Al j F Y - Al.θ (F.K Y) - dIPowG Al j F Y +
        ∑ b ∈ blocks j Y, Al.θ (F.J b Y)) ≤
        ENNReal.ofReal (κ₀ * δ₁ * (2 * A⁻¹) ^ nb j Y) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  have hYp := hY.1
  have hnb : nb j Y ≠ 0 := fun h0 => (nonempty_iff_ne_empty.1 hY.2.1) (nb_eq_zero_iff.1 h0)
  have h2p : (2 * A⁻¹) ^ nb j Y = 2 ^ nb j Y * A⁻¹ ^ nb j Y := mul_pow _ _ _
  set S1 := ∑ W ∈ (Pj j Y).erase Y, Al.θ (KextG j F.K (Y \ W)) * dIPowG Al j F W
  set S2 := ∑ W ∈ ((Pj j Y).erase Y).erase ∅, Al.θ (KextG j F.K (Y \ W)) * dIPowG Al j F W
  set SJ := ∑ b ∈ blocks j Y, Al.θ (F.J b Y)
  have hsp := KtilG_split Al j F hYp
  have hsp2 := sum_erase_splitG Al j F hY
  have hS1 : n2.nrm S1 ≤ ENNReal.ofReal (κ₀ * (2 * A⁻¹) ^ nb j Y) := by
    refine (n2.sum_constR _ _ (r := κ₀ * A⁻¹ ^ nb j Y) (by positivity)
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
  have hS2 : n2.nrm S2 ≤ ENNReal.ofReal (κ₀ * δ₁ * (2 * A⁻¹) ^ nb j Y) := by
    refine (n2.sum_constR _ _ (r := κ₀ * δ₁ * A⁻¹ ^ nb j Y)
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
  have hSJ : n2.nrm SJ ≤ ENNReal.ofReal (2 ^ d * cJ * κ₀ * (2 * A⁻¹) ^ nb j Y) := by
    refine H.Jsum_le.trans (ENNReal.ofReal_le_ofReal ?_)
    have : A⁻¹ ^ nb j Y ≤ (2 * A⁻¹) ^ nb j Y := by
      rw [h2p]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    gcongr
  have hdIY : n2.nrm (dIPowG Al j F Y) ≤ ENNReal.ofReal (δ₁ * (2 * A⁻¹) ^ nb j Y) := by
    refine (H.dIPow_le Y).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_pow]
    have : δ₁ ^ nb j Y ≤ δ₁ := pow_le_of_le_one hδ H.hδ₁1 hnb
    have h2 : A⁻¹ ^ nb j Y ≤ (2 * A⁻¹) ^ nb j Y := by
      rw [h2p]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    gcongr
  have e2 : KchkCG Al j F Y - dIPowG Al j F Y = S1 - SJ := by
    rw [KchkCG, hsp]; ring
  have hB2 : n2.nrm (KchkCG Al j F Y - dIPowG Al j F Y) ≤
      ENNReal.ofReal ((1 + 2 ^ d * cJ) * κ₀ * (2 * A⁻¹) ^ nb j Y) := by
    rw [e2]
    exact (n2.subR (by positivity) (by positivity) hS1 hSJ).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  refine ⟨?_, hB2, ?_, ?_⟩
  · have e1 : KchkCG Al j F Y = dIPowG Al j F Y + (KchkCG Al j F Y - dIPowG Al j F Y) := by
      ring
    rw [e1]
    exact (n2.addR (by positivity) (by positivity) hdIY hB2).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  · refine hdIY.trans (ENNReal.ofReal_le_ofReal ?_)
    have : δ₁ ≤ (1 + 2 ^ d * cJ) * κ₀ + δ₁ := by
      have : 0 ≤ (1 + 2 ^ d * cJ) * κ₀ := by positivity
      linarith
    gcongr
  · have e4 : KchkCG Al j F Y - Al.θ (F.K Y) - dIPowG Al j F Y + SJ = S2 := by
      rw [KchkCG, hsp, hsp2]; ring
    rw [e4]; exact hS2

theorem thetaJ_le_kappa {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) :
    n2.nrm (Al.θ (F.J b X)) ≤ ENNReal.ofReal ((1 + 2 ^ d * cJ) * κ₀) := by
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
    n2.nrm ((KchkG Al j F g.2 - if g.1 = ∅ then dIPowG Al j F g.2 else 0) *
      JprodG Al F g.1) ≤
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
  have hB := fun Y (hY : Y ∈ Comp j g.2) => H.KchkC_bounds (isConn_of_mem_comp hg2 hY)
  have h4 : (4 * A⁻¹) ^ nb j g.2 = 2 ^ nb j g.2 * (2 * A⁻¹) ^ nb j g.2 := by
    rw [← mul_pow]; ring_nf
  have hw : ∏ Y ∈ Comp j g.2, (2 * A⁻¹) ^ nb j Y = (2 * A⁻¹) ^ nb j g.2 := prod_comp_pow hg2 _
  by_cases h1 : g.1 = ∅
  · have hJ1 : JprodG Al F g.1 = 1 := by rw [h1, JprodG, prod_empty]
    rw [if_pos h1, hJ1, mul_one]
    have e : KchkG Al j F g.2 - dIPowG Al j F g.2 =
        ∏ Y ∈ Comp j g.2, (dIPowG Al j F Y + (KchkCG Al j F Y - dIPowG Al j F Y)) -
          ∏ Y ∈ Comp j g.2, dIPowG Al j F Y := by
      rw [KchkG, dIPowG_eq_prod_comp Al j F hg2]; simp only [add_sub_cancel]
    rw [e]
    classical
    refine (n2.prod_sub_prod (Comp j g.2)
      (dIPowG Al j F) (fun Y => KchkCG Al j F Y - dIPowG Al j F Y)
      (fun Y => (2 * A⁻¹) ^ nb j Y)
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
    have hK1 : n2.nrm (KchkG Al j F g.2) ≤
        ENNReal.ofReal (β ^ (Comp j g.2).card * (2 * A⁻¹) ^ nb j g.2) := by
      have := n2.prodR (Comp j g.2) (KchkCG Al j F)
        (fun Y => β * (2 * A⁻¹) ^ nb j Y) (fun _ _ => by positivity) (fun Y hY => (hB Y hY).1)
      rwa [prod_mul_distrib, prod_const, hw] at this
    have hJ : n2.nrm (JprodG Al F g.1) ≤ ENNReal.ofReal (κ ^ g.1.card) := by
      have := n2.prodR g.1
        (fun p => Al.θ (F.J p.1 p.2)) (fun _ => κ) (fun _ _ => hκ0)
        (fun p hp => H.thetaJ_le_kappa (hg1 p hp) p.2)
      rwa [prod_const] at this
    refine (n2.mulR (by positivity) hK1 hJ).trans (ENNReal.ofReal_le_ofReal ?_)
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
    n2.nrm (KchkG Al j F Y - Al.θ (F.K Y) - dIPowG Al j F Y +
      ∑ b ∈ blocks j Y, Al.θ (F.J b Y)) ≤
      ENNReal.ofReal (κ₀ * δ₁ * (4 * A⁻¹) ^ nb j Y) := by
  have hρ := H.hρ0
  have hκ := H.hκ₀
  have hδ := H.hδ₁
  rw [KchkG, comp_of_isConn hY, prod_singleton]
  refine (H.KchkC_bounds hY).2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  norm_num

end KHypG

/-! ### Lemma `lem:Ri-bd` -/

/-- The hypotheses for the bounds on `𝓡^1, 𝓡^2, 𝓡^3` at a fixed `U`. -/
structure RHypG (Al : RGAlg R R2) (j : ℕ) (F : RGIngr d L N R) (n : SNorm R) (n2 : SNorm R2)
    (U : Finset (Lam d L N)) (A κ₀ δ₁ cJ a η P : ℝ) (M : ℕ) : Prop
    extends KHypG Al j F n2 A κ₀ δ₁ cJ where
  hE : ∀ x : R2, n.nrm (Al.E x) ≤ n2.nrm x
  hJ0 : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
    ∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X), F.J b X = 0
  hU : IsPolymer (j + 1) U
  ha : 0 ≤ a
  ha1 : a ≤ 1 / 40
  heu : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, n.nrm (F.eu b) ≤ ENNReal.ofReal (Real.exp a)
  hIt : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
    n.nrm (It F b - 1) ≤ ENNReal.ofReal (10 * a)
  hpref : Real.exp (11 * a * nb j U) ≤ 2 ^ nb (j + 1) U
  hcount : (Gset j U).card ≤ M ^ nb (j + 1) U
  hη : 0 ≤ η
  hgeom : ∀ g ∈ Gset j U, (1 + 2 * η) * (nb (j + 1) U : ℝ) ≤
    nb j g.2 + (1 + 2 * η) * 2 ^ d * ((Comp j g.2).card + g.1.card)
  hP : P = 2 * M
  hM : 1 ≤ M
  hAP : 4 * P ≤ A ^ (2 * η / (1 + 2 * η))

namespace RHypG

variable {Al : RGAlg R R2} {j : ℕ} {F : RGIngr d L N R} {n : SNorm R} {n2 : SNorm R2}
  {U : Finset (Lam d L N)} {A κ₀ δ₁ cJ a η P : ℝ} {M : ℕ}
  (H : RHypG Al j F n n2 U A κ₀ δ₁ cJ a η P M)
include H

theorem hP1 : 1 ≤ P := by
  rw [H.hP]; have : (1 : ℝ) ≤ M := by exact_mod_cast H.hM
  linarith

theorem It_le {b : Fin d → ℕ} (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) :
    n.nrm (It F b) ≤ ENNReal.ofReal (Real.exp (10 * a)) := by
  have e : It F b = 1 + (It F b - 1) := by ring
  rw [e]
  refine (n.addR zero_le_one (by linarith [H.ha]) n.oneR (H.hIt b hb)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have := Real.add_one_le_exp (10 * a)
  linarith

/-- `‖e^{u_{j+1}(U)} e^{-(u+V)_{j+1}(U ∖ W)}‖ ≤ 2^{|𝓑_{j+1}(U)|}`. -/
theorem pref (W : Finset (Lam d L N)) :
    n.nrm (PrefG j F U * ItPow j F (U \ W)) ≤ ENNReal.ofReal (2 ^ nb (j + 1) U) := by
  have ha := H.ha
  have hU : IsPolymer j U := IsPolymer.of_succ H.hU
  have hsub : blocks j (U \ W) ⊆ blocks j U := blocks_mono sdiff_subset
  have h1 : n.nrm (PrefG j F U) ≤ ENNReal.ofReal (Real.exp a ^ nb j U) := by
    have := n.prodR (blocks j U) F.eu (fun _ => Real.exp a) (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.heu b (mem_blockIdx_of_mem_blocks hb))
    rwa [prod_const] at this
  have h2 : n.nrm (ItPow j F (U \ W)) ≤ ENNReal.ofReal (Real.exp (10 * a) ^ nb j U) := by
    have := n.prodR (blocks j (U \ W)) (It F) (fun _ => Real.exp (10 * a))
      (fun _ _ => (Real.exp_pos _).le)
      (fun b hb => H.It_le (mem_blockIdx_of_mem_blocks (hsub hb)))
    rw [prod_const] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (card_le_card hsub)
  refine (n.mulR (by positivity) h1 h2).trans (ENNReal.ofReal_le_ofReal ?_)
  refine le_trans (le_of_eq ?_) H.hpref
  rw [← mul_pow, ← Real.exp_add, ← Real.exp_nat_mul]
  congr 1; ring

theorem term_le (W : Finset (Lam d L N)) (x : R2) {r : ℝ}
    (_hr : 0 ≤ r) (hx : n2.nrm x ≤ ENNReal.ofReal r) :
    n.nrm ((PrefG j F U * ItPow j F (U \ W)) * Al.E x) ≤
      ENNReal.ofReal (2 ^ nb (j + 1) U * r) :=
  n.mulR (by positivity) (H.pref W) ((H.hE x).trans hx)

/-- `‖1 - e^{-(u+V)_{j+1}(X)}‖ ≤ |𝓑(X)| 10 a (1 + 10 a)^{|𝓑(X)| - 1}`. -/
theorem one_sub_ItPow_le (X : Finset (Lam d L N)) :
    n.nrm (1 - ItPow j F X) ≤
      ENNReal.ofReal (nb j X * (10 * a) * (1 + 10 * a) ^ (nb j X - 1)) := by
  have ha := H.ha
  have key := n.prod_sub_prod (blocks j X)
    (fun _ => (1 : R)) (fun b => It F b - 1) (fun _ => 1)
    (β := 1 + 10 * a) (κ := 10 * a) (fun _ _ => zero_le_one) (by positivity) (by linarith)
    (fun b _ => by
      simp only [mul_one]
      exact n.oneR.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    (fun b hb => by
      simp only [add_sub_cancel, mul_one]
      have e : It F b = 1 + (It F b - 1) := by ring
      rw [e]
      exact n.addR zero_le_one (by positivity) n.oneR (H.hIt b (mem_blockIdx_of_mem_blocks hb)))
    (fun b hb => by rw [mul_one]; exact H.hIt b (mem_blockIdx_of_mem_blocks hb))
  simp only [add_sub_cancel, prod_const_one, mul_one] at key
  rw [← neg_sub, n.neg]
  exact key

theorem R1_le :
    ENNReal.ofReal (A ^ nb (j + 1) U) * n.nrm (R1G Al j F U) ≤
      ENNReal.ofReal ((A * P) ^ 2 ^ d * (2 ^ d * (10 * a) * 2 ^ 2 ^ d) *
        (cJ * κ₀ * A⁻¹ ^ 2 ^ d)) := by
  classical
  have hA0 : 0 < A := by linarith [H.hA]
  have hP1 := H.hP1
  have hκ := H.hκ₀
  have hc := H.hcJ
  have ha := H.ha
  have hρ := H.hρ0
  set x := nb (j + 1) U
  rw [R1G_eq Al j F H.hJ0 H.hU]
  refine n.wsum_bound _ _ (M ^ x) ((card_filter_le _ _).trans H.hcount)
    fun g hg => ?_
  obtain ⟨hgG, h1, h2⟩ := mem_filter.1 hg
  obtain ⟨p, hp⟩ := card_eq_one.1 h1
  obtain ⟨-, -, -, f4⟩ := Gset_facts hgG
  obtain ⟨hb, hs, -⟩ := mem_pairsU.1 (f4 p (by rw [hp]; exact mem_singleton_self p)).1
  have hX : Xcal g.1 = p.2 := by rw [hp, Xcal, singleton_biUnion]
  have hJ : n.nrm (Al.E (JprodG Al F g.1)) ≤ ENNReal.ofReal (cJ * κ₀ * A⁻¹ ^ 2 ^ d) := by
    rw [hp, JprodG, prod_singleton]
    exact (H.hE _).trans (H.hJ p.1 hb p.2)
  have hO := H.one_sub_ItPow_le (Xcal g.1)
  have hT := n.mulR (by positivity) (H.pref (Xcal g.1)) (n.mulR (by positivity) hO hJ)
  refine (mul_le_mul_right hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx : x ≤ 2 ^ d := by
    have := H.hgeom g hgG
    rw [h2, nb_empty', comp_empty, card_empty, h1] at this
    have hη := H.hη
    have : (x : ℝ) ≤ 2 ^ d := by
      push_cast at this
      nlinarith
    exact_mod_cast this
  have hnX : nb j (Xcal g.1) ≤ 2 ^ d := by rw [hX]; exact hs.2.2
  have hAP1 : 1 ≤ A * P := one_le_mul_of_one_le_of_one_le H.hA hP1
  have e1 : ((M ^ x : ℕ) : ℝ) * A ^ x * 2 ^ x = (A * P) ^ x := by
    rw [H.hP, mul_pow, mul_pow]; push_cast; ring
  have e2 : (A * P) ^ x ≤ (A * P) ^ 2 ^ d := pow_le_pow_right₀ hAP1 hx
  have e3 : (nb j (Xcal g.1) : ℝ) * (10 * a) * (1 + 10 * a) ^ (nb j (Xcal g.1) - 1) ≤
      2 ^ d * (10 * a) * 2 ^ 2 ^ d := by
    have hn : (nb j (Xcal g.1) : ℝ) ≤ 2 ^ d := by exact_mod_cast hnX
    have h10 : 1 + 10 * a ≤ 2 := by linarith [H.ha1]
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

theorem R2_le (hDβ : (A * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * κ₀ + δ₁) ≤ 1) :
    ENNReal.ofReal (A ^ nb (j + 1) U) * n.nrm (R2G Al j F U) ≤
      ENNReal.ofReal (((A * P) ^ 2 ^ d) ^ 2 *
        ((1 + 2 ^ d * cJ) * κ₀ * ((1 + 2 ^ d * cJ) * κ₀ + δ₁))) := by
  classical
  have hA0 : 0 < A := by linarith [H.hA]
  have hP1 := H.hP1
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  set x := nb (j + 1) U
  set κ := (1 + 2 ^ d * cJ) * κ₀ with hκdef
  set β := (1 + 2 ^ d * cJ) * κ₀ + δ₁ with hβdef
  have hκ0 : 0 ≤ κ := by positivity
  have hβ0 : 0 ≤ β := by positivity
  set S := (Gset j U).filter (fun g => 2 ≤ g.1.card + (Comp j g.2).card)
  have e : R2G Al j F U = ∑ g ∈ S, (PrefG j F U * ItPow j F (U \ (g.2 ∪ Xcal g.1))) *
        Al.E ((KchkG Al j F g.2 - if g.1 = ∅ then dIPowG Al j F g.2 else 0) *
          JprodG Al F g.1) := by
    rw [R2G, mul_sum]; exact sum_congr rfl fun g _ => (mul_assoc _ _ _).symm
  rw [e]
  refine n.wsum_bound S _ (M ^ x) ((card_filter_le _ _).trans H.hcount) fun g hg => ?_
  obtain ⟨hgG, hm⟩ := mem_filter.1 hg
  obtain ⟨f1, -, -, f4⟩ := Gset_facts hgG
  have hI := H.toKHypG.R2_integrand_le f1 (fun p hp => (mem_pairsU.1 (f4 p hp).1).1) hm
  have hT := H.term_le (g.2 ∪ Xcal g.1) _ (by positivity) hI
  refine (mul_le_mul_right hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set m := g.1.card + (Comp j g.2).card
  set t := nb j g.2
  have hgeo := geom_real (d := d) (x := x) (t := t) (m := m) H.hA hP1 H.hη
    (by
      rw [show ((m : ℕ) : ℝ) = ((Comp j g.2).card : ℝ) + g.1.card by push_cast [m]; ring]
      exact H.hgeom g hgG) H.hAP
  have hpm := pow_m_real (D := (A * P) ^ 2 ^ d) (κ := κ) (β := β) (m := m) (by positivity)
    hκ0 hβ0 hDβ hm
  have hkb : 0 ≤ κ * β ^ (m - 1) := by positivity
  calc ((M ^ x : ℕ) : ℝ) * A ^ x * (2 ^ x * (κ * β ^ (m - 1) * (4 * A⁻¹) ^ t))
      = (A ^ x * P ^ x * (4 * A⁻¹) ^ t) * (κ * β ^ (m - 1)) := by
        rw [H.hP, mul_pow]; push_cast; ring
    _ ≤ (A * P) ^ (2 ^ d * m) * (κ * β ^ (m - 1)) := by gcongr
    _ = ((A * P) ^ 2 ^ d) ^ m * (κ * β ^ (m - 1)) := by rw [pow_mul]
    _ ≤ _ := hpm

theorem R3_le :
    ENNReal.ofReal (A ^ nb (j + 1) U) * n.nrm (R3G Al j F U) ≤
      ENNReal.ofReal ((A * P) ^ 2 ^ d * (κ₀ * δ₁)) := by
  classical
  have hA0 : 0 < A := by linarith [H.hA]
  have hP1 := H.hP1
  have hκ := H.hκ₀
  have hδ := H.hδ₁
  set x := nb (j + 1) U
  set S := (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2)
  have e : R3G Al j F U = ∑ g ∈ S, (PrefG j F U * ItPow j F (U \ g.2)) *
        Al.E (KchkG Al j F g.2 - Al.θ (F.K g.2) - dIPowG Al j F g.2 +
          ∑ b ∈ blocks j g.2, Al.θ (F.J b g.2)) := by
    rw [R3G, mul_sum]; exact sum_congr rfl fun g _ => (mul_assoc _ _ _).symm
  rw [e]
  refine n.wsum_bound S _ (M ^ x) ((card_filter_le _ _).trans H.hcount) fun g hg => ?_
  obtain ⟨hgG, h1, hc⟩ := mem_filter.1 hg
  have hI := H.toKHypG.R3_integrand_le hc
  have hT := H.term_le g.2 _ (by positivity) hI
  refine (mul_le_mul_right hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := nb j g.2
  have hgeo := geom_real (d := d) (x := x) (t := t) (m := 1) H.hA hP1 H.hη
    (by
      have := H.hgeom g hgG
      rw [comp_of_isConn hc, card_singleton, h1, card_empty] at this
      push_cast at this ⊢; linarith) H.hAP
  calc ((M ^ x : ℕ) : ℝ) * A ^ x * (2 ^ x * (κ₀ * δ₁ * (4 * A⁻¹) ^ t))
      = (A ^ x * P ^ x * (4 * A⁻¹) ^ t) * (κ₀ * δ₁) := by
        rw [H.hP, mul_pow]; push_cast; ring
    _ ≤ (A * P) ^ (2 ^ d * 1) * (κ₀ * δ₁) := by gcongr
    _ = _ := by rw [mul_one]

/-- **Lemma `lem:Ri-bd`** (generic): the weighted norm of `𝓡^1 + 𝓡^2 + 𝓡^3`. -/
theorem R_le (hDβ : (A * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * κ₀ + δ₁) ≤ 1) :
    ENNReal.ofReal (A ^ nb (j + 1) U) *
      n.nrm (R1G Al j F U + R2G Al j F U + R3G Al j F U) ≤
      ENNReal.ofReal ((A * P) ^ 2 ^ d * (2 ^ d * (10 * a) * 2 ^ 2 ^ d) *
          (cJ * κ₀ * A⁻¹ ^ 2 ^ d) +
        ((A * P) ^ 2 ^ d) ^ 2 * ((1 + 2 ^ d * cJ) * κ₀ * ((1 + 2 ^ d * cJ) * κ₀ + δ₁)) +
        (A * P) ^ 2 ^ d * (κ₀ * δ₁)) := by
  have hA0 : 0 < A := by linarith [H.hA]
  have hP0 : 0 < P := by linarith [H.hP1]
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  have ha := H.ha
  refine (mul_le_mul_right ((n.add _ _).trans (add_le_add (n.add _ _) le_rfl)) _).trans ?_
  rw [mul_add, mul_add]
  refine (add_le_add (add_le_add H.R1_le (H.R2_le hDβ)) H.R3_le).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end RHypG

end

end Obs.Gen
