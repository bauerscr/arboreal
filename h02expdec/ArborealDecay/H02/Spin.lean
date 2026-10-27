module

public import ArborealDecay.H02.Main

/-!
# Corollary `cor:spin`

Spin representations of arboreal gas probabilities, for `h = 0` and non-negative symmetric edge
weights `β`:
* `P_β[ab] = β_ab ⟨u_a · u_b + 1⟩_β`                                     (`e:edge-spin`)
* `P_β[S] = ⟨∏_{ij ∈ S} β_ij (u_i · u_j + 1)⟩_β`                         (`e:edges-spin`)
* `P_β[a ↔ b] = -⟨z_a z_b⟩_β = -⟨u_a · u_b⟩_β = ⟨ξ_a η_b⟩_β = 1 - ⟨η_a ξ_a η_b ξ_b⟩_β`
                                                                           (`e:conn-spin`)
* `⟨z_a⟩_β = 0`                                                           (`eq:expz0`)
-/

@[expose] public section

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

local notation "A" => Grassmann Λ

/-! ## Definitions -/

theorem inv'_dot (i j : Λ) : inv' (dot i j) = dot i j := by simp [dot, z]

theorem dot_comm (i j : Λ) : dot i j = dot j i := by
  have := congrArg cv (Xc_comm i j)
  simpa [coe_Xc] using this

/-- The factor `β_ij (u_i · u_j + 1)` attached to the unordered pair `ij`. -/
def edgeSpin (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) : Sym2 Λ → A :=
  Sym2.lift ⟨fun i j => β i j • (dot i j + 1), fun i j => by
    show β i j • (dot i j + 1) = β j i • (dot j i + 1); rw [hβ, dot_comm]⟩

theorem inv'_edgeSpin (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (e : Sym2 Λ) :
    inv' (edgeSpin β hβ e) = edgeSpin β hβ e := by
  induction e using Sym2.ind with
  | h i j => simp [edgeSpin, map_smul, inv'_dot]

/-- `∏_{ij ∈ S} β_ij (u_i · u_j + 1)`. The factors are even, hence commute, so the product is
well defined. -/
def edgeProd (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (S : Finset (Sym2 Λ)) : A :=
  S.noncommProd (edgeSpin β hβ) fun e _ _ _ _ => mul_comm_of_even (inv'_edgeSpin β hβ e) _

/-- The weight `∏_{ij ∈ F} β_ij` of a forest `F`. -/
def forestWeight (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (F : SimpleGraph Λ) : ℝ :=
  ∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e

/-- The partition function `Z_β = ∑_{F ∈ 𝓕} ∏_{ij ∈ F} β_ij` of the arboreal gas. -/
def Zforest (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) : ℝ :=
  ∑ F : SimpleGraph Λ with F.IsAcyclic, forestWeight β hβ F

/-- The arboreal gas probability `P_β[P] = Z_β⁻¹ ∑_{F ∈ 𝓕, F satisfies P} ∏_{ij ∈ F} β_ij`. -/
def arborealProb (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (P : SimpleGraph Λ → Prop) : ℝ :=
  (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ P F, forestWeight β hβ F) / Zforest β hβ

/-- The normalised expectation `⟨F⟩_{β,h} = [F]_{β,h} / [1]_{β,h}`. -/
def avg (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : A) : ℝ := expect β h F / expect β h 1

/-! ## Linearity of the expectation -/

/-- The expectation as a linear map. -/
def expectL (β : Λ → Λ → ℝ) (h : Λ → ℝ) : A →ₗ[ℝ] ℝ :=
  ExteriorAlgebra.algebraMapInv.toLinearMap ∘ₗ berezin (univ : Finset Λ).toList ∘ₗ
    LinearMap.mulRight ℝ (IsNilpotent.exp (-action β h))

theorem expect_eq_L (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : A) : expect β h F = expectL β h F := rfl

theorem expect_add (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F G : A) :
    expect β h (F + G) = expect β h F + expect β h G := by
  simp only [expect_eq_L, map_add]

theorem expect_sub (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F G : A) :
    expect β h (F - G) = expect β h F - expect β h G := by
  simp only [expect_eq_L, map_sub]

theorem expect_neg (β : Λ → Λ → ℝ) (h : Λ → ℝ) (F : A) :
    expect β h (-F) = -expect β h F := by
  simp only [expect_eq_L, map_neg]

theorem expect_smul (β : Λ → Λ → ℝ) (h : Λ → ℝ) (r : ℝ) (F : A) :
    expect β h (r • F) = r * expect β h F := by
  simp only [expect_eq_L, map_smul, smul_eq_mul]

theorem int0_smul (r : ℝ) (F : A) : int0 (r • F) = r * int0 F := by
  simp [int0, map_smul]

/-! ## The partition function -/

theorem expect_one_eq_Z (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) :
    expect β 0 1 = Zforest β hβ := by
  rw [thm_H02forest β hβ 0]
  simp [Zforest, forestWeight]

theorem forestWeight_nonneg {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (F : SimpleGraph Λ) : 0 ≤ forestWeight β hβ F := by
  refine Finset.prod_nonneg fun e _ => ?_
  induction e using Sym2.ind with | h i j => exact hβ0 i j

theorem Zforest_pos {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) :
    0 < Zforest β hβ := by
  have h1 : forestWeight β hβ ⊥ = 1 := Finset.prod_eq_one fun e he => by simp at he
  have := Finset.single_le_sum (s := univ.filter fun F : SimpleGraph Λ => F.IsAcyclic)
    (fun F _ => forestWeight_nonneg hβ hβ0 F) (a := ⊥) (by simp)
  rw [h1] at this
  exact lt_of_lt_of_le one_pos this

theorem expect_one_ne_zero {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) : expect β 0 1 ≠ 0 := by
  rw [expect_one_eq_Z β hβ]; exact (Zforest_pos hβ hβ0).ne'

/-! ## Expectations of central forms -/

theorem exp_W0 (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) :
    IsNilpotent.exp (W β hβ 0) =
      ∑ t ∈ (E (⊤ : SimpleGraph Λ)).powerset, (∏ e ∈ t, Sym2.lift ⟨β, hβ⟩ e) • ∏ e ∈ t, Xs e := by
  rw [exp_W]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (∅ : Finset Λ)]
  · simp [mono]
  · intro R _ hR
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hR
    rw [Finset.prod_eq_zero hi (by simp), mul_zero, zero_smul]
  · simp

theorem expect_cv_eq (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (F : A) :
    expect β 0 F = int0 (F * cv (IsNilpotent.exp (W β hβ 0))) := by
  rw [expect, action_eq β hβ 0, neg_neg, ← IsNilpotent.map_exp (isNilpotent_W β hβ 0)]

/-- Expansion of `[c]_β` for a central form `c`, as a sum over edge sets. -/
theorem expect_cv_t (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (c : C Λ) :
    expect β 0 (cv c) = ∑ t ∈ (E (⊤ : SimpleGraph Λ)).powerset,
      (∏ e ∈ t, Sym2.lift ⟨β, hβ⟩ e) * int0 (cv (c * ∏ e ∈ t, Xs e)) := by
  rw [expect_cv_eq β hβ, ← map_mul, exp_W0, Finset.mul_sum, map_sum, int0_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm, map_smul, int0_smul]

/-- Expansion of `[c]_β` for a central form `c`, as a sum over graphs. -/
theorem expect_cv (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (c : C Λ) :
    expect β 0 (cv c) = ∑ G : SimpleGraph Λ,
      (∏ e ∈ E G, Sym2.lift ⟨β, hβ⟩ e) * int0 (cv (c * ∏ e ∈ E G, Xs e)) := by
  rw [expect_cv_t β hβ, sum_E_powerset (fun t => (∏ e ∈ t, Sym2.lift ⟨β, hβ⟩ e) *
    int0 (cv (c * ∏ e ∈ t, Xs e)))]

theorem int0_prodX (G : SimpleGraph Λ) :
    int0 (cv (∏ e ∈ E G, Xs e)) = if G.IsAcyclic then 1 else 0 := by
  have := int0_mono G ∅
  simp only [mono, Finset.prod_empty, mul_one] at this
  rw [this]
  simp [Good]

theorem prodX_mul (S t : Finset (Sym2 Λ)) :
    (∏ e ∈ S, Xs e) * ∏ e ∈ t, Xs e = if Disjoint S t then ∏ e ∈ S ∪ t, Xs e else 0 := by
  split_ifs with h
  · rw [Finset.prod_union h]
  · obtain ⟨e, heS, het⟩ := Finset.not_disjoint_iff.1 h
    rw [← Finset.mul_prod_erase S _ heS, ← Finset.mul_prod_erase t _ het]
    linear_combination (∏ x ∈ S.erase e, Xs x) * (∏ x ∈ t.erase e, Xs x) * Xs_sq e

theorem forestWeight_eq (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (G : SimpleGraph Λ) :
    forestWeight β hβ G = ∏ e ∈ E G, Sym2.lift ⟨β, hβ⟩ e := by
  rw [forestWeight, E_eq]

theorem mem_E_top {e : Sym2 Λ} : e ∈ E (⊤ : SimpleGraph Λ) ↔ ¬e.IsDiag := by
  simp

/-! ## Edge probabilities -/

theorem sum_disjoint_union {M : Type*} [AddCommMonoid M] {U S : Finset (Sym2 Λ)} (hS : S ⊆ U)
    (g : Finset (Sym2 Λ) → M) :
    ∑ t ∈ U.powerset, (if Disjoint S t then g (S ∪ t) else 0) =
      ∑ u ∈ U.powerset, (if S ⊆ u then g u else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun t => S ∪ t) (fun u => u \ S) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht ⊢
    exact ⟨Finset.union_subset hS ht.1, Finset.subset_union_left⟩
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu ⊢
    exact ⟨Finset.sdiff_subset.trans hu.1, Finset.disjoint_sdiff⟩
  · intro t ht
    simp only [Finset.mem_filter] at ht
    exact Finset.union_sdiff_cancel_left ht.2
  · intro u hu
    simp only [Finset.mem_filter] at hu
    exact Finset.union_sdiff_of_subset hu.2
  · intro t _; rfl

/-- `[∏_{ij ∈ S} β_ij (1 + u_i · u_j)]_β = ∑_{F ∈ 𝓕, S ⊆ F} ∏_{ij ∈ F} β_ij`. -/
theorem expect_prodX (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (S : Finset (Sym2 Λ)) :
    (∏ e ∈ S, Sym2.lift ⟨β, hβ⟩ e) * expect β 0 (cv (∏ e ∈ S, Xs e)) =
      ∑ G : SimpleGraph Λ with G.IsAcyclic ∧ ↑S ⊆ G.edgeSet, forestWeight β hβ G := by
  by_cases hS : S ⊆ E (⊤ : SimpleGraph Λ)
  · rw [expect_cv_t β hβ, Finset.mul_sum]
    have : ∀ t ∈ (E (⊤ : SimpleGraph Λ)).powerset, (∏ e ∈ S, Sym2.lift ⟨β, hβ⟩ e) *
        ((∏ e ∈ t, Sym2.lift ⟨β, hβ⟩ e) * int0 (cv ((∏ e ∈ S, Xs e) * ∏ e ∈ t, Xs e))) =
        if Disjoint S t then (∏ e ∈ S ∪ t, Sym2.lift ⟨β, hβ⟩ e) *
          int0 (cv (∏ e ∈ S ∪ t, Xs e)) else 0 := by
      intro t _
      rw [prodX_mul]
      split_ifs with h
      · rw [Finset.prod_union h, Finset.prod_union h]; ring
      · simp [int0]
    rw [Finset.sum_congr rfl this, sum_disjoint_union hS (fun u =>
        (∏ e ∈ u, Sym2.lift ⟨β, hβ⟩ e) * int0 (cv (∏ e ∈ u, Xs e))),
      sum_E_powerset (fun u => if S ⊆ u then
        (∏ e ∈ u, Sym2.lift ⟨β, hβ⟩ e) * int0 (cv (∏ e ∈ u, Xs e)) else 0),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [int0_prodX, forestWeight_eq]
    have hSG : S ⊆ E G ↔ ↑S ⊆ G.edgeSet := by
      constructor
      · intro h e he; exact mem_E.1 (h he)
      · intro h e he; exact mem_E.2 (h he)
    by_cases h1 : S ⊆ E G <;> by_cases h2 : G.IsAcyclic <;> simp [h1, h2, ← hSG]
  · obtain ⟨e, heS, heT⟩ := Finset.not_subset.1 hS
    have hdiag := mem_E_top.not.1 heT
    push Not at hdiag
    have hX : Xs e = 0 := by
      induction e using Sym2.ind with
      | h a b =>
        rw [Sym2.mk_isDiag_iff] at hdiag
        rw [hdiag, Xs_mk, Xc_self]
    rw [Finset.prod_eq_zero heS hX, map_zero, show expect β 0 0 = 0 by
      simpa using expect_smul β 0 0 0, mul_zero]
    refine (Finset.sum_eq_zero fun G hG => ?_).symm
    simp only [Finset.mem_filter] at hG
    exact absurd (hG.2.2 heS) (SimpleGraph.not_isDiag_of_mem_edgeSet _ |>.mt (not_not.2 hdiag))

theorem edgeSpin_eq (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (e : Sym2 Λ) :
    edgeSpin β hβ e = cv (Sym2.lift ⟨β, hβ⟩ e • Xs e) := by
  induction e using Sym2.ind with
  | h i j => simp [edgeSpin, map_smul, coe_Xc, add_comm]

theorem edgeProd_eq (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (S : Finset (Sym2 Λ)) :
    edgeProd β hβ S = cv ((∏ e ∈ S, Sym2.lift ⟨β, hβ⟩ e) • ∏ e ∈ S, Xs e) := by
  rw [← Finset.prod_smul, ← Finset.noncommProd_eq_prod _ _]
  refine Eq.trans ?_ (Finset.map_noncommProd _ _ _ cv).symm
  exact Finset.noncommProd_congr rfl (fun e _ => edgeSpin_eq β hβ e) _

/-- **Corollary `cor:spin`, (`e:edges-spin`).** For every set `S` of edges,
`P_β[S] = ⟨∏_{ij ∈ S} β_ij (u_i · u_j + 1)⟩_β`. -/
theorem cor_spin_edges {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (S : Finset (Sym2 Λ)) :
    arborealProb β hβ (fun F => ↑S ⊆ F.edgeSet) = avg β 0 (edgeProd β hβ S) := by
  rw [arborealProb, avg, edgeProd_eq, map_smul, expect_smul, expect_prodX, expect_one_eq_Z β hβ]

/-- **Corollary `cor:spin`, (`e:edge-spin`).** For all `a, b`,
`P_β[ab] = β_ab ⟨u_a · u_b + 1⟩_β`. -/
theorem cor_spin_edge {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (a b : Λ) :
    arborealProb β hβ (fun F => F.Adj a b) = β a b * avg β 0 (dot a b + 1) := by
  have h1 := cor_spin_edges hβ {s(a, b)}
  simp only [Finset.coe_singleton, Set.singleton_subset_iff, SimpleGraph.mem_edgeSet] at h1
  rw [h1, edgeProd, Finset.noncommProd_singleton, avg, avg,
    show edgeSpin β hβ s(a, b) = β a b • (dot a b + 1) from rfl, expect_smul, mul_div_assoc]

/-! ## Ward identities -/

theorem T_exp_W0 (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) :
    T univ (cv (IsNilpotent.exp (W β hβ 0))) = 0 := by
  rw [exp_W0, map_sum, map_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [map_smul, map_smul, T_prod univ t Xs (fun e _ => ?_) (fun e _ => ?_), smul_zero] <;>
  induction e using Sym2.ind with
  | h a b =>
    first
    | exact T_Xc (mem_univ a) (mem_univ b)
    | exact inv'_Xc a b

/-- `T` is a symmetry of `[·]_β` when `h = 0` (Lemma `lem:hypsym`). -/
theorem expect_T (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (y : A) :
    expect β 0 (T univ y) = 0 := by
  rw [expect_cv_eq β hβ]
  have : T univ y * cv (IsNilpotent.exp (W β hβ 0)) =
      T univ (y * cv (IsNilpotent.exp (W β hβ 0))) := by
    rw [T_mul, T_exp_W0, mul_zero, add_zero]
  rw [this, int0, berezin_T (fun i _ => Finset.mem_toList.2 (mem_univ i)), map_zero]

theorem T_zξ (a b : Λ) : T univ (z b * ξ a) = ξ a * η b + z a * z b := by
  rw [T_mul, T_z (mem_univ b), inv'_z, T_ξ (mem_univ a), neg_mul, η_anticomm_ξ, neg_neg,
    mul_comm_of_even (inv'_z b) (z a)]

theorem expect_zz (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : Λ) :
    expect β 0 (z a * z b) = -expect β 0 (ξ a * η b) := by
  have := expect_T β hβ (z b * ξ a)
  rw [T_zξ, expect_add] at this
  linarith

/-- **Corollary `cor:spin`, (`eq:expz0`).** `⟨z_a⟩_β = 0`. -/
theorem cor_spin_z (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (a : Λ) :
    avg β 0 (z a) = 0 := by
  rw [avg, ← T_ξ (mem_univ a), expect_T β hβ, zero_div]

/-! ## Connection probabilities -/

theorem E_sup_edge (G : SimpleGraph Λ) {a b : Λ} (hab : a ≠ b) :
    E (G ⊔ SimpleGraph.edge a b) = insert s(a, b) (E G) := by
  ext e
  simp only [mem_E, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge, Finset.mem_insert,
    Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Sym2.mem_diagSet]
  constructor
  · rintro (h | ⟨rfl, _⟩) <;> tauto
  · rintro (rfl | h)
    · exact Or.inr ⟨rfl, hab⟩
    · exact Or.inl h

theorem term_X (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) {a b : Λ} (hab : a ≠ b)
    (G : SimpleGraph Λ) :
    (∏ e ∈ E G, Sym2.lift ⟨β, hβ⟩ e) * int0 (cv (Xc a b * ∏ e ∈ E G, Xs e)) =
      if G.IsAcyclic ∧ ¬G.Reachable a b then ∏ e ∈ E G, Sym2.lift ⟨β, hβ⟩ e else 0 := by
  by_cases hG : G.Adj a b
  · have hmem : s(a, b) ∈ E G := by simpa using hG
    have : Xc a b * ∏ e ∈ E G, Xs e = 0 := by
      rw [← Finset.mul_prod_erase _ _ hmem, Xs_mk, ← mul_assoc, Xc_sq, zero_mul]
    rw [this, map_zero, if_neg (fun h => h.2 hG.reachable)]
    simp [int0]
  · have hnot : s(a, b) ∉ E G := by simpa using hG
    rw [← Xs_mk, ← Finset.prod_insert hnot, ← E_sup_edge G hab, int0_prodX,
      SimpleGraph.isAcyclic_sup_fromEdgeSet_iff]
    have : (G.Reachable a b → a = b ∨ G.Adj a b) ↔ ¬G.Reachable a b := by tauto
    rw [this]
    split_ifs <;> simp

theorem sum_reach (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : Λ) :
    ∑ G : SimpleGraph Λ with G.IsAcyclic ∧ G.Reachable a b, forestWeight β hβ G =
      -expect β 0 (dot a b) := by
  by_cases hab : a = b
  · subst hab
    have hd : dot a a = -1 := by
      have := congrArg cv (Xc_self a)
      rw [coe_Xc, map_zero] at this
      exact eq_neg_of_add_eq_zero_right this
    rw [hd, expect_neg, neg_neg, expect_one_eq_Z β hβ, Zforest]
    simp
  have hX := expect_cv β hβ (Xc a b)
  rw [coe_Xc, expect_add, expect_one_eq_Z β hβ, Finset.sum_congr rfl fun G _ => term_X β hβ hab G]
    at hX
  have hsplit : Zforest β hβ =
      (∑ G : SimpleGraph Λ with G.IsAcyclic ∧ G.Reachable a b, forestWeight β hβ G) +
      ∑ G : SimpleGraph Λ, if G.IsAcyclic ∧ ¬G.Reachable a b then
        ∏ e ∈ E G, Sym2.lift ⟨β, hβ⟩ e else 0 := by
    rw [Zforest, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [forestWeight_eq]
    by_cases h1 : G.IsAcyclic <;> by_cases h2 : G.Reachable a b <;> simp [h1, h2]
  linarith

/-- **Corollary `cor:spin`, (`e:conn-spin`).** For all vertices `a, b`,
`P_β[a ↔ b] = -⟨z_a z_b⟩_β = -⟨u_a · u_b⟩_β = ⟨ξ_a η_b⟩_β = 1 - ⟨η_a ξ_a η_b ξ_b⟩_β`. -/
theorem cor_spin_conn {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (a b : Λ) :
    arborealProb β hβ (fun F => F.Reachable a b) = -avg β 0 (z a * z b) ∧
    -avg β 0 (z a * z b) = -avg β 0 (dot a b) ∧
    -avg β 0 (dot a b) = avg β 0 (ξ a * η b) ∧
    avg β 0 (ξ a * η b) = 1 - avg β 0 (η a * ξ a * η b * ξ b) := by
  have hZ := expect_one_ne_zero hβ hβ0
  -- Ward identities
  have w1 := expect_zz β hβ a b
  have w2 : expect β 0 (ξ b * η a) = expect β 0 (ξ a * η b) := by
    have := expect_zz β hβ b a
    rw [← mul_comm_of_even (inv'_z a) (z b), w1] at this
    linarith
  have hdot : expect β 0 (dot a b) = -expect β 0 (ξ a * η b) := by
    rw [dot, expect_sub, expect_sub, expect_neg, w1, w2]; ring
  have hQ : ∀ i : Λ, expect β 0 (ξ i * η i) = expect β 0 1 := by
    intro i
    have := expect_zz β hβ i i
    have hzz : z i * z i = 1 - (2 : ℝ) • (ξ i * η i) := by
      simp only [z]
      rw [sub_mul, one_mul, mul_sub, mul_one, ξη_sq, sub_zero, two_smul]; abel
    rw [hzz, expect_sub, expect_smul] at this
    linarith
  have hzz : z a * z b = 1 - ξ a * η a - ξ b * η b + ξ a * η a * (ξ b * η b) := by
    simp only [z]; noncomm_ring
  have hηξ : η a * ξ a * η b * ξ b = ξ a * η a * (ξ b * η b) := by
    rw [mul_assoc, η_anticomm_ξ b b, η_anticomm_ξ a a]; noncomm_ring
  have hP : arborealProb β hβ (fun F => F.Reachable a b) = -expect β 0 (dot a b) / expect β 0 1 := by
    rw [arborealProb, expect_one_eq_Z β hβ, ← sum_reach β hβ a b]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr_decidable _ _ _) fun _ _ => rfl
  have e4 : expect β 0 (ξ a * η b) = expect β 0 1 - expect β 0 (ξ a * η a * (ξ b * η b)) := by
    have := w1
    rw [hzz, expect_add, expect_sub, expect_sub, hQ, hQ] at this
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP, avg, w1, hdot]; ring
  · rw [avg, avg, w1, hdot]
  · rw [avg, avg, hdot]; ring
  · rw [avg, avg, hηξ, e4, sub_div, div_self hZ]

end

end H02

end
