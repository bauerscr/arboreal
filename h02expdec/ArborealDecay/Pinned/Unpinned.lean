module

public import ArborealDecay.H02

/-!
# The unpinned model with the pin insertion `ξ_r η_r`

Zero-field `ℍ^{0|2}` computations on an arbitrary finite vertex type `V` (real symmetric weights,
no sign or connectivity hypothesis):

* `expect_pin`:  `[ξ_r η_r]^V_{w,0} = ∑_{F ∈ 𝓕(K_V)} w(F) = Z_Γ`;
* `expect_pin_ξη`: for `a, b ≠ r` (including `a = b`),
  `[ξ_r η_r ξ_a η_b]^V_{w,0} = ∑_{F ∈ 𝓕(K_V) : a ↔ b, a ↮ r} w(F)`.

These are the zero-field (unpinned) forms of supplement `thm:H02-pinned` (i), (ii); see
`lem:pinning` (`ArborealDecay.Pinned.Pinning`) for the passage to the pinned model.

Proof route.  Instead of the tree-level evaluations of supplement `prop:tree-eval`, we use the
`ξ ↔ η` symmetry `J` (`expect_Jmap`) and the identity
`ξ_a η_b + ξ_b η_a = q_a + q_b - q_a q_b - x_{ab}` (BCHS (2.3)), which reduces the insertion
`ξ_a η_b` (for `a ≠ b`) to central forms `q_R X_S`, whose integrals are the indicator that `S`
is a forest in which no two vertices of `R` are connected (`H02.int0_mono`).
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `∑_{F : P F} w(F)` written as a sum over all graphs with an indicator. -/
theorem fsum_eq_sum_ite (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (P : SimpleGraph V → Prop) :
    fsum w hw P = ∑ F : SimpleGraph V, if P F then forestWeight w hw F else 0 := by
  rw [fsum, fset, Finset.sum_filter]

theorem good_singleton_iff (G : SimpleGraph V) (r : V) : Good G {r} ↔ G.IsAcyclic := by
  simp [Good]

theorem good_pair_iff (G : SimpleGraph V) {r a : V} (h : r ≠ a) :
    Good G {r, a} ↔ G.IsAcyclic ∧ ¬G.Reachable r a := by
  simp only [Good, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hG, hR⟩
    exact ⟨hG, fun hra => h (hR r (Or.inl rfl) a (Or.inr rfl) hra)⟩
  · rintro ⟨hG, hR⟩
    refine ⟨hG, ?_⟩
    rintro x (rfl | rfl) y (rfl | rfl) hxy
    · rfl
    · exact absurd hxy hR
    · exact absurd hxy.symm hR
    · rfl

theorem good_triple_iff (G : SimpleGraph V) {r a b : V} (hra : r ≠ a) (hrb : r ≠ b)
    (hab : a ≠ b) :
    Good G {r, a, b} ↔
      G.IsAcyclic ∧ ¬G.Reachable r a ∧ ¬G.Reachable r b ∧ ¬G.Reachable a b := by
  simp only [Good, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hG, hR⟩
    exact ⟨hG, fun h => hra (hR _ (Or.inl rfl) _ (Or.inr (Or.inl rfl)) h),
      fun h => hrb (hR _ (Or.inl rfl) _ (Or.inr (Or.inr rfl)) h),
      fun h => hab (hR _ (Or.inr (Or.inl rfl)) _ (Or.inr (Or.inr rfl)) h)⟩
  · rintro ⟨hG, h1, h2, h3⟩
    refine ⟨hG, ?_⟩
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) hxy
    all_goals first
      | rfl
      | exact absurd hxy h1 | exact absurd hxy.symm h1
      | exact absurd hxy h2 | exact absurd hxy.symm h2
      | exact absurd hxy h3 | exact absurd hxy.symm h3

/-- `[q_R X_G]_0 = 1` if `G` is a forest in which no two vertices of `R` are connected, else
`0` (`H02.int0_mono`, with the factors in the other order). -/
theorem int0_prodPc_mul_prodX (G : SimpleGraph V) (R : Finset V) :
    int0 (cv ((∏ i ∈ R, pc i i) * ∏ e ∈ E G, Xs e)) = if Good G R then 1 else 0 := by
  rw [mul_comm]; exact int0_mono G R

/-- `[q_r x_{ab} X_G]_0 = 1_{G forest, a ↮_G b}` for `a ≠ b`. -/
theorem int0_pc_Xc_prodX (G : SimpleGraph V) (r : V) {a b : V} (hab : a ≠ b) :
    int0 (cv (pc r r * Xc a b * ∏ e ∈ E G, Xs e)) =
      if G.IsAcyclic ∧ ¬G.Reachable a b then 1 else 0 := by
  by_cases hG : G.Adj a b
  · have hmem : s(a, b) ∈ E G := by simpa using hG
    have : pc r r * Xc a b * ∏ e ∈ E G, Xs e = 0 := by
      rw [← Finset.mul_prod_erase _ _ hmem, Xs_mk, mul_assoc, ← mul_assoc (Xc a b), Xc_sq,
        zero_mul, mul_zero]
    rw [this]
    simp [int0, hG.reachable]
  · have hnot : s(a, b) ∉ E G := by simpa using hG
    have h1 : pc r r * Xc a b * ∏ e ∈ E G, Xs e =
        (∏ i ∈ ({r} : Finset V), pc i i) * ∏ e ∈ E (G ⊔ SimpleGraph.edge a b), Xs e := by
      rw [E_sup_edge G hab, Finset.prod_insert hnot, Finset.prod_singleton, Xs_mk, mul_assoc]
    rw [h1, int0_prodPc_mul_prodX]
    exact if_congr ((good_singleton_iff _ r).trans (acyclic_sup_edge_iff hab hG)) rfl rfl

/-- `ξ_r η_r` written in the centre. -/
theorem ξη_eq_cv (r : V) : ξ r * η r = cv (pc r r) := rfl

/-- **Denominator, unpinned form**: `[ξ_r η_r]^V_{w,0} = Z_Γ` (real symmetric weights). -/
theorem expect_pin (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) (r : V) :
    expect w 0 (ξ r * η r) = Zforest w hw := by
  rw [ξη_eq_cv, expect_cv w hw, Zforest, Finset.sum_filter]
  refine Finset.sum_congr rfl fun G _ => ?_
  have := int0_prodPc_mul_prodX G {r}
  rw [Finset.prod_singleton, good_singleton_iff] at this
  rw [this, forestWeight_eq]
  split_ifs <;> simp

/-- The pin insertion with `q_a`, `a ≠ r`. -/
theorem expect_pin_q (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) {r a : V} (har : a ≠ r) :
    expect w 0 (ξ r * η r * (ξ a * η a)) =
      fsum w hw (fun F => F.IsAcyclic ∧ ¬F.Reachable a r) := by
  rw [ξη_eq_cv, ξη_eq_cv, ← map_mul, expect_cv w hw, fsum_eq_sum_ite]
  refine Finset.sum_congr rfl fun G _ => ?_
  have := int0_prodPc_mul_prodX G {r, a}
  rw [Finset.prod_pair har.symm, good_pair_iff G har.symm] at this
  rw [this, forestWeight_eq]
  have hc : (¬G.Reachable r a) ↔ ¬G.Reachable a r := ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  by_cases h1 : G.IsAcyclic <;> by_cases h2 : G.Reachable a r <;> simp [h1, h2, hc]

/-- The per-graph indicator identity
`[a ↮ r] + [b ↮ r] - [r, a, b pairwise ↮] - [a ↮ b] = 2 [a ↔ b, a ↮ r]` (on forests). -/
theorem indicator_identity (G : SimpleGraph V) {r a b : V} (c : ℝ) :
    (if G.IsAcyclic ∧ ¬G.Reachable r a then c else 0) +
        (if G.IsAcyclic ∧ ¬G.Reachable r b then c else 0) -
        (if G.IsAcyclic ∧ ¬G.Reachable r a ∧ ¬G.Reachable r b ∧ ¬G.Reachable a b then c
          else 0) -
        (if G.IsAcyclic ∧ ¬G.Reachable a b then c else 0) =
      2 * (if G.IsAcyclic ∧ G.Reachable a b ∧ ¬G.Reachable a r then c else 0) := by
  by_cases hA : G.IsAcyclic
  swap
  · simp [hA]
  by_cases hab : G.Reachable a b
  · have hb : G.Reachable r a ↔ G.Reachable r b :=
      ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩
    have hc : G.Reachable a r ↔ G.Reachable r a := ⟨fun h => h.symm, fun h => h.symm⟩
    by_cases hra : G.Reachable r a
    · simp [hA, hab, hra, hb.1 hra, hc]
    · have hrb : ¬G.Reachable r b := fun h => hra (hb.2 h)
      simp [hA, hab, hra, hrb, hc]; ring
  · by_cases hra : G.Reachable r a <;> by_cases hrb : G.Reachable r b
    · exact absurd ((hra.symm).trans hrb) hab
    · simp [hA, hab, hra, hrb]
    · simp [hA, hab, hra, hrb]
    · simp [hA, hab, hra, hrb]

/-- **Numerator, unpinned form**: for `a, b ≠ r` (including `a = b`),
`[ξ_r η_r ξ_a η_b]^V_{w,0} = ∑_{F ∈ 𝓕(K_V) : a ↔ b, a ↮ r} w(F)` (real symmetric weights). -/
theorem expect_pin_ξη (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) {r a b : V}
    (har : a ≠ r) (hbr : b ≠ r) :
    expect w 0 (ξ r * η r * (ξ a * η b)) =
      fsum w hw (fun F => F.IsAcyclic ∧ F.Reachable a b ∧ ¬F.Reachable a r) := by
  by_cases hab : a = b
  · subst hab
    rw [expect_pin_q w hw har]
    congr 1
    funext F
    simp
  -- the `ξ ↔ η` symmetry
  have hJ : expect w 0 (ξ r * η r * (ξ b * η a)) = expect w 0 (ξ r * η r * (ξ a * η b)) := by
    rw [← expect_Jmap w hw 0, map_mul, Jmap_ξη, Jmap_ξη]
  -- `ξ_a η_b + ξ_b η_a = q_a + q_b - q_a q_b - x_{ab}`
  have hsum : ξ r * η r * (ξ a * η b) + ξ r * η r * (ξ b * η a) =
      cv ((∏ i ∈ ({r, a} : Finset V), pc i i) + (∏ i ∈ ({r, b} : Finset V), pc i i) -
        (∏ i ∈ ({r, a, b} : Finset V), pc i i) - pc r r * Xc a b) := by
    have hX := Xc_eq a b
    have hra : r ∉ ({a, b} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm har, Ne.symm hbr⟩
    rw [Finset.prod_pair (Ne.symm har), Finset.prod_pair (Ne.symm hbr), Finset.prod_insert hra,
      Finset.prod_pair hab, hX]
    simp only [map_add, map_sub, map_mul, coe_pc]
    noncomm_ring
  have h2 : 2 * expect w 0 (ξ r * η r * (ξ a * η b)) = expect w 0 (cv
      ((∏ i ∈ ({r, a} : Finset V), pc i i) + (∏ i ∈ ({r, b} : Finset V), pc i i) -
        (∏ i ∈ ({r, a, b} : Finset V), pc i i) - pc r r * Xc a b)) := by
    rw [← hsum, expect_add, hJ]; ring
  rw [expect_cv w hw] at h2
  have hterm : ∀ G : SimpleGraph V, (∏ e ∈ E G, Sym2.lift ⟨w, hw⟩ e) *
      int0 (cv (((∏ i ∈ ({r, a} : Finset V), pc i i) + (∏ i ∈ ({r, b} : Finset V), pc i i) -
        (∏ i ∈ ({r, a, b} : Finset V), pc i i) - pc r r * Xc a b) * ∏ e ∈ E G, Xs e)) =
      2 * (if G.IsAcyclic ∧ G.Reachable a b ∧ ¬G.Reachable a r then forestWeight w hw G
        else 0) := by
    intro G
    rw [← indicator_identity G (r := r)]
    simp only [add_mul, sub_mul, map_add, map_sub, int0_eq_L, map_add, map_sub]
    simp only [← int0_eq_L]
    rw [int0_prodPc_mul_prodX, int0_prodPc_mul_prodX, int0_prodPc_mul_prodX,
      int0_pc_Xc_prodX G r hab, good_pair_iff G (Ne.symm har), good_pair_iff G (Ne.symm hbr),
      good_triple_iff G (Ne.symm har) (Ne.symm hbr) hab, ← forestWeight_eq]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun G _ => hterm G, ← Finset.mul_sum] at h2
  rw [fsum_eq_sum_ite]
  have h3 := (mul_right_inj' (two_ne_zero (α := ℝ))).1 h2
  rw [h3]
  exact Finset.sum_congr rfl fun F _ => by split_ifs <;> rfl

end

end ArborealDecay.Pinned

end
