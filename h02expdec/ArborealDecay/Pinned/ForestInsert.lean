module

public import ArborealDecay.Pinned.TreeEval

/-!
# Forest expansion of `[ξ_a η_b]_{β,h}` with a field

For real symmetric `β` and real `h` on a finite `Λ` and `a, b ∈ Λ` (`a = b` allowed):
`[ξ_a η_b]^Λ_{β,h} = ∑_{F ∈ 𝓕(K_Λ) : a ↔_F b} β(F) ∏_{τ ≠ τ_F(a)} (1 + h(τ))`
(`expect_ξη_forest`; supplement `thm:H02-pinned`, Steps "forest expansion", "different trees"
and "same tree").

The form-level input is `int0_ξη_mono`:
`[ξ_a η_b X_F q_R]_0 = 1` iff `F` is a forest, `a ↔_F b`, no two vertices of `R` are
`F`-connected and no vertex of `R` is `F`-connected to `a`; otherwise `0`.
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-! ### Combinatorics of `Good` -/

theorem good_insert_iff (F : SimpleGraph Λ) {R : Finset Λ} {a : Λ} (ha : a ∉ R) :
    Good F (insert a R) ↔ Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x := by
  constructor
  · rintro ⟨hA, hR⟩
    refine ⟨⟨hA, fun x hx y hy => hR x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)⟩,
      fun x hx hax => ?_⟩
    exact ha (hR a (mem_insert_self a R) x (mem_insert_of_mem hx) hax ▸ hx)
  · rintro ⟨⟨hA, hR⟩, hx⟩
    refine ⟨hA, fun x hx' y hy' hxy => ?_⟩
    rw [mem_insert] at hx' hy'
    rcases hx' with rfl | hx' <;> rcases hy' with rfl | hy'
    · rfl
    · exact absurd hxy (hx y hy')
    · exact absurd hxy.symm (hx x hx')
    · exact hR x hx' y hy' hxy

theorem good_sup_edge_iff (F : SimpleGraph Λ) (R : Finset Λ) {a b : Λ} (hab : a ≠ b)
    (hF : ¬F.Adj a b) :
    Good (F ⊔ SimpleGraph.edge a b) R ↔ Good F R ∧ ¬F.Reachable a b ∧
      ((∀ x ∈ R, ¬F.Reachable a x) ∨ (∀ y ∈ R, ¬F.Reachable b y)) := by
  have hle : F ≤ F ⊔ SimpleGraph.edge a b := le_sup_left
  have hab' : (F ⊔ SimpleGraph.edge a b).Reachable a b :=
    SimpleGraph.Adj.reachable (by simp [SimpleGraph.edge_adj, hab])
  constructor
  · rintro ⟨hA, hR⟩
    obtain ⟨hFA, hnr⟩ := (acyclic_sup_edge_iff hab hF).1 hA
    refine ⟨⟨hFA, fun x hx y hy hxy => hR x hx y hy (hxy.mono hle)⟩, hnr, ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨⟨x, hx, hax⟩, ⟨y, hy, hby⟩⟩ := hc
    have hxy : x = y := hR x hx y hy
      (((hax.mono hle).symm.trans hab').trans (hby.mono hle))
    subst hxy
    exact hnr (hax.trans hby.symm)
  · rintro ⟨⟨hFA, hR⟩, hnr, hAB⟩
    refine ⟨(acyclic_sup_edge_iff hab hF).2 ⟨hFA, hnr⟩, fun x hx y hy hxy => ?_⟩
    rcases reachable_sup_edge hxy with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hR x hx y hy h1
    · rcases hAB with hA | hB
      · exact absurd h1.symm (hA x hx)
      · exact absurd h2 (hB y hy)
    · rcases hAB with hA | hB
      · exact absurd h2 (hA y hy)
      · exact absurd h1.symm (hB x hx)

/-! ### The form-level evaluation -/

theorem Jmap_cv_pc (i : Λ) : Jmap (cv (pc i i)) = cv (pc i i) := by
  rw [coe_pc, Jmap_ξη]

theorem Jmap_cv_prodPc (R : Finset Λ) :
    Jmap (cv (∏ i ∈ R, pc i i)) = cv (∏ i ∈ R, pc i i) := by
  induction R using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, map_mul, map_mul, Jmap_cv_pc, ih]

theorem Jmap_cv_mono (F : SimpleGraph Λ) (R : Finset Λ) :
    Jmap (cv (mono (E F) R)) = cv (mono (E F) R) := by
  rw [mono, map_mul, map_mul, Jmap_prodX, Jmap_cv_prodPc]

/-- `[q_a X_F q_R]_0 = 1_{Good F R, a ↮ R}`. -/
theorem int0_pc_mono (F : SimpleGraph Λ) (R : Finset Λ) (a : Λ) :
    int0 (cv (pc a a * mono (E F) R)) =
      if Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x then 1 else 0 := by
  by_cases ha : a ∈ R
  · have : pc a a * mono (E F) R = 0 := by
      rw [mono, prod_pc_eq ha, mul_left_comm, ← mul_assoc (pc a a), pc_sq, zero_mul, mul_zero]
    rw [this]
    have : ¬(Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x) := fun h =>
      h.2 a ha (SimpleGraph.Reachable.refl a)
    simp [int0, this]
  · have : pc a a * mono (E F) R = mono (E F) (insert a R) := by
      rw [mono, mono, Finset.prod_insert ha]; ring
    rw [this, int0_mono]
    exact if_congr (good_insert_iff F ha) rfl rfl

/-- `[q_a q_b X_F q_R]_0`. -/
theorem int0_pc_pc_mono (F : SimpleGraph Λ) (R : Finset Λ) (a b : Λ) :
    int0 (cv (pc a a * pc b b * mono (E F) R)) =
      if Good F R ∧ (∀ x ∈ R, ¬F.Reachable a x) ∧ (∀ y ∈ R, ¬F.Reachable b y) ∧
        ¬F.Reachable a b then 1 else 0 := by
  rw [mul_assoc]
  by_cases hb : b ∈ R
  · have h2 : ¬(Good F R ∧ (∀ x ∈ R, ¬F.Reachable a x) ∧ (∀ y ∈ R, ¬F.Reachable b y) ∧
        ¬F.Reachable a b) := fun h => h.2.2.1 b hb (SimpleGraph.Reachable.refl b)
    have : pc a a * (pc b b * mono (E F) R) = 0 := by
      rw [mono, prod_pc_eq hb, mul_left_comm (pc b b), ← mul_assoc (pc b b), pc_sq, zero_mul,
        mul_zero, mul_zero]
    rw [this]
    simp [int0, h2]
  · have : pc a a * (pc b b * mono (E F) R) = pc a a * mono (E F) (insert b R) := by
      rw [mono, mono, Finset.prod_insert hb]; ring
    rw [this, int0_pc_mono]
    refine if_congr ?_ rfl rfl
    rw [good_insert_iff F hb]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨hg, hbR⟩, hab', haR⟩
      exact ⟨hg, haR, hbR, hab'⟩
    · rintro ⟨hg, haR, hbR, hab'⟩
      exact ⟨⟨hg, hbR⟩, hab', haR⟩

/-- `[x_{ab} X_F q_R]_0` for `a ≠ b`. -/
theorem int0_Xc_mono (F : SimpleGraph Λ) (R : Finset Λ) {a b : Λ} (hab : a ≠ b) :
    int0 (cv (Xc a b * mono (E F) R)) =
      if Good F R ∧ ¬F.Reachable a b ∧
        ((∀ x ∈ R, ¬F.Reachable a x) ∨ (∀ y ∈ R, ¬F.Reachable b y)) then 1 else 0 := by
  by_cases hF : F.Adj a b
  · have hmem : s(a, b) ∈ E F := by simpa using hF
    have : Xc a b * mono (E F) R = 0 := by
      rw [mono, ← Finset.mul_prod_erase _ _ hmem, Xs_mk, ← mul_assoc, ← mul_assoc, Xc_sq,
        zero_mul, zero_mul]
    rw [this]
    simp [int0, hF.reachable]
  · have hnot : s(a, b) ∉ E F := by simpa using hF
    have : Xc a b * mono (E F) R = mono (E (F ⊔ SimpleGraph.edge a b)) R := by
      rw [mono, mono, E_sup_edge F hab, Finset.prod_insert hnot, Xs_mk, mul_assoc]
    rw [this, int0_mono]
    exact if_congr (good_sup_edge_iff F R hab hF) rfl rfl

/-- Propositional form of the per-forest indicator identity. -/
theorem indicator_aux (A g r pa pb : Prop) (hgA : g → A) (hr : r → (pa ↔ pb)) :
    (if g ∧ pa then (1 : ℝ) else 0) + (if g ∧ pb then 1 else 0) -
        (if g ∧ pa ∧ pb ∧ ¬r then 1 else 0) - (if g ∧ ¬r ∧ (pa ∨ pb) then 1 else 0) =
      2 * (if A ∧ r ∧ g ∧ pa then 1 else 0) := by
  by_cases hg : g
  · have hA := hgA hg
    by_cases hr' : r
    · have hab := hr hr'
      by_cases ha : pa
      · have hb := hab.1 ha
        simp [hg, hA, hr', ha, hb]; norm_num
      · have hb : ¬pb := fun h => ha (hab.2 h)
        simp [hg, hA, hr', ha, hb]
    · by_cases ha : pa <;> by_cases hb : pb <;> simp [hg, hA, hr', ha, hb]
  · simp [hg]

/-- The per-forest indicator identity behind `int0_ξη_mono`. -/
theorem indicator_identity_R (F : SimpleGraph Λ) (R : Finset Λ) (a b : Λ) :
    (if Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x then (1 : ℝ) else 0) +
        (if Good F R ∧ ∀ y ∈ R, ¬F.Reachable b y then 1 else 0) -
        (if Good F R ∧ (∀ x ∈ R, ¬F.Reachable a x) ∧ (∀ y ∈ R, ¬F.Reachable b y) ∧
          ¬F.Reachable a b then 1 else 0) -
        (if Good F R ∧ ¬F.Reachable a b ∧
          ((∀ x ∈ R, ¬F.Reachable a x) ∨ (∀ y ∈ R, ¬F.Reachable b y)) then 1 else 0) =
      2 * (if F.IsAcyclic ∧ F.Reachable a b ∧ Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x then 1
        else 0) := by
  convert indicator_aux F.IsAcyclic (Good F R) (F.Reachable a b) (∀ x ∈ R, ¬F.Reachable a x)
    (∀ y ∈ R, ¬F.Reachable b y) (fun hg => hg.1) fun hr =>
    ⟨fun h y hy hby => h y hy (hr.trans hby), fun h x hx hax => h x hx (hr.symm.trans hax)⟩

/-- **Tree-level evaluations with insertions** (form level):
`[ξ_a η_b X_F q_R]_0 = 1` iff `F` is a forest, `a ↔_F b`, no two vertices of `R` are connected
and no vertex of `R` is connected to `a`; otherwise `0`. (Supplement `prop:tree-eval` (ii), (iii),
(v) combined with the parity/factorization Steps of `thm:H02-pinned`.) -/
theorem int0_ξη_mono (F : SimpleGraph Λ) (R : Finset Λ) (a b : Λ) :
    int0 (ξ a * η b * cv (mono (E F) R)) =
      if F.IsAcyclic ∧ F.Reachable a b ∧ Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x then 1 else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [← coe_pc, ← map_mul, int0_pc_mono]
    refine if_congr ?_ rfl rfl
    exact ⟨fun h => ⟨h.1.1, SimpleGraph.Reachable.refl a, h⟩, fun h => h.2.2⟩
  have hJ : int0 (ξ b * η a * cv (mono (E F) R)) = int0 (ξ a * η b * cv (mono (E F) R)) := by
    rw [← int0_Jmap, map_mul, Jmap_ξη, Jmap_cv_mono]
  have hsum : ξ a * η b * cv (mono (E F) R) + ξ b * η a * cv (mono (E F) R) =
      cv (pc a a * mono (E F) R) + cv (pc b b * mono (E F) R) -
        cv (pc a a * pc b b * mono (E F) R) - cv (Xc a b * mono (E F) R) := by
    simp only [map_mul, coe_pc, cv_Xc]
    noncomm_ring
  have h2 := congrArg int0 hsum
  simp only [int0_eq_L, map_add, map_sub] at h2
  simp only [← int0_eq_L] at h2
  rw [hJ, int0_pc_mono, int0_pc_mono, int0_pc_pc_mono F R a b, int0_Xc_mono F R hab,
    indicator_identity_R] at h2
  linarith

/-! ### Summing over `R` and over forests -/

/-- The expansion `[Y]_{β,h} = ∑_{t, R} β^t h^R [Y X_t q_R]_0`. -/
theorem expect_eq_sum_mono (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ)
    (Y : Grassmann Λ) :
    expect β h Y = ∑ G : SimpleGraph Λ, ∑ R ∈ (univ : Finset Λ).powerset,
      ((∏ e ∈ E G, Sym2.lift ⟨β, hβ⟩ e) * ∏ i ∈ R, h i) * int0 (Y * cv (mono (E G) R)) := by
  have hW := isNilpotent_W β hβ h
  rw [H02.expect, action_eq β hβ h, neg_neg, ← IsNilpotent.map_exp hW, exp_W, map_sum,
    Finset.mul_sum, int0_sum]
  rw [← sum_E_powerset (fun t => ∑ R ∈ (univ : Finset Λ).powerset,
    ((∏ e ∈ t, Sym2.lift ⟨β, hβ⟩ e) * ∏ i ∈ R, h i) * int0 (Y * cv (mono t R)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_sum, Finset.mul_sum, int0_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [map_smul, mul_smul_comm, int0_smul]

/-- `∑_R h^R 1_{Good F R, a ↮ R} = ∏_{τ ≠ τ_F(a)} (1 + h(τ))` for a forest `F`. -/
theorem sum_good_avoid (F : SimpleGraph Λ) (hF : F.IsAcyclic) (h : Λ → ℝ) (a : Λ) :
    ∑ R ∈ (univ : Finset Λ).powerset,
        (if Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x then ∏ i ∈ R, h i else 0) =
      ∏ T : F.ConnectedComponent with T ≠ F.connectedComponentMk a,
        (1 + ∑ i with F.connectedComponentMk i = T, h i) := by
  set h' : Λ → ℝ := fun i => if F.Reachable a i then 0 else h i
  have hterm : ∀ R : Finset Λ,
      (if Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x then ∏ i ∈ R, h i else 0) =
        if Good F R then ∏ i ∈ R, h' i else 0 := by
    intro R
    by_cases hg : Good F R
    · by_cases hx : ∀ x ∈ R, ¬F.Reachable a x
      · rw [ite_eq_left ⟨hg, hx⟩, ite_eq_left hg]
        exact Finset.prod_congr rfl fun i hi => by simp [h', hx i hi]
      · push Not at hx
        obtain ⟨x, hxR, hax⟩ := hx
        rw [ite_eq_right (fun h => h.2 x hxR hax), ite_eq_left hg]
        exact (Finset.prod_eq_zero hxR (by simp [h', hax])).symm
    · rw [ite_eq_right (fun h => hg h.1), ite_eq_right hg]
  rw [Finset.sum_congr rfl fun R _ => hterm R, sum_good F h', ite_eq_left hF]
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun T => T ≠ F.connectedComponentMk a)]
  have hone : ∏ T : F.ConnectedComponent with ¬T ≠ F.connectedComponentMk a,
      (1 + ∑ i with F.connectedComponentMk i = T, h' i) = 1 := by
    refine Finset.prod_eq_one fun T hT => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hT
    subst hT
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have : F.Reachable a i := SimpleGraph.ConnectedComponent.exact hi.symm
    simp [h', this]
  rw [hone, mul_one]
  refine Finset.prod_congr rfl fun T hT => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have : ¬F.Reachable a i := fun hai => hT (hi ▸ (SimpleGraph.ConnectedComponent.eq.2 hai).symm)
  simp [h', this]

/-- **Forest expansion of `[ξ_a η_b]_{β,h}`** (supplement `thm:H02-pinned`, Steps
"forest expansion", "different trees", "same tree"): for real symmetric `β`, real `h` and
`a, b ∈ Λ` (`a = b` allowed),
`[ξ_a η_b]^Λ_{β,h} = ∑_{F ∈ 𝓕(K_Λ) : a ↔_F b} β(F) ∏_{τ ≠ τ_F(a)} (1 + ∑_{i ∈ τ} h_i)`. -/
theorem expect_ξη_forest (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) (a b : Λ) :
    expect β h (ξ a * η b) = ∑ F : SimpleGraph Λ with F.IsAcyclic ∧ F.Reachable a b,
      (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        ∏ T : F.ConnectedComponent with T ≠ F.connectedComponentMk a,
          (1 + ∑ i with F.connectedComponentMk i = T, h i) := by
  rw [expect_eq_sum_mono β hβ h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp_rw [int0_ξη_mono, ← E_eq F]
  by_cases hF : F.IsAcyclic ∧ F.Reachable a b
  · rw [ite_eq_left hF, ← sum_good_avoid F hF.1 h a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ => ?_
    by_cases hR : Good F R ∧ ∀ x ∈ R, ¬F.Reachable a x
    · rw [ite_eq_left ⟨hF.1, hF.2, hR⟩, ite_eq_left hR]; ring
    · rw [ite_eq_right (fun h => hR h.2.2), ite_eq_right hR]; ring
  · rw [ite_eq_right hF]
    refine Finset.sum_eq_zero fun R _ => ?_
    rw [ite_eq_right (fun h => hF ⟨h.1, h.2.1⟩), mul_zero]

end

end ArborealDecay.Pinned

end
