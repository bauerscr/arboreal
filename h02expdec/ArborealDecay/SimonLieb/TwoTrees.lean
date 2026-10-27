module

public import ArborealDecay.SimonLieb.IncidentNC

/-!
# Two rooted trees (`lem:two-trees`)

If `A` and `B` are edge-disjoint graphs all of whose edges lie in the connected component of a
common vertex `r` (e.g. two trees sharing the vertex `r`), then
`μ(A ∪ B ⊆ F) ≤ μ(A ⊆ F) μ(B ⊆ F)` (conditional on `hstab`, via `incident_NC_of_stable`).

Proof: both graphs are grown from `r` by adding edges at vertices already reached (`Grown`).
For `B = B' + qj` and `A` grown from `r`, `μ(B' ∪ A ∪ qj) μ(B') ≤ μ(B' ∪ A) μ(B' ∪ qj)`
(`inner_of_stable`, induction on `A` using conditional incident-edge negative correlation:
after conditioning on `B'` and the earlier edges of `A`, the next edge of `A` and `qj` are
incident to the contracted root).  Then induct on `B`.  No acyclicity of `A ∪ B` is needed
(otherwise the left side is `0`).
-/

@[expose] public section

namespace ArborealDecay.SimonLieb

universe u

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical SimpleGraph

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- `μ(G ⊆ F)`. -/
def probLe (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (G : SimpleGraph Λ) : ℝ :=
  H02.arborealProb β hβ (fun F => G ≤ F)

/-- Graphs grown from `r` by successively adding edges at vertices already reached from `r`. -/
inductive Grown (r : Λ) : SimpleGraph Λ → Prop
  | bot : Grown r ⊥
  | step {G : SimpleGraph Λ} {p : Λ} (i : Λ) : Grown r G → G.Reachable r p →
      Grown r (G ⊔ edge p i)

theorem walk_cross {G H : SimpleGraph Λ} {r : Λ} {a b : Λ} (w : G.Walk a b)
    (h : H.Reachable r a) :
    H.Reachable r b ∨ ∃ x y, G.Adj x y ∧ ¬ H.Adj x y ∧ H.Reachable r x := by
  induction w with
  | nil => exact Or.inl h
  | @cons u v _ hadj _ ih =>
    by_cases hH : H.Adj u v
    · exact ih (h.trans hH.reachable)
    · exact Or.inr ⟨u, v, hadj, hH, h⟩

/-- A graph all of whose edges lie in the component of `r` is grown from `r`. -/
theorem grown_of_reachable {r : Λ} (G : SimpleGraph Λ)
    (hG : ∀ u v, G.Adj u v → G.Reachable r u) : Grown r G := by
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    (univ.filter fun H : SimpleGraph Λ => H ≤ G ∧ Grown r H) (fun H => H.edgeFinset.card)
    ⟨⊥, by simp [Grown.bot]⟩
  simp only [mem_filter, mem_univ, true_and] at hH hmax
  suffices hHG : H = G by rw [← hHG]; exact hH.2
  by_contra hne
  have hex : ∃ u v, G.Adj u v ∧ ¬ H.Adj u v := by
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hH.1 fun u v h => hc u v h)
  obtain ⟨u, v, huv, hnuv⟩ := hex
  obtain ⟨x, y, hxy, hnxy, hrx⟩ : ∃ x y, G.Adj x y ∧ ¬ H.Adj x y ∧ H.Reachable r x := by
    obtain ⟨w⟩ := hG u v huv
    rcases walk_cross (H := H) w (Reachable.refl r) with h | h
    · exact ⟨u, v, huv, hnuv, h⟩
    · exact h
  have hlt : H < H ⊔ edge x y := by
    refine lt_of_le_of_ne le_sup_left fun h => hnxy ?_
    rw [h]
    exact Or.inr (by simp [edge_adj, hxy.ne])
  have h1 := hmax (H ⊔ edge x y) ⟨sup_le hH.1 ((edge_le_iff G).2 (Or.inr hxy)), Grown.step y hH.2 hrx⟩
  have h2 := Finset.card_lt_card (edgeFinset_ssubset_edgeFinset.2 hlt)
  have h3 : ¬ ((fun H : SimpleGraph Λ => H.edgeFinset.card) (H ⊔ edge x y) ≤
      (fun H : SimpleGraph Λ => H.edgeFinset.card) H) := by
    dsimp only
    convert not_le.2 h2 using 3
    ext e; simp
  exact h3 h1

variable {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)

include hβ0 in
theorem probLe_nonneg (G : SimpleGraph Λ) : 0 ≤ probLe β hβ G :=
  H02.arborealProb_nonneg hβ hβ0 _

include hβ0 in
theorem probLe_anti {G G' : SimpleGraph Λ} (h : G ≤ G') : probLe β hβ G' ≤ probLe β hβ G :=
  Forest.arborealProb_mono hβ hβ0 fun _ _ hF => h.trans hF

include hβ0 in
theorem probLe_bot : probLe β hβ ⊥ = 1 := by
  unfold probLe
  rw [← H02.arborealProb_true hβ hβ0]
  exact Forest.arborealProb_congr hβ fun F _ => ⟨fun _ => trivial, fun _ => bot_le⟩

theorem probLe_eq_zero_of_not_acyclic {G : SimpleGraph Λ} (hG : ¬ G.IsAcyclic) :
    probLe β hβ G = 0 :=
  arborealProb_eq_zero_of hβ fun _ hF hGF => hG (hF.anti hGF)

include hβ0

/-- Conditional incident-edge negative correlation for graphs (conditional on `hstab`). -/
theorem NC_graph_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    (C : SimpleGraph Λ) {p i q j : Λ} (hpq : C.Reachable p q) (hef : s(p, i) ≠ s(q, j)) :
    probLe β hβ (C ⊔ edge p i ⊔ edge q j) * probLe β hβ C ≤
      probLe β hβ (C ⊔ edge p i) * probLe β hβ (C ⊔ edge q j) := by
  by_cases hC : C.IsAcyclic
  · by_cases hp : p = i
    · subst hp
      simp only [edge_self_eq_bot, sup_bot_eq]
      exact le_of_eq (mul_comm _ _)
    by_cases hq : q = j
    · subst hq
      simp only [edge_self_eq_bot, sup_bot_eq]
      exact le_rfl
    have key := incident_NC_of_stable hstab hβ hβ0 C hC p i q j hpq hef
    have e1 : (fun F : SimpleGraph Λ => C ⊔ edge p i ⊔ edge q j ≤ F) =
        fun F => C ≤ F ∧ s(p, i) ∈ F.edgeSet ∧ s(q, j) ∈ F.edgeSet := by
      funext F; simp [sup_le_iff, hp, hq, and_assoc]
    have e2 : (fun F : SimpleGraph Λ => C ⊔ edge p i ≤ F) =
        fun F => C ≤ F ∧ s(p, i) ∈ F.edgeSet := by
      funext F; simp [sup_le_iff, hp]
    have e3 : (fun F : SimpleGraph Λ => C ⊔ edge q j ≤ F) =
        fun F => C ≤ F ∧ s(q, j) ∈ F.edgeSet := by
      funext F; simp [sup_le_iff, hq]
    unfold probLe
    rw [e1, e2, e3]
    exact key
  · rw [probLe_eq_zero_of_not_acyclic hβ hC, mul_zero]
    exact mul_nonneg (probLe_nonneg hβ hβ0 _) (probLe_nonneg hβ hβ0 _)

/-- The inner induction (on `A`) of `lem:two-trees`. -/
theorem inner_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    {r : Λ} {A : SimpleGraph Λ} (hA : Grown r A) :
    ∀ (C : SimpleGraph Λ) (q j : Λ), C.Reachable r q → s(q, j) ∉ A.edgeSet →
      probLe β hβ (C ⊔ A ⊔ edge q j) * probLe β hβ C ≤
        probLe β hβ (C ⊔ A) * probLe β hβ (C ⊔ edge q j) := by
  induction hA with
  | bot =>
    intro C q j _ _
    simp only [sup_bot_eq]
    exact le_of_eq (mul_comm _ _)
  | @step G p i hG hr ih =>
    intro C q j hCq hqj
    by_cases hpi : p = i
    · subst hpi
      simp only [edge_self_eq_bot, sup_bot_eq] at hqj ⊢
      exact ih C q j hCq hqj
    have hqjG : s(q, j) ∉ G.edgeSet := fun h => hqj (by simp [edgeSet_sup, h])
    have hne : s(p, i) ≠ s(q, j) := by
      intro h
      apply hqj
      rw [← h, edgeSet_sup]
      exact Or.inr (by simp [hpi])
    have hreach : (C ⊔ G).Reachable p q :=
      (hr.mono le_sup_right).symm.trans (hCq.mono le_sup_left)
    have hNC := NC_graph_of_stable hβ hβ0 hstab (C ⊔ G) hreach hne
    have hih := ih C q j hCq hqjG
    rw [← sup_assoc]
    set X := probLe β hβ (C ⊔ G ⊔ edge p i ⊔ edge q j)
    set Y := probLe β hβ (C ⊔ G)
    set U := probLe β hβ (C ⊔ G ⊔ edge p i)
    set V := probLe β hβ (C ⊔ G ⊔ edge q j)
    set W := probLe β hβ C
    set K := probLe β hβ (C ⊔ edge q j)
    have hXY : X ≤ Y := probLe_anti hβ hβ0 (le_sup_left.trans le_sup_left)
    have hX0 : 0 ≤ X := probLe_nonneg hβ hβ0 _
    have hU0 : 0 ≤ U := probLe_nonneg hβ hβ0 _
    have hW0 : 0 ≤ W := probLe_nonneg hβ hβ0 _
    have hK0 : 0 ≤ K := probLe_nonneg hβ hβ0 _
    rcases (probLe_nonneg hβ hβ0 (C ⊔ G)).lt_or_eq with hY | hY
    · refine le_of_mul_le_mul_right ?_ hY
      calc X * W * Y = X * Y * W := by ring
        _ ≤ U * V * W := mul_le_mul_of_nonneg_right hNC hW0
        _ = U * (V * W) := by ring
        _ ≤ U * (Y * K) := mul_le_mul_of_nonneg_left hih hU0
        _ = U * K * Y := by ring
    · have : X = 0 := le_antisymm (hXY.trans hY.symm.le) hX0
      rw [this, zero_mul]
      exact mul_nonneg hU0 hK0

/-- `lem:two-trees` for grown graphs (conditional on `hstab`). -/
theorem two_trees_grown_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    {r : Λ} {B : SimpleGraph Λ} (hB : Grown r B) :
    ∀ A : SimpleGraph Λ, Grown r A → (∀ e ∈ B.edgeSet, e ∉ A.edgeSet) →
      probLe β hβ (A ⊔ B) ≤ probLe β hβ A * probLe β hβ B := by
  induction hB with
  | bot =>
    intro A _ _
    rw [sup_bot_eq, probLe_bot hβ hβ0, mul_one]
  | @step G q j hG hr ih =>
    intro A hA hdisj
    by_cases hqj : q = j
    · subst hqj
      simp only [edge_self_eq_bot, sup_bot_eq] at hdisj ⊢
      exact ih A hA hdisj
    have hdisj' : ∀ e ∈ G.edgeSet, e ∉ A.edgeSet :=
      fun e he => hdisj e (by rw [edgeSet_sup]; exact Or.inl he)
    have hqjA : s(q, j) ∉ A.edgeSet :=
      hdisj _ (by rw [edgeSet_sup]; exact Or.inr (by simp [hqj]))
    have hin := inner_of_stable hβ hβ0 hstab hA G q j hr hqjA
    have hih := ih A hA hdisj'
    have e1 : A ⊔ (G ⊔ edge q j) = G ⊔ A ⊔ edge q j := by
      rw [← sup_assoc, sup_comm A G]
    rw [e1]
    rw [sup_comm A G] at hih
    set X := probLe β hβ (G ⊔ A ⊔ edge q j)
    set Y := probLe β hβ G
    set U := probLe β hβ (G ⊔ A)
    set V := probLe β hβ (G ⊔ edge q j)
    set P := probLe β hβ A
    have hXY : X ≤ Y := probLe_anti hβ hβ0 (le_sup_left.trans le_sup_left)
    have hX0 : 0 ≤ X := probLe_nonneg hβ hβ0 _
    have hV0 : 0 ≤ V := probLe_nonneg hβ hβ0 _
    have hP0 : 0 ≤ P := probLe_nonneg hβ hβ0 _
    rcases (probLe_nonneg hβ hβ0 G).lt_or_eq with hY | hY
    · refine le_of_mul_le_mul_right ?_ hY
      calc X * Y ≤ U * V := hin
        _ ≤ P * Y * V := mul_le_mul_of_nonneg_right hih hV0
        _ = P * V * Y := by ring
    · have : X = 0 := le_antisymm (hXY.trans hY.symm.le) hX0
      rw [this]
      exact mul_nonneg hP0 hV0

/-- **Two rooted trees** (`lem:two-trees`; conditional on `hstab`).  If all edges of `A` and of
`B` lie in the connected component of `r` (in `A`, resp. `B`), and `A`, `B` are edge-disjoint,
then `μ(A ∪ B ⊆ F) ≤ μ(A ⊆ F) μ(B ⊆ F)`.  This applies in particular to two edge-disjoint trees
sharing the vertex `r`. -/
theorem two_trees_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    (r : Λ) (A B : SimpleGraph Λ) (hA : ∀ u v, A.Adj u v → A.Reachable r u)
    (hB : ∀ u v, B.Adj u v → B.Reachable r u) (hAB : Disjoint A.edgeSet B.edgeSet) :
    H02.arborealProb β hβ (fun F => A ⊔ B ≤ F) ≤
      H02.arborealProb β hβ (fun F => A ≤ F) * H02.arborealProb β hβ (fun F => B ≤ F) :=
  two_trees_grown_of_stable hβ hβ0 hstab (grown_of_reachable B hB) A (grown_of_reachable A hA)
    fun _ he hA' => Set.disjoint_left.1 hAB hA' he

end

end ArborealDecay.SimonLieb
