module

public import ArborealDecay.Surgery

/-!
# Independence over a one-vertex union

For a one-vertex union `Λ = V₁ ∪ V₂` at `ρ`, `a ∈ V₁`, `b ∈ V₂`, the events `a ↮ ρ` and `b ↮ ρ`
are independent (`prob_not_reach_pair`), and `μ(a ↔ b) = (1 - r_a)(1 - r_b)` with
`r_a = μ(a ↮ ρ)` (`prob_reach_eq`).  Also `r_a > 0`.
-/

@[expose] public section

namespace ArborealDecay.Wiring

noncomputable section

open Finset Classical ArborealDecay.Surgery

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {V₁ V₂ : Finset Λ} {ρ : Λ}

theorem prob_not_reach_pair (hU : OneVertexUnion V₁ V₂ ρ) {w : Λ → Λ → ℝ}
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → w u v = 0) {a b : Λ} (ha : a ∈ V₁)
    (hb : b ∈ V₂) :
    H02.arborealProb w hw (fun F => ¬ F.Reachable a ρ ∧ ¬ F.Reachable b ρ) =
      H02.arborealProb w hw (fun F => ¬ F.Reachable a ρ) *
        H02.arborealProb w hw (fun F => ¬ F.Reachable b ρ) := by
  have t1 := H02.arborealProb_true (w := fun a b : V₁ => w a b) (fun a b => hw a b)
    (fun a b => hw0 a b)
  have t2 := H02.arborealProb_true (w := fun a b : V₂ => w a b) (fun a b => hw a b)
    (fun a b => hw0 a b)
  have e1 := arborealProb_union hU hw hcross
    (fun G => ¬ G.Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩) (fun G => ¬ G.Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩)
  have e2 := arborealProb_union hU hw hcross
    (fun G => ¬ G.Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩) (fun _ => True)
  have e3 := arborealProb_union hU hw hcross
    (fun _ => True) (fun G => ¬ G.Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩)
  rw [t2, mul_one] at e2
  rw [t1, one_mul] at e3
  have c1 := arborealProb_congr_noCross hw hcross (fun F => ¬ F.Reachable a ρ ∧ ¬ F.Reachable b ρ)
    (fun F => ¬ (resFin V₁ F).Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩ ∧
      ¬ (resFin V₂ F).Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩) (fun F _ hF => by
        rw [← reach_iff_res₁ hU hF ha, ← reach_iff_res₂ hU hF hb, SimpleGraph.reachable_comm (u := ρ)])
  have c2 := arborealProb_congr_noCross hw hcross (fun F => ¬ F.Reachable a ρ)
    (fun F => ¬ (resFin V₁ F).Reachable ⟨a, ha⟩ ⟨ρ, hU.mem₁⟩ ∧ True)
    (fun F _ hF => by rw [← reach_iff_res₁ hU hF ha]; simp)
  have c3 := arborealProb_congr_noCross hw hcross (fun F => ¬ F.Reachable b ρ)
    (fun F => True ∧ ¬ (resFin V₂ F).Reachable ⟨ρ, hU.mem₂⟩ ⟨b, hb⟩)
    (fun F _ hF => by
      rw [← reach_iff_res₂ hU hF hb, SimpleGraph.reachable_comm (u := ρ)]; simp)
  rw [c1, c2, c3, e1, e2, e3]

/-- Triple event: `a ↮ b` is implied. -/
theorem prob_not_reach_triple (hU : OneVertexUnion V₁ V₂ ρ) {w : Λ → Λ → ℝ}
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → w u v = 0) {a b : Λ} (ha : a ∈ V₁)
    (hb : b ∈ V₂) :
    H02.arborealProb w hw
        (fun F => ¬ F.Reachable a ρ ∧ ¬ F.Reachable b ρ ∧ ¬ F.Reachable a b) =
      H02.arborealProb w hw (fun F => ¬ F.Reachable a ρ) *
        H02.arborealProb w hw (fun F => ¬ F.Reachable b ρ) := by
  rw [← prob_not_reach_pair hU hw hw0 hcross ha hb]
  refine arborealProb_congr_noCross hw hcross _ _ fun F _ hF => ?_
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, fun h => h1 ?_⟩
    rw [reach_iff_res₁ hU hF ha]
    exact ((reach_iff_res hU hF ha hb).1 h).1

theorem prob_not (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (a b : Λ) :
    H02.arborealProb w hw (fun F => F.Reachable a b) =
      1 - H02.arborealProb w hw (fun F => ¬ F.Reachable a b) := by
  have h := Forest.arborealProb_or hw (P := fun F : SimpleGraph Λ => F.Reachable a b)
    (Q := fun F => ¬ F.Reachable a b) (fun F _ h1 h2 => h2 h1)
  have h2 := H02.arborealProb_true hw hw0
  have h3 : H02.arborealProb w hw (fun F => F.Reachable a b ∨ ¬ F.Reachable a b) =
      H02.arborealProb w hw (fun _ => True) :=
    Forest.arborealProb_congr hw (fun F _ => iff_true_intro (_root_.em _))
  rw [h3, h2] at h
  linarith

theorem prob_reach_eq (hU : OneVertexUnion V₁ V₂ ρ) {w : Λ → Λ → ℝ}
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → w u v = 0) {a b : Λ} (ha : a ∈ V₁)
    (hb : b ∈ V₂) :
    H02.arborealProb w hw (fun F => F.Reachable a b) =
      (1 - H02.arborealProb w hw (fun F => ¬ F.Reachable a ρ)) *
        (1 - H02.arborealProb w hw (fun F => ¬ F.Reachable b ρ)) := by
  have hsym : H02.arborealProb w hw (fun F => ¬ F.Reachable ρ b) =
      H02.arborealProb w hw (fun F => ¬ F.Reachable b ρ) :=
    Forest.arborealProb_congr hw (fun F _ => by rw [SimpleGraph.reachable_comm])
  rw [arborealProb_reachable_union hU hw hw0 hcross ha hb, prob_not w hw hw0 a ρ,
    prob_not w hw hw0 ρ b, hsym]

theorem prob_pos_of_bot (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (P : SimpleGraph Λ → Prop) (hP : P ⊥) : 0 < H02.arborealProb w hw P := by
  unfold H02.arborealProb
  refine div_pos ?_ (H02.Zforest_pos hw hw0)
  have h1 : H02.forestWeight w hw ⊥ = 1 := Finset.prod_eq_one fun e he => by simp at he
  have := Finset.single_le_sum (s := univ.filter fun F : SimpleGraph Λ => F.IsAcyclic ∧ P F)
    (fun F _ => H02.forestWeight_nonneg hw hw0 F) (a := ⊥) (by simp [hP])
  rw [h1] at this
  exact lt_of_lt_of_le one_pos this

end

end ArborealDecay.Wiring
