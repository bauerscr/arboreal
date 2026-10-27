module

public import ArborealDecay.SimonLieb.Uncond

/-!
# Incident-edge negative correlation (`prop:incident-NC`), conditional form

For an acyclic `A`, vertices `p, q` in one tree of `A`, and distinct edges `pi ≠ qj`:
`μ(A ⊆ F, pi ∈ F, qj ∈ F) μ(A ⊆ F) ≤ μ(A ⊆ F, pi ∈ F) μ(A ⊆ F, qj ∈ F)`
(conditional on `hstab`, the real stability of forest polynomials).

The proof contracts `A` (`Surgery.condProb_adj_components`, `condProb_adj_adj_components`); the
images of `pi` and `qj` are then incident to the common vertex `[p] = [q]` of `G/A`, and the
unconditional case (`uncond_NC_of_stable`) applies.  Degenerate cases: `w(A) = 0`; an edge of
`A` (equality); an edge inside a tree of `A` but not in `A` (both sides `0`); parallel images
(left side `0`).
-/

@[expose] public section

namespace ArborealDecay.SimonLieb

universe u

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

theorem arborealProb_eq_zero_of {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    {P : SimpleGraph Λ → Prop} (h : ∀ F : SimpleGraph Λ, F.IsAcyclic → P F → False) :
    H02.arborealProb β hβ P = 0 := by
  unfold H02.arborealProb
  rw [Finset.sum_eq_zero, zero_div]
  intro F hF
  simp only [mem_filter, mem_univ, true_and] at hF
  exact (h F hF.1 hF.2).elim

theorem forestWeight_eq_zero_of_le {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    {A F : SimpleGraph Λ} (hA : H02.forestWeight β hβ A = 0) (hAF : A ≤ F) :
    H02.forestWeight β hβ F = 0 := by
  unfold H02.forestWeight at hA ⊢
  obtain ⟨e, he, he0⟩ := Finset.prod_eq_zero_iff.1 hA
  exact Finset.prod_eq_zero (SimpleGraph.edgeFinset_mono hAF he) he0

theorem arborealProb_le_eq_zero {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    {A : SimpleGraph Λ} (hA : H02.forestWeight β hβ A = 0) (P : SimpleGraph Λ → Prop) :
    H02.arborealProb β hβ (fun F => A ≤ F ∧ P F) = 0 := by
  unfold H02.arborealProb
  rw [Finset.sum_eq_zero, zero_div]
  intro F hF
  simp only [mem_filter, mem_univ, true_and] at hF
  exact forestWeight_eq_zero_of_le hβ hA hF.2.1

theorem arborealProb_le_pos {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) {A : SimpleGraph Λ} (hAc : A.IsAcyclic)
    (hA : H02.forestWeight β hβ A ≠ 0) :
    0 < H02.arborealProb β hβ (fun F => A ≤ F) := by
  unfold H02.arborealProb
  refine div_pos ?_ (H02.Zforest_pos hβ hβ0)
  refine lt_of_lt_of_le (lt_of_le_of_ne (H02.forestWeight_nonneg hβ hβ0 A) (Ne.symm hA)) ?_
  refine Finset.single_le_sum (f := fun F => H02.forestWeight β hβ F)
    (fun F _ => H02.forestWeight_nonneg hβ hβ0 F) ?_
  simp [hAc]

/-- **Incident-edge negative correlation** (`prop:incident-NC`, conditional form; conditional on
`hstab`). -/
theorem incident_NC_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (A : SimpleGraph Λ) (hA : A.IsAcyclic) (p i q j : Λ) (hpq : A.Reachable p q)
    (hef : s(p, i) ≠ s(q, j)) :
    H02.arborealProb β hβ (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet ∧ s(q, j) ∈ F.edgeSet) *
        H02.arborealProb β hβ (fun F => A ≤ F) ≤
      H02.arborealProb β hβ (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet) *
        H02.arborealProb β hβ (fun F => A ≤ F ∧ s(q, j) ∈ F.edgeSet) := by
  simp only [SimpleGraph.mem_edgeSet]
  have hR0 : 0 ≤ H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i) *
      H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj q j) :=
    mul_nonneg (H02.arborealProb_nonneg hβ hβ0 _) (H02.arborealProb_nonneg hβ hβ0 _)
  -- the left side vanishes
  have hzero : H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i ∧ F.Adj q j) = 0 →
      H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i ∧ F.Adj q j) *
        H02.arborealProb β hβ (fun F => A ≤ F) ≤
      H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i) *
        H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj q j) := by
    intro h; rw [h, zero_mul]; exact hR0
  set c := A.connectedComponentMk with hc
  have hcA : ∀ u v, A.Reachable u v ↔ c u = c v := Surgery.hA_components A
  -- an edge inside a tree of `A` but not in `A` is never present
  have hint : ∀ u v, A.Reachable u v → ¬ A.Adj u v →
      ∀ F : SimpleGraph Λ, F.IsAcyclic → A ≤ F → ¬ F.Adj u v := by
    intro u v huv hnA F hF hAF hFuv
    exact Surgery.no_internal_edge c hA hcA hF hAF hFuv hnA ((hcA u v).1 huv)
  by_cases hw : H02.forestWeight β hβ A = 0
  · exact hzero (arborealProb_le_eq_zero hβ hw _)
  by_cases hApi : A.Adj p i
  · have e1 : H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i ∧ F.Adj q j) =
        H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj q j) :=
      Forest.arborealProb_congr hβ fun F _ =>
        ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1 hApi, h.2⟩⟩
    have e2 : H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i) =
        H02.arborealProb β hβ (fun F => A ≤ F) :=
      Forest.arborealProb_congr hβ fun F _ => ⟨fun h => h.1, fun h => ⟨h, h hApi⟩⟩
    rw [e1, e2, mul_comm]
  by_cases hAqj : A.Adj q j
  · have e1 : H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i ∧ F.Adj q j) =
        H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj p i) :=
      Forest.arborealProb_congr hβ fun F _ =>
        ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.1 hAqj⟩⟩
    have e2 : H02.arborealProb β hβ (fun F => A ≤ F ∧ F.Adj q j) =
        H02.arborealProb β hβ (fun F => A ≤ F) :=
      Forest.arborealProb_congr hβ fun F _ => ⟨fun h => h.1, fun h => ⟨h, h hAqj⟩⟩
    rw [e1, e2]
  by_cases hRpi : A.Reachable p i
  · exact hzero (arborealProb_eq_zero_of hβ fun F hF h => hint p i hRpi hApi F hF h.1 h.2.1)
  by_cases hRqj : A.Reachable q j
  · exact hzero (arborealProb_eq_zero_of hβ fun F hF h => hint q j hRqj hAqj F hF h.1 h.2.2)
  -- main case
  have hμA := arborealProb_le_pos hβ hβ0 hA hw
  have hpi : c p ≠ c i := fun h => hRpi ((hcA p i).2 h)
  have hqj : c q ≠ c j := fun h => hRqj ((hcA q j).2 h)
  have hcpq : c p = c q := (hcA p q).1 hpq
  have mulc : ∀ P : SimpleGraph Λ → Prop,
      H02.arborealProb β hβ (fun F => A ≤ F ∧ P F) =
        Surgery.condProb hβ (fun F => A ≤ F) P * H02.arborealProb β hβ (fun F => A ≤ F) := by
    intro P
    rw [Surgery.condProb, div_mul_cancel₀ _ hμA.ne']
  by_cases hpar : s(c p, c i) = s(c q, c j)
  · refine hzero ?_
    rw [mulc (fun F => F.Adj p i ∧ F.Adj q j),
      Surgery.condProb_adj_adj_parallel c hA hcA hβ hβ0 hpi hqj hpar hef, zero_mul]
  have hij : c i ≠ c j := by
    intro h; apply hpar; rw [hcpq, h]
  have h1 := Surgery.condProb_adj_components hA hβ hβ0 hw hRpi
  have h2 := Surgery.condProb_adj_components hA hβ hβ0 hw hRqj
  have h12 := Surgery.condProb_adj_adj_components hA hβ hβ0 hw hRpi hRqj hpar
  rw [mulc (fun F => F.Adj p i ∧ F.Adj q j), mulc (fun F => F.Adj p i),
    mulc (fun F => F.Adj q j), h1, h2, h12]
  rw [← hc] at *
  rw [← hcpq]
  have hm := Surgery.mapW_symm hβ c
  have hm0 := Surgery.mapW_nonneg hβ0 c
  have hNC := uncond_NC_of_stable hstab hm hm0 hij (Ne.symm hpi) 
    (fun h => hqj (hcpq.symm.trans h.symm))
  set κ₁ := β p i / Surgery.mapW β c (c p) (c i)
  set κ₂ := β q j / Surgery.mapW β c (c p) (c j)
  have hκ₁ : 0 ≤ κ₁ := div_nonneg (hβ0 _ _) (hm0 _ _)
  have hκ₂ : 0 ≤ κ₂ := div_nonneg (hβ0 _ _) (hm0 _ _)
  set μA := H02.arborealProb β hβ (fun F => A ≤ F)
  have hκ : 0 ≤ κ₁ * κ₂ * (μA * μA) := mul_nonneg (mul_nonneg hκ₁ hκ₂) (mul_nonneg hμA.le hμA.le)
  calc κ₁ * κ₂ * H02.arborealProb (Surgery.mapW β c) hm
          (fun F' => F'.Adj (c p) (c i) ∧ F'.Adj (c p) (c j)) * μA * μA
        = κ₁ * κ₂ * (μA * μA) * H02.arborealProb (Surgery.mapW β c) hm
          (fun F' => F'.Adj (c p) (c i) ∧ F'.Adj (c p) (c j)) := by ring
      _ ≤ κ₁ * κ₂ * (μA * μA) * (H02.arborealProb (Surgery.mapW β c) hm
          (fun F' => F'.Adj (c p) (c i)) * H02.arborealProb (Surgery.mapW β c) hm
          (fun F' => F'.Adj (c p) (c j))) := mul_le_mul_of_nonneg_left hNC hκ
      _ = _ := by ring

end

end ArborealDecay.SimonLieb
