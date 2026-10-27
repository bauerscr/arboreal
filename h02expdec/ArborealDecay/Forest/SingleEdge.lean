module

public import ArborealDecay.Forest.Basic

/-!
# Single-edge bound

For `u ≠ v` and nonnegative symmetric weights,
`P_β[uv ∈ F] ≤ β_uv / (1 + β_uv)` (note `eq:single-edge-bound`).
Proof: adding the edge `uv` is a bijection from forests with `u ↮ v` onto forests containing `uv`,
multiplying the weight by `β_uv`.
-/

@[expose] public section

namespace ArborealDecay.Forest

noncomputable section

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem forestWeight_sup_edge {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) {u v : Λ} (huv : u ≠ v)
    (G : SimpleGraph Λ) (hG : ¬ G.Adj u v) :
    H02.forestWeight β hβ (G ⊔ SimpleGraph.edge u v) = β u v * H02.forestWeight β hβ G := by
  have hn : s(u, v) ∉ G.edgeFinset := by simpa using hG
  unfold H02.forestWeight
  calc _ = ∏ e ∈ insert s(u, v) G.edgeFinset, Sym2.lift ⟨β, hβ⟩ e :=
        Finset.prod_congr (by
          ext e
          rcases eq_or_ne e s(u, v) with rfl | hne
          · simp [huv]
          · simp [hne]) (fun _ _ => rfl)
    _ = _ := by rw [Finset.prod_insert hn]; rfl

theorem adj_sup_edge_iff {G : SimpleGraph Λ} {u v a b : Λ} :
    (G ⊔ SimpleGraph.edge u v).Adj a b ↔ G.Adj a b ∨ ((a = u ∧ b = v ∨ a = v ∧ b = u) ∧ a ≠ b) := by
  simp [SimpleGraph.edge_adj]

/-- The sum of the weights of forests containing `uv` is `β_uv` times the sum of weights of
forests in which `u` and `v` are not connected. -/
theorem sum_adj_eq {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) {u v : Λ} (huv : u ≠ v) :
    (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ F.Adj u v, H02.forestWeight β hβ F) =
      β u v * ∑ G : SimpleGraph Λ with G.IsAcyclic ∧ ¬ G.Reachable u v,
        H02.forestWeight β hβ G := by
  rw [Finset.mul_sum]
  symm
  have hnadj : ∀ G : SimpleGraph Λ, ¬ G.Reachable u v → ¬ G.Adj u v :=
    fun G h h' => h h'.reachable
  refine Finset.sum_bij' (fun G _ => G ⊔ SimpleGraph.edge u v)
    (fun F _ => F.deleteEdges {s(u, v)}) ?_ ?_ ?_ ?_ ?_
  · intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
    refine ⟨(SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable u v hG.2).2 hG.1, ?_⟩
    rw [adj_sup_edge_iff]; exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF ⊢
    refine ⟨hF.1.anti (SimpleGraph.deleteEdges_le _), ?_⟩
    have := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hF.1) hF.2
    rw [SimpleGraph.isBridge_iff] at this
    exact this
  · intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    ext a b
    rw [SimpleGraph.deleteEdges_adj, adj_sup_edge_iff]
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨h | ⟨h, hab⟩, h2⟩
      · exact h
      · exact absurd h h2
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hnadj G hG.2 h
      · exact hnadj G hG.2 h.symm
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    ext a b
    rw [adj_sup_edge_iff, SimpleGraph.deleteEdges_adj]
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hF.2
        · exact hF.2.symm
    · intro h
      by_cases h2 : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
      · exact Or.inr ⟨h2, h.ne⟩
      · exact Or.inl ⟨h, h2⟩
  · intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    exact (forestWeight_sup_edge hβ huv G (hnadj G hG.2)).symm

/-- Single-edge bound (`eq:single-edge-bound`): for `u ≠ v`,
`P_β[uv ∈ F] ≤ β_uv / (1 + β_uv)`. -/
theorem arborealProb_adj_le {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) {u v : Λ} (huv : u ≠ v) :
    H02.arborealProb β hβ (fun F => F.Adj u v) ≤ β u v / (1 + β u v) := by
  have hZ := H02.Zforest_pos hβ hβ0
  have hb := hβ0 u v
  set SM := ∑ G : SimpleGraph Λ with G.IsAcyclic ∧ ¬ G.Reachable u v,
    H02.forestWeight β hβ G with hSM
  have hN := sum_adj_eq hβ huv
  have hle : (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ F.Adj u v, H02.forestWeight β hβ F) + SM
      ≤ H02.Zforest β hβ := by
    rw [hSM, ← Finset.sum_union]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        fun F _ _ => H02.forestWeight_nonneg hβ hβ0 F
      intro F hF
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hF ⊢
      rcases hF with h | h <;> exact h.1
    · rw [Finset.disjoint_left]
      intro F h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h2.2 h1.2.reachable
  have hSM0 : 0 ≤ SM := Finset.sum_nonneg fun F _ => H02.forestWeight_nonneg hβ hβ0 F
  unfold H02.arborealProb
  rw [div_le_div_iff₀ hZ (by linarith)]
  rw [hN] at hle ⊢
  nlinarith [mul_nonneg hb hSM0, mul_le_mul_of_nonneg_left hle hb]

end

end ArborealDecay.Forest
