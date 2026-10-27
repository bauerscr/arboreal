module

public import ArborealDecay.Superpoly.Chain

/-!
# Restriction of `μ(ρ k ↔ ρ (k+1))` to the window between two consecutive levels
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay

variable {T : Type} [Fintype T] [DecidableEq T]

theorem restrW_restrW (K₁ K₂ : Finset T) (β : T → T → ℝ) :
    restrW K₁ (restrW K₂ β) = restrW (K₁ ∩ K₂) β := by
  funext u v
  unfold restrW
  simp only [mem_inter]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- Wiring commutes with restriction to a window, provided the restriction is compatible with
the wiring map. -/
theorem mapW_restrW (β : T → T → ℝ) (hβ : ∀ i j, β i j = β j i) (π : T → T) (A K : Finset T)
    (h1 : ∀ u' ∈ A, π u' ∈ K)
    (h2 : ∀ u u', u ∈ K → π u' = u → u' ∈ A ∨ ∀ w, β u' w = 0) (u v : T) :
    mapW (restrW A β) π u v = restrW K (mapW β π) u v := by
  unfold mapW restrW
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, ite_false]
    by_cases hK : u ∈ K ∧ v ∈ K
    · simp only [hK, and_self, ↓reduceIte]
      refine Finset.sum_congr rfl fun u' hu' => Finset.sum_congr rfl fun v' hv' => ?_
      simp only [mem_filter, mem_univ, true_and] at hu' hv'
      by_cases hA : u' ∈ A ∧ v' ∈ A
      · simp only [hA, and_self, ↓reduceIte]
      · simp only [hA, ↓reduceIte]
        symm
        rcases h2 u u' hK.1 hu' with h | h
        · rcases h2 v v' hK.2 hv' with h' | h'
          · exact absurd ⟨h, h'⟩ hA
          · rw [hβ]; exact h' u'
        · exact h v'
    · simp only [hK, ↓reduceIte]
      refine Finset.sum_eq_zero fun u' hu' => Finset.sum_eq_zero fun v' hv' => ?_
      simp only [mem_filter, mem_univ, true_and] at hu' hv'
      have hA : ¬ (u' ∈ A ∧ v' ∈ A) := fun h => hK ⟨hu' ▸ h1 u' h.1, hv' ▸ h1 v' h.2⟩
      simp only [hA, ↓reduceIte]

theorem window_restrict {h : T → ℤ} {t : ℕ → ℤ} {ρ : ℕ → T} (ht : StrictMono t) {m : ℕ}
    (hρ : ∀ k ≤ m, h (ρ k) = t k) {β' : T → T → ℝ} (hβ : ∀ i j, β' i j = β' j i)
    (hβ0 : ∀ i j, 0 ≤ β' i j) (hLip : ∀ u v, β' u v ≠ 0 → |h u - h v| ≤ 1)
    (hjunk : ∀ k ≤ m, ∀ u, h u = t k → u ≠ ρ k → ∀ v, β' u v = 0) {k : ℕ} (hk : k < m) :
    connProb β' hβ (ρ k) (ρ (k + 1)) =
      H02.arborealProb (restrW (hi h t k ∩ lo h t ρ (k + 1)) β')
        (restrW_symm _ hβ) (fun F => F.Reachable (ρ k) (ρ (k + 1))) := by
  have hU1 := oneVertexUnion_lo_hi (h := h) (t := t) (ρ := ρ) (hρ (k + 1) hk)
  have hc1 := hcross_lo_hi (ρ := ρ) hβ hLip (hjunk (k + 1) hk)
  have hx1 : ρ k ∈ lo h t ρ (k + 1) := mem_lo.2 (Or.inl (by
    rw [hρ k hk.le]; exact ht (Nat.lt_succ_self k)))
  have s1 := arborealProb_reach_restrW hU1 hβ hβ0 hc1 hx1
  have hU2 := oneVertexUnion_symm (oneVertexUnion_lo_hi (h := h) (t := t) (ρ := ρ) (hρ k hk.le))
  have hc0 := hcross_lo_hi (ρ := ρ) hβ hLip (hjunk k hk.le)
  have hβ2 := restrW_symm (lo h t ρ (k + 1)) hβ
  have hc2 : ∀ u v, u ∈ hi h t k → u ≠ ρ k → v ∈ lo h t ρ k → v ≠ ρ k →
      restrW (lo h t ρ (k + 1)) β' u v = 0 := by
    intro u v hu hu' hv hv'
    unfold restrW
    split_ifs
    · rw [hβ]; exact hc0 v u hv hv' hu hu'
    · rfl
  have hx2 : ρ (k + 1) ∈ hi h t k := mem_hi.2 (by
    rw [hρ (k + 1) hk]; exact (ht (Nat.lt_succ_self k)).le)
  have s2 := arborealProb_reach_restrW hU2 hβ2 (restrW_nonneg _ hβ0) hc2 hx2
  have e := restrW_restrW (hi h t k) (lo h t ρ (k + 1)) β'
  unfold connProb
  rw [s1, arborealProb_reach_comm _ hβ2, s2,
    arborealProb_reach_comm _ (restrW_symm _ hβ2)]
  exact arborealProb_congr_weights e _ _ _

end

end ArborealDecay.Superpoly
