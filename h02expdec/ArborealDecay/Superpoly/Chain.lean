module

public import ArborealDecay.Superpoly.Iter

/-!
# Factorisation along the chain of terminals

On a type `T` with a height function `h`, let `β'` be a weight function that is
`h`-Lipschitz and in which the vertices of the level sets `{h = t k}` other than the terminals
`ρ k` are isolated.  Then the terminals form a chain of one-vertex unions, and
`μ(a ↔ ρ N) ≤ ∏_{k<N} μ(ρ k ↔ ρ (k+1))`.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The part below the level `t k`, together with the terminal `ρ k`. -/
def lo (h : T → ℤ) (t : ℕ → ℤ) (ρ : ℕ → T) (k : ℕ) : Finset T :=
  univ.filter (fun v => h v < t k ∨ v = ρ k)

/-- The part at or above the level `t k`. -/
def hi (h : T → ℤ) (t : ℕ → ℤ) (k : ℕ) : Finset T :=
  univ.filter (fun v => t k ≤ h v)

theorem mem_lo {h : T → ℤ} {t : ℕ → ℤ} {ρ : ℕ → T} {k : ℕ} {v : T} :
    v ∈ lo h t ρ k ↔ h v < t k ∨ v = ρ k := by simp [lo]

theorem mem_hi {h : T → ℤ} {t : ℕ → ℤ} {k : ℕ} {v : T} :
    v ∈ hi h t k ↔ t k ≤ h v := by simp [hi]

theorem oneVertexUnion_lo_hi {h : T → ℤ} {t : ℕ → ℤ} {ρ : ℕ → T} {k : ℕ} (hρ : h (ρ k) = t k) :
    OneVertexUnion (lo h t ρ k) (hi h t k) (ρ k) where
  cover x := by
    by_cases hx : h x < t k
    · exact Or.inl (mem_lo.2 (Or.inl hx))
    · exact Or.inr (mem_hi.2 (not_lt.1 hx))
  inter x h1 h2 := by
    rcases mem_lo.1 h1 with h1 | h1
    · exact absurd (mem_hi.1 h2) (not_le.2 h1)
    · exact h1
  mem₁ := mem_lo.2 (Or.inr rfl)
  mem₂ := mem_hi.2 hρ.ge

/-- The hypotheses on the wired weights. -/
theorem hcross_lo_hi {h : T → ℤ} {t : ℕ → ℤ} {ρ : ℕ → T} {k : ℕ} {β' : T → T → ℝ}
    (hβ : ∀ i j, β' i j = β' j i) (hLip : ∀ u v, β' u v ≠ 0 → |h u - h v| ≤ 1)
    (hjunk : ∀ u, h u = t k → u ≠ ρ k → ∀ v, β' u v = 0) :
    ∀ u v, u ∈ lo h t ρ k → u ≠ ρ k → v ∈ hi h t k → v ≠ ρ k → β' u v = 0 := by
  intro u v hu hu' hv hv'
  by_contra hne
  have h1 := hLip u v hne
  have h2 : h u < t k := by
    rcases mem_lo.1 hu with h | h
    · exact h
    · exact absurd h hu'
  have h3 := mem_hi.1 hv
  have h4 : h v = t k := by
    rw [abs_le] at h1; omega
  rw [hβ, hjunk v h4 hv' u] at hne
  exact hne rfl

/-- **The chain**: `μ(a ↔ ρ N) ≤ ∏_{k<N} μ(ρ k ↔ ρ (k+1))`. -/
theorem chain_le {h : T → ℤ} {t : ℕ → ℤ} {ρ : ℕ → T} (ht : StrictMono t) {m : ℕ}
    (hρ : ∀ k ≤ m, h (ρ k) = t k) {β' : T → T → ℝ} (hβ : ∀ i j, β' i j = β' j i)
    (hβ0 : ∀ i j, 0 ≤ β' i j) (hLip : ∀ u v, β' u v ≠ 0 → |h u - h v| ≤ 1)
    (hjunk : ∀ k ≤ m, ∀ u, h u = t k → u ≠ ρ k → ∀ v, β' u v = 0) {a : T} (ha : h a < t 0) :
    ∀ N ≤ m, connProb β' hβ a (ρ N) ≤ ∏ k ∈ range N, connProb β' hβ (ρ k) (ρ (k + 1))
  | 0, _ => by
    simpa using connProb_le_one hβ hβ0 a (ρ 0)
  | N + 1, hN => by
    have ih := chain_le ht hρ hβ hβ0 hLip hjunk ha N (by omega)
    have hU := oneVertexUnion_lo_hi (h := h) (t := t) (ρ := ρ) (hρ N (by omega))
    have hc := hcross_lo_hi (ρ := ρ) hβ hLip (hjunk N (by omega))
    have haN : a ∈ lo h t ρ N := mem_lo.2 (Or.inl (lt_of_lt_of_le ha (ht.monotone (Nat.zero_le N))))
    have hbN : ρ (N + 1) ∈ hi h t N := mem_hi.2 (by
      rw [hρ (N + 1) hN]; exact (ht (Nat.lt_succ_self N)).le)
    have := arborealProb_reachable_union hU hβ hβ0 hc haN hbN
    unfold connProb
    rw [this, Finset.prod_range_succ]
    exact mul_le_mul ih le_rfl (H02.arborealProb_nonneg hβ hβ0 _)
      (Finset.prod_nonneg fun k _ => H02.arborealProb_nonneg hβ hβ0 _)

/-- Chain bound for the full separation `a ↔ b`, `h a < t 0`, `t m < h b`. -/
theorem chain_final {h : T → ℤ} {t : ℕ → ℤ} {ρ : ℕ → T} (ht : StrictMono t) {m : ℕ}
    (hρ : ∀ k ≤ m, h (ρ k) = t k) {β' : T → T → ℝ} (hβ : ∀ i j, β' i j = β' j i)
    (hβ0 : ∀ i j, 0 ≤ β' i j) (hLip : ∀ u v, β' u v ≠ 0 → |h u - h v| ≤ 1)
    (hjunk : ∀ k ≤ m, ∀ u, h u = t k → u ≠ ρ k → ∀ v, β' u v = 0) {a b : T} (ha : h a < t 0)
    (hb : t m < h b) :
    connProb β' hβ a b ≤ ∏ k ∈ range m, connProb β' hβ (ρ k) (ρ (k + 1)) := by
  have hU := oneVertexUnion_lo_hi (h := h) (t := t) (ρ := ρ) (hρ m le_rfl)
  have hc := hcross_lo_hi (ρ := ρ) hβ hLip (hjunk m le_rfl)
  have haN : a ∈ lo h t ρ m := mem_lo.2 (Or.inl (lt_of_lt_of_le ha (ht.monotone (Nat.zero_le m))))
  have hbN : b ∈ hi h t m := mem_hi.2 hb.le
  have := arborealProb_reachable_union hU hβ hβ0 hc haN hbN
  have h1 := chain_le ht hρ hβ hβ0 hLip hjunk ha m le_rfl
  unfold connProb at h1 ⊢
  rw [this]
  calc _ ≤ H02.arborealProb β' hβ (fun F => F.Reachable a (ρ m)) * 1 :=
        mul_le_mul_of_nonneg_left (H02.arborealProb_le_one hβ hβ0 _)
          (H02.arborealProb_nonneg hβ hβ0 _)
    _ ≤ _ := by rw [mul_one]; exact h1

end

end ArborealDecay.Superpoly
