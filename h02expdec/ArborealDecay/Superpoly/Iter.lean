module

public import ArborealDecay.Superpoly.Level

/-!
# Iterated wiring of level sets

`wireMap h t ρ n` collapses the level sets `{h = t k}`, `k < n`, to the points `ρ k`.
`wireIter_of_inputs`: wiring these `n` separators one after the other can only increase
`μ(a ↔ b)`; the final graph is `mapW β (wireMap h t ρ n)` on the same type.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The total wiring map. -/
def wireMap (h : T → ℤ) (t : ℕ → ℤ) (ρ : ℕ → T) : ℕ → T → T
  | 0 => id
  | n + 1 => lvlCollapse h (t n) (ρ n) ∘ wireMap h t ρ n

theorem h_wireMap (h : T → ℤ) (t : ℕ → ℤ) (ρ : ℕ → T) :
    ∀ n, (∀ k < n, h (ρ k) = t k) → ∀ u, h (wireMap h t ρ n u) = h u
  | 0, _, u => rfl
  | n + 1, hρ, u => by
    show h (lvlCollapse h (t n) (ρ n) (wireMap h t ρ n u)) = h u
    rw [h_lvlCollapse (hρ n (by omega)), h_wireMap h t ρ n (fun k hk => hρ k (by omega))]

theorem wireMap_of_ne (h : T → ℤ) (t : ℕ → ℤ) (ρ : ℕ → T) :
    ∀ n u, (∀ k < n, h u ≠ t k) → wireMap h t ρ n u = u
  | 0, u, _ => rfl
  | n + 1, u, hu => by
    show lvlCollapse h (t n) (ρ n) (wireMap h t ρ n u) = u
    rw [wireMap_of_ne h t ρ n u (fun k hk => hu k (by omega))]
    unfold lvlCollapse
    simp [hu n (by omega)]

theorem wireMap_of_eq (h : T → ℤ) (t : ℕ → ℤ) (ρ : ℕ → T) (ht : StrictMono t) :
    ∀ n, (∀ k < n, h (ρ k) = t k) → ∀ k < n, ∀ u, h u = t k → wireMap h t ρ n u = ρ k
  | 0, _, k, hk, _, _ => absurd hk (by omega)
  | n + 1, hρ, k, hk, u, hu => by
    show lvlCollapse h (t n) (ρ n) (wireMap h t ρ n u) = ρ k
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
    · rw [wireMap_of_eq h t ρ ht n (fun j hj => hρ j (by omega)) k hk' u hu]
      unfold lvlCollapse
      have : h (ρ k) ≠ t n := by
        rw [hρ k hk]; exact (ht hk').ne
      simp [this]
    · subst hk'
      rw [wireMap_of_ne h t ρ k u (fun j hj => by rw [hu]; exact (ht hj).ne')]
      unfold lvlCollapse
      simp [hu]

theorem wireMap_eq_iff (h : T → ℤ) (t : ℕ → ℤ) (ρ : ℕ → T) (ht : StrictMono t) (n : ℕ)
    (hρ : ∀ k < n, h (ρ k) = t k) {k : ℕ} (hk : k < n) (u : T) :
    wireMap h t ρ n u = ρ k ↔ h u = t k := by
  constructor
  · intro hu
    have := h_wireMap h t ρ n hρ u
    rw [hu, hρ k hk] at this
    exact this.symm
  · exact wireMap_of_eq h t ρ ht n hρ k hk u

/-- **Iterated wiring** (from `(W)`). -/
theorem wireIter_of_inputs
    (hW : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
      ∀ (S : Finset V) (a b : V), a ∉ S → b ∉ S →
        (∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) →
        connProb β hβ a b ≤
          connProb (mapW β (collapse S)) (mapW_symm hβ _) (collapse S a) (collapse S b))
    (h : T → ℤ) (t : ℕ → ℤ) (ρ : ℕ → T) {β : T → T → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (hdiag : ∀ u, β u u = 0)
    (hLip : ∀ u v, β u v ≠ 0 → |h u - h v| ≤ 1) {a b : T} :
    ∀ n, (∀ k < n, h (ρ k) = t k) → (∀ k < n, h a < t k ∧ t k < h b) →
      connProb β hβ a b ≤ connProb (mapW β (wireMap h t ρ n)) (mapW_symm hβ _) a b
  | 0, _, _ => by
    have : mapW β (wireMap h t ρ 0) = β := by
      funext u v
      unfold mapW
      by_cases huv : u = v
      · subst huv; simp [hdiag]
      · have e : ∀ c : T, (univ.filter (fun x : T => wireMap h t ρ 0 x = c)) = {c} := by
          intro c; ext x; simp only [mem_filter, mem_univ, true_and, mem_singleton]; rfl
        simp [huv, e]
    unfold connProb
    simp only [this]
    exact le_rfl
  | n + 1, hρ, hab => by
    have ih := wireIter_of_inputs hW h t ρ hβ hβ0 hdiag hLip n (fun k hk => hρ k (by omega))
      (fun k hk => hab k (by omega))
    refine ih.trans ?_
    have hsymm := mapW_symm hβ (wireMap h t ρ n)
    have hnn := mapW_nonneg hβ0 (wireMap h t ρ n)
    have hlip' : ∀ u v, mapW β (wireMap h t ρ n) u v ≠ 0 → |h u - h v| ≤ 1 :=
      fun u v huv => mapW_lip (wireMap h t ρ n) h h
        (h_wireMap h t ρ n (fun k hk => hρ k (by omega))) hLip u v huv
    have := wireLevel_of_inputs hW h (t n) (ρ n) (hρ n (by omega)) hsymm hnn hlip'
      (hab n (by omega)).1 (hab n (by omega)).2
    refine this.trans (le_of_eq ?_)
    unfold connProb
    have e : mapW (mapW β (wireMap h t ρ n)) (lvlCollapse h (t n) (ρ n)) =
        mapW β (wireMap h t ρ (n + 1)) := by
      funext u v; rw [mapW_comp]; rfl
    simp only [e]

end

end ArborealDecay.Superpoly
