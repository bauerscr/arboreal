module

public import ArborealDecay.Surgery

/-!
# Algebra of vertex identification `mapW`

* `mapW_comp`: successive wirings compose, `mapW (mapW β f) g = mapW β (g ∘ f)`.
* `mapW_inj_apply`, `mapW_not_range`: pushing forward along an injective map.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery

section

variable {Λ Λ' Λ'' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
  [Fintype Λ''] [DecidableEq Λ'']

theorem sum_fibre_fibre (f : Λ → Λ') (g : Λ' → Λ'') (c : Λ'') (F : Λ → ℝ) :
    ∑ b ∈ univ.filter (fun b => g b = c), ∑ u ∈ univ.filter (fun u => f u = b), F u =
      ∑ u ∈ univ.filter (fun u => g (f u) = c), F u := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun u => g (f u) = c))
    (t := univ.filter (fun b => g b = c)) (g := f)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext u
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    constructor
    · intro h; exact ⟨by rw [h]; exact hb, h⟩
    · intro h; exact h.2
  · intro u hu
    simpa using hu

/-- Successive wirings compose. -/
theorem mapW_comp (β : Λ → Λ → ℝ) (f : Λ → Λ') (g : Λ' → Λ'') (c d : Λ'') :
    mapW (mapW β f) g c d = mapW β (g ∘ f) c d := by
  unfold mapW
  by_cases hcd : c = d
  · simp [hcd]
  · simp only [hcd, ite_false]
    have h1 : ∀ b ∈ univ.filter (fun b => g b = c), ∀ b' ∈ univ.filter (fun b' => g b' = d),
        (if b = b' then (0 : ℝ) else ∑ u ∈ univ.filter (fun u => f u = b),
          ∑ v ∈ univ.filter (fun v => f v = b'), β u v) =
        ∑ u ∈ univ.filter (fun u => f u = b), ∑ v ∈ univ.filter (fun v => f v = b'), β u v := by
      intro b hb b' hb'
      simp only [mem_filter, mem_univ, true_and] at hb hb'
      have : b ≠ b' := by rintro rfl; exact hcd (hb.symm.trans hb')
      simp [this]
    rw [Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => h1 b hb b' hb']
    have h2 : ∀ b ∈ univ.filter (fun b => g b = c),
        ∑ b' ∈ univ.filter (fun b' => g b' = d), ∑ u ∈ univ.filter (fun u => f u = b),
          ∑ v ∈ univ.filter (fun v => f v = b'), β u v =
        ∑ u ∈ univ.filter (fun u => f u = b),
          ∑ v ∈ univ.filter (fun v => g (f v) = d), β u v := by
      intro b _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      exact sum_fibre_fibre f g d (fun v => β u v)
    rw [Finset.sum_congr rfl h2]
    rw [sum_fibre_fibre f g c (fun u => ∑ v ∈ univ.filter (fun v => g (f v) = d), β u v)]
    rfl

/-- Pushing forward along an injective map does not change the weights between image points. -/
theorem mapW_inj_apply {j : Λ → Λ'} (hj : Function.Injective j) (γ : Λ → Λ → ℝ)
    (hdiag : ∀ a, γ a a = 0) (a b : Λ) : mapW γ j (j a) (j b) = γ a b := by
  unfold mapW
  by_cases hab : a = b
  · subst hab; simp [hdiag]
  · have hne : j a ≠ j b := fun h => hab (hj h)
    have e : ∀ c : Λ, univ.filter (fun u => j u = j c) = {c} := by
      intro c; ext u; simp [hj.eq_iff]
    simp [hne, e]

theorem mapW_not_range_left {j : Λ → Λ'} (γ : Λ → Λ → ℝ) {u : Λ'} (hu : ∀ a, j a ≠ u)
    (v : Λ') : mapW γ j u v = 0 := by
  unfold mapW
  have : univ.filter (fun a => j a = u) = ∅ := by
    ext a; simp [hu a]
  simp [this]

theorem mapW_not_range_right {j : Λ → Λ'} (γ : Λ → Λ → ℝ) {v : Λ'} (hv : ∀ a, j a ≠ v)
    (u : Λ') : mapW γ j u v = 0 := by
  unfold mapW
  have : univ.filter (fun a => j a = v) = ∅ := by
    ext a; simp [hv a]
  simp [this]

end

end

end ArborealDecay.Superpoly
