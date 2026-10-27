module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Fibre expansion

For a map `π : α → β` and weights `g`, the weighted count of the subsets `S` of `N` on which `π`
is injective with image `T` factors over the fibres:
`∑_{S ⊆ N, π|_S injective, π(S) = T} ∏_{e ∈ S} g e = ∏_{t ∈ T} ∑_{e ∈ N, π e = t} g e`.
-/

@[expose] public section

namespace ArborealDecay.Surgery

noncomputable section

open Finset Classical

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The family of subsets of `N` on which `π` is injective, with prescribed image `T`. -/
theorem fibre_prod (π : α → β) (g : α → ℝ) (T : Finset β) :
    ∀ N : Finset α,
      ∑ S ∈ N.powerset.filter (fun S : Finset α => Set.InjOn π ↑S ∧ S.image π = T), ∏ e ∈ S, g e =
        ∏ t ∈ T, ∑ e ∈ N.filter (fun e => π e = t), g e := by
  induction T using Finset.induction_on with
  | empty =>
    intro N
    rw [Finset.prod_empty]
    have : N.powerset.filter (fun S : Finset α => Set.InjOn π ↑S ∧ S.image π = ∅) = {∅} := by
      ext S
      simp only [mem_filter, mem_powerset, mem_singleton, image_eq_empty]
      constructor
      · exact fun h => h.2.2
      · rintro rfl; simp
    rw [this, sum_singleton, prod_empty]
  | insert t T ht ih =>
    intro N
    rw [Finset.prod_insert ht, ← ih, Finset.sum_mul_sum, ← Finset.sum_product']
    symm
    refine Finset.sum_bij (fun p _ => insert p.1 p.2) ?_ ?_ ?_ ?_
    · rintro ⟨e, S₀⟩ hp
      simp only [mem_product, mem_filter, mem_powerset] at hp
      obtain ⟨⟨heN, het⟩, hS₀N, hinj, himg⟩ := hp
      have heS : e ∉ S₀ := by
        intro h
        have : π e ∈ S₀.image π := mem_image_of_mem _ h
        rw [himg, het] at this; exact ht this
      simp only [mem_filter, mem_powerset, Finset.insert_subset_iff]
      refine ⟨⟨heN, hS₀N⟩, ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert (by simpa using heS)).2 ⟨hinj, ?_⟩
        rintro ⟨x, hx, hxe⟩
        have : π e ∈ S₀.image π := hxe ▸ mem_image_of_mem _ (by simpa using hx)
        rw [himg, het] at this; exact ht this
      · rw [Finset.image_insert, himg, het]
    · rintro ⟨e, S₀⟩ hp ⟨e', S₀'⟩ hp' h
      simp only [mem_product, mem_filter, mem_powerset] at hp hp'
      obtain ⟨⟨heN, het⟩, hS₀N, hinj, himg⟩ := hp
      obtain ⟨⟨heN', het'⟩, hS₀N', hinj', himg'⟩ := hp'
      have heS : e ∉ S₀ := by
        intro h
        have : π e ∈ S₀.image π := mem_image_of_mem _ h
        rw [himg, het] at this; exact ht this
      have heS' : e' ∉ S₀' := by
        intro h
        have : π e' ∈ S₀'.image π := mem_image_of_mem _ h
        rw [himg', het'] at this; exact ht this
      have hee : e = e' := by
        have h1 : e' ∈ insert e S₀ := by simp only at h; rw [h]; exact mem_insert_self _ _
        rcases mem_insert.1 h1 with h2 | h2
        · exact h2.symm
        · exfalso
          have : π e' ∈ S₀.image π := mem_image_of_mem _ h2
          rw [himg, het'] at this; exact ht this
      subst hee
      simp only at h
      have : S₀ = S₀' := by
        rw [← Finset.erase_insert heS, h, Finset.erase_insert heS']
      rw [this]
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS
      obtain ⟨hSN, hinj, himg⟩ := hS
      have : t ∈ S.image π := by rw [himg]; exact mem_insert_self _ _
      obtain ⟨e, heS, het⟩ := mem_image.1 this
      refine ⟨(e, S.erase e), ?_, Finset.insert_erase heS⟩
      simp only [mem_product, mem_filter, mem_powerset]
      refine ⟨⟨hSN heS, het⟩, (Finset.erase_subset _ _).trans hSN,
        hinj.mono (by simp), ?_⟩
      ext x
      simp only [mem_image, mem_erase]
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        have : π y ∈ insert t T := by rw [← himg]; exact mem_image_of_mem _ hy2
        rcases mem_insert.1 this with h | h
        · exact absurd (hinj hy2 heS (h.trans het.symm)) hy1
        · exact h
      · intro hx
        have : x ∈ S.image π := by rw [himg]; exact mem_insert_of_mem hx
        obtain ⟨y, hy, rfl⟩ := mem_image.1 this
        refine ⟨y, ⟨fun hye => ht ?_, hy⟩, rfl⟩
        rw [hye, het] at hx; exact hx
    · rintro ⟨e, S₀⟩ hp
      simp only [mem_product, mem_filter, mem_powerset] at hp
      obtain ⟨⟨heN, het⟩, hS₀N, hinj, himg⟩ := hp
      have heS : e ∉ S₀ := by
        intro h
        have : π e ∈ S₀.image π := mem_image_of_mem _ h
        rw [himg, het] at this; exact ht this
      simp only
      rw [Finset.prod_insert heS]

end

end ArborealDecay.Surgery
