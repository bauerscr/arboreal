module

public import ArborealDecay.Superpoly.Annulus

/-!
# One annulus: the factor `μ_{β'}(ρ k ↔ ρ (k+1))`
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The window between the levels `k` and `k+1`, as a subset of the ambient type. -/
def KF (φ : V → ℤ × ℤ) (r₀ m k : ℕ) : Finset (Amb V m) :=
  hi (heightT φ r₀ m) (lev r₀) k ∩ lo (heightT φ r₀ m) (lev r₀) (rho V m) (k + 1)

section

variable {φ : V → ℤ × ℤ} (hφ : Function.Injective φ) {r₀ : ℕ} (hr : 0 < r₀) {m k : ℕ}
  (hk : k < m)

include hφ hr hk

theorem piW_mem_KF {u' : Amb V m} (hu' : u' ∈ AkF φ r₀ m k) : piW φ r₀ m u' ∈ KF φ r₀ m k := by
  have hmono := lev_strictMono hr
  obtain ⟨x, rfl, h1, h2⟩ := (mem_AkF hφ).1 hu'
  have hh : heightT φ r₀ m (Sum.inr x) = supNorm (φ x) := rfl
  by_cases e1 : supNorm (φ x) = lev r₀ k
  · rw [piW_of_eq φ hr m hk.le _ (hh.trans e1)]
    refine mem_inter.2 ⟨mem_hi.2 ?_, mem_lo.2 (Or.inl ?_)⟩
    · rw [heightT_rho φ r₀ m hk.le]
    · rw [heightT_rho φ r₀ m hk.le]; exact hmono (Nat.lt_succ_self k)
  · by_cases e2 : supNorm (φ x) = lev r₀ (k + 1)
    · rw [piW_of_eq φ hr m (Nat.succ_le_of_lt hk) _ (hh.trans e2)]
      refine mem_inter.2 ⟨mem_hi.2 ?_, mem_lo.2 (Or.inr rfl)⟩
      rw [heightT_rho φ r₀ m (Nat.succ_le_of_lt hk)]; exact (hmono (Nat.lt_succ_self k)).le
    · have hfix : piW φ r₀ m (Sum.inr x) = Sum.inr x := by
        refine piW_of_ne φ r₀ m _ fun j hj hjx => ?_
        rw [hh] at hjx
        rcases le_or_gt j k with hjk | hjk
        · have := hmono.monotone hjk; omega
        · have := hmono.monotone (show k + 1 ≤ j by omega); omega
      rw [hfix]
      refine mem_inter.2 ⟨mem_hi.2 (by rw [hh]; exact h1), mem_lo.2 (Or.inl ?_)⟩
      rw [hh]; omega

theorem piW_preimage_KF {β : V → V → ℝ} {u u' : Amb V m} (hu : u ∈ KF φ r₀ m k)
    (h : piW φ r₀ m u' = u) : u' ∈ AkF φ r₀ m k ∨ ∀ w, liftW β u' w = 0 := by
  cases u' with
  | inl i => exact Or.inr (liftW_inl_left β i)
  | inr x =>
    left
    rw [mem_AkF hφ]
    refine ⟨x, rfl, ?_⟩
    have hh : heightT φ r₀ m (Sum.inr x) = supNorm (φ x) := rfl
    have e : heightT φ r₀ m (Sum.inr x) = heightT φ r₀ m u := by
      rw [← heightT_piW φ r₀ m, h]
    rw [hh] at e
    obtain ⟨hu1, hu2⟩ := mem_inter.1 hu
    have h3 := mem_hi.1 hu1
    have h4 : heightT φ r₀ m u ≤ lev r₀ (k + 1) := by
      rcases mem_lo.1 hu2 with h | h
      · exact h.le
      · rw [h, heightT_rho φ r₀ m (Nat.succ_le_of_lt hk)]
    rw [e]; exact ⟨h3, h4⟩

end

end

end ArborealDecay.Superpoly
