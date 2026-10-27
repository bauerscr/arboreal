module

public import ArborealDecay.Superpoly.Setup

/-!
# The wired graph and its chain factorisation
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The total wiring map on the ambient type. -/
def piW (φ : V → ℤ × ℤ) (r₀ m : ℕ) : Amb V m → Amb V m :=
  wireMap (heightT φ r₀ m) (lev r₀) (rho V m) (m + 1)

/-- The wired weights `β' = mapW (liftW β) π`. -/
def wiredW (φ : V → ℤ × ℤ) (r₀ m : ℕ) (β : V → V → ℝ) : Amb V m → Amb V m → ℝ :=
  mapW (liftW β) (piW φ r₀ m)

theorem hρ_all (φ : V → ℤ × ℤ) (r₀ m : ℕ) :
    ∀ k < m + 1, heightT φ r₀ m (rho V m k) = lev r₀ k :=
  fun k hk => heightT_rho φ r₀ m (by omega)

theorem heightT_piW (φ : V → ℤ × ℤ) (r₀ m : ℕ) (u : Amb V m) :
    heightT φ r₀ m (piW φ r₀ m u) = heightT φ r₀ m u :=
  h_wireMap _ _ _ (m + 1) (hρ_all φ r₀ m) u

theorem piW_of_ne (φ : V → ℤ × ℤ) (r₀ m : ℕ) (u : Amb V m)
    (hu : ∀ k < m + 1, heightT φ r₀ m u ≠ lev r₀ k) : piW φ r₀ m u = u :=
  wireMap_of_ne _ _ _ (m + 1) u hu

theorem piW_of_eq (φ : V → ℤ × ℤ) {r₀ : ℕ} (hr : 0 < r₀) (m : ℕ) {k : ℕ} (hk : k ≤ m)
    (u : Amb V m) (hu : heightT φ r₀ m u = lev r₀ k) : piW φ r₀ m u = rho V m k :=
  wireMap_of_eq _ _ _ (lev_strictMono hr) (m + 1) (hρ_all φ r₀ m) k (by omega) u hu

theorem wiredW_symm (φ : V → ℤ × ℤ) (r₀ m : ℕ) {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    (u v : Amb V m) : wiredW φ r₀ m β u v = wiredW φ r₀ m β v u :=
  mapW_symm (liftW_symm hβ) _ u v

theorem wiredW_nonneg (φ : V → ℤ × ℤ) (r₀ m : ℕ) {β : V → V → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j)
    (u v : Amb V m) : 0 ≤ wiredW φ r₀ m β u v :=
  mapW_nonneg (liftW_nonneg hβ0) _ u v

theorem wiredW_lip (φ : V → ℤ × ℤ) (r₀ m : ℕ) {β : V → V → ℝ} (hdiag : ∀ u, β u u = 0)
    (hLip : ∀ u v, β u v ≠ 0 → |supNorm (φ u) - supNorm (φ v)| ≤ 1) (u v : Amb V m)
    (huv : wiredW φ r₀ m β u v ≠ 0) : |heightT φ r₀ m u - heightT φ r₀ m v| ≤ 1 :=
  mapW_lip (piW φ r₀ m) (heightT φ r₀ m) (heightT φ r₀ m) (heightT_piW φ r₀ m)
    (liftW_lip φ r₀ hdiag hLip) u v huv

theorem wiredW_junk (φ : V → ℤ × ℤ) {r₀ : ℕ} (hr : 0 < r₀) (m : ℕ) (β : V → V → ℝ) {k : ℕ}
    (hk : k ≤ m) (u : Amb V m) (hu : heightT φ r₀ m u = lev r₀ k) (hne : u ≠ rho V m k)
    (v : Amb V m) : wiredW φ r₀ m β u v = 0 := by
  refine mapW_not_range_left _ (fun w hw => hne ?_) v
  have h1 : heightT φ r₀ m w = lev r₀ k := by
    rw [← heightT_piW φ r₀ m w]; unfold piW at hw ⊢; rw [hw]; exact hu
  rw [← hw]
  exact piW_of_eq φ hr m hk w h1

theorem connProb_liftW {m : ℕ} {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (hdiag : ∀ u, β u u = 0) (a b : V) :
    connProb (liftW (m := m) β) (liftW_symm hβ) (Sum.inr a) (Sum.inr b) = connProb β hβ a b := by
  unfold connProb
  have := arborealProb_reach_embed (Sum.inr : V → Amb V m) Sum.inr_injective
    (liftW_symm hβ) hβ (liftW_nonneg hβ0)
    (fun u v huv => by
      rcases huv with h | h
      · cases u with
        | inl i => exact liftW_inl_left β i v
        | inr x => exact absurd rfl (h x)
      · cases v with
        | inl i => exact liftW_inl_right β u i
        | inr x => exact absurd rfl (h x))
    (fun x y => liftW_inr hdiag x y) b a
  exact this

/-- **The chain bound** (from `(W)`): `μ_β(a ↔ b) ≤ ∏_{k<m} μ_{β'}(ρ k ↔ ρ (k+1))`. -/
theorem chain_bound_of_inputs
    (hW : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
      ∀ (S : Finset V) (a b : V), a ∉ S → b ∉ S →
        (∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) →
        connProb β hβ a b ≤
          connProb (mapW β (collapse S)) (mapW_symm hβ _) (collapse S a) (collapse S b))
    (φ : V → ℤ × ℤ) {r₀ : ℕ} (hr : 0 < r₀) (m : ℕ) {β : V → V → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) (hdiag : ∀ u, β u u = 0)
    (hLip : ∀ u v, β u v ≠ 0 → |supNorm (φ u) - supNorm (φ v)| ≤ 1) {a b : V}
    (ha : supNorm (φ a) < lev r₀ 0) (hb : lev r₀ m < supNorm (φ b)) :
    connProb β hβ a b ≤
      ∏ k ∈ range m, connProb (wiredW φ r₀ m β) (wiredW_symm φ r₀ m hβ) (rho V m k)
        (rho V m (k + 1)) := by
  have hmono := lev_strictMono hr
  rw [← connProb_liftW (m := m) hβ hβ0 hdiag a b]
  have h1 := wireIter_of_inputs hW (heightT φ r₀ m) (lev r₀) (rho V m) (liftW_symm hβ)
    (liftW_nonneg hβ0) (liftW_diag β) (liftW_lip φ r₀ hdiag hLip) (a := Sum.inr a)
    (b := Sum.inr b) (m + 1) (hρ_all φ r₀ m)
    (fun k hk => ⟨by
        have := hmono.monotone (Nat.zero_le k)
        simp only [heightT, Sum.elim_inr]; omega,
      by
        have := hmono.monotone (show k ≤ m by omega)
        simp only [heightT, Sum.elim_inr]; omega⟩)
  refine h1.trans ?_
  exact chain_final hmono (m := m) (fun k hk => hρ_all φ r₀ m k (by omega))
    (wiredW_symm φ r₀ m hβ) (wiredW_nonneg φ r₀ m hβ0) (wiredW_lip φ r₀ m hdiag hLip)
    (fun k hk u hu hne v => wiredW_junk φ hr m β hk u hu hne v)
    (a := Sum.inr a) (b := Sum.inr b)
    (by simp only [heightT, Sum.elim_inr]; exact ha)
    (by simp only [heightT, Sum.elim_inr]; exact hb)

end

end ArborealDecay.Superpoly
