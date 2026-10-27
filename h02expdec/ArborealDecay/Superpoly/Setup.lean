module

public import ArborealDecay.Superpoly.Chain
public import ArborealDecay.Lattice

/-!
# Set-up for the nested-separator argument

A finite vertex type `V` carries an injective "position" map `φ : V → ℤ²` (relative to the
centre); the height of `v` is `supNorm (φ v)`.  The levels are `lev r₀ k = 2^k r₀`.  The ambient
type of the wired graph is `T = Fin (m+1) ⊕ V`: the vertex `inl k` is the terminal into which the
level set `{height = lev k}` is wired, and `inr v` is a vertex of the original graph.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

/-- The level `2^k r₀`. -/
def lev (r₀ k : ℕ) : ℤ := ((2 ^ k * r₀ : ℕ) : ℤ)

theorem lev_succ (r₀ k : ℕ) : lev r₀ (k + 1) = 2 * lev r₀ k := by
  unfold lev; push_cast; ring

theorem lev_strictMono {r₀ : ℕ} (hr : 0 < r₀) : StrictMono (lev r₀) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rw [lev_succ]
  have : 0 < lev r₀ k := by unfold lev; positivity
  omega

theorem lev_pos {r₀ : ℕ} (hr : 0 < r₀) (k : ℕ) : 0 < lev r₀ k := by unfold lev; positivity

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The ambient type of the wired graph. -/
abbrev Amb (V : Type) (m : ℕ) : Type := Fin (m + 1) ⊕ V

/-- The height on the ambient type. -/
def heightT (φ : V → ℤ × ℤ) (r₀ m : ℕ) : Amb V m → ℤ :=
  Sum.elim (fun i => lev r₀ i) (fun v => supNorm (φ v))

/-- The terminal `ρ k`. -/
def rho (V : Type) (m k : ℕ) : Amb V m := Sum.inl (Fin.ofNat (m + 1) k)

theorem heightT_rho (φ : V → ℤ × ℤ) (r₀ m : ℕ) {k : ℕ} (hk : k ≤ m) :
    heightT φ r₀ m (rho V m k) = lev r₀ k := by
  unfold heightT rho
  have : (Fin.ofNat (m + 1) k).val = k := by simp; omega
  show lev r₀ (Fin.ofNat (m + 1) k).val = lev r₀ k
  rw [this]

theorem rho_injective {m : ℕ} {j k : ℕ} (hj : j ≤ m) (hk : k ≤ m) (h : rho V m j = rho V m k) :
    j = k := by
  unfold rho at h
  have h1 := Sum.inl.inj h
  have e1 : (Fin.ofNat (m + 1) j).val = j := by simp; omega
  have e2 : (Fin.ofNat (m + 1) k).val = k := by simp; omega
  rw [← e1, ← e2, h1]

/-- The wiring of the original graph into the ambient type. -/
def liftW {m : ℕ} (β : V → V → ℝ) : Amb V m → Amb V m → ℝ := mapW β Sum.inr

theorem liftW_symm {m : ℕ} {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (u v : Amb V m) :
    liftW β u v = liftW β v u := mapW_symm hβ _ u v

theorem liftW_nonneg {m : ℕ} {β : V → V → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j) (u v : Amb V m) :
    0 ≤ liftW β u v := mapW_nonneg hβ0 _ u v

theorem liftW_inr {m : ℕ} {β : V → V → ℝ} (hdiag : ∀ u, β u u = 0) (u v : V) :
    liftW (m := m) β (Sum.inr u) (Sum.inr v) = β u v :=
  mapW_inj_apply Sum.inr_injective β hdiag u v

theorem liftW_inl_left {m : ℕ} (β : V → V → ℝ) (i : Fin (m + 1)) (v : Amb V m) :
    liftW β (Sum.inl i) v = 0 :=
  mapW_not_range_left _ (fun a => by simp) v

theorem liftW_inl_right {m : ℕ} (β : V → V → ℝ) (u : Amb V m) (i : Fin (m + 1)) :
    liftW β u (Sum.inl i) = 0 :=
  mapW_not_range_right _ (fun a => by simp) u

theorem liftW_diag {m : ℕ} (β : V → V → ℝ) (u : Amb V m) : liftW β u u = 0 := mapW_diag _ _ _

theorem liftW_lip {m : ℕ} {β : V → V → ℝ} (φ : V → ℤ × ℤ) (r₀ : ℕ) (hdiag : ∀ u, β u u = 0)
    (hLip : ∀ u v, β u v ≠ 0 → |supNorm (φ u) - supNorm (φ v)| ≤ 1) (u v : Amb V m)
    (huv : liftW β u v ≠ 0) : |heightT φ r₀ m u - heightT φ r₀ m v| ≤ 1 := by
  rcases u with i | u
  · exact absurd (liftW_inl_left β i v) huv
  · rcases v with j | v
    · exact absurd (liftW_inl_right β _ j) huv
    · rw [liftW_inr hdiag] at huv
      exact hLip u v huv

end

end ArborealDecay.Superpoly
