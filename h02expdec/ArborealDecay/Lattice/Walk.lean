module

public import Mathlib
public import ArborealDecay.Lattice.Basic
public import ArborealDecay.Lattice.Torus

/-!
# Discrete intermediate value property along walks

A walk whose endpoints lie on different sides of a sup-distance sphere meets the sphere.
-/

@[expose] public section

namespace ArborealDecay.Lattice

open SimpleGraph

variable {Λ : Type*} {G : SimpleGraph Λ}

/-- Generic discrete intermediate value theorem along a walk. -/
theorem exists_mem_support_eq_of_lipschitz (f : Λ → ℤ) (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ 1)
    {x z : Λ} (p : G.Walk x z) {r : ℤ} (h1 : f x ≤ r) (h2 : r ≤ f z) :
    ∃ v ∈ p.support, f v = r := by
  induction p with
  | nil => exact ⟨_, by simp, le_antisymm h1 h2⟩
  | @cons a b c hab p ih =>
    have hb := abs_le.mp (hf a b hab)
    by_cases hfb : f b ≤ r
    · obtain ⟨v, hv, hv'⟩ := ih hfb h2
      exact ⟨v, by simp [hv], hv'⟩
    · refine ⟨a, by simp, ?_⟩
      omega

/-- Reverse version: values decrease from `x` to `z`. -/
theorem exists_mem_support_eq_of_lipschitz' (f : Λ → ℤ) (hf : ∀ x y, G.Adj x y → |f x - f y| ≤ 1)
    {x z : Λ} (p : G.Walk x z) {r : ℤ} (h1 : r ≤ f x) (h2 : f z ≤ r) :
    ∃ v ∈ p.support, f v = r := by
  obtain ⟨v, hv, hv'⟩ := exists_mem_support_eq_of_lipschitz f
    (fun a b h => by rw [abs_sub_comm]; exact hf b a h.symm) p.reverse h2 h1
  exact ⟨v, by simpa using hv, hv'⟩

section Square

variable {φ : Λ → ℤ × ℤ} (hφ : ∀ x y, G.Adj x y → IsNN (φ x) (φ y))
include hφ

/-- Square boundary separates: a walk from inside the closed square `supDist c · ≤ r` to
strictly outside meets the boundary `supDist c · = r`. -/
theorem exists_mem_support_supDist_eq {x z : Λ} (p : G.Walk x z) (c : ℤ × ℤ) {r : ℤ}
    (hx : supDist c (φ x) ≤ r) (hz : r < supDist c (φ z)) :
    ∃ v ∈ p.support, supDist c (φ v) = r :=
  exists_mem_support_eq_of_lipschitz (fun v => supDist c (φ v))
    (fun a b h => abs_supDist_sub_le' (hφ a b h) c) p hx hz.le

/-- Same, with a walk from outside to inside. -/
theorem exists_mem_support_supDist_eq' {x z : Λ} (p : G.Walk x z) (c : ℤ × ℤ) {r : ℤ}
    (hx : r < supDist c (φ x)) (hz : supDist c (φ z) ≤ r) :
    ∃ v ∈ p.support, supDist c (φ v) = r :=
  exists_mem_support_eq_of_lipschitz' (fun v => supDist c (φ v))
    (fun a b h => abs_supDist_sub_le' (hφ a b h) c) p hx.le hz

/-- Centre at the start point: if `supDist x z > R ≥ 0` the walk visits the sphere of radius
`R` around `x`. -/
theorem exists_mem_support_supDist_eq_start {x z : Λ} (p : G.Walk x z) {R : ℤ} (hR : 0 ≤ R)
    (hz : R < supDist (φ x) (φ z)) : ∃ v ∈ p.support, supDist (φ x) (φ v) = R :=
  exists_mem_support_supDist_eq hφ p (φ x) (by rw [supDist_self]; exact hR) hz

end Square

section Torus

variable {L : ℕ} {ψ : Λ → ZMod L × ZMod L} (hψ : ∀ x y, G.Adj x y → IsTorusNN L (ψ x) (ψ y))
include hψ

/-- Torus analogue: a walk from `torusSupDist c · ≤ r` to `torusSupDist c · > r` meets the
sphere `torusSupDist c · = r`.  (Such a walk can exist only if `r < L / 2`.) -/
theorem exists_mem_support_torusSupDist_eq {x z : Λ} (p : G.Walk x z) (c : ZMod L × ZMod L)
    {r : ℕ} (hx : torusSupDist L c (ψ x) ≤ r) (hz : r < torusSupDist L c (ψ z)) :
    ∃ v ∈ p.support, torusSupDist L c (ψ v) = r := by
  obtain ⟨v, hv, hv'⟩ := exists_mem_support_eq_of_lipschitz
    (fun v => (torusSupDist L c (ψ v) : ℤ))
    (fun a b h => abs_torusSupDist_sub_le' (hψ a b h) c) p (r := r) (by exact_mod_cast hx)
    (by exact_mod_cast hz.le)
  exact ⟨v, hv, by exact_mod_cast hv'⟩

theorem exists_mem_support_torusSupDist_eq' {x z : Λ} (p : G.Walk x z) (c : ZMod L × ZMod L)
    {r : ℕ} (hx : r < torusSupDist L c (ψ x)) (hz : torusSupDist L c (ψ z) ≤ r) :
    ∃ v ∈ p.support, torusSupDist L c (ψ v) = r := by
  obtain ⟨v, hv, hv'⟩ := exists_mem_support_eq_of_lipschitz'
    (fun v => (torusSupDist L c (ψ v) : ℤ))
    (fun a b h => abs_torusSupDist_sub_le' (hψ a b h) c) p (r := r) (by exact_mod_cast hx.le)
    (by exact_mod_cast hz)
  exact ⟨v, hv, by exact_mod_cast hv'⟩

end Torus

/-- Specialisation to a finite set of lattice points. -/
theorem exists_mem_support_supDist_eq_finset {Λ' : Finset (ℤ × ℤ)} {G : SimpleGraph Λ'}
    (hG : ∀ x y, G.Adj x y → IsNN x.1 y.1) {x z : Λ'} (p : G.Walk x z) (c : ℤ × ℤ) {r : ℤ}
    (hx : supDist c x.1 ≤ r) (hz : r < supDist c z.1) :
    ∃ v ∈ p.support, supDist c v.1 = r :=
  exists_mem_support_supDist_eq (φ := fun v : Λ' => v.1) hG p c hx hz

end ArborealDecay.Lattice
