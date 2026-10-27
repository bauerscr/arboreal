module

public import ArborealDecay.ExpDecay.Defs

/-!
# Exit edges on the torus

For `L > 2R + 2` the toroidal square of radius `R` around `y` is an ordinary lattice square:
the lift `u ↦ (valMinAbs (y - u))` embeds the toroidal exit edges into the `ℤ²` exit edges of
the origin, so there are at most `8R + 4` of them.
-/

@[expose] public section

namespace ArborealDecay.ExpDecay

open Finset ArborealDecay.Lattice

variable {L : ℕ}

/-- Lift of a torus point to `ℤ²`, centred at `y`. -/
def torusLift (y u : ZMod L × ZMod L) : ℤ × ℤ :=
  ((y.1 - u.1).valMinAbs, (y.2 - u.2).valMinAbs)

theorem supDist_zero_torusLift (y u : ZMod L × ZMod L) :
    supDist (0 : ℤ × ℤ) (torusLift y u) = (torusSupDist L y u : ℤ) := by
  simp only [supDist, torusLift, torusSupDist, Prod.fst_zero, Prod.snd_zero, zero_sub,
    abs_neg]
  rw [Nat.cast_max, Int.natCast_natAbs, Int.natCast_natAbs]

theorem torusLift_injective (y : ZMod L × ZMod L) : Function.Injective (torusLift y) := by
  intro u u' h
  simp only [torusLift, Prod.mk.injEq, ZMod.valMinAbs_inj, sub_right_inj] at h
  exact Prod.ext h.1 h.2

/-- A one-dimensional step on the torus lifts to a step on `ℤ`. -/
theorem valMinAbs_step {a b : ZMod L} {R : ℕ} {c : ℤ} (hL : 2 * (R : ℤ) + 2 < L)
    (ha : a.valMinAbs.natAbs ≤ R) (hb : b.valMinAbs.natAbs ≤ R + 1)
    (hc : c = 1 ∨ c = -1) (h : b = a + c) : b.valMinAbs = a.valMinAbs + c := by
  have h1 : ((b.valMinAbs - a.valMinAbs - c : ℤ) : ZMod L) = 0 := by
    push_cast
    rw [h]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have h2 : |b.valMinAbs - a.valMinAbs - c| < L := by
    rw [abs_lt]; omega
  have := Int.eq_zero_of_abs_lt_dvd h1 h2
  omega

theorem isNN_torusLift {y u v : ZMod L × ZMod L} {R : ℕ} (hL : 2 * (R : ℤ) + 2 < L)
    (hu : torusSupDist L y u ≤ R) (hv : torusSupDist L y v ≤ R + 1) (huv : IsTorusNN L u v) :
    IsNN (torusLift y u) (torusLift y v) := by
  have hu1 : (y.1 - u.1).valMinAbs.natAbs ≤ R := (le_max_left _ _).trans hu
  have hu2 : (y.2 - u.2).valMinAbs.natAbs ≤ R := (le_max_right _ _).trans hu
  have hv1 : (y.1 - v.1).valMinAbs.natAbs ≤ R + 1 := (le_max_left _ _).trans hv
  have hv2 : (y.2 - v.2).valMinAbs.natAbs ≤ R + 1 := (le_max_right _ _).trans hv
  unfold IsNN torusLift
  simp only
  rcases huv with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have := valMinAbs_step (c := 1) hL hu2 hv2 (Or.inl rfl) (by
      rw [show y.2 - v.2 = (y.2 - u.2) + (u.2 - v.2) by ring, h2]; norm_cast)
    rw [h1]; simp only [sub_self, abs_zero, zero_add]; rw [this]; simp
  · have := valMinAbs_step (c := -1) hL hu2 hv2 (Or.inr rfl) (by
      rw [show y.2 - v.2 = (y.2 - u.2) - (v.2 - u.2) by ring, h2]; push_cast; ring)
    rw [h1]; simp only [sub_self, abs_zero, zero_add]; rw [this]; simp
  · have := valMinAbs_step (c := 1) hL hu1 hv1 (Or.inl rfl) (by
      rw [show y.1 - v.1 = (y.1 - u.1) + (u.1 - v.1) by ring, h2]; norm_cast)
    rw [h1]; simp only [sub_self, abs_zero, add_zero]; rw [this]; simp
  · have := valMinAbs_step (c := -1) hL hu1 hv1 (Or.inr rfl) (by
      rw [show y.1 - v.1 = (y.1 - u.1) - (v.1 - u.1) by ring, h2]; push_cast; ring)
    rw [h1]; simp only [sub_self, abs_zero, add_zero]; rw [this]; simp

end ArborealDecay.ExpDecay
