module

public import ArborealDecay.Superpoly.Diag

/-!
# Lattice positions on the torus

`torusPos L x u` is the position of `u` relative to `x`, in centred representatives.  It is
injective, its sup norm is the toroidal distance, and nearest-neighbour edges inside a ball of
radius `R` with `4 R ≤ L` are nearest-neighbour edges of `ℤ²`.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

variable {L : ℕ} [NeZero L]

/-- The position of `u` relative to `x` in `ℤ²`, by centred representatives. -/
def torusPos (L : ℕ) [NeZero L] (x u : ZMod L × ZMod L) : ℤ × ℤ :=
  ((x.1 - u.1).valMinAbs, (x.2 - u.2).valMinAbs)

theorem supNorm_torusPos (x u : ZMod L × ZMod L) :
    supNorm (torusPos L x u) = (torusSupDist L x u : ℤ) := by
  unfold supNorm torusPos torusSupDist
  simp only [Nat.cast_max, Int.natCast_natAbs]

theorem torusPos_injective (x : ZMod L × ZMod L) : Function.Injective (torusPos L x) := by
  intro u v h
  unfold torusPos at h
  simp only [Prod.mk.injEq] at h
  have h1 : x.1 - u.1 = x.1 - v.1 := by
    rw [← ZMod.coe_valMinAbs (x.1 - u.1), h.1, ZMod.coe_valMinAbs]
  have h2 : x.2 - u.2 = x.2 - v.2 := by
    rw [← ZMod.coe_valMinAbs (x.2 - u.2), h.2, ZMod.coe_valMinAbs]
  exact Prod.ext (sub_right_injective h1) (sub_right_injective h2)

theorem torusPos_self (x : ZMod L × ZMod L) : torusPos L x x = 0 := by
  simp [torusPos]

theorem valMinAbs_succ (s t : ZMod L) (R : ℤ) (hs : |s.valMinAbs| ≤ R) (ht : |t.valMinAbs| ≤ R)
    (hL : 2 * R + 1 < L) (h : t = s + 1) : t.valMinAbs = s.valMinAbs + 1 := by
  have h1 : (((t.valMinAbs - (s.valMinAbs + 1) : ℤ)) : ZMod L) = 0 := by
    push_cast
    rw [h]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have h2 : |t.valMinAbs - (s.valMinAbs + 1)| < (L : ℤ) := by
    rw [abs_lt]
    rw [abs_le] at hs ht
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd h1 h2
  omega

theorem isNN_torusPos {x u v : ZMod L × ZMod L} {R : ℤ} (hL : 4 * R ≤ L) (huv : u ≠ v)
    (hnn : IsTorusNN L u v) (hu : supNorm (torusPos L x u) ≤ R)
    (hv : supNorm (torusPos L x v) ≤ R) : IsNN (torusPos L x u) (torusPos L x v) := by
  have hu1 : |(x.1 - u.1).valMinAbs| ≤ R :=
    le_trans (le_max_left _ _) hu
  have hu2 : |(x.2 - u.2).valMinAbs| ≤ R :=
    le_trans (le_max_right _ _) hu
  have hv1 : |(x.1 - v.1).valMinAbs| ≤ R :=
    le_trans (le_max_left _ _) hv
  have hv2 : |(x.2 - v.2).valMinAbs| ≤ R :=
    le_trans (le_max_right _ _) hv
  have hR : 1 ≤ R := by
    by_contra hR
    push Not at hR
    have e1 : (x.1 - u.1).valMinAbs = 0 := abs_nonpos_iff.1 (hu1.trans (by omega))
    have e2 : (x.2 - u.2).valMinAbs = 0 := abs_nonpos_iff.1 (hu2.trans (by omega))
    have e3 : (x.1 - v.1).valMinAbs = 0 := abs_nonpos_iff.1 (hv1.trans (by omega))
    have e4 : (x.2 - v.2).valMinAbs = 0 := abs_nonpos_iff.1 (hv2.trans (by omega))
    rw [ZMod.valMinAbs_eq_zero] at e1 e2 e3 e4
    apply huv
    exact Prod.ext (by rw [sub_eq_zero] at e1 e3; rw [← e1, ← e3])
      (by rw [sub_eq_zero] at e2 e4; rw [← e2, ← e4])
  have hL2 : 2 * R + 1 < L := by omega
  unfold IsTorusNN at hnn
  unfold IsNN torusPos
  simp only
  rcases hnn with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have e : (x.1 - u.1) = (x.1 - v.1) := by rw [h1]
    have e2 := valMinAbs_succ (x.2 - u.2) (x.2 - v.2) R hu2 hv2 hL2 (by rw [← h2]; ring)
    rw [e, e2]; simp
  · have e : (x.1 - u.1) = (x.1 - v.1) := by rw [h1]
    have e2 := valMinAbs_succ (x.2 - v.2) (x.2 - u.2) R hv2 hu2 hL2 (by rw [← h2]; ring)
    rw [e, e2]; simp
  · have e : (x.2 - u.2) = (x.2 - v.2) := by rw [h1]
    have e2 := valMinAbs_succ (x.1 - u.1) (x.1 - v.1) R hu1 hv1 hL2 (by rw [← h2]; ring)
    rw [e, e2]; simp
  · have e : (x.2 - u.2) = (x.2 - v.2) := by rw [h1]
    have e2 := valMinAbs_succ (x.1 - v.1) (x.1 - u.1) R hv1 hu1 hL2 (by rw [← h2]; ring)
    rw [e, e2]; simp

end

end ArborealDecay.Superpoly
