module

public import Mathlib
public import ArborealDecay.Lattice.Basic

/-!
# Toroidal sup-distance on `ZMod L × ZMod L`
-/

@[expose] public section

namespace ArborealDecay.Lattice

/-- Nearest-neighbour adjacency on the torus `(ℤ/L)²`. -/
def IsTorusNN (L : ℕ) (x y : ZMod L × ZMod L) : Prop :=
  (x.1 = y.1 ∧ (x.2 - y.2 = 1 ∨ y.2 - x.2 = 1)) ∨ (x.2 = y.2 ∧ (x.1 - y.1 = 1 ∨ y.1 - x.1 = 1))

/-- Toroidal sup distance. -/
def torusSupDist (L : ℕ) (x y : ZMod L × ZMod L) : ℕ :=
  max (x.1 - y.1).valMinAbs.natAbs (x.2 - y.2).valMinAbs.natAbs

variable {L : ℕ}

/-- Triangle inequality for the one-dimensional toroidal distance. -/
theorem natAbs_valMinAbs_add_le' (a b : ZMod L) :
    (a + b).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + b.valMinAbs.natAbs :=
  (ZMod.natAbs_valMinAbs_add_le a b).trans (Int.natAbs_add_le _ _)

theorem natAbs_valMinAbs_one_le : (1 : ZMod L).valMinAbs.natAbs ≤ 1 := by
  rcases Nat.lt_or_ge L 2 with h | h
  · interval_cases L
    · simp
    · have : (1 : ZMod 1) = 0 := Subsingleton.elim _ _
      simp [this]
  · have : NeZero L := ⟨by omega⟩
    have : (1 : ZMod L) = ((1 : ℕ) : ZMod L) := by simp
    rw [this, ZMod.valMinAbs_natCast_of_le_half (by omega)]
    simp

theorem natAbs_valMinAbs_sub_le (a b c : ZMod L) :
    (a - c).valMinAbs.natAbs ≤ (a - b).valMinAbs.natAbs + (b - c).valMinAbs.natAbs := by
  have := natAbs_valMinAbs_add_le' (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

theorem natAbs_valMinAbs_sub_comm (a b : ZMod L) :
    (a - b).valMinAbs.natAbs = (b - a).valMinAbs.natAbs := by
  rw [← neg_sub, ZMod.natAbs_valMinAbs_neg]

theorem torusSupDist_comm (x y : ZMod L × ZMod L) : torusSupDist L x y = torusSupDist L y x := by
  simp only [torusSupDist]; rw [natAbs_valMinAbs_sub_comm x.1, natAbs_valMinAbs_sub_comm x.2]

theorem torusSupDist_self (x : ZMod L × ZMod L) : torusSupDist L x x = 0 := by
  simp [torusSupDist]

theorem torusSupDist_triangle (x y z : ZMod L × ZMod L) :
    torusSupDist L x z ≤ torusSupDist L x y + torusSupDist L y z := by
  unfold torusSupDist
  have h1 := natAbs_valMinAbs_sub_le x.1 y.1 z.1
  have h2 := natAbs_valMinAbs_sub_le x.2 y.2 z.2
  have := le_max_left (x.1 - y.1).valMinAbs.natAbs (x.2 - y.2).valMinAbs.natAbs
  have := le_max_right (x.1 - y.1).valMinAbs.natAbs (x.2 - y.2).valMinAbs.natAbs
  have := le_max_left (y.1 - z.1).valMinAbs.natAbs (y.2 - z.2).valMinAbs.natAbs
  have := le_max_right (y.1 - z.1).valMinAbs.natAbs (y.2 - z.2).valMinAbs.natAbs
  omega

theorem torusSupDist_le_half [NeZero L] (x y : ZMod L × ZMod L) : torusSupDist L x y ≤ L / 2 :=
  max_le (ZMod.natAbs_valMinAbs_le _) (ZMod.natAbs_valMinAbs_le _)

theorem IsTorusNN.symm {x y : ZMod L × ZMod L} (h : IsTorusNN L x y) : IsTorusNN L y x := by
  unfold IsTorusNN at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

theorem IsTorusNN.torusSupDist_le_one {x y : ZMod L × ZMod L} (h : IsTorusNN L x y) :
    torusSupDist L x y ≤ 1 := by
  unfold torusSupDist
  have key : ∀ a b : ZMod L, a = b → (a - b).valMinAbs.natAbs = 0 := by
    intro a b hab; simp [hab]
  have key2 : ∀ a b : ZMod L, (a - b = 1 ∨ b - a = 1) → (a - b).valMinAbs.natAbs ≤ 1 := by
    rintro a b (h | h)
    · rw [h]; exact natAbs_valMinAbs_one_le
    · rw [natAbs_valMinAbs_sub_comm, h]; exact natAbs_valMinAbs_one_le
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact max_le (by rw [key _ _ h1]; omega) (key2 _ _ h2)
  · exact max_le (key2 _ _ h2) (by rw [key _ _ h1]; omega)

/-- Discrete Lipschitz property of the toroidal sup distance. -/
theorem abs_torusSupDist_sub_le {x y : ZMod L × ZMod L} (h : IsTorusNN L x y)
    (z : ZMod L × ZMod L) :
    |(torusSupDist L x z : ℤ) - (torusSupDist L y z : ℤ)| ≤ 1 := by
  have h1 := h.torusSupDist_le_one
  have h2 := h.symm.torusSupDist_le_one
  have a := torusSupDist_triangle x y z
  have b := torusSupDist_triangle y x z
  rw [abs_le]; constructor <;> omega

theorem abs_torusSupDist_sub_le' {x y : ZMod L × ZMod L} (h : IsTorusNN L x y)
    (c : ZMod L × ZMod L) :
    |(torusSupDist L c x : ℤ) - (torusSupDist L c y : ℤ)| ≤ 1 := by
  rw [torusSupDist_comm c x, torusSupDist_comm c y]; exact abs_torusSupDist_sub_le h c

end ArborealDecay.Lattice
