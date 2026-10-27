module

public import Mathlib

/-!
# Sup-distance on `ℤ × ℤ`

Definitions of nearest-neighbour adjacency, the sup distance and sup norm, together with
the triangle inequality, symmetry and the discrete Lipschitz property.
-/

@[expose] public section

namespace ArborealDecay.Lattice

/-- Nearest-neighbour adjacency on `ℤ²`. -/
def IsNN (x y : ℤ × ℤ) : Prop := |x.1 - y.1| + |x.2 - y.2| = 1

/-- Sup distance on `ℤ²`. -/
def supDist (x y : ℤ × ℤ) : ℤ := max |x.1 - y.1| |x.2 - y.2|

/-- Sup norm on `ℤ²`. -/
def supNorm (z : ℤ × ℤ) : ℤ := max |z.1| |z.2|

instance (x y : ℤ × ℤ) : Decidable (IsNN x y) := by unfold IsNN; infer_instance

theorem supDist_eq_supNorm (x y : ℤ × ℤ) : supDist x y = supNorm (x - y) := rfl

theorem supDist_nonneg (x y : ℤ × ℤ) : 0 ≤ supDist x y :=
  le_max_of_le_left (abs_nonneg _)

theorem supNorm_nonneg (z : ℤ × ℤ) : 0 ≤ supNorm z :=
  le_max_of_le_left (abs_nonneg _)

theorem supDist_self (x : ℤ × ℤ) : supDist x x = 0 := by simp [supDist]

theorem supDist_comm (x y : ℤ × ℤ) : supDist x y = supDist y x := by
  simp only [supDist]; rw [abs_sub_comm x.1, abs_sub_comm x.2]

theorem supDist_eq_zero {x y : ℤ × ℤ} : supDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 : |x.1 - y.1| ≤ 0 := h ▸ le_max_left _ _
    have h2 : |x.2 - y.2| ≤ 0 := h ▸ le_max_right _ _
    have := abs_nonpos_iff.mp h1
    have := abs_nonpos_iff.mp h2
    ext <;> omega
  · rintro rfl; exact supDist_self _

theorem supDist_le_iff {x y : ℤ × ℤ} {R : ℤ} :
    supDist x y ≤ R ↔ |x.1 - y.1| ≤ R ∧ |x.2 - y.2| ≤ R := max_le_iff

theorem supDist_le_iff' {x y : ℤ × ℤ} {R : ℤ} :
    supDist x y ≤ R ↔ y.1 - R ≤ x.1 ∧ x.1 ≤ y.1 + R ∧ y.2 - R ≤ x.2 ∧ x.2 ≤ y.2 + R := by
  rw [supDist_le_iff, abs_le, abs_le]; omega

theorem supDist_triangle (x y z : ℤ × ℤ) : supDist x z ≤ supDist x y + supDist y z := by
  rw [supDist_le_iff]
  have h1 : |x.1 - z.1| ≤ supDist x y + supDist y z := by
    calc |x.1 - z.1| = |(x.1 - y.1) + (y.1 - z.1)| := by ring_nf
      _ ≤ |x.1 - y.1| + |y.1 - z.1| := abs_add_le _ _
      _ ≤ _ := add_le_add (le_max_left _ _) (le_max_left _ _)
  have h2 : |x.2 - z.2| ≤ supDist x y + supDist y z := by
    calc |x.2 - z.2| = |(x.2 - y.2) + (y.2 - z.2)| := by ring_nf
      _ ≤ |x.2 - y.2| + |y.2 - z.2| := abs_add_le _ _
      _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)
  exact ⟨h1, h2⟩

theorem IsNN.symm {x y : ℤ × ℤ} (h : IsNN x y) : IsNN y x := by
  unfold IsNN at *; rwa [abs_sub_comm y.1, abs_sub_comm y.2]

theorem IsNN.supDist_le_one {x y : ℤ × ℤ} (h : IsNN x y) : supDist x y ≤ 1 := by
  unfold IsNN at h
  rw [supDist_le_iff]
  constructor <;> linarith [abs_nonneg (x.1 - y.1), abs_nonneg (x.2 - y.2)]

theorem IsNN.supDist_eq_one {x y : ℤ × ℤ} (h : IsNN x y) : supDist x y = 1 := by
  have h1 := h.supDist_le_one
  have h2 : supDist x y ≠ 0 := by
    intro h0
    have := supDist_eq_zero.mp h0
    subst this; simp [IsNN] at h
  have := supDist_nonneg x y
  omega

/-- Discrete Lipschitz property of the sup distance. -/
theorem abs_supDist_sub_le {x y : ℤ × ℤ} (h : IsNN x y) (z : ℤ × ℤ) :
    |supDist x z - supDist y z| ≤ 1 := by
  have h1 := h.supDist_le_one
  have h2 := h.symm.supDist_le_one
  have a := supDist_triangle x y z
  have b := supDist_triangle y x z
  rw [abs_le]; constructor <;> linarith

/-- Lipschitz in the centre variable. -/
theorem abs_supDist_sub_le' {x y : ℤ × ℤ} (h : IsNN x y) (c : ℤ × ℤ) :
    |supDist c x - supDist c y| ≤ 1 := by
  rw [supDist_comm c x, supDist_comm c y]; exact abs_supDist_sub_le h c

/-- Nearest neighbours are among the four unit translates. -/
theorem isNN_iff {x y : ℤ × ℤ} :
    IsNN x y ↔ y = x + (1, 0) ∨ y = x - (1, 0) ∨ y = x + (0, 1) ∨ y = x - (0, 1) := by
  unfold IsNN
  rw [abs_eq_max_neg, abs_eq_max_neg]
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  constructor
  · intro h
    rcases le_total 0 (x.1 - y.1) with h1 | h1 <;> rcases le_total 0 (x.2 - y.2) with h2 | h2 <;>
      simp only [max_def] at h <;> split_ifs at h <;> omega
  · intro h; rcases h with h | h | h | h <;> simp only [max_def] <;> split_ifs <;> omega

/-- The four nearest neighbours of `x`. -/
def nbrs (x : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {x + (1, 0), x - (1, 0), x + (0, 1), x - (0, 1)}

theorem mem_nbrs {x y : ℤ × ℤ} : y ∈ nbrs x ↔ IsNN x y := by
  rw [isNN_iff]; simp [nbrs]

theorem card_nbrs_le (x : ℤ × ℤ) : (nbrs x).card ≤ 4 := Finset.card_le_four

end ArborealDecay.Lattice
