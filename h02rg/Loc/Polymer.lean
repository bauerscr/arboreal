import FRD.Lift

/-!
# Blocks, polymers and small sets (Section `sec:polymers`, as needed for `sec:Loc`)

On the torus `Λ_N = (ℤ/L^Nℤ)^d`:

* the `j`-block of `x` is indexed by `blk j x = (⌊x_i / L^j⌋)_i`;
* a `j`-polymer is a union of `j`-blocks;
* `X` and `Y` *touch* if `|x - y|_∞ ≤ 1` for some `x ∈ X`, `y ∈ Y`;
* a polymer is *connected* if it is nonempty and any two of its blocks are joined by a path of
  touching blocks;
* *small sets* `𝒮_j` are connected polymers with at most `2^d` blocks;
* `X^□` (`nbhd`) is the union of all small sets containing a block of `X`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d : ℕ} {L N : ℕ}

/-- The torus `Λ_N` of side `L^N`. -/
abbrev Lam (d L N : ℕ) := Torus d (L ^ N)

variable [NeZero L]

instance : NeZero (L ^ N) := ⟨pow_ne_zero _ (NeZero.ne L)⟩

/-- The index of the `j`-block containing `x`. -/
def blk (j : ℕ) (x : Lam d L N) : Fin d → ℕ := fun i => (co x i).val / L ^ j

/-- The `j`-block with index `b`. -/
def blockSet (j : ℕ) (b : Fin d → ℕ) : Finset (Lam d L N) := univ.filter fun x => blk j x = b

/-- `X` is a `j`-polymer: a union of `j`-blocks. -/
def IsPolymer (j : ℕ) (X : Finset (Lam d L N)) : Prop :=
  ∀ x y, blk j x = blk j y → x ∈ X → y ∈ X

/-- The indices of the `j`-blocks of `X`. -/
def blocks (j : ℕ) (X : Finset (Lam d L N)) : Finset (Fin d → ℕ) := X.image (blk j)

/-- `X` and `Y` touch: `inf_{x ∈ X, y ∈ Y} |x - y|_∞ ≤ 1`. -/
def Touch (X Y : Finset (Lam d L N)) : Prop := ∃ x ∈ X, ∃ y ∈ Y, supNorm (x - y) ≤ 1

/-- Two blocks of `X` are adjacent if they touch. -/
def BlockAdj (j : ℕ) (X : Finset (Lam d L N)) (b b' : Fin d → ℕ) : Prop :=
  b ∈ blocks j X ∧ b' ∈ blocks j X ∧ Touch (blockSet (L := L) (N := N) j b) (blockSet j b')

/-- `X` is connected: nonempty, and any two blocks are joined by a path of touching blocks. -/
def IsConnected (j : ℕ) (X : Finset (Lam d L N)) : Prop :=
  X.Nonempty ∧ ∀ b ∈ blocks j X, ∀ b' ∈ blocks j X, Relation.ReflTransGen (BlockAdj j X) b b'

/-- Small sets: connected polymers with at most `2^d` blocks. -/
def IsSmall (j : ℕ) (X : Finset (Lam d L N)) : Prop :=
  IsPolymer j X ∧ IsConnected j X ∧ (blocks j X).card ≤ 2 ^ d

open Classical in
/-- The small set neighbourhood `X^□`: the union of all small sets containing a block of `X`. -/
def nbhd (j : ℕ) (X : Finset (Lam d L N)) : Finset (Lam d L N) :=
  univ.filter fun y => ∃ S : Finset (Lam d L N), IsSmall j S ∧ y ∈ S ∧
    ∃ b ∈ blocks j X, blockSet j b ⊆ S

end

end Loc
