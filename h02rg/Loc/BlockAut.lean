import Loc.Symplectic

/-!
# Automorphisms fixing a block

For a `j`-block `B` (with `j ≤ N`), the reflection of the `i`-th coordinate about the centre of
`B` and the permutations of the coordinates about the corner of `B` are affine automorphisms
mapping `B` to itself.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

theorem mem_blockSet_iff {j : ℕ} {b : Fin d → ℕ} {x : Lam d L N} :
    x ∈ blockSet j b ↔ ∀ i, (co x i).val / L ^ j = b i := by
  simp [blockSet, blk, funext_iff]

theorem val_lt_pow (x : Lam d L N) (i : Fin d) : (co x i).val < L ^ N := ZMod.val_lt _

theorem block_bound {j : ℕ} (hj : j ≤ N) {x : Lam d L N} {b : Fin d → ℕ} (hx : x ∈ blockSet j b)
    (i : Fin d) : b i * L ^ j ≤ (co x i).val ∧ (co x i).val < b i * L ^ j + L ^ j ∧
      b i * L ^ j + L ^ j ≤ L ^ N := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hb := (mem_blockSet_iff.1 hx) i
  have hv := val_lt_pow x i
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb]; exact Nat.div_mul_le_self _ _
  · rw [← hb]; exact Nat.lt_div_mul_add hL
  · have hdvd : L ^ j ∣ L ^ N := pow_dvd_pow L hj
    have h1 : b i < L ^ N / L ^ j := by
      rw [← hb]; exact Nat.div_lt_div_of_lt_of_dvd hdvd hv
    have h2 : L ^ N / L ^ j * L ^ j = L ^ N := Nat.div_mul_cancel hdvd
    nlinarith

theorem div_eq_of_bounds {v m q : ℕ} (hm : 0 < m) (h1 : q * m ≤ v) (h2 : v < q * m + m) :
    v / m = q := by
  refine Nat.div_eq_of_lt_le ?_ ?_
  · exact h1
  · rw [Nat.succ_mul]; exact h2

theorem img_eq_of_maps (T : AffAut d L N) {B : Finset (Lam d L N)} (h : ∀ y ∈ B, T.E y ∈ B) :
    T.img B = B := by
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [T.card_img])
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
  exact h x hx

/-- The reflection of the `i`-th coordinate about the centre of the block `b`. -/
def reflCenter (j : ℕ) (b : Fin d → ℕ) (i : Fin d) : AffAut d L N :=
  (AffAut.refl i).comp (AffAut.transl
    ((Pi.single i (((2 * (b i * L ^ j) + L ^ j - 1 : ℕ)) : ZMod (L ^ N)) : Fin d → ZMod (L ^ N))))

theorem reflCenter_maps {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) (i : Fin d) {y : Lam d L N}
    (hy : y ∈ blockSet j b) : (reflCenter (L := L) (N := N) j b i).E y ∈ blockSet j b := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  rw [mem_blockSet_iff]
  intro k
  have hk := block_bound hj hy k
  have hb := (mem_blockSet_iff.1 hy) k
  have hco : co ((reflCenter (L := L) (N := N) j b i).E y) k =
      (if k = i then -co y k else co y k) +
        (Pi.single i (((2 * (b i * L ^ j) + L ^ j - 1 : ℕ)) : ZMod (L ^ N)) : Fin d → ZMod (L ^ N)) k := rfl
  rw [hco]
  by_cases h : k = i
  · subst h
    simp only [if_true, Pi.single_eq_same]
    set v := (co y k).val
    have hyv : co y k = (v : ZMod (L ^ N)) := (ZMod.natCast_zmod_val _).symm
    have hle : v ≤ 2 * (b k * L ^ j) + L ^ j - 1 := by omega
    rw [hyv, show -(v : ZMod (L ^ N)) + ((2 * (b k * L ^ j) + L ^ j - 1 : ℕ) : ZMod (L ^ N)) =
      ((2 * (b k * L ^ j) + L ^ j - 1 - v : ℕ) : ZMod (L ^ N)) by push_cast [Nat.cast_sub hle]; ring,
      ZMod.val_natCast_of_lt (by omega)]
    exact div_eq_of_bounds hL (by omega) (by omega)
  · simp only [if_neg h, Pi.single_eq_of_ne h, add_zero]
    exact hb

theorem reflCenter_img {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) (i : Fin d) :
    (reflCenter (L := L) (N := N) j b i).img (blockSet j b) = blockSet j b :=
  img_eq_of_maps _ fun _ hy => reflCenter_maps hj b i hy

/-- The corner of the block `b`. -/
def corner (j : ℕ) (b : Fin d → ℕ) : Lam d L N :=
  (fun k => ((b k * L ^ j : ℕ) : ZMod (L ^ N)) : Fin d → ZMod (L ^ N))

/-- A permutation of the coordinates about the corner of the block `b`. -/
def permCorner (j : ℕ) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) : AffAut d L N :=
  (AffAut.transl (-corner j b)).comp ((AffAut.perm σ).comp (AffAut.transl (corner j b)))

theorem permCorner_maps {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d))
    {y : Lam d L N} (hy : y ∈ blockSet j b) :
    (permCorner (L := L) (N := N) j b σ).E y ∈ blockSet j b := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  rw [mem_blockSet_iff]
  intro k
  set m := σ.symm k
  have hkm := block_bound hj hy m
  have hkk := block_bound hj hy k
  have hco : co ((permCorner (L := L) (N := N) j b σ).E y) k =
      (co y m - ((b m * L ^ j : ℕ) : ZMod (L ^ N))) + ((b k * L ^ j : ℕ) : ZMod (L ^ N)) := by
    show co (y + -corner j b) m + co (corner j b) k = _
    rw [co_add, co_neg]
    simp only [Pi.add_apply, Pi.neg_apply, corner, co, sub_eq_add_neg]
  rw [hco]
  set v := (co y m).val
  have hyv : co y m = (v : ZMod (L ^ N)) := (ZMod.natCast_zmod_val _).symm
  have hle : b m * L ^ j ≤ v := hkm.1
  rw [hyv, show (v : ZMod (L ^ N)) - ((b m * L ^ j : ℕ) : ZMod (L ^ N)) + ((b k * L ^ j : ℕ) : ZMod (L ^ N)) =
    ((v - b m * L ^ j + b k * L ^ j : ℕ) : ZMod (L ^ N)) by push_cast [Nat.cast_sub hle]; ring,
    ZMod.val_natCast_of_lt (by omega)]
  exact div_eq_of_bounds hL (by omega) (by omega)

theorem permCorner_img {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) :
    (permCorner (L := L) (N := N) j b σ).img (blockSet j b) = blockSet j b :=
  img_eq_of_maps _ fun _ hy => permCorner_maps hj b σ hy

end

end Loc
