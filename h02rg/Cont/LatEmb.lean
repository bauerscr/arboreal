import Cont.LatScale

/-!
# Lattice points as torus points; the signed permutations of `𝕋²` (B3, T6 (c))

* `latEmb n z ∈ 𝕋²`: the torus point `z/n` of a lattice point `z ∈ Torus 2 n`
  (`ZMod.toAddCircle` in each coordinate, an additive hom).
* `latPt_latEmb`: `latPt n (latEmb n z) = z` (rounding recovers the lattice point).
* `dist_latEmb_latPt_le`: `dist (latEmb n (latPt n x)) x ≤ 1/(2n)`.
* `norm_latEmb_le`: `‖latEmb n z‖ ≤ |z|_∞/n`; `norm_le_supNorm_latPt`: `‖x‖ ≤ |latPt n x|_∞/n + 1/(2n)`.
* `abs_zabs_latPt_sub_le`: `| zabs(latPt n x i)/n - ‖x i‖ | ≤ 1/(2n)`.
* `clSgn τ s`: the signed permutation `y ↦ (±y_{τ⁻¹ i})_i` of `𝕋²`; `norm_clSgn`, `dist_clSgn`
  (isometries fixing `0`).
-/

set_option autoImplicit false

namespace Cont

noncomputable section

open Real Set Filter Topology Grassmann

/-- `‖(t : 𝕋¹)‖ ≤ |t|`. -/
lemma t6_norm_coe_le_abs (t : ℝ) : ‖(t : UnitAddCircle)‖ ≤ |t| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le t 0

/-- The torus point `z / n` of a lattice point. -/
def latEmb (n : ℕ) [NeZero n] (z : Torus 2 n) : UnitAddTorus (Fin 2) :=
  fun i => ZMod.toAddCircle ((z : Fin 2 → ZMod n) i)

lemma latEmb_apply (n : ℕ) [NeZero n] (z : Torus 2 n) (i : Fin 2) :
    latEmb n z i = ZMod.toAddCircle ((z : Fin 2 → ZMod n) i) := rfl

/-- `‖z/n‖_{𝕋¹} ≤ zabs z / n`. -/
lemma t6_norm_toAddCircle_le (n : ℕ) [NeZero n] (z : ZMod n) :
    ‖ZMod.toAddCircle z‖ ≤ (zabs z : ℝ) / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hv := ZMod.val_lt z
  rw [ZMod.toAddCircle_apply]
  have h1 : ‖((z.val / n : ℝ) : UnitAddCircle)‖ ≤ (z.val : ℝ) / n := by
    refine (t6_norm_coe_le_abs _).trans (le_of_eq (abs_of_nonneg (by positivity)))
  have h2 : ‖((z.val / n : ℝ) : UnitAddCircle)‖ ≤ ((n - z.val : ℕ) : ℝ) / n := by
    have e : ((z.val / n : ℝ) : UnitAddCircle) = (((z.val : ℝ) / n - 1 : ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    rw [e]
    refine (t6_norm_coe_le_abs _).trans (le_of_eq ?_)
    rw [Nat.cast_sub hv.le]
    have : (z.val : ℝ) / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn]; exact_mod_cast hv.le
    rw [abs_of_nonpos this]; field_simp; ring
  unfold zabs
  rcases min_choice z.val (n - z.val) with h | h <;> rw [h] <;> assumption

lemma norm_latEmb_le (n : ℕ) [NeZero n] (z : Torus 2 n) :
    ‖latEmb n z‖ ≤ (supNorm z : ℝ) / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (t6_norm_toAddCircle_le n _).trans ?_
  refine div_le_div_of_nonneg_right ?_ hn.le
  exact_mod_cast (Finset.le_sup (f := fun i => zabs ((z : Fin 2 → ZMod n) i)) (Finset.mem_univ i))

/-- `dist (z/n) x ≤ 1/(2n)` for the rounded lattice point `z = latPt n x`. -/
lemma dist_latEmb_latPt_le (n : ℕ) [NeZero n] (x : UnitAddTorus (Fin 2)) :
    dist (latEmb n (latPt n x)) x ≤ 1 / (2 * n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  have hx : x i = ((torusRep x i : ℝ) : UnitAddCircle) := (congrFun (torusProj_torusRep x) i).symm
  have e : latEmb n (latPt n x) i = (((b1c_j n x i : ℝ) / n : ℝ) : UnitAddCircle) := by
    rw [latEmb_apply]
    exact ZMod.toAddCircle_intCast (N := n) (b1c_j n x i)
  rw [e, hx, dist_eq_norm, ← AddCircle.coe_sub]
  exact (t6_norm_coe_le_abs _).trans (b1c_abs_j_sub hn x i)

/-- Rounding recovers a lattice point: `latPt n (z/n) = z`. -/
lemma latPt_latEmb (n : ℕ) [NeZero n] (z : Torus 2 n) : latPt n (latEmb n z) = z := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  funext i
  set v := ((z : Fin 2 → ZMod n) i).val with hvd
  have h1 : ((torusRep (latEmb n z) i : ℝ) : UnitAddCircle) = (((v : ℝ) / n : ℝ) : UnitAddCircle) := by
    refine (congrFun (torusProj_torusRep (latEmb n z)) i).trans ?_
    rw [latEmb_apply, ZMod.toAddCircle_apply]
  have h2 : (((torusRep (latEmb n z) i - (v : ℝ) / n : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, h1, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
  rw [zsmul_eq_mul, mul_one] at hk
  have h3 : (n : ℝ) * torusRep (latEmb n z) i = ((v + n * k : ℤ) : ℝ) := by
    have : torusRep (latEmb n z) i = (v : ℝ) / n + k := by linarith
    rw [this]; push_cast; field_simp
  show (((round ((n : ℝ) * torusRep (latEmb n z) i) : ℤ)) : ZMod n) = (z : Fin 2 → ZMod n) i
  rw [h3, round_intCast]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero, hvd, ZMod.natCast_zmod_val]

/-- `‖x‖ ≤ |latPt n x|_∞/n + 1/(2n)`. -/
lemma norm_le_supNorm_latPt (n : ℕ) [NeZero n] (x : UnitAddTorus (Fin 2)) :
    ‖x‖ ≤ (supNorm (latPt n x) : ℝ) / n + 1 / (2 * n) := by
  have h1 := norm_latEmb_le n (latPt n x)
  have h2 := dist_latEmb_latPt_le n x
  have h3 : ‖x‖ ≤ ‖latEmb n (latPt n x)‖ + dist (latEmb n (latPt n x)) x := by
    have := norm_le_insert' x (latEmb n (latPt n x))
    rw [dist_eq_norm, norm_sub_rev]
    linarith [norm_sub_rev (latEmb n (latPt n x)) x]
  linarith

/-- `| zabs(latPt n x)_i / n - ‖x_i‖ | ≤ 1/(2n)`. -/
lemma abs_zabs_latPt_sub_le (n : ℕ) [NeZero n] (x : UnitAddTorus (Fin 2)) (i : Fin 2) :
    |(zabs ((latPt n x : Fin 2 → ZMod n) i) : ℝ) / n - ‖x i‖| ≤ 1 / (2 * n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hj := b1c_abs_j_sub hn0 x i
  have hrep := Cont.b1c_norm_eq_rep x i
  -- upper bound: `zabs (k : ZMod n) ≤ |k|`
  have hup : (zabs ((latPt n x : Fin 2 → ZMod n) i) : ℝ) / n ≤ ‖x i‖ + 1 / (2 * n) := by
    have hz : (zabs (((b1c_j n x i : ℤ)) : ZMod n) : ℝ) ≤ |(b1c_j n x i : ℝ)| := by
      have := FRD.zabs_le_natAbs (n := n) (b1c_j n x i)
      have e : (((b1c_j n x i).natAbs : ℕ) : ℝ) = |(b1c_j n x i : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [← e]
      exact_mod_cast this
    have : |(b1c_j n x i : ℝ)| / n ≤ |torusRep x i| + 1 / (2 * n) := by
      have e : |(b1c_j n x i : ℝ)| / n = |(b1c_j n x i : ℝ) / n| := by
        rw [abs_div, abs_of_pos hn]
      rw [e]
      have := abs_sub_abs_le_abs_sub ((b1c_j n x i : ℝ) / n) (torusRep x i)
      linarith
    rw [hrep]
    exact (div_le_div_of_nonneg_right hz hn.le).trans this
  -- lower bound from the embedding
  have hlo : ‖x i‖ ≤ (zabs ((latPt n x : Fin 2 → ZMod n) i) : ℝ) / n + 1 / (2 * n) := by
    have h1 := t6_norm_toAddCircle_le n ((latPt n x : Fin 2 → ZMod n) i)
    have h2 : dist (latEmb n (latPt n x) i) (x i) ≤ 1 / (2 * n) :=
      (dist_le_pi_dist _ _ i).trans (dist_latEmb_latPt_le n x)
    rw [latEmb_apply] at h2
    have h3 := norm_le_insert' (x i) (ZMod.toAddCircle ((latPt n x : Fin 2 → ZMod n) i))
    rw [dist_eq_norm] at h2
    linarith [norm_sub_rev (ZMod.toAddCircle ((latPt n x : Fin 2 → ZMod n) i)) (x i)]
  rw [abs_le]; constructor <;> linarith

/-! ### Signed permutations of `𝕋²` -/

/-- The signed permutation `y ↦ (s_i y_{τ⁻¹ i})_i` of `𝕋²`, `s_i = -1` iff `s i`. -/
def clSgn (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) :
    UnitAddTorus (Fin 2) →+ UnitAddTorus (Fin 2) where
  toFun y := fun i => if s i then -y (τ.symm i) else y (τ.symm i)
  map_zero' := by funext i; simp
  map_add' x y := by
    funext i
    show (if s i then -(x (τ.symm i) + y (τ.symm i)) else x (τ.symm i) + y (τ.symm i)) =
      (if s i then -x (τ.symm i) else x (τ.symm i)) + (if s i then -y (τ.symm i) else y (τ.symm i))
    split_ifs <;> abel

lemma clSgn_apply (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) (y : UnitAddTorus (Fin 2))
    (i : Fin 2) : clSgn τ s y i = if s i then -y (τ.symm i) else y (τ.symm i) := rfl

lemma norm_clSgn (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) (y : UnitAddTorus (Fin 2)) :
    ‖clSgn τ s y‖ = ‖y‖ := by
  have hc : ∀ i, ‖clSgn τ s y i‖ = ‖y (τ.symm i)‖ := fun i => by
    rw [clSgn_apply]; split_ifs <;> simp
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
  · rw [hc]; exact norm_le_pi_norm y _
  · have := hc (τ j)
    rw [Equiv.symm_apply_apply] at this
    rw [← this]; exact norm_le_pi_norm (clSgn τ s y) _

lemma dist_clSgn (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) (x y : UnitAddTorus (Fin 2)) :
    dist (clSgn τ s x) (clSgn τ s y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_clSgn]

end

end Cont
