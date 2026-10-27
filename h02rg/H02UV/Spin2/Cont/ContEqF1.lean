import Spin2.Cont.ContEqS8
import Cont.LatEmb

set_option autoImplicit false

/-!
# B3, `r`-dependent form, final assembly (I): lattice geometry

* `eqf_latEmb_sub`: `latEmb` is additive.
* `eqf_supNorm_le`: `|z|_∞ ≤ n‖z/n‖ + 1/2`.
* **`eqf_supNorm_latPt_sub`**: `|latPt y − latPt x|_∞ ≤ n·dist(x, y) + 3/2`.
* **`eqf_supNorm_latPt_ge`**: `n‖x‖ − 1/2 ≤ |latPt x|_∞`.
-/

namespace Spin2

open Cont Loc

noncomputable section

theorem eqf_latEmb_sub (n : ℕ) [NeZero n] (z w : Grassmann.Torus 2 n) :
    latEmb n (z - w) = latEmb n z - latEmb n w := by
  funext i
  simp only [latEmb_apply, Pi.sub_apply]
  exact map_sub (ZMod.toAddCircle (N := n)) _ _

theorem eqf_supNorm_le (n : ℕ) [NeZero n] (z : Grassmann.Torus 2 n) :
    (Grassmann.supNorm z : ℝ) ≤ n * ‖latEmb n z‖ + 1 / 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
    (fun i => Grassmann.zabs ((z : Fin 2 → ZMod n) i))
  have hs : Grassmann.supNorm z = Grassmann.zabs ((z : Fin 2 → ZMod n) i) := hi
  have h := abs_zabs_latPt_sub_le n (latEmb n z) i
  rw [latPt_latEmb] at h
  have h1 := (abs_le.1 h).2
  have h2 : ‖latEmb n z i‖ ≤ ‖latEmb n z‖ := norm_le_pi_norm (latEmb n z) i
  rw [hs]
  have h3 : (Grassmann.zabs ((z : Fin 2 → ZMod n) i) : ℝ) / n ≤ ‖latEmb n z‖ + 1 / (2 * n) := by linarith
  rw [div_le_iff₀ hn] at h3
  have e : (‖latEmb n z‖ + 1 / (2 * n)) * n = n * ‖latEmb n z‖ + 1 / 2 := by field_simp
  linarith

/-- **`|latPt y − latPt x|_∞ ≤ n·dist(x, y) + 3/2`.** -/
theorem eqf_supNorm_latPt_sub (n : ℕ) [NeZero n] (x y : UnitAddTorus (Fin 2)) :
    (Grassmann.supNorm (latPt n y - latPt n x) : ℝ) ≤ n * dist x y + 3 / 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have h1 := eqf_supNorm_le n (latPt n y - latPt n x)
  rw [eqf_latEmb_sub, ← dist_eq_norm] at h1
  have h2 := dist_latEmb_latPt_le n y
  have h3 := dist_latEmb_latPt_le n x
  have h4 : dist (latEmb n (latPt n y)) (latEmb n (latPt n x)) ≤
      dist (latEmb n (latPt n y)) y + dist y x + dist x (latEmb n (latPt n x)) :=
    dist_triangle4 _ _ _ _
  rw [dist_comm x (latEmb n (latPt n x)), dist_comm y x] at h4
  have h5 : dist (latEmb n (latPt n y)) (latEmb n (latPt n x)) ≤ dist x y + 1 / n := by
    have : 1 / (2 * (n : ℝ)) + 1 / (2 * n) = 1 / n := by field_simp; ring
    linarith
  have := mul_le_mul_of_nonneg_left h5 hn.le
  have e : (n : ℝ) * (dist x y + 1 / n) = n * dist x y + 1 := by field_simp
  linarith

/-- **`n‖x‖ − 1/2 ≤ |latPt x|_∞`.** -/
theorem eqf_supNorm_latPt_ge (n : ℕ) [NeZero n] (x : UnitAddTorus (Fin 2)) :
    n * ‖x‖ - 1 / 2 ≤ (Grassmann.supNorm (latPt n x) : ℝ) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have h := norm_le_supNorm_latPt n x
  have := mul_le_mul_of_nonneg_left h hn.le
  have e : (n : ℝ) * ((Grassmann.supNorm (latPt n x) : ℝ) / n + 1 / (2 * n)) =
      Grassmann.supNorm (latPt n x) + 1 / 2 := by field_simp
  linarith

end

end Spin2
