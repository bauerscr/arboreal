import FRD.Continuity

/-!
# Zero-mode-free lattice Green function on the discrete torus (B1, lattice side)

On `Λ = Torus d n` (for `Λ_N = Lam d L N = Torus d (L ^ N)`), the zero-mode-free inverse of
`-Δ` is the Fourier multiplier with symbol `λ(k)⁻¹` for `k ≠ 0` and `0` at `k = 0`:
`G_lat(x) = |Λ|⁻¹ ∑_{k ≠ 0} e^{ik·x}/λ(k)`.
We prove `(-Δ) G_lat = 1 - Q` and `G_lat Q = 0`, with `Q = |Λ|⁻¹ 𝟙𝟙ᵀ` the zero-mode projector.
-/

namespace Cont

noncomputable section

open FRD Grassmann

variable {d n : ℕ} [NeZero n]

/-- Symbol of the zero-mode-free lattice Green function. -/
def latGreenSym (m : Torus d n) : ℝ := if m = 0 then 0 else (lam m)⁻¹

/-- Symbol of the zero-mode projector `Q`. -/
def latZeroSym (m : Torus d n) : ℝ := if m = 0 then 1 else 0

lemma latGreenSym_even : Even' (latGreenSym : Torus d n → ℝ) := fun m ↦ by
  simp [latGreenSym, neg_eq_zero, lam_neg]

omit [NeZero n] in
lemma latZeroSym_even : Even' (latZeroSym : Torus d n → ℝ) := fun m ↦ by
  simp [latZeroSym, neg_eq_zero]

/-- The zero-mode-free lattice Green matrix. -/
def latGreenMat : Matrix (Torus d n) (Torus d n) ℝ := fmat latGreenSym

/-- The zero-mode projector `Q x y = |Λ|⁻¹`. -/
def latQ : Matrix (Torus d n) (Torus d n) ℝ := fmat latZeroSym

/-- `G_lat(x) = G_lat(x, 0)`. -/
def latGreen (x : Torus d n) : ℝ := latGreenMat x 0

lemma latQ_apply (x y : Torus d n) : latQ x y = ((n : ℝ) ^ d)⁻¹ := by
  simp [latQ, fmat, latZeroSym, char_zero_left]

lemma latGreenMat_apply (x y : Torus d n) : latGreenMat x y = latGreen (x - y) := by
  simp [latGreen, latGreenMat, fmat]

lemma latGreen_neg (x : Torus d n) : latGreen (-x) = latGreen x := by
  simp only [latGreen, latGreenMat, fmat, sub_zero]
  congr 1
  exact Fintype.sum_congr _ _ fun m ↦ by
    rw [char_neg_right, Complex.conj_re]

/-- Symmetry of the lattice Green kernel. -/
lemma latGreenMat_symm (x y : Torus d n) : latGreenMat x y = latGreenMat y x := by
  rw [latGreenMat_apply, latGreenMat_apply, ← neg_sub, latGreen_neg]

/-- `(-Δ) G_lat = 1 - Q`: `G_lat` is the inverse of `-Δ` on the complement of the zero mode. -/
theorem negLap_mul_latGreenMat :
    (negLap : Matrix (Torus d n) (Torus d n) ℝ) * latGreenMat = 1 - latQ := by
  rw [negLap_eq_fmat, latGreenMat, fmat_mul lam_even latGreenSym_even, ← fmat_one, latQ,
    eq_sub_iff_add_eq, fmat_add]
  congr 1; funext m
  by_cases hm : m = 0
  · simp [latGreenSym, latZeroSym, hm]
  · simp [latGreenSym, latZeroSym, hm, mul_inv_cancel₀ (lam_pos hm).ne']

/-- `G_lat Q = 0`: `G_lat` annihilates the zero mode. -/
theorem latGreenMat_mul_latQ :
    (latGreenMat : Matrix (Torus d n) (Torus d n) ℝ) * latQ = 0 := by
  rw [latGreenMat, latQ, fmat_mul latGreenSym_even latZeroSym_even]
  have : (fun m : Torus d n ↦ latGreenSym m * latZeroSym m) = fun _ ↦ 0 := by
    funext m; by_cases hm : m = 0 <;> simp [latGreenSym, latZeroSym, hm]
  rw [this, fmat_const, zero_smul]

/-- Zero mean: `∑ₓ G_lat(x) = 0`. -/
theorem sum_latGreen : ∑ x : Torus d n, latGreen x = 0 := by
  have h := congrFun (congrFun (latGreenMat_mul_latQ (d := d) (n := n)) 0) 0
  simp only [Matrix.mul_apply, latQ_apply, Matrix.zero_apply, ← Finset.sum_mul] at h
  have hn : ((n : ℝ) ^ d)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n)))
  have h' := (mul_eq_zero.mp h).resolve_right hn
  rw [← h']
  exact Fintype.sum_congr _ _ fun x ↦ by rw [latGreenMat_apply, zero_sub, latGreen_neg]

end

end Cont
