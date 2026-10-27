import FRD.Decomp

/-!
# Invariance under lattice symmetries

The covariances are invariant under the symmetries of the lattice: permutations of the
coordinates and reflections `x_i ↦ -x_i` (`cov_symm`); together with `fmat_translate` this is
the invariance of `C_j` under all lattice symmetries.
-/

namespace FRD

noncomputable section

open Finset Grassmann

variable {d n : ℕ} [NeZero n]

/-- A lattice symmetry fixing `0`: `(g x)_i = s_i x_{π(i)}` with `s_i = ±1`. -/
def symm (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (x : Torus d n) : Torus d n :=
  (fun i => ((s i : ℤ) : ZMod n) * co x (π i) : Fin d → ZMod n)

/-- The dual action: `(g^* m)_j = s_{π⁻¹ j} m_{π⁻¹ j}`, so that `k · (g x) = (g^* k) · x`. -/
def symmDual (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (m : Torus d n) : Torus d n :=
  (fun j => ((s (π.symm j) : ℤ) : ZMod n) * co m (π.symm j) : Fin d → ZMod n)

theorem co_symm (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (x : Torus d n) (i : Fin d) :
    co (symm π s x) i = ((s i : ℤ) : ZMod n) * co x (π i) := rfl

theorem symm_sub (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (x y : Torus d n) :
    symm π s (x - y) = symm π s x - symm π s y := by
  show (fun i => ((s i : ℤ) : ZMod n) * co (x - y) (π i)) =
    (fun i => ((s i : ℤ) : ZMod n) * co x (π i) - ((s i : ℤ) : ZMod n) * co y (π i))
  funext i; rw [co_sub, Pi.sub_apply, mul_sub]

theorem char_symm (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (m z : Torus d n) :
    char m (symm π s z) = char (symmDual π s m) z := by
  simp only [char, co_symm, symmDual]
  refine Fintype.prod_equiv π _ _ fun i => ?_
  simp only [co, Equiv.symm_apply_apply]
  ring_nf

theorem symmDual_bijective (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) :
    Function.Bijective (symmDual (n := n) π s) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun m m' h => ?_, rfl⟩
  funext i
  have := congrFun (congrArg (fun y : Torus d n => (y : Fin d → ZMod n)) h) (π i)
  simp only [symmDual, co, Equiv.symm_apply_apply] at this
  have hs : ((s i : ℤ) : ZMod n) * ((s i : ℤ) : ZMod n) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  calc co m i = ((s i : ℤ) : ZMod n) * ((s i : ℤ) : ZMod n) * co m i := by rw [hs, one_mul]
    _ = ((s i : ℤ) : ZMod n) * ((s i : ℤ) : ZMod n) * co m' i := by rw [mul_assoc, this, ← mul_assoc]
    _ = co m' i := by rw [hs, one_mul]

theorem cosk_units_mul (u : ℤˣ) (a : ZMod n) :
    Real.cos (2 * Real.pi * (((u : ℤ) : ZMod n) * a).val / n) = Real.cos (2 * Real.pi * a.val / n) := by
  rcases Int.units_eq_one_or u with h | h
  · simp [h]
  · rw [h]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    by_cases ha : a = 0
    · simp [ha]
    · rw [ZMod.neg_val, if_neg ha, Nat.cast_sub (ZMod.val_lt _).le]
      rw [show 2 * Real.pi * ((n : ℝ) - a.val) / n = 2 * Real.pi - 2 * Real.pi * a.val / n by
        have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
        field_simp]
      rw [Real.cos_two_pi_sub]

theorem lam_symmDual (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (m : Torus d n) :
    lam (symmDual π s m) = lam m := by
  simp only [lam, cosk, symmDual, co]
  simp only [cosk_units_mul]
  exact Fintype.sum_equiv π.symm _ _ fun i => rfl

/-- Fourier multipliers with symbols depending only on `λ(k)` are invariant under lattice
symmetries. -/
theorem fmat_symm_invariant {w : Torus d n → ℝ} (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)
    (hw : ∀ m, w (symmDual π s m) = w m) (x y : Torus d n) :
    fmat w (symm π s x) (symm π s y) = fmat w x y := by
  simp only [fmat, ← symm_sub, char_symm]
  congr 1
  refine Fintype.sum_bijective _ (symmDual_bijective π s) _ _ fun m => ?_
  rw [hw]

theorem uhat_symmDual (msq : ℝ) (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (m : Torus d n) :
    uhat msq (symmDual π s m) = uhat msq m := by
  simp [uhat, lam_symmDual]

/-- The covariances are invariant under lattice symmetries. -/
theorem cov_symm (P : PtFamily) (msq : ℝ) (S : Set ℝ) (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)
    (x y : Torus d n) : cov P msq S (symm π s x) (symm π s y) = cov P msq S x y :=
  fmat_symm_invariant π s (fun m => by simp [wt, uhat_symmDual]) x y

theorem Cj_symm (P : PtFamily) (msq L : ℝ) (j : ℕ) (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)
    (x y : Torus d n) : Cj P msq L j (symm π s x) (symm π s y) = Cj P msq L j x y :=
  cov_symm P msq _ π s x y

end

end FRD
