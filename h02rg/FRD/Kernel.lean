import FRD.Bounds
import FRD.Lift

/-!
# Bounds on the `ℤ^d` covariances

The `ℤ^d` kernels `c_j` (`covZ` at the scales of `C_j`) satisfy the scaling estimates of the
torus covariances: they agree with `C_j` on a large torus (`Cj_eq_Zd`).
-/

namespace FRD

noncomputable section

open Finset Grassmann

variable (P : PtFamily) {d : ℕ}

theorem nabC_zero {n : ℕ} [NeZero n] (C : Matrix (Torus d n) (Torus d n) ℝ) (x y : Torus d n) :
    nabC C (0 : Dir d → ℕ) 0 x y = C x y := by
  have h : (![0, 0] : Fin 2 → Dir d → ℕ) = 0 := by funext i; fin_cases i <;> rfl
  rw [nabC, h, nabla_zero _ (fun y => zero_vadd _ y)]
  rfl

theorem supNormZ_rep {n : ℕ} [NeZero n] (x : Torus d n) : 2 * supNormZ (rep x) ≤ n := by
  have : supNormZ (rep x) ≤ n / 2 := by
    rw [supNormZ_le_iff]; intro i; rw [natAbs_rep]; unfold zabs; omega
  omega

/-- `|c_{j+1}(z)| ≤ K L^{-(d-2)j}` at `m² = 0` for `2|z|_∞ < L^{j+2}`. -/
theorem covZ_bound (hd : 3 ≤ d) : ∃ K : ℝ, ∀ (L : ℕ), 2 ≤ L → ∀ j : ℕ, ∀ z : Zd d,
    2 * supNormZ z < L ^ (j + 2) →
    |covZ P d 0 (Set.Ioc (lowEnd L (j + 1)) ((L : ℝ) ^ (j + 1) / 2)) z| ≤
      K * (L : ℝ) ^ (-(((d : ℝ) - 2) * j)) := by
  obtain ⟨K, hK⟩ := Cj_bound P hd 0 le_rfl 0
  refine ⟨K * (2 * (d : ℝ))⁻¹, fun L hL j z hz => ?_⟩
  haveI : NeZero (L ^ (j + 2)) := ⟨by positivity⟩
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hz' : 2 * supNormZ z < L ^ (j + 2) := hz
  have hrep : rep (prj z - 0 : Torus d (L ^ (j + 2))) = z := by
    rw [sub_zero]; exact (eq_rep (x := prj z) rfl hz').symm
  have hlt : (L : ℝ) ^ (j + 1) < ((L ^ (j + 2) : ℕ) : ℝ) := by
    push_cast; exact pow_lt_pow_right₀ hL1 (by omega)
  have heq := Cj_eq_Zd P (n := L ^ (j + 2)) le_rfl (by omega) (L := L) (by positivity) (j + 1)
    hlt (prj z) 0
  rw [hrep] at heq
  have hb := hK (L ^ (j + 2)) L hL1.le j hlt.le 0 le_rfl 0 0 (by simp [Grassmann.mabs]) (by simp [Grassmann.mabs])
    (prj z) 0
  rw [nabC_zero, heq] at hb
  have h0 : Grassmann.mabs (0 : Dir d → ℕ) = 0 := by simp [Grassmann.mabs]
  simpa [h0] using hb

end

end FRD
