import Grassmann.TNorm
import Grassmann.NablaRec

/-!
# Examples of `T_j(ℓ)` norms (Section `sec:norms`)

* `tNorm_ψ`: `‖ψ_x‖_{T_j(ℓ)} = ‖ψ̄_x‖_{T_j(ℓ)} = ℓ`;
* `tNorm_dψ_le`: `‖(∇_e ψ)_x‖_{T_j(ℓ)} ≤ ℓ L^{-j}` (the text states equality; we prove the
  upper bound, which is what the power counting uses);
* `tNorm_psi_psibar_le`, `tNorm_dpsi_psibar_le`: `‖ψ_x ψ̄_x‖ ≤ ℓ^2`,
  `‖(∇_e ψ)_x ψ̄_x‖ ≤ ℓ^2 L^{-j}`;
* `four_eq` and `tNorm_four_le`:
  `ψ_x ψ̄_x ψ_{x+e} ψ̄_{x+e} = ψ_x ψ̄_x (∇_e ψ)_x (∇_e ψ̄)_x` and its norm is `≤ ℓ^4 L^{-2j}`
  (the upper half of the `≍` in the text).
-/

namespace Grassmann

noncomputable section

open Finset Equiv

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

theorem psiPow_one (a : Sf X) : psiPow ![a] = ψ a := by
  simp [psiPow, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, ψ]

theorem asym_one (g : TestFn X) (u : Fin 1 → Sf X) : asym g 1 u = g 1 u := by
  simp [asym]

theorem pair_ψ (a : Sf X) (g : TestFn X) : pair (ψ a) g = g 1 ![a] := by
  rw [← psiPow_one, pair_psiPow, asym_one]

/-- `‖ψ_a‖_{T(ℓ)} = ℓ`. -/
theorem tNorm_ψ (hh : 0 < h) (hℓ : 0 < ℓ) (a : Sf X) :
    tNorm E p h ℓ (ψ a) = ENNReal.ofReal ℓ := by
  refine le_antisymm (tNorm_le fun g hg => ?_) ?_
  · rw [pair_ψ]
    simpa using abs_le_of_phiNorm_le hh hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) ![a]
  · -- the test function equal to `ℓ` on sequences of length one
    let g : TestFn X := fun n _ => if n = 1 then (ℓ : ℂ) else 0
    have hg : phiNorm E p h ℓ g ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      refine phiNorm_le fun n z α hα => ?_
      unfold phiTerm
      by_cases hn : n = 1
      · subst hn
        by_cases hα0 : α = 0
        · subst hα0
          rw [nabla_zero _ (by simp)]
          simp [g, ord, mabs, abs_of_pos hℓ, hℓ.ne']
        · have : nab α (g 1) z = 0 := nabla_const _ hα0 (ℓ : ℂ) z
          rw [this]; simp
      · have : g n = 0 := funext fun _ => if_neg hn
        rw [this, map_zero]; simp
    have := le_tNorm (ψ a) hg
    rwa [pair_ψ, show g 1 ![a] = (ℓ : ℂ) from if_pos rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hℓ] at this

theorem tNorm_psi (hh : 0 < h) (hℓ : 0 < ℓ) (x : X) :
    tNorm E p h ℓ (psi x) = ENNReal.ofReal ℓ := tNorm_ψ hh hℓ _

theorem tNorm_psibar (hh : 0 < h) (hℓ : 0 < ℓ) (x : X) :
    tNorm E p h ℓ (psibar x) = ENNReal.ofReal ℓ := tNorm_ψ hh hℓ _

/-- `(∇_e ψ)_a = ψ_{a + e} - ψ_a`. -/
def dψ (e : E) (a : Sf X) : N X := ψ (sh (Pi.single e 1) a) - ψ a

theorem sh_add (b b' : E → ℕ) (a : Sf X) : sh (b + b') a = sh b (sh b' a) := by
  simp [sh, add_vadd]

/-- `‖(∇_e ψ)_a‖_{T(ℓ)} ≤ ℓ h^{-1}` (with `h = L^j`), for `p_Φ ≥ 1`. -/
theorem tNorm_dψ_le (hp : 1 ≤ p) (hh : 0 < h) (hℓ : 0 < ℓ) (e : E) (a : Sf X) :
    tNorm E p h ℓ (dψ e a) ≤ ENNReal.ofReal (ℓ * h⁻¹) := by
  refine tNorm_le fun g hg => ?_
  have hpair : pair (dψ e a) g =
      nab (Pi.single (0 : Fin 1) (Pi.single e 1)) (g 1) ![a] := by
    rw [nabla_single sh (fun _ => sh_zero _) sh_add, ediff, dψ, sub_eq_add_neg, pair_add, pair_ψ,
      show -ψ a = (-1 : ℂ) • ψ a by simp, pair_smul, pair_ψ]
    have : Function.update ![a] 0 (sh (Pi.single e 1) (![a] 0)) = ![sh (Pi.single e 1) a] := by
      funext i; fin_cases i; simp
    rw [this]; ring
  have hord : ord (Pi.single (0 : Fin 1) (Pi.single e 1) : Fin 1 → E → ℕ) = 1 := by
    simp [ord, mabs]
  have hb := abs_nab_le hh hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) ![a]
    (Pi.single (0 : Fin 1) (Pi.single e 1)) (fun i => by fin_cases i; simpa [mabs] using hp)
  rw [hpair]
  simpa [hord] using hb

/-- `‖ψ_x ψ̄_x‖_{T(ℓ)} ≤ ‖ψ_x‖ ‖ψ̄_x‖ = ℓ^2`. -/
theorem tNorm_psi_psibar_le (hh : 0 < h) (hℓ : 0 < ℓ) (x : X) :
    tNorm E p h ℓ (psi x * psibar x) ≤ ENNReal.ofReal (ℓ ^ 2) := by
  refine (tNorm_mul_le hh hℓ _ _).trans ?_
  rw [tNorm_psi hh hℓ, tNorm_psibar hh hℓ, ← ENNReal.ofReal_mul hℓ.le, sq]

theorem ψ_mul_self (a : Sf X) : ψ a * ψ a = 0 := ExteriorAlgebra.ι_sq_zero _

theorem ψ_anticomm (a b : Sf X) : ψ a * ψ b = -(ψ b * ψ a) := ι_anticomm _ _

/-- `ψ_x ψ̄_x ψ_{x+e} ψ̄_{x+e} = ψ_x ψ̄_x (∇_e ψ)_x (∇_e ψ̄)_x`, using `ψ_x^2 = ψ̄_x^2 = 0`. -/
theorem four_eq (e : E) (x : X) :
    psi x * psibar x * (ψ (sh (Pi.single e 1) (x, 1)) * ψ (sh (Pi.single e 1) (x, -1))) =
      psi x * psibar x * (dψ e (x, 1) * dψ e (x, -1)) := by
  set A := psi x
  set B := psibar x
  set P := ψ (sh (Pi.single e 1) (x, 1))
  set Q := ψ (sh (Pi.single e 1) (x, -1))
  have hA : A * A = 0 := ψ_mul_self _
  have hB : B * B = 0 := ψ_mul_self _
  have hBA : B * A = -(A * B) := ψ_anticomm _ _
  have hBP : B * P = -(P * B) := ψ_anticomm _ _
  have e1 : A * B * (P * B) = 0 := by
    rw [show A * B * (P * B) = A * (B * P) * B by noncomm_ring, hBP,
      show A * -(P * B) * B = -(A * P * (B * B)) by noncomm_ring, hB, mul_zero, neg_zero]
  have e2 : A * B * (A * Q) = 0 := by
    rw [show A * B * (A * Q) = A * (B * A) * Q by noncomm_ring, hBA,
      show A * -(A * B) * Q = -((A * A) * B * Q) by noncomm_ring, hA, zero_mul, zero_mul,
      neg_zero]
  have e3 : A * B * (A * B) = 0 := by
    rw [show A * B * (A * B) = A * (B * A) * B by noncomm_ring, hBA,
      show A * -(A * B) * B = -((A * A) * (B * B)) by noncomm_ring, hA, zero_mul, neg_zero]
  have : dψ e (x, 1) * dψ e (x, -1) = P * Q - P * B - A * Q + A * B := by
    simp only [dψ, A, B, P, Q, psi, psibar]; noncomm_ring
  rw [this, mul_add, mul_sub, mul_sub, e1, e2, e3]; abel

/-- `‖ψ_x ψ̄_x ψ_{x+e} ψ̄_{x+e}‖_{T(ℓ)} ≤ ℓ^4 h^{-2}`. -/
theorem tNorm_four_le (hp : 1 ≤ p) (hh : 0 < h) (hℓ : 0 < ℓ) (e : E) (x : X) :
    tNorm E p h ℓ
        (psi x * psibar x * (ψ (sh (Pi.single e 1) (x, 1)) * ψ (sh (Pi.single e 1) (x, -1)))) ≤
      ENNReal.ofReal (ℓ ^ 4 * h⁻¹ ^ 2) := by
  rw [four_eq]
  refine (tNorm_mul_le hh hℓ _ _).trans ?_
  refine (mul_le_mul' (tNorm_psi_psibar_le hh hℓ x) (tNorm_mul_le hh hℓ _ _)).trans ?_
  calc ENNReal.ofReal (ℓ ^ 2) * (tNorm E p h ℓ (dψ e (x, 1)) * tNorm E p h ℓ (dψ e (x, -1)))
      ≤ ENNReal.ofReal (ℓ ^ 2) * (ENNReal.ofReal (ℓ * h⁻¹) * ENNReal.ofReal (ℓ * h⁻¹)) := by
        gcongr <;> exact tNorm_dψ_le hp hh hℓ e _
    _ = ENNReal.ofReal (ℓ ^ 4 * h⁻¹ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end

end Grassmann
