import Loc.EstTaylor
import Loc.EstLocCoeffs

/-!
# Polynomials of degree `≤ 2` are annihilated by `F - Loc_X F`

If all pairings `μ_β(G)` vanish, then `∑_{x,y} G_{(x,+)(y,-)} P(ℓx, ℓy) = 0` for every polynomial
`P` of degree `≤ 2` in the lifted coordinates, in particular for the Taylor polynomial `taylor2`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

/-- The lifted coordinates of the pair `(x, y)`. -/
def wxy (b x y : Lam d L N) : Fin 2 → Zd d := ![rep (x - b), rep (y - b)]

/-- The coordinate functions. -/
def coordF (k : Fin 2) (i : Fin d) (w : Fin 2 → Zd d) : ℂ := (w k i : ℂ)

/-- The functional `f ↦ ∑_{x,y} G_{(x,+)(y,-)} f(ℓx, ℓy)`. -/
def omegaL (b : Lam d L N) (G : Alg d L N) : ((Fin 2 → Zd d) → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, ∑ y, cf2 G x y * f (wxy b x y)
  map_add' f g := by
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sum, RingHom.id_apply]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem omegaL_apply (b : Lam d L N) (G : Alg d L N) (f : (Fin 2 → Zd d) → ℂ) :
    omegaL b G f = ∑ x, ∑ y, cf2 G x y * f (wxy b x y) := rfl

theorem coordF_wxy0 (b x y : Lam d L N) (i : Fin d) :
    coordF 0 i (wxy b x y) = (lift b x i : ℂ) := by
  simp [coordF, wxy, lift]
theorem coordF_wxy1 (b x y : Lam d L N) (i : Fin d) :
    coordF 1 i (wxy b x y) = (lift b y i : ℂ) := by
  simp [coordF, wxy, lift]

section Vanish

variable {b : Lam d L N} {G : Alg d L N} (hμ : ∀ β : Mono d, mu b β G = 0)
include hμ

theorem omegaL_one : omegaL b G (fun _ => 1) = 0 := by
  have := hμ Mono.c
  simpa [mu, Qpoly, omegaL_apply] using this

theorem omegaL_coord (k : Fin 2) (i : Fin d) : omegaL b G (coordF k i) = 0 := by
  fin_cases k
  · have := hμ (Mono.a1 i)
    simpa [mu, Qpoly, omegaL_apply, coordF_wxy0] using this
  · have := hμ (Mono.b1 i)
    simpa [mu, Qpoly, omegaL_apply, coordF_wxy1] using this

theorem omegaL_coord2 (k : Fin 2) (i : Fin d) (k' : Fin 2) (i' : Fin d) :
    omegaL b G (fun w => coordF k i w * coordF k' i' w) = 0 := by
  fin_cases k <;> fin_cases k'
  · have := hμ (Mono.a2 s(i, i'))
    rcases eq_or_ne i i' with rfl | hii
    · simp only [mu, Qpoly, Sym2.lift_mk, if_true] at this
      simp only [omegaL_apply]
      have e : ∀ x y, cf2 G x y * (coordF 0 i (wxy b x y) * coordF 0 i (wxy b x y)) =
          2 * (cf2 G x y * ((lift b x i ^ 2 / 2 : ℝ) : ℂ)) := fun x y => by
        rw [coordF_wxy0]; push_cast; ring
      simp only [Fin.zero_eta, Fin.isValue] at e ⊢
      rw [sum_congr rfl fun x _ => sum_congr rfl fun y _ => e x y]
      simp only [← mul_sum]
      rw [this, mul_zero]
    · simpa [mu, Qpoly, hii, omegaL_apply, coordF_wxy0] using this
  · have := hμ (Mono.m2 i i')
    simpa [mu, Qpoly, omegaL_apply, coordF_wxy0, coordF_wxy1] using this
  · have := hμ (Mono.m2 i' i)
    simp only [mu, Qpoly] at this
    simp only [omegaL_apply]
    rw [← this]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, coordF_wxy0, coordF_wxy1]
    push_cast
    ring
  · have := hμ (Mono.b2 s(i, i'))
    rcases eq_or_ne i i' with rfl | hii
    · simp only [mu, Qpoly, Sym2.lift_mk, if_true] at this
      simp only [omegaL_apply]
      have e : ∀ x y, cf2 G x y * (coordF 1 i (wxy b x y) * coordF 1 i (wxy b x y)) =
          2 * (cf2 G x y * ((lift b y i ^ 2 / 2 : ℝ) : ℂ)) := fun x y => by
        rw [coordF_wxy1]; push_cast; ring
      simp only [Fin.mk_one, Fin.isValue] at e ⊢
      rw [sum_congr rfl fun x _ => sum_congr rfl fun y _ => e x y]
      simp only [← mul_sum]
      rw [this, mul_zero]
    · simpa [mu, Qpoly, hii, omegaL_apply, coordF_wxy1] using this

/-- `F - Loc_X F` annihilates the Taylor polynomial. -/
theorem omegaL_taylor2 (Φ : (Fin 2 → Zd d) → ℂ) : omegaL b G (taylor2 Φ) = 0 := by
  have e : taylor2 Φ = (Φ 0) • (fun _ => (1 : ℂ)) + ∑ k, ∑ i, (Dp k i Φ 0) • coordF k i +
      (1 / 2 : ℂ) • ∑ k, ∑ i, ∑ k', ∑ i', (Dp k' i' (Dp k i Φ) 0) •
        (fun w => coordF k i w * coordF k' i' w) -
      (1 / 2 : ℂ) • ∑ k, ∑ i, (Dp k i (Dp k i Φ) 0) • coordF k i := by
    funext w
    simp only [taylor2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      coordF, mul_one]
    congr 1
    congr 1
    congr 1
    refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun k' _ =>
      sum_congr rfl fun i' _ => by ring
  rw [e, map_sub, map_add, map_add, map_smul, map_smul, map_smul, omegaL_one hμ, map_sum, map_sum,
    map_sum]
  simp only [map_sum, map_smul, omegaL_coord hμ, omegaL_coord2 hμ, smul_zero, sum_const_zero,
    add_zero, sub_zero]

end Vanish

end

end Loc
