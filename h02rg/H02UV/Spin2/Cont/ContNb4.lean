import Spin2.Cont.ContNa3
import Spin2.Pair.PairTop1

set_option autoImplicit false

/-!
# The reference zero mode at `h = 0` for any `y` (no coalescence condition)

`pairTop_E` gives `s_∅Ω ≠ 0` and `n_aΩ = r − γ_{a,N}` (`r = 0` at `h = 0`) only for
`N_h + 1 ≤ j_y`. At `h = 0` both follow for **every** `y` from the generating element at the top:
`n_a(W_top(ref)) = 0`, `s_∅W_top ≠ 0` (`pl2_WTop_facts`), `W_top = e^{−u_{N_h+1}}·lastO`,
`lastO = X·Ω` (`lastOF_eq_cst_zm`) and `γ_{0,N_h+1} + n_aX = γ_{a,N}` (`uA_add_nA_zCst`).

* **`nb_ref_zm`**: `s_∅(zZm) ≠ 0` and `n_a(zZm) = −γ_{a,N}` (`zZm = ω_{cQ}F_N`, pair `(0, y)`).
-/

set_option linter.unusedSectionVars false

namespace Spin2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist PtCorr2

variable {L N : ℕ} [NeZero L]

section Ref

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem nb_zmOF_zero (Nh : ℕ) (m b μ₀ : ℝ) (y : Lam 2 L N) :
    zmOF (R.withMsq m) (ptsX y) 0 (obsInit .two (zV b) (ptsX y)) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) = zZm R Nh m b μ₀ y := by
  unfold zmOF finOF zmC zZm zFin zCc
  rw [obsHistFrom_zero]

set_option maxHeartbeats 1000000 in
/-- **The reference zero mode at `h = 0`, any `y`.** -/
theorem nb_ref_zm {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh) (hL7 : 7 ≤ L)
    {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (y : Lam 2 L N) :
    sE (zZm R Nh m b μ₀ y) ≠ 0 ∧ nA (zZm R Nh m b μ₀ y) = -gamNa R Nh m b μ₀ y := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set o₀ := obsInit .two (zV b) (ptsX y) with ho₀d
  have ho₀ : o₀.IsObs := obsInit_isObs .two (zV b) (ptsX y)
  obtain ⟨s₁, a₁, -, -⟩ := pl2_WTop_facts (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0
    (ptsX y)
  have hu : bulk ((obsHistFrom (R.withMsq m) (ptsX y) 0 o₀ (Nh + 1) t).u) = 0 :=
    (obsHistFrom_isObs (R := R.withMsq m) (P := ptsX y) (j := 0) ho₀ t (Nh + 1)).u
  have hbn : bulk (-(obsHistFrom (R.withMsq m) (ptsX y) 0 o₀ (Nh + 1) t).u) = 0 := by
    rw [map_neg, hu, neg_zero]
  have eW : plWTop (R.withMsq m) (ptsX y) 0 o₀ Nh t =
      oexp (-(obsHistFrom (R.withMsq m) (ptsX y) 0 o₀ (Nh + 1) t).u) *
        lastOF (R.withMsq m) (ptsX y) 0 o₀ Nh t := rfl
  have hY : sE (lastOF (R.withMsq m) (ptsX y) 0 o₀ Nh t) ≠ 0 := by
    have e : sE (plWTop (R.withMsq m) (ptsX y) 0 o₀ Nh t) ≠ 0 := s₁
    rw [eW, sE_mul, (pl_sX_oexp_obs hbn).1, one_mul] at e
    exact e
  have hA : nA (plWTop (R.withMsq m) (ptsX y) 0 o₀ Nh t) = 0 := a₁
  rw [eW, na_nA_oexp_mul hu hY] at hA
  have eL : lastOF (R.withMsq m) (ptsX y) 0 o₀ Nh t =
      zCst R Nh m b μ₀ y (Nh + 1) * zZm R Nh m b μ₀ y := by
    rw [lastOF_eq_cst_zm]
    exact congrArg₂ (· * ·) (lastCstOF_zero_eq R Nh m b μ₀ y) (nb_zmOF_zero R Nh m b μ₀ y)
  rw [eL] at hY hA
  have hX : sE (zCst R Nh m b μ₀ y (Nh + 1)) ≠ 0 := by
    intro h; apply hY; rw [sE_mul, h, zero_mul]
  have hΩ : sE (zZm R Nh m b μ₀ y) ≠ 0 := by
    intro h; apply hY; rw [sE_mul, h, mul_zero]
  refine ⟨hΩ, ?_⟩
  rw [nA_mul hX hΩ] at hA
  have hg := uA_add_nA_zCst R Nh m b μ₀ y le_rfl hX
  have eu : uA R m b μ₀ y (Nh + 1) =
      -ε (((obsHistFrom (R.withMsq m) (ptsX y) 0 o₀ (Nh + 1) t).u : SA .two (Lam 2 L N)).a) := by
    unfold uA; rw [obsHistFrom_zero]; rfl
  rw [eu] at hg
  linear_combination hA - hg

end Ref

end

end Spin2
