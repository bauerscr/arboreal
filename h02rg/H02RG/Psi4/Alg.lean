import PtCorr.TwoPtOne
import PtCorr.TwoPtTwo
import Suscept.Main
import Psi4.SumParts

/-!
# Algebraic helpers for Section `sec:proofs`

* `one_add_ne_zero_of_norm_le`: `|ũ| ≤ 1/2 ⇒ 1 + ũ ≠ 0` and `|1/(1+ũ)| ≤ 2`;
* `trunc_eq`, `trunc_bound`: the truncated 4-point function
  `⟨ψ̄_0ψ_0 ψ̄_xψ_x⟩ - ⟨ψ̄_0ψ_0⟩⟨ψ̄_xψ_x⟩` from `e:2pt-b` and the two 1-point formulas;
* `twoPt_one_eq`, `twoPt_one_bound`: `⟨ψ̄_0ψ_x⟩` from `e:2pt-a`;
* real-power bookkeeping (`rpow_two_add_mul`, `T_le_of_mass`, …).
-/

namespace Psi4

noncomputable section

open Finset

/-- `|u| ≤ 1/2` implies `1 + u ≠ 0` and `|(1+u)⁻¹| ≤ 2`. -/
theorem one_add_ne_zero_of_norm_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    1 + u ≠ 0 ∧ ‖(1 + u)⁻¹‖ ≤ 2 := by
  have h1 : (1 : ℝ) ≤ ‖1 + u‖ + ‖u‖ := by
    have := norm_sub_le (1 + u) u
    rw [add_sub_cancel_right, norm_one] at this
    exact this
  have h2 : (1 / 2 : ℝ) ≤ ‖1 + u‖ := by linarith
  have hne : 1 + u ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; linarith
  refine ⟨hne, ?_⟩
  rw [norm_inv]
  have hp : 0 < ‖1 + u‖ := by linarith
  rw [inv_le_comm₀ hp (by norm_num)]
  linarith

/-- The truncated 4-point function: exact algebra. -/
theorem trunc_eq {u τ W Cv la lb ga gb Ea Eb E1 E2 av4 av1a av1b : ℂ} (hu : 1 + u ≠ 0)
    (h4 : av4 = -la * lb * W ^ 2 + ga * gb + (-2 * la * lb * W + la * gb + lb * ga) * τ / (1 + u) +
      E1 + E2 / (1 + u))
    (ha : av1a = ga + (la * τ + Ea) / (1 + u)) (hb : av1b = gb + (lb * τ + Eb) / (1 + u))
    (hW : W = Cv - τ) :
    av4 - av1a * av1b = -la * lb * Cv ^ 2 + E1 +
      (la * lb * (τ * u * (1 + u)⁻¹) * (2 * Cv - τ * u * (1 + u)⁻¹) + E2 * (1 + u)⁻¹ -
        (ga * Eb + gb * Ea) * (1 + u)⁻¹ - (la * τ * Eb + lb * τ * Ea + Ea * Eb) * ((1 + u)⁻¹) ^ 2) := by
  subst h4 ha hb hW
  field_simp
  ring

/-- The truncated 4-point function: the bound on the remainder. -/
theorem trunc_bound {u τ Cv la lb ga gb Ea Eb E2 : ℂ} {β θ ρ Cu Λ G K0 Ce B C2 : ℝ}
    (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (hCu : 0 ≤ Cu) (hCe : 0 ≤ Ce) (hC2 : 0 ≤ C2)
    (hu : ‖u‖ ≤ Cu * β * θ) (hu2 : ‖u‖ ≤ 1 / 2) (hv : ‖(1 + u)⁻¹‖ ≤ 2) (hτ : ‖τ‖ ≤ 1)
    (hla : ‖la‖ ≤ Λ) (hlb : ‖lb‖ ≤ Λ) (hga : ‖ga‖ ≤ G) (hgb : ‖gb‖ ≤ G) (hCv : ‖Cv‖ ≤ K0)
    (hEa : ‖Ea‖ ≤ Ce * β * θ) (hEb : ‖Eb‖ ≤ Ce * β * θ) (hEB : ‖Eb‖ ≤ B)
    (hE2 : ‖E2‖ ≤ C2 * β * (2 * θ + ρ)) :
    ‖la * lb * (τ * u * (1 + u)⁻¹) * (2 * Cv - τ * u * (1 + u)⁻¹) + E2 * (1 + u)⁻¹ -
        (ga * Eb + gb * Ea) * (1 + u)⁻¹ - (la * τ * Eb + lb * τ * Ea + Ea * Eb) * ((1 + u)⁻¹) ^ 2‖ ≤
      (Λ * Λ * (2 * Cu) * (2 * K0 + 1) + 4 * C2 + 4 * G * Ce + 4 * (2 * Λ * Ce + B * Ce)) *
        β * (θ + ρ) := by
  set v := (1 + u)⁻¹ with hvdef
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hla
  have hG : 0 ≤ G := (norm_nonneg _).trans hga
  have hK0 : 0 ≤ K0 := (norm_nonneg _).trans hCv
  have hB : 0 ≤ B := (norm_nonneg _).trans hEB
  have hX : 0 ≤ β * θ := mul_nonneg hβ hθ
  -- `|τ u v| ≤ 1` and `≤ 2 Cu β θ`
  have htuv : ‖τ * u * v‖ ≤ 2 * Cu * (β * θ) := by
    rw [norm_mul, norm_mul]
    calc ‖τ‖ * ‖u‖ * ‖v‖ ≤ 1 * (Cu * β * θ) * 2 := by gcongr
      _ = 2 * Cu * (β * θ) := by ring
  have htuv1 : ‖τ * u * v‖ ≤ 1 := by
    rw [norm_mul, norm_mul]
    calc ‖τ‖ * ‖u‖ * ‖v‖ ≤ 1 * (1 / 2) * 2 := by gcongr
      _ = 1 := by ring
  have h2C : ‖2 * Cv - τ * u * v‖ ≤ 2 * K0 + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_two]; linarith
  have t1 : ‖la * lb * (τ * u * v) * (2 * Cv - τ * u * v)‖ ≤
      Λ * Λ * (2 * Cu) * (2 * K0 + 1) * (β * θ) := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖la‖ * ‖lb‖ * ‖τ * u * v‖ * ‖2 * Cv - τ * u * v‖ ≤
        Λ * Λ * (2 * Cu * (β * θ)) * (2 * K0 + 1) := by gcongr
      _ = _ := by ring
  have t2 : ‖E2 * v‖ ≤ 4 * C2 * (β * (θ + ρ)) := by
    rw [norm_mul]
    calc ‖E2‖ * ‖v‖ ≤ C2 * β * (2 * θ + ρ) * 2 := by gcongr
      _ ≤ 4 * C2 * (β * (θ + ρ)) := by nlinarith [mul_nonneg hC2 (mul_nonneg hβ hρ)]
  have t3 : ‖(ga * Eb + gb * Ea) * v‖ ≤ 4 * G * Ce * (β * θ) := by
    rw [norm_mul]
    have : ‖ga * Eb + gb * Ea‖ ≤ G * (Ce * β * θ) + G * (Ce * β * θ) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]; gcongr
    calc ‖ga * Eb + gb * Ea‖ * ‖v‖ ≤ (G * (Ce * β * θ) + G * (Ce * β * θ)) * 2 := by gcongr
      _ = 4 * G * Ce * (β * θ) := by ring
  have t4 : ‖(la * τ * Eb + lb * τ * Ea + Ea * Eb) * v ^ 2‖ ≤
      4 * (2 * Λ * Ce + B * Ce) * (β * θ) := by
    rw [norm_mul, norm_pow]
    have : ‖la * τ * Eb + lb * τ * Ea + Ea * Eb‖ ≤
        Λ * 1 * (Ce * β * θ) + Λ * 1 * (Ce * β * θ) + (Ce * β * θ) * B := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
      · rw [norm_mul, norm_mul, norm_mul, norm_mul]; gcongr
      · rw [norm_mul]; gcongr
    calc ‖la * τ * Eb + lb * τ * Ea + Ea * Eb‖ * ‖v‖ ^ 2 ≤
        (Λ * 1 * (Ce * β * θ) + Λ * 1 * (Ce * β * θ) + (Ce * β * θ) * B) * 2 ^ 2 := by gcongr
      _ = 4 * (2 * Λ * Ce + B * Ce) * (β * θ) := by ring
  have hsum := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)
  refine hsum.trans ?_
  have hθρ : β * θ ≤ β * (θ + ρ) := mul_le_mul_of_nonneg_left (by linarith) hβ
  have c1 : 0 ≤ Λ * Λ * (2 * Cu) * (2 * K0 + 1) := by positivity
  have c3 : 0 ≤ 4 * G * Ce := by positivity
  have c4 : 0 ≤ 4 * (2 * Λ * Ce + B * Ce) := by positivity
  have e1 := mul_le_mul_of_nonneg_left hθρ c1
  have e3 := mul_le_mul_of_nonneg_left hθρ c3
  have e4 := mul_le_mul_of_nonneg_left hθρ c4
  have : (Λ * Λ * (2 * Cu) * (2 * K0 + 1) + 4 * C2 + 4 * G * Ce + 4 * (2 * Λ * Ce + B * Ce)) *
      β * (θ + ρ) = Λ * Λ * (2 * Cu) * (2 * K0 + 1) * (β * (θ + ρ)) + 4 * C2 * (β * (θ + ρ)) +
        4 * G * Ce * (β * (θ + ρ)) + 4 * (2 * Λ * Ce + B * Ce) * (β * (θ + ρ)) := by ring
  rw [this]
  linarith

/-- `⟨ψ̄_0ψ_x⟩` from `e:2pt-a`: exact algebra, with `W = Cov(0,x) - τ`. -/
theorem twoPt_one_eq {u τ W Cv E1 E2 av : ℂ} (hu : 1 + u ≠ 0)
    (h : av = W + (τ + E2) / (1 + u) + E1) (hW : W = Cv - τ) :
    av = Cv + E1 + (E2 * (1 + u)⁻¹ - τ * u * (1 + u)⁻¹) := by
  subst h hW
  field_simp
  ring

/-! ### Real powers -/

theorem rpow_neg_add_mul {L : ℝ} (hL : 0 < L) (s t : ℝ) (N : ℕ) :
    L ^ (-((s + t) * N)) = L ^ (-(s * N)) * L ^ (-(t * N)) := by
  rw [← Real.rpow_add hL]; ring_nf

theorem rpow_neg_mul_le_one {L : ℝ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    L ^ (-(s * N)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hL (by
    have : 0 ≤ s * (N : ℝ) := mul_nonneg hs (Nat.cast_nonneg N)
    linarith)

/-- `(L^{2N})⁻¹ = L^{-2N}` as a real power. -/
theorem inv_pow_two_mul {L : ℝ} (hL : 0 < L) (N : ℕ) :
    ((L ^ (2 * N) : ℝ))⁻¹ = L ^ (-((2 : ℝ) * N)) := by
  rw [Real.rpow_neg hL.le, ← Real.rpow_natCast]; push_cast; ring_nf

end

end Psi4
