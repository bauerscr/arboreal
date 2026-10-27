import Suscept.ZNN
import Flow.Main

/-!
# Reality of the bulk quantities of the susceptibility analysis

For real coupling constants `V₀` (`V₀.conj = V₀`), in particular for `V₀ = V₀^c(m², b)` with real
`b` (by `Flow.thm_flow_real`), the quantities `u_N`, `k_N^0`, `k_N^2`, `ã_{N,N}` and
`ũ_{N,N}` of `Suscept.ZNN` are real. More precisely each of them commutes with conjugation of
`V₀` (`uN_conj`, `kN0_conj`, `kN2_conj`, `atN_conj`, `utN_conj`).
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow

local notation "cj" => starRingEnd ℂ

variable {d L : ℕ} [NeZero L]

theorem c2_conjN {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (F : Grassmann.N Λ) :
    c2 (conjN F) = cj (c2 F) := by
  simp [c2, map_sum]

section

variable (hd : 1 ≤ d) (hL : 3 ≤ L)
include hd hL

theorem VN_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : VN d L N msq V₀.conj = (VN d L N msq V₀).conj := by
  simp only [VN, flowN_conj hd hL N msq V₀ N le_rfl]

theorem KN_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : KN d L N msq V₀.conj = conjE (KN d L N msq V₀) := by
  simp only [KN, flowN_conj hd hL N msq V₀ N le_rfl, conjA_apply]

theorem aN_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : aN d L N msq V₀.conj = cj (aN d L N msq V₀) := by
  simp only [aN, VN_conj hd hL, Vcoup.conj_a]

theorem uN_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : uN d L N msq V₀.conj = cj (uN d L N msq V₀) := by
  simp only [uN, map_sum]
  exact sum_congr rfl fun j hj => uflow_conj hd hL msq V₀ (mem_range.1 hj)

theorem kN0_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : kN0 d L N msq V₀.conj = cj (kN0 d L N msq V₀) := by
  rw [kN0, kN0, KN_conj hd hL, coe_conjE, ε_conjN]

theorem kN2_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : kN2 d L N msq V₀.conj = cj (kN2 d L N msq V₀) := by
  rw [kN2, kN2, KN_conj hd hL, coe_conjE, c2_conjN]

theorem atN_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : atN d L N msq V₀.conj = cj (atN d L N msq V₀) := by
  rw [atN, atN, aN_conj hd hL, kN2_conj hd hL, _root_.map_sub, map_div₀, map_natCast]

theorem utN_conj (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : utN d L N msq V₀.conj = cj (utN d L N msq V₀) := by
  rw [utN, utN, kN0_conj hd hL, atN_conj hd hL, _root_.map_add, _root_.map_mul, Complex.conj_ofReal]

/-- The quantities are real for real `V₀`. -/
theorem im_eq_zero_of_real {V₀ : Vcoup} (hV : V₀.conj = V₀) (N : ℕ) (msq : ℝ) :
    (uN d L N msq V₀).im = 0 ∧ (kN0 d L N msq V₀).im = 0 ∧ (kN2 d L N msq V₀).im = 0 ∧
      (atN d L N msq V₀).im = 0 ∧ (utN d L N msq V₀).im = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine Complex.conj_eq_iff_im.1 ?_
  · rw [← uN_conj hd hL, hV]
  · rw [← kN0_conj hd hL, hV]
  · rw [← kN2_conj hd hL, hV]
  · rw [← atN_conj hd hL, hV]
  · rw [← utN_conj hd hL, hV]

/-- **Reality for `V₀ = V₀^c(m², b)`, `b` real**: `u_N`, `k_N^0`, `k_N^2`, `ã_{N,N}` and `ũ_{N,N}`
are real. -/
theorem im_eq_zero_V0c {V₀c : ℝ → ℂ → Vcoup}
    (hconj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj) (N : ℕ) (msq b : ℝ) :
    (uN d L N msq (V₀c msq b)).im = 0 ∧ (kN0 d L N msq (V₀c msq b)).im = 0 ∧
      (kN2 d L N msq (V₀c msq b)).im = 0 ∧ (atN d L N msq (V₀c msq b)).im = 0 ∧
      (utN d L N msq (V₀c msq b)).im = 0 :=
  im_eq_zero_of_real hd hL (conj_V0c_real hconj msq b) N msq

end

end

end Suscept
