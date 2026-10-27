import Mathlib

/-!
# The polynomials `P_t` (`e:decomp-Pt`)

The finite range decomposition of Section `sec:frd` of `h02rg.tex` (Appendix `app:decomp`) is
built from a family of polynomials `P_t`, `t > 0`, of degree at most `t` such that
`1/λ = ∫_0^∞ t^2 P_t(λ) dt/t` and `0 ≤ P_t(u) ≤ O_s(1 + t^2 u)^{-s}` for `u ∈ [0, 2]`
(`e:decomp-Pt`).  `PtFamily` records these properties (together with the measurability needed to
integrate in `t`, and the positivity of the tails of the integral, which gives `t_N > 0`).
A family is constructed in `FRD.GreenBd`.
-/

namespace FRD

open MeasureTheory Set Polynomial

/-- A family of polynomials `P_t` with the properties `e:decomp-Pt`. -/
structure PtFamily where
  /-- The polynomial `P_t`. -/
  P : ℝ → ℝ[X]
  /-- `P_t` has degree at most `t`. -/
  natDegree_le : ∀ t, 0 < t → ((P t).natDegree : ℝ) ≤ t
  /-- `P_t ≥ 0` on `[0, 2]`. -/
  nonneg : ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2, 0 ≤ (P t).eval u
  /-- `P_t(u) ≤ O_s(1 + t^2 u)^{-s}` on `[0, 2]`. -/
  bound : ∀ s : ℝ, 0 ≤ s → ∃ K : ℝ, ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2,
    (P t).eval u ≤ K * (1 + t ^ 2 * u) ^ (-s)
  /-- `t ↦ P_t(u)` is measurable. -/
  measurable : ∀ u, Measurable fun t => (P t).eval u
  /-- `1/u = ∫_0^∞ t^2 P_t(u) dt/t`. -/
  integral_eq : ∀ u ∈ Ioc (0 : ℝ) 2, ∫ t in Ioi 0, t * (P t).eval u = 1 / u
  /-- The tails of the integral are positive. -/
  tail_pos : ∀ u ∈ Ioc (0 : ℝ) 2, ∀ T, 0 < T → 0 < ∫ t in Ioi T, t * (P t).eval u

end FRD
