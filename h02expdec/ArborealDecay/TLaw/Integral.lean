module

public import ArborealDecay.TLaw.Elem

/-!
# Analytic facts about the density of the pinned `t`-law

Continuity and positivity of `density`, the log form `density = exp (logDensity)`, and the
passage between the real expectation `expect` and `[0,∞]`-valued integrals.
-/

open Finset Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem continuous_Phi (w : V → V → ℝ) : Continuous (Phi w) := by
  unfold Phi; fun_prop

theorem continuous_D (w : V → V → ℝ) (ρ : V) : Continuous (D w ρ) := by
  unfold D
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : i = k
  · simp only [Hmat, of_apply, h, ↓reduceIte]; fun_prop
  · simp only [Hmat, of_apply, h, ↓reduceIte]; fun_prop

/-- The normalization `(2π)^{-|V∖ρ|/2}`. -/
noncomputable abbrev normC (ρ : V) : ℝ := (2 * π) ^ (-(Fintype.card {i // i ≠ ρ} : ℝ) / 2)

theorem normC_pos (ρ : V) : 0 < normC ρ := rpow_pos_of_pos (by positivity) _

/-- `log` of the density: `-Φ(τ̂) + a log D(τ̂) + log (2π)^{-n/2}`. -/
noncomputable def logDensity (w : V → V → ℝ) (ρ : V) (a : ℝ) (τ : {i // i ≠ ρ} → ℝ) : ℝ :=
  -Phi w (ext ρ τ) + a * log (D w ρ (ext ρ τ)) + log (normC ρ)

theorem density_eq_exp {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) (a : ℝ) (τ : {i // i ≠ ρ} → ℝ) :
    density w ρ a τ = exp (logDensity w ρ a τ) := by
  rw [density, logDensity, exp_add, exp_add, exp_log (normC_pos ρ),
    rpow_def_of_pos (D_pos hW hconn ρ _), mul_comm (log _) a]

theorem density_pos {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) (a : ℝ) (τ : {i // i ≠ ρ} → ℝ) : 0 < density w ρ a τ := by
  rw [density_eq_exp hW hconn]; exact exp_pos _

theorem continuous_density {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) (a : ℝ) : Continuous (density w ρ a) := by
  have h1 : Continuous fun τ => D w ρ (ext ρ τ) := (continuous_D w ρ).comp (continuous_ext ρ)
  have h2 : Continuous fun τ => Phi w (ext ρ τ) := (continuous_Phi w).comp (continuous_ext ρ)
  unfold density
  refine ((continuous_exp.comp h2.neg).mul (h1.rpow_const fun τ =>
    Or.inl (D_pos hW hconn ρ _).ne')).mul continuous_const

/-- From the real-valued normalization `E[g] = 1` (with `g ≥ 0` continuous) to the identity
`∫⁻ g · density = Z` in `[0,∞]`, together with `0 < Z < ∞`. -/
theorem lintegral_eq_Z_of_expect_eq_one {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) (a : ℝ) {g : ({i // i ≠ ρ} → ℝ) → ℝ}
    (hg0 : ∀ τ, 0 ≤ g τ) (hgc : Continuous g) (h : expect w ρ a g = 1) :
    (∫⁻ τ, ENNReal.ofReal (g τ * density w ρ a τ)) = Z w ρ a ∧ Z w ρ a ≠ 0 ∧ Z w ρ a ≠ ⊤ := by
  unfold expect at h
  have hZ : (Z w ρ a).toReal ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero, zero_mul] at h; exact zero_ne_one h
  have hI : (∫ τ, g τ * density w ρ a τ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
  have hint : Integrable (fun τ => g τ * density w ρ a τ) := by
    by_contra hni; exact hI (integral_undef hni)
  have hcont : Continuous fun τ => g τ * density w ρ a τ := hgc.mul (continuous_density hW hconn ρ a)
  have hnn : 0 ≤ᵐ[volume] fun τ => g τ * density w ρ a τ :=
    Filter.Eventually.of_forall fun τ => mul_nonneg (hg0 τ) (density_pos hW hconn ρ a τ).le
  rw [integral_eq_lintegral_of_nonneg_ae hnn hcont.aestronglyMeasurable] at h
  have hfin := hint.lintegral_lt_top
  have hZ' := (ENNReal.toReal_ne_zero.1 hZ)
  refine ⟨?_, hZ'.1, hZ'.2⟩
  have : (∫⁻ τ, ENNReal.ofReal (g τ * density w ρ a τ)).toReal = (Z w ρ a).toReal := by
    field_simp at h; linarith
  exact (ENNReal.toReal_eq_toReal_iff' hfin.ne hZ'.2).1 this

/-- From a `[0,∞]` bound `∫⁻ g · density ≤ B · Z` (with `0 < Z < ∞`) to integrability and the
real bound `E[g] ≤ B`. -/
theorem expect_le_of_lintegral_le {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) (a : ℝ) {g : ({i // i ≠ ρ} → ℝ) → ℝ}
    (hg0 : ∀ τ, 0 ≤ g τ) (hgc : Continuous g) {B : ℝ} (hB : 0 ≤ B) (hZ0 : Z w ρ a ≠ 0)
    (hZt : Z w ρ a ≠ ⊤)
    (h : (∫⁻ τ, ENNReal.ofReal (g τ * density w ρ a τ)) ≤ ENNReal.ofReal B * Z w ρ a) :
    Integrable (fun τ => g τ * density w ρ a τ) ∧ expect w ρ a g ≤ B := by
  have hcont : Continuous fun τ => g τ * density w ρ a τ := hgc.mul (continuous_density hW hconn ρ a)
  have hnn : 0 ≤ᵐ[volume] fun τ => g τ * density w ρ a τ :=
    Filter.Eventually.of_forall fun τ => mul_nonneg (hg0 τ) (density_pos hW hconn ρ a τ).le
  have hfin : (∫⁻ τ, ENNReal.ofReal (g τ * density w ρ a τ)) < ⊤ :=
    lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZt.lt_top)
  refine ⟨⟨hcont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩, ?_⟩
  unfold expect
  rw [integral_eq_lintegral_of_nonneg_ae hnn hcont.aestronglyMeasurable]
  have hZpos : 0 < (Z w ρ a).toReal := ENNReal.toReal_pos hZ0 hZt
  have := (ENNReal.toReal_le_toReal hfin.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZt)).2 h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at this
  rw [inv_mul_le_iff₀ hZpos]
  linarith

end ArborealDecay.TLaw
