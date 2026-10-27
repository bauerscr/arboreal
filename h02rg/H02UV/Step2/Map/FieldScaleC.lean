import Step2.Map.FieldScale

/-!
# Complex field rescalings and the principal square root

* `tNorm_sig_unit`: `‖σ_ω F‖ = ‖F‖` for `|ω| = 1` (phase invariance);
* `tNorm_sig_cscale`: `‖σ_a F‖_{T(ℓ)} = ‖F‖_{T(|a| ℓ)}` for `a ≠ 0`, and the versions for block
  families and activities;
* `csq`: the principal square root, `csq w ^ 2 = w`, `|csq w| = |w|^{1/2}`, continuous on the
  slit plane.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section Gen

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-- **Phase invariance**: `‖σ_ω F‖ = ‖F‖` for `|ω| = 1`. -/
theorem tNorm_sig_unit (hh : 0 ≤ h) (hℓ : 0 < ℓ) {ω : ℂ} (hω : ‖ω‖ = 1) (F : Grassmann.N X) :
    tNorm E p h ℓ (sig ω F) = tNorm E p h ℓ F := by
  refine le_antisymm (tNorm_sig_le hh hℓ hω.le F) ?_
  have hω0 : ω ≠ 0 := by intro h0; rw [h0, norm_zero] at hω; exact zero_ne_one hω
  have h1 : ‖ω⁻¹‖ ≤ 1 := by rw [norm_inv, hω, inv_one]
  have h2 := tNorm_sig_le (E := E) (p := p) hh hℓ h1 (sig ω F)
  rwa [sig_sig, inv_mul_cancel₀ hω0, sig_one] at h2

/-- `‖σ_a F‖_{T(ℓ)} = ‖F‖_{T(|a| ℓ)}` for `a ≠ 0`. -/
theorem tNorm_sig_cscale (hh : 0 ≤ h) (hℓ : 0 < ℓ) {a : ℂ} (ha : a ≠ 0) (F : Grassmann.N X) :
    tNorm E p h ℓ (sig a F) = tNorm E p h (‖a‖ * ℓ) F := by
  have hn : 0 < ‖a‖ := norm_pos_iff.2 ha
  have e : a = (a / (‖a‖ : ℂ)) * (‖a‖ : ℂ) := by
    rw [div_mul_cancel₀]; exact_mod_cast hn.ne'
  have hu : ‖a / (‖a‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne']
  have e' : sig a F = sig (a / (‖a‖ : ℂ)) (sig ((‖a‖ : ℝ) : ℂ) F) := by rw [sig_sig, ← e]
  rw [e', tNorm_sig_unit hh hℓ hu, tNorm_sig_eq hh hℓ hn]

end Gen

variable {d L N : ℕ} [NeZero L]

theorem Tj_sig_cscale {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℂ} (ha : a ≠ 0) (F : Alg d L N) :
    Tj d (L : ℝ) j ℓ (sig a F) = Tj d (L : ℝ) j (‖a‖ * ℓ) F :=
  tNorm_sig_cscale (by positivity) hℓ ha F

theorem Fnorm_sigF_cscale {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℂ} (ha : a ≠ 0) (F : Fam d L N) :
    Fnorm j ℓ (sigF a F) = Fnorm j (‖a‖ * ℓ) F := by
  unfold Fnorm; simp only [sigF, coe_sigE, Tj_sig_cscale hℓ ha]

theorem Knorm_sigK_cscale {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) {a : ℂ} (ha : a ≠ 0) (K : Act d L N) :
    Knorm j ℓ A (sigK a K) = Knorm j (‖a‖ * ℓ) A K := by
  unfold Knorm; simp only [sigK, coe_sigE, Tj_sig_cscale hℓ ha]

/-! ### The principal square root -/

/-- The principal square root. -/
def csq (w : ℂ) : ℂ := w ^ (2⁻¹ : ℂ)

theorem csq_sq (w : ℂ) : csq w ^ 2 = w := Complex.cpow_ofNat_inv_pow w 2

theorem csq_ne {w : ℂ} (hw : w ≠ 0) : csq w ≠ 0 := by
  intro h; have := csq_sq w; rw [h, zero_pow two_ne_zero] at this; exact hw this.symm

theorem one_add_mem_slitPlane {ζ : ℂ} (h : ‖ζ‖ < 1) : 1 + ζ ∈ Complex.slitPlane := by
  left
  have := Complex.abs_re_le_norm ζ
  have : (1 + ζ).re = 1 + ζ.re := by simp
  rw [this]
  have := (abs_le.1 (Complex.abs_re_le_norm ζ)).1
  linarith

theorem continuousAt_csq {w : ℂ} (hw : w ∈ Complex.slitPlane) : ContinuousAt csq w :=
  continuousAt_cpow_const hw

end

end Step2
