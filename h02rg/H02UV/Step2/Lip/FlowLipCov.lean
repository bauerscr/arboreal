import Step2.Lip.FlowLipNorm
import Step2.Lip.CdrLip
import Step2.Lip.Lip
import Step2.Lip.LipW

/-!
# Covariance families along a segment (Lipschitz bounds, part 3)

For the Lipschitz bounds in the covariance we interpolate linearly between two covariances
`C` and `C'` whose difference is a good covariance at a *small* field scale `ℓ_Δ`
(`prop_C5_lip`: `ℓ_Δ² ∝ ∑_k ρ^{j-k} |ζ_k - ζ'_k|`). Then `C + z (C' - C)` is a good covariance
at `ℓ_C + |z|^{1/2} ℓ_Δ` (`GoodCov2.line`), so a radius `|z| ≤ R` with `R ℓ_Δ² ≤ τ² ℓ_C²` is
admissible, and the Cauchy estimate gives a Lipschitz bound `∝ ℓ_Δ²/ℓ_C²`.

`cauchy_lip` is the radius choice for a joint segment in all the arguments: if the output is
bounded by `B` on the doubled domain and the relative distance is `s`, then the difference of
the outputs is at most `4 B s`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Sums of good covariances -/

section Sum

theorem norm_toLp_le {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (x : WithLp 2 (H₁ × H₂)) :
    ‖x‖ ≤ ‖(WithLp.ofLp x).1‖ + ‖(WithLp.ofLp x).2‖ := by
  have h : ‖x‖ ^ 2 = ‖(WithLp.ofLp x).1‖ ^ 2 + ‖(WithLp.ofLp x).2‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 x
  have h1 := norm_nonneg (WithLp.ofLp x).1
  have h2 := norm_nonneg (WithLp.ofLp x).2
  have h0 := norm_nonneg x
  have : ‖x‖ ^ 2 ≤ (‖(WithLp.ofLp x).1‖ + ‖(WithLp.ofLp x).2‖) ^ 2 := by
    rw [h]; nlinarith [mul_nonneg h1 h2]
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 this

theorem gvec_prod {Λ : Type*} [Fintype Λ] {H₁ H₂ : Type} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (F₁ : Λ → H₁)
    (F₂ : Λ → H₂) (f : Λ → ℝ) :
    WithLp.ofLp (gvec (fun x => WithLp.toLp 2 (F₁ x, F₂ x)) f) = (gvec F₁ f, gvec F₂ f) := by
  have e := map_sum (WithLp.linearEquiv 2 ℂ (H₁ × H₂))
    (fun x => (f x : ℂ) • WithLp.toLp 2 (F₁ x, F₂ x)) univ
  simp only [map_smul] at e
  rw [gvec, gvec, gvec]
  refine (e.trans ?_)
  ext <;> simp [WithLp.linearEquiv, Prod.fst_sum, Prod.snd_sum]

/-- **The sum of good covariances is good**, at the sum of the field scales. -/
theorem GoodCov2.add {j : ℕ} {ℓ₁ ℓ₂ : ℝ} {C₁ C₂ : Matrix (Lam d L N) (Lam d L N) ℂ}
    (h₁ : GoodCov2 j ℓ₁ C₁) (h₂ : GoodCov2 j ℓ₂ C₂) : GoodCov2 j (ℓ₁ + ℓ₂) (C₁ + C₂) := by
  obtain ⟨H₁, i₁, i₁', F₁, G₁, hG₁, hB₁⟩ := h₁.gram
  obtain ⟨H₂, i₂, i₂', F₂, G₂, hG₂, hB₂⟩ := h₂.gram
  refine ⟨⟨WithLp 2 (H₁ × H₂), inferInstance, inferInstance,
    fun x => WithLp.toLp 2 (F₁ x, F₂ x), fun y => WithLp.toLp 2 (G₁ y, G₂ y), ?_, ?_⟩, ?_⟩
  · intro x y
    rw [Matrix.add_apply, hG₁, hG₂, WithLp.prod_inner_apply]
  · intro α hα x
    obtain ⟨a1, a2⟩ := hB₁ α hα x
    obtain ⟨b1, b2⟩ := hB₂ α hα x
    refine ⟨(norm_toLp_le _).trans ?_, (norm_toLp_le _).trans ?_⟩
    · rw [gvec_prod]; dsimp only; rw [add_mul]; exact add_le_add a1 b1
    · rw [gvec_prod]; dsimp only; rw [add_mul]; exact add_le_add a2 b2
  · intro hjN x y hxy
    rw [Matrix.add_apply, h₁.range hjN x y hxy, h₂.range hjN x y hxy, add_zero]

/-- **Good covariances along a segment.** If `C` is good at `ℓ_C` and `C' - C` is good at `ℓ_Δ`,
then `C + z (C' - C)` is good at `ℓ_C + R^{1/2} ℓ_Δ` for `|z| ≤ R`. -/
theorem GoodCov2.line {j : ℕ} {ℓC ℓΔ R : ℝ} {C C' : Matrix (Lam d L N) (Lam d L N) ℂ}
    (hC : GoodCov2 j ℓC C) (hΔ : GoodCov2 j ℓΔ (C' - C)) (hℓΔ : 0 ≤ ℓΔ) {z : ℂ} (hz : ‖z‖ ≤ R) :
    GoodCov2 j (ℓC + Real.sqrt R * ℓΔ) (C + z • (C' - C)) :=
  hC.add ((hΔ.smul z).mono (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hz) hℓΔ))

theorem TInv.line {C C' : Matrix (Lam d L N) (Lam d L N) ℂ} (h : TInv C) (h' : TInv C') (z : ℂ) :
    TInv (C + z • (C' - C)) := fun t x y => by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, h t x y, h' t x y]

theorem CSym.line {C C' : Matrix (Lam d L N) (Lam d L N) ℂ} (h : CSym C) (h' : CSym C') (z : ℂ) :
    CSym (C + z • (C' - C)) := fun T hT x y => by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, h T hT x y, h' T hT x y]

theorem symm_line {C C' : Matrix (Lam d L N) (Lam d L N) ℂ} (h : ∀ x y, C x y = C y x)
    (h' : ∀ x y, C' x y = C' y x) (z : ℂ) (x y : Lam d L N) :
    (C + z • (C' - C)) x y = (C + z • (C' - C)) y x := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, h x y, h' x y]

theorem cov_line_diff {C C' : Matrix (Lam d L N) (Lam d L N) ℂ} (x y : Lam d L N) :
    Differentiable ℂ (fun z : ℂ => (C + z • (C' - C)) x y) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

end Sum

/-! ### The choice of the radius -/

/-- **Radius choice for a joint Cauchy estimate.** If `X ≤ 2B` and `X ≤ B/(R - 1)` for all
`R ≥ 2` with `R s ≤ 1`, then `X ≤ 4 B s`. -/
theorem cauchy_lip {X : ENNReal} {B s : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hfar : X ≤ ENNReal.ofReal (2 * B))
    (hline : ∀ R : ℝ, 2 ≤ R → R * s ≤ 1 → X ≤ ENNReal.ofReal (B / (R - 1))) :
    X ≤ ENNReal.ofReal (4 * B * s) := by
  by_cases hbig : 1 < 2 * s
  · exact hfar.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  · push Not at hbig
    have key : ∀ R : ℝ, 2 ≤ R → R * s ≤ 1 → X ≤ ENNReal.ofReal (2 * B / R) := fun R hR hRs =>
      (hline R hR hRs).trans (ENNReal.ofReal_le_ofReal (by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith))
    have h := le_of_radius (X := X) (M := 2 * B) (s := s) (T := 1) (by positivity) hs one_pos
      (by linarith) key
    exact h.trans (ENNReal.ofReal_le_ofReal (by rw [div_one]; nlinarith))

/-- The same for real-valued quantities. -/
theorem cauchy_lip_real {X B s : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s) (hfar : X ≤ 2 * B)
    (hline : ∀ R : ℝ, 2 ≤ R → R * s ≤ 1 → X ≤ B / (R - 1)) : X ≤ 4 * B * s := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (by positivity)
  have h := cauchy_lip (X := ENNReal.ofReal X) hB hs (ENNReal.ofReal_le_ofReal hfar)
    fun R hR hRs => ENNReal.ofReal_le_ofReal (hline R hR hRs)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

end

end Step2
