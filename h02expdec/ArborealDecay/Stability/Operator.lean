module

public import ArborealDecay.Stability.Decomp
public import ArborealDecay.Stability.TwoVar

/-!
# The operator `1 - c ∂ᵢ ∂ⱼ` preserves stability (Corollary A2)

For a multi-affine polynomial `p` which is stable or zero, `i ≠ j` and a real `c ≥ 0`, the
polynomial `p - c • ∂ᵢ ∂ⱼ p` is again multi-affine and stable or zero.
-/

@[expose] public section

open MvPolynomial

namespace ArborealDecay.Stability

noncomputable section

variable {σ : Type*} [DecidableEq σ]

/-- A real polynomial is real stable or zero. -/
@[expose] def IsRealStableOrZero (p : MvPolynomial σ ℝ) : Prop := p = 0 ∨ IsRealStable p

theorem isRealStableOrZero_iff (p : MvPolynomial σ ℝ) :
    IsRealStableOrZero p ↔ IsStableOrZero (p.map Complex.ofRealHom) := by
  unfold IsRealStableOrZero IsStableOrZero IsRealStable
  refine or_congr ?_ Iff.rfl
  exact ⟨fun h => by rw [h, map_zero], fun h =>
    MvPolynomial.map_injective _ Complex.ofReal_injective (by rw [h, map_zero])⟩

/-- Evaluation of a real scalar multiple. -/
theorem eval_real_smul (c : ℝ) (q : MvPolynomial σ ℂ) (z : σ → ℂ) :
    eval z (c • q) = (c : ℂ) * eval z q := by
  rw [Algebra.smul_def]
  simp [MvPolynomial.algebraMap_eq]

/-- Restricting a stable polynomial to an `(i, j)`-plane through a point of `H ^ σ` yields a
two-variable zero-free polynomial. -/
theorem IsStable.twoVarZeroFree {p : MvPolynomial σ ℂ} (hs : IsStable p) {i j : σ} (hij : i ≠ j)
    {p₀₀ p₁₀ p₀₁ p₁₁ : MvPolynomial σ ℂ} (hdec : IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁)
    {w : σ → ℂ} (hw : ∀ k, 0 < (w k).im) :
    TwoVarZeroFree (eval w p₀₀) (eval w p₁₀) (eval w p₀₁) (eval w p₁₁) := by
  intro x y hx hy
  rw [← hdec.eval_update hij]
  apply hs
  intro k
  by_cases hkj : k = j
  · subst hkj; simpa using hy
  · by_cases hki : k = i
    · subst hki; simpa [Function.update_of_ne hkj] using hx
    · simpa [Function.update_of_ne hkj, Function.update_of_ne hki] using hw k

/-- Corollary A2, stability part (complex coefficients). -/
theorem IsStableOrZero.sub_smul_pderiv_pderiv {p : MvPolynomial σ ℂ} (hp : IsMultiAffine p)
    (hs : IsStableOrZero p) {i j : σ} (hij : i ≠ j) {c : ℝ} (hc : 0 ≤ c) :
    IsStableOrZero (p - c • pderiv i (pderiv j p)) := by
  rcases hs with rfl | hs
  · left; simp
  right
  intro w hw
  obtain ⟨p₀₀, p₁₀, p₀₁, p₁₁, hdec, hD⟩ := exists_isTwoVarDecomp hij (hp i) (hp j)
  have hfree := hs.twoVarZeroFree hij hdec hw
  have := (hfree.sub_real_mul hc) (w i) (w j) (hw i) (hw j)
  have hp' := hdec.eval_update hij w (w i) (w j)
  simp only [Function.update_eq_self] at hp'
  rw [map_sub, eval_real_smul, ← hD, hp']
  intro h0; apply this; linear_combination h0

theorem real_smul_eq_C_mul (c : ℝ) (q : MvPolynomial σ ℂ) : c • q = C (c : ℂ) * q := by
  rw [Algebra.smul_def]
  simp

/-- Corollary A2, multi-affinity part. -/
theorem IsMultiAffine.sub_C_mul_pderiv_pderiv {R : Type*} [CommRing R]
    {p : MvPolynomial σ R} (hp : IsMultiAffine p) (i j : σ) (c : R) :
    IsMultiAffine (p - C c * pderiv i (pderiv j p)) := fun k => by
  refine (degreeOf_sub_le _ _ _).trans (max_le (hp k) ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 : (C c : MvPolynomial σ R).degreeOf k = 0 := degreeOf_C _ _
  rw [h1, zero_add]
  exact ((degreeOf_pderiv_le _ _ _).trans ((degreeOf_pderiv_le _ _ _).trans (hp k)))

/-- Corollary A2, multi-affinity part, for a real scalar acting on a complex polynomial. -/
theorem IsMultiAffine.sub_smul_pderiv_pderiv {p : MvPolynomial σ ℂ} (hp : IsMultiAffine p)
    (i j : σ) (c : ℝ) : IsMultiAffine (p - c • pderiv i (pderiv j p)) := by
  rw [real_smul_eq_C_mul]
  exact hp.sub_C_mul_pderiv_pderiv i j (c : ℂ)

/-- Corollary A2, real-coefficient version. -/
theorem IsRealStableOrZero.sub_smul_pderiv_pderiv {p : MvPolynomial σ ℝ} (hp : IsMultiAffine p)
    (hs : IsRealStableOrZero p) {i j : σ} (hij : i ≠ j) {c : ℝ} (hc : 0 ≤ c) :
    IsRealStableOrZero (p - c • pderiv i (pderiv j p)) ∧
      IsMultiAffine (p - c • pderiv i (pderiv j p)) := by
  refine ⟨?_, by rw [smul_eq_C_mul]; exact hp.sub_C_mul_pderiv_pderiv i j c⟩
  rw [isRealStableOrZero_iff] at hs ⊢
  have := IsStableOrZero.sub_smul_pderiv_pderiv (hp.map Complex.ofRealHom) hs hij hc
  convert this using 1
  rw [map_sub, smul_eq_C_mul, real_smul_eq_C_mul, map_mul, MvPolynomial.map_C, pderiv_map,
    pderiv_map]
  rfl

end

end ArborealDecay.Stability
