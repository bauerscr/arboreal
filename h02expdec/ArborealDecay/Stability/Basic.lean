module

public import Mathlib

/-!
# Stable and multi-affine polynomials: definitions and basic API

`IsStable p` says that the complex polynomial `p` has no zero in the product of open upper
half-planes. `IsRealStable p` is the same for a real polynomial, viewed as a complex one.
`IsMultiAffine p` says that every variable has degree at most `1`.

We also set up the decomposition of a multi-affine polynomial in two variables
`p = p₀₀ + X i * p₁₀ + X j * p₀₁ + X i * X j * p₁₁` with `p₁₁ = ∂ᵢ ∂ⱼ p`.
-/

@[expose] public section

open MvPolynomial

namespace ArborealDecay.Stability

noncomputable section

variable {σ : Type*}

/-- A complex polynomial is stable if it has no zero with all coordinates in the open upper
half-plane. (The zero polynomial is *not* stable.) -/
@[expose] def IsStable (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, 0 < (z i).im) → MvPolynomial.eval z p ≠ 0

/-- A complex polynomial is stable or zero. -/
@[expose] def IsStableOrZero (p : MvPolynomial σ ℂ) : Prop := p = 0 ∨ IsStable p

/-- A real polynomial is real stable if it is stable as a complex polynomial. -/
@[expose] def IsRealStable (p : MvPolynomial σ ℝ) : Prop :=
  IsStable (p.map Complex.ofRealHom)

/-- A polynomial is multi-affine if it has degree at most one in every variable. -/
@[expose] def IsMultiAffine {R : Type*} [CommSemiring R] (p : MvPolynomial σ R) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

theorem isRealStable_iff_aeval (p : MvPolynomial σ ℝ) :
    IsRealStable p ↔ ∀ z : σ → ℂ, (∀ i, 0 < (z i).im) → MvPolynomial.aeval z p ≠ 0 := by
  unfold IsRealStable IsStable
  refine forall_congr' fun z => forall_congr' fun _ => ?_
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]
  rfl

theorem IsStable.ne_zero [Nonempty σ] {p : MvPolynomial σ ℂ} (h : IsStable p) : p ≠ 0 := by
  rintro rfl
  exact h (fun _ => Complex.I) (fun _ => by simp) (by simp)

theorem isStableOrZero_zero : IsStableOrZero (0 : MvPolynomial σ ℂ) := Or.inl rfl

theorem IsStable.isStableOrZero {p : MvPolynomial σ ℂ} (h : IsStable p) : IsStableOrZero p :=
  Or.inr h

theorem degreeOf_map_le {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : MvPolynomial σ R) (i : σ) : (p.map f).degreeOf i ≤ p.degreeOf i := by
  rw [degreeOf_le_iff]
  intro m hm
  exact le_degreeOf_of_mem_support i (MvPolynomial.support_map_subset _ _ hm)

theorem IsMultiAffine.map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {p : MvPolynomial σ R} (hp : IsMultiAffine p) :
    IsMultiAffine (p.map f) := fun i => (degreeOf_map_le f p i).trans (hp i)

/-! ### Degree API for `pderiv` -/

section Degree

variable {R : Type*} [CommRing R] [DecidableEq σ]

theorem degreeOf_pderiv_le (i j : σ) (p : MvPolynomial σ R) :
    (pderiv i p).degreeOf j ≤ p.degreeOf j := by
  rw [degreeOf_le_iff]
  intro m hm
  have hc : (pderiv i p).coeff m ≠ 0 := by simpa using hm
  rw [coeff_pderiv] at hc
  have h1 : p.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hc
  have := le_degreeOf_of_mem_support j (s := m + Finsupp.single i 1) (by simpa using h1)
  have h2 : m j ≤ (m + Finsupp.single i 1 : σ →₀ ℕ) j := by simp
  exact h2.trans this

theorem degreeOf_pderiv_self_of_le_one {i : σ} {p : MvPolynomial σ R}
    (hp : p.degreeOf i ≤ 1) : (pderiv i p).degreeOf i = 0 := by
  apply Nat.le_zero.mp; rw [degreeOf_le_iff]
  intro m hm
  have hc : (pderiv i p).coeff m ≠ 0 := by simpa using hm
  rw [coeff_pderiv] at hc
  have h1 : p.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hc
  have := (degreeOf_le_iff.mp hp) (m + Finsupp.single i 1) (by simpa using h1)
  simp at this
  omega

theorem degreeOf_X_mul_le_of_ne {i j : σ} (h : i ≠ j) (q : MvPolynomial σ R) :
    (X i * q).degreeOf j ≤ q.degreeOf j := by
  refine (degreeOf_mul_le _ _ _).trans ?_
  simp [degreeOf_X_of_ne h.symm]

/-- The part of `p` not involving `X i`: `p - X i * ∂ᵢ p`. -/
theorem degreeOf_sub_X_mul_pderiv_self {i : σ} {p : MvPolynomial σ R}
    (hp : p.degreeOf i ≤ 1) : (p - X i * pderiv i p).degreeOf i = 0 := by
  apply Nat.le_zero.mp; rw [degreeOf_le_iff]
  intro m hm
  by_contra hmi
  have hmi : 1 ≤ m i := by omega
  have hc : (p - X i * pderiv i p).coeff m ≠ 0 := by simpa using hm
  rw [coeff_sub, coeff_X_mul'] at hc
  have hmem : i ∈ m.support := by simp; omega
  rw [if_pos hmem, coeff_pderiv] at hc
  have e1 : (m - Finsupp.single i 1 : σ →₀ ℕ) + Finsupp.single i 1 = m := by
    ext k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [hk]
  rw [e1] at hc
  have e2 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : R) + 1 = (m i : R) := by
    have : (m - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = m i := by simp; omega
    have := congrArg (Nat.cast (R := R)) this
    push_cast at this
    exact this
  rw [e2] at hc
  by_cases h1 : m i = 1
  · rw [h1] at hc; simp at hc
  · have : p.coeff m = 0 := by
      by_contra hne
      have := (degreeOf_le_iff.mp hp) m (by simpa using hne)
      omega
    rw [this] at hc; simp at hc

theorem degreeOf_sub_X_mul_pderiv_le_of_ne {i j : σ} (h : i ≠ j) (p : MvPolynomial σ R) :
    (p - X i * pderiv i p).degreeOf j ≤ p.degreeOf j := by
  refine (degreeOf_sub_le _ _ _).trans (max_le le_rfl ?_)
  exact (degreeOf_X_mul_le_of_ne h _).trans (degreeOf_pderiv_le _ _ _)

theorem pderiv_comm (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have : ⁅(pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)), (pderiv j : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    simp only [Derivation.commutator_apply, Derivation.leibniz, pderiv_X, LinearMap.sub_apply,
      Derivation.coeFn_coe]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) => D p) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h2
  exact sub_eq_zero.mp h2

end Degree

end

end ArborealDecay.Stability
