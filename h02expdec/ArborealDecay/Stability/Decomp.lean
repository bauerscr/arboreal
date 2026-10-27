module

public import ArborealDecay.Stability.Basic

/-!
# Two-variable decomposition of multi-affine polynomials

For `i ≠ j` and a polynomial `p` of degree `≤ 1` in `X i` and in `X j`, we write
`p = p₀₀ + X i * p₁₀ + X j * p₀₁ + X i * X j * p₁₁` with all four pieces free of `X i` and `X j`,
and `p₁₁ = ∂ᵢ ∂ⱼ p`. We derive the pointwise formula for the restriction to the `(i, j)`-plane
and the closed forms of the Rayleigh combination.
-/

@[expose] public section

open MvPolynomial

namespace ArborealDecay.Stability

noncomputable section

variable {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ]

/-- Evaluation does not depend on a variable that the polynomial does not involve. -/
theorem eval_update_of_degreeOf_eq_zero {q : MvPolynomial σ R} {i : σ} (h : q.degreeOf i = 0)
    (z : σ → R) (t : R) : eval (Function.update z i t) q = eval z q := by
  have hv : i ∉ q.vars := by
    rw [mem_vars_iff_degreeOf_ne_zero]; simpa using h
  have := eval₂Hom_congr' (f₁ := RingHom.id R) (f₂ := RingHom.id R)
    (g₁ := Function.update z i t) (g₂ := z) (p₁ := q) (p₂ := q) rfl ?_ rfl
  · simpa using this
  · intro k hk _
    have : k ≠ i := fun e => hv (e ▸ hk)
    simp [Function.update_of_ne this]

/-- `p₀₀ + X i * p₁₀ + X j * p₀₁ + X i * X j * p₁₁` is a decomposition of `p` along `i, j`. -/
structure IsTwoVarDecomp (i j : σ) (p p₀₀ p₁₀ p₀₁ p₁₁ : MvPolynomial σ R) : Prop where
  eq : p = p₀₀ + X i * p₁₀ + X j * p₀₁ + X i * X j * p₁₁
  i₀₀ : p₀₀.degreeOf i = 0
  j₀₀ : p₀₀.degreeOf j = 0
  i₁₀ : p₁₀.degreeOf i = 0
  j₁₀ : p₁₀.degreeOf j = 0
  i₀₁ : p₀₁.degreeOf i = 0
  j₀₁ : p₀₁.degreeOf j = 0
  i₁₁ : p₁₁.degreeOf i = 0
  j₁₁ : p₁₁.degreeOf j = 0

theorem IsTwoVarDecomp.map {S : Type*} [CommRing S] (f : R →+* S) {i j : σ}
    {p p₀₀ p₁₀ p₀₁ p₁₁ : MvPolynomial σ R} (h : IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁) :
    IsTwoVarDecomp i j (p.map f) (p₀₀.map f) (p₁₀.map f) (p₀₁.map f) (p₁₁.map f) where
  eq := by rw [h.eq]; simp
  i₀₀ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.i₀₀.le)
  j₀₀ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.j₀₀.le)
  i₁₀ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.i₁₀.le)
  j₁₀ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.j₁₀.le)
  i₀₁ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.i₀₁.le)
  j₀₁ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.j₀₁.le)
  i₁₁ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.i₁₁.le)
  j₁₁ := Nat.le_zero.mp ((degreeOf_map_le f _ _).trans h.j₁₁.le)

section Decomp

variable {i j : σ} {p p₀₀ p₁₀ p₀₁ p₁₁ : MvPolynomial σ R}

theorem eval_update_of_free {q : MvPolynomial σ R} (hi : q.degreeOf i = 0) (hj : q.degreeOf j = 0)
    (z : σ → R) (x y : R) :
    eval (Function.update (Function.update z i x) j y) q = eval z q := by
  rw [eval_update_of_degreeOf_eq_zero hj, eval_update_of_degreeOf_eq_zero hi]

/-- Restriction of a decomposed polynomial to the `(i, j)`-plane through `z`. -/
theorem IsTwoVarDecomp.eval_update (h : IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁) (hij : i ≠ j)
    (z : σ → R) (x y : R) :
    eval (Function.update (Function.update z i x) j y) p =
      eval z p₀₀ + eval z p₁₀ * x + eval z p₀₁ * y + eval z p₁₁ * x * y := by
  rw [h.eq]
  simp only [map_add, map_mul, eval_X, Function.update_self,
    Function.update_of_ne hij, eval_update_of_free h.i₀₀ h.j₀₀, eval_update_of_free h.i₁₀ h.j₁₀,
    eval_update_of_free h.i₀₁ h.j₀₁, eval_update_of_free h.i₁₁ h.j₁₁]
  ring

theorem IsTwoVarDecomp.pderiv_i (h : IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁) (hij : i ≠ j) :
    pderiv i p = p₁₀ + X j * p₁₁ := by
  have z : ∀ {q : MvPolynomial σ R}, q.degreeOf i = 0 → pderiv i q = 0 := fun hq =>
    pderiv_eq_zero_of_notMem_vars (by rw [mem_vars_iff_degreeOf_ne_zero]; simpa using hq)
  rw [h.eq]
  simp only [map_add, Derivation.leibniz, pderiv_X_self, pderiv_X_of_ne hij.symm, z h.i₀₀,
    z h.i₁₀, z h.i₀₁, z h.i₁₁, smul_eq_mul]
  ring

theorem IsTwoVarDecomp.pderiv_j (h : IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁) (hij : i ≠ j) :
    pderiv j p = p₀₁ + X i * p₁₁ := by
  have z : ∀ {q : MvPolynomial σ R}, q.degreeOf j = 0 → pderiv j q = 0 := fun hq =>
    pderiv_eq_zero_of_notMem_vars (by rw [mem_vars_iff_degreeOf_ne_zero]; simpa using hq)
  rw [h.eq]
  simp only [map_add, Derivation.leibniz, pderiv_X_self, pderiv_X_of_ne hij, z h.j₀₀,
    z h.j₁₀, z h.j₀₁, z h.j₁₁, smul_eq_mul]
  ring

theorem IsTwoVarDecomp.pderiv_ij (h : IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁) (hij : i ≠ j) :
    pderiv i (pderiv j p) = p₁₁ := by
  have z : ∀ {q : MvPolynomial σ R}, q.degreeOf i = 0 → pderiv i q = 0 := fun hq =>
    pderiv_eq_zero_of_notMem_vars (by rw [mem_vars_iff_degreeOf_ne_zero]; simpa using hq)
  rw [h.pderiv_j hij]
  simp only [map_add, Derivation.leibniz, pderiv_X_self, z h.i₀₁, z h.i₁₁, smul_eq_mul]
  ring

/-- The Rayleigh combination of a decomposed polynomial is `p₁₀ p₀₁ - p₀₀ p₁₁`. -/
theorem IsTwoVarDecomp.rayleigh_eq (h : IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁) (hij : i ≠ j)
    (z : σ → R) :
    eval z (pderiv i p) * eval z (pderiv j p) - eval z p * eval z (pderiv i (pderiv j p)) =
      eval z p₁₀ * eval z p₀₁ - eval z p₀₀ * eval z p₁₁ := by
  rw [h.pderiv_ij hij, h.pderiv_i hij, h.pderiv_j hij]
  conv_lhs => rw [h.eq]
  simp only [map_add, map_mul, eval_X]
  ring

end Decomp

/-- Existence of the two-variable decomposition. -/
theorem exists_isTwoVarDecomp {i j : σ} (hij : i ≠ j) {p : MvPolynomial σ R}
    (hi : p.degreeOf i ≤ 1) (hj : p.degreeOf j ≤ 1) :
    ∃ p₀₀ p₁₀ p₀₁ p₁₁ : MvPolynomial σ R, IsTwoVarDecomp i j p p₀₀ p₁₀ p₀₁ p₁₁ ∧
      p₁₁ = pderiv i (pderiv j p) := by
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ = p - X i * pderiv i p := ⟨_, rfl⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁, q₁ = pderiv i p := ⟨_, rfl⟩
  have hq₀i : q₀.degreeOf i = 0 := hq₀ ▸ degreeOf_sub_X_mul_pderiv_self hi
  have hq₁i : q₁.degreeOf i = 0 := hq₁ ▸ degreeOf_pderiv_self_of_le_one hi
  have hq₀j : q₀.degreeOf j ≤ 1 :=
    hq₀ ▸ (degreeOf_sub_X_mul_pderiv_le_of_ne hij p).trans hj
  have hq₁j : q₁.degreeOf j ≤ 1 := hq₁ ▸ (degreeOf_pderiv_le _ _ _).trans hj
  have hp : p = q₀ + X i * q₁ := by rw [hq₀, hq₁]; ring
  have a1 : (q₀ - X j * pderiv j q₀).degreeOf i = 0 :=
    Nat.le_zero.mp ((degreeOf_sub_X_mul_pderiv_le_of_ne hij.symm q₀).trans hq₀i.le)
  have a2 : (q₀ - X j * pderiv j q₀).degreeOf j = 0 := degreeOf_sub_X_mul_pderiv_self hq₀j
  have a3 : (pderiv j q₀).degreeOf i = 0 :=
    Nat.le_zero.mp ((degreeOf_pderiv_le _ _ _).trans hq₀i.le)
  have a4 : (pderiv j q₀).degreeOf j = 0 := degreeOf_pderiv_self_of_le_one hq₀j
  have b1 : (q₁ - X j * pderiv j q₁).degreeOf i = 0 :=
    Nat.le_zero.mp ((degreeOf_sub_X_mul_pderiv_le_of_ne hij.symm q₁).trans hq₁i.le)
  have b2 : (q₁ - X j * pderiv j q₁).degreeOf j = 0 := degreeOf_sub_X_mul_pderiv_self hq₁j
  have b3 : (pderiv j q₁).degreeOf i = 0 :=
    Nat.le_zero.mp ((degreeOf_pderiv_le _ _ _).trans hq₁i.le)
  have b4 : (pderiv j q₁).degreeOf j = 0 := degreeOf_pderiv_self_of_le_one hq₁j
  refine ⟨q₀ - X j * pderiv j q₀, q₁ - X j * pderiv j q₁, pderiv j q₀, pderiv j q₁,
    ⟨?_, a1, a2, b1, b2, a3, a4, b3, b4⟩, ?_⟩
  · rw [hp]; ring
  · rw [hq₁, pderiv_comm]

end

end ArborealDecay.Stability
