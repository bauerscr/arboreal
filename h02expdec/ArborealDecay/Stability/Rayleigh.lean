module

public import ArborealDecay.Stability.Operator

/-!
# The Rayleigh inequality for real stable multi-affine polynomials (§2.D)

If `p : MvPolynomial σ ℝ` is multi-affine and real stable, then for `i ≠ j` and every real point
`x`, `(∂ᵢ p)(x) (∂ⱼ p)(x) - p(x) (∂ᵢ ∂ⱼ p)(x) ≥ 0`.

Proof: evaluate at `x + i ε` and restrict to the `(i, j)`-plane, apply the closed inequality
`TwoVarZeroFree.im_mul_conj_nonneg`, and let `ε → 0⁺`.

We also show that the Rayleigh inequality passes from `p = p₀ + X k * p₁` to the coefficient
`p₁` (§2.D, last paragraph).
-/

@[expose] public section

open MvPolynomial Filter Topology

namespace ArborealDecay.Stability

noncomputable section

variable {σ : Type*} [DecidableEq σ]

/-- The Rayleigh combination `∂ᵢ p ∂ⱼ p - p ∂ᵢ ∂ⱼ p` at a point. -/
@[expose] def rayleighForm {R : Type*} [CommRing R] (p : MvPolynomial σ R) (i j : σ)
    (x : σ → R) : R :=
  eval x (pderiv i p) * eval x (pderiv j p) - eval x p * eval x (pderiv i (pderiv j p))

/-- `p` satisfies the Rayleigh inequality for `(i, j)` at all real points. -/
@[expose] def RayleighAt (p : MvPolynomial σ ℝ) (i j : σ) : Prop :=
  ∀ x : σ → ℝ, 0 ≤ rayleighForm p i j x

theorem eval_map_ofReal (q : MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval (fun k => (x k : ℂ)) (q.map Complex.ofRealHom) = (eval x q : ℂ) := by
  rw [MvPolynomial.eval_map]
  have := MvPolynomial.eval₂_comp_left Complex.ofRealHom (RingHom.id ℝ) x q
  exact this.symm

/-- **Rayleigh inequality** for real stable multi-affine polynomials. -/
theorem IsRealStable.rayleighForm_nonneg {p : MvPolynomial σ ℝ} (hp : IsMultiAffine p)
    (hs : IsRealStable p) {i j : σ} (hij : i ≠ j) (x : σ → ℝ) :
    0 ≤ rayleighForm p i j x := by
  obtain ⟨p₀₀, p₁₀, p₀₁, p₁₁, hdec, -⟩ := exists_isTwoVarDecomp hij (hp i) (hp j)
  have hdecC := hdec.map Complex.ofRealHom
  let z : ℝ → σ → ℂ := fun ε k => (x k : ℂ) + (ε : ℂ) * Complex.I
  let N : ℝ → ℝ := fun ε =>
    (((eval (z ε) (p₀₀.map Complex.ofRealHom)) + Complex.I * eval (z ε) (p₁₀.map Complex.ofRealHom)) *
      (starRingEnd ℂ) (eval (z ε) (p₀₁.map Complex.ofRealHom) + Complex.I * eval (z ε) (p₁₁.map Complex.ofRealHom))).im
  have hzc : Continuous z := by
    unfold z; fun_prop
  have hNc : Continuous N := by
    have hev : ∀ q : MvPolynomial σ ℂ, Continuous fun ε => eval (z ε) q := fun q =>
      (MvPolynomial.continuous_eval q).comp hzc
    unfold N
    have := hev (p₀₀.map Complex.ofRealHom); have := hev (p₁₀.map Complex.ofRealHom); have := hev (p₀₁.map Complex.ofRealHom)
    have := hev (p₁₁.map Complex.ofRealHom)
    fun_prop
  have hpos : ∀ ε : ℝ, 0 < ε → 0 ≤ N ε := by
    intro ε hε
    apply TwoVarZeroFree.im_mul_conj_nonneg
    intro u v hu hv
    rw [← hdecC.eval_update hij]
    apply hs
    intro k
    by_cases hkj : k = j
    · subst hkj; simpa using hv
    · by_cases hki : k = i
      · subst hki; simpa [Function.update_of_ne hkj] using hu
      · simpa [Function.update_of_ne hkj, Function.update_of_ne hki, z] using hε
  have h0 : 0 ≤ N 0 := by
    refine ge_of_tendsto (hNc.tendsto 0 |>.mono_left nhdsWithin_le_nhds : Tendsto N (𝓝[>] 0) _) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using hpos ε hε
  have hz0 : z 0 = fun k => (x k : ℂ) := by funext k; simp [z]
  have hN0 : N 0 = eval x p₁₀ * eval x p₀₁ - eval x p₀₀ * eval x p₁₁ := by
    simp only [N, hz0, eval_map_ofReal]
    simp [Complex.mul_im]
    ring
  rw [hN0] at h0
  unfold rayleighForm
  rw [hdec.rayleigh_eq hij]
  exact h0

/-- A quadratic that is nonnegative everywhere has nonnegative leading coefficient. -/
theorem nonneg_of_forall_quadratic_nonneg {α β γ : ℝ}
    (h : ∀ t : ℝ, 0 ≤ α + β * t + γ * t ^ 2) : 0 ≤ γ := by
  by_contra hγ
  have hγ : γ < 0 := not_le.mp hγ
  set M : ℝ := (|β| + |α|) / (-γ) + 1 with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ (|β| + |α|) / (-γ) := div_nonneg (by positivity) (by linarith)
    linarith
  have hM2 : |β| + |α| < -γ * M := by
    have : (|β| + |α|) / (-γ) < M := by linarith
    rw [div_lt_iff₀ (by linarith)] at this
    linarith [mul_comm M (-γ)]
  have h1 := h M
  have h2 : α ≤ |α| * M := by nlinarith [le_abs_self α, abs_nonneg α]
  have h3 : β * M ≤ |β| * M := by nlinarith [le_abs_self β]
  nlinarith

/-- **Rayleigh for coefficient polynomials**: if `p = p₀ + X k * p₁` with `p₀, p₁` free of `X k`
satisfies the Rayleigh inequality for `(i, j)` (with `i, j ≠ k`) at all real points, then so
does `p₁`. -/
theorem RayleighAt.of_decomp {p p₀ p₁ : MvPolynomial σ ℝ} {k i j : σ}
    (hk : p = p₀ + X k * p₁) (h0 : p₀.degreeOf k = 0) (h1 : p₁.degreeOf k = 0)
    (hik : i ≠ k) (hjk : j ≠ k) (h : RayleighAt p i j) : RayleighAt p₁ i j := by
  intro x
  have fr : ∀ q : MvPolynomial σ ℝ, q.degreeOf k = 0 → ∀ l, (pderiv l q).degreeOf k = 0 :=
    fun q hq l => Nat.le_zero.mp ((degreeOf_pderiv_le _ _ _).trans hq.le)
  have dI : pderiv i p = pderiv i p₀ + X k * pderiv i p₁ := by
    rw [hk]; simp [Derivation.leibniz, pderiv_X_of_ne hik.symm]
  have dJ : pderiv j p = pderiv j p₀ + X k * pderiv j p₁ := by
    rw [hk]; simp [Derivation.leibniz, pderiv_X_of_ne hjk.symm]
  have dIJ : pderiv i (pderiv j p) =
      pderiv i (pderiv j p₀) + X k * pderiv i (pderiv j p₁) := by
    rw [dJ]; simp [Derivation.leibniz, pderiv_X_of_ne hik.symm]
  have key : ∀ t : ℝ, 0 ≤ (eval x (pderiv i p₀) + t * eval x (pderiv i p₁)) *
        (eval x (pderiv j p₀) + t * eval x (pderiv j p₁)) -
      (eval x p₀ + t * eval x p₁) *
        (eval x (pderiv i (pderiv j p₀)) + t * eval x (pderiv i (pderiv j p₁))) := by
    intro t
    have := h (Function.update x k t)
    unfold rayleighForm at this
    rw [dIJ, dI, dJ, hk] at this
    simp only [map_add, map_mul, eval_X, Function.update_self,
      eval_update_of_degreeOf_eq_zero h0, eval_update_of_degreeOf_eq_zero h1,
      eval_update_of_degreeOf_eq_zero (fr _ h0 _), eval_update_of_degreeOf_eq_zero (fr _ h1 _),
      eval_update_of_degreeOf_eq_zero (fr _ (fr _ h0 _) _),
      eval_update_of_degreeOf_eq_zero (fr _ (fr _ h1 _) _)] at this
    exact this
  unfold rayleighForm
  generalize eval x (pderiv i p₀) = b₀ at key
  generalize eval x (pderiv i p₁) = b₁ at key ⊢
  generalize eval x (pderiv j p₀) = c₀ at key
  generalize eval x (pderiv j p₁) = c₁ at key ⊢
  generalize eval x (pderiv i (pderiv j p₀)) = d₀ at key
  generalize eval x (pderiv i (pderiv j p₁)) = d₁ at key ⊢
  generalize eval x p₀ = a₀ at key
  generalize eval x p₁ = a₁ at key ⊢
  exact nonneg_of_forall_quadratic_nonneg (α := b₀ * c₀ - a₀ * d₀)
    (β := b₀ * c₁ + b₁ * c₀ - a₀ * d₁ - a₁ * d₀) (γ := b₁ * c₁ - a₁ * d₁) (fun t => by
      have := key t; nlinarith [this])

end

end ArborealDecay.Stability
