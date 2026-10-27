module

public import ArborealDecay.Separator.Core
public import ArborealDecay.Separator.Diag
public import ArborealDecay.Stability.Rayleigh

/-!
# The stable separator lemma (`lem:stable-separator`, via supplement `thm:separator`)

Set-up step of the supplement: from `p` we form `a₀ = p(0,0,t,…,t)`, `a₁ = (∂ₓ p)(0,0,t,…,t)`,
`a₂ = (∂_y p)(0,0,t,…,t)`, `a₁₂ = (∂ₓ ∂_y p)(0,0,t,…,t)` and verify every hypothesis of
`separator_core`:

* degrees and top coefficients (`natDegree_diagHom_le`, `coeff_card_diagHom`, `htop`);
* `a₁ > 0` on `[0, ∞)` (nonnegative coefficients, positive coefficient of `x`);
* `a₁ a₂ - a₀ a₁₂ ≥ 0` (`thm:rayleigh` for the pair `x, y`, `lem:diag` (ii) first identity);
* `a₁₂ a₁' - a₁ a₁₂' ≥ 0` (`lem:rayleigh-deriv` for `∂ₓ p`, then `lem:diag` with distinguished
  variable `y`);
* `Δ_{x t} f ≥ 0` (`thm:rayleigh` for the pairs `x, s_j`, summed by `lem:diag` (ii));
* stability of `(x, y, t) ↦ p(x, y, t, …, t)` (`lem:ident` (i)).
-/

@[expose] public section

open MvPolynomial

namespace ArborealDecay.Separator

noncomputable section

open ArborealDecay.Stability

variable {ι : Type*}

theorem pderiv_pderiv_self_eq_zero {σ : Type*} [DecidableEq σ] {q : MvPolynomial σ ℝ} {v : σ}
    (hq : q.degreeOf v ≤ 1) : pderiv v (pderiv v q) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  rw [mem_vars_iff_degreeOf_ne_zero, not_not]
  exact degreeOf_pderiv_self_of_le_one hq

theorem coeff_nonneg_of_pos {σ : Type*} {p : MvPolynomial σ ℝ} (hma : ∀ v, p.degreeOf v ≤ 1)
    (hpos : ∀ d : σ →₀ ℕ, (∀ v, d v ≤ 1) → 0 < p.coeff d) (d : σ →₀ ℕ) : 0 ≤ p.coeff d := by
  by_cases hd : ∀ v, d v ≤ 1
  · exact (hpos d hd).le
  · by_cases hs : d ∈ p.support
    · exact absurd (le_one_of_mem_support hma hs) hd
    · rw [notMem_support_iff.mp hs]

/-- The chain-rule sum of Rayleigh forms along the diagonal (`lem:diag` (ii)). -/
theorem sum_rayleighForm_eq [Fintype ι] [DecidableEq ι] (q : MvPolynomial (Fin 2 ⊕ ι) ℝ)
    (i : Fin 2) (c₀ c₁ t : ℝ) :
    ∑ j : ι, rayleighForm q (Sum.inl i) (Sum.inr j) (Sum.elim ![c₀, c₁] (fun _ => t)) =
      (diagHom ι c₀ c₁ (pderiv (Sum.inl i) q)).eval t *
          (Polynomial.derivative (diagHom ι c₀ c₁ q)).eval t -
        (diagHom ι c₀ c₁ q).eval t *
          (Polynomial.derivative (diagHom ι c₀ c₁ (pderiv (Sum.inl i) q))).eval t := by
  have h1 : ∀ j : ι, eval (Sum.elim ![c₀, c₁] (fun _ => t))
      (pderiv (Sum.inl i) (pderiv (Sum.inr j) q)) =
      eval (Sum.elim ![c₀, c₁] (fun _ => t)) (pderiv (Sum.inr j) (pderiv (Sum.inl i) q)) := by
    intro j; rw [pderiv_comm]
  simp only [rayleighForm, Finset.sum_sub_distrib, h1, derivative_diagHom,
    Polynomial.eval_finsetSum, eval_diagHom, Finset.mul_sum]

/-- **Stable separator lemma** (`lem:stable-separator`), proved along the supplement's
alternative route `thm:separator`. -/
theorem stable_separator {ι : Type*} [Fintype ι] (p : MvPolynomial (Fin 2 ⊕ ι) ℝ)
    (hstab : ∀ z : Fin 2 ⊕ ι → ℂ, (∀ j, 0 < (z j).im) → MvPolynomial.aeval z p ≠ 0)
    (hma : ∀ v, p.degreeOf v ≤ 1)
    (hpos : ∀ d : Fin 2 ⊕ ι →₀ ℕ, (∀ v, d v ≤ 1) → 0 < p.coeff d)
    (c A B : ℝ) (hc : 0 < c) (hA : 0 < A) (hB : 0 < B)
    (htop :
      p.coeff (sMonomial ι + Finsupp.single (Sum.inl 0) 1 + Finsupp.single (Sum.inl 1) 1) = c ∧
      p.coeff (sMonomial ι + Finsupp.single (Sum.inl 0) 1) = c * B ∧
      p.coeff (sMonomial ι + Finsupp.single (Sum.inl 1) 1) = c * A ∧
      p.coeff (sMonomial ι) = c * A * B) :
    0 ≤ MvPolynomial.eval (Sum.elim ![-A, -B] 0) p := by
  classical
  -- `A > 0` is not needed (only `B > 0` is used, as noted in the supplement).
  have _ : 0 < A := hA
  obtain ⟨htop12, htop1, htop2, htop0⟩ := htop
  set x₀ : Fin 2 ⊕ ι := Sum.inl 0 with hx₀
  set y₀ : Fin 2 ⊕ ι := Sum.inl 1 with hy₀
  have hxy : x₀ ≠ y₀ := by simp [hx₀, hy₀]
  have hs : IsRealStable p := (isRealStable_iff_aeval p).mpr hstab
  have hmaD : ∀ (w : Fin 2 ⊕ ι) (q : MvPolynomial (Fin 2 ⊕ ι) ℝ), (∀ v, q.degreeOf v ≤ 1) →
      ∀ v, (pderiv w q).degreeOf v ≤ 1 :=
    fun w q hq v => (degreeOf_pderiv_le _ _ _).trans (hq v)
  set a0 := diagHom ι 0 0 p with ha0
  set a1 := diagHom ι 0 0 (pderiv x₀ p) with ha1
  set a2 := diagHom ι 0 0 (pderiv y₀ p) with ha2
  set a12 := diagHom ι 0 0 (pderiv x₀ (pderiv y₀ p)) with ha12
  have hsx : sMonomial ι x₀ = 0 := sMonomial_apply_inl 0
  have hsy : sMonomial ι y₀ = 0 := sMonomial_apply_inl 1
  -- top coefficients
  have ht12 : a12.coeff (Fintype.card ι) = c := by
    rw [ha12, coeff_card_diagHom (hmaD _ _ (hmaD _ _ hma)), coeff_pderiv, coeff_pderiv]
    simp [hsx, hsy, hxy.symm, htop12]
  have ht1 : a1.coeff (Fintype.card ι) = c * B := by
    rw [ha1, coeff_card_diagHom (hmaD _ _ hma), coeff_pderiv]
    simp [hsx, htop1]
  have ht2 : a2.coeff (Fintype.card ι) = c * A := by
    rw [ha2, coeff_card_diagHom (hmaD _ _ hma), coeff_pderiv]
    simp [hsy, htop2]
  have ht0 : a0.coeff (Fintype.card ι) = c * A * B := by
    rw [ha0, coeff_card_diagHom hma, htop0]
  -- positivity of `a₁` on `[0, ∞)`
  have hpos1 : ∀ t : ℝ, 0 ≤ t → 0 < a1.eval t := by
    intro t ht
    rw [ha1, eval_diagHom]
    have hcoeff : ∀ d, 0 ≤ (pderiv x₀ p).coeff d := by
      intro d
      rw [coeff_pderiv]
      exact mul_nonneg (coeff_nonneg_of_pos hma hpos _) (by positivity)
    have hpt : ∀ v, 0 ≤ (Sum.elim ![(0 : ℝ), 0] (fun _ => t) : Fin 2 ⊕ ι → ℝ) v := by
      intro v; rcases v with i | k
      · fin_cases i <;> simp
      · simpa using ht
    refine lt_of_lt_of_le ?_ (coeff_zero_le_eval_of_nonneg hcoeff hpt)
    rw [coeff_pderiv]
    simp only [Finsupp.coe_zero, Pi.zero_apply, CharP.cast_eq_zero, zero_add, mul_one]
    apply hpos
    intro v
    simp only [Finsupp.single_apply]
    split_ifs <;> omega
  -- Rayleigh for the pair `x, y`
  have hR1 : ∀ t : ℝ, 0 ≤ a1.eval t * a2.eval t - a0.eval t * a12.eval t := by
    intro t
    have := hs.rayleighForm_nonneg hma hxy (Sum.elim ![0, 0] (fun _ => t))
    simpa only [rayleighForm, ha0, ha1, ha2, ha12, eval_diagHom] using this
  -- Rayleigh for `∂ₓ p` (pairs `y, s_j`), summed along the diagonal
  have hR2 : ∀ t : ℝ, 0 ≤ a12.eval t * (Polynomial.derivative a1).eval t -
      a1.eval t * (Polynomial.derivative a12).eval t := by
    intro t
    have hray : ∀ j : ι, RayleighAt (pderiv x₀ p) y₀ (Sum.inr j) := by
      intro j
      refine RayleighAt.of_decomp (p₀ := p - X x₀ * pderiv x₀ p) (k := x₀) (by ring)
        (degreeOf_sub_X_mul_pderiv_self (hma x₀)) (degreeOf_pderiv_self_of_le_one (hma x₀))
        hxy.symm (by simp [hx₀]) ?_
      intro z
      exact hs.rayleighForm_nonneg hma (by simp [hy₀]) z
    have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      hray j (Sum.elim ![0, 0] (fun _ => t)))
    rw [sum_rayleighForm_eq] at hsum
    have e : pderiv y₀ (pderiv x₀ p) = pderiv x₀ (pderiv y₀ p) := pderiv_comm _ _ _
    rw [e] at hsum
    exact hsum
  -- Rayleigh for the pairs `x, s_j`, summed along the diagonal through `(-A, η)`
  have hR3 : ∀ η t : ℝ, 0 ≤
      (a1 + Polynomial.C η * a12).eval t *
          (Polynomial.derivative (a0 + Polynomial.C (-A) * a1 + Polynomial.C η * a2 +
            Polynomial.C (-A) * Polynomial.C η * a12)).eval t -
        (a0 + Polynomial.C (-A) * a1 + Polynomial.C η * a2 +
            Polynomial.C (-A) * Polynomial.C η * a12).eval t *
          (Polynomial.derivative (a1 + Polynomial.C η * a12)).eval t := by
    intro η t
    have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      hs.rayleighForm_nonneg hma (i := x₀) (j := Sum.inr j) (by simp [hx₀])
        (Sum.elim ![-A, η] (fun _ => t)))
    rw [sum_rayleighForm_eq] at hsum
    have eP : diagHom ι (-A) η p = a0 + Polynomial.C (-A) * a1 + Polynomial.C η * a2 +
        Polynomial.C (-A) * Polynomial.C η * a12 := by
      have := aeval_elim_eq (S := Polynomial ℝ) (hma x₀) (hma y₀) (Polynomial.C (-A))
        (Polynomial.C η) Polynomial.X
      simp only [Polynomial.aeval_X_left_apply] at this
      rw [ha0, ha1, ha2, ha12]
      exact this
    have eQ : diagHom ι (-A) η (pderiv x₀ p) = a1 + Polynomial.C η * a12 := by
      have := aeval_elim_eq (S := Polynomial ℝ) (hmaD x₀ p hma x₀) (hmaD x₀ p hma y₀)
        (Polynomial.C (-A)) (Polynomial.C η) Polynomial.X
      simp only [Polynomial.aeval_X_left_apply] at this
      change diagHom ι (-A) η (pderiv x₀ p) = _ at this
      rw [this, pderiv_pderiv_self_eq_zero (hma x₀), pderiv_comm y₀ x₀,
        pderiv_pderiv_self_eq_zero (hmaD y₀ p hma x₀)]
      simp [ha1, ha12]
    rw [eP, eQ] at hsum
    exact hsum
  -- stability of the diagonal specialization
  have hS : ∀ x y z : ℂ, 0 < x.im → 0 < y.im → 0 < z.im →
      Polynomial.aeval z a0 + x * Polynomial.aeval z a1 + y * Polynomial.aeval z a2 +
        x * y * Polynomial.aeval z a12 ≠ 0 := by
    intro x y z hx hy hz
    rw [← aeval_elim_eq (hma x₀) (hma y₀) x y z]
    apply hstab
    intro v
    rcases v with i | k
    · fin_cases i
      · simpa using hx
      · simpa using hy
    · simpa using hz
  -- conclusion
  have hcore := separator_core (Fintype.card ι) hc hB
    (natDegree_diagHom_le hma) (natDegree_diagHom_le (hmaD _ _ hma))
    (natDegree_diagHom_le (hmaD _ _ hma)) (natDegree_diagHom_le (hmaD _ _ (hmaD _ _ hma)))
    ht12 ht1 ht2 ht0 hpos1 hR1 hR2 hR3 hS
  have hval := aeval_elim_eq (S := ℝ) (hma x₀) (hma y₀) (-A) (-B) 0
  simp only [Polynomial.coe_aeval_eq_eval] at hval
  have hval' : eval (Sum.elim ![-A, -B] 0 : Fin 2 ⊕ ι → ℝ) p = _ := hval
  rw [hval']
  linarith

end

end ArborealDecay.Separator
