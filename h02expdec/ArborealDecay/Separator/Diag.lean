module

public import ArborealDecay.Stability.Decomp

/-!
# Diagonal specialization (supplement `lem:diag` and the set-up of `thm:separator`)

For `p : MvPolynomial (Fin 2 ⊕ ι) ℝ` (variables `x = inl 0`, `y = inl 1`, `s_k = inr k`) and real
constants `c₀, c₁`, `diagHom ι c₀ c₁ p ∈ ℝ[t]` is `p(c₀, c₁, t, …, t)`.

* `eval_diagHom`: evaluation at `t` is evaluation of `p` at `(c₀, c₁, t, …, t)`.
* `derivative_diagHom`: the chain rule `∂ₜ (p^ι) = ∑ⱼ (∂_{s_j} p)^ι` (`lem:diag` (i)).
* `coeff_diagHom_zero`, `natDegree_diagHom_le`, `coeff_card_diagHom`: the coefficients of
  `p(0, 0, t, …, t)`; for multi-affine `p` the degree is at most `|ι|` and the coefficient of
  `t^|ι|` is the coefficient of `s₁ ⋯ s_m`.
* `aeval_elim_eq`: for `p` of degree `≤ 1` in `x` and `y`, the four-term expansion
  `p(x, y, z, …, z) = a₀(z) + x a₁(z) + y a₂(z) + x y a₁₂(z)` in any commutative `ℝ`-algebra.
-/

@[expose] public section

open MvPolynomial

namespace ArborealDecay.Separator

noncomputable section

variable {ι : Type*}

/-- The monomial `s₁ ⋯ s_m`. -/
def sMonomial (ι : Type*) [Fintype ι] : Fin 2 ⊕ ι →₀ ℕ :=
  ∑ k, Finsupp.single (Sum.inr k) 1

theorem sMonomial_apply_inl [Fintype ι] (i : Fin 2) : sMonomial ι (Sum.inl i) = 0 := by
  classical
  simp [sMonomial, Finsupp.finsetSum_apply]

theorem sMonomial_apply_inr [Fintype ι] (k : ι) : sMonomial ι (Sum.inr k) = 1 := by
  classical
  simp [sMonomial, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The diagonal specialization `x ↦ c₀`, `y ↦ c₁`, `s_k ↦ t`. -/
def diagHom (ι : Type*) (c₀ c₁ : ℝ) : MvPolynomial (Fin 2 ⊕ ι) ℝ →ₐ[ℝ] Polynomial ℝ :=
  aeval (Sum.elim ![Polynomial.C c₀, Polynomial.C c₁] (fun _ => Polynomial.X))

theorem aeval_diagHom {S : Type*} [CommRing S] [Algebra ℝ S] (c₀ c₁ : ℝ) (z : S)
    (q : MvPolynomial (Fin 2 ⊕ ι) ℝ) :
    Polynomial.aeval z (diagHom ι c₀ c₁ q) =
      aeval (Sum.elim ![algebraMap ℝ S c₀, algebraMap ℝ S c₁] (fun _ => z)) q := by
  rw [diagHom, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext v
  rcases v with i | k
  · fin_cases i <;> simp
  · simp

theorem eval_diagHom (c₀ c₁ t : ℝ) (q : MvPolynomial (Fin 2 ⊕ ι) ℝ) :
    (diagHom ι c₀ c₁ q).eval t = eval (Sum.elim ![c₀, c₁] (fun _ => t)) q := by
  have := aeval_diagHom (S := ℝ) c₀ c₁ t q
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.coe_aeval_eq_eval] at this
  exact this

/-- Chain rule along the diagonal (`lem:diag` (i), third identity). -/
theorem derivative_diagHom [Fintype ι] [DecidableEq ι] (c₀ c₁ : ℝ)
    (q : MvPolynomial (Fin 2 ⊕ ι) ℝ) :
    Polynomial.derivative (diagHom ι c₀ c₁ q) =
      ∑ k, diagHom ι c₀ c₁ (pderiv (Sum.inr k) q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [diagHom]
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have hk : ∀ k, diagHom ι c₀ c₁ (pderiv (Sum.inr k) (p * X v)) =
        diagHom ι c₀ c₁ (pderiv (Sum.inr k) p) * diagHom ι c₀ c₁ (X v) +
        diagHom ι c₀ c₁ p * (if v = Sum.inr k then 1 else 0) := by
      intro k
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : v = Sum.inr k
      · simp [h]; ring
      · simp [h]; ring
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib, ← Finset.sum_mul, ← hp,
      ← Finset.mul_sum, map_mul, Polynomial.derivative_mul]
    congr 1
    rcases v with i | j
    · fin_cases i <;> simp [diagHom]
    · simp [diagHom]

/-- Explicit form of `p(0, 0, t, …, t)`. -/
theorem diagHom_zero_eq [Fintype ι] (q : MvPolynomial (Fin 2 ⊕ ι) ℝ) :
    diagHom ι 0 0 q = ∑ d ∈ q.support,
      if d (Sum.inl 0) = 0 ∧ d (Sum.inl 1) = 0 then
        Polynomial.C (q.coeff d) * Polynomial.X ^ (∑ k, d (Sum.inr k)) else 0 := by
  rw [diagHom, aeval_def, eval₂_eq']
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.prod_sum_type, Fin.prod_univ_two]
  simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_zero, Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq]
  split_ifs with h
  · simp [h.1, h.2]
  · rcases not_and_or.mp h with h | h
    · simp [zero_pow h]
    · simp [zero_pow h]

theorem coeff_diagHom_zero [Fintype ι] (q : MvPolynomial (Fin 2 ⊕ ι) ℝ) (n : ℕ) :
    (diagHom ι 0 0 q).coeff n = ∑ d ∈ q.support,
      if d (Sum.inl 0) = 0 ∧ d (Sum.inl 1) = 0 ∧ ∑ k, d (Sum.inr k) = n then q.coeff d else 0 := by
  rw [diagHom_zero_eq, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : d (Sum.inl 0) = 0 ∧ d (Sum.inl 1) = 0
  · rw [ite_eq_left h, Polynomial.coeff_C_mul_X_pow]
    by_cases hn : n = ∑ k, d (Sum.inr k)
    · rw [ite_eq_left hn, ite_eq_left ⟨h.1, h.2, hn.symm⟩]
    · rw [ite_eq_right hn, ite_eq_right (fun h' => hn h'.2.2.symm)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩), Polynomial.coeff_zero]

theorem le_one_of_mem_support {σ : Type*} {q : MvPolynomial σ ℝ}
    (hq : ∀ v, q.degreeOf v ≤ 1) {d : σ →₀ ℕ} (hd : d ∈ q.support) (v : σ) : d v ≤ 1 :=
  (le_degreeOf_of_mem_support v hd).trans (hq v)

theorem natDegree_diagHom_le [Fintype ι] {q : MvPolynomial (Fin 2 ⊕ ι) ℝ}
    (hq : ∀ v, q.degreeOf v ≤ 1) : (diagHom ι 0 0 q).natDegree ≤ Fintype.card ι := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_diagHom_zero]
  apply Finset.sum_eq_zero
  intro d hd
  rw [ite_eq_right]
  rintro ⟨-, -, hs⟩
  have : ∑ k, d (Sum.inr k) ≤ ∑ _k : ι, 1 :=
    Finset.sum_le_sum fun k _ => le_one_of_mem_support hq hd _
  simp at this
  omega

theorem coeff_card_diagHom [Fintype ι] {q : MvPolynomial (Fin 2 ⊕ ι) ℝ}
    (hq : ∀ v, q.degreeOf v ≤ 1) :
    (diagHom ι 0 0 q).coeff (Fintype.card ι) = q.coeff (sMonomial ι) := by
  rw [coeff_diagHom_zero]
  rw [Finset.sum_eq_single (sMonomial ι)]
  · rw [ite_eq_left]
    refine ⟨sMonomial_apply_inl 0, sMonomial_apply_inl 1, ?_⟩
    simp [sMonomial_apply_inr]
  · intro d hd hne
    rw [ite_eq_right]
    rintro ⟨h0, h1, hs⟩
    apply hne
    have hle : ∀ k ∈ (Finset.univ : Finset ι), d (Sum.inr k) ≤ 1 :=
      fun k _ => le_one_of_mem_support hq hd _
    have heq : ∑ k, d (Sum.inr k) = ∑ _k : ι, 1 := by simp [hs]
    have hall := (Finset.sum_eq_sum_iff_of_le hle).mp heq
    ext v
    rcases v with i | k
    · fin_cases i
      · simp [h0, sMonomial_apply_inl]
      · simp [h1, sMonomial_apply_inl]
    · simp [hall k (Finset.mem_univ _), sMonomial_apply_inr]
  · intro h
    rw [notMem_support_iff.mp h]
    simp

/-- If all coefficients are nonnegative and the point is nonnegative, the value is at least the
constant coefficient. -/
theorem coeff_zero_le_eval_of_nonneg {σ : Type*} [Fintype σ] {q : MvPolynomial σ ℝ}
    (hq : ∀ d, 0 ≤ q.coeff d) {x : σ → ℝ} (hx : ∀ v, 0 ≤ x v) :
    q.coeff 0 ≤ eval x q := by
  rw [eval_eq']
  have hterm : ∀ d ∈ q.support, 0 ≤ q.coeff d * ∏ i, x i ^ d i := fun d _ =>
    mul_nonneg (hq d) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)
  by_cases h0 : (0 : σ →₀ ℕ) ∈ q.support
  · have := Finset.single_le_sum hterm h0
    simpa using this
  · rw [notMem_support_iff.mp h0]
    exact Finset.sum_nonneg hterm

/-! ### The four-term expansion -/

section Expansion

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem aeval_elim_of_free {S : Type*} [CommRing S] [Algebra ℝ S]
    {r : MvPolynomial (Fin 2 ⊕ ι) ℝ} (h0 : r.degreeOf (Sum.inl 0) = 0)
    (h1 : r.degreeOf (Sum.inl 1) = 0) (x y z : S) :
    aeval (Sum.elim ![x, y] (fun _ => z)) r = Polynomial.aeval z (diagHom ι 0 0 r) := by
  rw [aeval_diagHom, map_zero, aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
  apply eval₂Hom_congr' rfl _ rfl
  intro v hv _
  rcases v with i | k
  · exfalso
    rw [mem_vars_iff_degreeOf_ne_zero] at hv
    fin_cases i
    · exact hv h0
    · exact hv h1
  · simp

/-- The four-term expansion of a polynomial of degree `≤ 1` in `x` and `y`. -/
theorem aeval_elim_eq [Fintype ι] {S : Type*} [CommRing S] [Algebra ℝ S]
    {q : MvPolynomial (Fin 2 ⊕ ι) ℝ} (hx : q.degreeOf (Sum.inl 0) ≤ 1)
    (hy : q.degreeOf (Sum.inl 1) ≤ 1) (x y z : S) :
    aeval (Sum.elim ![x, y] (fun _ => z)) q =
      Polynomial.aeval z (diagHom ι 0 0 q) +
        x * Polynomial.aeval z (diagHom ι 0 0 (pderiv (Sum.inl 0) q)) +
        y * Polynomial.aeval z (diagHom ι 0 0 (pderiv (Sum.inl 1) q)) +
        x * y * Polynomial.aeval z
          (diagHom ι 0 0 (pderiv (Sum.inl 0) (pderiv (Sum.inl 1) q))) := by
  have hne : (Sum.inl 0 : Fin 2 ⊕ ι) ≠ Sum.inl 1 := by simp
  obtain ⟨p₀₀, p₁₀, p₀₁, p₁₁, hdec, -⟩ := ArborealDecay.Stability.exists_isTwoVarDecomp hne hx hy
  have hX0 : diagHom ι 0 0 (X (Sum.inl 0)) = 0 := by simp [diagHom]
  have hX1 : diagHom ι 0 0 (X (Sum.inl 1)) = 0 := by simp [diagHom]
  have e0 : diagHom ι 0 0 q = diagHom ι 0 0 p₀₀ := by
    rw [hdec.eq]; simp [hX0, hX1]
  have e1 : diagHom ι 0 0 (pderiv (Sum.inl 0) q) = diagHom ι 0 0 p₁₀ := by
    rw [hdec.pderiv_i hne]; simp [hX1]
  have e2 : diagHom ι 0 0 (pderiv (Sum.inl 1) q) = diagHom ι 0 0 p₀₁ := by
    rw [hdec.pderiv_j hne]; simp [hX0]
  have e3 : pderiv (Sum.inl 0) (pderiv (Sum.inl 1) q) = p₁₁ := hdec.pderiv_ij hne
  rw [e0, e1, e2, e3, ← aeval_elim_of_free hdec.i₀₀ hdec.j₀₀ x y z,
    ← aeval_elim_of_free hdec.i₁₀ hdec.j₁₀ x y z, ← aeval_elim_of_free hdec.i₀₁ hdec.j₀₁ x y z,
    ← aeval_elim_of_free hdec.i₁₁ hdec.j₁₁ x y z]
  conv_lhs => rw [hdec.eq]
  simp only [map_add, map_mul, aeval_X, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one]

end Expansion

end

end ArborealDecay.Separator
