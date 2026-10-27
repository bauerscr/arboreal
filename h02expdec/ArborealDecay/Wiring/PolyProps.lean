module

public import ArborealDecay.Wiring.Poly

/-!
# Properties of `p`: evaluation at `(x, y, 0)`, multi-affinity, positive coefficients
-/

@[expose] public section

namespace ArborealDecay.Wiring

open MvPolynomial Finset

noncomputable section

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Evaluation of `p` as a sum over forests. -/
theorem eval_wpoly (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) (S : Finset V)
    (e : Var S → ℝ) :
    eval e (wpoly β hβ a b S) = ∑ F : SimpleGraph V with F.IsAcyclic,
      (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        ∏ T : F.ConnectedComponent, (1 + ∑ u with cmp a b S F u = T, e u) := by
  rw [wpoly_eq_prod, map_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp [map_prod]

theorem prod_two_comp {F : SimpleGraph V} (a b : V) (A B : ℝ) :
    ∏ T : F.ConnectedComponent, (1 + ((if F.connectedComponentMk a = T then -A else 0) +
      (if F.connectedComponentMk b = T then -B else 0))) =
      if F.Reachable a b then 1 - A - B else (1 - A) * (1 - B) := by
  by_cases h : F.Reachable a b
  · have hc : F.connectedComponentMk a = F.connectedComponentMk b :=
      SimpleGraph.ConnectedComponent.eq.2 h
    rw [if_pos h, Finset.prod_eq_single (F.connectedComponentMk a)]
    · simp [hc]; ring
    · intro T _ hT
      rw [if_neg (fun h' => hT h'.symm), if_neg (fun h' => hT (h'.symm.trans hc.symm))]
      simp
    · simp
  · have hc : F.connectedComponentMk a ≠ F.connectedComponentMk b := fun h' =>
      h (SimpleGraph.ConnectedComponent.eq.1 h')
    rw [if_neg h, Finset.prod_eq_mul (F.connectedComponentMk a) (F.connectedComponentMk b) hc]
    · rw [if_pos rfl, if_neg hc, if_neg hc.symm, if_pos rfl]; ring
    · intro T _ hT
      rw [if_neg (fun h' => hT.1 h'.symm), if_neg (fun h' => hT.2 h'.symm)]
      simp
    · simp
    · simp

/-- **`eq:p-szero`**: `p(x, y, 0)` at `x = -A`, `y = -B`. -/
theorem eval_wpoly_two (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (a b : V) (S : Finset V)
    (A B : ℝ) :
    eval (Sum.elim ![-A, -B] (fun _ => 0)) (wpoly β hβ a b S) =
      ∑ F : SimpleGraph V with F.IsAcyclic, (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        if F.Reachable a b then 1 - A - B else (1 - A) * (1 - B) := by
  rw [eval_wpoly]
  refine Finset.sum_congr rfl fun F _ => ?_
  congr 1
  rw [← prod_two_comp (F := F) a b A B]
  refine Finset.prod_congr rfl fun T _ => ?_
  congr 1
  have h0 : cmp a b S F (Sum.inl 0) = F.connectedComponentMk a := rfl
  have h1 : cmp a b S F (Sum.inl 1) = F.connectedComponentMk b := rfl
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [h0, h1, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inr,
    ite_self, Finset.sum_const_zero, add_zero]

theorem le_one_of_mem_support' {σ : Type*} {q : MvPolynomial σ ℝ} (hq : ∀ v, q.degreeOf v ≤ 1)
    {d : σ →₀ ℕ} (hd : d ∈ q.support) (v : σ) : d v ≤ 1 :=
  (le_degreeOf_of_mem_support v hd).trans (hq v)

/-- Multi-affinity of a substitution. -/
theorem degreeOf_bind₁_le_one {σ τ : Type*} [DecidableEq σ] {P : MvPolynomial σ ℝ} (hP : ∀ v, P.degreeOf v ≤ 1)
    (κ : τ → σ) (g : σ → MvPolynomial τ ℝ)
    (hg : ∀ j k, (g k).degreeOf j ≤ if k = κ j then 1 else 0) (j : τ) :
    (bind₁ g P).degreeOf j ≤ 1 := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [bind₁_monomial]
  refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_prod_le _ _ _).trans ?_)
  have h1 : ∀ k ∈ d.support, (g k ^ d k).degreeOf j ≤ if k = κ j then d k else 0 := by
    intro k _
    refine (degreeOf_pow_le _ _ _).trans ?_
    by_cases hk : k = κ j
    · rw [if_pos hk]
      have := hg j k
      rw [if_pos hk] at this
      simpa using Nat.mul_le_mul_left (d k) this
    · rw [if_neg hk]
      have := hg j k
      rw [if_neg hk] at this
      simp [Nat.le_zero.1 this]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs
  · exact le_one_of_mem_support' hP hd _
  · exact zero_le_one

theorem phi_degreeOf_le (a b : V) (S : Finset V) (j : Var S) (k : V) :
    (phi a b S k).degreeOf j ≤ if k = lab a b S j then 1 else 0 := by
  unfold phi
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun u hu => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  by_cases hk : k = lab a b S j
  · rw [if_pos hk]
    exact (degreeOf_X_le_one j u)
  · rw [if_neg hk]
    have : u ≠ j := fun h => hk (h ▸ hu.symm)
    simp [degreeOf_X, this.symm]
where
  degreeOf_X_le_one (j u : Var S) : (X u : MvPolynomial (Var S) ℝ).degreeOf j ≤ 1 := by
    rw [degreeOf_X]; split_ifs <;> simp

/-- `p` is multi-affine. -/
theorem wpoly_degreeOf_le_one (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i)
    (hP : ∀ v, (forestPolynomial β hβ).degreeOf v ≤ 1) (a b : V) (S : Finset V) (j : Var S) :
    (wpoly β hβ a b S).degreeOf j ≤ 1 :=
  degreeOf_bind₁_le_one hP (lab a b S) (phi a b S) (fun j k => phi_degreeOf_le a b S j k) j

/-- **Positivity of the coefficients of `p`** (squarefree monomials). -/
theorem coeff_wpoly_pos (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : V} {S : Finset V} (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S) (d : Var S →₀ ℕ)
    (hd : ∀ v, d v ≤ 1) : 0 < (wpoly β hβ a b S).coeff d := by
  rw [eq_mon_support hd, coeff_wpoly]
  refine Finset.sum_pos' (fun F _ => ?_) ⟨⊥, by simp, ?_⟩
  · refine mul_nonneg (H02.forestWeight_nonneg hβ hβ0 F) ?_
    split_ifs <;> norm_num
  · have hinj : Set.InjOn (cmp a b S ⊥) ↑d.support := by
      intro u _ v _ h
      have := (SimpleGraph.ConnectedComponent.eq.1 h)
      rw [SimpleGraph.reachable_bot] at this
      exact lab_injective hab ha hb this
    rw [if_pos hinj, mul_one]
    refine lt_of_lt_of_eq one_pos (Finset.prod_eq_one ?_).symm
    intro e he
    simp at he

end

end ArborealDecay.Wiring
