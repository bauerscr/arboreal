module

public import ArborealDecay.Pinned.Unpinned

/-!
# Berezin parity, leaf integrals and tree-level evaluations

* `int0_eq_zero_of_odd` (supplement `lem:berezin`(e)): `[F]_0 = 0` for odd `F`.
* `lem_leaf` (supplement `lem:leaf`): `∂²_ℓ[(1 + q_ℓ) x_{ℓk}] = 1`,
  `∂²_ℓ[(1 + q_ℓ) ξ_ℓ x_{ℓk}] = ξ_k` (`H02.intStep ℓ = ∂_{η_ℓ} ∂_{ξ_ℓ} (1 + q_ℓ) ·`).
* `prop_tree_eval` (supplement `prop:tree-eval` (i), (ii)): for a tree `T` on its vertex type
  `τ`, `[X_T]^τ_0 = 1` and `[ξ_a η_b X_T]^τ_0 = 1` (`a = b` allowed).

The tree evaluations are proved with the route of `ArborealDecay.Pinned.Unpinned`
(`J`-symmetry and `ξ_a η_b + ξ_b η_a = q_a + q_b - q_a q_b - x_{ab}`) rather than by leaf
removal; `lem:leaf` is recorded for completeness.
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02 CliffordAlgebra

section Parity

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem contractLeft_inv' (d : Module.Dual ℝ M) (x : ExteriorAlgebra ℝ M) :
    contractLeft d (inv' x) = -inv' (contractLeft d x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [contractLeft_ι]
  | mul a b ha hb =>
    rw [map_mul, contractLeft_mul, contractLeft_mul, ha, hb, map_add, map_mul, map_mul,
      inv', involute_involute]
    noncomm_ring
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add, neg_add]

end Parity

section Grassmann

variable {Λ : Type*} [DecidableEq Λ]

theorem intStep_inv' (v : Λ) (x : Grassmann Λ) : intStep v (inv' x) = inv' (intStep v x) := by
  have hq : inv' (1 + ξ v * η v) = (1 + ξ v * η v : Grassmann Λ) := by simp
  rw [intStep_apply, intStep_apply, ← hq, ← map_mul, hq, dξ, contractLeft_inv', ← dξ, map_neg,
    dη, contractLeft_inv', ← dη, neg_neg]

theorem berezin_inv' (l : List Λ) (x : Grassmann Λ) : berezin l (inv' x) = inv' (berezin l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih => rw [berezin_cons, berezin_cons, intStep_inv', ih]

theorem algebraMapInv_inv' (x : Grassmann Λ) :
    ExteriorAlgebra.algebraMapInv (inv' x) = ExteriorAlgebra.algebraMapInv x := by
  have : (ExteriorAlgebra.algebraMapInv : Grassmann Λ →ₐ[ℝ] ℝ).comp inv' =
      ExteriorAlgebra.algebraMapInv := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun f : Grassmann Λ →ₐ[ℝ] ℝ => f x) this

variable [Fintype Λ]

theorem int0_inv' (F : Grassmann Λ) : int0 (inv' F) = int0 F := by
  rw [int0, int0, berezin_inv', algebraMapInv_inv']

/-- **Supplement `lem:berezin`(e)** (parity): if `F` is odd then `[F]_0 = 0`. -/
theorem int0_eq_zero_of_odd {F : Grassmann Λ} (hF : inv' F = -F) : int0 F = 0 := by
  have h := int0_inv' F
  rw [hF, int0_eq_L, map_neg, ← int0_eq_L] at h
  linarith

end Grassmann

section Leaf

variable {Λ : Type*} [DecidableEq Λ]

/-- `x_{ℓk} = 1 + u_ℓ · u_k` in the Grassmann algebra (BCHS (2.3)). -/
theorem cv_Xc (ℓ k : Λ) :
    cv (Xc ℓ k) = ξ ℓ * η ℓ + ξ k * η k - ξ ℓ * η ℓ * (ξ k * η k) - ξ ℓ * η k - ξ k * η ℓ := by
  rw [Xc_eq]; simp

/-- **Supplement `lem:leaf`**: for `ℓ ≠ k`,
`∂²_ℓ[(1 + q_ℓ) x_{ℓk}] = 1` and `∂²_ℓ[(1 + q_ℓ) ξ_ℓ x_{ℓk}] = ξ_k`. -/
theorem lem_leaf {ℓ k : Λ} (h : ℓ ≠ k) :
    intStep ℓ (cv (Xc ℓ k)) = 1 ∧ intStep ℓ (ξ ℓ * cv (Xc ℓ k)) = ξ k := by
  have hk : k ≠ ℓ := Ne.symm h
  have e1 : (1 + ξ ℓ * η ℓ) * cv (Xc ℓ k) =
      ξ ℓ * η ℓ + ξ k * η k - ξ ℓ * η k - ξ k * η ℓ := by
    rw [cv_Xc]
    have q2 : ξ ℓ * η ℓ * (ξ ℓ * η ℓ) = (0 : Grassmann Λ) := ξη_sq ℓ
    have a1 : ξ ℓ * η ℓ * (ξ ℓ * η k) = (0 : Grassmann Λ) := by
      have := congrArg cv (pc_mul_pc_left ℓ ℓ k); simpa using this
    have a2 : ξ ℓ * η ℓ * (ξ k * η ℓ) = (0 : Grassmann Λ) := by
      have := congrArg cv (pc_mul_pc_right ℓ ℓ k); simpa using this
    have e : (1 + ξ ℓ * η ℓ) * (ξ ℓ * η ℓ + ξ k * η k - ξ ℓ * η ℓ * (ξ k * η k) - ξ ℓ * η k -
        ξ k * η ℓ) = ξ ℓ * η ℓ + ξ k * η k - ξ ℓ * η k - ξ k * η ℓ +
        (ξ ℓ * η ℓ * (ξ ℓ * η ℓ) - ξ ℓ * η ℓ * (ξ ℓ * η ℓ) * (ξ k * η k) -
          ξ ℓ * η ℓ * (ξ ℓ * η k) - ξ ℓ * η ℓ * (ξ k * η ℓ)) := by noncomm_ring
    rw [e, q2, a1, a2]; noncomm_ring
  have e2 : (1 + ξ ℓ * η ℓ) * (ξ ℓ * cv (Xc ℓ k)) = ξ ℓ * η ℓ * ξ k + ξ ℓ * (ξ k * η k) := by
    rw [cv_Xc]
    have s1 : ξ ℓ * ξ ℓ = (0 : Grassmann Λ) := ξ_mul_ξ ℓ
    have a : η ℓ * ξ k = -(ξ k * η ℓ) := η_anticomm_ξ ℓ k
    have c : η ℓ * ξ ℓ = -(ξ ℓ * η ℓ) := η_anticomm_ξ ℓ ℓ
    have hx : ξ ℓ * (ξ ℓ * η ℓ + ξ k * η k - ξ ℓ * η ℓ * (ξ k * η k) - ξ ℓ * η k - ξ k * η ℓ) =
        ξ ℓ * η ℓ * ξ k + ξ ℓ * (ξ k * η k) := by
      have e : ξ ℓ * (ξ ℓ * η ℓ + ξ k * η k - ξ ℓ * η ℓ * (ξ k * η k) - ξ ℓ * η k - ξ k * η ℓ) =
          (ξ ℓ * ξ ℓ) * (η ℓ - η ℓ * (ξ k * η k) - η k) + ξ ℓ * (ξ k * η k) -
            (ξ ℓ * ξ k) * η ℓ := by
        noncomm_ring
      rw [e, s1, zero_mul, zero_add]
      have : ξ ℓ * η ℓ * ξ k = -(ξ ℓ * ξ k * η ℓ) := by
        rw [mul_assoc, a, mul_neg, mul_assoc]
      rw [this]; abel
    rw [hx, mul_add]
    have z1 : ξ ℓ * η ℓ * (ξ ℓ * η ℓ * ξ k) = 0 := by rw [← mul_assoc, ξη_sq, zero_mul]
    have z2 : ξ ℓ * η ℓ * (ξ ℓ * (ξ k * η k)) = 0 := by
      have e : ξ ℓ * η ℓ * (ξ ℓ * (ξ k * η k)) = ξ ℓ * (η ℓ * ξ ℓ) * (ξ k * η k) := by
        noncomm_ring
      rw [e, c, mul_neg, ← mul_assoc (ξ ℓ) (ξ ℓ), s1]; simp
    rw [add_mul, add_mul, one_mul, one_mul, z1, z2]; abel
  refine ⟨?_, ?_⟩
  · rw [intStep_apply, e1]
    simp [dξ_mul, dξ_ξ, dξ_η, dη_η, h]
  · rw [intStep_apply, e2]
    simp [dξ_mul, dη_mul, dξ_ξ, dξ_η, dη_ξ, dη_η, h]

end Leaf

section Tree

variable {τ : Type*} [DecidableEq τ] [Fintype τ]

theorem Jmap_cv_Xc (a b : τ) : Jmap (cv (Xc a b)) = cv (Xc a b) := by
  rw [coe_Xc, map_add, map_one, Jmap_dot]

theorem Jmap_cv_Xs (e : Sym2 τ) : Jmap (cv (Xs e)) = cv (Xs e) := by
  induction e using Sym2.ind with
  | h a b => exact Jmap_cv_Xc a b

theorem Jmap_cv_prod (t : Finset (Sym2 τ)) :
    Jmap (cv (∏ e ∈ t, Xs e)) = cv (∏ e ∈ t, Xs e) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, map_mul, map_mul, Jmap_cv_Xs, ih]

theorem Jmap_prodX (G : SimpleGraph τ) :
    Jmap (cv (∏ e ∈ E G, Xs e)) = cv (∏ e ∈ E G, Xs e) := Jmap_cv_prod _

/-- `[x_{ab} X_G]_0 = 1_{G forest, a ↮_G b}` for `a ≠ b`. -/
theorem int0_Xc_prodX (G : SimpleGraph τ) {a b : τ} (hab : a ≠ b) :
    int0 (cv (Xc a b * ∏ e ∈ E G, Xs e)) = if G.IsAcyclic ∧ ¬G.Reachable a b then 1 else 0 := by
  by_cases hG : G.Adj a b
  · have hmem : s(a, b) ∈ E G := by simpa using hG
    have : Xc a b * ∏ e ∈ E G, Xs e = 0 := by
      rw [← Finset.mul_prod_erase _ _ hmem, Xs_mk, ← mul_assoc, Xc_sq, zero_mul]
    rw [this]
    simp [int0, hG.reachable]
  · have hnot : s(a, b) ∉ E G := by simpa using hG
    rw [← Xs_mk, ← Finset.prod_insert hnot, ← E_sup_edge G hab, int0_prodX]
    exact if_congr (acyclic_sup_edge_iff hab hG) rfl rfl

/-- **Supplement `prop:tree-eval` (i), (ii)**: for a tree `T` whose vertex set is `τ` and
`a, b ∈ τ` (`a = b` allowed), `[X_T]^τ_0 = 1` and `[ξ_a η_b X_T]^τ_0 = 1`. -/
theorem prop_tree_eval {T : SimpleGraph τ} (hT : T.IsTree) (a b : τ) :
    int0 (cv (∏ e ∈ E T, Xs e)) = 1 ∧ int0 (ξ a * η b * cv (∏ e ∈ E T, Xs e)) = 1 := by
  have hA : T.IsAcyclic := hT.isAcyclic
  refine ⟨by simp [int0_prodX, hA], ?_⟩
  have hq : ∀ c : τ, int0 (ξ c * η c * cv (∏ e ∈ E T, Xs e)) = 1 := by
    intro c
    have := int0_prodPc_mul_prodX T {c}
    rw [Finset.prod_singleton, good_singleton_iff, map_mul, coe_pc] at this
    simpa [hA] using this
  by_cases hab : a = b
  · subst hab; exact hq a
  have hJ : int0 (ξ b * η a * cv (∏ e ∈ E T, Xs e)) = int0 (ξ a * η b * cv (∏ e ∈ E T, Xs e)) := by
    rw [← int0_Jmap, map_mul, Jmap_ξη, Jmap_prodX]
  have hsum : ξ a * η b * cv (∏ e ∈ E T, Xs e) + ξ b * η a * cv (∏ e ∈ E T, Xs e) =
      ξ a * η a * cv (∏ e ∈ E T, Xs e) + ξ b * η b * cv (∏ e ∈ E T, Xs e) -
        cv ((∏ i ∈ ({a, b} : Finset τ), pc i i) * ∏ e ∈ E T, Xs e) -
        cv (Xc a b * ∏ e ∈ E T, Xs e) := by
    rw [Finset.prod_pair hab]
    simp only [map_mul, coe_pc, cv_Xc]
    noncomm_ring
  have hreach : T.Reachable a b := hT.connected.preconnected a b
  have h2 := congrArg int0 hsum
  simp only [int0_eq_L, map_add, map_sub] at h2
  simp only [← int0_eq_L] at h2
  rw [hJ, hq, hq, int0_prodPc_mul_prodX, good_pair_iff T hab, int0_Xc_prodX T hab] at h2
  simp only [hA, hreach, not_true_eq_false, and_false, ite_false] at h2
  linarith

end Tree

end

end ArborealDecay.Pinned

end
