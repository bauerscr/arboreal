import Obs2.Flow.VObsAB4X

/-!
# The first-order `S`-contribution to the pair mass cancels: `Loc S` in `V'` vs. in `𝒲'`

The `M₄` coefficient of `V'_k(X)_{ab}` is sourced at every step by `−M₄(Q_i)` and
`−M₄(Loc S_i)` (`m4X_succ`), and its Pauli defect `𝔡₂_k(X) = M₄_k(X)·m2D(C_k)` enters the
`r'` error with the factor `1 − n_{a,k}` (`errABX2`). The same localised parts `Loc S_i(B)` are
subtracted from `𝒲'_{i+1}`, and their tadpoles at the later covariances appear in the memory
terms (`memABX`, the `pdefLSX` increments): since `Loc S_i(B)_{ab} ∈ 𝒩({a,b})` is symmetric,
`pdefLSX_i(Γ) = M₄(Loc S_i)(X)·m2D(Γ)` is **linear** in `Γ`, so the increment at step `k` is
exactly `M₄(Loc S_i)(X)·m2D(C_k)`. The two first-order contributions cancel identically:

`−𝔡₂_k(X)(1 − n_k) − ∑_i M₄(Loc S_i)(X)m2D(C_k)
   = (∑_iM₄(Q_i)(X))m2D(C_k)(1 − n_k) − n_k(∑_iM₄(Loc S_i)(X))m2D(C_k)`

(given `M₄_k(X) = −∑_{j₀≤i<k}(M₄(Q_i)(X) + M₄(Loc S_i)(X))`). What is left of `S` is multiplied
by the vertex factor `n_k = O(ǧ_k)` — second order.

* `m2D`, `m2D_add`, `m4QX`, `m4LSX`, `LSO_ab_memNX`, `LSO_ab_isSym`, **`pdefLSX_eq_m4`**;
* `memABX3` (the memory term without the `Loc S` tadpole), **`memABX_eq3`**;
* `errABX3` (the reorganised region error), **`errABX2_eq3`**;
* `m4_eq_neg_sum` (pure: the `M₄` recursion summed), `norm_errABX3_le`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

variable {d L N : ℕ} [NeZero L]

/-- The Pauli covariance combination `Γ_{aa} + Γ_{bb} − Γ_{ab} − Γ_{ba}`. -/
def m2D (P : ObsPts d L N) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : ℂ :=
  Γ P.a P.a + Γ P.b P.b - Γ P.a P.b - Γ P.b P.a

theorem m2D_add (P : ObsPts d L N) (Γ₁ Γ₂ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    m2D P (Γ₁ + Γ₂) = m2D P Γ₁ + m2D P Γ₂ := by
  unfold m2D; simp only [Matrix.add_apply]; ring

/-- The `M₄` source of the activity in the region `X` at step `j`. -/
def m4QX (P : ObsPts d L N) (j : ℕ) (K : OAct .two d L N) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks j X, cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab

/-- The `M₄` source of the localised second-order term `Loc S` in the region `X` at step `j`. -/
def m4LSX (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (X : Finset (Lam d L N)) : ℂ :=
  ∑ b ∈ blocks j X, cfAB4 P.a P.b (LSO P j C V W b : SA .two (Lam d L N)).ab

theorem LSO_ab_memNX (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (b : Fin d → ℕ) :
    (LSO P j C V W b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)) := by
  rw [LSO, LocO2_ab]; exact locABtXY_mem P _ _ _

theorem LSO_ab_isSym (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (b : Fin d → ℕ) :
    IsSym (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  rw [LSO, LocO2_ab]; exact locABtXY_isSym P _ _ _

/-- **The tadpoles of the localised parts are linear in the covariance**:
`pdefLSX_j(Γ) = M₄(Loc S_j)(X)·m2D(Γ)`. -/
theorem pdefLSX_eq_m4 (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (X : Finset (Lam d L N)) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    pdefLSX P j C V W X Γ = m4LSX P j C V W X * m2D P Γ := by
  rw [pdefLSX, m4LSX, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  have h := pauliDef2_of_ab Γ (LSO_ab_memNX P j C V W b) (LSO_ab_isSym P j C V W b)
  rw [pauliDef2] at h
  rw [h]; rfl

/-- The memory term of step `i` at step `k` **without** the tadpole of `Loc S_i`. -/
def memABX3 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (X : Finset (Lam d L N)) (i k : ℕ) : ℂ :=
  pdefM2X i (C i) (V i) X * tadInc2 P C V i k +
    (dTauABX P i (C i) (V i) X (C k + cumBetween C i k) -
      dTauABX P i (C i) (V i) X (cumBetween C i k)) +
    (wProdABX P i (C i) (V i) (W i) X (C k + cumBetween C i k) -
      wProdABX P i (C i) (V i) (W i) X (cumBetween C i k))

/-- **`mem(i,k) = mem₃(i,k) − M₄(Loc S_i)(X)·m2D(C_k)`.** -/
theorem memABX_eq3 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (X : Finset (Lam d L N)) (i k : ℕ) :
    memABX P C V W X i k =
      memABX3 P C V W X i k - m4LSX P i (C i) (V i) (W i) X * m2D P (C k) := by
  unfold memABX memABX3
  rw [pdefLSX_eq_m4, pdefLSX_eq_m4, m2D_add]
  ring

/-- **The reorganised region error**: the Pauli defect of `V'_k` and the `Loc S` tadpoles of the
memory are combined; what remains is the `Q`-part of `M₄` (with `1 − n_k`), the `Loc S`-part with
the vertex factor `n_k`, and the memory without `Loc S`. -/
def errABX3 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (X : Finset (Lam d L N))
    (j0 k : ℕ) : ℂ :=
  qABX P k (C k) (K k) X + wMassABX P C V W X j0 k +
    (∑ i ∈ Ico j0 k, m4QX P i (K i) X) * m2D P (C k) * (1 - nA2 P k (C k) (V k)) -
    nA2 P k (C k) (V k) * (∑ i ∈ Ico j0 k, m4LSX P i (C i) (V i) (W i) X) * m2D P (C k) +
    mass2 (FC (C k) (dABX P k (C k) (V k) X) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e) -
    farABmX P k (C k) (V k) (W k) X + ∑ i ∈ Ico j0 k, memABX3 P C V W X i k

/-- **The cancellation** (exact): given the summed `M₄` recursion of the region and the
invariants of `V_k`, `errABX2 = errABX3`. -/
theorem errABX2_eq3 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (X : Finset (Lam d L N)) (j0 k : ℕ)
    (hM4 : m4X P k (V k) X =
      -∑ i ∈ Ico j0 k, (m4QX P i (K i) X + m4LSX P i (C i) (V i) (W i) X))
    (hVk : ∀ b, (V k b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hSk : ∀ b, IsSym (V k b : SA .two (Lam d L N)).ab) :
    errABX2 P C V W K X j0 k = errABX3 P C V W K X j0 k := by
  have hp : pdefM2X k (C k) (V k) X = m4X P k (V k) X * m2D P (C k) := by
    rw [pdefM2X, m4X, sum_mul]
    exact sum_congr rfl fun b _ => pauliDef2_of_ab _ (hVk b) (hSk b)
  unfold errABX2 errABX3
  rw [hp, hM4, sum_congr rfl fun i _ => memABX_eq3 P C V W X i k, sum_sub_distrib,
    sum_add_distrib, ← sum_mul]
  ring

/-- The summed `M₄` recursion (pure). -/
theorem m4_eq_neg_sum {M q l : ℕ → ℂ} {j0 n : ℕ} (h0 : M j0 = 0)
    (hs : ∀ i, j0 ≤ i → i < n → M (i + 1) = M i - q i - l i) :
    ∀ k, j0 ≤ k → k ≤ n → M k = -∑ i ∈ Ico j0 k, (q i + l i) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; rw [h0, Ico_self, sum_empty, neg_zero]
  | succ k hk ih =>
    intro hkn
    rw [hs k hk (by omega), ih (by omega), sum_Ico_succ_top hk]
    ring

/-- **The norm of the reorganised error** (the far term vanishes on anchored inputs). -/
theorem norm_errABX3_le (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (X : Finset (Lam d L N)) (j0 k : ℕ)
    (hf : farABmX P k (C k) (V k) (W k) X = 0) :
    ‖errABX3 P C V W K X j0 k‖ ≤ ‖qABX P k (C k) (K k) X‖ + ‖wMassABX P C V W X j0 k‖ +
      (‖∑ i ∈ Ico j0 k, m4QX P i (K i) X‖ * ‖m2D P (C k)‖ * ‖1 - nA2 P k (C k) (V k)‖ +
        ‖nA2 P k (C k) (V k)‖ * ‖∑ i ∈ Ico j0 k, m4LSX P i (C i) (V i) (W i) X‖ *
          ‖m2D P (C k)‖) +
      ‖mass2 (FC (C k) (dABX P k (C k) (V k) X) (VprLO k (C k) (V k) : SA .two (Lam d L N)).e)‖ +
      ∑ i ∈ Ico j0 k, ‖memABX3 P C V W X i k‖ := by
  unfold errABX3
  rw [hf, sub_zero]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_add_le (qABX P k (C k) (K k) X + wMassABX P C V W X j0 k)
    ((∑ i ∈ Ico j0 k, m4QX P i (K i) X) * m2D P (C k) * (1 - nA2 P k (C k) (V k)))
  have h2 := norm_add_le (qABX P k (C k) (K k) X) (wMassABX P C V W X j0 k)
  rw [norm_mul, norm_mul] at h1
  have h3 : ‖nA2 P k (C k) (V k) * (∑ i ∈ Ico j0 k, m4LSX P i (C i) (V i) (W i) X) *
      m2D P (C k)‖ = ‖nA2 P k (C k) (V k)‖ * ‖∑ i ∈ Ico j0 k, m4LSX P i (C i) (V i) (W i) X‖ *
        ‖m2D P (C k)‖ := by rw [norm_mul, norm_mul]
  rw [h3]
  linarith

end

end Obs2
