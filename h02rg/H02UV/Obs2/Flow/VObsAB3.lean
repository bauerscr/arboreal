import Obs2.Flow.VObsAB2

/-!
# The flow of the quartic coefficient `M₄` of `V'_{ab}` (one step)

For `V(B)_{ab}` `U(1)`-invariant in `𝒩({a,b})`, the total quartic coefficient
`M₄ = ∑_BM₄(V(B)_{ab})` (`m4Tot`) obeys the exact one-step identity (**`m4Tot_succ`**)

  `M₄' = M₄ − ∑_BM₄(Q(B)_{ab}) − ∑_BM₄(Loc_{B_+,B}S(B_+)_{ab})`

(`e^{ℒ_C}` does not change the top coefficient, `cfAB4_expLC_of_ab`; constants carry none). The
quartic coefficient of the barycentric localisation is the weighted moment
`M₄(loc^{ab,t}_XF) = Mw_X(σ₄; t,t,·,·)(F)` (**`cfAB4_locABtX`**), bounded by `‖F‖` through
`norm_Mw_le`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

theorem cfAB4_one (a b : Lam d L N) : cfAB4 a b (1 : Alg d L N) = 0 :=
  coeff_one_of_ne' _ (by decide)

theorem cfAB4_algebraMap (a b : Lam d L N) (r : ℂ) :
    cfAB4 a b (algebraMap ℂ (Alg d L N) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, cfAB4_smul, cfAB4_one, mul_zero]

theorem cfAB4_of_isHom2 (a b : Lam d L N) {F : Alg d L N} (hF : IsHom 2 F) : cfAB4 a b F = 0 :=
  hF 4 _ (by decide)

theorem cfAB4_m4_self {a b : Lam d L N} (hab : a ≠ b) : cfAB4 a b (m4 a b) = 1 := by
  unfold cfAB4
  rw [m4_eq_psiPow, coeff_psiPow_self _ (injective_m4 hab)]

theorem cfAB4_comm (a b : Lam d L N) (G : Alg d L N) : cfAB4 a b G = cfAB4 b a G := by
  unfold cfAB4
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  have h := coeff_perm G (![(b, -1), (b, 1), (a, -1), (a, 1)] : Fin 4 → Sf (Lam d L N)) σ
  have e : (![(b, -1), (b, 1), (a, -1), (a, 1)] : Fin 4 → Sf (Lam d L N)) ∘ σ =
      ![(a, -1), (a, 1), (b, -1), (b, 1)] := by
    funext i; fin_cases i <;> simp [σ, Equiv.swap_apply_def]
  have hs : Equiv.Perm.sign σ = 1 := by decide
  rw [e, hs] at h
  rw [h]; simp

/-- **The quartic coefficient of `loc^{ab,t}`** (based at `a`): the weighted moment `Mw₄`. -/
theorem cfAB4_locABt {X : Finset (Lam d L N)} {a b : Lam d L N} (ha : a ∈ X) (hab : a ≠ b)
    (F : Alg d L N) :
    cfAB4 a b (locABt X a b F) = Mw X a b sg4 ![true, true, false, false] F := by
  have h1 : IsHom 2 (dbar a b * psi a : Alg d L N) := (isHom_dbar a b).mul (isHom_ι _)
  have h2 : IsHom 2 (psibar a * dlt a b : Alg d L N) := (isHom_ι _).mul (isHom_dlt a b)
  have h3 : IsHom 2 (dbar a b * dlt a b : Alg d L N) := (isHom_dbar a b).mul (isHom_dlt a b)
  rw [locABt, locEven_single_eq' ha subset_rfl, Dt, pbp_dbar_dlt]
  simp only [cfAB4_add, cfAB4_smul, cfAB4_one, cfAB4_of_isHom2 a b (isHom_pbp a),
    cfAB4_of_isHom2 a b h1, cfAB4_of_isHom2 a b h2, cfAB4_of_isHom2 a b h3, cfAB4_m4_self hab]
  ring

/-- **The quartic coefficient of `loc^{ab}_X`**: the weighted moment at the base point. -/
theorem cfAB4_locABtX {X : Finset (Lam d L N)} {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X)
    (hab : a ≠ b) (F : Alg d L N) :
    cfAB4 a b (locABtX X a b F) =
      if a ∈ X then Mw X a b sg4 ![true, true, false, false] F
      else Mw X b a sg4 ![true, true, false, false] F := by
  unfold locABtX
  split_ifs with ha
  · exact cfAB4_locABt ha hab F
  · have hb : b ∈ X := h.resolve_left ha
    rw [cfAB4_comm, cfAB4_locABt hb (Ne.symm hab)]

/-! ### One step -/

section StepM4

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

theorem locABtXY_isSym (X Y : Finset (Lam d L N)) (F : Alg d L N) : IsSym (locABtXY P X Y F) := by
  rw [isSym_iff_mem_SymS, mem_SymS]; exact locABtXY_scal P X Y F

theorem Q2O_ab_sym (b : Fin d → ℕ) : IsSym (Q2O P j K b : SA .two (Lam d L N)).ab := by
  classical
  rw [isSym_iff_mem_SymS]
  unfold Q2O
  split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    exact Subalgebra.sum_mem _ fun X _ => by
      rw [LocO2_ab, ← isSym_iff_mem_SymS]; exact locABtXY_isSym P _ _ _
  · exact zero_mem _

/-- The quartic coefficient of `V_{j+1}(B)`. -/
theorem cfAB4_VpO (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) (b : Fin d → ℕ) :
    cfAB4 P.a P.b (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      cfAB4 P.a P.b (V b : SA .two (Lam d L N)).ab -
        cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab -
        cfAB4 P.a P.b (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).ab = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
  have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      (uVpO P j C V W K b : SA .two (Lam d L N)).ab -
        ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).ab - (upO P j C V W K b : SA .two (Lam d L N)).ab := rfl
  have hsub : ∀ F G : Alg d L N, cfAB4 P.a P.b (F - G) = cfAB4 P.a P.b F - cfAB4 P.a P.b G :=
    fun F G => by
      rw [sub_eq_add_neg, cfAB4_add, show -G = (-1 : ℂ) • G by simp, cfAB4_smul]; ring
  rw [h1, halg, upO_ab_eq, sub_zero, hsub, cfAB4_algebraMap, sub_zero, uVpO_ab, hsub, hsub,
    cfAB4_expLC_of_ab C (hV b) (hS b),
    cfAB4_expLC_of_ab C (Q2O_ab_mem_pair P j K b) (Q2O_ab_sym P j K b)]
  rfl

/-- **The one-step flow of the total quartic coefficient.** -/
theorem m4Tot_succ (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) :
    m4Tot P (j + 1) (Vnext2O P j C V W K) = m4Tot P j V -
      ∑ b ∈ blockIdx (L := L) (N := N) j, cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab -
      ∑ b ∈ blockIdx (L := L) (N := N) j, cfAB4 P.a P.b (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  have e : m4Tot P (j + 1) (Vnext2O P j C V W K) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, cfAB4 P.a P.b (VpO P j C V W K b : SA .two (Lam d L N)).ab := by
    rw [m4Tot, ← sum_blockIdx_succ j]
    refine sum_congr rfl fun c' _ => ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    induction (blocks j (blockSet (L := L) (N := N) (j + 1) c')) using Finset.induction_on with
    | empty => rw [sum_empty, sum_empty]; exact coeff_zero _
    | insert x s hx ih => rw [sum_insert hx, sum_insert hx, cfAB4_add, ih]
  rw [e, sum_congr rfl fun b _ => cfAB4_VpO P j C V W K hV hS b, sum_sub_distrib, sum_sub_distrib]
  rfl

end StepM4

end

end Obs2
