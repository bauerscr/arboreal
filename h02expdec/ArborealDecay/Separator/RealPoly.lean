module

public import Mathlib

/-!
# Elementary facts on real polynomials (supplement `lem:realpoly`)

* `exists_eval_neg_of_odd_natDegree` (item (i)): a nonzero real polynomial of odd degree takes
  a negative value.
* `quot_ge_of_tendsto` (item (ii), specialised to quotients of polynomials): if `P / Q` has
  nonpositive derivative on `[0, ∞)` and tends to `L`, then `P / Q ≥ L` on `[0, ∞)`, and equality
  at a point propagates to the right.
* `eq_zero_of_forall_quadratic_nonneg` (item (iii)).
* `wronskian_ne_zero` (item (iv)).
-/

@[expose] public section

open Polynomial Filter Topology

namespace ArborealDecay.Separator

noncomputable section

/-- Item (i): a nonzero real polynomial of odd degree takes a negative value. -/
theorem exists_eval_neg_of_odd_natDegree {P : ℝ[X]} (hP : P ≠ 0) (hodd : Odd P.natDegree) :
    ∃ t : ℝ, P.eval t < 0 := by
  have hdeg : 0 < P.degree := by
    rw [degree_eq_natDegree hP]; exact_mod_cast hodd.pos
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  rcases lt_or_gt_of_ne hlc with hneg | hpos
  · have := tendsto_atBot_of_leadingCoeff_nonpos P hdeg hneg.le
    exact (this.eventually (eventually_lt_atBot 0)).exists
  · set Q := P.comp (-X) with hQ
    have hQdeg : 0 < Q.degree := by rw [hQ, degree_comp_neg_X]; exact hdeg
    have hQlc : Q.leadingCoeff ≤ 0 := by
      rw [hQ, comp_neg_X_leadingCoeff_eq, hodd.neg_one_pow]; linarith
    obtain ⟨t, ht⟩ :=
      ((tendsto_atBot_of_leadingCoeff_nonpos Q hQdeg hQlc).eventually (eventually_lt_atBot 0)).exists
    exact ⟨-t, by simpa [hQ] using ht⟩

/-- Item (ii) for quotients of polynomials. If `Q` does not vanish on `[0, ∞)`, the Wronskian-type
expression `P Q' - Q P'` is nonnegative there, and `P / Q → L`, then `P / Q ≥ L` on `[0, ∞)`;
moreover, if `P / Q = L` at `t₁ ≥ 0` then `P / Q = L` on `[t₁, ∞)`. -/
theorem quot_ge_of_tendsto {P Q : ℝ[X]} {L : ℝ} (hQ : ∀ t, 0 ≤ t → Q.eval t ≠ 0)
    (hW : ∀ t, 0 ≤ t → 0 ≤ P.eval t * (derivative Q).eval t - Q.eval t * (derivative P).eval t)
    (hL : Tendsto (fun t => P.eval t / Q.eval t) atTop (𝓝 L)) :
    ∀ t, 0 ≤ t → L ≤ P.eval t / Q.eval t ∧
      (P.eval t / Q.eval t = L → ∀ t', t ≤ t' → P.eval t' / Q.eval t' = L) := by
  set g : ℝ → ℝ := fun t => P.eval t / Q.eval t with hg
  have hder : ∀ t, 0 ≤ t → HasDerivAt g (((derivative P).eval t * Q.eval t -
      P.eval t * (derivative Q).eval t) / Q.eval t ^ 2) t := fun t ht =>
    (P.hasDerivAt t).div (Q.hasDerivAt t) (hQ t ht)
  have hanti : AntitoneOn g (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hder t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hder t (le_of_lt ht)).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have := hW t (le_of_lt ht)
      linarith
  have hge : ∀ t, 0 ≤ t → L ≤ g t := by
    intro t ht
    refine le_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop t] with t' ht'
    exact hanti ht (le_trans ht ht') ht'
  intro t ht
  refine ⟨hge t ht, fun heq t' ht' => ?_⟩
  have h1 := hanti ht (le_trans ht ht') ht'
  have h2 := hge t' (le_trans ht ht')
  change g t' = L
  change g t = L at heq
  linarith

/-- Item (iii): if `α y² + β y ≥ 0` for all real `y`, then `β = 0`. -/
theorem eq_zero_of_forall_quadratic_nonneg {α β : ℝ} (h : ∀ y : ℝ, 0 ≤ α * y ^ 2 + β * y) :
    β = 0 := by
  by_contra hβ
  set ε : ℝ := 1 / (1 + |α|) with hε
  have hεpos : 0 < ε := by positivity
  have hαε : α * ε < 1 := by
    rw [hε, mul_one_div, div_lt_one (by positivity)]
    linarith [le_abs_self α]
  have := h (-ε * β)
  have hβ2 : 0 < β ^ 2 := by positivity
  have : α * (-ε * β) ^ 2 + β * (-ε * β) = ε * β ^ 2 * (α * ε - 1) := by ring
  nlinarith [mul_pos hεpos hβ2]

/-- Item (iv): if `deg U = m ≥ 1`, `X ≠ 0` and `deg X < m`, then `U X' - X U' ≠ 0`. -/
theorem wronskian_ne_zero {U X : ℝ[X]} (hU : 1 ≤ U.natDegree) (hX : X ≠ 0)
    (hXU : X.natDegree < U.natDegree) :
    U * derivative X - X * derivative U ≠ 0 := by
  set m := U.natDegree with hm
  set k := X.natDegree with hk
  have hu : U.coeff m ≠ 0 := by
    have hU0 : U ≠ 0 := by rintro rfl; simp [hm] at hU
    simpa [hm] using leadingCoeff_ne_zero.mpr hU0
  have hχ : X.coeff k ≠ 0 := by simpa [hk] using leadingCoeff_ne_zero.mpr hX
  have hdU : (derivative U).natDegree ≤ m - 1 := natDegree_derivative_le U
  have hcU : (derivative U).coeff (m - 1) = U.coeff m * m := by
    rw [coeff_derivative]
    have : m - 1 + 1 = m := by omega
    rw [this]; push_cast [Nat.cast_sub hU]; ring
  -- coefficient of `t^(k + (m-1))`
  have h2 : (X * derivative U).coeff (k + (m - 1)) = X.coeff k * (U.coeff m * m) := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl hdU, hcU]
  have h1 : (U * derivative X).coeff (k + (m - 1)) = U.coeff m * (X.coeff k * k) := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · have hX0 : derivative X = 0 := by
        rw [eq_C_of_natDegree_eq_zero h0]; simp
      rw [hX0, h0]; simp
    · have hdX : (derivative X).natDegree ≤ k - 1 := natDegree_derivative_le X
      have : k + (m - 1) = m + (k - 1) := by omega
      rw [this, coeff_mul_add_eq_of_natDegree_le le_rfl hdX, coeff_derivative]
      have : k - 1 + 1 = k := by omega
      rw [this]; push_cast [Nat.cast_sub hpos]; ring
  intro h0
  have := congrArg (fun P => P.coeff (k + (m - 1))) h0
  simp only [coeff_sub, h1, h2, coeff_zero] at this
  have hkm : (k : ℝ) - m ≠ 0 := by
    have : (k : ℝ) < m := by exact_mod_cast hXU
    linarith
  have : U.coeff m * X.coeff k * ((k : ℝ) - m) = 0 := by linear_combination this
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hu h
    · exact hχ h
  · exact hkm h

end

end ArborealDecay.Separator
