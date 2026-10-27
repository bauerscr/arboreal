import Obs2.Flow.GradAB1

/-!
# The gradient coefficients of `V'_{ab}`: a scale-weighted size, its sources, one step

For the flow of the gradient part of `V'_k(B)_{ab}` across scales the T-norm is not convenient (it
is not monotone under a change of scale); the coefficient size of `Obs2.tNorm_gradAB_le` is. With a
fixed separation scale `E` (an upper bound for `|e|₁`, e.g. `d|a−b|_∞`) and `g = Eℓ/h`:

  `gSzE E a b h ℓ F = (|c_{ab}+c_{bb}| + |c_{ba}+c_{bb}|)ℓg + |c_{bb}|g² + |M₄|ℓ²g²`

(the gradient coefficients seen from `a`). Here:

* algebra: **`gSzE_add_le`**, `gSzE_smul`, `gSzE_sum_le`, `gSzE_neg`, `gSzE_sub_le`,
  **`gSzE_scale_le`** (`h ≤ h'`, `ℓ' ≤ ℓ`: `gSzE h' ℓ' ≤ (h/h')gSzE h ℓ` — every term carries a
  factor `h^{-1}`; one step `h' = Lh` gives the contraction `1/L`), `gSzE_mono_E`,
  **`tNorm_le_gSzE`** (`‖F‖_{T_h(ℓ)} ≤ |ε| + |m₂|ℓ² + gSzE` for `|e_X|₁ ≤ E`);
* coefficients of the localisation remainders: **`gradCf_Dt`** (based at `a`), **`gradCf_Dt_swap`**
  (based at `b`, seen from `a`), `gradCf_pbp_sub`;
* sources: **`gSzE_Dt_le`**: `gSzE(Dt_{X,a,b}F) ≤ K_G(L^j/h)‖F‖_{T_j(ℓ)}` (`norm_Mw_le`; needs
  `E|e_X|₁ ≤ κ|e_X|²`, true for `E = d|a−b|_∞` with `κ = d²`, `eN1_mul_le`), **`gSzE_Dt_swap_le`**
  (base `b`, with `E ≤ ηh`), **`gSzE_locABtX_le`**, **`gSzE_locABtXY_le`**;
* one step: **`gSzE_VpO_le`**: `gSzE(V_{j+1}(B)) ≤ gSzE(V(B)) + |M₄(V(B))|gSzE(ℒ_C m₄) + gSzE(Q(B)) +
  |M₄(Q(B))|gSzE(ℒ_C m₄) + gSzE(Loc S(B))` (`cfAB2_VpO`, `cfAB4_VpO`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

/-- The scale-weighted size of the gradient coefficients (seen from `a`), separation `E`. -/
def gSzE (E : ℝ) (a b : Lam d L N) (h ℓ : ℝ) (F : Alg d L N) : ℝ :=
  (‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 b a F + cfAB2 b b F‖) * (ℓ * (E * ℓ * h⁻¹)) +
    ‖cfAB2 b b F‖ * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) +
    ‖cfAB4 a b F‖ * (ℓ * ℓ * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)))

section Alg

variable {E h ℓ : ℝ} (hE : 0 ≤ E) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
include hE hh hℓ

theorem gSzE_nonneg (a b : Lam d L N) (F : Alg d L N) : 0 ≤ gSzE E a b h ℓ F := by
  have hg : 0 ≤ E * ℓ * h⁻¹ := by positivity
  unfold gSzE
  have h1 : 0 ≤ ℓ * (E * ℓ * h⁻¹) := mul_nonneg hℓ hg
  have h2 : 0 ≤ (E * ℓ * h⁻¹) * (E * ℓ * h⁻¹) := mul_nonneg hg hg
  have h3 : 0 ≤ ℓ * ℓ * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) := mul_nonneg (mul_nonneg hℓ hℓ) h2
  have := mul_nonneg (add_nonneg (norm_nonneg (cfAB2 a b F + cfAB2 b b F))
    (norm_nonneg (cfAB2 b a F + cfAB2 b b F))) h1
  have := mul_nonneg (norm_nonneg (cfAB2 b b F)) h2
  have := mul_nonneg (norm_nonneg (cfAB4 a b F)) h3
  linarith

theorem gSzE_add_le (a b : Lam d L N) (F G : Alg d L N) :
    gSzE E a b h ℓ (F + G) ≤ gSzE E a b h ℓ F + gSzE E a b h ℓ G := by
  have hg : 0 ≤ E * ℓ * h⁻¹ := by positivity
  have h1 : 0 ≤ ℓ * (E * ℓ * h⁻¹) := mul_nonneg hℓ hg
  have h2 : 0 ≤ (E * ℓ * h⁻¹) * (E * ℓ * h⁻¹) := mul_nonneg hg hg
  have h3 : 0 ≤ ℓ * ℓ * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) := mul_nonneg (mul_nonneg hℓ hℓ) h2
  unfold gSzE
  simp only [cfAB2_add, cfAB4_add]
  have e1 : ‖cfAB2 a b F + cfAB2 a b G + (cfAB2 b b F + cfAB2 b b G)‖ ≤
      ‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 a b G + cfAB2 b b G‖ := by
    rw [show cfAB2 a b F + cfAB2 a b G + (cfAB2 b b F + cfAB2 b b G) =
      (cfAB2 a b F + cfAB2 b b F) + (cfAB2 a b G + cfAB2 b b G) by ring]
    exact norm_add_le _ _
  have e2 : ‖cfAB2 b a F + cfAB2 b a G + (cfAB2 b b F + cfAB2 b b G)‖ ≤
      ‖cfAB2 b a F + cfAB2 b b F‖ + ‖cfAB2 b a G + cfAB2 b b G‖ := by
    rw [show cfAB2 b a F + cfAB2 b a G + (cfAB2 b b F + cfAB2 b b G) =
      (cfAB2 b a F + cfAB2 b b F) + (cfAB2 b a G + cfAB2 b b G) by ring]
    exact norm_add_le _ _
  have e3 := norm_add_le (cfAB2 b b F) (cfAB2 b b G)
  have e4 := norm_add_le (cfAB4 a b F) (cfAB4 a b G)
  have f1 := mul_le_mul_of_nonneg_right (add_le_add e1 e2) h1
  have f2 := mul_le_mul_of_nonneg_right e3 h2
  have f3 := mul_le_mul_of_nonneg_right e4 h3
  linarith

theorem gSzE_smul (a b : Lam d L N) (r : ℂ) (F : Alg d L N) :
    gSzE E a b h ℓ (r • F) = ‖r‖ * gSzE E a b h ℓ F := by
  unfold gSzE
  simp only [cfAB2_smul, cfAB4_smul, ← mul_add, norm_mul]
  ring

theorem gSzE_neg (a b : Lam d L N) (F : Alg d L N) :
    gSzE E a b h ℓ (-F) = gSzE E a b h ℓ F := by
  rw [show -F = (-1 : ℂ) • F by simp, gSzE_smul hE hh hℓ, norm_neg, norm_one, one_mul]

theorem gSzE_sub_le (a b : Lam d L N) (F G : Alg d L N) :
    gSzE E a b h ℓ (F - G) ≤ gSzE E a b h ℓ F + gSzE E a b h ℓ G := by
  rw [sub_eq_add_neg]
  exact (gSzE_add_le hE hh hℓ a b F (-G)).trans_eq (by rw [gSzE_neg hE hh hℓ])

theorem gSzE_sum_le {ι : Type*} (s : Finset ι) (f : ι → Alg d L N) (a b : Lam d L N) :
    gSzE E a b h ℓ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, gSzE E a b h ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty]
    unfold gSzE
    simp only [show cfAB2 a b (0 : Alg d L N) = 0 from coeff_zero _,
      show cfAB2 b a (0 : Alg d L N) = 0 from coeff_zero _,
      show cfAB2 b b (0 : Alg d L N) = 0 from coeff_zero _,
      show cfAB4 a b (0 : Alg d L N) = 0 from coeff_zero _]
    simp
  | insert x s hx ih =>
    rw [sum_insert hx, sum_insert hx]
    exact (gSzE_add_le hE hh hℓ a b _ _).trans (add_le_add le_rfl ih)

end Alg

/-- **The change of scale**: `h ≤ h'`, `ℓ' ≤ ℓ` give `gSzE h' ℓ' ≤ (h/h')gSzE h ℓ`. -/
theorem gSzE_scale_le {E h h' ℓ ℓ' : ℝ} (hE : 0 ≤ E) (hh : 0 < h) (hhh : h ≤ h') (hℓ' : 0 ≤ ℓ')
    (hℓℓ : ℓ' ≤ ℓ) (a b : Lam d L N) (F : Alg d L N) :
    gSzE E a b h' ℓ' F ≤ h * h'⁻¹ * gSzE E a b h ℓ F := by
  have hh' : 0 < h' := hh.trans_le hhh
  set r := h * h'⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, ← div_eq_mul_inv, div_le_one hh']; exact hhh
  have hinv : h'⁻¹ = r * h⁻¹ := by rw [hr]; field_simp
  have hℓ : 0 ≤ ℓ := hℓ'.trans hℓℓ
  set g := E * ℓ * h⁻¹ with hg
  have hg0 : 0 ≤ g := by positivity
  have hg' : E * ℓ' * h'⁻¹ ≤ r * g := by
    rw [hinv, hg]
    have : E * ℓ' ≤ E * ℓ := mul_le_mul_of_nonneg_left hℓℓ hE
    have h1 : 0 ≤ r * h⁻¹ := by positivity
    calc E * ℓ' * (r * h⁻¹) ≤ E * ℓ * (r * h⁻¹) := mul_le_mul_of_nonneg_right this h1
      _ = r * (E * ℓ * h⁻¹) := by ring
  have hg'0 : 0 ≤ E * ℓ' * h'⁻¹ := by positivity
  set g' := E * ℓ' * h'⁻¹
  have w1 : ℓ' * g' ≤ r * (ℓ * g) := by
    calc ℓ' * g' ≤ ℓ * (r * g) := mul_le_mul hℓℓ hg' hg'0 hℓ
      _ = r * (ℓ * g) := by ring
  have w2 : g' * g' ≤ r * (g * g) := by
    calc g' * g' ≤ (r * g) * (r * g) := mul_le_mul hg' hg' hg'0 (by positivity)
      _ = r * (r * (g * g)) := by ring
      _ ≤ r * (1 * (g * g)) := by
          gcongr
      _ = r * (g * g) := by ring
  have w3 : ℓ' * ℓ' * (g' * g') ≤ r * (ℓ * ℓ * (g * g)) := by
    calc ℓ' * ℓ' * (g' * g') ≤ ℓ * ℓ * (r * (g * g)) :=
          mul_le_mul (mul_le_mul hℓℓ hℓℓ hℓ' hℓ) w2 (by positivity) (by positivity)
      _ = r * (ℓ * ℓ * (g * g)) := by ring
  unfold gSzE
  rw [← hg]
  have n1 := add_nonneg (norm_nonneg (cfAB2 a b F + cfAB2 b b F))
    (norm_nonneg (cfAB2 b a F + cfAB2 b b F))
  have f1 := mul_le_mul_of_nonneg_left w1 n1
  have f2 := mul_le_mul_of_nonneg_left w2 (norm_nonneg (cfAB2 b b F))
  have f3 := mul_le_mul_of_nonneg_left w3 (norm_nonneg (cfAB4 a b F))
  calc _ ≤ (‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 b a F + cfAB2 b b F‖) * (r * (ℓ * g)) +
        ‖cfAB2 b b F‖ * (r * (g * g)) + ‖cfAB4 a b F‖ * (r * (ℓ * ℓ * (g * g))) := by
        linarith
    _ = _ := by ring

/-- `gSzE` is monotone in the separation scale. -/
theorem gSzE_mono_E {E E' h ℓ : ℝ} (hE : 0 ≤ E) (hEE : E ≤ E') (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (a b : Lam d L N) (F : Alg d L N) : gSzE E a b h ℓ F ≤ gSzE E' a b h ℓ F := by
  have hg : E * ℓ * h⁻¹ ≤ E' * ℓ * h⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEE hℓ) (inv_nonneg.2 hh)
  have hg0 : 0 ≤ E * ℓ * h⁻¹ := by positivity
  unfold gSzE
  have n1 := add_nonneg (norm_nonneg (cfAB2 a b F + cfAB2 b b F))
    (norm_nonneg (cfAB2 b a F + cfAB2 b b F))
  have w1 := mul_le_mul_of_nonneg_left hg hℓ
  have w2 := mul_le_mul hg hg hg0 (hg0.trans hg)
  have w3 := mul_le_mul_of_nonneg_left w2 (mul_nonneg hℓ hℓ)
  have f1 := mul_le_mul_of_nonneg_left w1 n1
  have f2 := mul_le_mul_of_nonneg_left w2 (norm_nonneg (cfAB2 b b F))
  have f3 := mul_le_mul_of_nonneg_left w3 (norm_nonneg (cfAB4 a b F))
  linarith

/-! ### The coefficients of the localisation remainders -/

theorem cfAB2_Dt (X : Finset (Lam d L N)) (a b u v : Lam d L N) (F : Alg d L N) :
    cfAB2 u v (Dt X a b F) =
      Mw X a b sg2 ![true, false] F * (cfAB2 u v (m2 b a) - cfAB2 u v (m2 a a)) +
      Mw X a b sg2 ![false, true] F * (cfAB2 u v (m2 a b) - cfAB2 u v (m2 a a)) +
      Mw X a b sg2 ![true, true] F * (cfAB2 u v (m2 b b) - cfAB2 u v (m2 b a) -
        cfAB2 u v (m2 a b) + cfAB2 u v (m2 a a)) := by
  have e1 : (dbar a b * psi a : Alg d L N) = m2 b a - m2 a a := by
    unfold dbar m2; rw [sub_mul]
  have e2 : (psibar a * dlt a b : Alg d L N) = m2 a b - m2 a a := by
    unfold dlt m2; rw [mul_sub]
  have e3 : (dbar a b * dlt a b : Alg d L N) = m2 b b - m2 b a - m2 a b + m2 a a := by
    unfold dbar dlt m2; rw [sub_mul, mul_sub, mul_sub]; abel
  unfold Dt
  rw [pbp_dbar_dlt, e1, e2, e3]
  simp only [cfAB2_add, cfAB2_sub, cfAB2_smul, cfAB2_m4, mul_zero, add_zero]

theorem cfAB4_Dt {X : Finset (Lam d L N)} {a b : Lam d L N} (hab : a ≠ b) (F : Alg d L N) :
    cfAB4 a b (Dt X a b F) = Mw X a b sg4 ![true, true, false, false] F := by
  have e1 : (dbar a b * psi a : Alg d L N) = m2 b a - m2 a a := by
    unfold dbar m2; rw [sub_mul]
  have e2 : (psibar a * dlt a b : Alg d L N) = m2 a b - m2 a a := by
    unfold dlt m2; rw [mul_sub]
  have e3 : (dbar a b * dlt a b : Alg d L N) = m2 b b - m2 b a - m2 a b + m2 a a := by
    unfold dbar dlt m2; rw [sub_mul, mul_sub, mul_sub]; abel
  unfold Dt
  rw [pbp_dbar_dlt, e1, e2, e3]
  simp only [cfAB4_add, cfAB4_sub, cfAB4_smul, cfAB4_m2, cfAB4_m4_self hab]
  ring

/-- **The gradient coefficients of `Dt_{X,a,b}`** (seen from `a`): `M₀₁`, `M₁₀`, `M₁₁`, `M₄`. -/
theorem gradCf_Dt (X : Finset (Lam d L N)) {a b : Lam d L N} (hab : a ≠ b) (F : Alg d L N) :
    cfAB2 a b (Dt X a b F) + cfAB2 b b (Dt X a b F) = Mw X a b sg2 ![false, true] F ∧
      cfAB2 b a (Dt X a b F) + cfAB2 b b (Dt X a b F) = Mw X a b sg2 ![true, false] F ∧
      cfAB2 b b (Dt X a b F) = Mw X a b sg2 ![true, true] F := by
  simp only [cfAB2_Dt, cfAB2_m2, hab, Ne.symm hab, and_self, and_true, and_false,
    if_true, if_false]
  refine ⟨by ring, by ring, by ring⟩

/-- **The gradient coefficients of `Dt_{X,b,a}`, seen from `a`**: `−M₀₁'`, `−M₁₀'`,
`M₁₁' − M₁₀' − M₀₁'` (`M' = Mw_{X,b,a}`). -/
theorem gradCf_Dt_swap (X : Finset (Lam d L N)) {a b : Lam d L N} (hab : a ≠ b) (F : Alg d L N) :
    cfAB2 a b (Dt X b a F) + cfAB2 b b (Dt X b a F) = -Mw X b a sg2 ![false, true] F ∧
      cfAB2 b a (Dt X b a F) + cfAB2 b b (Dt X b a F) = -Mw X b a sg2 ![true, false] F ∧
      cfAB2 b b (Dt X b a F) = Mw X b a sg2 ![true, true] F - Mw X b a sg2 ![true, false] F -
        Mw X b a sg2 ![false, true] F := by
  simp only [cfAB2_Dt, cfAB2_m2, hab, Ne.symm hab, and_self, and_true, and_false,
    if_true, if_false]
  refine ⟨by ring, by ring, by ring⟩

/-! ### The sources -/

/-- The constant of `gSzE_Dt_le`. -/
def KG (d : ℕ) (Cc κ : ℝ) : ℝ :=
  32 * Cc ^ 2 * κ * 2 ^ (d + 1) + (32 * Cc ^ 2 * κ ^ 2 + 1536 * Cc ^ 4 * κ ^ 2) * 4 ^ (d + 1)

theorem KG_nonneg (d : ℕ) {Cc κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ KG d Cc κ := by unfold KG; positivity

/-- The real arithmetic of `gSzE_Dt_le`. -/
theorem gSzE_Dt_real {Cc κ R hi T ℓ ℓ' E At m01 m10 m11 m4 : ℝ} (hCc : 0 ≤ Cc) (hκ : 0 ≤ κ)
    (hR : 0 ≤ R) (hhi : 0 ≤ hi) (hT : 0 ≤ T) (hℓ : 0 < ℓ) (hℓ' : 0 ≤ ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ)
    (hE : 0 ≤ E) (hA : 0 ≤ At) (hAE : At * E ≤ 2 * Cc * R * κ)
    (h01 : m01 ≤ 2 * (ℓ⁻¹ ^ 2 * (Cc * At)) * T) (h10 : m10 ≤ 2 * (ℓ⁻¹ ^ 2 * (At * Cc)) * T)
    (h11 : m11 ≤ 2 * (ℓ⁻¹ ^ 2 * (At * At)) * T)
    (h4 : m4 ≤ 24 * (ℓ⁻¹ ^ 4 * (At * At * (Cc * Cc))) * T)
    (h01' : 0 ≤ m01) (h10' : 0 ≤ m10) (h11' : 0 ≤ m11) (h4' : 0 ≤ m4) :
    (m01 + m10) * (ℓ' * (E * ℓ' * hi)) + m11 * ((E * ℓ' * hi) * (E * ℓ' * hi)) +
        m4 * (ℓ' * ℓ' * ((E * ℓ' * hi) * (E * ℓ' * hi))) ≤
      (32 * Cc ^ 2 * κ * (R * hi) + (32 * Cc ^ 2 * κ ^ 2 + 1536 * Cc ^ 4 * κ ^ 2) *
        ((R * hi) * (R * hi))) * T := by
  set q := ℓ' * ℓ⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq2 : q ≤ 2 := by
    rw [hq, ← div_eq_mul_inv, div_le_iff₀ hℓ]; linarith
  have hℓe : ℓ' = q * ℓ := by rw [hq]; field_simp
  have hqq : q * q ≤ 4 := by nlinarith
  set x := At * E with hx
  have hx0 : 0 ≤ x := mul_nonneg hA hE
  have hxx : x * x ≤ (2 * Cc * R * κ) * (2 * Cc * R * κ) := mul_le_mul hAE hAE hx0 (by positivity)
  have hlinv : ℓ⁻¹ * ℓ = 1 := inv_mul_cancel₀ hℓ.ne'
  -- term 1
  have t1 : (m01 + m10) * (ℓ' * (E * ℓ' * hi)) ≤ 4 * Cc * (q * q) * x * hi * T := by
    have hw : 0 ≤ ℓ' * (E * ℓ' * hi) := by positivity
    calc (m01 + m10) * (ℓ' * (E * ℓ' * hi)) ≤
          (2 * (ℓ⁻¹ ^ 2 * (Cc * At)) * T + 2 * (ℓ⁻¹ ^ 2 * (At * Cc)) * T) *
            (ℓ' * (E * ℓ' * hi)) := mul_le_mul_of_nonneg_right (add_le_add h01 h10) hw
      _ = 4 * Cc * (q * q) * x * hi * T * ((ℓ⁻¹ * ℓ) * (ℓ⁻¹ * ℓ)) := by
          rw [hℓe, hx, hq]; ring
      _ = _ := by rw [hlinv]; ring
  have t2 : m11 * ((E * ℓ' * hi) * (E * ℓ' * hi)) ≤ 2 * (q * q) * (x * x) * (hi * hi) * T := by
    have hw : 0 ≤ (E * ℓ' * hi) * (E * ℓ' * hi) := by positivity
    calc m11 * ((E * ℓ' * hi) * (E * ℓ' * hi)) ≤
          2 * (ℓ⁻¹ ^ 2 * (At * At)) * T * ((E * ℓ' * hi) * (E * ℓ' * hi)) :=
          mul_le_mul_of_nonneg_right h11 hw
      _ = 2 * (q * q) * (x * x) * (hi * hi) * T * ((ℓ⁻¹ * ℓ) * (ℓ⁻¹ * ℓ)) := by
          rw [hℓe, hx, hq]; ring
      _ = _ := by rw [hlinv]; ring
  have t3 : m4 * (ℓ' * ℓ' * ((E * ℓ' * hi) * (E * ℓ' * hi))) ≤
      24 * ((q * q) * (q * q)) * (x * x) * (Cc * Cc) * (hi * hi) * T := by
    have hw : 0 ≤ ℓ' * ℓ' * ((E * ℓ' * hi) * (E * ℓ' * hi)) := by positivity
    calc m4 * (ℓ' * ℓ' * ((E * ℓ' * hi) * (E * ℓ' * hi))) ≤
          24 * (ℓ⁻¹ ^ 4 * (At * At * (Cc * Cc))) * T *
            (ℓ' * ℓ' * ((E * ℓ' * hi) * (E * ℓ' * hi))) := mul_le_mul_of_nonneg_right h4 hw
      _ = 24 * ((q * q) * (q * q)) * (x * x) * (Cc * Cc) * (hi * hi) * T *
            ((ℓ⁻¹ * ℓ) * (ℓ⁻¹ * ℓ) * ((ℓ⁻¹ * ℓ) * (ℓ⁻¹ * ℓ))) := by
          rw [hℓe, hx, hq]; ring
      _ = _ := by rw [hlinv]; ring
  have s1 : 4 * Cc * (q * q) * x * hi * T ≤ 32 * Cc ^ 2 * κ * (R * hi) * T := by
    have := mul_le_mul hqq hAE hx0 (by norm_num)
    calc 4 * Cc * (q * q) * x * hi * T = 4 * Cc * hi * T * ((q * q) * x) := by ring
      _ ≤ 4 * Cc * hi * T * (4 * (2 * Cc * R * κ)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have s2 : 2 * (q * q) * (x * x) * (hi * hi) * T ≤
      32 * Cc ^ 2 * κ ^ 2 * ((R * hi) * (R * hi)) * T := by
    have := mul_le_mul hqq hxx (mul_nonneg hx0 hx0) (by norm_num)
    calc 2 * (q * q) * (x * x) * (hi * hi) * T = 2 * (hi * hi) * T * ((q * q) * (x * x)) := by
          ring
      _ ≤ 2 * (hi * hi) * T * (4 * ((2 * Cc * R * κ) * (2 * Cc * R * κ))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have s3 : 24 * ((q * q) * (q * q)) * (x * x) * (Cc * Cc) * (hi * hi) * T ≤
      1536 * Cc ^ 4 * κ ^ 2 * ((R * hi) * (R * hi)) * T := by
    have hq4 : (q * q) * (q * q) ≤ 16 := by
      have := mul_le_mul hqq hqq (mul_nonneg hq0 hq0) (by norm_num); linarith
    have := mul_le_mul hq4 hxx (mul_nonneg hx0 hx0) (by norm_num)
    calc 24 * ((q * q) * (q * q)) * (x * x) * (Cc * Cc) * (hi * hi) * T =
          24 * (Cc * Cc) * (hi * hi) * T * (((q * q) * (q * q)) * (x * x)) := by ring
      _ ≤ 24 * (Cc * Cc) * (hi * hi) * T * (16 * ((2 * Cc * R * κ) * (2 * Cc * R * κ))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have e : (32 * Cc ^ 2 * κ * (R * hi) + (32 * Cc ^ 2 * κ ^ 2 + 1536 * Cc ^ 4 * κ ^ 2) *
        ((R * hi) * (R * hi))) * T = 32 * Cc ^ 2 * κ * (R * hi) * T +
      32 * Cc ^ 2 * κ ^ 2 * ((R * hi) * (R * hi)) * T +
      1536 * Cc ^ 4 * κ ^ 2 * ((R * hi) * (R * hi)) * T := by ring
  rw [e]
  linarith

/-- `E·|e|₁/|e|² ≤ κ` from `E|e|₁ ≤ κ|e|²`. -/
theorem At_mul_le {Cc R E κ e1 e2 : ℝ} (hCc : 0 ≤ Cc) (hR : 0 ≤ R) (he2 : 0 ≤ e2) (hκ : 0 ≤ κ)
    (h : E * e1 ≤ κ * e2) : 2 * Cc * R * e1 * e2⁻¹ * E ≤ 2 * Cc * R * κ := by
  have h1 : E * e1 * e2⁻¹ ≤ κ := by
    rcases he2.eq_or_lt with h0 | hpos
    · rw [← h0, inv_zero, mul_zero]; exact hκ
    · rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact h
  calc 2 * Cc * R * e1 * e2⁻¹ * E = 2 * Cc * R * (E * e1 * e2⁻¹) := by ring
    _ ≤ 2 * Cc * R * κ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **The gradient source of `loc^{ab,t}` based at `a`**:
`gSzE(Dt_{X,a,b}F) ≤ K_G(L^j/h)‖F‖_{T_j(ℓ)}` for `E|e_X|₁ ≤ κ|e_X|²`, `h ≥ L^j`, `ℓ' ≤ 2ℓ`. -/
theorem gSzE_Dt_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a b : Lam d L N} (ha : a ∈ nbhd j X) (hab : a ≠ b)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ ℓ' h E κ : ℝ} (hℓ : 0 < ℓ)
    (hℓ' : 0 ≤ ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h) (hsh : (L : ℝ) ^ j ≤ h) (hE : 0 ≤ E)
    (hκ : 0 ≤ κ) (hEκ : E * eN1 X a b ≤ κ * eN2 X a b) :
    gSzE E a b h ℓ' (Dt X a b F) ≤ KG d Cc κ * ((L : ℝ) ^ j * h⁻¹) * (Tj d (L : ℝ) j ℓ F).toReal := by
  set T := (Tj d (L : ℝ) j ℓ F).toReal with hT
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  obtain ⟨g1, g2, g3⟩ := gradCf_Dt X hab F
  have h4 := cfAB4_Dt (X := X) hab F
  set At := 2 * Cc * (rad d L j : ℝ) * eN1 X a b * (eN2 X a b)⁻¹ with hAt
  have hA0 : 0 ≤ At := by
    have := eN1_nonneg X a b; have := inv_nonneg.2 (eN2_nonneg X a b); positivity
  have hR0 : (0 : ℝ) ≤ (rad d L j : ℝ) := Nat.cast_nonneg _
  have hAE : At * E ≤ 2 * Cc * (rad d L j : ℝ) * κ :=
    At_mul_le hCc0 hR0 (eN2_nonneg X a b) hκ hEκ
  have m10 := norm_M10_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg2 ![true, false] hℓ)
  have m01 := norm_M01_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg2 ![false, true] hℓ)
  have m11 := norm_M11_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg2 ![true, true] hℓ)
  have m4 := norm_M4_le (norm_Mw_le hCc0 hCc hL hj hX ha b hF sg4 ![true, true, false, false] hℓ)
  unfold gSzE
  rw [g1, g2, g3, h4]
  have key := gSzE_Dt_real hCc0 hκ hR0 (inv_nonneg.2 hh.le) hT0 hℓ hℓ' hℓℓ hE hA0 hAE m01 m10 m11
    m4 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  refine key.trans ?_
  have hR : ((rad d L j : ℕ) : ℝ) * h⁻¹ = 2 ^ (d + 1) * ((L : ℝ) ^ j * h⁻¹) := by
    push_cast [rad]; ring
  have hu0 : 0 ≤ (L : ℝ) ^ j * h⁻¹ := by positivity
  have hu1 : (L : ℝ) ^ j * h⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hh]; exact hsh
  rw [hR]
  set u := (L : ℝ) ^ j * h⁻¹
  have huu : (2 ^ (d + 1) * u) * (2 ^ (d + 1) * u) ≤ 4 ^ (d + 1) * u := by
    have e : (2 ^ (d + 1) * u) * (2 ^ (d + 1) * u) = 4 ^ (d + 1) * (u * u) := by
      rw [show (4 : ℝ) ^ (d + 1) = 2 ^ (d + 1) * 2 ^ (d + 1) by
        rw [← mul_pow]; norm_num]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hc0 : 0 ≤ 32 * Cc ^ 2 * κ ^ 2 + 1536 * Cc ^ 4 * κ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left huu hc0
  have := mul_le_mul_of_nonneg_right this hT0
  unfold KG
  nlinarith

theorem eN2_swap (X : Finset (Lam d L N)) (a b : Lam d L N) : eN2 X b a = eN2 X a b := by
  unfold eN2 eV
  exact sum_congr rfl fun i _ => by rw [← neg_sub, neg_sq]

/-- **`|e|₁·|a−b|_∞ ≤ d|e|²`**: the separation hypothesis of `gSzE_Dt_le` holds for
`E = d|a−b|_∞`, `κ = d²`. -/
theorem eN1_mul_supNorm_le (hd : 1 ≤ d) (X : Finset (Lam d L N)) (a b : Lam d L N) :
    eN1 X a b * ((supNorm (a - b) : ℕ) : ℝ) ≤ d * eN2 X a b := by
  have h1 := eN1_sq_le X a b
  have h2 := supNorm_sq_le_eN2 X a b
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he := eN2_nonneg X a b
  have hs0 : (0 : ℝ) ≤ ((supNorm (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : (eN1 X a b * ((supNorm (a - b) : ℕ) : ℝ)) ^ 2 ≤ (d * eN2 X a b) ^ 2 := by
    rw [mul_pow, mul_pow]
    calc eN1 X a b ^ 2 * ((supNorm (a - b) : ℕ) : ℝ) ^ 2 ≤ (d * eN2 X a b) * eN2 X a b :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ ≤ (d : ℝ) ^ 2 * eN2 X a b ^ 2 := by
          have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right this (sq_nonneg (eN2 X a b))
          nlinarith
  exact (pow_le_pow_iff_left₀ (mul_nonneg (eN1_nonneg X a b) hs0) (by positivity)
    two_ne_zero).1 hsq

theorem gSzE_mul_eq {E h ℓ : ℝ} (a b : Lam d L N) (F : Alg d L N) : gSzE E a b h ℓ F =
    (‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 b a F + cfAB2 b b F‖) * (ℓ * (E * ℓ * h⁻¹)) +
    ‖cfAB2 b b F‖ * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) +
    ‖cfAB4 a b F‖ * (ℓ * ℓ * ((E * ℓ * h⁻¹) * (E * ℓ * h⁻¹))) := rfl

/-- **The gradient source of `loc^{ab,t}` based at `b`, seen from `a`**: with `E/h ≤ η`,
`gSzE(Dt_{X,b,a}F) ≤ (1 + η)K_G(L^j/h)‖F‖_{T_j(ℓ)}`. -/
theorem gSzE_Dt_swap_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a b : Lam d L N} (hb : b ∈ nbhd j X) (hab : a ≠ b)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ ℓ' h E κ η : ℝ} (hℓ : 0 < ℓ)
    (hℓ' : 0 ≤ ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h) (hsh : (L : ℝ) ^ j ≤ h) (hE : 0 ≤ E)
    (hκ : 0 ≤ κ) (hEκ : E * eN1 X a b ≤ κ * eN2 X a b) (hη : E * h⁻¹ ≤ η) :
    gSzE E a b h ℓ' (Dt X b a F) ≤
      (1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹) * (Tj d (L : ℝ) j ℓ F).toReal) := by
  have hEκ' : E * eN1 X b a ≤ κ * eN2 X b a := by rw [eN1_swap, eN2_swap]; exact hEκ
  have hB := gSzE_Dt_le hCc0 hCc hL hj hX hb (Ne.symm hab) hF hℓ hℓ' hℓℓ hh hsh hE hκ hEκ'
  obtain ⟨g1, g2, g3⟩ := gradCf_Dt X (Ne.symm hab) F
  obtain ⟨s1, s2, s3⟩ := gradCf_Dt_swap X hab F
  rw [gSzE_mul_eq] at hB
  rw [g1, g2, g3, cfAB4_comm b a] at hB
  rw [gSzE_mul_eq, s1, s2, s3]
  set M01 := Mw X b a sg2 ![false, true] F
  set M10 := Mw X b a sg2 ![true, false] F
  set M11 := Mw X b a sg2 ![true, true] F
  set M4 := cfAB4 a b (Dt X b a F)
  set g := E * ℓ' * h⁻¹ with hg
  have hg0 : 0 ≤ g := by positivity
  set Br := (‖M01‖ + ‖M10‖) * (ℓ' * g) + ‖M11‖ * (g * g) + ‖M4‖ * (ℓ' * ℓ' * (g * g))
  have hB' : Br ≤ KG d Cc κ * ((L : ℝ) ^ j * h⁻¹) * (Tj d (L : ℝ) j ℓ F).toReal := by
    calc Br = (‖M01‖ + ‖M10‖) * (ℓ' * g) + ‖M11‖ * (g * g) + ‖M4‖ * (ℓ' * ℓ' * (g * g)) := rfl
      _ ≤ _ := by linarith [hB]
  have hBr0 : 0 ≤ Br := by
    have := mul_nonneg (add_nonneg (norm_nonneg M01) (norm_nonneg M10)) (mul_nonneg hℓ' hg0)
    have := mul_nonneg (norm_nonneg M11) (mul_nonneg hg0 hg0)
    have := mul_nonneg (norm_nonneg M4) (mul_nonneg (mul_nonneg hℓ' hℓ') (mul_nonneg hg0 hg0))
    linarith
  have hgg : g * g = (ℓ' * g) * (E * h⁻¹) := by rw [hg]; ring
  have hx : (‖M01‖ + ‖M10‖) * (g * g) ≤ η * Br := by
    rw [hgg]
    have h1 : 0 ≤ (‖M01‖ + ‖M10‖) * (ℓ' * g) :=
      mul_nonneg (add_nonneg (norm_nonneg M01) (norm_nonneg M10)) (mul_nonneg hℓ' hg0)
    have h2 : (‖M01‖ + ‖M10‖) * (ℓ' * g) ≤ Br := by
      have := mul_nonneg (norm_nonneg M11) (mul_nonneg hg0 hg0)
      have := mul_nonneg (norm_nonneg M4) (mul_nonneg (mul_nonneg hℓ' hℓ') (mul_nonneg hg0 hg0))
      linarith
    have hη0 : 0 ≤ η := (by positivity : (0 : ℝ) ≤ E * h⁻¹).trans hη
    calc (‖M01‖ + ‖M10‖) * ((ℓ' * g) * (E * h⁻¹)) =
          ((‖M01‖ + ‖M10‖) * (ℓ' * g)) * (E * h⁻¹) := by ring
      _ ≤ Br * η := mul_le_mul h2 hη (by positivity) hBr0
      _ = η * Br := by ring
  have n1 : ‖-M01‖ + ‖-M10‖ = ‖M01‖ + ‖M10‖ := by rw [norm_neg, norm_neg]
  have n2 : ‖M11 - M10 - M01‖ ≤ ‖M11‖ + (‖M01‖ + ‖M10‖) := by
    have := norm_sub_le (M11 - M10) M01
    have := norm_sub_le M11 M10
    linarith
  rw [n1]
  have f2 := mul_le_mul_of_nonneg_right n2 (mul_nonneg hg0 hg0)
  calc _ ≤ (‖M01‖ + ‖M10‖) * (ℓ' * g) + (‖M11‖ + (‖M01‖ + ‖M10‖)) * (g * g) +
        ‖M4‖ * (ℓ' * ℓ' * (g * g)) := by linarith
    _ = Br + (‖M01‖ + ‖M10‖) * (g * g) := by ring
    _ ≤ Br + η * Br := add_le_add le_rfl hx
    _ = (1 + η) * Br := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB' (by linarith [(by positivity : (0 : ℝ) ≤ E * h⁻¹)])

/-- `gSzE` only sees the four gradient coefficients. -/
theorem gSzE_congr {E h ℓ : ℝ} {a b : Lam d L N} {F G : Alg d L N}
    (h1 : cfAB2 a b F = cfAB2 a b G) (h2 : cfAB2 b a F = cfAB2 b a G)
    (h3 : cfAB2 b b F = cfAB2 b b G) (h4 : cfAB4 a b F = cfAB4 a b G) :
    gSzE E a b h ℓ F = gSzE E a b h ℓ G := by
  unfold gSzE; rw [h1, h2, h3, h4]

/-- The one-point part based at `a` has no gradient part seen from `a`. -/
theorem gSzE_loc_a {E h ℓ : ℝ} {a b : Lam d L N} (hab : a ≠ b) (α β : ℂ) :
    gSzE E a b h ℓ (α • (1 : Alg d L N) + β • pbp a) = 0 := by
  have e : (pbp a : Alg d L N) = m2 a a := rfl
  unfold gSzE
  rw [e]
  simp only [cfAB2_add, cfAB2_smul, cfAB2_one, cfAB2_m2, cfAB4_add, cfAB4_smul, cfAB4_one,
    cfAB4_m2, hab, Ne.symm hab, and_self, and_true, and_false, if_false]
  simp

/-- The one-point part based at `b`, seen from `a`: `‖β‖(2ℓg + g²)`. -/
theorem gSzE_loc_b {E h ℓ : ℝ} {a b : Lam d L N} (hab : a ≠ b) (α β : ℂ) :
    gSzE E a b h ℓ (α • (1 : Alg d L N) + β • pbp b) =
      ‖β‖ * (2 * (ℓ * (E * ℓ * h⁻¹)) + (E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) := by
  have e : (pbp b : Alg d L N) = m2 b b := rfl
  unfold gSzE
  rw [e]
  simp only [cfAB2_add, cfAB2_smul, cfAB2_one, cfAB2_m2, cfAB4_add, cfAB4_smul, cfAB4_one,
    cfAB4_m2, hab, Ne.symm hab, and_self, and_true, and_false, if_false, if_true]
  simp only [mul_zero, mul_one, zero_add, add_zero, norm_zero, zero_mul]
  ring

/-- **The gradient part of `loc^{ab}_X` (either base point), coefficient form**:
`gSzE(loc^{ab}_XF) ≤ ((1+η)K_G L^j/h + ℓ^{-2}(2ℓ'g + g²))‖F‖_{T_j(ℓ)}`, `g = Eℓ'/h`. -/
theorem gSzE_locABtX_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a b : Lam d L N} (hp : a ∈ X ∨ b ∈ X) (hab : a ≠ b)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ ℓ' h E κ η : ℝ} (hℓ : 0 < ℓ)
    (hℓ' : 0 ≤ ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h) (hsh : (L : ℝ) ^ j ≤ h) (hE : 0 ≤ E)
    (hκ : 0 ≤ κ) (hEκ : E * eN1 X a b ≤ κ * eN2 X a b) (hη : E * h⁻¹ ≤ η) :
    gSzE E a b h ℓ' (locABtX X a b F) ≤
      ((1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) +
        ℓ⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹))) *
        (Tj d (L : ℝ) j ℓ F).toReal := by
  set T := (Tj d (L : ℝ) j ℓ F).toReal with hT
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  set g := E * ℓ' * h⁻¹ with hg
  have hg0 : 0 ≤ g := by positivity
  have hP0 : 0 ≤ 2 * (ℓ' * g) + g * g := by
    have := mul_nonneg hℓ' hg0; have := mul_nonneg hg0 hg0; linarith
  have hM0 : 0 ≤ ℓ⁻¹ ^ 2 * (2 * (ℓ' * g) + g * g) * T :=
    mul_nonneg (mul_nonneg (by positivity) hP0) hT0
  have hη0 : 0 ≤ η := (by positivity : (0 : ℝ) ≤ E * h⁻¹).trans hη
  have hK0 : 0 ≤ KG d Cc κ * ((L : ℝ) ^ j * h⁻¹) * T :=
    mul_nonneg (mul_nonneg (KG_nonneg d hκ) (by positivity)) hT0
  have hhi : 0 ≤ h := hh.le
  unfold locABtX
  split_ifs with ha
  · rw [locABt, locEven_single_eq' ha subset_rfl]
    refine (gSzE_add_le hE hhi hℓ' a b _ _).trans ?_
    rw [gSzE_loc_a hab, zero_add]
    refine (gSzE_Dt_le hCc0 hCc hL hj hX (subset_nbhd hX.1 ha) hab hF hℓ hℓ' hℓℓ hh hsh hE hκ
      hEκ).trans ?_
    have : KG d Cc κ * ((L : ℝ) ^ j * h⁻¹) * T ≤ (1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) * T := by
      have := mul_nonneg hη0 hK0; nlinarith
    nlinarith
  · have hb : b ∈ X := hp.resolve_left ha
    rw [locABt, locEven_single_eq' hb subset_rfl]
    refine (gSzE_add_le hE hhi hℓ' a b _ _).trans ?_
    rw [gSzE_loc_b hab]
    have h1 := gSzE_Dt_swap_le hCc0 hCc hL hj hX (subset_nbhd hX.1 hb) hab hF hℓ hℓ' hℓℓ hh hsh
      hE hκ hEκ hη
    have hm := norm_mass2_le hℓ j F
    rw [← hT] at hm
    have h2 : ‖mass2 F‖ * (2 * (ℓ' * g) + g * g) ≤ ℓ⁻¹ ^ 2 * (2 * (ℓ' * g) + g * g) * T := by
      calc ‖mass2 F‖ * (2 * (ℓ' * g) + g * g) ≤ T * ℓ⁻¹ ^ 2 * (2 * (ℓ' * g) + g * g) :=
            mul_le_mul_of_nonneg_right hm hP0
        _ = _ := by ring
    have e : ((1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) + ℓ⁻¹ ^ 2 * (2 * (ℓ' * g) + g * g)) * T =
        ℓ⁻¹ ^ 2 * (2 * (ℓ' * g) + g * g) * T +
          (1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹) * T) := by ring
    rw [e]
    exact add_le_add h2 h1

/-- **The gradient part of `loc^{ab}_{X,Y}`** (`Y ⊆ X`), coefficient form: the same bound. -/
theorem gSzE_locABtXY_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) (P : ObsPts d L N) (hab : P.a ≠ P.b)
    {X Y : Finset (Lam d L N)} (hX : IsSmall j X) (hYX : Y ⊆ X)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ ℓ' h E κ η : ℝ} (hℓ : 0 < ℓ)
    (hℓ' : 0 ≤ ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h) (hsh : (L : ℝ) ^ j ≤ h) (hE : 0 ≤ E)
    (hκ : 0 ≤ κ) (hEκ : E * eN1 X P.a P.b ≤ κ * eN2 X P.a P.b) (hη : E * h⁻¹ ≤ η) :
    gSzE E P.a P.b h ℓ' (locABtXY P X Y F) ≤
      ((1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) +
        ℓ⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹))) *
        (Tj d (L : ℝ) j ℓ F).toReal := by
  have hη0 : 0 ≤ η := (by positivity : (0 : ℝ) ≤ E * h⁻¹).trans hη
  have hB0 : 0 ≤ ((1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) +
        ℓ⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹))) *
        (Tj d (L : ℝ) j ℓ F).toReal := by
    have hg0 : 0 ≤ E * ℓ' * h⁻¹ := by positivity
    have : 0 ≤ KG d Cc κ := KG_nonneg d hκ
    have h2 : 0 ≤ 2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹) := by
      have := mul_nonneg hℓ' hg0; have := mul_nonneg hg0 hg0; linarith
    have : 0 ≤ (Tj d (L : ℝ) j ℓ F).toReal := ENNReal.toReal_nonneg
    have : 0 ≤ (L : ℝ) ^ j * h⁻¹ := by positivity
    positivity
  rw [locABtXY, gSzE_smul hE hh.le hℓ']
  by_cases hXp : P.a ∈ X ∨ P.b ∈ X
  · calc _ ≤ 1 * (((1 + η) * (KG d Cc κ * ((L : ℝ) ^ j * h⁻¹)) +
          ℓ⁻¹ ^ 2 * (2 * (ℓ' * (E * ℓ' * h⁻¹)) + (E * ℓ' * h⁻¹) * (E * ℓ' * h⁻¹))) *
          (Tj d (L : ℝ) j ℓ F).toReal) :=
          mul_le_mul (norm_ratio_pts_le P hYX)
            (gSzE_locABtX_le hCc0 hCc hL hj hX hXp hab hF hℓ hℓ' hℓℓ hh hsh hE hκ hEκ hη)
            (gSzE_nonneg hE hh.le hℓ' _ _ _) zero_le_one
      _ = _ := one_mul _
  · have h0 : X ∩ P.pts = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_inter, ObsPts.pts, mem_insert, mem_singleton] at hz
      rcases hz with ⟨hzX, rfl | rfl⟩
      · exact hXp (Or.inl hzX)
      · exact hXp (Or.inr hzX)
    rw [h0, card_empty, Nat.cast_zero, div_zero, norm_zero, zero_mul]
    exact hB0

end

end Obs2
