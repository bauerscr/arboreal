import Obs2.Flow.GradAB3
import Flow.Embed

/-!
# The gradient coefficients of `V'_{ab}`: scale-free inputs

Three small inputs of the gradient flow (`PtCorr2.gSzE_gX_flow_le`) that do not depend on the
history:

* **`eN1_single_le`**: `|e_{\{a\}}|₁ ≤ d|a − b|_∞` (base point `a`; the separation input of
  `tNorm_le_gSzE` / `gradM4Sz_le_gSzE` with `X = {a}`);
* **`gSzE_LopM4_le`**: `gSzE(ℒ_C(ψ̄_aψ_aψ̄_bψ_b)) ≤ c(4ℓg + g²)`, `g = Eℓ/h`, from `|C(x,y)| ≤ c`
  (no first-order covariance differences are needed: above coalescence `g ≲ |a−b|/L^{i+1}` is small);
* **`gSzE_scale_le_q`**: the scale change with a non-monotone field scale, `ℓ' ≤ qℓ`, `q ≥ 1`:
  `gSzE_{h',ℓ'} ≤ q⁴(h/h')gSzE_{h,ℓ}` (the field scale `s_j` of the history is not monotone, but
  `s_{j+1} ≤ (1 + |ζ_j|)s_j`, `PtCorr2.histS_ratio_le`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

/-- **`|e_{\{a\}}|₁ ≤ d|a − b|_∞`.** -/
theorem eN1_single_le (a b : Lam d L N) :
    eN1 ({a} : Finset (Lam d L N)) a b ≤ d * ((supNorm (a - b) : ℕ) : ℝ) := by
  have hb : base ({a} : Finset (Lam d L N)) = a := by
    unfold base
    rw [dif_pos (singleton_nonempty a)]
    exact Finset.mem_singleton.1 (singleton_nonempty a).choose_spec
  have h0 : ∀ i, (rep (a - a) i : ℤ) = 0 := fun i => by
    have hp := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) N
    have hz : supNormZ (0 : Zd d) = 0 := by simp [supNormZ]
    rw [sub_self, ← eq_rep prj_zero (by rw [hz]; omega)]
    rfl
  unfold eN1
  have hi : ∀ i, |eV ({a} : Finset (Lam d L N)) a b i| ≤ ((supNorm (a - b) : ℕ) : ℝ) := by
    intro i
    unfold eV lift
    rw [hb, h0 i, Int.cast_zero, sub_zero]
    have := Flow.natAbs_rep_le (b - a) i
    rw [← supNorm_neg, neg_sub] at this
    have h2 : (((rep (b - a) i).natAbs : ℕ) : ℝ) ≤ ((supNorm (a - b) : ℕ) : ℝ) := by
      exact_mod_cast this
    rwa [Nat.cast_natAbs, Int.cast_abs] at h2
  calc ∑ i, |eV ({a} : Finset (Lam d L N)) a b i| ≤ ∑ _i : Fin d, ((supNorm (a - b) : ℕ) : ℝ) :=
        sum_le_sum fun i _ => hi i
    _ = d * ((supNorm (a - b) : ℕ) : ℝ) := by simp

/-- **The gradient size of `ℒ_C m₄` from a uniform bound on `C`.** -/
theorem gSzE_LopM4_le {E h ℓ c : ℝ} (hE : 0 ≤ E) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N} (hab : a ≠ b)
    (hC : ∀ x y, ‖C x y‖ ≤ c) :
    gSzE E a b h ℓ (LopM4 C a b) ≤
      c * (4 * (ℓ * (E * ℓ * h⁻¹)) + (E * ℓ * h⁻¹) * (E * ℓ * h⁻¹)) := by
  rw [gSzE_LopM4_eq C hab]
  have hg : 0 ≤ E * ℓ * h⁻¹ := by positivity
  have h1 : ‖C a a - C b a‖ ≤ 2 * c :=
    (norm_sub_le _ _).trans (by linarith [hC a a, hC b a])
  have h2 : ‖C a a - C a b‖ ≤ 2 * c :=
    (norm_sub_le _ _).trans (by linarith [hC a a, hC a b])
  have hu : 0 ≤ ℓ * (E * ℓ * h⁻¹) := mul_nonneg hℓ hg
  have hv : 0 ≤ (E * ℓ * h⁻¹) * (E * ℓ * h⁻¹) := mul_nonneg hg hg
  have := mul_le_mul_of_nonneg_right (add_le_add h1 h2) hu
  have := mul_le_mul_of_nonneg_right (hC a a) hv
  nlinarith

/-- **Scale change with a field-scale ratio `q ≥ 1`**: `ℓ' ≤ qℓ`, `h ≤ h'` give
`gSzE_{h',ℓ'}(F) ≤ q⁴(h/h')gSzE_{h,ℓ}(F)`. -/
theorem gSzE_scale_le_q {E h h' ℓ ℓ' q : ℝ} (hE : 0 ≤ E) (hh : 0 < h) (hhh : h ≤ h')
    (hℓ' : 0 ≤ ℓ') (hq : 1 ≤ q) (hℓℓ : ℓ' ≤ q * ℓ) (a b : Lam d L N) (F : Alg d L N) :
    gSzE E a b h' ℓ' F ≤ q ^ 4 * (h * h'⁻¹) * gSzE E a b h ℓ F := by
  have hh' : 0 < h' := hh.trans_le hhh
  have hq0 : 0 ≤ q := by linarith
  have hℓ : 0 ≤ ℓ := by
    by_contra hneg
    push Not at hneg
    have : q * ℓ < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  set r := h * h'⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, ← div_eq_mul_inv, div_le_one hh']; exact hhh
  have hinv : h'⁻¹ = r * h⁻¹ := by rw [hr]; field_simp
  set g := E * ℓ * h⁻¹ with hg
  have hg0 : 0 ≤ g := by positivity
  have hg' : E * ℓ' * h'⁻¹ ≤ q * r * g := by
    rw [hinv, hg]
    have : E * ℓ' ≤ E * (q * ℓ) := mul_le_mul_of_nonneg_left hℓℓ hE
    calc E * ℓ' * (r * h⁻¹) ≤ E * (q * ℓ) * (r * h⁻¹) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = q * r * (E * ℓ * h⁻¹) := by ring
  have hg'0 : 0 ≤ E * ℓ' * h'⁻¹ := by positivity
  have hq1 : q ≤ q ^ 2 := by nlinarith
  have hq2 : q ^ 2 ≤ q ^ 4 := by nlinarith
  have hq3 : q ^ 3 ≤ q ^ 4 := by nlinarith
  -- the three weights
  have w1 : ℓ' * (E * ℓ' * h'⁻¹) ≤ q ^ 4 * r * (ℓ * g) := by
    calc ℓ' * (E * ℓ' * h'⁻¹) ≤ (q * ℓ) * (q * r * g) := mul_le_mul hℓℓ hg' hg'0 (by positivity)
      _ = q ^ 2 * r * (ℓ * g) := by ring
      _ ≤ q ^ 4 * r * (ℓ * g) := by gcongr
  have w2 : (E * ℓ' * h'⁻¹) * (E * ℓ' * h'⁻¹) ≤ q ^ 4 * r * (g * g) := by
    calc (E * ℓ' * h'⁻¹) * (E * ℓ' * h'⁻¹) ≤ (q * r * g) * (q * r * g) :=
          mul_le_mul hg' hg' hg'0 (by positivity)
      _ = q ^ 2 * r * (r * (g * g)) := by ring
      _ ≤ q ^ 2 * r * (1 * (g * g)) := by gcongr
      _ ≤ q ^ 4 * r * (g * g) := by rw [one_mul]; gcongr
  have w3 : ℓ' * ℓ' * ((E * ℓ' * h'⁻¹) * (E * ℓ' * h'⁻¹)) ≤ q ^ 4 * r * (ℓ * ℓ * (g * g)) := by
    calc ℓ' * ℓ' * ((E * ℓ' * h'⁻¹) * (E * ℓ' * h'⁻¹)) ≤
          (q * ℓ) * (q * ℓ) * ((q * r * g) * (q * r * g)) :=
          mul_le_mul (mul_le_mul hℓℓ hℓℓ hℓ' (by positivity)) (mul_le_mul hg' hg' hg'0
            (by positivity)) (by positivity) (by positivity)
      _ = q ^ 4 * r * (r * (ℓ * ℓ * (g * g))) := by ring
      _ ≤ q ^ 4 * r * (1 * (ℓ * ℓ * (g * g))) := by gcongr
      _ = q ^ 4 * r * (ℓ * ℓ * (g * g)) := by rw [one_mul]
  rw [gSzE_mul_eq, gSzE_mul_eq]
  set A1 := ‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 b a F + cfAB2 b b F‖
  set A2 := ‖cfAB2 b b F‖
  set A3 := ‖cfAB4 a b F‖
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := norm_nonneg _
  have hA3 : 0 ≤ A3 := norm_nonneg _
  have := mul_le_mul_of_nonneg_left w1 hA1
  have := mul_le_mul_of_nonneg_left w2 hA2
  have := mul_le_mul_of_nonneg_left w3 hA3
  calc _ ≤ A1 * (q ^ 4 * r * (ℓ * g)) + A2 * (q ^ 4 * r * (g * g)) +
        A3 * (q ^ 4 * r * (ℓ * ℓ * (g * g))) := by linarith
    _ = _ := by ring

end

end Obs2
