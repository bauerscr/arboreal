module

public import ArborealDecay.TLaw.Integral

/-!
# Pointwise steps of the proof of `thm:sabot`

For `q ≥ 1`, `γ`, `v : V → ℝ` put `κ_{ik} = (q-1) q² γ² (v_i - v_k)²` (`kappa`) and
`w̃_{ik} = (1 - κ_{ik}) w_{ik}` (`wScale`). This file proves:

* `energy_le` (Step `cosh`): `-q Φ_w(x) + (q-1) Φ_w(x + γ v) ≤ -Φ_{w̃}(x + c* v) + ∑_e w_e κ_e`;
* `logD_le` (Step `determinant convexity`): `q log D(x) - (q-1) log D(x + γ v) ≤ log D(x + c* v)`;
* `D_le_exp_mul` (Step `determinant comparison`): `D_w ≤ e^{2 ∑_e κ_e} D_{w̃}`;
* `logDensity_combo_le`: the combined pointwise bound on `q F(τ) + (1-q) F(τ + γ v̄)`.

Here `c* = -(q-1) γ` and `∑_e` is `edgeSum w` (unordered support edges).
-/

open Finset Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `κ_{ik} = (q-1) q² γ² (v_i - v_k)²`. -/
noncomputable def kappa (q γ : ℝ) (v : V → ℝ) (i k : V) : ℝ :=
  (q - 1) * q ^ 2 * γ ^ 2 * (v i - v k) ^ 2

/-- The scaled weights `w̃_{ik} = (1 - κ_{ik}) w_{ik}`. -/
noncomputable def wScale (w κ : V → V → ℝ) : V → V → ℝ := fun i k => (1 - κ i k) * w i k

theorem kappa_symm (q γ : ℝ) (v : V → ℝ) (i k : V) : kappa q γ v i k = kappa q γ v k i := by
  unfold kappa; ring

theorem edgeSum_add (w g h : V → V → ℝ) :
    edgeSum w (fun i k => g i k + h i k) = edgeSum w g + edgeSum w h := by
  have : ∀ i k, (if 0 < w i k then g i k + h i k else 0) =
      (if 0 < w i k then g i k else 0) + (if 0 < w i k then h i k else 0) := fun i k => by
    split_ifs <;> ring
  simp only [edgeSum, this, Finset.sum_add_distrib]; ring

theorem edgeSum_const_mul (w g : V → V → ℝ) (c : ℝ) :
    edgeSum w (fun i k => c * g i k) = c * edgeSum w g := by
  have : ∀ i k, (if 0 < w i k then c * g i k else 0) = c * (if 0 < w i k then g i k else 0) :=
    fun i k => by split_ifs <;> ring
  simp only [edgeSum, this, ← Finset.mul_sum]; ring

theorem edgeSum_mono (w : V → V → ℝ) {g h : V → V → ℝ} (hgh : ∀ i k, 0 < w i k → g i k ≤ h i k) :
    edgeSum w g ≤ edgeSum w h := by
  unfold edgeSum
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_)
    (by norm_num)
  split_ifs with h0
  · exact hgh i k h0
  · rfl

/-- `wScale` preserves the weighted-graph axioms when `κ` is symmetric and `κ ≤ 1` on `E(w)`. -/
theorem isWGraph_wScale {w κ : V → V → ℝ} (hW : IsWGraph w) (hκs : ∀ i k, κ i k = κ k i)
    (hκ1 : ∀ i k, 0 < w i k → κ i k < 1) : IsWGraph (wScale w κ) where
  symm i k := by simp only [wScale, hκs i k, hW.symm i k]
  nonneg i k := by
    rcases (hW.nonneg i k).lt_or_eq with h | h
    · exact mul_nonneg (by linarith [hκ1 i k h]) h.le
    · simp [wScale, ← h]
  diag i := by simp [wScale, hW.diag]

theorem wScale_pos_iff {w κ : V → V → ℝ} (hW : IsWGraph w) (hκ1 : ∀ i k, 0 < w i k → κ i k < 1)
    (i k : V) : 0 < wScale w κ i k ↔ 0 < w i k := by
  constructor
  · intro h
    by_contra h'
    have : w i k = 0 := le_antisymm (not_lt.1 h') (hW.nonneg i k)
    simp [wScale, this] at h
  · intro h; exact mul_pos (by linarith [hκ1 i k h]) h

theorem wScale_le {w κ : V → V → ℝ} (hW : IsWGraph w) (hκ0 : ∀ i k, 0 < w i k → 0 ≤ κ i k)
    (i k : V) : wScale w κ i k ≤ w i k := by
  rcases (hW.nonneg i k).lt_or_eq with h | h
  · have := hκ0 i k h
    unfold wScale; nlinarith
  · simp [wScale, ← h]

theorem supportGraph_wScale {w κ : V → V → ℝ} (hW : IsWGraph w)
    (hκ1 : ∀ i k, 0 < w i k → κ i k < 1) : supportGraph (wScale w κ) = supportGraph w := by
  ext i k
  simp only [supportGraph, SimpleGraph.fromRel_adj, wScale_pos_iff hW hκ1]

/-- The per-pair inequality behind Step `cosh`. -/
theorem pair_ineq {q γ d X wik : ℝ} (hq : 1 ≤ q) (hw : 0 ≤ wik) (hd : 0 < wik → |q * γ * d| ≤ 1) :
    -(q * (wik * (cosh X - 1))) + (q - 1) * (wik * (cosh (X + γ * d) - 1)) ≤
      -((1 - (q - 1) * q ^ 2 * γ ^ 2 * d ^ 2) * wik * (cosh (X - (q - 1) * γ * d) - 1)) +
        (if 0 < wik then wik * ((q - 1) * q ^ 2 * γ ^ 2 * d ^ 2) else 0) := by
  rcases hw.lt_or_eq with h | h
  · simp only [h, ↓reduceIte]
    have := mul_le_mul_of_nonneg_left (cosh_combo_ge hq (hd h) X) hw
    nlinarith
  · subst h; simp

/-- Step `cosh` of `thm:sabot`. -/
theorem energy_le {w : V → V → ℝ} (hW : IsWGraph w) {q γ : ℝ} (hq : 1 ≤ q) (v : V → ℝ)
    (hgrad : ∀ i k, 0 < w i k → |q * γ * (v i - v k)| ≤ 1) (x : V → ℝ) :
    -(q * Phi w x) + (q - 1) * Phi w (x + γ • v) ≤
      -Phi (wScale w (kappa q γ v)) (x + (-(q - 1) * γ) • v) +
        edgeSum w (fun i k => w i k * kappa q γ v i k) := by
  have key : ∀ i k, -(q * (w i k * (cosh (x i - x k) - 1))) +
      (q - 1) * (w i k * (cosh ((x + γ • v) i - (x + γ • v) k) - 1)) ≤
      -(wScale w (kappa q γ v) i k *
          (cosh ((x + (-(q - 1) * γ) • v) i - (x + (-(q - 1) * γ) • v) k) - 1)) +
        (if 0 < w i k then w i k * kappa q γ v i k else 0) := fun i k => by
    have := pair_ineq (X := x i - x k) hq (hW.nonneg i k) (hgrad i k)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wScale, kappa]
    convert this using 4 <;> ring_nf
  have hs := Finset.sum_le_sum fun i (_ : i ∈ univ) =>
    Finset.sum_le_sum fun k (_ : k ∈ univ) => key i k
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hs
  unfold Phi edgeSum
  linarith

/-- Step `determinant convexity` of `thm:sabot`, in log form. -/
theorem logD_le {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected) (ρ : V)
    {q γ : ℝ} (hq : 1 < q) (x v : V → ℝ) :
    q * log (D w ρ x) - (q - 1) * log (D w ρ (x + γ • v)) ≤
      log (D w ρ (x + (-(q - 1) * γ) • v)) := by
  have hθ0 : 0 < q⁻¹ := inv_pos.2 (by linarith)
  have hθ1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have h := D_logconvex hW ρ x v hθ0 hθ1 (-(q - 1) * γ) γ
  have h0 : q⁻¹ * (-(q - 1) * γ) + (1 - q⁻¹) * γ = 0 := by field_simp; ring
  rw [h0, zero_smul, add_zero] at h
  have hp : ∀ y, 0 < D w ρ y := D_pos hW hconn ρ
  have hl := log_le_log (hp x) h
  rw [log_mul (rpow_pos_of_pos (hp _) _).ne' (rpow_pos_of_pos (hp _) _).ne', log_rpow (hp _),
    log_rpow (hp _)] at hl
  have hq0 : 0 < q := by linarith
  have := mul_le_mul_of_nonneg_left hl hq0.le
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hq0.ne', mul_sub, mul_inv_cancel₀ hq0.ne',
    mul_one, one_mul] at this
  linarith

/-- Step `determinant comparison` of `thm:sabot`: `D_w ≤ e^{2 ∑_e κ_e} D_{w̃}`. -/
theorem D_le_exp_mul {w κ : V → V → ℝ} (hW : IsWGraph w) (hκs : ∀ i k, κ i k = κ k i)
    (hκ0 : ∀ i k, 0 < w i k → 0 ≤ κ i k) (hκ1 : ∀ i k, 0 < w i k → κ i k ≤ 1 / 2)
    (ρ : V) (y : V → ℝ) :
    D w ρ y ≤ exp (2 * edgeSum w κ) * D (wScale w κ) ρ y := by
  classical
  have hκ1' : ∀ i k, 0 < w i k → κ i k < 1 := fun i k h => by linarith [hκ1 i k h]
  have hW' := isWGraph_wScale hW hκs hκ1'
  rw [D_eq_treeSum w hW.symm hW.diag, D_eq_treeSum _ hW'.symm hW'.diag, Finset.mul_sum]
  refine Finset.sum_le_sum fun T _ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
  have hlift : ∀ e : Sym2 V, Sym2.lift ⟨wScale w κ, hW'.symm⟩ e =
      (1 - Sym2.lift ⟨κ, hκs⟩ e) * Sym2.lift ⟨w, hW.symm⟩ e := fun e => by
    induction e using Sym2.ind with
    | h i k => simp [wScale]
  simp_rw [hlift]
  rw [Finset.prod_mul_distrib]
  have hwT : 0 ≤ ∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hW.symm⟩ e :=
    Finset.prod_nonneg fun e _ => by
      induction e using Sym2.ind with
      | h i k => exact hW.nonneg i k
  by_cases hall : ∀ e ∈ T.edgeFinset, 0 < Sym2.lift ⟨w, hW.symm⟩ e
  · have hsub : T.edgeFinset ⊆ (supportGraph w).edgeFinset := by
      intro e he
      have hpos := hall e he
      induction e using Sym2.ind with
      | h i k =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        rw [supportGraph_adj hW.symm]
        exact ⟨he.ne, by simpa using hpos⟩
    have hκE : ∀ e ∈ (supportGraph w).edgeFinset, 0 ≤ Sym2.lift ⟨κ, hκs⟩ e ∧
        Sym2.lift ⟨κ, hκs⟩ e ≤ 1 / 2 := by
      intro e he
      induction e using Sym2.ind with
      | h i k =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, supportGraph_adj hW.symm] at he
        simp only [Sym2.lift_mk]
        exact ⟨hκ0 i k he.2, hκ1 i k he.2⟩
    -- `∏_T (1 - κ_e) ≥ e^{-2 ∑_E κ}`
    have hprod : exp (-(2 * edgeSum w κ)) ≤ ∏ e ∈ T.edgeFinset, (1 - Sym2.lift ⟨κ, hκs⟩ e) := by
      rw [edgeSum_eq_sum_edgeFinset hW κ hκs]
      calc exp (-(2 * ∑ e ∈ (supportGraph w).edgeFinset, Sym2.lift ⟨κ, hκs⟩ e))
          ≤ exp (-(2 * ∑ e ∈ T.edgeFinset, Sym2.lift ⟨κ, hκs⟩ e)) := by
            refine exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun e he _ => (hκE e he).1
        _ = ∏ e ∈ T.edgeFinset, exp (-(2 * Sym2.lift ⟨κ, hκs⟩ e)) := by
            rw [← exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
        _ ≤ ∏ e ∈ T.edgeFinset, (1 - Sym2.lift ⟨κ, hκs⟩ e) := by
            refine Finset.prod_le_prod₀ (fun e _ => (exp_pos _).le) fun e he => ?_
            obtain ⟨h0, h1⟩ := hκE e (hsub he)
            have := inv_one_sub_le_exp h0 h1
            have hpos : 0 < 1 - Sym2.lift ⟨κ, hκs⟩ e := by linarith
            rw [exp_neg]
            calc (exp (2 * Sym2.lift ⟨κ, hκs⟩ e))⁻¹ ≤ ((1 - Sym2.lift ⟨κ, hκs⟩ e)⁻¹)⁻¹ :=
                  inv_anti₀ (inv_pos.2 hpos) this
              _ = 1 - Sym2.lift ⟨κ, hκs⟩ e := inv_inv _
    have h1 : 1 ≤ exp (2 * edgeSum w κ) * ∏ e ∈ T.edgeFinset, (1 - Sym2.lift ⟨κ, hκs⟩ e) := by
      calc (1 : ℝ) = exp (2 * edgeSum w κ) * exp (-(2 * edgeSum w κ)) := by
            rw [← exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    calc ∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hW.symm⟩ e
        = 1 * ∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hW.symm⟩ e := (one_mul _).symm
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hwT
  · push Not at hall
    obtain ⟨e, he, hle⟩ := hall
    have hz : ∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hW.symm⟩ e = 0 := by
      refine Finset.prod_eq_zero he (le_antisymm hle ?_)
      induction e using Sym2.ind with
      | h i k => exact hW.nonneg i k
    rw [hz, mul_zero, mul_zero]

end ArborealDecay.TLaw
