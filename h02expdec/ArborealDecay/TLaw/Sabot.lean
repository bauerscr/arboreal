module

public import ArborealDecay.TLaw.Steps

/-!
# BCHS Lemma 4.1 (supplement `thm:sabot`, `cor:sabot`)

* `sabot`: for a connected weighted graph, root `ρ`, `j ≠ ρ`, `a ≥ 0`, `s ∈ (0,1)`,
  `q = (1-s)⁻¹`, `γ > 0`, `v` with `v ρ = 0`, `v j = 1`, `γ |v_i - v_k| ≤ ½(1-s)²` on support
  edges, and the hypotheses (4.4) of BCHS — (H1) monotonicity/finiteness of `Z_{·,a}` over
  weights with the same support, (H2) `E e^{2a t_j} = 1` — one has
  `E e^{2as t_j} ≤ exp(-2asγ + q(q-1)γ² ∑_{e ∈ E(w)} (w_e + 2a)(∇_e v)²)`.
* `sabot_bchs`: the weaker BCHS (4.6) form with `½ γ² q² ∑_{i,k}` over all ordered pairs.
* `sabot_two_thirds`, `sabot_one_third`: `cor:sabot` (`a = 3/2`, `s = 2/3`, `s = 1/3`).
-/

open Finset Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The combined pointwise bound (Steps `cosh`, `determinant convexity`, `determinant
comparison`) on the log-density: with `F = logDensity`, `c* = -(q-1)γ`,
`q F(τ) + (1-q) F(τ + γ v̄) ≤ ∑_e (w_e + 2a) κ_e + F_{w̃}(τ + c* v̄)`. -/
theorem logDensity_combo_le {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected) (ρ : V) {a q γ : ℝ} (ha : 0 ≤ a) (hq : 1 < q)
    (v : V → ℝ) (hvρ : v ρ = 0)
    (hgq : ∀ i k, 0 < w i k → |q * γ * (v i - v k)| ≤ 1)
    (hκ : ∀ i k, 0 < w i k → kappa q γ v i k ≤ 1 / 2) (τ : {i // i ≠ ρ} → ℝ) :
    q * logDensity w ρ a τ + (1 - q) * logDensity w ρ a (τ + γ • fun i : {i // i ≠ ρ} => v i) ≤
      edgeSum w (fun i k => (w i k + 2 * a) * kappa q γ v i k) +
        logDensity (wScale w (kappa q γ v)) ρ a
          (τ + (-(q - 1) * γ) • fun i : {i // i ≠ ρ} => v i) := by
  set κ := kappa q γ v
  have hκ0 : ∀ i k, 0 < w i k → 0 ≤ κ i k := fun i k _ => by
    simp only [κ, kappa]
    have : 0 ≤ q - 1 := by linarith
    positivity
  have hκ1 : ∀ i k, 0 < w i k → κ i k < 1 := fun i k h => by linarith [hκ i k h]
  have hW' := isWGraph_wScale hW (kappa_symm q γ v) hκ1
  have hconn' : (supportGraph (wScale w κ)).Connected := by
    rwa [supportGraph_wScale hW hκ1]
  unfold logDensity
  rw [ext_add_smul ρ τ v hvρ, ext_add_smul ρ τ v hvρ]
  set x := ext ρ τ
  have hE := energy_le hW hq.le v hgq x
  have hL := logD_le hW hconn ρ hq x v (γ := γ)
  have hC := D_le_exp_mul hW (kappa_symm q γ v) hκ0 hκ ρ (x + (-(q - 1) * γ) • v)
  have hC' : log (D w ρ (x + (-(q - 1) * γ) • v)) ≤
      2 * edgeSum w κ + log (D (wScale w κ) ρ (x + (-(q - 1) * γ) • v)) := by
    have := log_le_log (D_pos hW hconn ρ _) hC
    rwa [log_mul (exp_pos _).ne' (D_pos hW' hconn' ρ _).ne', log_exp] at this
  have hsum : edgeSum w (fun i k => (w i k + 2 * a) * κ i k) =
      edgeSum w (fun i k => w i k * κ i k) + 2 * a * edgeSum w κ := by
    rw [show (fun i k => (w i k + 2 * a) * κ i k) = fun i k => w i k * κ i k + 2 * a * κ i k by
      funext i k; ring, edgeSum_add, edgeSum_const_mul]
  have hA := mul_le_mul_of_nonneg_left (hL.trans hC') ha
  rw [hsum]
  nlinarith

/-- **BCHS Lemma 4.1** (supplement `thm:sabot`). Hypotheses: a connected weighted graph `w`,
root `ρ`, `j ≠ ρ`, `a ≥ 0`, `s ∈ (0,1)`, `γ > 0`, `v` with `v ρ = 0`, `v j = 1` and
`γ |v_i - v_k| ≤ ½ (1-s)²` on support edges, and BCHS (4.4):
(H1) for every weighted graph `w'` with the same support and `w' ≤ w`, `Z_{w',a} < ∞` and
`Z_{w',a} ≤ Z_{w,a}`; (H2) `E_{w,a} e^{2a t_j} = 1`. Conclusion (with `q = (1-s)⁻¹`, and
`edgeSum w g = ∑_{e ∈ E(w)} g_e` over unordered support edges):
`E_{w,a} e^{2as t_j} ≤ exp(-2asγ + q(q-1)γ² ∑_{e ∈ E(w)} (w_e + 2a)(∇_e v)²)`,
the left side being an honest (integrable) expectation. -/
theorem sabot {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    {ρ j : V} (hj : j ≠ ρ) {a s γ : ℝ} (ha : 0 ≤ a) (hs0 : 0 < s) (hs1 : s < 1) (hγ : 0 < γ)
    (v : V → ℝ) (hvρ : v ρ = 0) (hvj : v j = 1)
    (hgrad : ∀ i k, 0 < w i k → γ * |v i - v k| ≤ (1 - s) ^ 2 / 2)
    (H1 : ∀ w' : V → V → ℝ, IsWGraph w' → (∀ i k, 0 < w' i k ↔ 0 < w i k) →
      (∀ i k, w' i k ≤ w i k) → Z w' ρ a < ⊤ ∧ Z w' ρ a ≤ Z w ρ a)
    (H2 : expect w ρ a (fun τ => exp (2 * a * ext ρ τ j)) = 1) :
    Integrable (fun τ => exp (2 * a * s * ext ρ τ j) * density w ρ a τ) ∧
      expect w ρ a (fun τ => exp (2 * a * s * ext ρ τ j)) ≤
        exp (-2 * a * s * γ + (1 - s)⁻¹ * ((1 - s)⁻¹ - 1) * γ ^ 2 *
          edgeSum w (fun i k => (w i k + 2 * a) * (v i - v k) ^ 2)) := by
  -- constants
  set q := (1 - s)⁻¹ with hqdef
  have h1s : 0 < 1 - s := by linarith
  have hq1 : 1 < q := by rw [hqdef]; exact one_lt_inv₀ h1s |>.2 (by linarith)
  have hq0 : 0 < q := by linarith
  have hqinv : q⁻¹ = 1 - s := by rw [hqdef, inv_inv]
  have hsq : s * q = q - 1 := by rw [hqdef]; field_simp; ring
  set κ := kappa q γ v
  set c := -(q - 1) * γ
  set vb : {i // i ≠ ρ} → ℝ := fun i => v i
  set j' : {i // i ≠ ρ} := ⟨j, hj⟩
  -- gradient consequences
  have hgq : ∀ i k, 0 < w i k → |q * γ * (v i - v k)| ≤ 1 := fun i k h => by
    have hg := hgrad i k h
    rw [abs_mul, abs_mul, abs_of_pos hq0, abs_of_pos hγ]
    have : γ * |v i - v k| ≤ 1 / (2 * q ^ 2) := by
      rw [show (1 - s) = q⁻¹ from hqinv.symm] at hg
      calc γ * |v i - v k| ≤ q⁻¹ ^ 2 / 2 := hg
        _ = 1 / (2 * q ^ 2) := by field_simp
    have h2 : q * (1 / (2 * q ^ 2)) ≤ 1 := by
      rw [show q * (1 / (2 * q ^ 2)) = 1 / (2 * q) by field_simp]
      rw [div_le_one (by positivity)]; linarith
    calc q * γ * |v i - v k| = q * (γ * |v i - v k|) := by ring
      _ ≤ q * (1 / (2 * q ^ 2)) := mul_le_mul_of_nonneg_left this hq0.le
      _ ≤ 1 := h2
  have hκ : ∀ i k, 0 < w i k → κ i k ≤ 1 / 2 := fun i k h => by
    have hg := hgrad i k h
    rw [show (1 - s) = q⁻¹ from hqinv.symm] at hg
    have hγd : γ * |v i - v k| ≤ 1 / (2 * q ^ 2) := by
      calc γ * |v i - v k| ≤ q⁻¹ ^ 2 / 2 := hg
        _ = 1 / (2 * q ^ 2) := by field_simp
    have hsq' : γ ^ 2 * (v i - v k) ^ 2 ≤ (1 / (2 * q ^ 2)) ^ 2 := by
      rw [← sq_abs (v i - v k), ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hγd 2
    simp only [κ, kappa]
    calc (q - 1) * q ^ 2 * γ ^ 2 * (v i - v k) ^ 2
        = (q - 1) * q ^ 2 * (γ ^ 2 * (v i - v k) ^ 2) := by ring
      _ ≤ (q - 1) * q ^ 2 * (1 / (2 * q ^ 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq' (mul_nonneg (by linarith) (by positivity))
      _ = (q - 1) / (4 * q ^ 2) := by field_simp; ring
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
  have hκ1 : ∀ i k, 0 < w i k → κ i k < 1 := fun i k h => by linarith [hκ i k h]
  have hW' := isWGraph_wScale hW (kappa_symm q γ v) hκ1
  have hconn' : (supportGraph (wScale w κ)).Connected := by
    rwa [supportGraph_wScale hW hκ1]
  -- (H2) in `[0,∞]` form
  have hgc : Continuous fun τ : {i // i ≠ ρ} → ℝ => exp (2 * a * ext ρ τ j) :=
    continuous_exp.comp (continuous_const.mul ((continuous_apply j).comp (continuous_ext ρ)))
  obtain ⟨hL2, hZ0, hZt⟩ := lintegral_eq_Z_of_expect_eq_one hW hconn ρ a
    (fun τ => (exp_pos _).le) hgc H2
  -- notation
  set f := density w ρ a
  have hfpos : ∀ τ, 0 < f τ := density_pos hW hconn ρ a
  have hfc : Continuous f := continuous_density hW hconn ρ a
  have hfγc : Continuous fun τ => f (τ + γ • vb) := hfc.comp (continuous_id.add continuous_const)
  have hextj : ∀ τ : {i // i ≠ ρ} → ℝ, ext ρ τ j = τ j' := fun τ => by
    simp [j', ext, hj]
  -- the exponent
  set Es := edgeSum w (fun i k => (w i k + 2 * a) * κ i k)
  have hEs : Es / q = q * (q - 1) * γ ^ 2 *
      edgeSum w (fun i k => (w i k + 2 * a) * (v i - v k) ^ 2) := by
    simp only [Es, κ, kappa]
    rw [show (fun i k => (w i k + 2 * a) * ((q - 1) * q ^ 2 * γ ^ 2 * (v i - v k) ^ 2)) =
        fun i k => ((q - 1) * q ^ 2 * γ ^ 2) * ((w i k + 2 * a) * (v i - v k) ^ 2) by
      funext i k; ring, edgeSum_const_mul]
    field_simp
  -- Hölder
  set X : ({i // i ≠ ρ} → ℝ) → ENNReal := fun τ => ENNReal.ofReal (f τ * f (τ + γ • vb) ^ (-s))
  set Y : ({i // i ≠ ρ} → ℝ) → ENNReal :=
    fun τ => ENNReal.ofReal ((exp (2 * a * ext ρ τ j) * f (τ + γ • vb)) ^ s)
  have hXY : ∀ τ, ENNReal.ofReal (exp (2 * a * s * ext ρ τ j) * f τ) = (X * Y) τ := fun τ => by
    simp only [X, Y, Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hfpos τ).le (rpow_nonneg (hfpos _).le _)),
      mul_rpow (exp_pos _).le (hfpos _).le, ← exp_mul]
    congr 1
    have h1 : f (τ + γ • vb) ^ (-s) * f (τ + γ • vb) ^ s = 1 := by
      rw [← rpow_add (hfpos _), neg_add_cancel, rpow_zero]
    calc exp (2 * a * s * ext ρ τ j) * f τ
        = f τ * (f (τ + γ • vb) ^ (-s) * f (τ + γ • vb) ^ s) *
            exp (2 * a * ext ρ τ j * s) := by rw [h1]; ring_nf
      _ = _ := by ring
  have hXm : AEMeasurable X := by
    refine (Continuous.measurable ?_).ennreal_ofReal.aemeasurable
    exact hfc.mul (hfγc.rpow_const fun τ => Or.inl (hfpos _).ne')
  have hYm : AEMeasurable Y := by
    refine (Continuous.measurable ?_).ennreal_ofReal.aemeasurable
    exact (hgc.mul hfγc).rpow_const fun τ => Or.inr hs0.le
  have hpq : q.HolderConjugate (1 / s) := by
    rw [Real.holderConjugate_iff]
    exact ⟨hq1, by rw [hqinv, one_div, inv_inv]; ring⟩
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hXm hYm
  simp_rw [← hXY] at hHolder
  -- the first factor
  have hX : ∀ τ, X τ ^ q ≤ ENNReal.ofReal (exp Es) *
      ENNReal.ofReal (density (wScale w κ) ρ a (τ + c • vb)) := fun τ => by
    simp only [X]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (hfpos τ).le (rpow_nonneg (hfpos _).le _))
      hq0.le, ← ENNReal.ofReal_mul (exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcombo := logDensity_combo_le hW hconn ρ ha hq1 v hvρ hgq hκ τ (γ := γ)
    simp only [f]
    rw [density_eq_exp hW hconn, density_eq_exp hW hconn, density_eq_exp hW' hconn', ← exp_add,
      ← exp_mul, ← exp_add, ← exp_mul]
    refine exp_le_exp.2 ?_
    have : (logDensity w ρ a τ + logDensity w ρ a (τ + γ • vb) * -s) * q =
        q * logDensity w ρ a τ + (1 - q) * logDensity w ρ a (τ + γ • vb) := by
      linear_combination (-logDensity w ρ a (τ + γ • vb)) * hsq
    rw [this]
    exact hcombo
  have hI1 : ∫⁻ τ, X τ ^ q ≤ ENNReal.ofReal (exp Es) * Z w ρ a := by
    calc ∫⁻ τ, X τ ^ q
        ≤ ∫⁻ τ, ENNReal.ofReal (exp Es) *
            ENNReal.ofReal (density (wScale w κ) ρ a (τ + c • vb)) := lintegral_mono hX
      _ = ENNReal.ofReal (exp Es) * Z (wScale w κ) ρ a := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Z,
            lintegral_add_right_eq_self (fun σ => ENNReal.ofReal (density (wScale w κ) ρ a σ))]
      _ ≤ ENNReal.ofReal (exp Es) * Z w ρ a := by
          refine mul_le_mul_right ?_ _
          exact (H1 _ hW' (wScale_pos_iff hW hκ1) (wScale_le hW
            (fun i k h => by simp only [kappa]; have : 0 ≤ q - 1 := by linarith
                             positivity))).2
  -- the second factor
  have hI2 : ∫⁻ τ, Y τ ^ (1 / s) = ENNReal.ofReal (exp (-(2 * a * γ))) * Z w ρ a := by
    have hY : ∀ τ, Y τ ^ (1 / s) =
        (fun σ => ENNReal.ofReal (exp (-(2 * a * γ)) * (exp (2 * a * ext ρ σ j) * f σ)))
          (τ + γ • vb) := fun τ => by
      simp only [Y]
      rw [ENNReal.ofReal_rpow_of_nonneg (rpow_nonneg (mul_nonneg (exp_pos _).le
        (hfpos _).le) _) (by positivity), ← rpow_mul (mul_nonneg (exp_pos _).le (hfpos _).le),
        mul_one_div_cancel hs0.ne', rpow_one, hextj, hextj]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vb, j', hvj]
      rw [← mul_assoc, ← exp_add]; ring_nf
    simp_rw [hY]
    rw [lintegral_add_right_eq_self (fun σ => ENNReal.ofReal (exp (-(2 * a * γ)) *
      (exp (2 * a * ext ρ σ j) * f σ)))]
    simp_rw [ENNReal.ofReal_mul (exp_pos _).le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    simp_rw [← ENNReal.ofReal_mul (exp_pos _).le]
    exact hL2
  rw [hI2] at hHolder
  -- combine
  have hfinal : ∫⁻ τ, ENNReal.ofReal (exp (2 * a * s * ext ρ τ j) * f τ) ≤
      ENNReal.ofReal (exp (-2 * a * s * γ + Es / q)) * Z w ρ a := by
    refine hHolder.trans ?_
    calc (∫⁻ τ, X τ ^ q) ^ (1 / q) * (ENNReal.ofReal (exp (-(2 * a * γ))) * Z w ρ a) ^ (1 / (1 / s))
        ≤ (ENNReal.ofReal (exp Es) * Z w ρ a) ^ (1 / q) *
            (ENNReal.ofReal (exp (-(2 * a * γ))) * Z w ρ a) ^ (1 / (1 / s)) := by
          gcongr
      _ = ENNReal.ofReal (exp Es) ^ (1 / q) * ENNReal.ofReal (exp (-(2 * a * γ))) ^ s *
            (Z w ρ a ^ (1 / q) * Z w ρ a ^ s) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div_one_div]
          ring
      _ = ENNReal.ofReal (exp (-2 * a * s * γ + Es / q)) * Z w ρ a := by
          rw [← ENNReal.rpow_add _ _ hZ0 hZt, one_div, hqinv, sub_add_cancel, ENNReal.rpow_one,
            ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hs0.le,
            ← ENNReal.ofReal_mul (rpow_nonneg (exp_pos _).le _), ← exp_mul, ← exp_mul,
            ← exp_add, ← hqinv]
          congr 3
          rw [div_eq_mul_inv]; ring
  have hcont2 : Continuous fun τ : {i // i ≠ ρ} → ℝ => exp (2 * a * s * ext ρ τ j) :=
    continuous_exp.comp (continuous_const.mul ((continuous_apply j).comp (continuous_ext ρ)))
  have := expect_le_of_lintegral_le hW hconn ρ a (fun τ => (exp_pos _).le) hcont2
    (exp_pos _).le hZ0 hZt hfinal
  rw [hEs] at this
  exact this

end ArborealDecay.TLaw
