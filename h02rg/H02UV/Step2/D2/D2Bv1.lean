import Step2.D2.D2Lval

/-!
# The `x`-derivative of the concrete `P_τ` (`prop:d2`, line 3)

With `u = 1 - cos 2πx`, `x ∈ [0, 1/2]`:

* `ψd = ψ'`, `hasDerivAt_ψ`, `ψd_decay`: the derivative of `ψ` and its decay;
* `hasDerivAt_qsum`: `d/dx ∑_k s ψ(s(x+k)) = ∑_k s² ψ'(s(x+k))` on `(-1/4, 3/4)`;
* `Qderiv_eq`: `Q_s'(u) · 2π sin 2πx = ∑_k s² ψ'(s(x+k))`;
* `Dp τ x = P_τ'(1 - cos 2πx) · 2π sin 2πx` (`Pc`), `abs_Dp_le`:
  `|Dp τ x| ≤ C_D τ (1 + τx)^{-6}`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-! ### `ψ'` -/

/-- `ψ' = Re Ψ'`. -/
def ψd (r : ℝ) : ℝ := (deriv (ΨS : ℝ → ℂ) r).re

theorem hasDerivAt_ψ (r : ℝ) : HasDerivAt ψ (ψd r) r := by
  have h := (Complex.reCLM.hasFDerivAt (x := ΨS r)).comp_hasDerivAt r (ΨS.hasDerivAt r)
  show HasDerivAt (fun r => (ΨS r).re) _ r
  exact h

theorem abs_ψd_le (r : ℝ) : |ψd r| ≤ M2 * |r| :=
  (Complex.abs_re_le_norm _).trans (norm_deriv_ΨS_le r)

theorem ψd_decay (M : ℕ) : ∃ C, 0 ≤ C ∧ ∀ r, |ψd r| ≤ C / (1 + |r|) ^ M := by
  set F := SchwartzMap.derivCLM ℝ ℂ ΨS
  set C0 := 2 ^ M * (Finset.Iic (M, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨max C0 0, le_max_right _ _, fun r => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, 0)) (k := M) (n := 0)
    le_rfl le_rfl F r
  rw [norm_iteratedFDeriv_zero, SchwartzMap.derivCLM_apply, Real.norm_eq_abs] at this
  rw [le_div_iff₀ (by positivity), mul_comm]
  calc (1 + |r|) ^ M * |ψd r| ≤ (1 + |r|) ^ M * ‖deriv (ΨS : ℝ → ℂ) r‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ C0 := this
    _ ≤ max C0 0 := le_max_left _ _

/-- A decay constant for `ψ'` with exponent `8`. -/
def Cd : ℝ := (ψd_decay 8).choose

theorem Cd_nonneg : 0 ≤ Cd := (ψd_decay 8).choose_spec.1

theorem ψd_le (r : ℝ) : |ψd r| ≤ Cd / (1 + |r|) ^ 8 := (ψd_decay 8).choose_spec.2 r

/-! ### The `k`-sums -/

theorem summable_b4 : Summable fun k : ℤ => ((1 + |(k : ℝ)| / 4) ^ 2)⁻¹ := by
  refine (FRD.PtF.summable_b.mul_left 4).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  have h : (1 + |(k : ℝ)| / 2) ^ 2 ≤ 4 * (1 + |(k : ℝ)| / 4) ^ 2 := by
    have := abs_nonneg (k : ℝ); nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

theorem abs_add_int_ge_quarter {y : ℝ} (hy : y ∈ Ioo (-1 / 4 : ℝ) (3 / 4)) (k : ℤ) :
    |(k : ℝ)| / 4 ≤ |y + k| := by
  simp only [mem_Ioo] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  · simp
  · have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith

/-- **The derivative of the Poisson sum.** For `s ≥ 1` and `y ∈ (-1/4, 3/4)`,
`d/dy ∑_k s ψ(s(y+k)) = ∑_k s² ψ'(s(y+k))`. -/
theorem hasDerivAt_qsum {s : ℝ} (hs : 1 ≤ s) {y : ℝ} (hy : y ∈ Ioo (-1 / 4 : ℝ) (3 / 4)) :
    HasDerivAt (fun z => ∑' k : ℤ, s * ψ (s * (z + k)))
      (∑' k : ℤ, s ^ 2 * ψd (s * (y + k))) y := by
  have hs0 : 0 < s := by linarith
  set ub : ℤ → ℝ := fun k => s ^ 2 * Cd * ((1 + |(k : ℝ)| / 4) ^ 2)⁻¹
  have hub : Summable ub := (summable_b4.mul_left (s ^ 2 * Cd))
  refine hasDerivAt_tsum_of_isPreconnected (t := Ioo (-1 / 4 : ℝ) (3 / 4)) (y₀ := 1 / 4)
    (g := fun (k : ℤ) (z : ℝ) => s * ψ (s * (z + k)))
    (g' := fun (k : ℤ) (z : ℝ) => s ^ 2 * ψd (s * (z + k))) hub
    isOpen_Ioo isPreconnected_Ioo (fun k z _ => ?_) (fun k z hz => ?_) ⟨by norm_num, by norm_num⟩
    ?_ hy
  · have := ((hasDerivAt_ψ (s * (z + k))).comp z (((hasDerivAt_id z).add_const (k : ℝ)).const_mul s))
    convert this.const_mul s using 1
    simp; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    have h1 := ψd_le (s * (z + k))
    have h2 := abs_add_int_ge_quarter hz k
    have h3 : 1 + |(k : ℝ)| / 4 ≤ 1 + |s * (z + k)| := by
      rw [abs_mul, abs_of_pos hs0]; nlinarith [abs_nonneg (z + k)]
    have h4 : ((1 + |s * (z + k)|) ^ 8)⁻¹ ≤ ((1 + |(k : ℝ)| / 4) ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      calc (1 + |(k : ℝ)| / 4) ^ 2 ≤ (1 + |s * (z + k)|) ^ 2 := by gcongr
        _ ≤ (1 + |s * (z + k)|) ^ 8 := pow_le_pow_right₀ (by linarith [abs_nonneg (s * (z + k))])
            (by norm_num)
    simp only [ub]
    rw [div_eq_mul_inv] at h1
    have := Cd_nonneg
    calc s ^ 2 * |ψd (s * (z + k))| ≤ s ^ 2 * (Cd * ((1 + |s * (z + k)|) ^ 8)⁻¹) := by gcongr
      _ ≤ s ^ 2 * (Cd * ((1 + |(k : ℝ)| / 4) ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  · obtain ⟨D, -, hD⟩ := FRD.PtF.sum_bound 0
    have := (hD s hs (1 / 4) ⟨by norm_num, by norm_num⟩).1
    exact this.mul_left s

/-- The Poisson sum `q_s(x) = Q_s(1 - cos 2πx)`. -/
theorem Q_cos_eq {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (Q s).eval (1 - Real.cos (2 * π * x)) = ∑' k : ℤ, s * ψ (s * (x + k)) := by
  rw [eval_Q_cos hs]

theorem hasDerivAt_one_sub_cos (x : ℝ) :
    HasDerivAt (fun y => 1 - Real.cos (2 * π * y)) (2 * π * Real.sin (2 * π * x)) x := by
  have := ((Real.hasDerivAt_cos (2 * π * x)).comp x ((hasDerivAt_id x).const_mul (2 * π))).const_sub 1
  convert this using 1; simp; ring

/-- **`Q_s'(u) · 2π sin 2πx = ∑_k s² ψ'(s(x+k))`.** -/
theorem Qderiv_eq {s : ℝ} (hs : 1 ≤ s) {x : ℝ} (hx : x ∈ Ioo (-1 / 4 : ℝ) (3 / 4)) :
    ((Q s).derivative).eval (1 - Real.cos (2 * π * x)) * (2 * π * Real.sin (2 * π * x)) =
      ∑' k : ℤ, s ^ 2 * ψd (s * (x + k)) := by
  have h1 := ((Q s).hasDerivAt (1 - Real.cos (2 * π * x))).comp x (hasDerivAt_one_sub_cos x)
  have h2 := hasDerivAt_qsum hs hx
  have e : (fun z => (Q s).eval (1 - Real.cos (2 * π * z))) =
      fun z => ∑' k : ℤ, s * ψ (s * (z + k)) := funext (Q_cos_eq (by linarith))
  rw [Function.comp_def, e] at h1
  exact h1.unique h2

/-- The bound `∑_k |ψ'(s(x+k))| ≤ D (1 + s x)^{-6}`. -/
theorem exists_sum_ψd_bound : ∃ D, 0 ≤ D ∧ ∀ s, 1 ≤ s → ∀ x ∈ Icc (0 : ℝ) (1 / 2),
    Summable (fun k : ℤ => |ψd (s * (x + k))|) ∧
      ∑' k : ℤ, |ψd (s * (x + k))| ≤ D / (1 + s * x) ^ 6 := by
  set B := ∑' k : ℤ, ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹
  have hB : 0 ≤ B := tsum_nonneg fun k => by positivity
  refine ⟨Cd * B, mul_nonneg Cd_nonneg hB, fun s hs x hx => ?_⟩
  have hx0 := hx.1
  have hterm : ∀ k : ℤ, |ψd (s * (x + k))| ≤
      Cd / (1 + s * x) ^ 6 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
    intro k
    refine (ψd_le _).trans ?_
    obtain ⟨h1, h2⟩ := FRD.PtF.abs_add_int_ge hx k
    have ha : |s * (x + k)| = s * |x + k| := by rw [abs_mul, abs_of_pos (by linarith)]
    have e1 : 1 + s * x ≤ 1 + |s * (x + k)| := by rw [ha]; gcongr
    have e2 : 1 + |(k : ℝ)| / 2 ≤ 1 + |s * (x + k)| := by
      rw [ha]; nlinarith [abs_nonneg (x + k)]
    have hp : 0 < 1 + s * x := by positivity
    have key : (1 + s * x) ^ 6 * (1 + |(k : ℝ)| / 2) ^ 2 ≤ (1 + |s * (x + k)|) ^ 8 := by
      calc (1 + s * x) ^ 6 * (1 + |(k : ℝ)| / 2) ^ 2
          ≤ (1 + |s * (x + k)|) ^ 6 * (1 + |s * (x + k)|) ^ 2 := by gcongr
        _ = (1 + |s * (x + k)|) ^ 8 := by rw [← pow_add]
    have := Cd_nonneg
    calc Cd / (1 + |s * (x + k)|) ^ 8
        ≤ Cd / ((1 + s * x) ^ 6 * (1 + |(k : ℝ)| / 2) ^ 2) :=
          div_le_div_of_nonneg_left this (by positivity) key
      _ = Cd / (1 + s * x) ^ 6 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv (Cd / _)]
  have hsb : Summable fun k : ℤ => Cd / (1 + s * x) ^ 6 * ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹ :=
    FRD.PtF.summable_b.mul_left _
  have hsum : Summable fun k : ℤ => |ψd (s * (x + k))| :=
    hsb.of_nonneg_of_le (fun k => abs_nonneg _) hterm
  refine ⟨hsum, (hsum.tsum_le_tsum hterm hsb).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left]; ring

/-- The constant of `exists_sum_ψd_bound`. -/
def Dψ : ℝ := exists_sum_ψd_bound.choose

theorem Dψ_nonneg : 0 ≤ Dψ := exists_sum_ψd_bound.choose_spec.1

theorem abs_Qderiv_le {s : ℝ} (hs : 1 ≤ s) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    |((Q s).derivative).eval (1 - Real.cos (2 * π * x)) * (2 * π * Real.sin (2 * π * x))| ≤
      s ^ 2 * Dψ / (1 + s * x) ^ 6 := by
  obtain ⟨hsum, hle⟩ := exists_sum_ψd_bound.choose_spec.2 s hs x hx
  rw [Qderiv_eq hs ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  have hs2 : Summable fun k : ℤ => s ^ 2 * ψd (s * (x + k)) :=
    (hsum.mul_left (s ^ 2)).of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)])
  calc |∑' k : ℤ, s ^ 2 * ψd (s * (x + k))| ≤ ∑' k : ℤ, |s ^ 2 * ψd (s * (x + k))| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun k : ℤ =>
          s ^ 2 * ψd (s * (x + k))) (by simpa only [Real.norm_eq_abs] using hs2.abs)
    _ = s ^ 2 * ∑' k : ℤ, |ψd (s * (x + k))| := by
        rw [← tsum_mul_left]; congr 1; funext k; rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ s ^ 2 * (Dψ / (1 + s * x) ^ 6) := by gcongr; exact hle
    _ = s ^ 2 * Dψ / (1 + s * x) ^ 6 := by ring

/-! ### The derivative of `P_τ` -/

open Polynomial in
theorem derivative_P0 (s : ℝ) :
    (P0 s).derivative = if s < 1 then 0 else C (1 / (cc * s)) * (Q s).derivative := by
  unfold P0
  split_ifs <;> simp [derivative_mul]

/-- `D_τ(x) = P_τ'(1 - cos 2πx) · 2π sin 2πx` for the concrete family. -/
def Dp (τ x : ℝ) : ℝ :=
  ((Pc.P τ).derivative).eval (1 - Real.cos (2 * π * x)) * (2 * π * Real.sin (2 * π * x))

open Polynomial in
theorem Dp_eq (τ x : ℝ) :
    Dp τ x = ∑ i ∈ Finset.range (⌊τ⌋₊ + 1), PrePtFamily.a i *
      (if τ / 2 ^ i < 1 then 0 else 1 / (cc * (τ / 2 ^ i)) *
        (((Q (τ / 2 ^ i)).derivative).eval (1 - Real.cos (2 * π * x)) *
          (2 * π * Real.sin (2 * π * x)))) := by
  simp only [Dp, Pc, PrePtFamily.toPtFamily, PrePtFamily.avgP, derivative_sum, derivative_mul,
    derivative_C, zero_mul, zero_add, eval_finsetSum, eval_mul, eval_C, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show PtF.prePt.P = P0 from rfl, derivative_P0]
  split_ifs <;> simp; ring

/-- The constant `C_D = D_ψ S_8 / c`. -/
def CD : ℝ := Dψ / cc * Som 8

theorem CD_nonneg : 0 ≤ CD := by
  have := Dψ_nonneg; have := cc_pos; have := Som_nonneg (r := 8) (by norm_num)
  unfold CD; positivity

/-- **`|D_τ(x)| ≤ C_D τ (1 + τx)^{-6}`** for `x ∈ [0, 1/2]`, `τ > 0`. -/
theorem abs_Dp_le {τ : ℝ} (hτ : 0 < τ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    |Dp τ x| ≤ CD * τ / (1 + τ * x) ^ 6 := by
  rw [Dp_eq]
  have hcc := cc_pos
  have hx0 := hx.1
  have hterm : ∀ i : ℕ, |PrePtFamily.a i * (if τ / 2 ^ i < 1 then 0 else 1 / (cc * (τ / 2 ^ i)) *
      (((Q (τ / 2 ^ i)).derivative).eval (1 - Real.cos (2 * π * x)) *
        (2 * π * Real.sin (2 * π * x))))| ≤
      om i * (Dψ / cc * τ / (1 + τ * x) ^ 6) * 8 ^ i := by
    intro i
    have ha := PrePtFamily.a_pos i
    have h4 : (0 : ℝ) < 4 ^ i := by positivity
    have h2 : (0 : ℝ) < 2 ^ i := by positivity
    split_ifs with h
    · simp; have := om_pos i; have := Dψ_nonneg; positivity
    · push_neg at h
      set σ := τ / 2 ^ i
      have hσ : 0 < σ := by positivity
      have hb := abs_Qderiv_le h hx
      have hinv := inv_one_add_div_pow_le (z := τ * x) (by positivity) i 6
      have e1 : (1 + σ * x) = 1 + τ * x / 2 ^ i := by simp only [σ]; ring
      rw [abs_mul, abs_of_pos ha, abs_mul, abs_of_pos (by positivity : 0 < 1 / (cc * σ))]
      have hD := Dψ_nonneg
      calc PrePtFamily.a i * (1 / (cc * σ) * |((Q σ).derivative).eval (1 - Real.cos (2 * π * x)) *
            (2 * π * Real.sin (2 * π * x))|)
          ≤ PrePtFamily.a i * (1 / (cc * σ) * (σ ^ 2 * Dψ / (1 + σ * x) ^ 6)) := by gcongr
        _ = PrePtFamily.a i * (σ * Dψ / cc) * ((1 + τ * x / 2 ^ i) ^ 6)⁻¹ := by
            rw [e1]; field_simp
        _ ≤ PrePtFamily.a i * (σ * Dψ / cc) * ((2 ^ 6) ^ i * ((1 + τ * x) ^ 6)⁻¹) := by
            gcongr
        _ = om i * (Dψ / cc * τ / (1 + τ * x) ^ 6) * 8 ^ i := by
            rw [← a_mul_four_pow]
            simp only [σ]
            have h8 : ((2 : ℝ) ^ 6) ^ i = 4 ^ i * 2 ^ i * 8 ^ i := by
              rw [← mul_pow, ← mul_pow]; norm_num
            rw [h8]
            field_simp
  have hpos : 0 ≤ Dψ / cc * τ / (1 + τ * x) ^ 6 := by
    have := Dψ_nonneg; positivity
  have hsum : Summable fun i : ℕ => om i * (Dψ / cc * τ / (1 + τ * x) ^ 6) * 8 ^ i := by
    have := (summable_om_pow 8).mul_left (Dψ / cc * τ / (1 + τ * x) ^ 6)
    convert this using 1; funext i; ring
  calc _ ≤ ∑ i ∈ Finset.range (⌊τ⌋₊ + 1), |PrePtFamily.a i * _| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (⌊τ⌋₊ + 1), om i * (Dψ / cc * τ / (1 + τ * x) ^ 6) * 8 ^ i :=
        Finset.sum_le_sum fun i _ => hterm i
    _ ≤ ∑' i, om i * (Dψ / cc * τ / (1 + τ * x) ^ 6) * 8 ^ i :=
        hsum.sum_le_tsum _ (fun i _ => by have := om_pos i; positivity)
    _ = CD * τ / (1 + τ * x) ^ 6 := by
        rw [show (fun i : ℕ => om i * (Dψ / cc * τ / (1 + τ * x) ^ 6) * 8 ^ i) =
          fun i => (Dψ / cc * τ / (1 + τ * x) ^ 6) * (om i * 8 ^ i) by funext i; ring,
          tsum_mul_left]
        simp only [CD, Som]; ring

end

end Step2.D2
