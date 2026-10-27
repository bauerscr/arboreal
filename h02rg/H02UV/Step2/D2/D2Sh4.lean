import Step2.D2.D2Sh3

/-!
# Sharp line 3, part 4: the corner `u ∈ [1, 2)` (`x ∈ [1/4, 1/2)`)

Near `x = 1/2` the factor `sin 2πx` of `D_τ` vanishes. Using `ψ''` and the symmetry
`∑_k ψ'(s(1/2 + k)) = 0`:

* `abs_Qd_corner`: `|Q_s'(u)| ≤ C s³ (1 + s/4)^{-6}` for `u ∈ [1, 2)`, `s ≥ 1`;
* `abs_tau_Pd_corner`: `|τ P_τ'(u)| ≤ K_c τ^{-3}`;
* `abs_tail_corner`: `|∫_T^∞ τ P_τ'(u) dτ| ≤ K_c/(2T²)`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- `ψ''`. -/
def ψdd (r : ℝ) : ℝ := (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ ΨS) r).re

theorem ψd_eq (r : ℝ) : ψd r = (SchwartzMap.derivCLM ℝ ℂ ΨS r).re := by
  unfold ψd; rw [deriv_ΨS_eq]

theorem hasDerivAt_ψd (r : ℝ) : HasDerivAt ψd (ψdd r) r := by
  set g := SchwartzMap.derivCLM ℝ ℂ ΨS
  have h1 : HasDerivAt (g : ℝ → ℂ) (deriv g r) r := (g.differentiableAt).hasDerivAt
  have h2 := (Complex.reCLM.hasFDerivAt (x := g r)).comp_hasDerivAt r h1
  have e : ψd = fun r => (g r).re := funext ψd_eq
  rw [e]
  have e2 : deriv (g : ℝ → ℂ) r = SchwartzMap.derivCLM ℝ ℂ g r := by
    rw [SchwartzMap.derivCLM_apply]
  rw [e2] at h2
  exact h2

theorem ψdd_decay (M : ℕ) : ∃ C, 0 ≤ C ∧ ∀ r, |ψdd r| ≤ C / (1 + |r|) ^ M := by
  set F := SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ ΨS)
  set C0 := 2 ^ M * (Finset.Iic (M, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨max C0 0, le_max_right _ _, fun r => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, 0)) (k := M) (n := 0)
    le_rfl le_rfl F r
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  rw [le_div_iff₀ (by positivity), mul_comm]
  calc (1 + |r|) ^ M * |ψdd r| ≤ (1 + |r|) ^ M * ‖F r‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ C0 := this
    _ ≤ max C0 0 := le_max_left _ _

def Cdd : ℝ := (ψdd_decay 8).choose

theorem Cdd_nonneg : 0 ≤ Cdd := (ψdd_decay 8).choose_spec.1

theorem ψdd_le (r : ℝ) : |ψdd r| ≤ Cdd / (1 + |r|) ^ 8 := (ψdd_decay 8).choose_spec.2 r

theorem ψd_neg (r : ℝ) : ψd (-r) = -ψd r := by
  have h2 : HasDerivAt (fun r => ψ (-r)) (-ψd (-r)) r := by
    have := (hasDerivAt_ψ (-r)).comp r (hasDerivAt_neg r)
    convert this using 1; ring
  have h3 : (fun r => ψ (-r)) = ψ := funext ψ_neg
  rw [h3] at h2
  have := (hasDerivAt_ψ r).unique h2
  linarith

/-- `∑_k ψ'(s(1/2 + k)) = 0`. -/
theorem tsum_ψd_half (s : ℝ) : ∑' k : ℤ, ψd (s * (1 / 2 + k)) = 0 := by
  set f : ℤ → ℝ := fun k => ψd (s * (1 / 2 + k))
  let e : ℤ ≃ ℤ := ⟨fun k => -1 - k, fun k => -1 - k, fun k => by ring, fun k => by ring⟩
  have h : ∀ k, f (e k) = -f k := by
    intro k
    simp only [f, e, Equiv.coe_fn_mk]
    rw [show s * (1 / 2 + ((-1 - k : ℤ) : ℝ)) = -(s * (1 / 2 + k)) by push_cast; ring, ψd_neg]
  have h1 : ∑' k, f (e k) = ∑' k, f k := e.tsum_eq f
  simp_rw [h] at h1
  rw [tsum_neg] at h1
  linarith

theorem abs_add_int_ge_quarter' {y : ℝ} (hy : y ∈ Icc (1 / 4 : ℝ) (1 / 2)) (k : ℤ) :
    1 / 4 ≤ |y + k| ∧ |(k : ℝ)| / 4 ≤ |y + k| := by
  obtain ⟨h1, h2⟩ := hy
  rcases le_or_gt 0 k with hk | hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hk']
    constructor <;> linarith
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    constructor <;> linarith

/-- `B₄ = ∑_k (1 + |k|/4)^{-2}`. -/
def B4 : ℝ := ∑' k : ℤ, ((1 + |(k : ℝ)| / 4) ^ 2)⁻¹

theorem B4_nonneg : 0 ≤ B4 := tsum_nonneg fun k => by positivity

theorem ψdd_bound_term {s : ℝ} (hs : 1 ≤ s) {y : ℝ} (hy : y ∈ Icc (1 / 4 : ℝ) (1 / 2)) (k : ℤ) :
    |ψdd (s * (y + k))| ≤ Cdd * ((1 + s / 4) ^ 6)⁻¹ * ((1 + |(k : ℝ)| / 4) ^ 2)⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hCdd := Cdd_nonneg
  obtain ⟨h1, h2⟩ := abs_add_int_ge_quarter' hy k
  refine (ψdd_le _).trans ?_
  have ha : |s * (y + k)| = s * |y + k| := by rw [abs_mul, abs_of_pos hs0]
  have e1 : 1 + s / 4 ≤ 1 + |s * (y + k)| := by rw [ha]; nlinarith
  have e2 : 1 + |(k : ℝ)| / 4 ≤ 1 + |s * (y + k)| := by rw [ha]; nlinarith [abs_nonneg (y + k)]
  have key : (1 + s / 4) ^ 6 * (1 + |(k : ℝ)| / 4) ^ 2 ≤ (1 + |s * (y + k)|) ^ 8 := by
    calc (1 + s / 4) ^ 6 * (1 + |(k : ℝ)| / 4) ^ 2
        ≤ (1 + |s * (y + k)|) ^ 6 * (1 + |s * (y + k)|) ^ 2 := by gcongr
      _ = (1 + |s * (y + k)|) ^ 8 := by rw [← pow_add]
  calc Cdd / (1 + |s * (y + k)|) ^ 8 ≤ Cdd / ((1 + s / 4) ^ 6 * (1 + |(k : ℝ)| / 4) ^ 2) :=
        div_le_div_of_nonneg_left hCdd (by positivity) key
    _ = _ := by rw [div_mul_eq_div_div, div_eq_mul_inv (Cdd / _), div_eq_mul_inv]

/-- **The derivative of `Q_s` near `u = 2`.** -/
theorem abs_g'_corner {s : ℝ} (hs : 1 ≤ s) {x : ℝ} (hx : x ∈ Icc (1 / 4 : ℝ) (1 / 2)) :
    |∑' k : ℤ, s ^ 2 * ψd (s * (x + k))| ≤ s ^ 3 * (1 / 2 - x) * (Cdd * B4 * ((1 + s / 4) ^ 6)⁻¹) := by
  have hs0 : 0 < s := by linarith
  have hCdd := Cdd_nonneg
  set c : ℤ → ℝ := fun k => Cdd * ((1 + s / 4) ^ 6)⁻¹ * ((1 + |(k : ℝ)| / 4) ^ 2)⁻¹
  have hcs : Summable c := summable_b4.mul_left _
  -- termwise mean value bound
  have hterm : ∀ k : ℤ, |ψd (s * (x + k)) - ψd (s * (1 / 2 + k))| ≤ s * (1 / 2 - x) * c k := by
    intro k
    have hb : ∀ t ∈ Icc (s * (x + k)) (s * (1 / 2 + k)), ‖ψdd t‖ ≤ c k := by
      intro t ht
      set y := t / s - k
      have ht' : t = s * (y + k) := by simp only [y]; field_simp; ring
      have hy : y ∈ Icc (1 / 4 : ℝ) (1 / 2) := by
        have e1 : x + k ≤ t / s := by rw [le_div_iff₀ hs0]; linarith [ht.1]
        have e2 : t / s ≤ 1 / 2 + k := by rw [div_le_iff₀ hs0]; linarith [ht.2]
        constructor <;> simp only [y] <;> linarith [hx.1]
      rw [Real.norm_eq_abs, ht']
      exact ψdd_bound_term hs hy k
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ψd) (f' := ψdd)
      (s := Icc (s * (x + k)) (s * (1 / 2 + k))) (C := c k)
      (fun t _ => (hasDerivAt_ψd t).hasDerivWithinAt) hb (convex_Icc _ _)
      ⟨by nlinarith [hx.2], le_rfl⟩ ⟨le_rfl, by nlinarith [hx.2]⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      show s * (x + k) - s * (1 / 2 + k) = -(s * (1 / 2 - x)) by ring, abs_neg,
      abs_of_nonneg (a := s * (1 / 2 - x)) (by nlinarith [hx.2])] at h
    linarith
  -- summability
  have hsd : Summable fun k : ℤ => ψd (s * (x + k)) := by
    obtain ⟨h1, -⟩ := exists_sum_ψd_bound.choose_spec.2 s hs x ⟨by linarith [hx.1], hx.2⟩
    exact h1.of_abs
  have hsh : Summable fun k : ℤ => ψd (s * (1 / 2 + k)) := by
    obtain ⟨h1, -⟩ := exists_sum_ψd_bound.choose_spec.2 s hs (1 / 2) ⟨by norm_num, le_rfl⟩
    exact h1.of_abs
  have e : ∑' k : ℤ, s ^ 2 * ψd (s * (x + k)) =
      s ^ 2 * ∑' k : ℤ, (ψd (s * (x + k)) - ψd (s * (1 / 2 + k))) := by
    rw [Summable.tsum_sub hsd hsh, tsum_ψd_half, sub_zero, tsum_mul_left]
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg s)]
  have hsdiff : Summable fun k : ℤ => |ψd (s * (x + k)) - ψd (s * (1 / 2 + k))| :=
    (hcs.mul_left (s * (1 / 2 - x))).of_nonneg_of_le (fun k => abs_nonneg _) hterm
  have h1 : |∑' k : ℤ, (ψd (s * (x + k)) - ψd (s * (1 / 2 + k)))| ≤
      ∑' k : ℤ, s * (1 / 2 - x) * c k := by
    refine (show |∑' k : ℤ, (ψd (s * (x + k)) - ψd (s * (1 / 2 + k)))| ≤
        ∑' k : ℤ, |ψd (s * (x + k)) - ψd (s * (1 / 2 + k))| by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun k : ℤ =>
        ψd (s * (x + k)) - ψd (s * (1 / 2 + k))) (by simpa only [Real.norm_eq_abs] using hsdiff)).trans ?_
    exact hsdiff.tsum_le_tsum hterm (hcs.mul_left _)
  have h2 : ∑' k : ℤ, s * (1 / 2 - x) * c k = s * (1 / 2 - x) * (Cdd * B4 * ((1 + s / 4) ^ 6)⁻¹) := by
    rw [tsum_mul_left]
    simp only [c]
    rw [tsum_mul_left, B4]; ring
  calc s ^ 2 * |∑' k : ℤ, (ψd (s * (x + k)) - ψd (s * (1 / 2 + k)))| ≤
      s ^ 2 * (s * (1 / 2 - x) * (Cdd * B4 * ((1 + s / 4) ^ 6)⁻¹)) := by
        rw [← h2]; gcongr
    _ = _ := by ring

open Polynomial in
theorem Pd_eq_sum (τ u : ℝ) :
    Pd τ u = ∑ i ∈ Finset.range (⌊τ⌋₊ + 1), PrePtFamily.a i *
      (if τ / 2 ^ i < 1 then 0 else 1 / (cc * (τ / 2 ^ i)) * ((Q (τ / 2 ^ i)).derivative).eval u) := by
  simp only [Pd, Pc, PrePtFamily.toPtFamily, PrePtFamily.avgP, derivative_sum, derivative_mul,
    derivative_C, zero_mul, zero_add, eval_finsetSum, eval_mul, eval_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show PtF.prePt.P = P0 from rfl, derivative_P0]
  split_ifs <;> simp

theorem xu_one : xu 1 = 1 / 4 := by
  unfold xu; rw [sub_self, Real.arccos_zero]; have := pi_pos; field_simp; ring

/-- `|Q_s'(u)| ≤ s³ C_dd B₄ (1+s/4)^{-6}/(8π)` for `u ∈ [1, 2)`. -/
theorem abs_Qd_corner {s : ℝ} (hs : 1 ≤ s) {u : ℝ} (hu : u ∈ Ico (1 : ℝ) 2) :
    |((Polynomial.derivative (Q s))).eval u| ≤
      s ^ 3 * (Cdd * B4 * ((1 + s / 4) ^ 6)⁻¹) / (8 * π) := by
  have hpi := pi_pos
  set x := xu u
  have hx1 : 1 / 4 ≤ x := by rw [← xu_one]; exact xu_mono hu.1 zero_le_one hu.2.le
  have hx2 : x < 1 / 2 := xu_lt_half hu.2
  have hxI : x ∈ Ioo (-1 / 4 : ℝ) (3 / 4) := ⟨by linarith, by linarith⟩
  have hcos : 1 - Real.cos (2 * π * x) = u := cos_xu ⟨by linarith [hu.1], hu.2.le⟩
  have hQ := Qderiv_eq hs hxI
  rw [hcos] at hQ
  have hg := abs_g'_corner hs ⟨hx1, hx2.le⟩
  rw [← hQ] at hg
  -- `sin 2πx ≥ 4(1/2 - x)`
  have hsin : 4 * (1 / 2 - x) ≤ Real.sin (2 * π * x) := by
    have h1 : Real.sin (2 * π * x) = Real.sin (2 * π * (1 / 2 - x)) := by
      rw [show 2 * π * x = π - 2 * π * (1 / 2 - x) by ring, Real.sin_pi_sub]
    rw [h1]
    have h2 := Real.mul_le_sin (x := 2 * π * (1 / 2 - x)) (by nlinarith) (by nlinarith)
    have e : 2 / π * (2 * π * (1 / 2 - x)) = 4 * (1 / 2 - x) := by field_simp; ring
    linarith
  have hd : 0 < 1 / 2 - x := by linarith
  have hsp : 0 < 2 * π * Real.sin (2 * π * x) := by nlinarith
  rw [abs_mul, abs_of_pos hsp] at hg
  have hB := B4_nonneg
  have hCdd := Cdd_nonneg
  rw [le_div_iff₀ (by positivity)]
  have h1 : |((Polynomial.derivative (Q s))).eval u| * (8 * π) * (1 / 2 - x) ≤
      s ^ 3 * (Cdd * B4 * ((1 + s / 4) ^ 6)⁻¹) * (1 / 2 - x) := by
    calc |((Polynomial.derivative (Q s))).eval u| * (8 * π) * (1 / 2 - x)
        = |((Polynomial.derivative (Q s))).eval u| * (2 * π * (4 * (1 / 2 - x))) := by ring
      _ ≤ |((Polynomial.derivative (Q s))).eval u| * (2 * π * Real.sin (2 * π * x)) := by gcongr
      _ ≤ s ^ 3 * (1 / 2 - x) * (Cdd * B4 * ((1 + s / 4) ^ 6)⁻¹) := hg
      _ = _ := by ring
  exact le_of_mul_le_mul_right h1 hd

/-- The constant `K_c = 512 C_dd B₄ S₄/(π c)`. -/
def Kc : ℝ := 512 * Cdd * B4 * Som 4 / (π * cc)

theorem Kc_nonneg : 0 ≤ Kc := by
  have := Cdd_nonneg; have := B4_nonneg; have := Som_nonneg (r := 4) (by norm_num)
  have := pi_pos; have := cc_pos
  unfold Kc; positivity

/-- **`|τ P_τ'(u)| ≤ K_c τ^{-3}`** for `u ∈ [1, 2)`, `τ > 0`. -/
theorem abs_tau_Pd_corner {u : ℝ} (hu : u ∈ Ico (1 : ℝ) 2) {τ : ℝ} (hτ : 0 < τ) :
    |τ * Pd τ u| ≤ Kc * (τ ^ 3)⁻¹ := by
  have hpi := pi_pos
  have hcc := cc_pos
  set K := 512 * Cdd * B4 / (π * cc)
  have hK : 0 ≤ K := by have := Cdd_nonneg; have := B4_nonneg; positivity
  have hterm : ∀ i : ℕ, |PrePtFamily.a i * (if τ / 2 ^ i < 1 then 0 else
      1 / (cc * (τ / 2 ^ i)) * ((Polynomial.derivative (Q (τ / 2 ^ i)))).eval u)| ≤
      K * (τ ^ 4)⁻¹ * (om i * 4 ^ i) := by
    intro i
    split_ifs with h
    · simp; have := om_pos i; positivity
    · push Not at h
      set s := τ / 2 ^ i
      have hs0 : 0 < s := by linarith
      have hQ := abs_Qd_corner h hu
      rw [abs_mul, abs_of_pos (PrePtFamily.a_pos i), abs_mul,
        abs_of_pos (by positivity : 0 < 1 / (cc * s)), a_eq_om]
      have h6 : ((1 + s / 4) ^ 6)⁻¹ ≤ 4096 * (s ^ 6)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
          div_le_iff₀ (by positivity)]
        have : s ≤ 4 * (1 + s / 4) := by linarith
        calc s ^ 6 ≤ (4 * (1 + s / 4)) ^ 6 := pow_le_pow_left₀ hs0.le this 6
          _ = 4096 * (1 + s / 4) ^ 6 := by ring
      have hs4 : s ^ 4 = τ ^ 4 / 16 ^ i := by
        simp only [s]; rw [div_pow, two_pow_pow]; norm_num
      have hCdd := Cdd_nonneg; have hB := B4_nonneg
      calc om i / 4 ^ i * (1 / (cc * s) * |((Polynomial.derivative (Q s))).eval u|)
          ≤ om i / 4 ^ i * (1 / (cc * s) * (s ^ 3 * (Cdd * B4 * (4096 * (s ^ 6)⁻¹)) / (8 * π))) := by
            gcongr
            · have := om_pos i; positivity
            · exact hQ.trans (by gcongr)
        _ = K * om i / (4 ^ i * s ^ 4) := by simp only [K]; field_simp; ring
        _ = K * (τ ^ 4)⁻¹ * (om i * 4 ^ i) := by
            rw [hs4]
            have : (16 : ℝ) ^ i = 4 ^ i * 4 ^ i := by rw [← mul_pow]; norm_num
            rw [this]; field_simp
  rw [Pd_eq_sum, abs_mul, abs_of_pos hτ]
  have hsum := summable_om_pow 4
  have h1 : |∑ i ∈ Finset.range (⌊τ⌋₊ + 1), PrePtFamily.a i * (if τ / 2 ^ i < 1 then 0 else
      1 / (cc * (τ / 2 ^ i)) * ((Polynomial.derivative (Q (τ / 2 ^ i)))).eval u)| ≤
      K * (τ ^ 4)⁻¹ * Som 4 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [← Finset.mul_sum, Som]
    gcongr
    exact hsum.sum_le_tsum _ (fun i _ => by have := om_pos i; positivity)
  calc τ * |∑ i ∈ Finset.range (⌊τ⌋₊ + 1), PrePtFamily.a i * (if τ / 2 ^ i < 1 then 0 else
      1 / (cc * (τ / 2 ^ i)) * ((Polynomial.derivative (Q (τ / 2 ^ i)))).eval u)|
      ≤ τ * (K * (τ ^ 4)⁻¹ * Som 4) := by gcongr
    _ = Kc * (τ ^ 3)⁻¹ := by simp only [K, Kc]; field_simp

/-- **The tail near the corner**: `|∫_T^∞ τ P_τ'(u) dτ| ≤ K_c/(2T²)`. -/
theorem abs_tail_corner {u : ℝ} (hu : u ∈ Ico (1 : ℝ) 2) {T : ℝ} (hT : 0 < T) :
    |∫ τ in Ioi T, τ * Pd τ u| ≤ Kc * (T ^ 2)⁻¹ / 2 := by
  have e : EqOn (fun τ : ℝ => (τ ^ 3)⁻¹) (fun τ => τ ^ (-(3 : ℝ))) (Ioi T) := by
    intro τ hτ
    have : 0 < τ := lt_trans hT hτ
    simp only
    rw [Real.rpow_neg this.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hi := (integrableOn_Ioi_rpow_of_lt (show (-(3 : ℝ)) < -1 by norm_num) hT).congr_fun
    e.symm measurableSet_Ioi
  have hval : ∫ τ in Ioi T, (τ ^ 3)⁻¹ = (T ^ 2)⁻¹ / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_rpow_of_lt (by norm_num) hT,
      show (-(3 : ℝ)) + 1 = -2 by norm_num, Real.rpow_neg hT.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hi.const_mul Kc)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact abs_tau_Pd_corner hu (lt_trans hT hτ)
  · rw [integral_const_mul, hval]; ring_nf; rfl

end

end Step2.D2