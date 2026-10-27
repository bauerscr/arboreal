import Step2.D2.D2HV8

/-!
# Line 1 of `prop:d2` at `j = 0`

* `cov_e1_value`: `|C_{(L^j/2, L^{j+1}/2]}(x, y) - (1/2π) log L| ≤ (2π)^{-2}(ErrC1 L^{-2j} + …)` for
  `x - y = e₀`, for every `j ≥ 0` (the proof of `Cj_succ_e1_value` without the `lowEnd`);
* `C1_e1_value`: `|C_1(e₀, 0) - (1/2π) log L| ≤ E_line0`, `E_line0` independent of `L`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- `C_{(L^j/2, L^{j+1}/2]}(x, y)` for `x - y = e₀`, any `j`. -/
theorem cov_e1_value {n : ℕ} [NeZero n] {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1)
    (hL : 1 ≤ L) (j : ℕ) (x y : Grassmann.Torus 2 n)
    (hr : ∀ i, (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ZMod n) = ((x - y : Grassmann.Torus 2 n) :
      Fin 2 → ZMod n) i)
    (hn : L ^ (j + 1) / 2 + 1 < n) :
    |FRD.cov Pc msq (Ioc (L ^ j / 2) (L ^ (j + 1) / 2)) x y - Real.log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * (ErrC1 / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
  have hpi := pi_pos
  have hL0 : 0 < L := by linarith
  have hc : 0 < L ^ j := by positivity
  have hCj := cov_eq_integral_BZ Pc hm (a := L ^ j / 2) (b := L ^ (j + 1) / 2) (by positivity)
    x y ![1, 0] hr (by simpa using hn)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_zero, one_mul,
    zero_mul, add_zero] at hCj
  set S := Ioc (L ^ j / 2) (L ^ (j + 1) / 2)
  set F := fun z : ℂ => (Ep (L ^ (j + 1) * √(lamC z)) - Ep (L ^ j * √(lamC z))) / lamC z
  have hi : IntegrableOn (fun y => (Ep (L * y) - Ep y) / y) (Ioi 0) := by
    have := Ep_profile.integrableOn one_pos hL
    simpa using this
  have hF : IntegrableOn F BZ := by
    have := lattice_integrableOn (h := fun y => Ep (L * y) - Ep y)
      (h' := fun y => L * Ep' (L * y) - Ep' y)
      (fun y hy => hasDerivAt_scale_diff (fun y _ => hasDerivAt_Ep y) hL0 hy)
      (fun y hy => Ep_decay.diff (by norm_num) hL hy) hi (by norm_num : (2 : ℝ) < 3) hc
    simpa only [pow_succ_mul_eq] using this
  have hch : IntegrableOn (chat Pc msq S) BZ :=
    integrableOn_chat Pc hm (by positivity) (by
      rw [pow_succ]; gcongr; nlinarith)
  have hcos : ∀ g : ℂ → ℝ, IntegrableOn g BZ → IntegrableOn (fun z => g z * Real.cos z.re) BZ :=
    fun g hg => Integrable.mul_bdd (c := 1) hg (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  have h1 := lattice_Ce1 Ep_profile (fun y _ => hasDerivAt_Ep y) Ep_decay (by norm_num) hL j
  have h2 := chat_profile_error hm hm1 hL j
  have hsplit : (∫ p in BZ, chat Pc msq S p * Real.cos p.re) =
      (∫ p in BZ, Real.cos p.re * F p) + ∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re := by
    rw [← integral_add ((hcos F hF).congr_fun (fun z _ => mul_comm _ _) measurableSet_BZ)
      (by
        have := (hcos _ hch).sub (hcos _ hF)
        exact this.congr_fun (fun z _ => by simp only [Pi.sub_apply]; ring) measurableSet_BZ)]
    refine setIntegral_congr_fun measurableSet_BZ fun z _ => ?_
    simp only [F]; ring
  have h3 : |∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re| ≤
      ∫ p in BZ, |chat Pc msq S p - F p| := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) (hch.sub hF).abs
      (Eventually.of_forall fun z => ?_))
    simp only [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have hp : (0 : ℝ) < (2 * π)⁻¹ ^ 2 := by positivity
  rw [hCj, ← inv_pow, hsplit, mul_add]
  have e : (2 * π)⁻¹ ^ 2 * ∫ p in BZ, Real.cos p.re * F p = (2 * π)⁻¹ ^ 2 * (∫ z in BZ, Real.cos z.re *
      ((Ep (L ^ (j + 1) * √(lamC z)) - Ep (L ^ j * √(lamC z))) / lamC z)) := rfl
  have h4 : |(2 * π)⁻¹ ^ 2 * ∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re| ≤
      (2 * π)⁻¹ ^ 2 * (ErrA / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left (h3.trans h2) hp.le
  have h5 := (abs_add_le _ _).trans (add_le_add h1 h4)
  rw [← e] at h5
  calc _ = |((2 * π)⁻¹ ^ 2 * (∫ p in BZ, Real.cos p.re * F p) - Real.log L / (2 * π)) +
        (2 * π)⁻¹ ^ 2 * ∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re| := by
        congr 1; ring
    _ ≤ _ := h5
    _ = _ := by rw [ErrC1]; ring

/-- **Line 1 at `j = 0`**: `|C_1(e₀, 0) - (1/2π) log L| ≤ E`, `E` independent of `L`. -/
theorem C1_e1_value : ∃ E : ℝ, 0 ≤ E ∧ ∀ (n : ℕ) [NeZero n] (L : ℝ) (msq : ℝ), 1 ≤ L →
    0 < msq → msq ≤ 1 → msq * L ^ 2 ≤ 4 → L / 2 + 1 < n →
    |FRD.cov Pc msq (Ioc 0 (L / 2)) (unitT 0 : Grassmann.Torus 2 n) 0 - Real.log L / (2 * π)| ≤ E := by
  obtain ⟨B, hB0, hB⟩ := DressedFRD.wt_Ioc_le Pc (d := 2) (by norm_num) 0
  have hpi := pi_pos
  have hE1 : 0 ≤ ErrC1 := by
    rw [ErrC1]
    have := ErrA_nonneg; have := KH_nonneg; have := kap_pos; have := Ia_nonneg 3
    positivity
  have hEB := ErrB_nonneg
  refine ⟨(2 * π)⁻¹ ^ 2 * (ErrC1 + 5 * ErrB) + B / 4, by positivity,
    fun n _ L msq hL hm hm1 hmL hn => ?_⟩
  have hsplit := cov_Ioc_add (n := n) Pc hm.le (a := 0) (b := 1 / 2) (c := L / 2) le_rfl
    (by norm_num) (by linarith)
  have e : FRD.cov Pc msq (Ioc 0 (L / 2)) (unitT 0 : Grassmann.Torus 2 n) 0 =
      FRD.cov Pc msq (Ioc 0 (1 / 2)) (unitT 0 : Grassmann.Torus 2 n) 0 +
        FRD.cov Pc msq (Ioc (1 / 2) (L / 2)) (unitT 0 : Grassmann.Torus 2 n) 0 := by
    rw [← hsplit]; rfl
  have h0 : |FRD.cov Pc msq (Ioc 0 (1 / 2)) (unitT 0 : Grassmann.Torus 2 n) 0| ≤ B / 4 := by
    simp only [FRD.cov, FRD.fmat]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    rw [abs_mul, abs_of_pos (by positivity)]
    have hw : ∀ m : Grassmann.Torus 2 n, |FRD.wt Pc msq (Ioc 0 (1 / 2)) m * (FRD.char m ((unitT 0 : Grassmann.Torus 2 n) - 0)).re|
        ≤ B / 4 := by
      intro m
      have h1 := hB n msq hm.le 0 (1 / 2) le_rfl (by norm_num) m
      simp only [pow_zero, inv_one, mul_one] at h1
      have h2 : 0 ≤ FRD.wt Pc msq (Ioc 0 (1 / 2)) m :=
        FRD.wt_nonneg Pc hm.le measurableSet_Ioc (fun t ht => ht.1) m
      have h3 : |(FRD.char m ((unitT 0 : Grassmann.Torus 2 n) - 0)).re| ≤ 1 :=
        (Complex.abs_re_le_norm _).trans (by rw [FRD.norm_char])
      rw [abs_mul, abs_of_nonneg h2]
      calc FRD.wt Pc msq (Ioc 0 (1 / 2)) m * |(FRD.char m ((unitT 0 : Grassmann.Torus 2 n) - 0)).re| ≤ B * (1 / 2) ^ 2 * 1 :=
            mul_le_mul h1 h3 (abs_nonneg _) (by positivity)
        _ = B / 4 := by ring
    calc ((n : ℝ) ^ 2)⁻¹ * |∑ m, FRD.wt Pc msq (Ioc 0 (1 / 2)) m * (FRD.char m ((unitT 0 : Grassmann.Torus 2 n) - 0)).re|
        ≤ ((n : ℝ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, B / 4 := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => hw m)
      _ = B / 4 := by
          rw [Finset.sum_const, Finset.card_univ, FRD.card_torus, nsmul_eq_mul]
          push_cast
          field_simp
  have h1 := cov_e1_value (n := n) hm.le hm1 hL 0 (unitT 0) 0 (lift_e1 n) (by simpa using hn)
  simp only [pow_zero, zero_add, pow_one, one_pow] at h1
  have h1' : (2 * π)⁻¹ ^ 2 * (ErrC1 / 1 + ErrB * msq * (1 + L ^ 2)) ≤
      (2 * π)⁻¹ ^ 2 * (ErrC1 + 5 * ErrB) := by
    have : msq * (1 + L ^ 2) ≤ 5 := by nlinarith
    have h2 : ErrB * msq * (1 + L ^ 2) ≤ 5 * ErrB := by
      calc ErrB * msq * (1 + L ^ 2) = ErrB * (msq * (1 + L ^ 2)) := by ring
        _ ≤ ErrB * 5 := mul_le_mul_of_nonneg_left this hEB
        _ = 5 * ErrB := by ring
    rw [div_one]
    gcongr
  rw [e]
  calc |FRD.cov Pc msq (Ioc 0 (1 / 2)) (unitT 0 : Grassmann.Torus 2 n) 0 +
        FRD.cov Pc msq (Ioc (1 / 2) (L / 2)) (unitT 0 : Grassmann.Torus 2 n) 0 - Real.log L / (2 * π)|
      ≤ |FRD.cov Pc msq (Ioc 0 (1 / 2)) (unitT 0 : Grassmann.Torus 2 n) 0| +
        |FRD.cov Pc msq (Ioc (1 / 2) (L / 2)) (unitT 0 : Grassmann.Torus 2 n) 0 -
          Real.log L / (2 * π)| := by
        rw [add_sub_assoc]; exact abs_add_le _ _
    _ ≤ B / 4 + (2 * π)⁻¹ ^ 2 * (ErrC1 + 5 * ErrB) := add_le_add h0 (h1.trans h1')
    _ = _ := by ring

end

end Step2.D2