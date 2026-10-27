import Step2.D2.D2Bv3

/-!
# `𝔅(w_T)` in terms of `ĉ_T` and `∂_{p₀} ĉ_T` (`prop:d2`, line 3)

* `cov_eq_cTor`: the torus covariance `w_T = cov(0, T]` is `C(a, b) = ĉ(r(a - b))` with the
  kernel `kerT`;
* `symb_kerT_zero`, `hasDerivAt_symb0`: `Â₀ = ĉ_T`, `∂_{p₀} Â₀ = i Â₁`;
* `hasDerivAt_chat_re`: `∂_{p₀} ĉ_T = K^{-2} 2 sin p₀ ∫_0^T τ P_τ'(u) dτ`;
* `symb_one_sq`: `Â₁² = -(∂_{p₀} ĉ_T)²`;
* `frakBT_eq`: `𝔅(w_T) = (2π)^{-2} ∫ [(2λ - 4 sin² p₀) ĉ_T² + (λ²/2)(∂_{p₀} ĉ_T)²]`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF Step2 Loc

variable {msq T : ℝ}

theorem natAbs_rep_le {n : ℕ} [NeZero n] (z : Grassmann.Torus 2 n) (i : Fin 2) :
    2 * (rep z i).natAbs ≤ n := by
  rw [natAbs_rep]; unfold Grassmann.zabs; omega

/-- **The covariance `w_T` is translation invariant with kernel `kerT`.** -/
theorem cov_eq_cTor {L N : ℕ} [NeZero L] (hm : 0 ≤ msq) (hT : 0 ≤ T)
    (hTn : 2 * T < (L ^ N : ℕ)) (a b : Lam 2 L N) :
    ((FRD.cov Pc msq (Ioc 0 T) a b : ℝ) : ℂ) = cTor (kerT msq T) (a - b) := by
  set r : Fin 2 → ℤ := rep (a - b)
  have hr : ∀ i, ((r i : ℤ) : ZMod (L ^ N)) = ((a - b : Lam 2 L N) : Fin 2 → ZMod (L ^ N)) i := by
    intro i
    have := congrFun (congrArg (fun y : Lam 2 L N => (y : Fin 2 → ZMod (L ^ N))) (prj_rep (a - b))) i
    exact this
  have h0 : 2 * (r 0).natAbs ≤ L ^ N := natAbs_rep_le (a - b) 0
  have h1 : 2 * (r 1).natAbs ≤ L ^ N := natAbs_rep_le (a - b) 1
  have hmax : 2 * max (r 0).natAbs (r 1).natAbs ≤ L ^ N := by
    rcases le_total (r 0).natAbs (r 1).natAbs with h | h
    · rw [max_eq_right h]; exact h1
    · rw [max_eq_left h]; exact h0
  have hn : T + max (r 0).natAbs (r 1).natAbs < ((L ^ N : ℕ) : ℝ) := by
    have h2 : ((2 * max (r 0).natAbs (r 1).natAbs : ℕ) : ℝ) ≤ ((L ^ N : ℕ) : ℝ) := by
      exact_mod_cast hmax
    have h3 : ((2 * max (r 0).natAbs (r 1).natAbs : ℕ) : ℝ) =
        2 * ((max (r 0).natAbs (r 1).natAbs : ℕ) : ℝ) := by push_cast; ring
    rw [h3] at h2
    have : ((max (r 0).natAbs (r 1).natAbs : ℕ) : ℝ) = max ((r 0).natAbs : ℝ) ((r 1).natAbs : ℝ) :=
      Nat.cast_max _ _
    rw [this] at h2
    linarith
  rw [cov_eq_integral_BZ Pc hm le_rfl a b r hr hn, cTor, kerT_eq_cos hm hT]

theorem kerT_range (hm : 0 ≤ msq) (hT : 0 ≤ T) (u : ℤ × ℤ) (hu : ⌊T⌋₊ < nm u) :
    kerT msq T u = 0 := by
  apply kerT_eq_zero hm hT
  intro h
  simp only [boxZ, Finset.mem_product, Finset.mem_Icc] at h
  simp only [nm] at hu
  omega

theorem kerT_even (u : ℤ × ℤ) : kerT msq T (-u.1, -u.2) = kerT msq T u :=
  kerT_neg u

theorem symb_kerT_eq_sum (hm : 0 ≤ msq) (hT : 0 ≤ T) (j : ℕ) (p : ℂ) :
    symb (kerT msq T) j p = ∑ v ∈ boxZ ⌊T⌋₊, (v.1 : ℂ) ^ j * kerT msq T v * ex v p := by
  rw [symb, finsum_eq_sum_of_support_subset]
  intro v hv
  simp only [Function.mem_support, ne_eq] at hv
  simp only [Finset.mem_coe]
  by_contra h
  exact hv (by rw [kerT_eq_zero hm hT h]; ring)

/-- **`Â₀ = ĉ_T`.** -/
theorem symb_kerT_zero (hm : 0 ≤ msq) (hT : 0 ≤ T) (p : ℂ) :
    symb (kerT msq T) 0 p = ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ) := by
  rw [symb_kerT_eq_sum hm hT, chat_fourier hm hT]
  simp

theorem hasDerivAt_ex_re (v : ℤ × ℤ) (p : ℂ) :
    HasDerivAt (fun t : ℝ => ex v (p + t)) (Complex.I * v.1 * ex v p) 0 := by
  have e : (fun t : ℝ => ex v (p + t)) = fun t : ℝ =>
      Complex.exp (((v.1 : ℝ) * (p.re + t) + (v.2 : ℝ) * p.im : ℝ) * Complex.I) := by
    funext t; simp [ex]
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => (((v.1 : ℝ) * (p.re + t) + (v.2 : ℝ) * p.im : ℝ) : ℂ))
      ((v.1 : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add p.re |>.const_mul (v.1 : ℝ)).add_const
      ((v.2 : ℝ) * p.im)
    have := this.ofReal_comp
    simpa using this
  have h2 := (h1.mul_const Complex.I).cexp
  convert h2 using 1
  simp [ex]; ring

/-- **`∂_{p₀} Â₀ = i Â₁`.** -/
theorem hasDerivAt_symb0 (hm : 0 ≤ msq) (hT : 0 ≤ T) (p : ℂ) :
    HasDerivAt (fun t : ℝ => symb (kerT msq T) 0 (p + t))
      (Complex.I * symb (kerT msq T) 1 p) 0 := by
  simp_rw [symb_kerT_eq_sum hm hT]
  rw [Finset.mul_sum]
  refine HasDerivAt.fun_sum fun v _ => ?_
  have := (hasDerivAt_ex_re v p).const_mul ((v.1 : ℂ) ^ 0 * kerT msq T v)
  convert this using 1; ring

/-! ### The `p₀`-derivative of `ĉ_T` -/

theorem uhatC_mem_Ioo (hm : 0 < msq) (p : ℂ) : uhatC msq p ∈ Ioo (0 : ℝ) 2 := by
  have h0 := lamC_nonneg p
  have h8 := lamC_le_eight p
  constructor
  · unfold uhatC; positivity
  · unfold uhatC; rw [div_lt_iff₀ (by positivity)]; linarith

/-- `∂_{p₀} ĉ_T = K^{-1} (∫_0^T τ P_τ'(u) dτ) (2 sin p₀ / K)`. -/
def dchat (msq T : ℝ) (p : ℂ) : ℝ :=
  (2 * 2 + msq)⁻¹ * (∫ τ in Ioc 0 T, τ * Pd τ (uhatC msq p)) * (2 * Real.sin p.re / (2 * 2 + msq))

theorem hasDerivAt_uhatC_re (msq : ℝ) (p : ℂ) :
    HasDerivAt (fun t : ℝ => uhatC msq (p + t)) (2 * Real.sin p.re / (2 * 2 + msq)) 0 := by
  have e : (fun t : ℝ => uhatC msq (p + t)) = fun t : ℝ =>
      ((2 - 2 * Real.cos (p.re + t)) + (2 - 2 * Real.cos p.im) + msq) / (2 * 2 + msq) := by
    funext t; simp [uhatC, lamC]
  rw [e]
  have h := (((Real.hasDerivAt_cos (p.re + 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add p.re)).const_mul
    2).const_sub 2 |>.add_const (2 - 2 * Real.cos p.im) |>.add_const msq |>.div_const (2 * 2 + msq)
  convert h using 1
  simp

theorem hasDerivAt_chat_re (hm : 0 < msq) (hT : 0 < T) (p : ℂ) :
    HasDerivAt (fun t : ℝ => chat Pc msq (Ioc 0 T) (p + t)) (dchat msq T p) 0 := by
  have hu := uhatC_mem_Ioo hm p
  obtain ⟨-, hd⟩ := hasDerivAt_integral_P measurableSet_Ioc (fun τ hτ => hτ.1) hu
    (FRD.integrableOn_Ioc Pc ⟨hu.1.le, hu.2.le⟩ T le_rfl)
  have h1 := HasDerivAt.comp (0 : ℝ) (h := fun t : ℝ => uhatC msq (p + t))
    (by rw [show uhatC msq (p + ((0 : ℝ) : ℂ)) = uhatC msq p by simp]; exact hd)
    (hasDerivAt_uhatC_re msq p)
  have h2 := h1.const_mul (2 * 2 + msq)⁻¹
  unfold dchat
  convert h2 using 1
  ring

/-- **`Â₁ = -i ∂_{p₀} ĉ_T`**, hence `Â₁² = -(∂_{p₀}ĉ_T)²`. -/
theorem symb_one_eq (hm : 0 < msq) (hT : 0 < T) (p : ℂ) :
    Complex.I * symb (kerT msq T) 1 p = (dchat msq T p : ℂ) := by
  have h1 := hasDerivAt_symb0 hm.le hT.le p
  have h2 := (hasDerivAt_chat_re hm hT p).ofReal_comp
  have e : (fun t : ℝ => symb (kerT msq T) 0 (p + t)) =
      fun t : ℝ => ((chat Pc msq (Ioc 0 T) (p + t) : ℝ) : ℂ) := by
    funext t; exact symb_kerT_zero hm.le hT.le (p + t)
  rw [e] at h1
  exact h1.unique h2

theorem symb_one_sq (hm : 0 < msq) (hT : 0 < T) (p : ℂ) :
    symb (kerT msq T) 1 p * symb (kerT msq T) 1 p = -((dchat msq T p ^ 2 : ℝ) : ℂ) := by
  have h := symb_one_eq hm hT p
  have hI : symb (kerT msq T) 1 p = -Complex.I * (dchat msq T p : ℂ) := by
    rw [← h]; rw [← mul_assoc, neg_mul, Complex.I_mul_I]; ring
  rw [hI]; push_cast; ring_nf; rw [Complex.I_sq]; ring

/-! ### `𝔅(w_T)` -/

/-- `𝔅(w_T) = -negBub(w_T)`, with the block `{0}`. -/
def frakBT (L N : ℕ) [NeZero L] (msq T : ℝ) : ℂ :=
  -negBub (fun a b : Lam 2 L N => ((FRD.cov Pc msq (Ioc 0 T) a b : ℝ) : ℂ)) {0} 0

theorem base_singleton_zero {L N : ℕ} [NeZero L] : base ({0} : Finset (Lam 2 L N)) = 0 := by
  unfold base
  rw [dif_pos (Finset.singleton_nonempty 0)]
  exact Finset.mem_singleton.1 (Finset.singleton_nonempty (0 : Lam 2 L N)).choose_spec

/-- **`𝔅(w_T)` in momentum space.** For `0 < m²`, `0 < T`, `2(⌊T⌋ + 4) < L^N`:
`𝔅(w_T) = (2π)^{-2} [∫ (2λ - 4 sin² p₀) ĉ_T² + ∫ (λ²/2) (∂_{p₀} ĉ_T)²]`. -/
theorem frakBT_eq {L N : ℕ} [NeZero L] (hm : 0 < msq) (hT : 0 < T)
    (hn : 2 * (⌊T⌋₊ + 4) < L ^ N) :
    frakBT L N msq T = ((((2 * π) ^ 2)⁻¹ *
      ((∫ p in BZ, (2 * lamC p - 4 * Real.sin p.re ^ 2) * chat Pc msq (Ioc 0 T) p ^ 2) +
        ∫ p in BZ, lamC p ^ 2 / 2 * dchat msq T p ^ 2) : ℝ) : ℂ) := by
  have hTn : 2 * T < ((L ^ N : ℕ) : ℝ) := by
    have h1 : T < (⌊T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one T
    have h2 : ((2 * (⌊T⌋₊ + 4) : ℕ) : ℝ) < ((L ^ N : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at h2 ⊢; linarith
  unfold frakBT
  rw [negBub_momentum' (kerT msq T) (R := ⌊T⌋₊) (kerT_range hm.le hT.le) kerT_even hn
    (fun a b => cov_eq_cTor hm.le hT.le hTn a b) (Finset.singleton_nonempty 0)
    (fun x hx => by
      rw [Finset.mem_singleton.1 hx, base_singleton_zero, sub_zero, Grassmann.supNorm_zero]; omega)]
  simp_rw [symb_kerT_zero hm.le hT.le, symb_one_sq hm hT]
  have e1 : (∫ p in BZ, ((4 * Real.sin p.re ^ 2 - 2 * lamC p : ℝ) : ℂ) *
      (((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ) * ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ))) =
      ((-∫ p in BZ, (2 * lamC p - 4 * Real.sin p.re ^ 2) * chat Pc msq (Ioc 0 T) p ^ 2 : ℝ) : ℂ) := by
    rw [← integral_neg, ← integral_complex_ofReal]
    congr 1; funext p; push_cast; ring
  have e2 : (∫ p in BZ, ((lamC p ^ 2 / 2 : ℝ) : ℂ) * -((dchat msq T p ^ 2 : ℝ) : ℂ)) =
      ((-∫ p in BZ, lamC p ^ 2 / 2 * dchat msq T p ^ 2 : ℝ) : ℂ) := by
    rw [← integral_neg, ← integral_complex_ofReal]
    congr 1; funext p; push_cast; ring
  rw [e1, e2]
  push_cast
  ring

end

end Step2.D2
