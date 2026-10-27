import Step2.D2.D2Bv2
import Step2.D2.D2Bub5

/-!
# The symbol `ĉ_T` as a trigonometric polynomial and its `p₀`-derivative (`prop:d2`, line 3)

* `TP_fourier`: a trigonometric polynomial of degree `k` is its own Fourier series;
* `chat_fourier`: `ĉ_T = ∑_{|a|_∞ ≤ T} ĉ_a e^{i a·p}` with `ĉ_a = ⨍ ĉ_T e^{-i a·p}` (`kerT`);
* `hasDerivAt_chat_re`: the `p₀`-derivative of `ĉ_T`;
* `deriv_chat_bounds`: with `ν = λ + m²`, `A = -2 sin p₀/ν²`:
  `|∂₀ĉ_T - A| ≤ C_D (2π²K)³/(6πK ν³ T³)`, `|∂₀ĉ_T| ≤ C_D T³/(6πK)`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-! ### Fourier inversion for trigonometric polynomials -/

/-- `[-k, k]²`. -/
def boxZ (k : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(k : ℤ)) k ×ˢ Finset.Icc (-(k : ℤ)) k

/-- The Fourier coefficient `(2π)^{-2} ∫_{[-π,π]²} f e^{-i a·p}`. -/
def fcoef (f : ℂ → ℂ) (a : ℤ × ℤ) : ℂ := ((2 * (π : ℂ)) ^ 2)⁻¹ * ∫ q in BZ, f q * ex (-a) q

theorem two_pi_sq_ne : (2 * (π : ℂ)) ^ 2 ≠ 0 := by
  have := pi_pos; exact pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast this.ne'))

theorem fc_ex (a b : ℤ × ℤ) : fcoef (ex b) a = if b = a then 1 else 0 := by
  unfold fcoef
  have : (fun q => ex b q * ex (-a) q) = ex (b + -a) := funext fun q => ex_add _ _ _
  rw [this, integral_ex_BZ]
  have e : b + -a = 0 ↔ b = a := by rw [← sub_eq_add_neg, sub_eq_zero]
  by_cases h : b = a
  · rw [if_pos (e.2 h), if_pos h]; field_simp [two_pi_sq_ne]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h, mul_zero]

theorem TP_continuous {k : ℕ} {f : ℂ → ℂ} (hf : f ∈ TP k) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, -, -, rfl⟩ := hg
    exact continuous_ex a
  | zero => exact continuous_const
  | add g h _ _ hg hh => exact hg.add hh
  | smul c g _ hg => exact continuous_const.mul hg

theorem integrableOn_of_continuous {f : ℂ → ℂ} (hf : Continuous f) : IntegrableOn f BZ :=
  hf.continuousOn.integrableOn_compact isCompact_BZ

theorem fc_add {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g) (a : ℤ × ℤ) :
    fcoef (f + g) a = fcoef f a + fcoef g a := by
  unfold fcoef
  simp only [Pi.add_apply, add_mul]
  have := integral_add (μ := volume.restrict BZ) (f := fun q => f q * ex (-a) q)
    (g := fun q => g q * ex (-a) q) (integrableOn_of_continuous (hf.mul (continuous_ex _)))
    (integrableOn_of_continuous (hg.mul (continuous_ex _)))
  rw [this, mul_add]

theorem fc_smul (c : ℂ) (f : ℂ → ℂ) (a : ℤ × ℤ) : fcoef (c • f) a = c * fcoef f a := by
  unfold fcoef
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]; ring

/-- **Fourier inversion for trigonometric polynomials.** -/
theorem TP_fourier {k : ℕ} {f : ℂ → ℂ} (hf : f ∈ TP k) (p : ℂ) :
    f p = ∑ a ∈ boxZ k, fcoef f a * ex a p := by
  induction hf using Submodule.span_induction generalizing p with
  | mem g hg =>
    obtain ⟨b, h1, h2, rfl⟩ := hg
    simp_rw [fc_ex]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; rw [if_neg (Ne.symm hc), zero_mul]
    · intro hb
      exfalso; apply hb
      simp only [boxZ, Finset.mem_product, Finset.mem_Icc]
      omega
  | zero =>
    simp [fcoef]
  | add g h hg hh ihg ihh =>
    rw [Pi.add_apply, ihg, ihh, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fc_add (TP_continuous hg) (TP_continuous hh)]; ring
  | smul c g _ ih =>
    rw [Pi.smul_apply, ih, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fc_smul]; ring

/-! ### The symbol `ĉ_T` -/

variable {msq T : ℝ}

/-- `P_τ(û(·))` is a trigonometric polynomial of degree `⌊T⌋` for `0 < τ ≤ T`. -/
theorem P_TP (msq : ℝ) {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) T) :
    (fun p => (((Pc.P τ).eval (uhatC msq p) : ℝ) : ℂ)) ∈ TP ⌊T⌋₊ :=
  TP.poly (TP.uhat msq) _ (Nat.le_floor ((Pc.natDegree_le τ hτ.1).trans hτ.2))

/-- The kernel `ĉ_a = ⨍ ĉ_T e^{-i a·p}`. -/
def kerT (msq T : ℝ) (a : ℤ × ℤ) : ℂ :=
  fcoef (fun p => ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ)) a

theorem measurable_fcP (msq : ℝ) (a : ℤ × ℤ) :
    Measurable fun τ => fcoef (fun p => (((Pc.P τ).eval (uhatC msq p) : ℝ) : ℂ)) a := by
  unfold fcoef
  have hu := measurable_uncurry_of_continuous_of_measurable
    (u := fun (q : ℂ) (τ : ℝ) => (((Pc.P τ).eval (uhatC msq q) : ℝ) : ℂ) * ex (-a) q)
    (fun τ => (Complex.continuous_ofReal.comp ((Polynomial.continuous _).comp
      (continuous_uhatC msq))).mul (continuous_ex _))
    (fun q => (Complex.measurable_ofReal.comp (Pc.measurable _)).mul_const _)
  have h2 : Measurable (Function.uncurry fun (τ : ℝ) (q : ℂ) =>
      (((Pc.P τ).eval (uhatC msq q) : ℝ) : ℂ) * ex (-a) q) := by
    have := hu.comp measurable_swap; exact this
  have := h2.stronglyMeasurable.integral_prod_right (ν := volume.restrict BZ)
  exact this.measurable.const_mul _

theorem norm_fcP_le (hm : 0 ≤ msq) (a : ℤ × ℤ) {τ : ℝ} (hτ : 0 < τ) {K0 : ℝ}
    (hK : ∀ t, 0 < t → ∀ u ∈ Icc (0 : ℝ) 2, (Pc.P t).eval u ≤ K0) :
    ‖fcoef (fun p => (((Pc.P τ).eval (uhatC msq p) : ℝ) : ℂ)) a‖ ≤
      ‖((2 * (π : ℂ)) ^ 2)⁻¹‖ * (K0 * volume.real BZ) := by
  unfold fcoef
  rw [norm_mul]
  gcongr
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := BZ)
    (f := fun q => (((Pc.P τ).eval (uhatC msq q) : ℝ) : ℂ) * ex (-a) q) (C := K0)
    isCompact_BZ.measure_lt_top (fun q _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Pc.nonneg τ hτ _ (uhatC_mem hm q))]
      have : ‖ex (-a) q‖ = 1 := by rw [ex, Complex.norm_exp_ofReal_mul_I]
      rw [this, mul_one]; exact hK τ hτ _ (uhatC_mem hm q))
  exact h

/-- **`ĉ_T` is its Fourier series**, with coefficients supported in `[-⌊T⌋, ⌊T⌋]²`. -/
theorem chat_fourier (hm : 0 ≤ msq) (hT : 0 ≤ T) (p : ℂ) :
    ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ) = ∑ a ∈ boxZ ⌊T⌋₊, kerT msq T a * ex a p := by
  obtain ⟨K0, hK0, hK⟩ := FRD.eval_le_const Pc
  set K := (2 * 2 + msq : ℝ)
  set c : (ℤ × ℤ) → ℂ := fun a => (K : ℂ)⁻¹ *
    ∫ τ in Ioc 0 T, (τ : ℂ) * fcoef (fun p => (((Pc.P τ).eval (uhatC msq p) : ℝ) : ℂ)) a
  have hint : ∀ a, IntegrableOn (fun τ : ℝ => (τ : ℂ) *
      fcoef (fun p => (((Pc.P τ).eval (uhatC msq p) : ℝ) : ℂ)) a) (Ioc 0 T) := by
    intro a
    refine Measure.integrableOn_of_bounded (M := T * (‖((2 * (π : ℂ)) ^ 2)⁻¹‖ *
      (K0 * volume.real BZ))) (by simp) ?_ ?_
    · exact (Complex.measurable_ofReal.mul (measurable_fcP msq a)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ.1]
      exact mul_le_mul hτ.2 (norm_fcP_le hm a hτ.1 hK) (norm_nonneg _) hT
  -- the expansion with coefficients `c`
  have hexp : ∀ q, ((chat Pc msq (Ioc 0 T) q : ℝ) : ℂ) = ∑ a ∈ boxZ ⌊T⌋₊, c a * ex a q := by
    intro q
    have e1 : ((chat Pc msq (Ioc 0 T) q : ℝ) : ℂ) = (K : ℂ)⁻¹ *
        ∫ τ in Ioc 0 T, (τ : ℂ) * (((Pc.P τ).eval (uhatC msq q) : ℝ) : ℂ) := by
      simp only [chat, Complex.ofReal_mul, Complex.ofReal_inv]
      congr 1
      rw [← integral_complex_ofReal]; congr 1; funext τ; push_cast; ring
    have e2 : ∀ τ ∈ Ioc (0 : ℝ) T, (τ : ℂ) * (((Pc.P τ).eval (uhatC msq q) : ℝ) : ℂ) =
        ∑ a ∈ boxZ ⌊T⌋₊, ((τ : ℂ) * fcoef (fun p => (((Pc.P τ).eval (uhatC msq p) : ℝ) : ℂ)) a) *
          ex a q := by
      intro τ hτ
      rw [TP_fourier (P_TP msq hτ) q, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => by ring
    rw [e1, setIntegral_congr_fun measurableSet_Ioc e2, integral_finsetSum _ fun a _ =>
      (hint a).mul_const _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [c]
    rw [integral_mul_const]; ring
  -- the coefficients are the Fourier coefficients
  have hc : ∀ a ∈ boxZ ⌊T⌋₊, kerT msq T a = c a := by
    intro a ha
    have hf : (fun p => ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ)) =
        ∑ b ∈ boxZ ⌊T⌋₊, c b • ex b := by
      funext q; rw [hexp q, Finset.sum_apply]; rfl
    rw [kerT, hf]
    have key : ∀ (s : Finset (ℤ × ℤ)), fcoef (∑ b ∈ s, c b • ex b) a =
        ∑ b ∈ s, c b * (if b = a then 1 else 0) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp [fcoef]
      | insert b s hb ih =>
        have hcs : Continuous (∑ x ∈ s, c x • ex x) := by
          have e : (∑ x ∈ s, c x • ex x) = fun q => ∑ x ∈ s, c x • ex x q := by
            funext q; simp [Finset.sum_apply]
          rw [e]; exact continuous_finsetSum _ fun i _ => (continuous_ex i).const_smul _
        rw [Finset.sum_insert hb, Finset.sum_insert hb,
          fc_add (f := c b • ex b) (g := ∑ x ∈ s, c x • ex x)
            (by exact (continuous_ex b).const_smul (c b)) hcs a, fc_smul, fc_ex, ih]
    rw [key, Finset.sum_eq_single a]
    · simp
    · intro b _ hb; rw [if_neg hb, mul_zero]
    · intro h; exact absurd ha h
  rw [hexp p]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hc a ha]

theorem fcoef_sum (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (a : ℤ × ℤ) :
    fcoef (∑ b ∈ s, c b • ex b) a = ∑ b ∈ s, c b * (if b = a then 1 else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fcoef]
  | insert b s hb ih =>
    have hcs : Continuous (∑ x ∈ s, c x • ex x) := by
      have e : (∑ x ∈ s, c x • ex x) = fun q => ∑ x ∈ s, c x • ex x q := by
        funext q; simp [Finset.sum_apply]
      rw [e]; exact continuous_finsetSum _ fun i _ => (continuous_ex i).const_smul _
    rw [Finset.sum_insert hb, Finset.sum_insert hb,
      fc_add (f := c b • ex b) (g := ∑ x ∈ s, c x • ex x)
        (by exact (continuous_ex b).const_smul (c b)) hcs a, fc_smul, fc_ex, ih]

theorem chat_fun_eq (hm : 0 ≤ msq) (hT : 0 ≤ T) :
    (fun p => ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ)) = ∑ b ∈ boxZ ⌊T⌋₊, kerT msq T b • ex b := by
  funext q; rw [chat_fourier hm hT q, Finset.sum_apply]; rfl

/-- The kernel has range `⌊T⌋`. -/
theorem kerT_eq_zero (hm : 0 ≤ msq) (hT : 0 ≤ T) {a : ℤ × ℤ} (ha : a ∉ boxZ ⌊T⌋₊) :
    kerT msq T a = 0 := by
  have h : fcoef (fun p => ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ)) a =
      fcoef (∑ b ∈ boxZ ⌊T⌋₊, kerT msq T b • ex b) a := by rw [← chat_fun_eq hm hT]
  rw [fcoef_sum] at h
  rw [kerT, h]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hne : b ≠ a := fun h' => ha (h' ▸ hb)
  rw [if_neg hne, mul_zero]

theorem BZ_neg : Neg.neg ⁻¹' BZ = BZ := by
  ext z; simp [BZ, abs_neg]

theorem setIntegral_BZ_neg (g : ℂ → ℂ) : ∫ q in BZ, g (-q) = ∫ q in BZ, g q := by
  have := (Measure.measurePreserving_neg (volume : Measure ℂ)).setIntegral_preimage_emb
    (measurableEmbedding_neg) g BZ
  rwa [BZ_neg] at this

theorem ex_neg_arg (b : ℤ × ℤ) (q : ℂ) : ex b (-q) = ex (-b) q := by
  simp only [ex, Complex.neg_re, Complex.neg_im, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  congr 2; push_cast; ring

theorem lamC_neg (q : ℂ) : lamC (-q) = lamC q := by simp [lamC]

theorem chat_neg (msq : ℝ) (S : Set ℝ) (q : ℂ) : chat Pc msq S (-q) = chat Pc msq S q := by
  simp [chat, uhatC, lamC_neg]

theorem kerT_neg (a : ℤ × ℤ) : kerT msq T (-a) = kerT msq T a := by
  unfold kerT fcoef
  congr 1
  rw [← setIntegral_BZ_neg]
  refine setIntegral_congr_fun measurableSet_BZ fun q _ => ?_
  simp only [neg_neg, chat_neg, ex_neg_arg]

theorem ex_add_ex_neg (r : ℤ × ℤ) (q : ℂ) :
    ex r q + ex (-r) q = 2 * ((Real.cos (r.1 * q.re + r.2 * q.im) : ℝ) : ℂ) := by
  rw [← ex_neg_arg, ex, ex]
  simp only [Complex.neg_re, Complex.neg_im]
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

theorem continuous_chatC (hm : 0 ≤ msq) (hT : 0 ≤ T) :
    Continuous fun p => ((chat Pc msq (Ioc 0 T) p : ℝ) : ℂ) := by
  rw [chat_fun_eq hm hT]
  have e : (∑ b ∈ boxZ ⌊T⌋₊, kerT msq T b • ex b) = fun q => ∑ b ∈ boxZ ⌊T⌋₊, kerT msq T b • ex b q := by
    funext q; simp [Finset.sum_apply]
  rw [e]; exact continuous_finsetSum _ fun i _ => (continuous_ex i).const_smul _

/-- `ĉ_r = (2π)^{-2} ∫ ĉ_T cos(r·p)`. -/
theorem kerT_eq_cos (hm : 0 ≤ msq) (hT : 0 ≤ T) (r : ℤ × ℤ) :
    kerT msq T r = ((((2 * π) ^ 2)⁻¹ * ∫ q in BZ, chat Pc msq (Ioc 0 T) q *
      Real.cos (r.1 * q.re + r.2 * q.im) : ℝ) : ℂ) := by
  have hc := continuous_chatC hm hT
  have h1 : kerT msq T r = (kerT msq T r + kerT msq T (-r)) / 2 := by
    rw [kerT_neg]; ring
  rw [h1]
  unfold kerT fcoef
  rw [neg_neg, ← mul_add]
  have := integral_add (μ := volume.restrict BZ)
    (f := fun q => ((chat Pc msq (Ioc 0 T) q : ℝ) : ℂ) * ex (-r) q)
    (g := fun q => ((chat Pc msq (Ioc 0 T) q : ℝ) : ℂ) * ex r q)
    (integrableOn_of_continuous (hc.mul (continuous_ex _)))
    (integrableOn_of_continuous (hc.mul (continuous_ex _)))
  rw [← this]
  have e : ∀ q, ((chat Pc msq (Ioc 0 T) q : ℝ) : ℂ) * ex (-r) q +
      ((chat Pc msq (Ioc 0 T) q : ℝ) : ℂ) * ex r q =
      2 * (((chat Pc msq (Ioc 0 T) q * Real.cos (r.1 * q.re + r.2 * q.im) : ℝ)) : ℂ) := by
    intro q
    rw [← mul_add, add_comm (ex (-r) q), ex_add_ex_neg]; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, integral_complex_ofReal]
  push_cast
  ring

end

end Step2.D2
