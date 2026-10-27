import Step2.D2.D2Lattice
import FRD.Lift

/-!
# Torus averages as Brillouin-zone integrals (for `prop:d2`)

For a trigonometric polynomial `f` on `ℝ² = ℂ` with frequencies in `[-k, k]²`, `k < n`, the
torus average `n^{-2} ∑_{m ∈ (ℤ/n)²} f(2πm/n)` equals `(2π)^{-2} ∫_{[-π,π]²} f`
(`avg_eq_integral`). Polynomials in `λ(p)` of degree `k` are trigonometric polynomials of
degree `k` (`TP.lamC_poly`).

Applied to the finite range decomposition (`FRD.Decomp`, `d = 2`): if `n > L^j/2 + |r(x-y)|_∞`,
`C_j(x, y) = (2π)^{-2} ∫_{[-π,π]²} ĉ_j(p) cos(p·r(x-y)) d²p` exactly, where
`ĉ_j(p) = (4+m²)^{-1} ∫_{S_j} t P_t(û(p)) dt` is the `ℤ²` symbol (`Cj_eq_integral_BZ`).
So for `j + 1 < N` the torus averages of `prop:d2` may be replaced by `⨍_{[-π,π]²}` without error.

* `ehat`, `chat_eq_ehat`: `ĉ_{(a,b]} = (ê_b - ê_a)/(λ + m²)` with
  `ê_T(p) = 1 - û(p) ∫_T^∞ t P_t(û(p)) dt` (the symbol of `C_{≤T}` is `ê_T/(λ + m²)`);
* `Cj_succ_diag_sub_log`: combining with `D2Lattice.lattice_C`, for `j ≥ 1`, `L^{j+1}/2 < n`,
  `|C_{j+1}(x,x) - (1/2π) log L| ≤ O(L^{-2j}) + (2π)^{-2} ∫_{[-π,π]²} |ĉ_{j+1} - (E_{j+1} - E_j)/λ|`,
  which isolates the scaling-profile input (R1) in the last term.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real Complex
open scoped Pointwise

/-! ### Exponentials and trigonometric polynomials -/

/-- `e_a(p) = exp(i (a₁ p₁ + a₂ p₂))`. -/
def ex (a : ℤ × ℤ) (p : ℂ) : ℂ := Complex.exp ((((a.1 : ℝ) * p.re + (a.2 : ℝ) * p.im : ℝ)) * I)

theorem ex_add (a b : ℤ × ℤ) (p : ℂ) : ex a p * ex b p = ex (a + b) p := by
  simp only [ex, ← Complex.exp_add, Prod.fst_add, Prod.snd_add]
  congr 1
  push_cast; ring

theorem ex_zero (p : ℂ) : ex 0 p = 1 := by simp [ex]

theorem continuous_ex (a : ℤ × ℤ) : Continuous (ex a) := by unfold ex; fun_prop

/-- Exponentials with frequencies in `[-k, k]²`. -/
def Fr (k : ℕ) : Set (ℂ → ℂ) := {f | ∃ a : ℤ × ℤ, a.1.natAbs ≤ k ∧ a.2.natAbs ≤ k ∧ f = ex a}

/-- Trigonometric polynomials with frequencies in `[-k, k]²`. -/
def TP (k : ℕ) : Submodule ℂ (ℂ → ℂ) := Submodule.span ℂ (Fr k)

theorem Fr_mono {k l : ℕ} (h : k ≤ l) : Fr k ⊆ Fr l := by
  rintro f ⟨a, h1, h2, rfl⟩; exact ⟨a, h1.trans h, h2.trans h, rfl⟩

theorem TP_mono {k l : ℕ} (h : k ≤ l) : TP k ≤ TP l := Submodule.span_mono (Fr_mono h)

theorem Fr_mul (k l : ℕ) : Fr k * Fr l ⊆ Fr (k + l) := by
  rintro f ⟨g, ⟨a, ha1, ha2, rfl⟩, g', ⟨b, hb1, hb2, rfl⟩, rfl⟩
  refine ⟨a + b, ?_, ?_, ?_⟩
  · simp only [Prod.fst_add]; exact (Int.natAbs_add_le _ _).trans (by omega)
  · simp only [Prod.snd_add]; exact (Int.natAbs_add_le _ _).trans (by omega)
  · funext p; exact ex_add a b p

theorem TP.mul {k l : ℕ} {f g : ℂ → ℂ} (hf : f ∈ TP k) (hg : g ∈ TP l) : f * g ∈ TP (k + l) := by
  have := Submodule.mul_mem_mul hf hg
  rw [TP, TP, Submodule.span_mul_span] at this
  exact Submodule.span_mono (Fr_mul k l) this

theorem TP.const (c : ℂ) (k : ℕ) : (fun _ => c) ∈ TP k := by
  have : (fun _ : ℂ => c) = c • ex 0 := by funext p; simp [ex_zero]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, by simp, rfl⟩)

theorem TP.one (k : ℕ) : (1 : ℂ → ℂ) ∈ TP k := TP.const 1 k

theorem TP.pow {k : ℕ} {f : ℂ → ℂ} (hf : f ∈ TP k) (i : ℕ) : f ^ i ∈ TP (i * k) := by
  induction i with
  | zero => simpa using TP.one 0
  | succ i ih =>
    rw [pow_succ, show (i + 1) * k = i * k + k by ring]
    exact TP.mul ih hf

theorem TP.of_ex {a : ℤ × ℤ} {k : ℕ} (h1 : a.1.natAbs ≤ k) (h2 : a.2.natAbs ≤ k) : ex a ∈ TP k :=
  Submodule.subset_span ⟨a, h1, h2, rfl⟩

theorem TP.cos_re : (fun p : ℂ => ((Real.cos p.re : ℝ) : ℂ)) ∈ TP 1 := by
  have : (fun p : ℂ => ((Real.cos p.re : ℝ) : ℂ)) = (1 / 2 : ℂ) • (ex (1, 0) + ex (-1, 0)) := by
    funext p
    simp only [ex, Pi.smul_apply, Pi.add_apply, smul_eq_mul, ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (TP.of_ex (by simp) (by simp))
    (TP.of_ex (by simp) (by simp)))

theorem TP.cos_im : (fun p : ℂ => ((Real.cos p.im : ℝ) : ℂ)) ∈ TP 1 := by
  have : (fun p : ℂ => ((Real.cos p.im : ℝ) : ℂ)) = (1 / 2 : ℂ) • (ex (0, 1) + ex (0, -1)) := by
    funext p
    simp only [ex, Pi.smul_apply, Pi.add_apply, smul_eq_mul, ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (TP.of_ex (by simp) (by simp))
    (TP.of_ex (by simp) (by simp)))

theorem TP.lam : (fun p : ℂ => ((lamC p : ℝ) : ℂ)) ∈ TP 1 := by
  have : (fun p : ℂ => ((lamC p : ℝ) : ℂ)) = (fun _ => (4 : ℂ)) -
      (2 : ℂ) • ((fun p : ℂ => ((Real.cos p.re : ℝ) : ℂ)) + fun p : ℂ => ((Real.cos p.im : ℝ) : ℂ)) := by
    funext p; simp only [Step2.D2.lamC, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast; ring
  rw [this]
  exact Submodule.sub_mem _ (TP.const 4 1)
    (Submodule.smul_mem _ _ (Submodule.add_mem _ TP.cos_re TP.cos_im))

/-- A polynomial of degree `≤ k` in a trigonometric polynomial of degree `1`. -/
theorem TP.poly {u : ℂ → ℝ} (hu : (fun p => ((u p : ℝ) : ℂ)) ∈ TP 1) (g : Polynomial ℝ) {k : ℕ}
    (hk : g.natDegree ≤ k) : (fun p => ((g.eval (u p) : ℝ) : ℂ)) ∈ TP k := by
  have : (fun p => ((g.eval (u p) : ℝ) : ℂ)) = ∑ i ∈ Finset.range (g.natDegree + 1),
      (g.coeff i : ℂ) • (fun p => ((u p : ℝ) : ℂ)) ^ i := by
    funext p
    rw [Polynomial.eval_eq_sum_range, Finset.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [this]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have := TP.pow hu i
  rw [mul_one] at this
  exact TP_mono (by simp at hi; omega) this

/-! ### Averages of exponentials -/

/-- The torus point `2πm/n ∈ [0, 2π)²` of `m ∈ (ℤ/n)²`. -/
def ptT {n : ℕ} (m : Grassmann.Torus 2 n) : ℂ :=
  ⟨2 * π * ((m : Fin 2 → ZMod n) 0).val / n, 2 * π * ((m : Fin 2 → ZMod n) 1).val / n⟩

/-- `e(a, v) = exp(i a (2π v/n))` is the character `v ↦ ψ(a v)` of `ℤ/n`. -/
theorem exp_eq_stdAddChar {n : ℕ} [NeZero n] (a : ℤ) (v : ZMod n) :
    Complex.exp ((((a : ℝ) * (2 * π * v.val / n) : ℝ)) * I) = ZMod.stdAddChar ((a : ZMod n) * v) := by
  have h : ((a * (v.val : ℤ) : ℤ) : ZMod n) = (a : ZMod n) * v := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [← h, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem sum_exp_zmod {n : ℕ} [NeZero n] (a : ℤ) (ha : a.natAbs < n) :
    ∑ v : ZMod n, Complex.exp ((((a : ℝ) * (2 * π * v.val / n) : ℝ)) * I) =
      if a = 0 then (n : ℂ) else 0 := by
  simp only [exp_eq_stdAddChar, FRD.sum_stdAddChar_mul]
  have : (a : ZMod n) = 0 ↔ a = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro hd; exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using ha)
    · rintro rfl; exact dvd_zero _
  by_cases h0 : a = 0
  · rw [if_pos (this.2 h0), if_pos h0]
  · rw [if_neg (mt this.1 h0), if_neg h0]

/-- **Torus average of an exponential.** For `|a_i| < n`, `∑_{m ∈ (ℤ/n)²} e_a(2πm/n) = n² 1_{a=0}`. -/
theorem sum_ex_ptT {n : ℕ} [NeZero n] (a : ℤ × ℤ) (h1 : a.1.natAbs < n) (h2 : a.2.natAbs < n) :
    ∑ m : Grassmann.Torus 2 n, ex a (ptT m) = if a = 0 then (n : ℂ) ^ 2 else 0 := by
  have hf : ∀ m : Grassmann.Torus 2 n, ex a (ptT m) = ∏ i : Fin 2,
      Complex.exp (((((if i = 0 then a.1 else a.2 : ℤ) : ℝ) *
        (2 * π * ((m : Fin 2 → ZMod n) i).val / n) : ℝ)) * I) := by
    intro m
    rw [Fin.prod_univ_two, ← Complex.exp_add]
    simp only [ex, ptT, show (1 : Fin 2) ≠ 0 by decide, if_false]
    congr 1
    push_cast; ring
  simp only [hf]
  have key : ∑ m : Grassmann.Torus 2 n, ∏ i : Fin 2,
      Complex.exp (((((if i = 0 then a.1 else a.2 : ℤ) : ℝ) *
        (2 * π * ((m : Fin 2 → ZMod n) i).val / n) : ℝ)) * I) =
      ∏ i : Fin 2, ∑ v : ZMod n, Complex.exp (((((if i = 0 then a.1 else a.2 : ℤ) : ℝ) *
        (2 * π * v.val / n) : ℝ)) * I) := by
    rw [Finset.prod_univ_sum]; rfl
  rw [key]
  rw [Fin.prod_univ_two]
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, if_true]
  rw [sum_exp_zmod _ h1, sum_exp_zmod _ h2]
  rcases a with ⟨a1, a2⟩
  by_cases e1 : a1 = 0 <;> by_cases e2 : a2 = 0 <;> simp [e1, e2, sq]

/-- `∫_{-π}^{π} e^{iax} dx = 2π 1_{a=0}`. -/
theorem integral_exp_int (a : ℤ) :
    ∫ x in Icc (-π) π, Complex.exp ((((a : ℝ) * x : ℝ)) * I) = if a = 0 then 2 * (π : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  by_cases ha : a = 0
  · subst ha; simp; ring
  · rw [if_neg ha]
    have hc : (a : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ha) I_ne_zero
    have : ∀ x : ℝ, Complex.exp ((((a : ℝ) * x : ℝ)) * I) = Complex.exp ((a * I) * x) := by
      intro x; congr 1; push_cast; ring
    simp only [this]
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp ((a : ℂ) * I * (π : ℝ)) = Complex.exp ((a : ℂ) * I * ((-π : ℝ) : ℝ)) := by
      have h := Complex.exp_int_mul_two_pi_mul_I a
      rw [show (a : ℂ) * I * ((π : ℝ) : ℂ) = (a : ℂ) * I * ((-π : ℝ) : ℂ) + a * (2 * π * I) by
        push_cast; ring, Complex.exp_add, h, mul_one]
    rw [hper, sub_self, zero_div]

theorem BZ_eq_preimage : BZ = Complex.measurableEquivRealProd ⁻¹' (Icc (-π) π ×ˢ Icc (-π) π) := by
  ext z
  simp only [BZ, mem_setOf_eq, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod,
    mem_Icc, abs_le]

/-- `∫_{[-π,π]²} e_a = (2π)² 1_{a=0}`. -/
theorem integral_ex_BZ (a : ℤ × ℤ) :
    ∫ z in BZ, ex a z = if a = 0 then (2 * (π : ℂ)) ^ 2 else 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun q : ℝ × ℝ => Complex.exp ((((a.1 : ℝ) * q.1 : ℝ)) * I) *
      Complex.exp ((((a.2 : ℝ) * q.2 : ℝ)) * I)) (Icc (-π) π ×ˢ Icc (-π) π)
  have he : ∀ z : ℂ, ex a z = Complex.exp ((((a.1 : ℝ) * z.re : ℝ)) * I) *
      Complex.exp ((((a.2 : ℝ) * z.im : ℝ)) * I) := by
    intro z; rw [ex, ← Complex.exp_add]; congr 1; push_cast; ring
  simp only [Complex.measurableEquivRealProd_apply] at h
  rw [BZ_eq_preimage]
  simp only [he]
  have hp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => Complex.exp ((((a.1 : ℝ) * x : ℝ)) * I))
    (fun y : ℝ => Complex.exp ((((a.2 : ℝ) * y : ℝ)) * I)) (Icc (-π) π) (Icc (-π) π)
  rw [h, Measure.volume_eq_prod, hp, integral_exp_int, integral_exp_int]
  rcases a with ⟨a1, a2⟩
  by_cases e1 : a1 = 0 <;> by_cases e2 : a2 = 0 <;> simp [e1, e2, sq]

theorem isCompact_BZ : IsCompact BZ := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨2 * π, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [Complex.norm_le_abs_re_add_abs_im z, hz.1, hz.2]

/-- **Torus average = Brillouin-zone integral** for trigonometric polynomials with frequencies
in `[-k, k]²`, `k < n`: `n^{-2} ∑_{m ∈ (ℤ/n)²} f(2πm/n) = (2π)^{-2} ∫_{[-π,π]²} f`. -/
theorem avg_eq_integral {n k : ℕ} [NeZero n] (hk : k < n) {f : ℂ → ℂ} (hf : f ∈ TP k) :
    ((n : ℂ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, f (ptT m) =
      ((2 * (π : ℂ)) ^ 2)⁻¹ * ∫ z in BZ, f z := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hpi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast pi_ne_zero)
  suffices H : Continuous f ∧ ((n : ℂ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, f (ptT m) =
      ((2 * (π : ℂ)) ^ 2)⁻¹ * ∫ z in BZ, f z from H.2
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, h1, h2, rfl⟩ := hg
    refine ⟨continuous_ex a, ?_⟩
    rw [sum_ex_ptT a (by omega) (by omega), integral_ex_BZ]
    split_ifs
    · field_simp
    · simp
  | zero => exact ⟨continuous_const, by simp⟩
  | add g g' _ _ ih ih' =>
    refine ⟨ih.1.add ih'.1, ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
    rw [integral_add (ih.1.continuousOn.integrableOn_compact isCompact_BZ)
      (ih'.1.continuousOn.integrableOn_compact isCompact_BZ), mul_add, ih.2, ih'.2]
  | smul c g _ ih =>
    refine ⟨ih.1.const_smul c, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [integral_const_mul, mul_left_comm, ih.2]
    ring

/-! ### The finite range decomposition in `d = 2` -/

/-- `û(p) = (λ(p) + m²)/(2·2 + m²)` on `ℝ²`. -/
def uhatC (msq : ℝ) (p : ℂ) : ℝ := (lamC p + msq) / (2 * 2 + msq)

/-- The `ℤ²` symbol of the covariance of the scales `S`:
`ĉ_S(p) = (2·2 + m²)^{-1} ∫_S t P_t(û(p)) dt`. -/
def chat (P : FRD.PtFamily) (msq : ℝ) (S : Set ℝ) (p : ℂ) : ℝ :=
  (2 * 2 + msq)⁻¹ * ∫ t in S, t * (P.P t).eval (uhatC msq p)

theorem continuous_uhatC (msq : ℝ) : Continuous (uhatC msq) :=
  (continuous_lamC.add continuous_const).div_const _

theorem lamC_le_eight (p : ℂ) : lamC p ≤ 8 := by
  unfold lamC; linarith [neg_one_le_cos p.re, neg_one_le_cos p.im]

theorem uhatC_mem {msq : ℝ} (hmsq : 0 ≤ msq) (p : ℂ) : uhatC msq p ∈ Icc (0 : ℝ) 2 := by
  have h0 := lamC_nonneg p
  have h8 := lamC_le_eight p
  refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
  rw [uhatC, div_le_iff₀ (by linarith)]
  linarith

theorem TP.uhat (msq : ℝ) : (fun p => ((uhatC msq p : ℝ) : ℂ)) ∈ TP 1 := by
  have : (fun p => ((uhatC msq p : ℝ) : ℂ)) = ((2 * 2 + msq : ℝ) : ℂ)⁻¹ •
      ((fun p : ℂ => ((lamC p : ℝ) : ℂ)) + fun _ => (msq : ℂ)) := by
    funext p
    simp only [Step2.D2.uhatC, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast; ring
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ TP.lam (TP.const _ 1))

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem lam_eq_lamC (m : Grassmann.Torus 2 n) : FRD.lam m = lamC (ptT m) := by
  simp only [FRD.lam, FRD.cosk, Fin.sum_univ_two, lamC, ptT]

omit [NeZero n] in
theorem uhat_eq_uhatC (msq : ℝ) (m : Grassmann.Torus 2 n) :
    FRD.uhat msq m = uhatC msq (ptT m) := by
  simp only [FRD.uhat, uhatC, lam_eq_lamC]
  norm_num

/-- `e^{ik·z} = e_r(k)` for a lift `r ∈ ℤ²` of `z`. -/
theorem char_eq_ex (m z : Grassmann.Torus 2 n) (r : Fin 2 → ℤ)
    (hr : ∀ i, ((r i : ℤ) : ZMod n) = (z : Fin 2 → ZMod n) i) :
    FRD.char m z = ex (r 0, r 1) (ptT m) := by
  have h : ∀ i, ZMod.stdAddChar (FRD.co m i * FRD.co z i) = Complex.exp
      ((((r i : ℝ) * (2 * π * ((m : Fin 2 → ZMod n) i).val / n) : ℝ)) * I) := by
    intro i
    rw [exp_eq_stdAddChar, hr, mul_comm]
  rw [FRD.char, Fin.prod_univ_two, h, h, ex, ← Complex.exp_add]
  congr 1
  simp only [ptT]
  push_cast; ring

theorem re_ex (a : ℤ × ℤ) (p : ℂ) : (ex a p).re = Real.cos (a.1 * p.re + a.2 * p.im) := by
  rw [ex, Complex.exp_ofReal_mul_I_re]

/-- **Fourier multipliers that are polynomials in `A`.** For a polynomial `g` and a lift `r` of
`z = x - y` with `deg g + |r|_∞ < n`,
`n^{-2} ∑_k g(û(k)) cos(k·z) = (2π)^{-2} ∫_{[-π,π]²} g(û(p)) cos(p·r) d²p`. -/
theorem sum_poly_eq_integral (msq : ℝ) (g : Polynomial ℝ) (z : Grassmann.Torus 2 n)
    (r : Fin 2 → ℤ) (hr : ∀ i, ((r i : ℤ) : ZMod n) = (z : Fin 2 → ZMod n) i)
    (hdeg : g.natDegree + max (r 0).natAbs (r 1).natAbs < n) :
    ((n : ℝ) ^ 2)⁻¹ * ∑ m : Grassmann.Torus 2 n, g.eval (FRD.uhat msq m) * (FRD.char m z).re =
      ((2 * π) ^ 2)⁻¹ * ∫ p in BZ, g.eval (uhatC msq p) *
        Real.cos (r 0 * p.re + r 1 * p.im) := by
  set R := max (r 0).natAbs (r 1).natAbs
  set F : ℂ → ℂ := fun p => ((g.eval (uhatC msq p) : ℝ) : ℂ) * ex (r 0, r 1) p
  have hF : F ∈ TP (g.natDegree + R) :=
    TP.mul (TP.poly (TP.uhat msq) g le_rfl) (TP.of_ex (le_max_left _ _) (le_max_right _ _))
  have hFc : Continuous F :=
    (Complex.continuous_ofReal.comp ((Polynomial.continuous g).comp (continuous_uhatC msq))).mul
      (continuous_ex _)
  have h := congrArg Complex.re (avg_eq_integral hdeg hF)
  have e1 : ((n : ℂ) ^ 2)⁻¹ = ((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have e2 : ((2 * (π : ℂ)) ^ 2)⁻¹ = ((((2 * π) ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hre := integral_re (μ := volume.restrict BZ)
    (hFc.continuousOn.integrableOn_compact (μ := volume) isCompact_BZ)
  simp only [RCLike.re_to_complex] at hre
  rw [e1, e2, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_sum, ← hre] at h
  convert h using 2
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [F, Complex.re_ofReal_mul, uhat_eq_uhatC, char_eq_ex m z r hr]
  · refine setIntegral_congr_fun measurableSet_BZ fun p _ => ?_
    simp only [F, Complex.re_ofReal_mul, re_ex]

/-- **The covariance of bounded scales is a Brillouin-zone integral.** On the torus of side `n`
(`d = 2`), if `r ∈ ℤ²` lifts `x - y` and `b + |r|_∞ < n`, then
`cov_{(a,b]}(x, y) = (2π)^{-2} ∫_{[-π,π]²} ĉ_{(a,b]}(p) cos(p·r) d²p`, with the `ℤ²` symbol
`ĉ_{(a,b]}(p) = (4 + m²)^{-1} ∫_a^b t P_t(û(p)) dt` (no error term). -/
theorem cov_eq_integral_BZ (P : FRD.PtFamily) {msq : ℝ} (hmsq : 0 ≤ msq) {a b : ℝ} (ha : 0 ≤ a)
    (x y : Grassmann.Torus 2 n) (r : Fin 2 → ℤ)
    (hr : ∀ i, ((r i : ℤ) : ZMod n) = ((x - y : Grassmann.Torus 2 n) : Fin 2 → ZMod n) i)
    (hn : b + max (r 0).natAbs (r 1).natAbs < n) :
    FRD.cov P msq (Ioc a b) x y = ((2 * π) ^ 2)⁻¹ * ∫ p in BZ, chat P msq (Ioc a b) p *
        Real.cos (r 0 * p.re + r 1 * p.im) := by
  set S := Ioc a b
  set cs : ℂ → ℝ := fun p => Real.cos (r 0 * p.re + r 1 * p.im)
  set c : Grassmann.Torus 2 n → ℝ := fun m => (FRD.char m (x - y)).re
  have hpi : 0 < π := pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  -- the torus sum, with the `t`-integral outside
  have h1 : FRD.cov P msq S x y = ((n : ℝ) ^ 2)⁻¹ * ((2 * 2 + msq)⁻¹ *
      ∫ t in S, ∑ m : Grassmann.Torus 2 n, t * (P.P t).eval (FRD.uhat msq m) * c m) := by
    rw [integral_finsetSum _ fun m _ =>
      (FRD.integrableOn_Ioc P (FRD.uhat_mem hmsq m) b ha).mul_const _]
    simp only [FRD.cov, FRD.fmat, FRD.wt, integral_mul_const, Finset.mul_sum]
    norm_num
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  -- for each scale `t`, the torus sum is a Brillouin-zone integral
  have h2 : (∫ t in S, ∑ m : Grassmann.Torus 2 n, t * (P.P t).eval (FRD.uhat msq m) * c m) =
      (n : ℝ) ^ 2 * ((2 * π) ^ 2)⁻¹ *
        ∫ t in S, ∫ p in BZ, t * (P.P t).eval (uhatC msq p) * cs p := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    have hdeg : (P.P t).natDegree + max (r 0).natAbs (r 1).natAbs < n := by
      have h := P.natDegree_le t ht0
      have : ((P.P t).natDegree : ℝ) + ((max (r 0).natAbs (r 1).natAbs : ℕ) : ℝ) < n := by
        have := ht.2; linarith
      exact_mod_cast this
    have key := sum_poly_eq_integral msq (P.P t) (x - y) r hr hdeg
    have e1 : ∑ m : Grassmann.Torus 2 n, t * (P.P t).eval (FRD.uhat msq m) * c m =
        t * ∑ m : Grassmann.Torus 2 n, (P.P t).eval (FRD.uhat msq m) * c m := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
    have e2 : (∫ p in BZ, t * (P.P t).eval (uhatC msq p) * cs p) =
        t * ∫ p in BZ, (P.P t).eval (uhatC msq p) * cs p := by
      rw [← integral_const_mul]; congr 1; funext p; ring
    rw [e1, e2]
    have : ∑ m : Grassmann.Torus 2 n, (P.P t).eval (FRD.uhat msq m) * c m =
        (n : ℝ) ^ 2 * (((2 * π) ^ 2)⁻¹ * ∫ p in BZ, (P.P t).eval (uhatC msq p) * cs p) := by
      simp only [c]; rw [← key]; field_simp
    rw [this]; ring
  -- Fubini
  obtain ⟨K0, hK0, hK⟩ := FRD.eval_le_const P
  have hfub : (∫ t in S, ∫ p in BZ, t * (P.P t).eval (uhatC msq p) * cs p) =
      ∫ p in BZ, ∫ t in S, t * (P.P t).eval (uhatC msq p) * cs p := by
    refine integral_integral_swap ?_
    have hmeas : Measurable (Function.uncurry fun t p => t * (P.P t).eval (uhatC msq p) * cs p) := by
      have hu := measurable_uncurry_of_continuous_of_measurable
        (u := fun (p : ℂ) (t : ℝ) => t * (P.P t).eval (uhatC msq p) * cs p)
        (fun t => ((continuous_const.mul ((Polynomial.continuous _).comp
          (continuous_uhatC msq))).mul (by simp only [cs]; fun_prop)))
        (fun p => (measurable_id.mul (P.measurable _)).mul_const _)
      exact hu.comp measurable_swap
    rw [Measure.prod_restrict]
    have hfin : (volume.prod volume) (S ×ˢ BZ) ≠ ⊤ := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp [S]) isCompact_BZ.measure_lt_top.ne
    haveI : IsFiniteMeasure ((volume.prod volume).restrict (S ×ˢ BZ)) :=
      isFiniteMeasure_restrict.2 hfin
    refine Integrable.of_bound hmeas.aestronglyMeasurable (b * K0) ?_
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_BZ) fun q hq => ?_
    obtain ⟨ht, -⟩ := hq
    have ht0 : 0 < q.1 := lt_of_le_of_lt ha ht.1
    have he0 := P.nonneg q.1 ht0 _ (uhatC_mem hmsq q.2)
    have he1 := hK q.1 ht0 _ (uhatC_mem hmsq q.2)
    have hc1 : |cs q.2| ≤ 1 := abs_cos_le_one _
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, abs_of_pos ht0, abs_of_nonneg he0]
    have hb0 : 0 ≤ b := ht0.le.trans ht.2
    have h5 : q.1 * (P.P q.1).eval (uhatC msq q.2) ≤ b * K0 := mul_le_mul ht.2 he1 he0 hb0
    calc q.1 * (P.P q.1).eval (uhatC msq q.2) * |cs q.2|
        ≤ b * K0 * 1 := mul_le_mul h5 hc1 (abs_nonneg _) (mul_nonneg hb0 hK0)
      _ = b * K0 := mul_one _
  rw [h1, h2, hfub]
  have h4 : ∀ p, (∫ t in S, t * (P.P t).eval (uhatC msq p) * cs p) =
      (2 * 2 + msq) * (chat P msq S p * cs p) := by
    intro p
    have hK : (2 * 2 + msq) ≠ 0 := by linarith
    rw [integral_mul_const, chat]
    field_simp
  simp only [h4, integral_const_mul]
  have hK : (2 * 2 + msq) ≠ 0 := by linarith
  field_simp
  rfl

/-- **`C_j` on the torus is the `ℤ²` Brillouin-zone integral.** If `r ∈ ℤ²` lifts `x - y` and
`L^j/2 + |r|_∞ < n` (e.g. `n = L^N`, `j < N`, `|r|_∞ ≤ 1`, `L ≥ 4`), then
`C_j(x, y) = (2π)^{-2} ∫_{[-π,π]²} ĉ_j(p) cos(p·r) d²p` exactly, with
`ĉ_j = chat P m² (lowEnd L j, L^j/2]`. -/
theorem Cj_eq_integral_BZ (P : FRD.PtFamily) {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L) (j : ℕ)
    (x y : Grassmann.Torus 2 n) (r : Fin 2 → ℤ)
    (hr : ∀ i, ((r i : ℤ) : ZMod n) = ((x - y : Grassmann.Torus 2 n) : Fin 2 → ZMod n) i)
    (hn : L ^ j / 2 + max (r 0).natAbs (r 1).natAbs < n) :
    FRD.Cj P msq L j x y = ((2 * π) ^ 2)⁻¹ * ∫ p in BZ,
      chat P msq (Ioc (FRD.lowEnd L j) (L ^ j / 2)) p * Real.cos (r 0 * p.re + r 1 * p.im) :=
  cov_eq_integral_BZ P hmsq (FRD.lowEnd_nonneg hL j) x y r hr hn

/-- `C_j(x, x) = ⨍_{[-π,π]²} ĉ_j` if `L^j/2 < n`. -/
theorem Cj_diag_eq_integral_BZ (P : FRD.PtFamily) {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L)
    (j : ℕ) (x : Grassmann.Torus 2 n) (hn : L ^ j / 2 < n) :
    FRD.Cj P msq L j x x = ((2 * π) ^ 2)⁻¹ * ∫ p in BZ,
      chat P msq (Ioc (FRD.lowEnd L j) (L ^ j / 2)) p := by
  have := Cj_eq_integral_BZ P hmsq hL j x x 0 (fun i => by simp; rfl) (by simpa using hn)
  simpa using this

/-! ### The symbol `ĉ_j` in terms of `ê_T` -/

/-- `ê_T(p) = 1 - û(p) ∫_T^∞ t P_t(û(p)) dt`: the symbol of `C_{≤T}` is `ê_T/(λ + m²)`
(and `ê_0 = 0`, `ê_∞ = 1`). The scaling-profile input (R1) is `ê_{L^j/2}(p) ≈ E(L^j|p|)`. -/
def ehat (P : FRD.PtFamily) (msq T : ℝ) (p : ℂ) : ℝ :=
  1 - uhatC msq p * ∫ t in Ioi T, t * (P.P t).eval (uhatC msq p)

/-- `ĉ_{(a,b]} = (ê_b - ê_a)/(λ + m²)`. -/
theorem chat_eq_ehat (P : FRD.PtFamily) {msq : ℝ} (hmsq : 0 ≤ msq) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) {p : ℂ} (hp : 0 < lamC p + msq) :
    chat P msq (Ioc a b) p = (ehat P msq b p - ehat P msq a p) / (lamC p + msq) := by
  have hK : (0 : ℝ) < 2 * 2 + msq := by linarith
  have hu : uhatC msq p ∈ Ioc (0 : ℝ) 2 := ⟨div_pos hp hK, (uhatC_mem hmsq p).2⟩
  have hsplit : (∫ t in Ioi a, t * (P.P t).eval (uhatC msq p)) =
      (∫ t in Ioc a b, t * (P.P t).eval (uhatC msq p)) +
        ∫ t in Ioi b, t * (P.P t).eval (uhatC msq p) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (FRD.integrableOn_Ioc P (uhatC_mem hmsq p) b ha) (FRD.integrableOn_Ioi P hu (ha.trans hab)),
      Ioc_union_Ioi_eq_Ioi hab]
  rw [chat, ehat, ehat, hsplit]
  have e : uhatC msq p = (lamC p + msq) / (2 * 2 + msq) := rfl
  set I1 := ∫ t in Ioc a b, t * (P.P t).eval (uhatC msq p)
  set I2 := ∫ t in Ioi b, t * (P.P t).eval (uhatC msq p)
  rw [e]
  field_simp
  ring

theorem measurable_chat (P : FRD.PtFamily) (msq : ℝ) (S : Set ℝ) :
    Measurable (chat P msq S) := by
  have hu := measurable_uncurry_of_continuous_of_measurable
    (u := fun (p : ℂ) (t : ℝ) => t * (P.P t).eval (uhatC msq p))
    (fun t => continuous_const.mul ((Polynomial.continuous _).comp (continuous_uhatC msq)))
    (fun p => measurable_id.mul (P.measurable _))
  have := hu.stronglyMeasurable.integral_prod_right (ν := volume.restrict S)
  exact this.measurable.const_mul _

theorem integrableOn_chat (P : FRD.PtFamily) {msq : ℝ} (hmsq : 0 ≤ msq) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : IntegrableOn (chat P msq (Ioc a b)) BZ := by
  obtain ⟨K0, hK0, hK⟩ := FRD.eval_le_const P
  haveI : IsFiniteMeasure (volume.restrict BZ) :=
    isFiniteMeasure_restrict.2 isCompact_BZ.measure_lt_top.ne
  refine Integrable.of_bound (measurable_chat P msq _).aestronglyMeasurable
    (|(2 * 2 + msq)⁻¹| * (b * K0 * (b - a))) (Eventually.of_forall fun p => ?_)
  rw [chat, norm_mul, Real.norm_eq_abs]
  gcongr
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc a b)
    (f := fun t => t * (P.P t).eval (uhatC msq p)) (C := b * K0) (by simp)
    (fun t ht => by
      have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
      have he0 := P.nonneg t ht0 _ (uhatC_mem hmsq p)
      have he1 := hK t ht0 _ (uhatC_mem hmsq p)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht0, abs_of_nonneg he0]
      exact mul_le_mul ht.2 he1 he0 (ht0.le.trans ht.2))
  rwa [Real.volume_real_Ioc_of_le hab] at h

/-- **`C_{j+1}(x, x)` on the torus, conditional on the scaling profile.** For `j ≥ 1`,
`L^{j+1}/2 < n`, and a profile `E` (`0 → 1`) with `DecayProfile E E' K α`, `α > 2`:
`|C_{j+1}(x,x) - (1/2π) log L| ≤ (2π)^{-2} (π⁶/256 + π⁻²) Ia(α) 2K L^{-2j}
  + (2π)^{-2} ∫_{[-π,π]²} |ĉ_{j+1}(p) - (E(L^{j+1}√λ) - E(L^j√λ))/λ| d²p`.
The last term is the scaling-profile error (R1) and the mass error; by `chat_eq_ehat`,
`ĉ_{j+1} = (ê_{L^{j+1}/2} - ê_{L^j/2})/(λ + m²)`. -/
theorem Cj_succ_diag_sub_log {E E' : ℝ → ℝ} {K α : ℝ} (P : FRD.PtFamily) {msq L : ℝ}
    (hmsq : 0 ≤ msq) (hL : 1 ≤ L) {j : ℕ} (hj : 1 ≤ j) (x : Grassmann.Torus 2 n)
    (hn : L ^ (j + 1) / 2 < n) (hE : Profile E 0 1) (hd : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hD : DecayProfile E E' K α) (hα : 2 < α) :
    |FRD.Cj P msq L (j + 1) x x - Real.log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2) * Ia α * (2 * K) / (L ^ j) ^ 2) +
      (2 * π)⁻¹ ^ 2 * ∫ p in BZ, |chat P msq (Ioc (L ^ j / 2) (L ^ (j + 1) / 2)) p -
        (E (L ^ (j + 1) * √(lamC p)) - E (L ^ j * √(lamC p))) / lamC p| := by
  have hL0 : 0 < L := by linarith
  have hc : 0 < L ^ j := by positivity
  set S := Ioc (L ^ j / 2) (L ^ (j + 1) / 2)
  set F := fun z : ℂ => (E (L ^ (j + 1) * √(lamC z)) - E (L ^ j * √(lamC z))) / lamC z
  have hS : Ioc (FRD.lowEnd L (j + 1)) (L ^ (j + 1) / 2) = S := by rw [FRD.lowEnd_succ L hj]
  have hCj := Cj_diag_eq_integral_BZ P hmsq hL0.le (j + 1) x hn
  rw [hS] at hCj
  have hi : IntegrableOn (fun y => (E (L * y) - E y) / y) (Ioi 0) := by
    have := hE.integrableOn one_pos hL
    simpa using this
  have hF : IntegrableOn F BZ := by
    have := lattice_integrableOn (h := fun y => E (L * y) - E y)
      (h' := fun y => L * E' (L * y) - E' y) (fun y hy => hasDerivAt_scale_diff hd hL0 hy)
      (fun y hy => hD.diff (by linarith) hL hy) hi hα hc
    simpa only [pow_succ_mul_eq] using this
  have hch : IntegrableOn (chat P msq S) BZ :=
    integrableOn_chat P hmsq (by positivity)
      (by gcongr; exact Nat.le_succ j)
  have h1 := lattice_C hE hd hD hα hL j
  have hsplit : (∫ p in BZ, chat P msq S p) = (∫ p in BZ, F p) + ∫ p in BZ, (chat P msq S p - F p) := by
    rw [integral_sub hch hF]; ring
  have h2 : |(2 * π)⁻¹ ^ 2 * ∫ p in BZ, (chat P msq S p - F p)| ≤
      (2 * π)⁻¹ ^ 2 * ∫ p in BZ, |chat P msq S p - F p| := by
    rw [abs_mul, abs_of_pos (by have := pi_pos; positivity)]
    gcongr
    exact abs_integral_le_integral_abs
  rw [hCj, ← inv_pow, hsplit, mul_add]
  calc _ = |((2 * π)⁻¹ ^ 2 * (∫ p in BZ, F p) - Real.log L / (2 * π)) +
        (2 * π)⁻¹ ^ 2 * ∫ p in BZ, (chat P msq S p - F p)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

end

end Step2.D2

