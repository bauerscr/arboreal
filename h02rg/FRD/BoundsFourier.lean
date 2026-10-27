import FRD.Decomp

/-!
# Derivatives of Fourier multipliers

For a Fourier multiplier `fmat w`, the discrete derivatives act on the characters:
`∇^a e^{ik·x} = e^{ik·x} ∏_e (e^{ik·e} - 1)^{a(e)}`, hence
`|∇^{α_1}_x ∇^{α_2}_y fmat w (x, y)| ≤ |Λ|^{-1} ∑_k |w(k)| λ(k)^{(|α_1| + |α_2|)/2}`.
-/

namespace FRD

noncomputable section

open Finset Complex Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

theorem char_sum (m : Torus d n) {ι : Type*} (s : Finset ι) (f : ι → Torus d n) :
    char m (∑ i ∈ s, f i) = ∏ i ∈ s, char m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [char_zero_right]
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, char_add_right, ih]

theorem char_nsmul (m : Torus d n) (k : ℕ) (v : Torus d n) : char m (k • v) = char m v ^ k := by
  induction k with
  | zero => simp [char_zero_right]
  | succ k ih => rw [succ_nsmul, char_add_right, ih, pow_succ]

theorem char_vadd (m : Torus d n) (b : Dir d → ℕ) (x : Torus d n) :
    char m (b +ᵥ x) = (∏ e, char m (dirVec e) ^ b e) * char m x := by
  rw [vadd_def, char_add_right, char_sum]
  simp only [char_nsmul]

/-- The one-point difference operator `∇^α f(x) = ∑_{b ≤ α} cf α b f(x + b)`. -/
def dop (α : Dir d → ℕ) (f : Torus d n → ℂ) (x : Torus d n) : ℂ :=
  ∑ b ∈ Iic α, cf α b • f (b +ᵥ x)

theorem sum_binom (a : ℕ) (z : ℂ) :
    ∑ k ∈ Iic a, (((-1 : ℝ) ^ (a - k) * (a.choose k : ℝ) : ℝ) : ℂ) * z ^ k = (z - 1) ^ a := by
  rw [sub_eq_add_neg, add_pow]
  have : Iic a = range (a + 1) := by ext k; simp
  rw [this]
  refine sum_congr rfl fun k _ => ?_
  push_cast; ring

theorem dop_char (α : Dir d → ℕ) (m x : Torus d n) :
    dop α (char m) x = char m x * ∏ e, (char m (dirVec e) - 1) ^ α e := by
  unfold dop
  simp only [char_vadd, Complex.real_smul]
  have hIic : Iic α = Fintype.piFinset fun e => Iic (α e) := rfl
  rw [hIic]
  have : ∀ b : Dir d → ℕ, (cf α b : ℂ) * ((∏ e, char m (dirVec e) ^ b e) * char m x) =
      char m x * ∏ e, ((((-1 : ℝ) ^ (α e - b e) * ((α e).choose (b e) : ℝ) : ℝ) : ℂ) *
        char m (dirVec e) ^ b e) := by
    intro b
    rw [cf, Complex.ofReal_prod, prod_mul_distrib]; ring
  simp only [this, ← mul_sum]
  congr 1
  rw [← Finset.prod_univ_sum (fun e => Iic (α e))
    (fun e k => ((((-1 : ℝ) ^ (α e - k) * ((α e).choose k : ℝ) : ℝ) : ℂ) * char m (dirVec e) ^ k))]
  simp only [sum_binom]

theorem norm_char (m x : Torus d n) : ‖char m x‖ = 1 := by
  simp [char, norm_prod]

theorem norm_stdAddChar_sub_one_sq (a : ZMod n) :
    ‖(ZMod.stdAddChar a : ℂ) - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * a.val / n) := by
  rw [← re_stdAddChar, Complex.sq_norm, Complex.normSq_apply]
  have h1 : ‖(ZMod.stdAddChar a : ℂ)‖ = 1 := by simp
  have h2 : (ZMod.stdAddChar a : ℂ).re ^ 2 + (ZMod.stdAddChar a : ℂ).im ^ 2 = 1 := by
    have := Complex.sq_norm (ZMod.stdAddChar a : ℂ)
    rw [h1, Complex.normSq_apply] at this; nlinarith
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [h2]

theorem cosk_term_le (m : Torus d n) (i : Fin d) : 2 - 2 * cosk m i ≤ lam m := by
  unfold lam
  exact single_le_sum (f := fun i => 2 - 2 * cosk m i) (fun j _ => by linarith [cosk_le m j])
    (mem_univ i)

theorem norm_char_dirVec_sub_one (m : Torus d n) (e : Dir d) :
    ‖char m (dirVec e) - 1‖ ≤ Real.sqrt (lam m) := by
  have key : ∀ i, ‖char m (dirVec e) - 1‖ ^ 2 = 2 - 2 * cosk m i → ‖char m (dirVec e) - 1‖ ≤
      Real.sqrt (lam m) := by
    intro i h
    rw [← Real.sqrt_sq (norm_nonneg _), h]
    exact Real.sqrt_le_sqrt (cosk_term_le m i)
  rcases e with i | i
  · refine key i ?_
    rw [dirVec_inl, char_unitT, norm_stdAddChar_sub_one_sq]; rfl
  · refine key i ?_
    rw [dirVec_inr, char_neg_right, char_unitT,
      show conj (ZMod.stdAddChar (co m i) : ℂ) - 1 = conj ((ZMod.stdAddChar (co m i) : ℂ) - 1) by
        simp, Complex.norm_conj, norm_stdAddChar_sub_one_sq]; rfl

theorem norm_dop_char_le (α : Dir d → ℕ) (m x : Torus d n) :
    ‖dop α (char m) x‖ ≤ Real.sqrt (lam m) ^ mabs α := by
  rw [dop_char, norm_mul, norm_char, one_mul, norm_prod, Grassmann.mabs, ← prod_pow_eq_pow_sum]
  refine prod_le_prod (fun e _ => by positivity) fun e _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_char_dirVec_sub_one m e) _

/-- `∇^{α_1}_x ∇^{α_2}_y` of a Fourier multiplier. -/
theorem nabC_fmat (w : Torus d n → ℝ) (α₁ α₂ : Dir d → ℕ) (x y : Torus d n) :
    nabC (fmat w) α₁ α₂ x y =
      ∑ m, (((n : ℝ) ^ d)⁻¹ * w m) * (dop α₁ (char m) x * dop α₂ (char (-m)) y).re := by
  let Φ : MultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℂ := MultilinearMap.mkPiAlgebra ℝ (Fin 2) ℂ
  let v : Torus d n → Fin 2 → Torus d n → ℂ := fun m => ![char m, char (-m)]
  have hf : (fun z : Fin 2 → Torus d n => fmat w (z 0) (z 1)) =
      fun z => ∑ m, (((n : ℝ) ^ d)⁻¹ * w m) • Complex.reLm (Φ fun i => v m i (z i)) := by
    funext z
    simp only [fmat, Φ, v, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.reLm_coe, smul_eq_mul, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [char_sub_right, char_neg_left, mul_assoc]
  rw [nabC, hf, nabla_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [nabla_smul, nabla_comp_linear, nabla_multilinear, smul_eq_mul]
  congr 1
  simp only [Φ, v, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.reLm_coe]
  rfl

/-- `|∇^{α_1}_x ∇^{α_2}_y fmat w (x, y)| ≤ |Λ|^{-1} ∑_k |w(k)| λ(k)^{(|α_1|+|α_2|)/2}`. -/
theorem abs_nabC_fmat_le (w : Torus d n → ℝ) (α₁ α₂ : Dir d → ℕ) (x y : Torus d n) :
    |nabC (fmat w) α₁ α₂ x y| ≤
      ((n : ℝ) ^ d)⁻¹ * ∑ m, |w m| * Real.sqrt (lam m) ^ (mabs α₁ + mabs α₂) := by
  rw [nabC_fmat, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) ^ d)⁻¹), mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, pow_add]
  have h2 := norm_dop_char_le α₂ (-m) y
  rw [lam_neg] at h2
  exact mul_le_mul (norm_dop_char_le α₁ m x) h2 (norm_nonneg _) (by positivity)

end

end FRD
