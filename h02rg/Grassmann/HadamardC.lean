import Mathlib

/-!
# Hadamard and Gram–Hadamard inequalities over `ℝ` or `ℂ`

`Grassmann.Hadamard` proves these for real matrices and real inner product spaces. Here they
are proved for any `RCLike` field `𝕜`:
* `norm_det_le_prod_norm_rows`: `‖det A‖ ≤ ∏_i (∑_j ‖A_{ij}‖²)^{1/2}`;
* `norm_det_inner_le`: `‖det (⟪f_i, g_j⟫)‖ ≤ ∏_i ‖f_i‖ ‖g_i‖` in an inner product space over `𝕜`.
The second applies to a covariance with a Gram representation `C_{xy} = ⟪F_x, G_y⟫`, which
need not be positive semidefinite (`F ≠ G`).
-/

namespace Grassmann

open Matrix
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

lemma norm_det_le_one_of_unit_rows {n : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜)
    (hB : ∀ i, ∑ j, ‖B i j‖ ^ 2 = 1) : ‖B.det‖ ≤ 1 := by
  set P : Matrix (Fin n) (Fin n) 𝕜 := B * Bᴴ with hPdef
  have hP : P.PosSemidef := posSemidef_self_mul_conjTranspose B
  have hdet : P.det = ((‖B.det‖ ^ 2 : ℝ) : 𝕜) := by
    rw [hPdef, det_mul, det_conjTranspose, RCLike.star_def, RCLike.mul_conj]; push_cast; rfl
  have htr : P.trace = (n : 𝕜) := by
    have e : P.trace = ∑ i, ∑ j, B i j * (starRingEnd 𝕜) (B i j) := by
      simp only [hPdef, trace, diag, mul_apply, conjTranspose_apply, RCLike.star_def]
    rw [e]
    have : ∀ i, ∑ j, B i j * (starRingEnd 𝕜) (B i j) = (1 : 𝕜) := fun i => by
      have := congrArg (fun r : ℝ => (r : 𝕜)) (hB i)
      simp only [RCLike.ofReal_sum, RCLike.ofReal_pow, RCLike.ofReal_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [RCLike.mul_conj]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hdetE : P.det = ∏ i, ((hP.1.eigenvalues i : ℝ) : 𝕜) := hP.1.det_eq_prod_eigenvalues
  have htrE : P.trace = ∑ i, ((hP.1.eigenvalues i : ℝ) : 𝕜) := hP.1.trace_eq_sum_eigenvalues
  have hdetR : ‖B.det‖ ^ 2 = ∏ i, hP.1.eigenvalues i := by
    have := hdet.symm.trans hdetE
    rw [← RCLike.ofReal_prod] at this
    exact_mod_cast this
  have htrR : ∑ i, hP.1.eigenvalues i = n := by
    have := htrE.symm.trans htr
    rw [← RCLike.ofReal_sum] at this
    exact_mod_cast this
  have hle : ∏ i, hP.1.eigenvalues i ≤ ∏ i, Real.exp (hP.1.eigenvalues i - 1) := by
    apply Finset.prod_le_prod (fun i _ => hP.eigenvalues_nonneg i)
    intro i _
    have := Real.add_one_le_exp (hP.1.eigenvalues i - 1)
    linarith
  rw [← Real.exp_sum, Finset.sum_sub_distrib, htrR] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    sub_self, Real.exp_zero] at hle
  have : ‖B.det‖ ^ 2 ≤ 1 := by rw [hdetR]; exact hle
  nlinarith [norm_nonneg B.det]

/-- Hadamard's inequality over `𝕜`: `‖det A‖ ≤ ∏_i ‖row i‖₂`. -/
theorem norm_det_le_prod_norm_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  by_cases h : ∃ i, ∑ j, ‖A i j‖ ^ 2 = 0
  · obtain ⟨i, hi⟩ := h
    have hz : ∀ j, A i j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A i j‖)).1 hi j
        (Finset.mem_univ _)
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    rw [det_eq_zero_of_row_eq_zero i hz, norm_zero]
    exact Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  · push Not at h
    set r : Fin n → ℝ := fun i => Real.sqrt (∑ j, ‖A i j‖ ^ 2) with hr
    have hpos : ∀ i, 0 < r i := fun i =>
      Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg _) (h i).symm)
    set B : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i j => A i j / (r i : 𝕜) with hBdef
    have hr0 : ∀ i, (r i : 𝕜) ≠ 0 := fun i => by exact_mod_cast (hpos i).ne'
    have hAB : A = diagonal (fun i => (r i : 𝕜)) * B := by
      ext i j
      simp only [hBdef, diagonal_mul, of_apply]
      field_simp [hr0 i]
    have hB : ∀ i, ∑ j, ‖B i j‖ ^ 2 = 1 := by
      intro i
      simp only [hBdef, of_apply, norm_div, RCLike.norm_ofReal, abs_of_pos (hpos i), div_pow,
        ← Finset.sum_div]
      rw [hr]
      simp only
      rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _), div_self (h i)]
    rw [hAB, det_mul, det_diagonal, norm_mul, norm_prod]
    simp only [RCLike.norm_ofReal, abs_of_pos (hpos _)]
    calc (∏ i, r i) * ‖B.det‖ ≤ (∏ i, r i) * 1 :=
          mul_le_mul_of_nonneg_left (norm_det_le_one_of_unit_rows B hB)
            (Finset.prod_nonneg fun i _ => (hpos i).le)
      _ = ∏ i, r i := mul_one _

/-- Gram–Hadamard over `𝕜`: `‖det (⟪f_i, g_j⟫)‖ ≤ ∏_i ‖f_i‖ ‖g_i‖`. -/
theorem norm_det_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {n : ℕ} (f g : Fin n → E) :
    ‖(Matrix.of fun i j => inner 𝕜 (f i) (g j)).det‖ ≤ ∏ i, ‖f i‖ * ‖g i‖ := by
  classical
  have hnn : 0 ≤ ∏ i, ‖f i‖ * ‖g i‖ :=
    Finset.prod_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  by_cases hli : LinearIndependent 𝕜 f
  · set W := Submodule.span 𝕜 (Set.range f) with hWdef
    haveI : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range f)
    have hW : Module.finrank 𝕜 W = n := by
      rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
    let q : OrthonormalBasis (Fin n) 𝕜 W := (stdOrthonormalBasis 𝕜 W).reindex (finCongr hW)
    let v : Fin n → E := fun k => (q k : E)
    have hv : Orthonormal 𝕜 v := q.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hexp : ∀ i j, inner 𝕜 (f i) (g j) = ∑ k, inner 𝕜 (f i) (v k) * inner 𝕜 (v k) (g j) := by
      intro i j
      let x : W := ⟨f i, Submodule.subset_span ⟨i, rfl⟩⟩
      have h1 : ∑ k, inner 𝕜 (q k) x • q k = x := q.sum_repr' x
      have h2 : ∑ k, inner 𝕜 (v k) (f i) • v k = f i := by
        have := congrArg (fun y : W => (y : E)) h1
        simpa [v, x, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] using this
      conv_lhs => rw [← h2]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_smul_left, inner_conj_symm]
    set X : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i k => inner 𝕜 (f i) (v k) with hX
    set Y : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun k j => inner 𝕜 (v k) (g j) with hY
    have hM : (Matrix.of fun i j => inner 𝕜 (f i) (g j)) = X * Y := by
      ext i j
      simp [hX, hY, mul_apply, hexp]
    have hXle : ‖X.det‖ ≤ ∏ i, ‖f i‖ := by
      refine (norm_det_le_prod_norm_rows X).trans (Finset.prod_le_prod
        (fun i _ => Real.sqrt_nonneg _) fun i _ => ?_)
      have hb := hv.sum_inner_products_le (s := Finset.univ) (f i)
      have : ∑ k, ‖X i k‖ ^ 2 ≤ ‖f i‖ ^ 2 := by
        refine le_trans (le_of_eq ?_) hb
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hX, of_apply]; rw [norm_inner_symm]
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq (norm_nonneg _))
    have hYle : ‖Y.det‖ ≤ ∏ i, ‖g i‖ := by
      rw [← det_transpose]
      refine (norm_det_le_prod_norm_rows Yᵀ).trans (Finset.prod_le_prod
        (fun i _ => Real.sqrt_nonneg _) fun i _ => ?_)
      have hb := hv.sum_inner_products_le (s := Finset.univ) (g i)
      have : ∑ k, ‖Yᵀ i k‖ ^ 2 ≤ ‖g i‖ ^ 2 := by
        simpa [hY] using hb
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq (norm_nonneg _))
    rw [hM, det_mul, norm_mul, Finset.prod_mul_distrib]
    exact mul_le_mul hXle hYle (norm_nonneg _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  · obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
    have hdet : (Matrix.of fun i j => inner 𝕜 (f i) (g j)).det = 0 := by
      refine exists_vecMul_eq_zero_iff.1 ⟨star c, fun h => hi (by
        have := congrFun h i
        simpa using this), ?_⟩
      ext j
      have : inner 𝕜 (∑ i, c i • f i) (g j) = 0 := by rw [hc, inner_zero_left]
      rw [sum_inner] at this
      simpa [vecMul, dotProduct, inner_smul_left, mul_comm] using this
    rw [hdet, norm_zero]
    exact hnn

end Grassmann
