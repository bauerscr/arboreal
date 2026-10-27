import Mathlib

namespace Grassmann

open Matrix

/-- A real square matrix all of whose rows have unit Euclidean length has `|det| ≤ 1`. -/
lemma abs_det_le_one_of_unit_rows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, ∑ j, B i j ^ 2 = 1) : |B.det| ≤ 1 := by
  set P : Matrix (Fin n) (Fin n) ℝ := B * Bᵀ with hPdef
  have hP : P.PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose B
  have hdet : P.det = B.det ^ 2 := by
    rw [hPdef, det_mul, det_transpose, sq]
  have htr : P.trace = n := by
    simp only [hPdef, trace, diag, mul_apply, transpose_apply]
    simp [← sq, hB]
  have hdetE : P.det = ∏ i, hP.1.eigenvalues i := by
    simpa using hP.1.det_eq_prod_eigenvalues
  have htrE : P.trace = ∑ i, hP.1.eigenvalues i := by
    simpa using hP.1.trace_eq_sum_eigenvalues
  have hle : ∏ i, hP.1.eigenvalues i ≤ ∏ i, Real.exp (hP.1.eigenvalues i - 1) := by
    apply Finset.prod_le_prod (fun i _ => hP.eigenvalues_nonneg i)
    intro i _
    have := Real.add_one_le_exp (hP.1.eigenvalues i - 1)
    linarith
  rw [← Real.exp_sum, Finset.sum_sub_distrib, ← htrE, htr] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    sub_self, Real.exp_zero] at hle
  have : B.det ^ 2 ≤ 1 := by rw [← hdet, hdetE]; exact hle
  exact (sq_le_one_iff_abs_le_one _).1 this

/-- Hadamard's inequality for a real square matrix: |det A| ≤ ∏ᵢ ‖row i‖₂. -/
theorem abs_det_le_prod_norm_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, Real.sqrt (∑ j, A i j ^ 2) := by
  by_cases h : ∃ i, ∑ j, A i j ^ 2 = 0
  · obtain ⟨i, hi⟩ := h
    have hz : ∀ j, A i j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).1 hi j
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    rw [det_eq_zero_of_row_eq_zero i hz, abs_zero]
    exact Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  · push Not at h
    set r : Fin n → ℝ := fun i => Real.sqrt (∑ j, A i j ^ 2) with hr
    have hpos : ∀ i, 0 < r i := fun i =>
      Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg _) (h i).symm)
    set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => A i j / r i with hBdef
    have hAB : A = diagonal r * B := by
      ext i j
      simp only [hBdef, diagonal_mul, of_apply]
      field_simp [(hpos i).ne']
    have hB : ∀ i, ∑ j, B i j ^ 2 = 1 := by
      intro i
      simp only [hBdef, of_apply, div_pow, ← Finset.sum_div]
      rw [hr]
      simp only
      rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _), div_self (h i)]
    rw [hAB, det_mul, det_diagonal, abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun i _ => (hpos i).le)]
    calc (∏ i, r i) * |B.det| ≤ (∏ i, r i) * 1 :=
          mul_le_mul_of_nonneg_left (abs_det_le_one_of_unit_rows B hB)
            (Finset.prod_nonneg fun i _ => (hpos i).le)
      _ = ∏ i, r i := mul_one _

/-- Gram–Hadamard: for vectors in a real inner product space. -/
theorem abs_det_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (f g : Fin n → E) :
    |(Matrix.of fun i j => inner ℝ (f i) (g j)).det| ≤ ∏ i, ‖f i‖ * ‖g i‖ := by
  classical
  have hnn : 0 ≤ ∏ i, ‖f i‖ * ‖g i‖ :=
    Finset.prod_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  by_cases hli : LinearIndependent ℝ f
  · set W := Submodule.span ℝ (Set.range f) with hWdef
    haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
    have hW : Module.finrank ℝ W = n := by
      rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
    let q : OrthonormalBasis (Fin n) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
    let v : Fin n → E := fun k => (q k : E)
    have hv : Orthonormal ℝ v := q.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hexp : ∀ i j, inner ℝ (f i) (g j) = ∑ k, inner ℝ (f i) (v k) * inner ℝ (v k) (g j) := by
      intro i j
      let x : W := ⟨f i, Submodule.subset_span ⟨i, rfl⟩⟩
      have h1 : ∑ k, inner ℝ (q k) x • q k = x := q.sum_repr' x
      have h2 : ∑ k, inner ℝ (v k) (f i) • v k = f i := by
        have := congrArg (fun y : W => (y : E)) h1
        simpa [v, x, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] using this
      conv_lhs => rw [← h2]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_left, real_inner_comm (f i) (v k)]
    set X : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i k => inner ℝ (f i) (v k) with hX
    set Y : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => inner ℝ (v k) (g j) with hY
    have hM : (Matrix.of fun i j => inner ℝ (f i) (g j)) = X * Y := by
      ext i j
      simp [hX, hY, mul_apply, hexp]
    have hXle : |X.det| ≤ ∏ i, ‖f i‖ := by
      refine (abs_det_le_prod_norm_rows X).trans (Finset.prod_le_prod
        (fun i _ => Real.sqrt_nonneg _) fun i _ => ?_)
      have hb := hv.sum_inner_products_le (s := Finset.univ) (f i)
      simp only [Real.norm_eq_abs, sq_abs] at hb
      have : ∑ k, X i k ^ 2 ≤ ‖f i‖ ^ 2 := by
        simpa [hX, real_inner_comm] using hb
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq (norm_nonneg _))
    have hYle : |Y.det| ≤ ∏ i, ‖g i‖ := by
      rw [← det_transpose]
      refine (abs_det_le_prod_norm_rows Yᵀ).trans (Finset.prod_le_prod
        (fun i _ => Real.sqrt_nonneg _) fun i _ => ?_)
      have hb := hv.sum_inner_products_le (s := Finset.univ) (g i)
      simp only [Real.norm_eq_abs, sq_abs] at hb
      have : ∑ k, Yᵀ i k ^ 2 ≤ ‖g i‖ ^ 2 := by
        simpa [hY] using hb
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq (norm_nonneg _))
    rw [hM, det_mul, abs_mul, Finset.prod_mul_distrib]
    exact mul_le_mul hXle hYle (abs_nonneg _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  · obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
    have hdet : (Matrix.of fun i j => inner ℝ (f i) (g j)).det = 0 := by
      refine exists_vecMul_eq_zero_iff.1 ⟨c, fun h => hi (by simp [h]), ?_⟩
      ext j
      have : inner ℝ (∑ i, c i • f i) (g j) = 0 := by rw [hc, inner_zero_left]
      rw [sum_inner] at this
      simpa [vecMul, dotProduct, real_inner_smul_left] using this
    rw [hdet, abs_zero]
    exact hnn

open scoped MatrixOrder in
/-- Gram–Hadamard for a positive semidefinite real matrix `C`. -/
theorem abs_det_psd_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℝ}
    (hC : C.PosSemidef) {n : ℕ} (b a : Fin n → Λ → ℝ) :
    |(Matrix.of fun i j => b i ⬝ᵥ (C *ᵥ a j)).det| ≤
      ∏ i, Real.sqrt (b i ⬝ᵥ (C *ᵥ b i)) * Real.sqrt (a i ⬝ᵥ (C *ᵥ a i)) := by
  obtain ⟨D, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  have key : ∀ x y : Λ → ℝ, x ⬝ᵥ ((star D * D) *ᵥ y) =
      inner ℝ (WithLp.toLp 2 (D *ᵥ x) : EuclideanSpace ℝ Λ) (WithLp.toLp 2 (D *ᵥ y)) := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [← mulVec_mulVec, dotProduct_mulVec, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, vecMul_transpose, dotProduct_comm]
    simp
  have hnorm : ∀ x : Λ → ℝ, Real.sqrt (x ⬝ᵥ ((star D * D) *ᵥ x)) =
      ‖(WithLp.toLp 2 (D *ᵥ x) : EuclideanSpace ℝ Λ)‖ := by
    intro x
    rw [key, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  convert abs_det_inner_le (fun i => (WithLp.toLp 2 (D *ᵥ b i) : EuclideanSpace ℝ Λ))
    (fun i => (WithLp.toLp 2 (D *ᵥ a i) : EuclideanSpace ℝ Λ)) using 3
  · ext i j
    exact key _ _
  · exact hnorm _
  · exact hnorm _

end Grassmann
