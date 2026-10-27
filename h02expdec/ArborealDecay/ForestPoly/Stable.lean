module

public import ArborealDecay.ForestPoly.Operator
public import ArborealDecay.Stability.Operator
public import ArborealDecay.Stability.Hermitian
public import ArborealDecay.H02.Ghost

/-!
# Real stability of the forest polynomial (`lem:PG-stable`)

Following the supplement (lem:DG, prop:Tij, thm:PG-stable):

* `detPoly_isRealStable`: `D_G = det (L_β + diag (1 + h))` is real stable, since for `Im h > 0`
  and `v ≠ 0`, `Im (v* (L_β + diag (1 + h)) v) = ∑ᵢ Im hᵢ |vᵢ|² > 0` (`L_β` is real symmetric).
* `D_G` is multi-affine (`detPoly_isMultiAffine`), and each edge operator `1 - β_ij ∂ᵢ ∂ⱼ`
  (`β_ij ≥ 0`) preserves "multi-affine and real stable or zero"
  (`IsRealStableOrZero.sub_smul_pderiv_pderiv`).
* By `operator_identity`, `P_G` is obtained from `D_G` by these operators, and `P_G ≠ 0` since
  `P_G(0) = [1]_{β,0} > 0`.
-/

@[expose] public section

namespace ArborealDecay.ForestPoly

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Finset ArborealDecay.Stability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lap_symm (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (i j : V) :
    MatrixForest.lap β i j = MatrixForest.lap β j i := by
  by_cases h : i = j
  · rw [h]
  · rw [MatrixForest.lap_apply_of_ne β h, MatrixForest.lap_apply_of_ne β (Ne.symm h), hβ]

/-- For a real symmetric matrix `L`, the Hermitian form `v* L v` is real. -/
theorem im_quadForm_of_symm (L : Matrix V V ℝ) (hL : ∀ i j, L i j = L j i) (v : V → ℂ) :
    (star v ⬝ᵥ (L.map ((↑) : ℝ → ℂ)).mulVec v).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Matrix.map_apply, Complex.conj_ofReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hL]; ring

/-- `D_G(z) ≠ 0` whenever all `Im zᵢ > 0` (supplement lem:DG, step stable). -/
theorem aeval_detPoly_ne_zero (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (z : V → ℂ)
    (hz : ∀ i, 0 < (z i).im) : aeval z (detPoly β) ≠ 0 := by
  rw [detPoly, AlgHom.map_det]
  have hM : (aeval z).mapMatrix ((MatrixForest.lap β).map MvPolynomial.C +
      Matrix.diagonal fun i => 1 + X i) =
      (MatrixForest.lap β).map ((↑) : ℝ → ℂ) + Matrix.diagonal fun i => 1 + z i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hM]
  apply det_ne_zero_of_im_quadForm_pos
  intro v hv
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_im,
    im_quadForm_of_symm _ (lap_symm β hβ), zero_add]
  have hterm : ∀ i, (star v i * ((1 + z i) * v i)).im = Complex.normSq (v i) * (z i).im := by
    intro i
    rw [show star v i * ((1 + z i) * v i) = (1 + z i) * (star (v i) * v i) by
      rw [Pi.star_apply]; ring, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.mul_im]
    ring
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.im_sum, hterm]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  refine Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _) (hz j).le)
    ⟨i, Finset.mem_univ _, mul_pos (Complex.normSq_pos.2 hi) (hz i)⟩

/-- `D_G` is real stable (supplement lem:DG). -/
theorem detPoly_isRealStable (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) :
    IsRealStable (detPoly β) :=
  (isRealStable_iff_aeval _).2 fun z hz => aeval_detPoly_ne_zero β hβ z hz

/-- Each edge operator preserves "multi-affine and real stable or zero" (supplement
prop:Tij; diagonal pairs act trivially on multi-affine polynomials). -/
theorem edgeOp_preserves (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (e : Sym2 V) {p : MvPolynomial V ℝ} (hp : IsMultiAffine p) (hs : IsRealStableOrZero p) :
    IsRealStableOrZero (edgeOp β hβ e p) ∧ IsMultiAffine (edgeOp β hβ e p) := by
  induction e using Sym2.ind with
  | h i j =>
  have happ : edgeOp β hβ s(i, j) p = p - β i j • pderiv i (pderiv j p) := by simp [edgeOp_mk]
  rw [happ]
  by_cases hij : i = j
  · subst hij
    have h0 : pderiv i (pderiv i p) = 0 :=
      pderiv_eq_zero_of_notMem_vars (by
        rw [mem_vars_iff_degreeOf_ne_zero]
        simpa using degreeOf_pderiv_self_of_le_one (hp i))
    rw [h0, smul_zero, sub_zero]
    exact ⟨hs, hp⟩
  · exact IsRealStableOrZero.sub_smul_pderiv_pderiv hp hs hij (hβ0 i j)

theorem noncommProd_edgeOp_preserves (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (s : Finset (Sym2 V)) :
    IsRealStableOrZero (s.noncommProd (edgeOp β hβ) (edgeOp_pairwise β hβ s) (detPoly β)) ∧
      IsMultiAffine (s.noncommProd (edgeOp β hβ) (edgeOp_pairwise β hβ s) (detPoly β)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.noncommProd_empty]
    exact ⟨Or.inr (detPoly_isRealStable β hβ), detPoly_isMultiAffine β⟩
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    exact edgeOp_preserves β hβ hβ0 a ih.2 ih.1

theorem forestPolynomial_ne_zero (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) : forestPolynomial β hβ ≠ 0 := by
  intro h0
  have h1 := eval_forestPolynomial β hβ 0
  rw [h0, map_zero] at h1
  have h2 := H02.expect_one_pos hβ hβ0 (h := 0) (fun _ => le_rfl)
  linarith

/-- `P_G` is multi-affine. -/
theorem forestPolynomial_isMultiAffine (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) : IsMultiAffine (forestPolynomial β hβ) := by
  rw [operator_identity]
  exact (noncommProd_edgeOp_preserves β hβ hβ0 _).2

/-- **Lemma `lem:PG-stable`**: the forest polynomial `P_G` is real stable. -/
theorem forestPolynomial_isRealStable (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) :
    ∀ z : V → ℂ, (∀ j, 0 < (z j).im) → MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0 := by
  have key := (noncommProd_edgeOp_preserves β hβ hβ0 (⊤ : SimpleGraph V).edgeFinset).1
  change IsRealStableOrZero (edgeOpProd β hβ (detPoly β)) at key
  rw [← operator_identity] at key
  rcases key with h | h
  · exact absurd h (forestPolynomial_ne_zero β hβ hβ0)
  · exact (isRealStable_iff_aeval _).1 h

end

end ArborealDecay.ForestPoly

end
