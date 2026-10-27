module

public import ArborealDecay.TLaw.Defs

/-!
# Positive definiteness (supplement `lem:posdef`) and change of root (`cor:D-tree`(ii))

* `Lmat_posDef`, `Hmat_posDef`: for a connected weighted graph, `𝓛^{(ρ)}_w(t)` and `H^ρ_w(t)`
  are positive definite.
* `det_Lmat_root_eq`: `det 𝓛^{(r)}_w(t) = det 𝓛^{(k)}_w(t)` (cofactor equality).
* `D_root_change`: `D^k_w(t) = D^r_w(t) e^{2 (t_k - t_r)}`.
-/

open Finset Matrix Real

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `∑_{i ≠ ρ} F i = ∑_i F i - F ρ`. -/
theorem sum_ne_eq (ρ : V) (F : V → ℝ) :
    ∑ i : {i // i ≠ ρ}, F i = ∑ i, F i - F ρ := by
  rw [← Finset.add_sum_erase _ _ (mem_univ ρ), add_sub_cancel_left]
  exact (Finset.sum_subtype (univ.erase ρ) (p := fun i => i ≠ ρ) (fun x => by simp) F).symm

theorem sum_ne_eq_of_root (ρ : V) (F : V → ℝ) (hF : F ρ = 0) :
    ∑ i : {i // i ≠ ρ}, F i = ∑ i, F i := by
  rw [sum_ne_eq, hF, sub_zero]

/-- The quadratic form of the grounded Laplacian:
`u ⬝ 𝓛 u = ½ ∑_{i,k ∈ V} c_{ik} (û_i - û_k)²`, `c_{ik} = w_{ik} e^{t_i + t_k}`. -/
theorem dotProduct_Lmat_mulVec {w : V → V → ℝ} (hW : IsWGraph w) (ρ : V) (t : V → ℝ)
    (u : {i // i ≠ ρ} → ℝ) :
    u ⬝ᵥ (Lmat w ρ t *ᵥ u) = (1 / 2) * ∑ i, ∑ k, w i k * exp (t i + t k) *
      (ext ρ u i - ext ρ u k) ^ 2 := by
  set c : V → V → ℝ := fun i k => w i k * exp (t i + t k)
  set x := ext ρ u
  have hc : ∀ i k, c i k = c k i := fun i k => by simp only [c, hW.symm i k, add_comm]
  have hentry : ∀ i k : {i // i ≠ ρ}, Lmat w ρ t i k =
      (if i = k then ∑ m, c i m else 0) - c i k := fun i k => by
    simp only [Lmat, of_apply, c]
    split_ifs with h
    · subst h; rw [hW.diag]; ring
    · ring
  have hlhs : u ⬝ᵥ (Lmat w ρ t *ᵥ u) =
      ∑ i, (∑ m, c i m) * x i ^ 2 - ∑ i, ∑ k, c i k * x i * x k := by
    simp only [dotProduct, mulVec, hentry, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, mem_univ, ↓reduceIte, Finset.mul_sum, mul_sub]
    congr 1
    · rw [← sum_ne_eq_of_root ρ (fun i => (∑ m, c i m) * x i ^ 2) (by simp [x])]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [x, ext_val]; ring
    · rw [← sum_ne_eq_of_root ρ (fun i => ∑ k, c i k * x i * x k) (by simp [x])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sum_ne_eq_of_root ρ (fun k => c i k * x i * x k) (by simp [x])]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [x, ext_val]; ring
  rw [hlhs]
  have hswap : ∑ i, ∑ k, c i k * x k ^ 2 = ∑ i, (∑ m, c i m) * x i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [hc]
  have : ∑ i, ∑ k, c i k * (x i - x k) ^ 2 =
      ∑ i, (∑ m, c i m) * x i ^ 2 + ∑ i, ∑ k, c i k * x k ^ 2 -
        2 * ∑ i, ∑ k, c i k * x i * x k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [c] at this hswap ⊢
  rw [this, hswap]; ring

theorem eq_of_reachable {G : SimpleGraph V} {f : V → ℝ} (hf : ∀ i k, G.Adj i k → f i = f k)
    {u v : V} (h : G.Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

theorem Lmat_isHermitian {w : V → V → ℝ} (hW : IsWGraph w) (ρ : V) (t : V → ℝ) :
    (Lmat w ρ t).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply, star_trivial, Lmat, of_apply]
  split_ifs with h1 h2 h2
  · subst h1; rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [hW.symm, add_comm]

/-- **`lem:posdef`** for `𝓛^{(ρ)}_w(t)`. -/
theorem Lmat_posDef {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) (t : V → ℝ) : (Lmat w ρ t).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨Lmat_isHermitian hW ρ t, fun u hu => ?_⟩
  rw [star_trivial, dotProduct_Lmat_mulVec hW]
  have hnn : ∀ i k, 0 ≤ w i k * exp (t i + t k) * (ext ρ u i - ext ρ u k) ^ 2 := fun i k =>
    mul_nonneg (mul_nonneg (hW.nonneg i k) (exp_pos _).le) (sq_nonneg _)
  refine mul_pos (by norm_num) (lt_of_le_of_ne
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hnn i k) fun h0 => hu ?_)
  have hz : ∀ i k, w i k * exp (t i + t k) * (ext ρ u i - ext ρ u k) ^ 2 = 0 := fun i k => by
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => hnn i k).1 h0.symm i (mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hnn i k).1 h1 k (mem_univ _)
  have hadj : ∀ i k, (supportGraph w).Adj i k → ext ρ u i = ext ρ u k := fun i k h => by
    have hw := ((supportGraph_adj hW.symm).1 h).2
    have := hz i k
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (mul_pos hw (exp_pos _)).ne'
    · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  funext i
  have := eq_of_reachable hadj (hconn (i : V) ρ)
  rw [ext_val, ext_root] at this
  exact this

theorem Hmat_isHermitian {w : V → V → ℝ} (hW : IsWGraph w) (ρ : V) (t : V → ℝ) :
    (Hmat w ρ t).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply, star_trivial, Hmat, of_apply]
  split_ifs with h1 h2 h2
  · subst h1; rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [hW.symm]

/-- **`lem:posdef`** for `H^ρ_w(t) = E_t⁻¹ 𝓛 E_t⁻¹`. -/
theorem Hmat_posDef {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    (ρ : V) (t : V → ℝ) : (Hmat w ρ t).PosDef := by
  have hL := (posDef_iff_dotProduct_mulVec.1 (Lmat_posDef hW hconn ρ t)).2
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨Hmat_isHermitian hW ρ t, fun u hu => ?_⟩
  set e : {i // i ≠ ρ} → ℝ := fun i => exp (-t i)
  have hEu : diagonal e *ᵥ u ≠ 0 := by
    intro h; apply hu; funext i
    have := congr_fun h i
    simp only [mulVec_diagonal, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left (exp_pos _).ne'
  have key : star u ⬝ᵥ (Hmat w ρ t *ᵥ u) =
      star (diagonal e *ᵥ u) ⬝ᵥ (Lmat w ρ t *ᵥ (diagonal e *ᵥ u)) := by
    rw [Hmat_eq, ← mulVec_mulVec, ← mulVec_mulVec, star_trivial, star_trivial, dotProduct_mulVec]
    congr 1
    funext i; simp [vecMul_diagonal, mulVec_diagonal, e, mul_comm]
  rw [key]
  exact hL hEu

open Classical in
/-- **Cofactor equality** (`cor:D-tree`(ii)): `det 𝓛^{(r)}_w(t) = det 𝓛^{(k)}_w(t)`. -/
theorem det_Lmat_root_eq {w : V → V → ℝ} (hW : IsWGraph w) (r k : V) (t : V → ℝ) :
    (Lmat w r t).det = (Lmat w k t).det := by
  have hc : ∀ i k, w i k * exp (t i + t k) = w k i * exp (t k + t i) := fun i k => by
    rw [hW.symm, add_comm]
  rw [Lmat_eq_lap w hW.diag, Lmat_eq_lap w hW.diag, MatrixForest.det_lap_submatrix_ne _ hc,
    MatrixForest.det_lap_submatrix_ne _ hc]

/-- **Change of root** (`cor:D-tree`(ii)): `D^k_w(t) = D^r_w(t) e^{2 (t_k - t_r)}`. -/
theorem D_root_change {w : V → V → ℝ} (hW : IsWGraph w) (r k : V) (t : V → ℝ) :
    D w k t = D w r t * exp (2 * (t k - t r)) := by
  rw [D_eq_det_Lmat, D_eq_det_Lmat, det_Lmat_root_eq hW k r, mul_assoc, ← exp_add,
    sum_ne_eq k t, sum_ne_eq r t]
  congr 2; ring

end ArborealDecay.TLaw
