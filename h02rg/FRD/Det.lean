import FRD.Fourier

/-!
# Positivity and the determinant of `-Δ + m²` on the torus

* `negLap_symm`, `dotProduct_negLap_eq`: `(f, -Δ f) = ½ ∑_x ∑_{e ∈ 𝓔_d} (f(x+e) - f(x))² ≥ 0`.
* `posDef_negLap_add`: `-Δ + m²` is positive definite for `m² > 0`; hence
  `det_negLap_add_pos` (`det(-Δ + m²) > 0`) and `posDef_negLap_add_inv` (`(-Δ+m²)^{-1}` is
  positive definite).
* `det_negLap`: `det(-Δ) = 0` (constants are in the kernel).
* `det_negLap_add_le` (**Det**): for every torus there is `K` with `det(-Δ + m²) ≤ K m²` for
  `0 < m² ≤ 1`.  (`t ↦ det(-Δ + t)` is a polynomial vanishing at `t = 0`.)
-/

namespace FRD

noncomputable section

open Finset Grassmann Matrix

variable {d n : ℕ} [NeZero n]

local notation "T" => Torus d n

theorem sum_dir_shift {M : Type*} [AddCommMonoid M] (f : T → M) (x : T) :
    ∑ e : Dir d, f (x - dirVec e) = ∑ e : Dir d, f (x + dirVec e) := by
  refine Fintype.sum_equiv (Equiv.sumComm _ _) _ _ fun e => ?_
  show f (x - dirVec e) = f (x + dirVec e.swap)
  rw [dirVec_swap, sub_eq_add_neg]

theorem negLap_symm (x y : T) : (negLap : Matrix T T ℝ) x y = negLap y x := by
  simp only [negLap]
  congr 1
  · simp [eq_comm]
  · refine Fintype.sum_equiv (Equiv.sumComm _ _) _ _ fun e => ?_
    show (if y = x + dirVec e then (1 : ℝ) else 0) = if x = y + dirVec e.swap then 1 else 0
    rw [dirVec_swap]
    congr 1
    apply propext
    constructor <;> intro h <;> rw [h] <;> abel

theorem negLap_mulVec (f : T → ℝ) (x : T) :
    (negLap *ᵥ f) x = 2 * d * f x - ∑ e : Dir d, f (x + dirVec e) := by
  simp only [mulVec, dotProduct, negLap, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_mul, mul_assoc]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun e _ => ?_
    simp

/-- `(f, -Δ f) = ½ ∑_x ∑_e (f(x+e) - f(x))²`. -/
theorem dotProduct_negLap_eq (f : T → ℝ) :
    f ⬝ᵥ (negLap *ᵥ f) = (1 / 2) * ∑ x, ∑ e : Dir d, (f (x + dirVec e) - f x) ^ 2 := by
  simp only [dotProduct, negLap_mulVec]
  have hshift : ∀ e : Dir d, ∑ x : T, f (x + dirVec e) ^ 2 = ∑ x : T, f x ^ 2 := fun e =>
    Fintype.sum_equiv (Equiv.addRight (dirVec e)) _ _ fun x => rfl
  have h1 : ∑ x : T, ∑ e : Dir d, (f (x + dirVec e) - f x) ^ 2 =
      ∑ e : Dir d, ∑ x : T, f (x + dirVec e) ^ 2 - 2 * ∑ x : T, f x * ∑ e : Dir d, f (x + dirVec e)
        + ∑ x : T, ∑ e : Dir d, f x ^ 2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun x e => f (x + dirVec e) ^ 2)]
    congr 1; congr 1
    refine sum_congr rfl fun x _ => sum_congr rfl fun e _ => by ring
  rw [h1]
  simp only [hshift, sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum, mul_sub, sum_sub_distrib]
  push_cast
  have : ∀ x : T, f x * (2 * d * f x) = 2 * d * f x ^ 2 := fun x => by ring
  simp only [this, ← Finset.mul_sum]
  ring

theorem dotProduct_negLap_nonneg (f : T → ℝ) : 0 ≤ f ⬝ᵥ (negLap *ᵥ f) := by
  rw [dotProduct_negLap_eq]
  exact mul_nonneg (by norm_num) (sum_nonneg fun x _ => sum_nonneg fun e _ => sq_nonneg _)

/-- `-Δ + m²` is positive definite for `m² > 0`. -/
theorem posDef_negLap_add {msq : ℝ} (hmsq : 0 < msq) :
    (negLap + msq • 1 : Matrix T T ℝ).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun f hf => ?_
  · ext x y
    simp [Matrix.conjTranspose_apply, negLap_symm x y, Matrix.one_apply, eq_comm]
  · simp only [star_trivial, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    have h2 : 0 < f ⬝ᵥ f := by
      obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
      rw [dotProduct]
      exact lt_of_lt_of_le (mul_self_pos.2 hx)
        (single_le_sum (f := fun y => f y * f y) (fun y _ => mul_self_nonneg _) (mem_univ x))
    have := dotProduct_negLap_nonneg f
    nlinarith

theorem det_negLap_add_pos {msq : ℝ} (hmsq : 0 < msq) :
    0 < (negLap + msq • 1 : Matrix T T ℝ).det :=
  (posDef_negLap_add hmsq).det_pos

theorem isUnit_det_negLap_add {msq : ℝ} (hmsq : 0 < msq) :
    IsUnit (negLap + msq • 1 : Matrix T T ℝ).det :=
  (det_negLap_add_pos hmsq).ne'.isUnit

theorem negLap_mulVec_one : (negLap : Matrix T T ℝ) *ᵥ (fun _ => 1) = 0 := by
  funext x
  rw [negLap_mulVec]
  simp [Fintype.card_sum]; ring

/-- `det(-Δ) = 0`. -/
theorem det_negLap : (negLap : Matrix T T ℝ).det = 0 := by
  refine exists_mulVec_eq_zero_iff.1 ⟨fun _ => 1, ?_, negLap_mulVec_one⟩
  intro h
  have := congrFun h 0
  simp at this

theorem det_negLap_add_eq_eval (t : ℝ) :
    (negLap + t • 1 : Matrix T T ℝ).det = (charpoly (-negLap : Matrix T T ℝ)).eval t := by
  rw [eval_charpoly, sub_neg_eq_add, add_comm, smul_one_eq_diagonal]
  rfl

/-- **Det**: `det(-Δ + m²) ≤ K m²` for `0 < m² ≤ 1`, with `K` depending on the torus. -/
theorem det_negLap_add_le : ∃ K : ℝ, ∀ msq : ℝ, 0 < msq → msq ≤ 1 →
    (negLap + msq • 1 : Matrix T T ℝ).det ≤ K * msq := by
  have hp0 : (charpoly (-negLap : Matrix T T ℝ)).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← det_negLap_add_eq_eval, zero_smul, add_zero,
      det_negLap]
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.2 hp0
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (q.continuous (R := ℝ)).continuousOn
  refine ⟨K, fun msq h0 h1 => ?_⟩
  rw [det_negLap_add_eq_eval, hq, Polynomial.eval_mul, Polynomial.eval_X, mul_comm]
  have := hK msq ⟨h0.le, h1⟩
  rw [Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans this) h0.le

end

end FRD
