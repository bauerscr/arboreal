import Grassmann.Torus

/-!
# Fourier analysis on the torus `Λ = (ℤ/nℤ)^d`

* `char m x = e^{i k·x}` with `k = 2π m / n` (`m` in the dual torus, identified with `Λ`);
* `lam m = λ(k) = ∑_j (2 - 2 cos k_j) = 4 ∑_j sin^2(k_j/2)`;
* `negLap` is `-Δ`, with `-Δ e^{ik·x} = λ(k) e^{ik·x}` (`negLap_mulVec_char`);
* `fmat w` is the Fourier multiplier `(x, y) ↦ |Λ|^{-1} ∑_k w(k) e^{ik·(x-y)}` (real part);
  for even `w` these matrices multiply as their symbols (`fmat_mul`), `fmat 1 = 1`,
  `-Δ = fmat λ`, and polynomials of `fmat w` are `fmat (p ∘ w)` (`aeval_fmat`);
  `fmat w` is positive semidefinite for `w ≥ 0` (`fmat_posSemidef`).
-/

namespace FRD

noncomputable section

open Finset Complex Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- Coordinates of a torus point. -/
abbrev co (x : Torus d n) : Fin d → ZMod n := x

/-- The character `x ↦ e^{i k·x}`, `k = 2π m/n`. -/
def char (m x : Torus d n) : ℂ := ∏ i, ZMod.stdAddChar (co m i * co x i)

theorem co_add (x y : Torus d n) : co (x + y) = co x + co y := rfl
theorem co_neg (x : Torus d n) : co (-x) = -co x := rfl
theorem co_sub (x y : Torus d n) : co (x - y) = co x - co y := rfl
theorem co_zero : co (0 : Torus d n) = 0 := rfl

theorem char_add_right (m x y : Torus d n) : char m (x + y) = char m x * char m y := by
  simp only [char, co_add, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]

theorem char_comm (m x : Torus d n) : char m x = char x m := by
  simp only [char, mul_comm]

theorem char_add_left (m m' x : Torus d n) : char (m + m') x = char m x * char m' x := by
  rw [char_comm, char_add_right, char_comm x, char_comm x]

theorem char_zero_right (m : Torus d n) : char m 0 = 1 := by
  simp [char, co_zero]

theorem char_zero_left (x : Torus d n) : char 0 x = 1 := by
  rw [char_comm, char_zero_right]

theorem stdAddChar_neg (a : ZMod n) : ZMod.stdAddChar (-a) = conj (ZMod.stdAddChar a) := by
  have h1 : ZMod.stdAddChar a * ZMod.stdAddChar (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : ZMod.stdAddChar a * conj (ZMod.stdAddChar a) = 1 := by
    rw [Complex.mul_conj, ZMod.stdAddChar_apply, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    simp
  have h0 : ZMod.stdAddChar a ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ h0 (h1.trans h2.symm)

theorem char_neg_right (m x : Torus d n) : char m (-x) = conj (char m x) := by
  simp only [char, co_neg, Pi.neg_apply, mul_neg, stdAddChar_neg, map_prod]

theorem char_neg_left (m x : Torus d n) : char (-m) x = conj (char m x) := by
  rw [char_comm, char_neg_right, char_comm]

theorem char_sub_right (m x y : Torus d n) : char m (x - y) = char m x * conj (char m y) := by
  rw [sub_eq_add_neg, char_add_right, char_neg_right]

theorem sum_stdAddChar_mul (a : ZMod n) :
    ∑ b : ZMod n, ZMod.stdAddChar (a * b) = if a = 0 then (n : ℂ) else 0 := by
  have := AddChar.sum_mulShift (R := ZMod n) (ψ := ZMod.stdAddChar) a
    (ZMod.isPrimitive_stdAddChar n)
  simpa [AddChar.mulShift_apply, ZMod.card, mul_comm] using this

/-- Orthogonality of characters. -/
theorem sum_char (m : Torus d n) :
    ∑ x : Torus d n, char m x = if m = 0 then (n : ℂ) ^ d else 0 := by
  have : ∑ x : Torus d n, char m x = ∏ i : Fin d, ∑ b : ZMod n, ZMod.stdAddChar (co m i * b) := by
    rw [Finset.prod_univ_sum]; rfl
  rw [this]
  simp only [sum_stdAddChar_mul]
  by_cases hm : m = 0
  · subst hm; simp [co_zero]
  · rw [if_neg hm]
    obtain ⟨i, hi⟩ : ∃ i, co m i ≠ 0 := by
      by_contra h; push Not at h; exact hm (funext h)
    exact prod_eq_zero (mem_univ i) (by simp [hi])

theorem sum_char_left (x : Torus d n) :
    ∑ m : Torus d n, char m x = if x = 0 then (n : ℂ) ^ d else 0 := by
  simp_rw [char_comm _ x]; exact sum_char x

theorem card_torus : Fintype.card (Torus d n) = n ^ d := by
  show Fintype.card (Fin d → ZMod n) = n ^ d
  simp

/-! ### The Laplacian -/

/-- `cos k_i`, `k = 2π m / n`. -/
def cosk (m : Torus d n) (i : Fin d) : ℝ := Real.cos (2 * Real.pi * (co m i).val / n)

/-- `λ(k) = ∑_j (2 - 2 cos k_j)`, `k = 2π m / n`. -/
def lam (m : Torus d n) : ℝ := ∑ i, (2 - 2 * cosk m i)

/-- `-Δ`: `(-Δ f)(x) = ∑_{e ∈ 𝓔_d} (f(x) - f(x + e))`. -/
def negLap : Matrix (Torus d n) (Torus d n) ℝ := fun x y =>
  (2 * d : ℝ) * (if x = y then 1 else 0) - ∑ e : Dir d, if y = x + dirVec e then 1 else 0

/-- The unit vector `e_i` of the torus. -/
def unitT (i : Fin d) : Torus d n := (Pi.single i 1 : Fin d → ZMod n)

theorem dirVec_inl (i : Fin d) : (dirVec (Sum.inl i) : Torus d n) = unitT i := rfl
theorem dirVec_inr (i : Fin d) : (dirVec (Sum.inr i) : Torus d n) = -unitT i := rfl

theorem char_unitT (m : Torus d n) (i : Fin d) :
    char m (unitT i) = ZMod.stdAddChar (co m i) := by
  rw [char, Finset.prod_eq_single i]
  · simp [unitT, co]
  · intro j _ hj; simp [co, unitT, hj]
  · simp

theorem re_stdAddChar (a : ZMod n) :
    (ZMod.stdAddChar a).re = Real.cos (2 * Real.pi * a.val / n) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [show (2 * ↑Real.pi * I * ↑a.val / ↑n : ℂ) = ((2 * Real.pi * a.val / n : ℝ) : ℂ) * I by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]

theorem sum_char_dirVec (m : Torus d n) :
    ∑ e : Dir d, char m (dirVec e) = ∑ i, (2 * cosk m i : ℂ) := by
  rw [Fintype.sum_sum_type]
  simp only [dirVec_inl, dirVec_inr]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [char_neg_right, char_unitT, Complex.add_conj, re_stdAddChar, cosk]
  push_cast; ring

/-- `-Δ e^{ik·x} = λ(k) e^{ik·x}`. -/
theorem negLap_mulVec_char (m x : Torus d n) :
    ∑ y, (negLap x y : ℂ) * char m y = lam m * char m x := by
  have h1 : ∀ y, (negLap x y : ℂ) * char m y =
      (2 * d : ℂ) * (if x = y then char m y else 0) -
        ∑ e : Dir d, (if y = x + dirVec e then char m y else 0) := by
    intro y
    simp only [negLap]
    push_cast
    rw [sub_mul, Finset.sum_mul (s := Finset.univ)]
    congr 1
    · rw [mul_assoc]; congr 1; split_ifs <;> simp
    · refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs <;> simp
  simp only [h1, sum_sub_distrib, ← mul_sum, sum_ite_eq, mem_univ, if_true]
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, if_true, char_add_right, ← mul_sum, sum_char_dirVec]
  simp only [lam, ofReal_sum, ofReal_sub, ofReal_mul, ofReal_ofNat]
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [← Finset.mul_sum]
  ring

/-! ### Fourier multipliers -/

/-- An even symbol: `w(-k) = w(k)`. -/
def Even' (w : Torus d n → ℝ) : Prop := ∀ m, w (-m) = w m

theorem lam_neg (m : Torus d n) : lam (-m) = lam m := by
  simp only [lam]
  refine sum_congr rfl fun i _ => ?_
  congr 2
  by_cases h : co m i = 0
  · simp [cosk, co_neg, h]
  · simp only [cosk, co_neg, Pi.neg_apply]
    rw [ZMod.neg_val, if_neg h, Nat.cast_sub (ZMod.val_lt _).le]
    rw [show 2 * Real.pi * ((n : ℝ) - (co m i).val) / n =
      2 * Real.pi - 2 * Real.pi * (co m i).val / n by
        have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
        field_simp]
    rw [Real.cos_two_pi_sub]

theorem lam_even : Even' (lam : Torus d n → ℝ) := lam_neg

/-- The matrix with symbol `w`: `|Λ|^{-1} ∑_k w(k) cos(k·(x - y))`. -/
def fmat (w : Torus d n → ℝ) : Matrix (Torus d n) (Torus d n) ℝ := fun x y =>
  ((n : ℝ) ^ d)⁻¹ * ∑ m, w m * (char m (x - y)).re

/-- For even `w`, the sum `∑_k w(k) e^{ik·z}` is real. -/
theorem sum_char_real {w : Torus d n → ℝ} (hw : Even' w) (z : Torus d n) :
    ((∑ m, w m * (char m z).re : ℝ) : ℂ) = ∑ m, (w m : ℂ) * char m z := by
  set S := ∑ m, (w m : ℂ) * char m z
  have hS : conj S = S := by
    simp only [S, map_sum, map_mul, conj_ofReal, ← char_neg_left]
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun m => by simp [hw m]
  have hre : ((S.re : ℝ) : ℂ) = S := Complex.conj_eq_iff_re.1 hS
  rw [← hre]
  congr 1
  simp [S, Complex.re_sum, Complex.mul_re]

theorem fmat_complex {w : Torus d n → ℝ} (hw : Even' w) (x y : Torus d n) :
    (fmat w x y : ℂ) = ((n : ℂ) ^ d)⁻¹ * ∑ m, (w m : ℂ) * char m (x - y) := by
  have := sum_char_real hw (x - y)
  rw [fmat, ofReal_mul, this]
  push_cast; rfl

theorem even_const (c : ℝ) : Even' (fun _ : Torus d n => c) := fun _ => rfl

theorem fmat_one : fmat (fun _ => (1 : ℝ)) = (1 : Matrix (Torus d n) (Torus d n) ℝ) := by
  ext x y
  apply Complex.ofReal_injective
  rw [fmat_complex (even_const 1)]
  simp only [ofReal_one, one_mul, sum_char_left, sub_eq_zero, Matrix.one_apply]
  split_ifs <;> simp [NeZero.ne]

theorem fmat_mul {w w' : Torus d n → ℝ} (hw : Even' w) (hw' : Even' w') :
    fmat w * fmat w' = fmat (fun m => w m * w' m) := by
  ext x y
  apply Complex.ofReal_injective
  rw [fmat_complex (fun m => by simp [hw m, hw' m]), Matrix.mul_apply]
  push_cast
  simp only [fmat_complex hw, fmat_complex hw']
  set c : ℂ := ((n : ℂ) ^ d)⁻¹
  have hc : (n : ℂ) ^ d * c = 1 := mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n)))
  have key : ∀ m m' : Torus d n,
      ∑ z, char m (x - z) * char m' (z - y) = if m' = m then (n : ℂ) ^ d * char m (x - y) else 0 := by
    intro m m'
    have : ∀ z, char m (x - z) * char m' (z - y) =
        char m x * conj (char m' y) * char (m' - m) z := by
      intro z
      rw [char_sub_right, char_sub_right, sub_eq_add_neg, char_add_left, char_neg_left]
      ring
    simp only [this, ← mul_sum, sum_char, sub_eq_zero]
    by_cases h : m' = m
    · subst h; rw [if_pos rfl, if_pos rfl, char_sub_right]; ring
    · rw [if_neg h, if_neg h, mul_zero]
  have e1 : ∀ z, (c * ∑ m, (w m : ℂ) * char m (x - z)) * (c * ∑ m', (w' m' : ℂ) * char m' (z - y)) =
      ∑ m, ∑ m', c * c * ((w m : ℂ) * (w' m' : ℂ)) * (char m (x - z) * char m' (z - y)) := by
    intro z
    rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun m' _ => by ring
  rw [sum_congr rfl fun z _ => e1 z, sum_comm]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm]
  simp only [← Finset.mul_sum, key, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  calc c * c * ((w m : ℂ) * (w' m : ℂ)) * ((n : ℂ) ^ d * char m (x - y))
      = c * ((n : ℂ) ^ d * c) * ((w m : ℂ) * (w' m : ℂ) * char m (x - y)) := by ring
    _ = _ := by rw [hc, mul_one]

theorem negLap_eq_fmat : (negLap : Matrix (Torus d n) (Torus d n) ℝ) = fmat lam := by
  ext x y
  apply Complex.ofReal_injective
  rw [fmat_complex lam_even]
  set c : ℂ := ((n : ℂ) ^ d)⁻¹
  have hc : (n : ℂ) ^ d * c = 1 := mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n)))
  have e1 : ∀ m, (lam m : ℂ) * char m (x - y) =
      ∑ z, (negLap x z : ℂ) * (char m z * conj (char m y)) := by
    intro m
    rw [char_sub_right, ← mul_assoc, ← negLap_mulVec_char, Finset.sum_mul]
    refine sum_congr rfl fun z _ => by ring
  simp only [e1, Finset.mul_sum]
  rw [sum_comm]
  have e2 : ∀ z, ∑ m, c * ((negLap x z : ℂ) * (char m z * conj (char m y))) =
      (negLap x z : ℂ) * (c * ∑ m, char m (z - y)) := by
    intro z
    rw [Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun m _ => by rw [char_sub_right]; ring
  simp only [e2, sum_char_left, sub_eq_zero, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [mul_comm c, hc, mul_one]

theorem fmat_add (w w' : Torus d n → ℝ) : fmat w + fmat w' = fmat (fun m => w m + w' m) := by
  ext x y; simp [fmat, add_mul, sum_add_distrib, mul_add]

theorem fmat_smul (c : ℝ) (w : Torus d n → ℝ) : c • fmat w = fmat (fun m => c * w m) := by
  ext x y; simp [fmat, mul_sum]; refine sum_congr rfl fun m _ => by ring

theorem fmat_const (c : ℝ) : fmat (fun _ => c) = c • (1 : Matrix (Torus d n) (Torus d n) ℝ) := by
  rw [show (fun _ : Torus d n => c) = fun m => c * 1 by simp, ← fmat_smul, fmat_one]

/-- Polynomials of Fourier multipliers: `p(fmat w) = fmat (p ∘ w)`. -/
theorem aeval_fmat {w : Torus d n → ℝ} (hw : Even' w) (p : Polynomial ℝ) :
    Polynomial.aeval (fmat w) p = fmat (fun m => p.eval (w m)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, fmat_add]
  | monomial k a =>
    have hpow : ∀ k : ℕ, fmat w ^ k = fmat (fun m => w m ^ k) := by
      intro k
      induction k with
      | zero => simp [fmat_one]
      | succ k ih =>
        rw [pow_succ, ih, fmat_mul (fun m => by simp [hw m]) hw]
        simp only [pow_succ]
    simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial, hpow]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, fmat_smul]

theorem fmat_symm (w : Torus d n → ℝ) (x y : Torus d n) : fmat w x y = fmat w y x := by
  simp only [fmat]
  congr 2; funext m
  rw [show y - x = -(x - y) by abel, char_neg_right, Complex.conj_re]

theorem re_char_sub (m x y : Torus d n) :
    (char m (x - y)).re = (char m x).re * (char m y).re + (char m x).im * (char m y).im := by
  rw [char_sub_right, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-- `fmat w` is positive semidefinite for even `w ≥ 0`. -/
theorem fmat_posSemidef {w : Torus d n → ℝ} (hw0 : ∀ m, 0 ≤ w m) :
    (fmat w).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
  · ext x y; exact fmat_symm w y x
  · simp only [star_trivial, dotProduct, Matrix.mulVec, fmat, re_char_sub]
    set c : ℝ := ((n : ℝ) ^ d)⁻¹
    have key : ∑ x, v x * ∑ y, c * (∑ m, w m * ((char m x).re * (char m y).re +
        (char m x).im * (char m y).im)) * v y =
        c * ∑ m, w m * ((∑ x, v x * (char m x).re) ^ 2 + (∑ x, v x * (char m x).im) ^ 2) := by
      calc ∑ x, v x * ∑ y, c * (∑ m, w m * ((char m x).re * (char m y).re +
            (char m x).im * (char m y).im)) * v y
          = ∑ x, ∑ y, ∑ m, c * w m * (v x * (char m x).re * (v y * (char m y).re) +
              v x * (char m x).im * (v y * (char m y).im)) := by
            refine sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            refine sum_congr rfl fun y _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
            refine sum_congr rfl fun m _ => by ring
        _ = ∑ m, ∑ x, ∑ y, c * w m * (v x * (char m x).re * (v y * (char m y).re) +
              v x * (char m x).im * (v y * (char m y).im)) := by
            rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
            exact Finset.sum_comm
        _ = _ := by
            rw [Finset.mul_sum]
            refine sum_congr rfl fun m _ => ?_
            rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
              Finset.mul_sum, Finset.mul_sum]
            refine sum_congr rfl fun x _ => ?_
            rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            refine sum_congr rfl fun y _ => by ring
    rw [key]
    exact mul_nonneg (by positivity) (sum_nonneg fun m _ => mul_nonneg (hw0 m) (by positivity))

end

end FRD
