import Step2.Lip.FlowLipCx

/-!
# The normalised step on the domain (Lipschitz bounds, part 11)

On the domain the clamps are inactive (`|ẑ + ŷ|, |ŷ| ≤ ρ`), so the coupling vector of `V♭` is
`(0, 0, μ/L^{2j} - ζ/(1+ζ) m², g/(1+n))` (`nVec_dom`) and that of `Δ` is
`(ẑ, ŷ, ζ m², 0)/(1+ζ)` (`nDel_dom`), `ζ = ẑ + ŷ`. Bounds and Lipschitz bounds for the
corresponding coupling polynomials (`d = 2`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

section Vec

variable (R : RGPar 2 L N) (k : ℕ)

theorem nZeta_dom {zh yh : ℂ} (h : ‖zh + yh‖ ≤ R.ρ) : nZeta R zh yh = zh + yh :=
  clampDisk_of_le h

theorem nVec_dom {zh yh : ℂ} (h : ‖zh + yh‖ ≤ R.ρ) (hy : ‖yh‖ ≤ R.ρ) (g μ : ℝ) (w : ℂ) :
    nVec R k zh yh g μ w = ![0, 0, (μ : ℂ) / (L : ℂ) ^ (2 * k) -
      (zh + yh) * (1 + (zh + yh))⁻¹ * R.msq, (g : ℂ) / (1 + nCor (μ : ℂ) w)] := by
  rw [nVec, nZeta_dom R h, clampDisk_of_le hy]
  congr 1
  · ring
  · congr 1; ring

theorem nDel_dom {zh yh : ℂ} (h : ‖zh + yh‖ ≤ R.ρ) (hy : ‖yh‖ ≤ R.ρ) :
    nDel R zh yh = ![zh * (1 + (zh + yh))⁻¹, yh * (1 + (zh + yh))⁻¹,
      (zh + yh) * (1 + (zh + yh))⁻¹ * R.msq, 0] := by
  rw [nDel, nZeta_dom R h, clampDisk_of_le hy]
  congr 1; ring

end Vec

/-! ### Elementary bounds -/

theorem norm_inv_one_add_le {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 8) : ‖(1 + ζ)⁻¹‖ ≤ 8 / 7 := by
  rw [norm_inv]
  have := norm_one_add_ge (ζ := ζ)
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

theorem norm_div_one_add_sub_le {ζ ζ' : ℂ} (h : ‖ζ‖ ≤ 1 / 8) (h' : ‖ζ'‖ ≤ 1 / 8) :
    ‖ζ * (1 + ζ)⁻¹ - ζ' * (1 + ζ')⁻¹‖ ≤ 2 * ‖ζ - ζ'‖ := by
  have h1 : 1 + ζ ≠ 0 := one_add_ne_zero (by linarith)
  have h2 : 1 + ζ' ≠ 0 := one_add_ne_zero (by linarith)
  have e : ζ * (1 + ζ)⁻¹ - ζ' * (1 + ζ')⁻¹ = (ζ - ζ') * ((1 + ζ)⁻¹ * (1 + ζ')⁻¹) := by
    field_simp; ring
  rw [e, norm_mul, norm_mul]
  have a1 := norm_inv_one_add_le h
  have a2 := norm_inv_one_add_le h'
  have : ‖(1 + ζ)⁻¹‖ * ‖(1 + ζ')⁻¹‖ ≤ 2 := by
    have := mul_le_mul a1 a2 (norm_nonneg _) (by norm_num); linarith
  nlinarith [norm_nonneg (ζ - ζ')]

theorem norm_inv_one_add_sub_le {n n' : ℂ} (h : ‖n‖ ≤ 1 / 8) (h' : ‖n'‖ ≤ 1 / 8) :
    ‖(1 + n)⁻¹ - (1 + n')⁻¹‖ ≤ 2 * ‖n - n'‖ := by
  have h1 : 1 + n ≠ 0 := one_add_ne_zero (by linarith)
  have h2 : 1 + n' ≠ 0 := one_add_ne_zero (by linarith)
  have e : (1 + n)⁻¹ - (1 + n')⁻¹ = (n' - n) * ((1 + n)⁻¹ * (1 + n')⁻¹) := by
    field_simp; ring
  rw [e, norm_mul, norm_mul, norm_sub_rev]
  have a1 := norm_inv_one_add_le h
  have a2 := norm_inv_one_add_le h'
  have : ‖(1 + n)⁻¹‖ * ‖(1 + n')⁻¹‖ ≤ 2 := by
    have := mul_le_mul a1 a2 (norm_nonneg _) (by norm_num); linarith
  nlinarith [norm_nonneg (n - n')]

/-! ### The coupling polynomials -/

section Poly

theorem Fnorm_VfamL_sub_le (j : ℕ) (hj : j ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) (v v' : Fin 4 → ℂ) :
    Fnorm j ℓ (VfamL (d := 2) (L := L) (N := N) j v' - VfamL j v) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (((L : ℝ) ^ j) ^ 2 * ‖v' 2 - v 2‖ + ‖v' 0 - v 0‖ +
        ‖v' 1 - v 1‖) + 4 * ℓ ^ 4 * ‖v' 3 - v 3‖) := by
  rw [← map_sub]
  exact Fnorm_VfamL_le j hj hℓ (v' - v)

/-- The norm of `V♭` on the domain. -/
theorem Fnorm_nVec_le (R : RGPar 2 L N) (k : ℕ) (hk : k ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) {zh yh : ℂ}
    (h : ‖zh + yh‖ ≤ R.ρ) (hy : ‖yh‖ ≤ R.ρ) (h8 : ‖zh + yh‖ ≤ 1 / 8)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) (g μ : ℝ) (w : ℂ) :
    Fnorm k ℓ (VfamL (d := 2) (L := L) (N := N) k (nVec R k zh yh g μ w)) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (|μ| + 2 * ‖zh + yh‖) + 5 * ℓ ^ 4 * |g|) := by
  rw [nVec_dom R k h hy]
  refine (Fnorm_VfamL_le k hk hℓ _).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, norm_zero, add_zero]
  have hh : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) k
  have hL2 : ‖(L : ℂ) ^ (2 * k)‖ = ((L : ℝ) ^ k) ^ 2 := by
    rw [norm_pow, Complex.norm_natCast, ← pow_mul, mul_comm]
  have h1 : ((L : ℝ) ^ k) ^ 2 * ‖(μ : ℂ) / (L : ℂ) ^ (2 * k) -
      (zh + yh) * (1 + (zh + yh))⁻¹ * R.msq‖ ≤ |μ| + 2 * ‖zh + yh‖ := by
    refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
    rw [norm_div, hL2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, mul_add, mul_div_cancel₀ _ (by positivity)]
    have a1 := norm_inv_one_add_le h8
    have : ((L : ℝ) ^ k) ^ 2 * (‖zh + yh‖ * ‖(1 + (zh + yh))⁻¹‖ * |R.msq|) ≤ 2 * ‖zh + yh‖ := by
      have e : ((L : ℝ) ^ k) ^ 2 * (‖zh + yh‖ * ‖(1 + (zh + yh))⁻¹‖ * |R.msq|) =
          ‖zh + yh‖ * ‖(1 + (zh + yh))⁻¹‖ * (|R.msq| * ((L : ℝ) ^ k) ^ 2) := by ring
      rw [e]
      have := mul_le_mul a1 hm (by positivity) (by norm_num)
      nlinarith [norm_nonneg (zh + yh), norm_nonneg ((1 + (zh + yh))⁻¹)]
    linarith
  have h2 : ‖(g : ℂ) / (1 + nCor (μ : ℂ) w)‖ ≤ 8 / 7 * |g| := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by linarith [norm_one_add_nCor (μ : ℂ) w])]
    have := norm_one_add_nCor (μ : ℂ) w
    nlinarith [abs_nonneg g]
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ cM * ℓ ^ 2)
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * ℓ ^ 4)
  nlinarith [abs_nonneg g, pow_pos hℓ 4]

/-- The norm of `Δ` on the domain. -/
theorem Fnorm_nDel_le (R : RGPar 2 L N) (k : ℕ) (hk : k ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) {zh yh : ℂ}
    (h : ‖zh + yh‖ ≤ R.ρ) (hy : ‖yh‖ ≤ R.ρ) (h8 : ‖zh + yh‖ ≤ 1 / 8)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    Fnorm k ℓ (VfamL (d := 2) (L := L) (N := N) k (nDel R zh yh)) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (2 * ‖zh + yh‖ + 2 * ‖zh‖ + 2 * ‖yh‖)) := by
  rw [nDel_dom R h hy]
  refine (Fnorm_VfamL_le k hk hℓ _).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, norm_zero, mul_zero, add_zero]
  have a1 := norm_inv_one_add_le h8
  have h1 : ((L : ℝ) ^ k) ^ 2 * ‖(zh + yh) * (1 + (zh + yh))⁻¹ * R.msq‖ ≤ 2 * ‖zh + yh‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e : ((L : ℝ) ^ k) ^ 2 * (‖zh + yh‖ * ‖(1 + (zh + yh))⁻¹‖ * |R.msq|) =
        ‖zh + yh‖ * ‖(1 + (zh + yh))⁻¹‖ * (|R.msq| * ((L : ℝ) ^ k) ^ 2) := by ring
    rw [e]
    have := mul_le_mul a1 hm (by positivity) (by norm_num)
    nlinarith [norm_nonneg (zh + yh), norm_nonneg ((1 + (zh + yh))⁻¹)]
  have h2 : ‖zh * (1 + (zh + yh))⁻¹‖ ≤ 2 * ‖zh‖ := by
    rw [norm_mul]; nlinarith [norm_nonneg zh]
  have h3 : ‖yh * (1 + (zh + yh))⁻¹‖ ≤ 2 * ‖yh‖ := by
    rw [norm_mul]; nlinarith [norm_nonneg yh]
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The difference of `V♭`** on the domain. -/
theorem Fnorm_nVec_sub_le (R : RGPar 2 L N) (k : ℕ) (hk : k ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {zh yh zh' yh' : ℂ} (h : ‖zh + yh‖ ≤ R.ρ) (hy : ‖yh‖ ≤ R.ρ) (h' : ‖zh' + yh'‖ ≤ R.ρ)
    (hy' : ‖yh'‖ ≤ R.ρ) (h8 : ‖zh + yh‖ ≤ 1 / 8) (h8' : ‖zh' + yh'‖ ≤ 1 / 8)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) (g μ g' μ' : ℝ) (w w' : ℂ) (hg' : |g'| ≤ 1) :
    Fnorm k ℓ (VfamL (d := 2) (L := L) (N := N) k (nVec R k zh' yh' g' μ' w') -
        VfamL k (nVec R k zh yh g μ w)) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (|μ' - μ| + 2 * ‖(zh' + yh') - (zh + yh)‖) +
        4 * ℓ ^ 4 * (8 / 7 * |g' - g| + 2 * ‖nCor (μ' : ℂ) w' - nCor (μ : ℂ) w‖)) := by
  refine (Fnorm_VfamL_sub_le k hk hℓ _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [nVec_dom R k h hy, nVec_dom R k h' hy']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, sub_self, norm_zero, add_zero]
  have hh : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) k
  have hL2 : ‖(L : ℂ) ^ (2 * k)‖ = ((L : ℝ) ^ k) ^ 2 := by
    rw [norm_pow, Complex.norm_natCast, ← pow_mul, mul_comm]
  have h1 : ((L : ℝ) ^ k) ^ 2 * ‖(μ' : ℂ) / (L : ℂ) ^ (2 * k) - (zh' + yh') * (1 + (zh' + yh'))⁻¹ *
      R.msq - ((μ : ℂ) / (L : ℂ) ^ (2 * k) - (zh + yh) * (1 + (zh + yh))⁻¹ * R.msq)‖ ≤
      |μ' - μ| + 2 * ‖(zh' + yh') - (zh + yh)‖ := by
    have e : (μ' : ℂ) / (L : ℂ) ^ (2 * k) - (zh' + yh') * (1 + (zh' + yh'))⁻¹ * R.msq -
        ((μ : ℂ) / (L : ℂ) ^ (2 * k) - (zh + yh) * (1 + (zh + yh))⁻¹ * R.msq) =
        ((μ' - μ : ℝ) : ℂ) / (L : ℂ) ^ (2 * k) - ((zh' + yh') * (1 + (zh' + yh'))⁻¹ -
          (zh + yh) * (1 + (zh + yh))⁻¹) * R.msq := by push_cast; ring
    rw [e]
    refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
    rw [norm_div, hL2, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, mul_add, mul_div_cancel₀ _ (by positivity)]
    have a1 := norm_div_one_add_sub_le h8' h8
    have e2 : ((L : ℝ) ^ k) ^ 2 * (‖(zh' + yh') * (1 + (zh' + yh'))⁻¹ -
        (zh + yh) * (1 + (zh + yh))⁻¹‖ * |R.msq|) = ‖(zh' + yh') * (1 + (zh' + yh'))⁻¹ -
        (zh + yh) * (1 + (zh + yh))⁻¹‖ * (|R.msq| * ((L : ℝ) ^ k) ^ 2) := by ring
    rw [e2]
    have := mul_le_mul a1 hm (by positivity) (by positivity)
    linarith
  have h2 : ‖(g' : ℂ) / (1 + nCor (μ' : ℂ) w') - (g : ℂ) / (1 + nCor (μ : ℂ) w)‖ ≤
      8 / 7 * |g' - g| + 2 * ‖nCor (μ' : ℂ) w' - nCor (μ : ℂ) w‖ := by
    have e : (g' : ℂ) / (1 + nCor (μ' : ℂ) w') - (g : ℂ) / (1 + nCor (μ : ℂ) w) =
        ((g' - g : ℝ) : ℂ) * (1 + nCor (μ : ℂ) w)⁻¹ +
          (g' : ℂ) * ((1 + nCor (μ' : ℂ) w')⁻¹ - (1 + nCor (μ : ℂ) w)⁻¹) := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have a1 := norm_inv_one_add_le (norm_nCor_le (μ : ℂ) w)
    have a2 := norm_inv_one_add_sub_le (norm_nCor_le (μ' : ℂ) w') (norm_nCor_le (μ : ℂ) w)
    have := mul_le_mul_of_nonneg_left a1 (abs_nonneg (g' - g))
    have := mul_le_mul hg' a2 (norm_nonneg _) zero_le_one
    nlinarith [abs_nonneg (g' - g)]
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ cM * ℓ ^ 2)
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * ℓ ^ 4)
  linarith

/-- **The difference of `Δ`** on the domain. -/
theorem Fnorm_nDel_sub_le (R : RGPar 2 L N) (k : ℕ) (hk : k ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {zh yh zh' yh' : ℂ} (h : ‖zh + yh‖ ≤ R.ρ) (hy : ‖yh‖ ≤ R.ρ) (h' : ‖zh' + yh'‖ ≤ R.ρ)
    (hy' : ‖yh'‖ ≤ R.ρ) (h8 : ‖zh + yh‖ ≤ 1 / 8) (h8' : ‖zh' + yh'‖ ≤ 1 / 8)
    (hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1) (hz1 : ‖zh‖ ≤ 1) (hy1 : ‖yh‖ ≤ 1) :
    Fnorm k ℓ (VfamL (d := 2) (L := L) (N := N) k (nDel R zh' yh') -
        VfamL k (nDel R zh yh)) ≤
      ENNReal.ofReal (cM * ℓ ^ 2 * (6 * ‖(zh' + yh') - (zh + yh)‖ + 2 * ‖zh' - zh‖ +
        2 * ‖yh' - yh‖)) := by
  refine (Fnorm_VfamL_sub_le k hk hℓ _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [nDel_dom R h hy, nDel_dom R h' hy']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, sub_self, norm_zero, mul_zero, add_zero]
  have a2 := norm_div_one_add_sub_le h8' h8
  have hinv : ‖(1 + (zh' + yh'))⁻¹ - (1 + (zh + yh))⁻¹‖ ≤ 2 * ‖(zh' + yh') - (zh + yh)‖ :=
    norm_inv_one_add_sub_le h8' h8
  have hi' := norm_inv_one_add_le h8'
  have h1 : ((L : ℝ) ^ k) ^ 2 * ‖(zh' + yh') * (1 + (zh' + yh'))⁻¹ * R.msq -
      (zh + yh) * (1 + (zh + yh))⁻¹ * R.msq‖ ≤ 2 * ‖(zh' + yh') - (zh + yh)‖ := by
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ((L : ℝ) ^ k) ^ 2 * (‖(zh' + yh') * (1 + (zh' + yh'))⁻¹ -
        (zh + yh) * (1 + (zh + yh))⁻¹‖ * |R.msq|) = ‖(zh' + yh') * (1 + (zh' + yh'))⁻¹ -
        (zh + yh) * (1 + (zh + yh))⁻¹‖ * (|R.msq| * ((L : ℝ) ^ k) ^ 2) := by ring
    rw [e2]
    have := mul_le_mul a2 hm (by positivity) (by positivity)
    linarith
  have hprod : ∀ a a' : ℂ, ‖a‖ ≤ 1 → ‖a' * (1 + (zh' + yh'))⁻¹ - a * (1 + (zh + yh))⁻¹‖ ≤
      2 * ‖a' - a‖ + 2 * ‖(zh' + yh') - (zh + yh)‖ := fun a a' ha => by
    have e : a' * (1 + (zh' + yh'))⁻¹ - a * (1 + (zh + yh))⁻¹ =
        (a' - a) * (1 + (zh' + yh'))⁻¹ + a * ((1 + (zh' + yh'))⁻¹ - (1 + (zh + yh))⁻¹) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := mul_le_mul ha hinv (norm_nonneg _) zero_le_one
    nlinarith [norm_nonneg (a' - a)]
  have h2 := hprod zh zh' hz1
  have h3 := hprod yh yh' hy1
  have hM : 0 ≤ cM := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end Poly

end

end Step2
