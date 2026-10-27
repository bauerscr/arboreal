import DressedFRD.StdLocBound

/-!
# Fourier moments of rapidly decaying symbols

`avg_pnorm_pow_le`: if `0 ≤ ŵ ≤ B` and `ŵ(p) (R|p|_σ)^{2r} ≤ B'` for `|p|_σ > R^{-1}`, then
`⨍ |p|_σ^a ŵ(p) dp ≤ (B + B' c_{d,2r-a}) R^{-(a+d)}`, provided `2r - a > d` and `n ≥ 7R`.

This is the lattice sum used for (S4) of the decomposition of `FRD` (`DressedFRD.Instance`).
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann

variable {d n : ℕ} [NeZero n]

/-- The constant `5^d (1 - 2^{d-b})^{-1} 4^{-b} (2π)^{b-d}` of `sum_pnorm_rpow_tail`. -/
def tailC (d : ℕ) (b : ℝ) : ℝ :=
  5 ^ d * (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹ * (4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d)

theorem tailC_nonneg {b : ℝ} (hb : (d : ℝ) < b) : 0 ≤ tailC d b := by
  have : 0 < 1 - (2 : ℝ) ^ ((d : ℝ) - b) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith :
      (d : ℝ) - b < 0)
    linarith
  unfold tailC
  have := inv_pos.2 this
  positivity

/-- `tailC d b ≤ 2 · 5^d (π/2)^b` for `b ≥ d + 1`. -/
theorem tailC_le {b : ℝ} (hb : (d : ℝ) + 1 ≤ b) : tailC d b ≤ 2 * 5 ^ d * (Real.pi / 2) ^ b := by
  have hb0 : 0 ≤ b := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hQ : (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹ ≤ 2 := by
    have h : (2 : ℝ) ^ ((d : ℝ) - b) ≤ 2 ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    rw [this] at h
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have heq : (4 : ℝ) ^ (-b) * (2 * Real.pi) ^ (b - d) =
      (Real.pi / 2) ^ b * ((2 * Real.pi) ^ (d : ℝ))⁻¹ := by
    rw [Real.rpow_sub hπ, Real.rpow_neg (by norm_num), Real.div_rpow Real.pi_pos.le
      (by norm_num), Real.mul_rpow (by norm_num) Real.pi_pos.le,
      show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    rw [show (2 : ℝ) * b = b + b by ring, Real.rpow_add (by norm_num)]
    have : (0 : ℝ) < 2 ^ b := by positivity
    have : (0 : ℝ) < Real.pi ^ b := by positivity
    have : (0 : ℝ) < (2 * Real.pi) ^ (d : ℝ) := by positivity
    field_simp
  have h2 : ((2 * Real.pi) ^ (d : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith [Real.pi_gt_three]) (Nat.cast_nonneg d))
  have hp : 0 ≤ (Real.pi / 2) ^ b := by positivity
  unfold tailC
  rw [mul_assoc (5 ^ d * _), heq]
  have h5 : (0 : ℝ) ≤ 5 ^ d := by positivity
  calc 5 ^ d * (1 - (2 : ℝ) ^ ((d : ℝ) - b))⁻¹ * ((Real.pi / 2) ^ b * ((2 * Real.pi) ^ (d : ℝ))⁻¹)
      ≤ 5 ^ d * 2 * ((Real.pi / 2) ^ b * 1) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hQ h5) (mul_le_mul_of_nonneg_left h2 hp)
          (by positivity) (by positivity)
    _ = _ := by ring

/-- Fourier moments of a symbol with decay at scale `R^{-1}`. -/
theorem avg_pnorm_pow_le (hd : 1 ≤ d) {w : Torus d n → ℝ} {B B' R : ℝ} (a r : ℕ)
    (hR : 0 < R) (hnR : 7 * R ≤ n) (hb : (d : ℝ) + a < 2 * r)
    (hw0 : ∀ m, 0 ≤ w m) (hB : ∀ m, w m ≤ B) (hB'0 : 0 ≤ B')
    (hB' : ∀ m, R⁻¹ < pnorm m → w m * (R * pnorm m) ^ (2 * r) ≤ B') :
    avg (fun m => pnorm m ^ a * w m) ≤
      (B + B' * tailC d (2 * r - a)) * R ^ (-((a : ℝ) + d)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnd : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hn d
  set ρ := R⁻¹
  have hρ : 0 < ρ := inv_pos.2 hR
  set b : ℝ := 2 * r - a
  have hbd : (d : ℝ) < b := by simp only [b]; linarith
  have hB0 : 0 ≤ B := (hw0 0).trans (hB 0)
  -- small momenta
  have hsmall : ∑ m ∈ univ.filter (fun m : Torus d n => pnorm m ≤ ρ), pnorm m ^ a * w m ≤
      ((n : ℝ) * ρ) ^ d * (ρ ^ a * B) := by
    calc _ ≤ ∑ m ∈ univ.filter (fun m : Torus d n => pnorm m ≤ ρ), ρ ^ a * B :=
          sum_le_sum fun m hm => mul_le_mul (pow_le_pow_left₀ (pnorm_nonneg m)
            (mem_filter.1 hm).2 a) (hB m) (hw0 m) (pow_nonneg hρ.le a)
      _ = ((univ.filter fun m : Torus d n => pnorm m ≤ ρ).card : ℝ) * (ρ ^ a * B) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ((card_pnorm_le hd hρ.le).trans
            (pow_le_pow_left₀ (by positivity) ?_ d)) (by positivity)
          have : (7 : ℝ) ≤ n * ρ := by
            simp only [ρ]; rw [← div_eq_mul_inv, le_div_iff₀ hR]; linarith
          linarith
  -- large momenta
  have hnr2 : 2 * Real.pi ≤ n * ρ := by
    have := Real.pi_lt_d2
    have : (7 : ℝ) ≤ n * ρ := by
      simp only [ρ]; rw [← div_eq_mul_inv, le_div_iff₀ hR]; linarith
    linarith
  have htail := sum_pnorm_rpow_tail (n := n) hd hbd hρ hnr2
  have hlarge : ∑ m ∈ univ.filter (fun m : Torus d n => ¬ pnorm m ≤ ρ), pnorm m ^ a * w m ≤
      B' * R ^ (-((2 * r : ℕ) : ℝ)) *
        ∑ m ∈ univ.filter (fun m : Torus d n => ρ < pnorm m), pnorm m ^ (-b) := by
    have hf : univ.filter (fun m : Torus d n => ¬ pnorm m ≤ ρ) =
        univ.filter (fun m : Torus d n => ρ < pnorm m) := by ext; simp
    rw [hf, mul_sum]
    refine sum_le_sum fun m hm => ?_
    have hm' := (mem_filter.1 hm).2
    have hp : 0 < pnorm m := hρ.trans hm'
    have hRp : 0 < R * pnorm m := mul_pos hR hp
    have h1 := hB' m hm'
    have h2 : w m ≤ B' / (R * pnorm m) ^ (2 * r) := by
      rw [le_div_iff₀ (pow_pos hRp _)]; exact h1
    calc pnorm m ^ a * w m ≤ pnorm m ^ a * (B' / (R * pnorm m) ^ (2 * r)) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hp.le a)
      _ = B' * R ^ (-((2 * r : ℕ) : ℝ)) * pnorm m ^ (-b) := by
          rw [Real.rpow_neg hR.le, Real.rpow_natCast, mul_pow]
          simp only [b]
          rw [show -((2 : ℝ) * r - a) = (a : ℝ) - ((2 * r : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_sub hp, Real.rpow_natCast, Real.rpow_natCast]
          field_simp
  -- assemble
  unfold avg
  rw [← sum_filter_add_sum_filter_not univ (fun m => pnorm m ≤ ρ), mul_add]
  have hi : (0 : ℝ) ≤ ((n : ℝ) ^ d)⁻¹ := inv_nonneg.2 hnd.le
  have hS0 : 0 ≤ ∑ m ∈ univ.filter (fun m : Torus d n => ρ < pnorm m), pnorm m ^ (-b) :=
    sum_nonneg fun m _ => Real.rpow_nonneg (pnorm_nonneg m) _
  have htail' : ∑ m ∈ univ.filter (fun m : Torus d n => ρ < pnorm m), pnorm m ^ (-b) ≤
      (n : ℝ) ^ d * (tailC d b * ρ ^ ((d : ℝ) - b)) := by
    refine htail.trans (le_of_eq ?_); unfold tailC; ring
  have hρa : ((n : ℝ) ^ d)⁻¹ * (((n : ℝ) * ρ) ^ d * (ρ ^ a * B)) = B * R ^ (-((a : ℝ) + d)) := by
    have e1 : ((n : ℝ) ^ d)⁻¹ * (((n : ℝ) * ρ) ^ d * (ρ ^ a * B)) = ρ ^ d * ρ ^ a * B := by
      rw [mul_pow]; field_simp
    rw [e1]
    simp only [ρ]
    rw [Real.rpow_neg hR.le, Real.rpow_add hR, Real.rpow_natCast, Real.rpow_natCast, inv_pow,
      inv_pow]
    ring
  have hρb : R ^ (-((2 * r : ℕ) : ℝ)) * ρ ^ ((d : ℝ) - b) = R ^ (-((a : ℝ) + d)) := by
    simp only [ρ, b]
    rw [Real.inv_rpow hR.le, ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
    congr 1; push_cast; ring
  have hT0 := tailC_nonneg (d := d) hbd
  calc ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ univ.filter (fun m : Torus d n => pnorm m ≤ ρ), pnorm m ^ a * w m +
        ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ univ.filter (fun m : Torus d n => ¬ pnorm m ≤ ρ), pnorm m ^ a * w m
      ≤ ((n : ℝ) ^ d)⁻¹ * (((n : ℝ) * ρ) ^ d * (ρ ^ a * B)) +
        ((n : ℝ) ^ d)⁻¹ * (B' * R ^ (-((2 * r : ℕ) : ℝ)) *
          ((n : ℝ) ^ d * (tailC d b * ρ ^ ((d : ℝ) - b)))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hsmall hi)
          (mul_le_mul_of_nonneg_left (hlarge.trans ?_) hi)
        exact mul_le_mul_of_nonneg_left htail' (mul_nonneg hB'0 (Real.rpow_nonneg hR.le _))
    _ = B * R ^ (-((a : ℝ) + d)) + B' * tailC d b *
          (R ^ (-((2 * r : ℕ) : ℝ)) * ρ ^ ((d : ℝ) - b)) := by
        rw [hρa]; field_simp
    _ = _ := by rw [hρb]; ring

end

end DressedFRD
