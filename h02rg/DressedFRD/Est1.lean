import DressedFRD.Range

/-!
# Generic estimates for `sec:proof`

* `snorm_le_of_pointwise`: pointwise domination `|v| ≤ B |u|` gives `‖v‖_{(s)} ≤ B ‖u‖_{(s)}`.
* `snorm_le_tsum`: the norm of a pointwise convergent series.
* `absorb`: the scale-change factor `L^{(s-r)c}` of a word with maximal tail scale `r` is paid by
  `η^k`, where `k` is the number of `c`-letters. (This replaces the factor `L^{-(r-j)(d-2+q)}` in
  the weights of `𝒮_j` in the text, see `Log.md`.)
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n] {L : ℝ} {q s : ℕ}

theorem mom_le_of_pointwise (α : Dir d → ℕ) {v u : Sym d n} {B : ℝ}
    (h : ∀ m, ‖v m‖ ≤ B * ‖u m‖) : mom α v ≤ B * mom α u := by
  unfold mom
  rw [← avg_smul]
  refine avg_mono fun m => ?_
  have := h m
  nlinarith [norm_nonneg (sigma α m)]

theorem snorm_le_of_pointwise (hL : 0 < L) {v u : Sym d n} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ m, ‖v m‖ ≤ B * ‖u m‖) : snorm L q s v ≤ B * snorm L q s u := by
  refine snorm_le_iff.2 fun α hα => ?_
  calc wgt d L s α * mom α v ≤ wgt d L s α * (B * mom α u) :=
        mul_le_mul_of_nonneg_left (mom_le_of_pointwise α h) (wgt_pos hL s α).le
    _ = B * (wgt d L s α * mom α u) := by ring
    _ ≤ B * snorm L q s u := mul_le_mul_of_nonneg_left (le_snorm hα u) hB

/-- The norm of a pointwise convergent series of symbols. -/
theorem snorm_le_tsum (hL : 0 < L) {f : ℕ → Sym d n} {S : Sym d n}
    (hS : ∀ m, HasSum (fun k => f k m) (S m)) (hf : Summable fun k => snorm L q s (f k)) :
    snorm L q s S ≤ ∑' k, snorm L q s (f k) := by
  refine snorm_le_iff.2 fun α hα => ?_
  have hw := wgt_pos hL s α
  -- `mom α S ≤ ∑' mom α (f k)`
  have hmom_sum : Summable fun k => mom α (f k) := by
    refine Summable.of_nonneg_of_le (fun k => mom_nonneg α (f k))
      (fun k => mom_le hL hα (f k)) (hf.mul_left _)
  have hnorm : ∀ m, Summable fun k => ‖f k m‖ := by
    intro m
    -- `|f k m| ≤ |Λ| sup ... ≤ |Λ| wgt⁻¹ snorm` via `mom 0`
    have hb : ∀ k, ‖f k m‖ ≤ ((n : ℝ) ^ d) * (wgt d L s 0)⁻¹ * snorm L q s (f k) := by
      intro k
      have h0 := mom_le (q := q) (s := s) hL (α := 0) (by simp [Grassmann.mabs]) (f k)
      rw [mom_zero] at h0
      have h1 : ‖f k m‖ ≤ (n : ℝ) ^ d * avg fun m => ‖f k m‖ := by
        unfold avg
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))),
          one_mul]
        exact single_le_sum (f := fun m => ‖f k m‖) (fun _ _ => norm_nonneg _) (mem_univ m)
      calc ‖f k m‖ ≤ (n : ℝ) ^ d * avg fun m => ‖f k m‖ := h1
        _ ≤ (n : ℝ) ^ d * ((wgt d L s 0)⁻¹ * snorm L q s (f k)) :=
            mul_le_mul_of_nonneg_left h0 (by positivity)
        _ = _ := by ring
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb (hf.mul_left _)
  have hmom : mom α S ≤ ∑' k, mom α (f k) := by
    have e : ∀ k, mom α (f k) = ((n : ℝ) ^ d)⁻¹ * ∑ m, ‖sigma α m‖ * ‖f k m‖ := fun k => rfl
    simp only [e]
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun m _ => (hnorm m).mul_left _)]
    unfold mom avg
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun m _ => ?_) (by positivity)
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← (hS m).tsum_eq]
    exact norm_tsum_le_tsum_norm (hnorm m)
  calc wgt d L s α * mom α S ≤ wgt d L s α * ∑' k, mom α (f k) :=
        mul_le_mul_of_nonneg_left hmom hw.le
    _ = ∑' k, wgt d L s α * mom α (f k) := (tsum_mul_left).symm
    _ ≤ ∑' k, snorm L q s (f k) :=
        Summable.tsum_le_tsum (fun k => le_snorm hα (f k)) (hmom_sum.mul_left _) hf

/-! ### The absorption inequality -/

theorem seven_pow_ge (m : ℕ) : 6 * m + 1 ≤ 7 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ]; omega

/-- If `L^{s-1} ≤ (k+2)(L^r + 2)` with `s ≥ r + 2`, `r ≥ 1`, `L ≥ 7`, then `k ≥ s - 1 - r`. -/
theorem k_ge {L r s k : ℕ} (hL : 7 ≤ L) (hr : 1 ≤ r) (hrs : r + 2 ≤ s)
    (hk : L ^ (s - 1) ≤ (k + 2) * (L ^ r + 2)) : s - 1 - r ≤ k := by
  set m := s - 1 - r with hm
  have hsplit : L ^ (s - 1) = L ^ m * L ^ r := by rw [← pow_add]; congr 1; omega
  have hLr : 7 ≤ L ^ r := le_trans hL (Nat.le_self_pow (by omega) L)
  have h7 : 7 * (L ^ r + 2) ≤ 9 * L ^ r := by omega
  have h1 : 7 * L ^ m * L ^ r ≤ 9 * (k + 2) * L ^ r := by
    calc 7 * L ^ m * L ^ r = 7 * L ^ (s - 1) := by rw [hsplit]; ring
      _ ≤ 7 * ((k + 2) * (L ^ r + 2)) := Nat.mul_le_mul_left 7 hk
      _ = (k + 2) * (7 * (L ^ r + 2)) := by ring
      _ ≤ (k + 2) * (9 * L ^ r) := Nat.mul_le_mul_left _ h7
      _ = 9 * (k + 2) * L ^ r := by ring
  have h2 : 7 * L ^ m ≤ 9 * (k + 2) := Nat.le_of_mul_le_mul_right h1 (by omega)
  have h3 : 7 ^ m ≤ L ^ m := Nat.pow_le_pow_left hL m
  have h4 := seven_pow_ge m
  have hm1 : 1 ≤ m := by omega
  omega

/-- The absorption inequality: `L^{(s-r)c} η^k ≤ L^c` if `η ≤ L^{-c}` and
`L^{s-1} ≤ (k+2)(L^r + 2)`. -/
theorem absorb {L : ℕ} (hL : 7 ≤ L) {c η : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hηc : η ≤ (L : ℝ) ^ (-c)) {r s k : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s)
    (hk : L ^ (s - 1) ≤ (k + 2) * (L ^ r + 2)) :
    (L : ℝ) ^ (((s - r : ℕ) : ℝ) * c) * η ^ k ≤ (L : ℝ) ^ c := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hη1 : η ≤ 1 := hηc.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  by_cases hsr : s ≤ r + 1
  · have h1 : (L : ℝ) ^ (((s - r : ℕ) : ℝ) * c) ≤ (L : ℝ) ^ c := by
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      have : ((s - r : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : s - r ≤ 1)
      nlinarith
    calc (L : ℝ) ^ (((s - r : ℕ) : ℝ) * c) * η ^ k ≤ (L : ℝ) ^ c * 1 :=
          mul_le_mul h1 (pow_le_one₀ hη hη1) (by positivity) (by positivity)
      _ = _ := mul_one _
  · have hk' := k_ge hL hr (by omega) hk
    have hηk : η ^ k ≤ (L : ℝ) ^ (-(c * k)) := by
      calc η ^ k ≤ ((L : ℝ) ^ (-c)) ^ k := pow_le_pow_left₀ hη hηc k
        _ = (L : ℝ) ^ (-(c * k)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
    calc (L : ℝ) ^ (((s - r : ℕ) : ℝ) * c) * η ^ k
        ≤ (L : ℝ) ^ (((s - r : ℕ) : ℝ) * c) * (L : ℝ) ^ (-(c * k)) :=
          mul_le_mul_of_nonneg_left hηk (by positivity)
      _ = (L : ℝ) ^ (((s - r : ℕ) : ℝ) * c + -(c * k)) := (Real.rpow_add hL0 _ _).symm
      _ ≤ (L : ℝ) ^ c := by
          refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
          have : ((s - r : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : s - r ≤ k + 1)
          nlinarith

end

end DressedFRD
