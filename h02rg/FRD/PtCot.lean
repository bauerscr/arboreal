import Mathlib

/-!
# `∑_{k ∈ ℤ} (x + k)^{-2} = π² / sin² (π x)`

Derived from the cotangent series `cot_series_rep'` by termwise differentiation, for
`x ∈ (0, 3/4)`.
-/

namespace FRD

open Real Filter Topology

/-- The real cotangent series on `(0, 1)`. -/
lemma real_cot_series {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    HasSum (fun n : ℕ => (y - (n + 1))⁻¹ + (y + (n + 1))⁻¹) (π * Real.cot (π * y) - y⁻¹) := by
  have hz : (y : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hn' : (n : ℝ) = y := by exact_mod_cast hn
    have a : (0 : ℝ) < n := hn' ▸ h0
    have b : (n : ℝ) < 1 := hn' ▸ h1
    have a' : 0 < n := by exact_mod_cast a
    have b' : n < 1 := by exact_mod_cast b
    omega
  have hc := cot_series_rep' hz
  have hs := summable_cotTerm hz
  set fr : ℕ → ℝ := fun n => (y - (n + 1))⁻¹ + (y + (n + 1))⁻¹
  have hcast : ∀ n : ℕ, ((fr n : ℝ) : ℂ) = cotTerm y n := by
    intro n; simp [fr, cotTerm]
  have hsr : Summable fr := by
    rw [← Complex.summable_ofReal]
    simpa [hcast] using hs
  convert hsr.hasSum using 1
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  simp_rw [hcast]
  push_cast
  simpa [cotTerm, one_div] using hc

lemma hasDerivAt_pi_cot (y : ℝ) (hy : Real.sin (π * y) ≠ 0) (hy0 : y ≠ 0) :
    HasDerivAt (fun z => π * Real.cot (π * z) - z⁻¹)
      (-(π ^ 2 / Real.sin (π * y) ^ 2) + (y ^ 2)⁻¹) y := by
  have hcot : (fun z => π * Real.cot (π * z) - z⁻¹) =
      fun z => π * (Real.cos (π * z) / Real.sin (π * z)) - z⁻¹ := by
    funext z; rw [Real.cot_eq_cos_div_sin]
  rw [hcot]
  have h1 : HasDerivAt (fun z => π * z) π y := by
    simpa using (hasDerivAt_id y).const_mul π
  have hcos := (Real.hasDerivAt_cos (π * y)).comp y h1
  have hsin := (Real.hasDerivAt_sin (π * y)).comp y h1
  have hq := (hcos.div hsin hy).const_mul π
  have hinv := hasDerivAt_inv hy0
  simp only [Function.comp_apply] at hq
  convert hq.sub hinv using 1
  have hsc := Real.sin_sq_add_cos_sq (π * y)
  field_simp
  linear_combination (π ^ 2 * y ^ 2) * hsc

/-- `∑_{k ∈ ℤ} (x + k)^{-2} = π² / sin²(π x)` for `x ∈ (0, 3/4)`. -/
theorem hasSum_inv_add_int_sq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 3 / 4) :
    HasSum (fun k : ℤ => ((x + k) ^ 2)⁻¹) (π ^ 2 / Real.sin (π * x) ^ 2) := by
  set U := Set.Ioo (0 : ℝ) (3 / 4)
  let g : ℕ → ℝ → ℝ := fun n y => (y - (n + 1))⁻¹ + (y + (n + 1))⁻¹
  let g' : ℕ → ℝ → ℝ := fun n y => -1 / (y - (n + 1)) ^ 2 + -1 / (y + (n + 1)) ^ 2
  let v : ℕ → ℝ := fun n => 17 / ((n + 1 : ℕ) : ℝ) ^ 2
  have hv : Summable v := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [v, div_eq_mul_inv] using this.mul_left 17
  have hsub : ∀ (n : ℕ) (y : ℝ), y ∈ U → y - (n + 1) ≠ 0 := by
    intro n y hy h; have := hy.2; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hadd : ∀ (n : ℕ) (y : ℝ), y ∈ U → y + (n + 1) ≠ 0 := by
    intro n y hy h; have := hy.1; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hg : ∀ n y, y ∈ U → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have e1 := ((hasDerivAt_id y).sub_const ((n : ℝ) + 1)).inv (hsub n y hy)
    have e2 := ((hasDerivAt_id y).add_const ((n : ℝ) + 1)).inv (hadd n y hy)
    convert e1.add e2 using 1
  have hg' : ∀ n y, y ∈ U → ‖g' n y‖ ≤ v n := by
    intro n y hy
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have a1 : ((n : ℝ) + 1) / 4 ≤ |y - (n + 1)| := by
      rw [abs_of_neg (by linarith [hy.2])]; linarith [hy.2]
    have a2 : ((n : ℝ) + 1) ≤ |y + (n + 1)| := by
      rw [abs_of_pos (by linarith [hy.1])]; linarith [hy.1]
    have hp : (0 : ℝ) < (n + 1) / 4 := by positivity
    have b1 : 1 / (y - (n + 1)) ^ 2 ≤ 16 / ((n : ℝ) + 1) ^ 2 := by
      rw [← sq_abs]
      calc 1 / |y - (n + 1)| ^ 2 ≤ 1 / (((n : ℝ) + 1) / 4) ^ 2 := by gcongr
        _ = 16 / ((n : ℝ) + 1) ^ 2 := by field_simp; norm_num
    have b2 : 1 / (y + (n + 1)) ^ 2 ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
      rw [← sq_abs]
      gcongr
    simp only [g', v, Real.norm_eq_abs]
    push_cast
    calc |-1 / (y - (n + 1)) ^ 2 + -1 / (y + (n + 1)) ^ 2|
        ≤ |-1 / (y - (n + 1)) ^ 2| + |-1 / (y + (n + 1)) ^ 2| := abs_add_le _ _
      _ = 1 / (y - (n + 1)) ^ 2 + 1 / (y + (n + 1)) ^ 2 := by
          rw [neg_div, neg_div, abs_neg, abs_neg, abs_of_nonneg (by positivity),
            abs_of_nonneg (by positivity)]
      _ ≤ 16 / ((n : ℝ) + 1) ^ 2 + 1 / ((n : ℝ) + 1) ^ 2 := add_le_add b1 b2
      _ = 17 / ((n : ℝ) + 1) ^ 2 := by ring
  have hU : IsOpen U := isOpen_Ioo
  have hUc : IsPreconnected U := isPreconnected_Ioo
  have hxU : x ∈ U := ⟨hx0, hx1⟩
  have hser : ∀ y ∈ U, HasSum (fun n => g n y) (π * Real.cot (π * y) - y⁻¹) :=
    fun y hy => real_cot_series hy.1 (by linarith [hy.2])
  have hD := hasDerivAt_tsum_of_isPreconnected hv hU hUc hg hg' hxU (hser x hxU).summable hxU
  have hev : (fun z => ∑' n, g n z) =ᶠ[𝓝 x] fun z => π * Real.cot (π * z) - z⁻¹ := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact (hser z hz).tsum_eq
  have hsinx : Real.sin (π * x) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) _).ne'
    nlinarith [Real.pi_pos]
  have hD2 := hasDerivAt_pi_cot x hsinx hx0.ne'
  have huniq := (hD.congr_of_eventuallyEq hev.symm).unique hD2
  -- huniq : ∑' n, g' n x = -(π²/sin²) + x⁻²
  have hg's : HasSum (fun n => g' n x) (-(π ^ 2 / Real.sin (π * x) ^ 2) + (x ^ 2)⁻¹) := by
    rw [← huniq]
    exact (hv.of_norm_bounded (fun n => hg' n x hxU)).hasSum
  -- split the series
  set f : ℤ → ℝ := fun k => ((x + k) ^ 2)⁻¹
  have hA : Summable fun n : ℕ => ((x + (n + 1)) ^ 2)⁻¹ := by
    refine hv.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    have := hg' n x hxU
    have h2 : 0 ≤ ((x - (n + 1)) ^ 2)⁻¹ := by positivity
    simp only [g', Real.norm_eq_abs] at this
    rw [neg_div, neg_div, ← neg_add, abs_neg, abs_of_nonneg (by positivity)] at this
    simp only [one_div] at this
    linarith
  have hB : Summable fun n : ℕ => ((x - (n + 1)) ^ 2)⁻¹ := by
    refine hv.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    have := hg' n x hxU
    have h2 : 0 ≤ ((x + (n + 1)) ^ 2)⁻¹ := by positivity
    simp only [g', Real.norm_eq_abs] at this
    rw [neg_div, neg_div, ← neg_add, abs_neg, abs_of_nonneg (by positivity)] at this
    simp only [one_div] at this
    linarith
  have hsumAB : ∑' n : ℕ, ((x + (n + 1)) ^ 2)⁻¹ + ∑' n : ℕ, ((x - (n + 1)) ^ 2)⁻¹ =
      π ^ 2 / Real.sin (π * x) ^ 2 - (x ^ 2)⁻¹ := by
    rw [← hA.tsum_add hB]
    have : ∀ n : ℕ, ((x + (n + 1)) ^ 2)⁻¹ + ((x - (n + 1)) ^ 2)⁻¹ = -g' n x := by
      intro n; simp only [g']; ring
    simp_rw [this, tsum_neg, hg's.tsum_eq]
    ring
  have h1 : HasSum (fun n : ℕ => f n) ((x ^ 2)⁻¹ + ∑' n : ℕ, ((x + (n + 1)) ^ 2)⁻¹) := by
    have := (hasSum_nat_add_iff (f := fun n : ℕ => f n) 1).mp (by
      convert hA.hasSum using 2 with n; simp [f])
    convert this using 1
    simp [f, add_comm]
  have h2 : HasSum (fun n : ℕ => f (-(n + 1))) (∑' n : ℕ, ((x - (n + 1)) ^ 2)⁻¹) := by
    convert hB.hasSum using 2 with n
    simp [f, sub_eq_add_neg]
  convert h1.of_nat_of_neg_add_one h2 using 1
  linarith [hsumAB]

end FRD
