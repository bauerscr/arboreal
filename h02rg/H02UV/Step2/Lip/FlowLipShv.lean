import Step2.Lip.FlowLipCmp2

/-!
# The explicit part of the coupling map and the zero mode (Lipschitz bounds, part 18)

On the domain, `κ♭ = (0, 0, ν̂, ĝ)`, so the explicit part `κ♭.shift(c₀, δ)` of the couplings is
`(-ĝ c₀, -ĝ δ, ν̂ + 4 ĝ δ, ĝ)` (`shv_dom`). Its differences along two histories (`shv_sub_le`) and
the recursion of the normalised zero mode `ŵ` (`ewH_succ_le`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

theorem GoodCov2.norm_le {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    (hC : GoodCov2 j ℓ C) (x y : Lam 2 L N) : ‖C x y‖ ≤ ℓ ^ 2 := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  exact norm_cov_le hG hB x y

theorem c0C_le {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 j ℓ C) :
    ‖c0C C‖ ≤ ℓ ^ 2 := hC.norm_le 0 0

theorem dlC_le {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 j ℓ C) :
    ‖dlC C‖ ≤ 2 * ℓ ^ 2 :=
  (norm_sub_le _ _).trans (by linarith [hC.norm_le (dirVec (Sum.inl 0)) 0, hC.norm_le 0 0])

/-- `L^{2(j+1)} |δ| ≤ ℓ²/2` for a symmetric good covariance. -/
theorem dlC_le' {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 j ℓ C)
    (hCs : CSym C) (hCsym : ∀ x y, C x y = C y x) :
    ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC C‖ ≤ ℓ ^ 2 / 2 := by
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num) hCs hCsym
  obtain ⟨-, hδb⟩ := cov_c0_delta_le hC hc₀ hδ hδ'
  have hdl : dlC C = δ := by
    unfold dlC
    have := hδ 0 (Sum.inl 0)
    rw [zero_add] at this
    rw [this, hc₀ 0]; ring
  rw [hdl]
  have hh : (0 : ℝ) < ((L : ℝ) ^ (j + 1)) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [le_div_iff₀ (by positivity)] at hδb
  nlinarith

theorem c0C_sub (C C' : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) : c0C C' - c0C C = c0C (C' - C) := by
  simp [c0C]

theorem dlC_sub (C C' : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) : dlC C' - dlC C = dlC (C' - C) := by
  simp [dlC]; ring

/-- The explicit part on the domain. -/
theorem shv_dom (R : RGPar 2 L N) (k : ℕ) (s : SD L N) (h : ‖s.zh + s.yh‖ ≤ R.ρ)
    (hy : ‖s.yh‖ ≤ R.ρ) :
    SD.shv R k s = ![-(((s.g : ℂ) / (1 + nCor (s.μ : ℂ) s.w)) * c0C s.C),
      -(((s.g : ℂ) / (1 + nCor (s.μ : ℂ) s.w)) * dlC s.C),
      ((s.μ : ℂ) / (L : ℂ) ^ (2 * k) - (s.zh + s.yh) * (1 + (s.zh + s.yh))⁻¹ * R.msq) +
        4 * ((s.g : ℂ) / (1 + nCor (s.μ : ℂ) s.w)) * dlC s.C,
      (s.g : ℂ) / (1 + nCor (s.μ : ℂ) s.w)] := by
  rw [SD.shv, nVec_dom R k h hy]
  funext i
  fin_cases i
  · simp [Coup.toVec, Coup.shift, Coup.ofVec]
  · simp [Coup.toVec, Coup.shift, Coup.ofVec]
  · simp only [Coup.toVec, Coup.shift, Coup.ofVec, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    push_cast; ring
  · simp [Coup.toVec, Coup.shift, Coup.ofVec]

/-- `ĝ = g/(1+n)`. -/
def ghat (s : SD L N) : ℂ := (s.g : ℂ) / (1 + nCor (s.μ : ℂ) s.w)

theorem norm_ghat_le (s : SD L N) : ‖ghat s‖ ≤ 8 / 7 * |s.g| := by
  rw [ghat, norm_div, Complex.norm_real, Real.norm_eq_abs,
    div_le_iff₀ (by linarith [norm_one_add_nCor (s.μ : ℂ) s.w])]
  have := norm_one_add_nCor (s.μ : ℂ) s.w
  nlinarith [abs_nonneg s.g]

theorem ghat_sub_le (s s' : SD L N) (hg' : |s'.g| ≤ 1) :
    ‖ghat s' - ghat s‖ ≤
      8 / 7 * |s'.g - s.g| + 2 * ‖nCor (s'.μ : ℂ) s'.w - nCor (s.μ : ℂ) s.w‖ := by
  have e : ghat s' - ghat s = ((s'.g - s.g : ℝ) : ℂ) * (1 + nCor (s.μ : ℂ) s.w)⁻¹ +
      (s'.g : ℂ) * ((1 + nCor (s'.μ : ℂ) s'.w)⁻¹ - (1 + nCor (s.μ : ℂ) s.w)⁻¹) := by
    simp only [ghat]; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have a1 := norm_inv_one_add_le (norm_nCor_le (s.μ : ℂ) s.w)
  have a2 := norm_inv_one_add_sub_le (norm_nCor_le (s'.μ : ℂ) s'.w) (norm_nCor_le (s.μ : ℂ) s.w)
  have := mul_le_mul_of_nonneg_left a1 (abs_nonneg (s'.g - s.g))
  have := mul_le_mul hg' a2 (norm_nonneg _) zero_le_one
  nlinarith [abs_nonneg (s'.g - s.g)]

/-- **The differences of the explicit part** (components `z, y` and `g`). -/
theorem shv01_sub_le (R : RGPar 2 L N) (k : ℕ) (s s' : SD L N) (h : ‖s.zh + s.yh‖ ≤ R.ρ)
    (hy : ‖s.yh‖ ≤ R.ρ) (h' : ‖s'.zh + s'.yh‖ ≤ R.ρ) (hy' : ‖s'.yh‖ ≤ R.ρ) {ℓC ℓΔ : ℝ}
    (hC' : GoodCov2 k ℓC s'.C) (hΔ : GoodCov2 k ℓΔ (s'.C - s.C)) :
    ‖SD.shv R k s' 0 - SD.shv R k s 0‖ + ‖SD.shv R k s' 1 - SD.shv R k s 1‖ ≤
      3 * ℓC ^ 2 * ‖ghat s' - ghat s‖ + 3 * ‖ghat s‖ * ℓΔ ^ 2 := by
  rw [shv_dom R k s h hy, shv_dom R k s' h' hy']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have e0 : -(((s'.g : ℂ) / (1 + nCor (s'.μ : ℂ) s'.w)) * c0C s'.C) -
      -(((s.g : ℂ) / (1 + nCor (s.μ : ℂ) s.w)) * c0C s.C) =
      -((ghat s' - ghat s) * c0C s'.C + ghat s * (c0C s'.C - c0C s.C)) := by simp only [ghat]; ring
  have e1 : -(((s'.g : ℂ) / (1 + nCor (s'.μ : ℂ) s'.w)) * dlC s'.C) -
      -(((s.g : ℂ) / (1 + nCor (s.μ : ℂ) s.w)) * dlC s.C) =
      -((ghat s' - ghat s) * dlC s'.C + ghat s * (dlC s'.C - dlC s.C)) := by simp only [ghat]; ring
  rw [e0, e1, norm_neg, norm_neg, c0C_sub, dlC_sub]
  have a1 := c0C_le hC'
  have a2 := dlC_le hC'
  have a3 := c0C_le hΔ
  have a4 := dlC_le hΔ
  have b1 := norm_add_le ((ghat s' - ghat s) * c0C s'.C) (ghat s * c0C (s'.C - s.C))
  have b2 := norm_add_le ((ghat s' - ghat s) * dlC s'.C) (ghat s * dlC (s'.C - s.C))
  rw [norm_mul, norm_mul] at b1 b2
  have := mul_le_mul_of_nonneg_left a1 (norm_nonneg (ghat s' - ghat s))
  have := mul_le_mul_of_nonneg_left a2 (norm_nonneg (ghat s' - ghat s))
  have := mul_le_mul_of_nonneg_left a3 (norm_nonneg (ghat s))
  have := mul_le_mul_of_nonneg_left a4 (norm_nonneg (ghat s))
  nlinarith

theorem shv3_sub (R : RGPar 2 L N) (k : ℕ) (s s' : SD L N) (h : ‖s.zh + s.yh‖ ≤ R.ρ)
    (hy : ‖s.yh‖ ≤ R.ρ) (h' : ‖s'.zh + s'.yh‖ ≤ R.ρ) (hy' : ‖s'.yh‖ ≤ R.ρ) :
    SD.shv R k s' 3 - SD.shv R k s 3 = ghat s' - ghat s := by
  rw [shv_dom R k s h hy, shv_dom R k s' h' hy']
  rfl

theorem shv_le (R : RGPar 2 L N) (k : ℕ) (s : SD L N) (h : ‖s.zh + s.yh‖ ≤ R.ρ)
    (hy : ‖s.yh‖ ≤ R.ρ) {ℓC : ℝ} (hC : GoodCov2 k ℓC s.C) :
    ‖SD.shv R k s 0‖ + ‖SD.shv R k s 1‖ ≤ 3 * ℓC ^ 2 * ‖ghat s‖ ∧
      ‖SD.shv R k s 3‖ = ‖ghat s‖ := by
  rw [shv_dom R k s h hy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
    norm_neg, norm_mul]
  refine ⟨?_, rfl⟩
  have a1 := c0C_le hC
  have a2 := dlC_le hC
  have := mul_le_mul_of_nonneg_left a1 (norm_nonneg (ghat s))
  have := mul_le_mul_of_nonneg_left a2 (norm_nonneg (ghat s))
  simp only [ghat] at *
  nlinarith

end

end Step2
