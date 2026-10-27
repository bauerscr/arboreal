module

public import ArborealDecay.Stability.Basic

/-!
# Two-variable lemmas over `ℂ`

Let `H` be the open upper half-plane. For `a b e d : ℂ`, the polynomial `a + b x + e y + d x y`
has no zero on `H × H` (`TwoVarZeroFree`).

* `TwoVarZeroFree.im_div_nonneg` (Sublemma A0): if `d ≠ 0` then `Im (e / d) ≥ 0` and
  `Im (b / d) ≥ 0`.
* `TwoVarZeroFree.sub_real_mul` (Lemma A1): for real `c ≥ 0`, the polynomial
  `a + b x + e y + d x y - c d` has no zero on `H × H` either.
* `TwoVarZeroFree.im_mul_conj_nonneg`: the closed Rayleigh-type inequality
  `Im ((a + i b) * conj (e + i d)) ≥ 0`.
-/

@[expose] public section

namespace ArborealDecay.Stability

noncomputable section

/-- The affine-in-each-variable polynomial `a + b x + e y + d x y` has no zero on `H × H`. -/
@[expose] def TwoVarZeroFree (a b e d : ℂ) : Prop :=
  ∀ x y : ℂ, 0 < x.im → 0 < y.im → a + b * x + e * y + d * x * y ≠ 0

namespace TwoVarZeroFree

variable {a b e d : ℂ}

/-- Symmetry in the two variables. -/
theorem symm (h : TwoVarZeroFree a b e d) : TwoVarZeroFree a e b d := fun x y hx hy => by
  have := h y x hy hx
  intro h0; apply this; linear_combination h0

/-- Sublemma A0, first half. -/
theorem im_div_nonneg_left (h : TwoVarZeroFree a b e d) (hd : d ≠ 0) : 0 ≤ (e / d).im := by
  by_contra hneg
  replace hneg := not_le.mp hneg
  set α := e / d with hα
  set β := b / d with hβ
  set γ := α * β - a / d with hγ
  have he : e = α * d := by rw [hα]; field_simp
  have hb : b = β * d := by rw [hβ]; field_simp
  have ha : a = d * (α * β - γ) := by rw [hγ]; field_simp; ring
  set R : ℝ := ‖γ‖ / (-α.im) + |β.im| + 1 with hR
  have hαp : 0 < -α.im := by linarith
  have hRpos : 0 < R := by
    have : 0 ≤ ‖γ‖ / (-α.im) := by positivity
    have := abs_nonneg β.im
    rw [hR]; linarith
  have hRγ : ‖γ‖ < R * (-α.im) := by
    have h1 : ‖γ‖ / (-α.im) < R := by
      have := abs_nonneg β.im
      rw [hR]; linarith
    rwa [div_lt_iff₀ hαp] at h1
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  set x : ℂ := -α - Complex.I * γ / R with hx
  set y : ℂ := Complex.I * R - β with hy
  have hximp : 0 < x.im := by
    have h1 : x.im = -α.im - γ.re / R := by
      rw [hx]; simp [Complex.div_ofReal_im, Complex.div_ofReal_re]
    have h2 : γ.re ≤ ‖γ‖ := (Complex.re_le_norm γ)
    have h3 : γ.re / R < -α.im := by
      rw [div_lt_iff₀ hRpos]; nlinarith
    rw [h1]; linarith
  have hyimp : 0 < y.im := by
    have : y.im = R - β.im := by rw [hy]; simp
    rw [this]
    have := neg_abs_le β.im
    have h4 : 0 ≤ ‖γ‖ / (-α.im) := by positivity
    rw [hR]; linarith [le_abs_self β.im]
  apply h x y hximp hyimp
  have hxy : (x + α) * (y + β) = γ := by
    rw [hx, hy]
    field_simp
    linear_combination (-(γ * (R:ℂ))) * Complex.I_mul_I
  rw [ha, hb, he]
  linear_combination d * hxy

/-- Sublemma A0, second half. -/
theorem im_div_nonneg_right (h : TwoVarZeroFree a b e d) (hd : d ≠ 0) : 0 ≤ (b / d).im :=
  h.symm.im_div_nonneg_left hd

/-- Lemma A1. -/
theorem sub_real_mul (h : TwoVarZeroFree a b e d) {c : ℝ} (hc : 0 ≤ c) :
    TwoVarZeroFree (a - c * d) b e d := fun x y hx hy => by
  have key : a + b * x + e * y + d * x * y - c * d ≠ 0 := by
    intro heq
    by_cases hd : d = 0
    · subst hd
      apply h x y hx hy
      simpa using heq
    · set α := e / d with hα
      have hα0 : 0 ≤ α.im := h.im_div_nonneg_left hd
      set u := x + α with hu
      have hui : 0 < u.im := by rw [hu]; simp; linarith
      have hu0 : u ≠ 0 := fun h0 => by rw [h0] at hui; simp at hui
      have he : e = α * d := by rw [hα]; field_simp
      have hdu : e + d * x = d * u := by rw [hu, he]; ring
      have hyi : 0 < (y - c / u).im := by
        have : (y - c / u).im = y.im + c * u.im / Complex.normSq u := by
          rw [Complex.sub_im, Complex.div_im]
          simp
        rw [this]
        have : 0 ≤ c * u.im / Complex.normSq u := by
          apply div_nonneg (mul_nonneg hc hui.le) (Complex.normSq_nonneg _)
        linarith
      apply h x (y - c / u) hx hyi
      have : (c : ℂ) / u * (e + d * x) = c * d := by
        rw [hdu]; field_simp
      linear_combination heq - this
  intro h0; apply key; linear_combination h0

/-- The closed inequality used for the Rayleigh property. -/
theorem im_mul_conj_nonneg (h : TwoVarZeroFree a b e d) :
    0 ≤ ((a + Complex.I * b) * (starRingEnd ℂ) (e + Complex.I * d)).im := by
  by_cases hs : e + Complex.I * d = 0
  · simp [hs]
  · by_contra hneg
    replace hneg := not_le.mp hneg
    set s := e + Complex.I * d with hsdef
    set t := a + Complex.I * b with htdef
    have hns : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs
    -- root v = -t / s
    have hv : 0 < (-t / s).im := by
      have : (-t / s).im = -(t * (starRingEnd ℂ) s).im / Complex.normSq s := by
        rw [Complex.div_im]
        simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      rw [this]
      apply div_pos _ hns
      linarith
    apply h Complex.I (-t / s) (by simp) hv
    have : s * (-t / s) = -t := by field_simp
    linear_combination this
  
end TwoVarZeroFree

end

end ArborealDecay.Stability
