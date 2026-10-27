module

public import ArborealDecay.Separator.RealPoly
public import ArborealDecay.Separator.LeadingTerm
public import ArborealDecay.Stability.TwoVar

/-!
# The univariate core of the separator lemma (supplement `thm:separator`, Steps 2–8)

All statements here are about the four univariate polynomials `a₀, a₁, a₂, a₁₂ ∈ ℝ[t]` of the
supplement's set-up, with `p(x, y, t, …, t) = a₀ + a₁ x + a₂ y + a₁₂ x y`. The hypotheses of
`separator_core` are exactly the facts that the set-up step derives from `p`:
degree and top coefficients, positivity of `a₁` on `[0, ∞)`, the Rayleigh inequalities
`(eq:sup-sep-rayleigh)` and the one for `∂ₓ p` (via `lem:rayleigh-deriv` and `lem:diag`), and
stability of the diagonal specialization. They are discharged in `ArborealDecay.Separator.Main`.
-/

@[expose] public section

open Polynomial Filter Topology

namespace ArborealDecay.Separator

noncomputable section

private theorem coeff_eq_zero_of_le {P : ℝ[X]} {m n : ℕ} (hP : P.natDegree ≤ m) (hn : m < n) :
    P.coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hn)

/-- Steps 2–8 of the supplement's proof of `thm:separator`, for the univariate data. -/
theorem separator_core (m : ℕ) {a0 a1 a2 a12 : ℝ[X]} {c A B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hd0 : a0.natDegree ≤ m) (hd1 : a1.natDegree ≤ m) (hd2 : a2.natDegree ≤ m)
    (hd12 : a12.natDegree ≤ m)
    (ht12 : a12.coeff m = c) (ht1 : a1.coeff m = c * B) (ht2 : a2.coeff m = c * A)
    (ht0 : a0.coeff m = c * A * B)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < a1.eval t)
    (hR1 : ∀ t : ℝ, 0 ≤ a1.eval t * a2.eval t - a0.eval t * a12.eval t)
    (hR2 : ∀ t : ℝ, 0 ≤ a12.eval t * (derivative a1).eval t - a1.eval t * (derivative a12).eval t)
    (hR3 : ∀ η t : ℝ, 0 ≤
      (a1 + C η * a12).eval t *
          (derivative (a0 + C (-A) * a1 + C η * a2 + C (-A) * C η * a12)).eval t -
        (a0 + C (-A) * a1 + C η * a2 + C (-A) * C η * a12).eval t *
          (derivative (a1 + C η * a12)).eval t)
    (hS : ∀ x y z : ℂ, 0 < x.im → 0 < y.im → 0 < z.im →
      aeval z a0 + x * aeval z a1 + y * aeval z a2 + x * y * aeval z a12 ≠ 0) :
    0 ≤ a0.eval 0 - A * a1.eval 0 - B * a2.eval 0 + A * B * a12.eval 0 := by
  set V := a1 - C B * a12 with hV
  set W := a2 - C A * a12 with hW
  set Xp := a0 - C A * a1 - C B * a2 + C (A * B) * a12 with hXp
  have hgoal : Xp.eval 0 = a0.eval 0 - A * a1.eval 0 - B * a2.eval 0 + A * B * a12.eval 0 := by
    simp [hXp]
  rw [← hgoal]
  have hc0 : c ≠ 0 := hc.ne'
  have hU : a12.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero hd12 (by rw [ht12]; exact hc0)
  have ha1 : a1.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hd1 (by rw [ht1]; positivity)
  -- `t^n` coefficients of `V, W, X` vanish for `n ≥ m`
  have hVc : ∀ n, m ≤ n → V.coeff n = 0 := by
    intro n hn
    rcases hn.lt_or_eq with hn | rfl
    · simp [hV, coeff_eq_zero_of_le hd1 hn, coeff_eq_zero_of_le hd12 hn]
    · simp [hV, ht1, ht12]; ring
  have hWc : ∀ n, m ≤ n → W.coeff n = 0 := by
    intro n hn
    rcases hn.lt_or_eq with hn | rfl
    · simp [hW, coeff_eq_zero_of_le hd2 hn, coeff_eq_zero_of_le hd12 hn]
    · simp [hW, ht2, ht12]; ring
  have hXc : ∀ n, m ≤ n → Xp.coeff n = 0 := by
    intro n hn
    rcases hn.lt_or_eq with hn | rfl
    · simp [hXp, mul_assoc, coeff_C_mul, coeff_eq_zero_of_le hd0 hn, coeff_eq_zero_of_le hd1 hn,
        coeff_eq_zero_of_le hd2 hn, coeff_eq_zero_of_le hd12 hn]
    · simp [hXp, mul_assoc, coeff_C_mul, ht0, ht1, ht2, ht12]; ring
  have natDeg_of : ∀ P : ℝ[X], (∀ n, m ≤ n → P.coeff n = 0) → P.natDegree ≤ m - 1 := by
    intro P hP
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    exact hP n (by omega)
  have hVd := natDeg_of V hVc
  have hWd := natDeg_of W hWc
  have hXd := natDeg_of Xp hXc
  ------------------------------------------------------------------
  -- Step 1 (`step:sep-X`): `deg X ≤ m - 2`.
  have hXc' : ∀ n, m ≤ n + 1 → Xp.coeff n = 0 := by
    intro n hn
    rcases Nat.lt_or_ge n m with hlt | hge
    · have hnm : n = m - 1 := by omega
      subst hnm
      have hm1 : 1 ≤ m := by omega
      by_contra hχ
      set P := V * W - Xp * a12 with hP
      have hPev : ∀ t, P.eval t = a1.eval t * a2.eval t - a0.eval t * a12.eval t := by
        intro t; simp [hP, hV, hW, hXp]; ring
      have hVW : (V * W).natDegree ≤ (m - 1) + (m - 1) :=
        (natDegree_mul_le).trans (add_le_add hVd hWd)
      have hcoeff : P.coeff ((m - 1) + m) = -(Xp.coeff (m - 1) * c) := by
        rw [hP, coeff_sub, coeff_mul_add_eq_of_natDegree_le hXd hd12, ht12,
          coeff_eq_zero_of_natDegree_lt (by omega : (V * W).natDegree < (m - 1) + m)]
        ring
      have hPd : P.natDegree ≤ (m - 1) + m :=
        (natDegree_sub_le _ _).trans (max_le (hVW.trans (by omega))
          ((natDegree_mul_le).trans (add_le_add hXd hd12)))
      have hne : P.coeff ((m - 1) + m) ≠ 0 := by
        rw [hcoeff]; exact neg_ne_zero.mpr (mul_ne_zero hχ hc0)
      have hPdeg : P.natDegree = (m - 1) + m := natDegree_eq_of_le_of_coeff_ne_zero hPd hne
      have hP0 : P ≠ 0 := by rintro h; rw [h] at hne; simp at hne
      obtain ⟨t, ht⟩ := exists_eval_neg_of_odd_natDegree hP0
        (by rw [hPdeg]; exact ⟨m - 1, by omega⟩)
      have := hR1 t
      rw [← hPev] at this
      linarith
    · exact hXc n hge
  -- if `X = 0` we are done (this covers `m ≤ 1`)
  by_cases hX0 : Xp = 0
  · rw [hX0]; simp
  have hXdeg : Xp.natDegree + 2 ≤ m := by
    by_contra h
    have := hXc' Xp.natDegree (by omega)
    exact hX0 (leadingCoeff_eq_zero.mp this)
  have hm2 : 2 ≤ m := by omega
  ------------------------------------------------------------------
  -- Step 2 (`step:sep-r`): `r = a₁₂ / a₁ ≥ 1 / B` on `[0, ∞)`.
  have ha1ne : ∀ t, 0 ≤ t → a1.eval t ≠ 0 := fun t ht => (hpos t ht).ne'
  have hlim_r : Tendsto (fun t => a12.eval t / a1.eval t) atTop (𝓝 (1 / B)) := by
    have hdeg : a12.degree = a1.degree := by
      have h12 : a12 ≠ 0 := by rintro h; rw [h, natDegree_zero] at hU; omega
      have h1 : a1 ≠ 0 := by rintro h; rw [h, natDegree_zero] at ha1; omega
      rw [degree_eq_natDegree h12, degree_eq_natDegree h1, hU, ha1]
    have := div_tendsto_atTop_leadingCoeff_div_of_degree_eq a12 a1 hdeg
    rwa [leadingCoeff, leadingCoeff, hU, ha1, ht12, ht1,
      show c / (c * B) = 1 / B by field_simp] at this
  have hr := quot_ge_of_tendsto ha1ne (fun t _ => hR2 t) hlim_r
  ------------------------------------------------------------------
  -- Step 3 (`step:sep-Vsign`): `V = 0` or `V < 0` on `[0, ∞)`.
  have hVev : ∀ t, V.eval t = a1.eval t - B * a12.eval t := fun t => by simp [hV]
  have hVle : ∀ t, 0 ≤ t → V.eval t ≤ 0 := by
    intro t ht
    have h1 := (hr t ht).1
    have hp := hpos t ht
    rw [hVev, div_le_div_iff₀ hB hp] at *
    linarith
  have hVsign : V = 0 ∨ ∀ t, 0 ≤ t → V.eval t < 0 := by
    by_cases h : ∃ t₁, 0 ≤ t₁ ∧ V.eval t₁ = 0
    · left
      obtain ⟨t₁, ht₁, hV0⟩ := h
      have hr1 : a12.eval t₁ / a1.eval t₁ = 1 / B := by
        rw [hVev] at hV0
        have hp := hpos t₁ ht₁
        field_simp
        linarith
      have hprop := (hr t₁ ht₁).2 hr1
      apply eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := Set.Ici t₁) _ (Set.Ici_infinite t₁)
      intro t ht
      have ht' : t₁ ≤ t := ht
      have := hprop t ht'
      have hp := hpos t (le_trans ht₁ ht')
      show V.eval t = 0
      rw [hVev]
      field_simp at this
      linarith
    · right
      intro t ht
      exact lt_of_le_of_ne (hVle t ht) (fun h' => h ⟨t, ht, h'⟩)
  rcases hVsign with hV0 | hVneg
  ------------------------------------------------------------------
  -- Step 6 (`step:sep-V-zero`): `V = 0` forces `X = 0`.
  · exfalso
    have ha1eq : a1 = C B * a12 := by rw [hV] at hV0; exact sub_eq_zero.mp hV0
    have hquad : ∀ t y : ℝ, 0 ≤
        (a12.eval t * (derivative W).eval t - W.eval t * (derivative a12).eval t) * y ^ 2 +
        (a12.eval t * (derivative Xp).eval t - Xp.eval t * (derivative a12).eval t) * y := by
      intro t y
      have e1 : a1.eval t = B * a12.eval t := by rw [ha1eq]; simp
      have e1' : (derivative a1).eval t = B * (derivative a12).eval t := by rw [ha1eq]; simp
      have := hR3 (y - B) t
      simp only [hW, hXp, derivative_add, derivative_sub, derivative_mul, derivative_C, eval_add,
        eval_sub, eval_mul, eval_C, zero_mul, mul_zero,
        zero_add, add_zero, e1, e1'] at this ⊢
      linear_combination this
    have hwr : a12 * derivative Xp - Xp * derivative a12 = 0 := by
      apply Polynomial.funext
      intro t
      have := eq_zero_of_forall_quadratic_nonneg (hquad t)
      simpa using this
    exact wronskian_ne_zero (by omega) hX0 (by omega) hwr
  ------------------------------------------------------------------
  -- Steps 4–5 (`step:sep-Vdeg`, `step:sep-V-nonzero`): `V < 0` on `[0, ∞)`.
  · have hV0 : V ≠ 0 := by
      intro h; have := hVneg 0 le_rfl; rw [h] at this; simp at this
    have hVdeg : a1.natDegree = (-V).natDegree + 1 := by
      apply natDegree_eq_succ_of_im_nonpos (neg_ne_zero.mpr hV0)
      · rw [natDegree_neg, ha1]; omega
      · intro z hz
        have hNz : aeval z (-V) = (B : ℂ) * aeval z a12 - aeval z a1 := by
          simp [hV]
        rw [hNz]
        by_cases h1 : aeval z a1 = 0
        · simp [h1]
        by_cases h12 : aeval z a12 = 0
        · simp [h12, h1]
        have hTV : ArborealDecay.Stability.TwoVarZeroFree (aeval z a0) (aeval z a1) (aeval z a2)
            (aeval z a12) := fun x y hx hy => by
          have := hS x y z hx hy hz
          intro h; apply this; linear_combination h
        have him := hTV.im_div_nonneg_right h12
        have e : ((B : ℂ) * aeval z a12 - aeval z a1) / aeval z a1 =
            (B : ℂ) * (aeval z a1 / aeval z a12)⁻¹ - 1 := by
          field_simp
        rw [e]
        set w := aeval z a1 / aeval z a12
        have hn : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
        simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.inv_im, Complex.one_im, zero_mul, add_zero, sub_zero]
        have : 0 ≤ w.im / Complex.normSq w := div_nonneg him hn
        rw [neg_div]
        nlinarith
    have hVd' : V.natDegree = m - 1 := by rw [natDegree_neg] at hVdeg; omega
    have hR3' : ∀ t, 0 ≤ (-Xp).eval t * (derivative V).eval t -
        V.eval t * (derivative (-Xp)).eval t := by
      intro t
      have := hR3 (-B) t
      have e1 : a1 + C (-B) * a12 = V := by rw [hV]; simp only [map_neg]; ring
      have e2 : a0 + C (-A) * a1 + C (-B) * a2 + C (-A) * C (-B) * a12 = Xp := by
        rw [hXp]; simp only [map_neg, map_mul]; ring
      rw [e1, e2] at this
      simp only [derivative_neg, eval_neg]
      linarith
    have hlim : Tendsto (fun t => (-Xp).eval t / V.eval t) atTop (𝓝 0) :=
      div_tendsto_atTop_zero_of_degree_lt _ _
        (by rw [degree_neg]; exact degree_lt_degree (by omega))
    have h0 := (quot_ge_of_tendsto (fun t ht => (hVneg t ht).ne) (fun t _ => hR3' t) hlim
      0 le_rfl).1
    have hv := hVneg 0 le_rfl
    rw [eval_neg] at h0
    rcases div_nonneg_iff.mp h0 with h | h
    · linarith [h.2]
    · linarith [h.1]

end

end ArborealDecay.Separator
