import Step2.Lip.FlowLipGH

/-!
# The final step: the differences of the couplings (Lipschitz bounds, part 28)

For two histories compared at step `j` (`Cmp`), with `Θ = Θ_j`:
* `d3_le`: `|δκ̂₃| ≤ 4β Θ + |δĝ|`;
* `dY_le`: `|δ(ν̃ - L²μ)| ≤ L² (4β Θ + 2 m² L^{2j} |δζ_j| + ℓ²/8 |δĝ| + 2|ĝ| ℓ_Δ²)`,
  `ν̃ = L^{2(j+1)} κ̂₂`;
* `dĝ_le`: `|δĝ| ≤ (1 + 2τ)|δg| + 2ε |δn|`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Diff

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e ℓΔ : ℝ}

theorem kap_rem_scaled (H : Cmp R j t t' Λ κ cm cT ε cz cw e ℓΔ) {Cq Cl cS : ℝ}
    (hkap : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
          (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
            (cIn R (cx κ cT) j t t') ℓΔ 1 (R.ℓ / 4)) (i : Fin 4) :
    cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
        (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ := by
  have h := hkap i
  rw [bRem_scale] at h
  have e2 : 4 * (e ^ 2 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) *
      relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
        (cIn R (cx κ cT) j t t') ℓΔ 1 (R.ℓ / 4) =
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        (e ^ 2 * relDist e (aIn R j t t') (bWIn R cw j t t' + bDIn R (cx κ cT) j t t')
          (cIn R (cx κ cT) j t t') ℓΔ 1 (R.ℓ / 4)) := by ring
  rwa [e2, thetaH_eq H] at h

/-- **The quartic coupling.** -/
theorem d3_le (H : Cmp R j t t' Λ κ cm cT ε cz cw e ℓΔ) {Cq Cl cS : ℝ}
    (hk : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
        (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ) :
    ‖kapH R j t' 3 - kapH R j t 3‖ ≤ 4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4))
      2 2 2 * thetaH R j t t' cw (cx κ cT) e ℓΔ + ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
  have h := hk 3
  rw [show cwt L j 3 = 1 from rfl, one_mul] at h
  have h3 := shv3_sub R j (sdH R j t) (sdH R j t') H.sOK.hzy H.sOK.hy H.sOK'.hzy H.sOK'.hy
  have := norm_add_le ((kapH R j t' 3 - kapH R j t 3) -
    (SD.shv R j (sdH R j t') 3 - SD.shv R j (sdH R j t) 3))
    (SD.shv R j (sdH R j t') 3 - SD.shv R j (sdH R j t) 3)
  rw [sub_add_cancel, h3] at this
  rw [h3] at h
  linarith

/-- **The relevant coupling minus its leading part.** -/
theorem dY_le (H : Cmp R j t t' Λ κ cm cT ε cz cw e ℓΔ) {Cq Cl cS : ℝ}
    (hk : ∀ i : Fin 4, cwt L j i * ‖(kapH R j t' i - kapH R j t i) -
        (SD.shv R j (sdH R j t') i - SD.shv R j (sdH R j t) i)‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ) :
    ‖((L : ℂ) ^ (2 * (j + 1)) * kapH R j t' 2 - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
        ((L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))‖ ≤
      (L : ℝ) ^ 2 * (4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ + 2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' +
        R.ℓ ^ 2 / 8 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ +
        2 * ‖ghat (sdH R j t)‖ * ℓΔ ^ 2) := by
  have h := hk 2
  rw [show cwt L j 2 = (L : ℝ) ^ (2 * j) from rfl] at h
  have hs := H.sOK
  have hs' := H.sOK'
  have e2 : ∀ (tt : Hist.Seq (Xs R)), DomH j tt Λ κ cm cT ε cz cw →
      SD.shv R j (sdH R j tt) 2 = ((tt j).2.1 : ℂ) / (L : ℂ) ^ (2 * j) -
        (zhH R j tt + yhH R j tt) * (1 + (zhH R j tt + yhH R j tt))⁻¹ * R.msq +
        4 * ghat (sdH R j tt) * dlC (sdH R j tt).C := fun tt Ht => by
    rw [shv_dom R j (sdH R j tt) Ht.sdH_OK.hzy Ht.sdH_OK.hy]; rfl
  have hLc : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  set f : ℂ → ℂ := fun z => z * (1 + z)⁻¹
  have e3 : ((L : ℂ) ^ (2 * (j + 1)) * kapH R j t' 2 - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ)) -
      ((L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)) =
      (L : ℂ) ^ 2 * ((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)) -
        (L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)) +
        4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t)) +
        4 * ghat (sdH R j t) * ((L : ℂ) ^ (2 * j) * dlC ((sdH R j t').C - (sdH R j t).C))) := by
    rw [e2 t' H.H', e2 t H.H, ← dlC_sub]
    simp only [f]
    field_simp
    ring
  rw [e3, norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hLj : ‖(L : ℂ) ^ (2 * j)‖ = (L : ℝ) ^ (2 * j) := by rw [norm_pow, Complex.norm_natCast]
  have hLL : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  -- the pieces
  have a1 : ‖(L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
      (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2))‖ ≤
      4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 *
        thetaH R j t t' cw (cx κ cT) e ℓΔ := by rw [norm_mul, hLj]; exact h
  have a2 : ‖(L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t))‖ ≤
      2 * (|R.msq| * ((L : ℝ) ^ j) ^ 2) * eζH R j t t' := by
    rw [norm_mul, norm_mul, hLj, Complex.norm_real, Real.norm_eq_abs]
    have hζ := norm_div_one_add_sub_le (H.H'.zy_le.trans (H.H'.czg.trans (by linarith [H.H'.h16])))
      (H.H.zy_le.trans (H.H.czg.trans (by linarith [H.H.h16])))
    rw [← H.H.zetaH_eq, ← H.H'.zetaH_eq] at hζ
    have e4 : (L : ℝ) ^ (2 * j) * |R.msq| = |R.msq| * ((L : ℝ) ^ j) ^ 2 := by ring
    rw [e4]
    have := mul_le_mul_of_nonneg_left hζ (by positivity : (0 : ℝ) ≤ |R.msq| * ((L : ℝ) ^ j) ^ 2)
    simp only [f, H.H.zetaH_eq, H.H'.zetaH_eq] at this ⊢
    unfold eζH; rw [H.H.zetaH_eq, H.H'.zetaH_eq]
    linarith only [this]
  have a3 : ‖4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t))‖ ≤
      R.ℓ ^ 2 / 8 * ‖ghat (sdH R j t') - ghat (sdH R j t)‖ := by
    rw [norm_mul, norm_mul, norm_mul, hLj, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hdl := H.H'.dl_le
    have b1 : (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t').C‖ ≤ R.ℓ ^ 2 / 32 := by
      have e5 : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC (sdH R j t').C‖ =
          (L : ℝ) ^ 2 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t').C‖) := by ring
      rw [e5] at hdl
      have h0 : 0 ≤ (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t').C‖ := by positivity
      have := le_mul_of_one_le_left h0 hLL
      linarith only [this, hdl]
    have := mul_le_mul_of_nonneg_right b1 (norm_nonneg (ghat (sdH R j t') - ghat (sdH R j t)))
    linarith only [this]
  have a4 : ‖4 * ghat (sdH R j t) * ((L : ℂ) ^ (2 * j) * dlC ((sdH R j t').C - (sdH R j t).C))‖ ≤
      2 * ‖ghat (sdH R j t)‖ * ℓΔ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hLj, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hsym : ∀ x y, ((sdH R j t').C - (sdH R j t).C) x y = ((sdH R j t').C - (sdH R j t).C) y x :=
      fun x y => by simp [Matrix.sub_apply, hs.hCsym x y, hs'.hCsym x y]
    have hCs : CSym ((sdH R j t').C - (sdH R j t).C) := fun T hT x y => by
      simp [Matrix.sub_apply, hs.hCs T hT x y, hs'.hCs T hT x y]
    have hdl : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ ≤ ℓΔ ^ 2 / 2 :=
      dlC_le' H.hC hCs hsym
    have b1 : (L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ ≤ ℓΔ ^ 2 / 2 := by
      have e5 : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ =
          (L : ℝ) ^ 2 * ((L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖) := by ring
      rw [e5] at hdl
      have h0 : 0 ≤ (L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖ := by positivity
      have := le_mul_of_one_le_left h0 hLL
      linarith only [this, hdl]
    have := mul_le_mul_of_nonneg_left b1 (norm_nonneg (ghat (sdH R j t)))
    have e6 : 4 * ‖ghat (sdH R j t)‖ * ((L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖) =
        4 * (‖ghat (sdH R j t)‖ * ((L : ℝ) ^ (2 * j) * ‖dlC ((sdH R j t').C - (sdH R j t).C)‖)) := by ring
    rw [e6]
    linarith only [this]
  have s1 := norm_add_le (((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)) -
        (L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)) +
        4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t))))
      (4 * ghat (sdH R j t) * ((L : ℂ) ^ (2 * j) * dlC ((sdH R j t').C - (sdH R j t).C)))
  have s2 := norm_add_le ((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)) -
        (L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)))
      (4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t').C) * (ghat (sdH R j t') - ghat (sdH R j t)))
  have s3 := norm_sub_le ((L : ℂ) ^ (2 * j) * ((kapH R j t' 2 - kapH R j t 2) -
        (SD.shv R j (sdH R j t') 2 - SD.shv R j (sdH R j t) 2)))
      ((L : ℂ) ^ (2 * j) * R.msq * (f (zhH R j t' + yhH R j t') - f (zhH R j t + yhH R j t)))
  linarith only [s1, s2, s3, a1, a2, a3, a4]

end Diff

end

end Step2
