import Step2.Lip.FlowLipGA

/-!
# The final step: sizes along one history (Lipschitz bounds, part 27)

The sizes of the outputs of the normalised step `j` of a history in the domain: the couplings
`κ̂_{0,1}` (`O(ε)`), `κ̂_3` (`O(ε)`), `ν̃ = L^{2(j+1)} κ̂_2` and `ν̃ - L²μ` (`O(ε)`), and
`ŵ_{j+1}` (`≤ 2ℓ²`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

theorem bRem_mono {Cq Cl cS ℓi ℓ ℓC v w k v' w' k' : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (hv : 0 ≤ v) (hvv : v ≤ v') (hww : w ≤ w') (hkk : k ≤ k') :
    bRem L Cq Cl cS ℓi ℓ ℓC v w k ≤ bRem L Cq Cl cS ℓi ℓ ℓC v' w' k' := by
  unfold bRem
  have hσ := BHsig_mono (L := L) hv hvv hww
  have h1 : 0 ≤ Cq * (ℓi ^ 2)⁻¹ * cS * Cl := by
    have : 0 ≤ (ℓi ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _); positivity
  have h2 : 0 ≤ Cq * (ℓi ^ 4)⁻¹ * cS * Cl := by
    have : 0 ≤ (ℓi ^ 4)⁻¹ := inv_nonneg.2 (by positivity); positivity
  have h3 : 0 ≤ Cq * (ℓ ^ 2)⁻¹ * Cl * (L : ℝ) ^ 2 := by
    have : 0 ≤ (ℓ ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _); positivity
  have h4 : 0 ≤ Cq * (ℓ ^ 4)⁻¹ * Cl * (L : ℝ) ^ 2 := by
    have : 0 ≤ (ℓ ^ 4)⁻¹ := inv_nonneg.2 (by positivity); positivity
  have a1 := mul_le_mul_of_nonneg_left hkk h1
  have a2 := mul_le_mul_of_nonneg_left hkk h2
  have a3 := mul_le_mul_of_nonneg_left hσ h3
  have a4 := mul_le_mul_of_nonneg_left hσ h4
  have a5 := mul_le_mul_of_nonneg_right a2 (sq_nonneg ℓC)
  nlinarith

theorem bRem_scale_le {Cq Cl cS ℓi ℓ ℓC v w k c : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (hw : 0 ≤ w) (hk : 0 ≤ k) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    bRem L Cq Cl cS ℓi ℓ ℓC (c * v) (c ^ 2 * w) (c * k) ≤ c * bRem L Cq Cl cS ℓi ℓ ℓC v w k := by
  have hs : BH.sig 2 L (c * v) (c ^ 2 * w) = c ^ 2 * BH.sig 2 L v w := by unfold BH.sig; ring
  have hσ := BHsig_nonneg (L := L) (v := v) hw
  have hc2 : c ^ 2 ≤ c := by nlinarith
  unfold bRem
  rw [hs]
  have h3 : 0 ≤ Cq * (ℓ ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) := by
    have : 0 ≤ (ℓ ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _); positivity
  have h4 : 0 ≤ Cq * (ℓ ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) := by
    have : 0 ≤ (ℓ ^ 4)⁻¹ := inv_nonneg.2 (by positivity); positivity
  have e1 : Cq * (ℓ ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * (c ^ 2 * BH.sig 2 L v w))) =
      c ^ 2 * (Cq * (ℓ ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w))) := by ring
  have e2 : Cq * (ℓ ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * (c ^ 2 * BH.sig 2 L v w))) =
      c ^ 2 * (Cq * (ℓ ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w))) := by ring
  rw [e1, e2]
  have a3 := mul_le_mul_of_nonneg_right hc2 h3
  have a4 := mul_le_mul_of_nonneg_right hc2 h4
  have e3 : ∀ X : ℝ, X * (cS * (Cl * (c * k))) = c * (X * (cS * (Cl * k))) := fun X => by ring
  rw [e3, e3, show 2 * (c * (Cq * (ℓi ^ 4)⁻¹ * (cS * (Cl * k)))) * ℓC ^ 2 =
    c * (2 * (Cq * (ℓi ^ 4)⁻¹ * (cS * (Cl * k))) * ℓC ^ 2) by ring]
  linarith

/-- The `M = 1` remainder constant. -/
def bR1 (L : ℕ) (Cq Cl cS ℓ cE cxx : ℝ) : ℝ :=
  bRem L Cq Cl cS (7 / 8 * ℓ) ℓ (ℓ / 4) cE (cE ^ 2) (Real.exp 1 * cxx)

theorem bR1_nonneg {Cq Cl cS ℓ cE cxx : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl) (hcS : 0 ≤ cS)
    (hcx : 0 ≤ cxx) : 0 ≤ bR1 L Cq Cl cS ℓ cE cxx := by
  unfold bR1 bRem
  have := BHsig_nonneg (L := L) (v := cE) (sq_nonneg cE)
  have : 0 ≤ ((7 / 8 * ℓ) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  have : 0 ≤ ((7 / 8 * ℓ) ^ 4)⁻¹ := inv_nonneg.2 (by positivity)
  have : 0 ≤ (ℓ ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  have : 0 ≤ (ℓ ^ 4)⁻¹ := inv_nonneg.2 (by positivity)
  positivity

section Sizes

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

/-- `L^{2(j+1)} |δ| ≤ ℓ²/32` for the covariance of the step. -/
theorem DomH.dl_le (H : DomH j t Λ κ cm cT ε cz cw) :
    ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC (sdH R j t).C‖ ≤ R.ℓ ^ 2 / 32 := by
  have hs := H.sdH_OK
  have := dlC_le' hs.hC hs.hCs hs.hCsym
  have e : (R.ℓ / 4) ^ 2 / 2 = R.ℓ ^ 2 / 32 := by ring
  linarith

/-- **The sizes at the final step.** -/
theorem DomH.sizes (H : DomH j t Λ κ cm cT ε cz cw) {Cq Cl cS : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (hcw : 0 ≤ cw) (hcx : 0 ≤ cx κ cT) (hcmu : 0 ≤ cmu Λ cm) (hε1 : ε ≤ 1)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hrem : ∀ i : Fin 4, cwt L j i * ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ ≤
        bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1)
          ((cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) * (t j).1) ^ 2)
          (Real.exp 1 * (cx κ cT * (t j).1 ^ 3))) :
    let b₁ := bR1 L Cq Cl cS R.ℓ (cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm)) (cx κ cT)
    ‖kapH R j t 0‖ + ‖kapH R j t 1‖ ≤ ε * (2 * b₁ + R.ℓ ^ 2 / 4) ∧
      ‖kapH R j t 3‖ ≤ ε * (b₁ + 2) ∧
      ‖(L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)‖ ≤
        ε * ((L : ℝ) ^ 2 * (b₁ + 3 * cz + R.ℓ ^ 2 / 7)) ∧
      ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
  intro b₁
  have hℓ : 0 < R.ℓ := Fact.out
  have hs := H.sdH_OK
  have hg := H.g_pos
  have hgε := H.g_le
  have hε0 : 0 ≤ ε := hg.le.trans hgε
  set cE := cEr R.ℓ cz cw (cx κ cT) (cmu Λ cm) with hcE
  have hcV : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
    unfold cVf; have := H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hcE0 : 0 ≤ cE := by rw [hcE]; unfold cEr; positivity
  -- the remainder
  have hB : bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cE * (t j).1) ((cE * (t j).1) ^ 2)
      (Real.exp 1 * (cx κ cT * (t j).1 ^ 3)) ≤ ε * b₁ := by
    have h1 : bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (cE * (t j).1) ((cE * (t j).1) ^ 2)
        (Real.exp 1 * (cx κ cT * (t j).1 ^ 3)) ≤ bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4)
          (ε * cE) (ε ^ 2 * cE ^ 2) (ε * (Real.exp 1 * cx κ cT)) := by
      refine bRem_mono hCq hCl hcS (by positivity) (by nlinarith) (by
        have : ((t j).1) ^ 2 ≤ ε ^ 2 := by gcongr
        nlinarith [sq_nonneg cE]) ?_
      have h3 : (t j).1 ^ 3 ≤ ε := by
        have : (t j).1 ^ 3 ≤ ε ^ 3 := by gcongr
        have : ε ^ 3 ≤ ε := by
          have := pow_le_pow_of_le_one hε0 hε1 (show 1 ≤ 3 by norm_num); simpa using this
        linarith
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg (Real.exp_pos 1).le hcx)
      nlinarith [Real.exp_pos 1]
    refine h1.trans (bRem_scale_le hCq hCl hcS (sq_nonneg _) (by positivity) hε0 hε1)
  have hr : ∀ i : Fin 4, cwt L j i * ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ ≤ ε * b₁ :=
    fun i => (hrem i).trans hB
  have hsh := shv_le R j (sdH R j t) hs.hzy hs.hy hs.hC
  have hĝ : ‖ghat (sdH R j t)‖ ≤ 8 / 7 * ε := by
    have := norm_ghat_le (sdH R j t)
    have h2 : |(sdH R j t).g| ≤ ε := by show |(t j).1| ≤ ε; rw [abs_of_pos hg]; exact hgε
    linarith
  have hc01 : cwt L j 0 = 1 ∧ cwt L j 1 = 1 ∧ cwt L j 3 = 1 ∧ cwt L j 2 = (L : ℝ) ^ (2 * j) :=
    ⟨rfl, rfl, rfl, rfl⟩
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have r3 := hr 3
  rw [hc01.1, one_mul] at r0
  rw [hc01.2.1, one_mul] at r1
  rw [hc01.2.2.1, one_mul] at r3
  rw [hc01.2.2.2] at r2
  have tri : ∀ i : Fin 4, ‖kapH R j t i‖ ≤ ‖kapH R j t i - SD.shv R j (sdH R j t) i‖ +
      ‖SD.shv R j (sdH R j t) i‖ := fun i => by
    have := norm_add_le (kapH R j t i - SD.shv R j (sdH R j t) i) (SD.shv R j (sdH R j t) i)
    simpa using this
  refine ⟨?_, ?_, ?_, hĝ⟩
  · have t0 := tri 0
    have t1 := tri 1
    have h1 : 3 * (R.ℓ / 4) ^ 2 * ‖ghat (sdH R j t)‖ ≤ 3 * (R.ℓ / 4) ^ 2 * (8 / 7 * ε) :=
      mul_le_mul_of_nonneg_left hĝ (by positivity)
    have e1 : 3 * (R.ℓ / 4) ^ 2 * (8 / 7 * ε) = ε * (3 * R.ℓ ^ 2 / 14) := by ring
    have h2 : ε * (3 * R.ℓ ^ 2 / 14) ≤ ε * (R.ℓ ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg R.ℓ]) hε0
    have e2 : ε * (2 * b₁ + R.ℓ ^ 2 / 4) = ε * b₁ + ε * b₁ + ε * (R.ℓ ^ 2 / 4) := by ring
    linarith only [t0, t1, r0, r1, hsh.1, h1, e1, h2, e2]
  · have t3 := tri 3
    rw [hsh.2] at t3
    have e2 : ε * (b₁ + 2) = ε * b₁ + 2 * ε := by ring
    linarith only [t3, r3, hĝ, e2, hε0]
  · -- the relevant coupling
    have hsh2 := shv_dom R j (sdH R j t) hs.hzy hs.hy
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hLc : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
    have e2 : SD.shv R j (sdH R j t) 2 = ((t j).2.1 : ℂ) / (L : ℂ) ^ (2 * j) -
        (zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq +
        4 * ghat (sdH R j t) * dlC (sdH R j t).C := by
      rw [hsh2]; rfl
    have e3 : (L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2 - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ) =
        (L : ℂ) ^ 2 * ((L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2) -
          (L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq) +
          4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t).C) * ghat (sdH R j t)) := by
      rw [e2]; field_simp; ring
    rw [e3, norm_mul, norm_pow, Complex.norm_natCast]
    have hLj : ‖(L : ℂ) ^ (2 * j)‖ = (L : ℝ) ^ (2 * j) := by
      rw [norm_pow, Complex.norm_natCast]
    have a1 : ‖(L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2)‖ ≤ ε * b₁ := by
      rw [norm_mul, hLj]; exact r2
    have hζ8 : ‖zhH R j t + yhH R j t‖ ≤ 2 * cz * ε := H.zy_le.trans H.czg
    have hζ16 : ‖zhH R j t + yhH R j t‖ ≤ 1 / 8 := hζ8.trans (by linarith [H.h16])
    have a2 : ‖(L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ *
        R.msq)‖ ≤ 3 * cz * ε := by
      rw [norm_mul, norm_mul, norm_mul, hLj, Complex.norm_real, Real.norm_eq_abs]
      have b1 := norm_inv_one_add_le hζ16
      have e4 : (L : ℝ) ^ (2 * j) * (‖zhH R j t + yhH R j t‖ * ‖(1 + (zhH R j t + yhH R j t))⁻¹‖ *
          |R.msq|) = ‖zhH R j t + yhH R j t‖ * ‖(1 + (zhH R j t + yhH R j t))⁻¹‖ *
          (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by ring
      rw [e4]
      have b2 : ‖zhH R j t + yhH R j t‖ * ‖(1 + (zhH R j t + yhH R j t))⁻¹‖ ≤ 2 * cz * ε * (8 / 7) :=
        mul_le_mul hζ8 b1 (norm_nonneg _) (by have := H.hcz; positivity)
      have b3 := mul_le_mul b2 hm (by positivity) (by have := H.hcz; positivity)
      have hce : 0 ≤ cz * ε := mul_nonneg H.hcz hε0
      linarith only [b3, hce]
    have a3 : ‖4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t).C) * ghat (sdH R j t)‖ ≤
        ε * (R.ℓ ^ 2 / 7) := by
      rw [norm_mul, norm_mul, norm_mul, hLj, show ‖(4 : ℂ)‖ = 4 by norm_num]
      have hdl := H.dl_le
      have hLL : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
      have b1 : (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖ ≤ R.ℓ ^ 2 / 32 := by
        have e5 : ((L : ℝ) ^ (j + 1)) ^ 2 * ‖dlC (sdH R j t).C‖ =
            (L : ℝ) ^ 2 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖) := by ring
        rw [e5] at hdl
        have h0 : 0 ≤ (L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖ := by positivity
        have := le_mul_of_one_le_left h0 hLL
        linarith only [this, hdl]
      have := mul_le_mul b1 hĝ (norm_nonneg _) (by positivity)
      have e7 : 4 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖) * ‖ghat (sdH R j t)‖ =
          4 * ((L : ℝ) ^ (2 * j) * ‖dlC (sdH R j t).C‖ * ‖ghat (sdH R j t)‖) := by ring
      rw [e7]
      linarith only [this]
    have hsum := norm_add_le ((L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2) -
      (L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq))
      (4 * ((L : ℂ) ^ (2 * j) * dlC (sdH R j t).C) * ghat (sdH R j t))
    have hsub := norm_sub_le ((L : ℂ) ^ (2 * j) * (kapH R j t 2 - SD.shv R j (sdH R j t) 2))
      ((L : ℂ) ^ (2 * j) * ((zhH R j t + yhH R j t) * (1 + (zhH R j t + yhH R j t))⁻¹ * R.msq))
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left (hsum.trans (add_le_add (hsub.trans (add_le_add a1 a2)) a3))
      hL2
    have e6 : (L : ℝ) ^ 2 * (ε * b₁ + 3 * cz * ε + ε * (R.ℓ ^ 2 / 7)) =
        ε * ((L : ℝ) ^ 2 * (b₁ + 3 * cz + R.ℓ ^ 2 / 7)) := by ring
    linarith only [this, e6]

end Sizes

end

end Step2
