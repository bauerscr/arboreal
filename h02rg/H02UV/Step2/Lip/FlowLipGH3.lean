import Step2.Lip.FlowLipGH2

/-!
# The final step: `G_j` and `m_j` through the normalised outputs (Lipschitz bounds, part 29)

`G_j = Re(κ̂₃ (1 + n₁)/(1 + ζ₁)²)` and `m_j = Re(P/(1 + ζ₁))`, `P = ν̃ - L²μ (1 + ζ₁)`, with
`ζ₁ = κ̂₀ + κ̂₁` (on the domain), `ν̃ = L^{2(j+1)} κ̂₂`, `n₁ = n(ν̃, ŵ_{j+1})` (`G_core`, `m_core`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Core

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

/-- `ν̃ = L^{2(j+1)} κ̂₂`. -/
abbrev nuT (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  (L : ℂ) ^ (2 * (j + 1)) * kapH R j t 2

theorem nCor_out (j : ℕ) (t : Hist.Seq (Xs R)) :
    nCor (kapH R j t 2) ((L : ℂ) ^ (2 * (j + 1)) * whH R (j + 1) t) =
      nCor (nuT R j t) (whH R (j + 1) t) := by
  unfold nCor; congr 1; ring

/-- `|ŵ_{j+1}| ≤ ℓ²`. -/
theorem DomH.whH_succ_le (H : DomH j t Λ κ cm cT ε cz cw) (hL2 : 2 ≤ L)
    (hnW : ‖nW1H R j t‖ ≤ R.ℓ ^ 2) : ‖whH R (j + 1) t‖ ≤ R.ℓ ^ 2 := by
  have HO := H.histOK
  have hs := H.sdH_OK
  have hk1 : j + 1 < N := by have := hs.hk; omega
  have hz : ‖∑ x, CvH R j t x 0‖ ≤ 9 * ((L : ℝ) ^ (j + 1)) ^ 2 * (R.ℓ / 4) ^ 2 :=
    zero_mode_le hk1 hs.hC
  have hL : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  rw [whH_succ HO]
  have hLp : (0 : ℝ) < (L : ℝ) ^ (2 * (j + 1)) := by positivity
  rw [norm_div, norm_pow, Complex.norm_natCast, div_le_iff₀ hLp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have e1 : (L : ℝ) ^ (2 * (j + 1)) = (L : ℝ) ^ 2 * (L : ℝ) ^ (2 * j) := by ring
  have e2 : ((L : ℝ) ^ (j + 1)) ^ 2 = (L : ℝ) ^ (2 * (j + 1)) := by ring
  rw [e2] at hz
  have h1 : ‖nW1H R j t‖ * (L : ℝ) ^ (2 * j) ≤ R.ℓ ^ 2 * (L : ℝ) ^ (2 * j) :=
    mul_le_mul_of_nonneg_right hnW (by positivity)
  have hLj : (0 : ℝ) ≤ (L : ℝ) ^ (2 * j) := by positivity
  have h2 : R.ℓ ^ 2 * (L : ℝ) ^ (2 * j) ≤ R.ℓ ^ 2 / 4 * (L : ℝ) ^ (2 * (j + 1)) := by
    rw [e1]
    have : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have hℓ := sq_nonneg R.ℓ
    nlinarith [mul_nonneg hℓ hLj]
  have h3 : 9 * (L : ℝ) ^ (2 * (j + 1)) * (R.ℓ / 4) ^ 2 = 9 / 16 * R.ℓ ^ 2 * (L : ℝ) ^ (2 * (j + 1)) := by
    ring
  have h4 := mul_nonneg (sq_nonneg R.ℓ) hLp.le
  linarith only [h1, h2, h3, hz, h4]

/-- On the domain, `ζ₁ = κ̂₀ + κ̂₁`. -/
theorem zeta1_eq (HO : HistOK R j t) (h : ‖kapH R j t 0 + kapH R j t 1‖ ≤ R.ρ) :
    zetaH R (j + 1) t = kapH R j t 0 + kapH R j t 1 := by
  rw [zetaH_succ HO, nZeta, clampDisk_of_le h]

/-- **`G_j` through the normalised outputs.** -/
theorem G_core (HO : HistOK R j t) (HO' : HistOK R j t') {s : ℝ} (hs : s ≤ 1 / 16)
    (hζ : ‖zetaH R (j + 1) t‖ ≤ s) (hζ' : ‖zetaH R (j + 1) t'‖ ≤ s)
    (hn : ‖nCor (nuT R j t) (whH R (j + 1) t)‖ ≤ s)
    (hn' : ‖nCor (nuT R j t') (whH R (j + 1) t')‖ ≤ s) :
    |(rgData R).G j t - (rgData R).G j t'| ≤ (1 + 4 * s) * ‖kapH R j t' 3 - kapH R j t 3‖ +
      ‖kapH R j t 3‖ * (2 * ‖nCor (nuT R j t') (whH R (j + 1) t') -
        nCor (nuT R j t) (whH R (j + 1) t)‖ + 5 * ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖) := by
  have h := G_lip (a := kapH R j t 3) (a' := kapH R j t' 3) hs hζ hζ' hn hn'
  show |(histOut R j t).g.re - (histOut R j t').g.re| ≤ _
  rw [histOut_g_norm HO, histOut_g_norm HO', nCor_out, nCor_out, abs_sub_comm, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans h

/-- **`m_j` through the normalised outputs.** -/
theorem m_core (HO : HistOK R j t) (HO' : HistOK R j t')
    (hζ : ‖zetaH R (j + 1) t‖ ≤ 1 / 8) (hζ' : ‖zetaH R (j + 1) t'‖ ≤ 1 / 8) :
    |(rgData R).m j t - (rgData R).m j t'| ≤
      2 * ‖(nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ) * (1 + zetaH R (j + 1) t')) -
        (nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ) * (1 + zetaH R (j + 1) t))‖ +
      2 * ‖nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ) * (1 + zetaH R (j + 1) t)‖ *
        ‖zetaH R (j + 1) t' - zetaH R (j + 1) t‖ := by
  have h := P_lip (P := nuT R j t - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ) * (1 + zetaH R (j + 1) t))
    (P' := nuT R j t' - (L : ℂ) ^ 2 * ((t' j).2.1 : ℂ) * (1 + zetaH R (j + 1) t')) hζ hζ'
  have hne : 1 + zetaH R (j + 1) t ≠ 0 := one_add_ne_zero (by linarith)
  have hne' : 1 + zetaH R (j + 1) t' ≠ 0 := one_add_ne_zero (by linarith)
  have key : ∀ (tt : Hist.Seq (Xs R)), HistOK R j tt → 1 + zetaH R (j + 1) tt ≠ 0 →
      (rgData R).m j tt = ((nuT R j tt - (L : ℂ) ^ 2 * ((tt j).2.1 : ℂ) *
        (1 + zetaH R (j + 1) tt)) / (1 + zetaH R (j + 1) tt)).re := fun tt Ht hn => by
    show (histOut R j tt).nu.re - (L : ℝ) ^ 2 * (tt j).2.1 = _
    rw [histOut_nu_norm Ht]
    have e : (nuT R j tt - (L : ℂ) ^ 2 * ((tt j).2.1 : ℂ) * (1 + zetaH R (j + 1) tt)) /
        (1 + zetaH R (j + 1) tt) = kapH R j tt 2 * (L : ℂ) ^ (2 * (j + 1)) /
          (1 + zetaH R (j + 1) tt) - (((L : ℝ) ^ 2 * (tt j).2.1 : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e, Complex.sub_re, Complex.ofReal_re]
  rw [key t HO hne, key t' HO' hne', abs_sub_comm, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans h

end Core

end

end Step2
