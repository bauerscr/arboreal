import Step2.Lip.FlowLipCovH

/-!
# Comparison of one step along two histories: the inputs (Lipschitz bounds, part 16)

`Cmp R k t t' …` collects the hypotheses for comparing step `k` of two histories `t, t'`: both
in the domain (`DomH`), the mass condition, the radius `e` of the step, and the field scale
`ℓ_Δ` of the difference of the covariances. Under `Cmp`, the step data `sdH R k t`,
`sdH R k t'` satisfy the hypotheses of the one-step Lipschitz bounds (`Step2.Lip.FlowLipStep2`) at
the input scale `ℓ_i = 7ℓ/8`, with input differences bounded by the differences of the normalised
states (`dV`, `dW`, `dD`, `dWD`, `dKf`):
* `‖δV♭‖ ≤ aIn = c_M ℓ_i²(|δμ| + 2δv) + 4ℓ_i⁴(8/7 |δg| + 2|δn|)`;
* `‖δ𝒲‖ ≤ δW + 28 δζ c_w g²`, `‖δD‖, ‖δK‖ ≤ ‖δx‖ + 28 δζ c_x g³`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Err

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The errors of the normalised states of two histories at step `k`. -/
def evH (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ :=
  ‖zhH R k t' - zhH R k t‖ + ‖yhH R k t' - yhH R k t‖
def eWH (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ := (Fnorm k R.ℓ (WhH R k t' - WhH R k t)).toReal
def ewH (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ := ‖whH R k t' - whH R k t‖
def eζH (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ := ‖zetaH R k t' - zetaH R k t‖

theorem eWH_le (k : ℕ) (t t' : Hist.Seq (Xs R)) :
    Fnorm k R.ℓ (WhH R k t' - WhH R k t) ≤ ENNReal.ofReal (eWH R k t t') := by
  rw [eWH, ENNReal.ofReal_toReal (Fnorm_ne_top' Fact.out _)]

theorem eWH_nonneg (k : ℕ) (t t' : Hist.Seq (Xs R)) : 0 ≤ eWH R k t t' := ENNReal.toReal_nonneg

/-- The bound on the difference of `V♭`. -/
def aIn (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ :=
  aVf (7 / 8 * R.ℓ) |(t' k).2.1 - (t k).2.1| (evH R k t t') |(t' k).1 - (t k).1|
    ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖

/-- The bound on the difference of `𝒲^lin`. -/
def bWIn (cw : ℝ) (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ :=
  eWH R k t t' + 28 * eζH R k t t' * (cw * (t k).1 ^ 2)

/-- The bound on the difference of `D` and of `K`. -/
def bDIn (cx : ℝ) (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ :=
  ‖(t' k).2.2 - (t k).2.2‖ + 14 * (2 * eζH R k t t') * (cx * (t k).1 ^ 3)

/-- The bound on the difference of `K♭`. -/
def cIn (cx : ℝ) (k : ℕ) (t t' : Hist.Seq (Xs R)) : ℝ :=
  Real.exp 1 * bDIn R cx k t t' + 4 * (Real.exp 2 * (cx * (t k).1 ^ 3)) *
    (cM * (7 / 8 * R.ℓ) ^ 2 * (8 * evH R k t t') / (1 / 4))

end Err

/-- **The hypotheses for comparing step `k` of two histories.** -/
structure Cmp (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (k : ℕ)
    (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ) : Prop where
  H : DomH k t Λ κ cm cT ε cz cw
  H' : DomH k t' Λ κ cm cT ε cz cw
  hm : |R.msq| * ((L : ℝ) ^ k) ^ 2 ≤ 1
  hcw : 0 ≤ cw
  hcx : 0 ≤ cx κ cT
  hcmu : 0 ≤ cmu Λ cm
  hε1 : ε ≤ 1
  hΔ : cDl (7 / 8 * R.ℓ) cz * ε ≤ 1 / 4
  he : 0 < e
  he1 : cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) * ε ≤ e
  he2 : cw * ε ^ 2 + cx κ cT * ε ^ 3 ≤ e ^ 2
  he3 : Real.exp 1 * (cx κ cT * ε ^ 3) ≤ e ^ 2
  hℓΔ : 0 ≤ ℓΔ
  hC : GoodCov2 k ℓΔ (CvH R k t' - CvH R k t)

namespace Cmp

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e ℓΔ : ℝ} (H : Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ)
include H

theorem hℓ : 0 < R.ℓ := Fact.out
theorem hA : 0 < R.A := Fact.out

theorem sOK : SD.OK R k (sdH R k t) (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm) :=
  H.H.sdH_OK
theorem sOK' : SD.OK R k (sdH R k t') (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm) :=
  H.H'.sdH_OK

theorem small : cz * (t k).1 ≤ 1 / 16 := by
  have := H.H.czg; have := H.H.h16; linarith
theorem small' : cz * (t' k).1 ≤ 1 / 16 := by
  have := H.H'.czg; have := H.H'.h16; linarith

theorem cDl_g : cDl (7 / 8 * R.ℓ) cz * (t k).1 ≤ 1 / 4 := by
  have h0 : 0 ≤ cDl (7 / 8 * R.ℓ) cz := by
    unfold cDl; have := H.H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  exact (mul_le_mul_of_nonneg_left H.H.g_le h0).trans H.hΔ
theorem cDl_g' : cDl (7 / 8 * R.ℓ) cz * (t' k).1 ≤ 1 / 4 := by
  have h0 : 0 ≤ cDl (7 / 8 * R.ℓ) cz := by
    unfold cDl; have := H.H.hcz; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  exact (mul_le_mul_of_nonneg_left H.H'.g_le h0).trans H.hΔ

theorem cVf_nonneg : 0 ≤ cVf (7 / 8 * R.ℓ) cz (cmu Λ cm) := by
  unfold cVf; have := H.H.hcz; have := H.hcmu; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  positivity

/-- `‖V♭‖ ≤ e`. -/
theorem V_e : Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t)) ≤ ENNReal.ofReal e :=
  (H.sOK.V_le (by have := H.hℓ; positivity) H.H.hcz H.small H.hm).trans
    (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left H.H.g_le H.cVf_nonneg).trans H.he1))
theorem V_e' : Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t')) ≤ ENNReal.ofReal e :=
  (H.sOK'.V_le (by have := H.hℓ; positivity) H.H.hcz H.small' H.hm).trans
    (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left H.H'.g_le H.cVf_nonneg).trans H.he1))

theorem WD_e_of {g : ℝ} (hg0 : 0 < g) (hg : g ≤ ε) {s : SD L N}
    (hs : SD.OK R k s (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm)) (hsg : s.g = g) :
    Fnorm k (7 / 8 * R.ℓ) (s.W + s.D) ≤ ENNReal.ofReal (e ^ 2) := by
  have hcw := H.hcw
  have hcx := H.hcx
  have hsg0 : 0 < s.g := hsg ▸ hg0
  refine (Fnorm_add_le _ _ (by positivity) (by positivity) hs.hWn hs.hDn).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [hsg]
  have h2 : g ^ 2 ≤ ε ^ 2 := by gcongr
  have h3 : g ^ 3 ≤ ε ^ 3 := by gcongr
  have := mul_le_mul_of_nonneg_left h2 hcw
  have := mul_le_mul_of_nonneg_left h3 hcx
  linarith [H.he2]

theorem WD_e : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t).W + (sdH R k t).D) ≤ ENNReal.ofReal (e ^ 2) :=
  H.WD_e_of H.H.g_pos H.H.g_le H.sOK rfl
theorem WD_e' : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t').W + (sdH R k t').D) ≤ ENNReal.ofReal (e ^ 2) :=
  H.WD_e_of H.H'.g_pos H.H'.g_le H.sOK' rfl

theorem half_le_exp : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 4) * 2) := by
  have := Real.add_one_le_exp (-(1 / 4) * 2); linarith

theorem Kf_e_of {g : ℝ} (hg0 : 0 < g) (hg : g ≤ ε) {s : SD L N}
    (hs : SD.OK R k s (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm)) (hsg : s.g = g)
    (hsm : cz * s.g ≤ 1 / 16) (hΔ : cDl (7 / 8 * R.ℓ) cz * s.g ≤ 1 / 4) :
    Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k s) ≤ ENNReal.ofReal (e ^ 2) := by
  have hA := H.hA
  have h1 : R.A / 2 ≤ R.A * Real.exp (-(1 / 4)) := by
    have := Real.add_one_le_exp (-(1 / 4)); nlinarith
  refine (Knorm_mono_wt (by positivity) h1 _).trans ((hs.Kf_le (by have := H.hℓ; positivity)
    hA.le H.H.hcz hsm H.hm hΔ).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hsg]
  have h3 : g ^ 3 ≤ ε ^ 3 := by gcongr
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 H.hcx) (Real.exp_pos 1).le
  linarith [H.he3]

theorem Kf_e : Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t)) ≤ ENNReal.ofReal (e ^ 2) :=
  H.Kf_e_of H.H.g_pos H.H.g_le H.sOK rfl H.small H.cDl_g
theorem Kf_e' : Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t')) ≤ ENNReal.ofReal (e ^ 2) :=
  H.Kf_e_of H.H'.g_pos H.H'.g_le H.sOK' rfl H.small' H.cDl_g'

/-- **The difference of `V♭`.** -/
theorem dV : Fnorm k (7 / 8 * R.ℓ) (SD.V R k (sdH R k t') - SD.V R k (sdH R k t)) ≤
    ENNReal.ofReal (aIn R k t t') :=
  nVec_sub_le H.sOK H.sOK' (by have := H.hℓ; positivity) H.H.hcz H.small H.small'
    (H.H'.g_le.trans H.hε1) H.hm

/-- **The difference of `𝒲^lin`.** -/
theorem dW : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t').W - (sdH R k t).W) ≤
    ENNReal.ofReal (bWIn R cw k t t') :=
  WinH_sub_le H.H H.H' (eWH_nonneg R k t t') (eWH_le R k t t') H.hcw

/-- **The difference of `D`.** -/
theorem dD : Fnorm k (7 / 8 * R.ℓ) ((sdH R k t').D - (sdH R k t).D) ≤
    ENNReal.ofReal (bDIn R (cx κ cT) k t t') :=
  DinH_sub_le H.H H.H' H.hcx

/-- **The difference of `K`.** -/
theorem dK : Knorm k (7 / 8 * R.ℓ) R.A ((sdH R k t').K - (sdH R k t).K) ≤
    ENNReal.ofReal (bDIn R (cx κ cT) k t t') :=
  KinH_sub_le H.H H.H' H.hcx

theorem bWIn_nonneg : 0 ≤ bWIn R cw k t t' := by
  unfold bWIn eζH; have := eWH_nonneg R k t t'; have := H.hcw; positivity
theorem bDIn_nonneg : 0 ≤ bDIn R (cx κ cT) k t t' := by
  unfold bDIn eζH; have := H.hcx; have := H.H.g_pos; positivity
theorem cIn_nonneg : 0 ≤ cIn R (cx κ cT) k t t' := by
  unfold cIn evH; have := H.bDIn_nonneg; have := H.hcx; have := H.H.g_pos
  have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
theorem aIn_nonneg : 0 ≤ aIn R k t t' := by
  unfold aIn aVf evH; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity

/-- **The difference of `𝒲^lin + D`.** -/
theorem dWD : Fnorm k (7 / 8 * R.ℓ) (((sdH R k t').W + (sdH R k t').D) -
    ((sdH R k t).W + (sdH R k t).D)) ≤
    ENNReal.ofReal (bWIn R cw k t t' + bDIn R (cx κ cT) k t t') := by
  have e : ((sdH R k t').W + (sdH R k t').D) - ((sdH R k t).W + (sdH R k t).D) =
      ((sdH R k t').W - (sdH R k t).W) + ((sdH R k t').D - (sdH R k t).D) := by abel
  rw [e]
  exact Fnorm_add_le _ _ H.bWIn_nonneg H.bDIn_nonneg H.dW H.dD

/-- **The difference of `K♭`**, at the weight `A/2`. -/
theorem dKf : Knorm k (7 / 8 * R.ℓ) (R.A / 2) (SD.Kf R k (sdH R k t') - SD.Kf R k (sdH R k t)) ≤
    ENNReal.ofReal (cIn R (cx κ cT) k t t') := by
  have hA := H.hA
  have h1 : R.A / 2 ≤ R.A * Real.exp (-(1 / 4) * 2) := by
    have := H.half_le_exp; nlinarith
  refine (Knorm_mono_wt (by positivity) h1 _).trans ?_
  have h := nKf_sub_le H.sOK H.sOK' (by have := H.hℓ; positivity) hA H.H.hcz H.small H.small' H.hm
    H.cDl_g H.cDl_g' H.bDIn_nonneg H.dK H.hcx
  exact h

end Cmp

end

end Step2
