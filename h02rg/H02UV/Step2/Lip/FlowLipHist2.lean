import Step2.Lip.FlowLipStep2
import Step2.Flow.FlowHist

/-!
# The step data along a history (Lipschitz bounds, part 14)

`sdH R k t` is the datum of the normalised step `k` of the history `t` (`Step2.Lip.FlowLipHist`). On
the domain (`DomH`: validity, `t_k ∈ D_ε`, the a priori bounds `APB`) it satisfies `SD.OK` at
the input field scale `ℓ_i = 7ℓ/8`, Gram scale `ℓ/4` (`sdH_OK`). For two histories the input
differences are bounded by the differences of the normalised states (`WinH_sub_le`,
`DinH_sub_le`, `KinH_sub_le`), and the difference of the covariances is a good covariance at the
scale `ℓ_Δ` of `prop_C5_lip` (`CvH_sub_good`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

theorem Fnorm_mono_ell {j : ℕ} {ℓ ℓ' : ℝ} (hℓ : 0 < ℓ) (h : ℓ ≤ ℓ') (F : Fam 2 L N) :
    Fnorm j ℓ F ≤ Fnorm j ℓ' F := by
  unfold Fnorm
  gcongr with b hb
  exact tNorm_mono (by positivity) le_rfl hℓ h _

theorem Knorm_mono_ell {j : ℕ} {ℓ ℓ' A : ℝ} (hℓ : 0 < ℓ) (h : ℓ ≤ ℓ') (K : Act 2 L N) :
    Knorm j ℓ A K ≤ Knorm j ℓ' A K := by
  unfold Knorm
  gcongr with X hX
  exact tNorm_mono (by positivity) le_rfl hℓ h _

/-- `‖σ_c F‖_{θℓ} ≤ ‖F‖_ℓ` for `|c| θ ≤ 1`. -/
theorem Fnorm_sigF_le_of {j : ℕ} {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ : 0 < θ) {c : ℂ} (hc : c ≠ 0)
    (hcθ : ‖c‖ * θ ≤ 1) (F : Fam 2 L N) : Fnorm j (θ * ℓ) (sigF c F) ≤ Fnorm j ℓ F := by
  rw [Fnorm_sigF_cscale (by positivity) hc, ← mul_assoc]
  exact Fnorm_mono_ell (by have := norm_pos_iff.2 hc; positivity) (by nlinarith) F

theorem Knorm_sigK_le_of {j : ℕ} {ℓ θ A : ℝ} (hℓ : 0 < ℓ) (hθ : 0 < θ) {c : ℂ} (hc : c ≠ 0)
    (hcθ : ‖c‖ * θ ≤ 1) (K : Act 2 L N) : Knorm j (θ * ℓ) A (sigK c K) ≤ Knorm j ℓ A K := by
  rw [Knorm_sigK_cscale (by positivity) hc, ← mul_assoc]
  exact Knorm_mono_ell (by have := norm_pos_iff.2 hc; positivity) (by nlinarith) K

/-- **The difference of two rescaled families** at the reduced scale `θℓ`. -/
theorem Fnorm_sigF_sub_le {j : ℕ} {ℓ θ τ : ℝ} (hℓ : 0 < ℓ) (hθ : 0 < θ) (hτ : 0 < τ) {c c' : ℂ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hcθ : ‖c'‖ * θ ≤ 1) (hcτ : θ * ‖c‖ ≤ 1 - τ)
    (hcτ' : θ * ‖c'‖ ≤ 1 - τ) (F F' : Fam 2 L N) {f df : ℝ}
    (hF : Fnorm j ℓ F ≤ ENNReal.ofReal f) (hdF : Fnorm j ℓ (F' - F) ≤ ENNReal.ofReal df)
    (hf : 0 ≤ f) (hdf : 0 ≤ df) :
    Fnorm j (θ * ℓ) (sigF c' F' - sigF c F) ≤ ENNReal.ofReal (df + θ * ‖c' - c‖ / τ * f) := by
  have e : sigF c' F' - sigF c F = sigF c' (F' - F) + (sigF c' F - sigF c F) := by
    rw [sigF_sub]; abel
  rw [e]
  refine (Fnorm_add_le' _ _).trans ?_
  rw [ENNReal.ofReal_add hdf (by positivity)]
  refine add_le_add ((Fnorm_sigF_le_of hℓ hθ hc' hcθ _).trans hdF) ?_
  have e2 : Fnorm j (θ * ℓ) (sigF c' F - sigF c F) =
      Fnorm j ℓ (sigF ((θ : ℂ) * c') F - sigF ((θ : ℂ) * c) F) := by
    rw [← Fnorm_sigF hℓ hθ, sigF_sub, sigF_sigF, sigF_sigF]
  rw [e2]
  have h1 : ‖(θ : ℂ) * c'‖ ≤ 1 - τ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]; exact hcτ'
  have h2 : ‖(θ : ℂ) * c‖ ≤ 1 - τ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]; exact hcτ
  refine (Fnorm_sigF_csub_le hℓ hτ h1 h2 F).trans ?_
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ,
    ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_right hF _

theorem Knorm_sigK_sub_le {j : ℕ} {ℓ θ τ A : ℝ} (hℓ : 0 < ℓ) (hθ : 0 < θ) (hτ : 0 < τ) {c c' : ℂ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hcθ : ‖c'‖ * θ ≤ 1) (hcτ : θ * ‖c‖ ≤ 1 - τ)
    (hcτ' : θ * ‖c'‖ ≤ 1 - τ) (K K' : Act 2 L N) {f df : ℝ}
    (hK : Knorm j ℓ A K ≤ ENNReal.ofReal f) (hdK : Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal df)
    (hf : 0 ≤ f) (hdf : 0 ≤ df) :
    Knorm j (θ * ℓ) A (sigK c' K' - sigK c K) ≤ ENNReal.ofReal (df + θ * ‖c' - c‖ / τ * f) := by
  have e : sigK c' K' - sigK c K = sigK c' (K' - K) + (sigK c' K - sigK c K) := by
    rw [sigK_sub]; abel
  rw [e]
  refine (Knorm_add_le j _ A _ _).trans ?_
  rw [ENNReal.ofReal_add hdf (by positivity)]
  refine add_le_add ((Knorm_sigK_le_of hℓ hθ hc' hcθ _).trans hdK) ?_
  have e2 : Knorm j (θ * ℓ) A (sigK c' K - sigK c K) =
      Knorm j ℓ A (sigK ((θ : ℂ) * c') K - sigK ((θ : ℂ) * c) K) := by
    rw [← Knorm_sigK hℓ hθ, sigK_sub, sigK_sigK, sigK_sigK]
  rw [e2]
  have h1 : ‖(θ : ℂ) * c'‖ ≤ 1 - τ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]; exact hcτ'
  have h2 : ‖(θ : ℂ) * c‖ ≤ 1 - τ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]; exact hcτ
  refine (Knorm_sigK_csub_le hℓ hτ h1 h2 K).trans ?_
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ,
    ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_right hK _

theorem norm_inv_csq_le16 {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 16) : ‖(csq (1 + ζ))⁻¹‖ ≤ 16 / 15 := by
  have h1 := norm_csq_sub_one_le ζ
  have h2 := Complex.abs_re_le_norm (csq (1 + ζ) - 1)
  have : (csq (1 + ζ) - 1).re = (csq (1 + ζ)).re - 1 := by simp
  rw [this] at h2
  have h3 := (abs_le.1 (h2.trans h1)).1
  have h4 : 15 / 16 ≤ ‖csq (1 + ζ)‖ := le_trans (by linarith) (Complex.re_le_norm _)
  rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The datum of the normalised step `k` of a history.** -/
def sdH (k : ℕ) (t : Hist.Seq (Xs R)) : SD L N :=
  ⟨CvH R k t, zhH R k t, yhH R k t, (t k).1, (t k).2.1, nW1H R k t, WinH R k t, DinH R k t,
    KinH R k t⟩

variable {R}

/-- **The domain at step `k`**: validity, `t_k ∈ D_ε`, the a priori bounds, and the smallness
`2 c_z ε ≤ min(ρ, 1/16)`. -/
structure DomH (k : ℕ) (t : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw : ℝ) : Prop where
  hV : ∀ i ≤ k, ValidAt R i
  hD : Hist.InD3 Λ κ cm cT ε (t k)
  hA : APB R cz cw (t k).1 (rawHist R k t) k
  hcz : 0 ≤ cz
  hρ : 2 * cz * ε ≤ R.ρ
  h16 : 2 * cz * ε ≤ 1 / 16

namespace DomH

variable {k : ℕ} {t : Hist.Seq (Xs R)} {Λ κ cm cT ε cz cw : ℝ}
  (H : DomH k t Λ κ cm cT ε cz cw)
include H

theorem g_pos : 0 < (t k).1 := H.hD.1
theorem g_le : (t k).1 ≤ ε := H.hD.2.1

theorem czg : 2 * cz * (t k).1 ≤ 2 * cz * ε :=
  mul_le_mul_of_nonneg_left H.g_le (by have := H.hcz; positivity)

theorem zh_le : ‖zhH R k t‖ ≤ cz * (t k).1 := H.hA.1
theorem yh_le : ‖yhH R k t‖ ≤ cz * (t k).1 := H.hA.2.1

theorem zy_le : ‖zhH R k t + yhH R k t‖ ≤ 2 * cz * (t k).1 :=
  (norm_add_le _ _).trans (by linarith [H.zh_le, H.yh_le])

theorem zetaH_eq : zetaH R k t = zhH R k t + yhH R k t := by
  rw [zetaH, absorbZeta, add_div]
  exact clampDisk_of_le (H.zy_le.trans (H.czg.trans H.hρ))

theorem zetaH_le : ‖zetaH R k t‖ ≤ 2 * cz * (t k).1 := by rw [H.zetaH_eq]; exact H.zy_le

theorem zetaH_16 : ‖zetaH R k t‖ ≤ 1 / 16 := H.zetaH_le.trans (H.czg.trans H.h16)

theorem histOK : HistOK R k t := by
  have hV0 := H.hV 0 (Nat.zero_le _)
  have hρ0 := hV0.2.2.2.1
  have hρ8 := hV0.2.2.2.2.1
  have HI := rawInv_hist R hρ0 k (fun i hi => H.hV i (by omega)) t
  exact ⟨HI.Z_ne_zero (by linarith), H.zetaH_16.trans (by norm_num)⟩

theorem rawInv : RawInv R k (rawHist R k t) :=
  rawInv_hist R (H.hV 0 (Nat.zero_le _)).2.2.2.1 k (fun i hi => H.hV i (by omega)) t

theorem uH_div : uH R k t / uH R (k + 1) t = (csq (1 + zetaH R k t))⁻¹ := by
  have hu := H.histOK.u_ne
  rw [show uH R (k + 1) t = uH R k t * csq (1 + zetaH R k t) from rfl]
  field_simp

theorem cxH_eq : cxH R k t = (csq (1 + zetaH R k t))⁻¹ := H.uH_div

theorem norm_cW : ‖uH R k t / uH R (k + 1) t‖ ≤ 16 / 15 := by
  rw [H.uH_div]; exact norm_inv_csq_le16 H.zetaH_16

theorem norm_cx : ‖cxH R k t‖ ≤ 16 / 15 := by
  rw [H.cxH_eq]
  exact norm_inv_csq_le16 H.zetaH_16

theorem cW_ne : uH R k t / uH R (k + 1) t ≠ 0 :=
  div_ne_zero H.histOK.u_ne H.histOK.u_succ_ne

theorem cx_ne : cxH R k t ≠ 0 := H.cW_ne

/-- `‖Ŵ_k‖_ℓ ≤ c_w g²`. -/
theorem WhH_le : Fnorm k R.ℓ (WhH R k t) ≤ ENNReal.ofReal (cw * (t k).1 ^ 2) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hu := H.histOK.u_ne
  rw [WhH, Fnorm_sigF_cscale hℓ (inv_ne_zero hu)]
  have hs : ‖(uH R k t)⁻¹‖ = fscale (rawHist R k t).Z := by
    rw [norm_inv, fscale, ← norm_uH_sq, Real.sqrt_inv, Real.sqrt_sq (norm_nonneg _)]
  rw [hs]
  exact H.hA.2.2

theorem WhH_mem : WhH R k t ∈ BSub (L := L) (N := N) k := sigF_mem H.rawInv.hWl _

theorem x1_le : Fnorm k R.ℓ (t k).2.2.1.toFam ≤ ENNReal.ofReal (cx κ cT * (t k).1 ^ 3) := by
  rw [BSp.Fnorm_le]
  exact ENNReal.ofReal_le_ofReal ((norm_fst_le _).trans H.hD.2.2.2)

theorem x2_le : Knorm k R.ℓ R.A (t k).2.2.2.toAct ≤ ENNReal.ofReal (cx κ cT * (t k).1 ^ 3) := by
  rw [ASp.Knorm_eq]
  exact ENNReal.ofReal_le_ofReal ((norm_snd_le _).trans H.hD.2.2.2)

/-- **The step datum of a history is admissible.** -/
theorem sdH_OK : SD.OK R k (sdH R k t) (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm) where
  hk := (H.hV k le_rfl).1
  hC := by
    obtain ⟨hC, -, -, -⟩ := H.rawInv.cov (H.hV k le_rfl)
    have hC' := hC.smul (uH R (k + 1) t ^ 2)
    have hu := H.histOK.u_succ_ne
    have e : Real.sqrt ‖uH R (k + 1) t ^ 2‖ * (fscale ((rawHist R k t).Z *
        (1 + absorbZeta R (rawHist R k t).Z ((rawHist R k t).z + (rawHist R k t).y))) * R.ℓ / 4) =
        R.ℓ / 4 := by
      have hZ1 : (rawHist R k t).Z * (1 + absorbZeta R (rawHist R k t).Z
          ((rawHist R k t).z + (rawHist R k t).y)) = uH R (k + 1) t ^ 2 := (uH_succ_sq k t).symm
      rw [hZ1, fscale, norm_pow, Real.sqrt_sq (norm_nonneg _), Real.sqrt_inv,
        Real.sqrt_sq (norm_nonneg _)]
      have := norm_pos_iff.2 hu
      field_simp
    rw [e] at hC'
    exact hC'
  hCt := by
    obtain ⟨-, hCt, -, -⟩ := H.rawInv.cov (H.hV k le_rfl)
    intro a x y
    simp only [sdH, CvH, nCov, Matrix.smul_apply]
    rw [hCt a x y]
  hCs := by
    obtain ⟨-, -, hCs, -⟩ := H.rawInv.cov (H.hV k le_rfl)
    intro T hT x y
    simp only [sdH, CvH, nCov, Matrix.smul_apply]
    rw [hCs T hT x y]
  hCsym := by
    obtain ⟨-, -, -, hCsym⟩ := H.rawInv.cov (H.hV k le_rfl)
    intro x y
    simp only [sdH, CvH, nCov, Matrix.smul_apply]
    rw [hCsym x y]
  hzy := H.zy_le.trans (H.czg.trans H.hρ)
  hy := H.yh_le.trans (by have := H.czg; have := H.hρ; have := H.hcz; have := H.g_pos; nlinarith)
  hz' := H.zh_le
  hy' := H.yh_le
  hg := H.g_pos
  hμ := H.hD.2.2.1
  hW := sigF_mem H.WhH_mem _
  hD := sigF_mem (t k).2.2.1.mem _
  hK := sigK_mem (t k).2.2.2.mem _
  hWn := by
    have hℓ : 0 < R.ℓ := Fact.out
    refine (Fnorm_sigF_le_of hℓ (by norm_num) H.cW_ne (by have := H.norm_cW; nlinarith) _).trans
      H.WhH_le
  hDn := by
    have hℓ : 0 < R.ℓ := Fact.out
    refine (Fnorm_sigF_le_of hℓ (by norm_num) H.cx_ne (by have := H.norm_cx; nlinarith) _).trans
      H.x1_le
  hKn := by
    have hℓ : 0 < R.ℓ := Fact.out
    refine (Knorm_sigK_le_of hℓ (by norm_num) H.cx_ne (by have := H.norm_cx; nlinarith) _).trans
      H.x2_le

end DomH

end Hist

section Two

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw : ℝ}

/-- **The difference of the inputs `𝒲^lin`.** -/
theorem WinH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw) {eW : ℝ}
    (heW0 : 0 ≤ eW) (heW : Fnorm k R.ℓ (WhH R k t' - WhH R k t) ≤ ENNReal.ofReal eW) (hcw : 0 ≤ cw) :
    Fnorm k (7 / 8 * R.ℓ) (WinH R k t' - WinH R k t) ≤
      ENNReal.ofReal (eW + 28 * ‖zetaH R k t' - zetaH R k t‖ * (cw * (t k).1 ^ 2)) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have h := Fnorm_sigF_sub_le (θ := 7 / 8) (τ := 1 / 16) hℓ (by norm_num) (by norm_num) H.cW_ne
    H'.cW_ne (by have := H'.norm_cW; nlinarith) (by have := H.norm_cW; nlinarith)
    (by have := H'.norm_cW; nlinarith) (WhH R k t) (WhH R k t') H.WhH_le heW (by positivity) heW0
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [H.uH_div, H'.uH_div]
  have hl := inv_csq_lip (H'.zetaH_16.trans (by norm_num)) (H.zetaH_16.trans (by norm_num))
  have hf : 0 ≤ cw * (t k).1 ^ 2 := by positivity
  have e : 7 / 8 * ‖(csq (1 + zetaH R k t'))⁻¹ - (csq (1 + zetaH R k t))⁻¹‖ / (1 / 16) *
      (cw * (t k).1 ^ 2) = 14 * ‖(csq (1 + zetaH R k t'))⁻¹ - (csq (1 + zetaH R k t))⁻¹‖ *
      (cw * (t k).1 ^ 2) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hl hf
  nlinarith

theorem cxH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw) :
    ‖cxH R k t' - cxH R k t‖ ≤ 2 * ‖zetaH R k t' - zetaH R k t‖ := by
  rw [H.cxH_eq, H'.cxH_eq]
  exact inv_csq_lip (H'.zetaH_16.trans (by norm_num)) (H.zetaH_16.trans (by norm_num))

/-- **The difference of the inputs `D`.** -/
theorem DinH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw)
    (hcx : 0 ≤ cx κ cT) :
    Fnorm k (7 / 8 * R.ℓ) (DinH R k t' - DinH R k t) ≤
      ENNReal.ofReal (‖(t' k).2.2 - (t k).2.2‖ +
        14 * (2 * ‖zetaH R k t' - zetaH R k t‖) * (cx κ cT * (t k).1 ^ 3)) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hdx : Fnorm k R.ℓ ((t' k).2.2.1.toFam - (t k).2.2.1.toFam) ≤
      ENNReal.ofReal ‖(t' k).2.2 - (t k).2.2‖ := by
    rw [← map_sub, ← Prod.fst_sub, BSp.Fnorm_le]
    exact ENNReal.ofReal_le_ofReal (norm_fst_le _)
  have h := Fnorm_sigF_sub_le (θ := 7 / 8) (τ := 1 / 16) hℓ (by norm_num) (by norm_num) H.cx_ne
    H'.cx_ne (by have := H'.norm_cx; nlinarith) (by have := H.norm_cx; nlinarith)
    (by have := H'.norm_cx; nlinarith) _ _ H.x1_le hdx (by have := H.g_pos; positivity)
    (norm_nonneg _)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hl := cxH_sub_le H H'
  have hf : 0 ≤ cx κ cT * (t k).1 ^ 3 := by have := H.g_pos; positivity
  have e : 7 / 8 * ‖cxH R k t' - cxH R k t‖ / (1 / 16) * (cx κ cT * (t k).1 ^ 3) =
      14 * ‖cxH R k t' - cxH R k t‖ * (cx κ cT * (t k).1 ^ 3) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 14)) hf
  linarith

/-- **The difference of the inputs `K`.** -/
theorem KinH_sub_le (H : DomH k t Λ κ cm cT ε cz cw) (H' : DomH k t' Λ κ cm cT ε cz cw)
    (hcx : 0 ≤ cx κ cT) :
    Knorm k (7 / 8 * R.ℓ) R.A (KinH R k t' - KinH R k t) ≤
      ENNReal.ofReal (‖(t' k).2.2 - (t k).2.2‖ +
        14 * (2 * ‖zetaH R k t' - zetaH R k t‖) * (cx κ cT * (t k).1 ^ 3)) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hdx : Knorm k R.ℓ R.A ((t' k).2.2.2.toAct - (t k).2.2.2.toAct) ≤
      ENNReal.ofReal ‖(t' k).2.2 - (t k).2.2‖ := by
    rw [← map_sub, ← Prod.snd_sub, ASp.Knorm_eq]
    exact ENNReal.ofReal_le_ofReal (norm_snd_le _)
  have h := Knorm_sigK_sub_le (θ := 7 / 8) (τ := 1 / 16) hℓ (by norm_num) (by norm_num) H.cx_ne
    H'.cx_ne (by have := H'.norm_cx; nlinarith) (by have := H.norm_cx; nlinarith)
    (by have := H'.norm_cx; nlinarith) _ _ H.x2_le hdx (by have := H.g_pos; positivity)
    (norm_nonneg _)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hl := cxH_sub_le H H'
  have hf : 0 ≤ cx κ cT * (t k).1 ^ 3 := by have := H.g_pos; positivity
  have e : 7 / 8 * ‖cxH R k t' - cxH R k t‖ / (1 / 16) * (cx κ cT * (t k).1 ^ 3) =
      14 * ‖cxH R k t' - cxH R k t‖ * (cx κ cT * (t k).1 ^ 3) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 14)) hf
  linarith

theorem nW1H_eq (k : ℕ) (t : Hist.Seq (Xs R)) : nW1H R k t = (1 + zetaH R k t) * whH R k t := by
  rw [nW1H, nW1, whH, ← zetaH]; ring

end Two

end

end Step2
