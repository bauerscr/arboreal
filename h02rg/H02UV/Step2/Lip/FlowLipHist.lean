import Step2.Lip.FlowLipIn

/-!
# The normalised state along a history (Lipschitz bounds, part 9)

Along a history `t` the raw state `rawHist R j t` is normalised by a consistent choice of square
roots `u_j` of `Z_j` (`uH`: `u_0 = 1`, `u_{j+1} = u_j (1 + ζ_j)^{1/2}`, principal branch):

* `zhH = z_j/Z_j`, `yhH = y_j/Z_j`, `whH = Z_j w^{(1)}_j / L^{2j}`, `WhH = σ_{u_j⁻¹} 𝒲^lin_j`;
* the phase `omH = u_j/|u_j|`;
* the inputs of step `j`: `CvH = Z_{j+1} Γ^int_{j+1}`, `WinH = σ_{u_j/u_{j+1}} WhH`,
  `DinH = σ_c x_j.1`, `KinH = σ_c x_j.2` with `c = u_{j+1}⁻¹ |Z_j|^{1/2}`
  (`|c| = |1 + ζ_j|^{-1/2}`, `c = ω̄_j (1 + ζ_j)^{-1/2}`).

By `rawStep_norm`, step `j` of the history is the normalised step with these inputs
(`normData_hist`), and the outputs `zhH, yhH, WhH, whH` at `j + 1`, the irrelevant map `T_j`,
`G_j` and `m_j` are expressed through the normalised step (`zhH_succ`, `WhH_succ`, `whH_succ`,
`Tmap_norm`, `histOut_g_norm`, `histOut_nu_norm`). The history enters only through these
normalised quantities (no phase of `Z_j`: the coordinates are normalised by `u_j`).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Defs

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The absorbed coupling `ζ_j` along the history. -/
def zetaH (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  absorbZeta R (rawHist R j t).Z ((rawHist R j t).z + (rawHist R j t).y)

/-- The consistent square roots `u_j` of `Z_j`. -/
def uH (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ := (rawHist R j t).u

/-- `ẑ_j = z_j / Z_j`. -/
def zhH (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ := (rawHist R j t).z / (rawHist R j t).Z

/-- `ŷ_j = y_j / Z_j`. -/
def yhH (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ := (rawHist R j t).y / (rawHist R j t).Z

/-- `ŵ_j = Z_j w^{(1)}_j / L^{2j}`. -/
def whH (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  (rawHist R j t).Z * (rawHist R j t).w1 / (L : ℂ) ^ (2 * j)

/-- `Ŵ_j = σ_{u_j⁻¹} 𝒲^lin_j`. -/
def WhH (j : ℕ) (t : Hist.Seq (Xs R)) : Fam 2 L N := sigF (uH R j t)⁻¹ (rawHist R j t).Wl

/-- The normalised covariance of step `j`. -/
def CvH (j : ℕ) (t : Hist.Seq (Xs R)) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ :=
  nCov R j (rawHist R j t) (uH R (j + 1) t)

/-- `ŵ` as entering step `j`: `Z_{j+1} w^{(1)}_j / L^{2j}`. -/
def nW1H (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ := nW1 R j (rawHist R j t)

/-- The input `𝒲^lin` of step `j`, normalised by `u_{j+1}`. -/
def WinH (j : ℕ) (t : Hist.Seq (Xs R)) : Fam 2 L N :=
  sigF (uH R j t / uH R (j + 1) t) (WhH R j t)

/-- The rescaling of the coordinate `x_j` entering step `j`. -/
def cxH (j : ℕ) (t : Hist.Seq (Xs R)) : ℂ := uH R j t / uH R (j + 1) t

/-- The input `D` of step `j`, normalised by `u_{j+1}`. -/
def DinH (j : ℕ) (t : Hist.Seq (Xs R)) : Fam 2 L N := sigF (cxH R j t) (t j).2.2.1.toFam

/-- The input `K` of step `j`, normalised by `u_{j+1}`. -/
def KinH (j : ℕ) (t : Hist.Seq (Xs R)) : Act 2 L N := sigK (cxH R j t) (t j).2.2.2.toAct

/-- The normalised step at `j` along the history: the outputs. -/
abbrev kapH (j : ℕ) (t : Hist.Seq (Xs R)) : Fin 4 → ℂ :=
  nKap R j (CvH R j t) (zhH R j t) (yhH R j t) (t j).1 (t j).2.1 (nW1H R j t) (WinH R j t)
    (DinH R j t) (KinH R j t)

abbrev nWlH (j : ℕ) (t : Hist.Seq (Xs R)) : Fam 2 L N :=
  nWl R j (CvH R j t) (zhH R j t) (yhH R j t) (t j).1 (t j).2.1 (nW1H R j t) (WinH R j t)

abbrev nDH (j : ℕ) (t : Hist.Seq (Xs R)) : Fam 2 L N :=
  nD R j (CvH R j t) (zhH R j t) (yhH R j t) (t j).1 (t j).2.1 (nW1H R j t) (WinH R j t)
    (DinH R j t)

abbrev nKH (j : ℕ) (t : Hist.Seq (Xs R)) : Act 2 L N :=
  nK R j (CvH R j t) (zhH R j t) (yhH R j t) (t j).1 (t j).2.1 (nW1H R j t) (WinH R j t)
    (DinH R j t) (KinH R j t)

end Defs

section Ident

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem rawHist_succ_Z (j : ℕ) (t : Hist.Seq (Xs R)) :
    (rawHist R (j + 1) t).Z = (rawHist R j t).Z * (1 + zetaH R j t) := rfl

theorem uH_succ (j : ℕ) (t : Hist.Seq (Xs R)) :
    uH R (j + 1) t = uH R j t * csq (1 + zetaH R j t) := rfl

theorem uH_sq : ∀ (j : ℕ) (t : Hist.Seq (Xs R)), uH R j t ^ 2 = (rawHist R j t).Z
  | 0, _ => by simp [uH, rawHist]
  | j + 1, t => by
    rw [uH_succ, mul_pow, uH_sq j t, csq_sq, rawHist_succ_Z]

/-- The invariants along the history, at the level needed here. -/
structure HistOK (j : ℕ) (t : Hist.Seq (Xs R)) : Prop where
  hZ : (rawHist R j t).Z ≠ 0
  hζ : ‖zetaH R j t‖ ≤ 1 / 8

variable {R}

theorem HistOK.one_add_ne {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    1 + zetaH R j t ≠ 0 := one_add_ne_zero (H.hζ.trans_lt (by norm_num))

theorem HistOK.u_ne {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) : uH R j t ≠ 0 := by
  intro h; have := uH_sq R j t; rw [h, zero_pow two_ne_zero] at this; exact H.hZ this.symm

theorem HistOK.u_succ_ne {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    uH R (j + 1) t ≠ 0 := mul_ne_zero H.u_ne (csq_ne H.one_add_ne)

/-- **Step `j` of the history is the normalised step.** -/
theorem normData_hist {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    NormData R j (rawHist R j t) (uH R (j + 1) t) (rawD R (rawHist R j t).u (t j).2.2)
      (rawK R (rawHist R j t).u (t j).2.2) (WinH R j t) (DinH R j t) (KinH R j t) where
  hZ := H.hZ
  hζ := H.one_add_ne
  hu := by rw [uH_sq]; rfl
  hW := by
    rw [WinH, WhH, sigF_sigF, sigF_sigF]
    have hu := H.u_ne
    have hu1 := H.u_succ_ne
    rw [show uH R (j + 1) t * (uH R j t / uH R (j + 1) t) * (uH R j t)⁻¹ = 1 by field_simp,
      sigF_one]
  hD := by
    rw [DinH, cxH, sigF_sigF, mul_div_cancel₀ _ H.u_succ_ne]; rfl
  hK := by
    rw [KinH, cxH, sigK_sigK, mul_div_cancel₀ _ H.u_succ_ne]; rfl

/-- The raw outputs through the normalised step. -/
theorem histOut_norm {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    cκ R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
        (rawK R (rawHist R j t).u (t j).2.2) = vsc (uH R (j + 1) t) (kapH R j t) ∧
      (histOut R j t).st.Wl = sigF (uH R (j + 1) t) (nWlH R j t) ∧
      (histOut R j t).D = sigF (uH R (j + 1) t) (nDH R j t) ∧
      (histOut R j t).K = sigK (uH R (j + 1) t) (nKH R j t) :=
  rawStep_norm (normData_hist H) (t j).1 (t j).2.1

theorem uH_succ_sq (j : ℕ) (t : Hist.Seq (Xs R)) :
    uH R (j + 1) t ^ 2 = (rawHist R j t).Z * (1 + zetaH R j t) := by
  rw [uH_sq, rawHist_succ_Z]

theorem zhH_succ {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    zhH R (j + 1) t = kapH R j t 0 := by
  obtain ⟨h1, -⟩ := histOut_norm H
  have e : (rawHist R (j + 1) t).z = cκ R j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) 0 := rfl
  rw [zhH, e, h1, rawHist_succ_Z, ← uH_succ_sq]
  simp only [vsc, Matrix.cons_val_zero]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 H.u_succ_ne)]

theorem yhH_succ {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    yhH R (j + 1) t = kapH R j t 1 := by
  obtain ⟨h1, -⟩ := histOut_norm H
  have e : (rawHist R (j + 1) t).y = cκ R j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) 1 := rfl
  rw [yhH, e, h1, rawHist_succ_Z, ← uH_succ_sq]
  simp only [vsc, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 H.u_succ_ne)]

theorem WhH_succ {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    WhH R (j + 1) t = nWlH R j t := by
  obtain ⟨-, h2, -⟩ := histOut_norm H
  rw [WhH, rawHist_succ, h2, sigF_sigF, inv_mul_cancel₀ H.u_succ_ne, sigF_one]

theorem zetaH_succ {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    zetaH R (j + 1) t = nZeta R (kapH R j t 0) (kapH R j t 1) := by
  rw [zetaH, absorbZeta_eq, ← zhH, ← yhH, zhH_succ H, yhH_succ H]

theorem CovH_eq (j : ℕ) (t : Hist.Seq (Xs R)) :
    CvH R j t = (rawHist R (j + 1) t).Z • rawCov R j (rawHist R (j + 1) t).ζ := by
  rw [CvH, nCov, uH_sq]; rfl

theorem whH_succ {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    whH R (j + 1) t = (nW1H R j t * (L : ℂ) ^ (2 * j) + ∑ x, CvH R j t x 0) /
      (L : ℂ) ^ (2 * (j + 1)) := by
  have hL : (L : ℂ) ^ (2 * j) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have e1 : (rawHist R (j + 1) t).w1 = (rawHist R j t).w1 +
      ∑ x, rawCov R j (rawHist R (j + 1) t).ζ x 0 := rfl
  rw [whH, e1, CovH_eq, nW1H, nW1]
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum]
  rw [rawHist_succ_Z, div_mul_cancel₀ _ hL]
  congr 1
  rw [← zetaH]; ring

/-- `|u_j|² = |Z_j|`, so `s_j u_j` is a phase. -/
theorem norm_uH_sq (j : ℕ) (t : Hist.Seq (Xs R)) : ‖uH R j t‖ ^ 2 = ‖(rawHist R j t).Z‖ := by
  rw [← norm_pow, uH_sq]

/-- **The irrelevant map is the normalised step**: `T_j = (D̂_{j+1}, K̂_{j+1})`. -/
theorem Tmap_norm {j : ℕ} (h : ∀ i ≤ j, ValidAt R i) (t : Hist.Seq (Xs R))
    (H : HistOK R j t) :
    (Tmap R j t).1.toFam = nDH R j t ∧ (Tmap R j t).2.toAct = nKH R j t := by
  obtain ⟨-, -, h3, h4⟩ := histOut_norm H
  have hu1 : (histOut R j t).st.u = uH R (j + 1) t := rfl
  simp only [Tmap, dif_pos h]
  refine ⟨?_, ?_⟩
  · show sigF (histOut R j t).st.u⁻¹ (histOut R j t).D = _
    rw [h3, sigF_sigF, hu1, inv_mul_cancel₀ H.u_succ_ne, sigF_one]
  · show sigK (histOut R j t).st.u⁻¹ (histOut R j t).K = _
    rw [h4, sigK_sigK, hu1, inv_mul_cancel₀ H.u_succ_ne, sigK_one]

/-- **The marginal coupling through the normalised step.** -/
theorem histOut_g_norm {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    (histOut R j t).g = kapH R j t 3 / (1 + zetaH R (j + 1) t) ^ 2 *
      (1 + nCor (kapH R j t 2) ((L : ℂ) ^ (2 * (j + 1)) * whH R (j + 1) t)) := by
  obtain ⟨h1, -⟩ := histOut_norm H
  have hL : (L : ℂ) ^ (2 * (j + 1)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have hu := H.u_succ_ne
  have hZ1 : (rawHist R (j + 1) t).Z = uH R (j + 1) t ^ 2 := (uH_sq R (j + 1) t).symm
  have e : (histOut R j t).g = cκ R j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) 3 /
      ((rawHist R (j + 1) t).Z * (1 + zetaH R (j + 1) t)) ^ 2 *
      (1 + nCor (cκ R j (rawHist R j t) (t j).1 (t j).2.1
        (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) 2)
        (rawHist R (j + 1) t).w1) := rfl
  rw [e, h1]
  have hZne : (rawHist R (j + 1) t).Z ≠ 0 := by rw [hZ1]; exact pow_ne_zero 2 hu
  have hw : (rawHist R (j + 1) t).w1 = (L : ℂ) ^ (2 * (j + 1)) * whH R (j + 1) t /
      uH R (j + 1) t ^ 2 := by
    rw [whH, ← hZ1, mul_div_cancel₀ _ hL]
    field_simp
  simp only [vsc, Fin.isValue, Matrix.cons_val]
  rw [hZ1, hw]
  have hn : nCor (uH R (j + 1) t ^ 2 * kapH R j t 2)
      ((L : ℂ) ^ (2 * (j + 1)) * whH R (j + 1) t / uH R (j + 1) t ^ 2) =
      nCor (kapH R j t 2) ((L : ℂ) ^ (2 * (j + 1)) * whH R (j + 1) t) := by
    unfold nCor; congr 1; field_simp
  rw [hn]
  field_simp

/-- **The relevant coupling through the normalised step.** -/
theorem histOut_nu_norm {j : ℕ} {t : Hist.Seq (Xs R)} (H : HistOK R j t) :
    (histOut R j t).nu = kapH R j t 2 * (L : ℂ) ^ (2 * (j + 1)) / (1 + zetaH R (j + 1) t) := by
  obtain ⟨h1, -⟩ := histOut_norm H
  have hu := H.u_succ_ne
  have hZ1 : (rawHist R (j + 1) t).Z = uH R (j + 1) t ^ 2 := (uH_sq R (j + 1) t).symm
  have e : (histOut R j t).nu = cκ R j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) 2 *
      (L : ℂ) ^ (2 * (j + 1)) / ((rawHist R (j + 1) t).Z * (1 + zetaH R (j + 1) t)) := rfl
  rw [e, h1, hZ1]
  simp only [vsc, Fin.isValue, Matrix.cons_val]
  field_simp

end Ident

end

end Step2
