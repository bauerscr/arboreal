import Step2.Last.FlowGlueStep
import Step2.Last.LastNRG
import Step2.Flow.FlowBase

/-!
# The last step `j = N - 1` fed by the output of the step `j = N - 2`

`LastN.BoundsP`: the statement of `LastN.rg_last_bounds` at fixed `L, A, ε_s, C_K`.
`glue_last`: if the input of the last step has the bounds produced by `glue_core` at `j = N - 2`
(`|z/Z|, |y/Z| ≤ c_z ǧ`, `0 ≤ ǧ' ≤ 3ǧ`, `|μ'| ≤ c_μ ǧ`, `‖W^lin‖ ≤ c_w ǧ²`, `‖D‖ ≤ c_D ǧ²`,
`‖K‖ ≤ c_K ǧ³`), then the final-scale object of `rawStepN` has the bounds of `rg_last_bounds` in
terms of `ǧ = ǧ_{N-2}`, with one constant `cFin`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

namespace LastN

/-- The statement of `rg_last_bounds` at fixed `L, A, εs, CK`. -/
def BoundsP (L : ℕ) [NeZero L] (A εs CK : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidLast R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
      ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
        8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
      ∀ wl dd k r : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ k →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k →
      let v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g
      v ≤ r → wl + dd ≤ r ^ 2 → r ≤ εs → 8 * k ≤ εs →
      let out := rawStepN R j st g μ D K
      let s' := fscale out.Z
      ‖out.κ.z / out.Z‖ ≤ R.ℓ ^ 2 / 14 * g ∧ ‖out.κ.y / out.Z‖ ≤ R.ℓ ^ 2 / 14 * g ∧
      ‖(L : ℂ) ^ (2 * (j + 1)) * out.κ.nu / out.Z - (L : ℂ) ^ 2 * (μ : ℂ)‖ ≤
        16 / 7 * (L : ℝ) ^ 2 * ηz + R.ℓ ^ 2 / 7 * g ∧
      ‖out.κ.g / out.Z ^ 2‖ ≤ 8 / 7 * g ∧
      ‖out.u‖ ≤ (L : ℝ) ^ 2 * (Q1 2 * v) ∧
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        (out.V b : Alg 2 L N) = Vcoup out.κ (blockSet j b) ∧
        ‖upN out.C (stVf R j st g μ) b‖ ≤ Q1 2 * v ∧
        Grassmann.Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ) (out.V b : Alg 2 L N) ≤
          ENNReal.ofReal (2 * (Q1 2 * v)) ∧
        Grassmann.Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ) (out.W b : Alg 2 L N) ≤
          ENNReal.ofReal ((L : ℝ) ^ 2 * Q1 2 ^ 2 * v ^ 2 + Q1 2 * (wl + dd))) ∧
      Grassmann.Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ) (out.K : Alg 2 L N) ≤
        ENNReal.ofReal (CK * (r ^ 3 + 8 * k))

theorem rg_last_boundsP : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ (εs CK : ℝ), 0 < εs ∧ 0 ≤ CK ∧
      BoundsP L A εs CK :=
  rg_last_bounds

end LastN

/-! ### Constants -/

/-- The constant of `|μ_{N-1}|` (and of `|ν_{N-1}|`). -/
def cMu (R : RGPar 2 L N) (Λ cm : ℝ) : ℝ := (L : ℝ) ^ 2 * cmu Λ cm + cNuL R Λ cm

/-- The constant of `v` at the last step. -/
def cV2 (R : RGPar 2 L N) (Λ cm : ℝ) : ℝ :=
  cM * R.ℓ ^ 2 * (2 * cMu R Λ cm + 2 * cZ R) + 24 * R.ℓ ^ 4

/-- The constant of the radius `r` at the last step. -/
def cRN (R : RGPar 2 L N) (Λ κ cm cT C₂ CD : ℝ) : ℝ :=
  cV2 R Λ cm + cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD + 1

/-- **The constant of the final bounds.** -/
def cFin (R : RGPar 2 L N) (Λ κ cm cT C₂ CD CK CKN : ℝ) : ℝ :=
  cZ R + cMu R Λ cm + 3 + cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD + cKL R Λ κ cm cT C₂ CK +
    3 * R.ℓ ^ 2 / 14 + ((L : ℝ) ^ 2 * cMu R Λ cm + 16 / 7 * (L : ℝ) ^ 2 * cZ R + 3 * R.ℓ ^ 2 / 7) +
    24 / 7 + (L : ℝ) ^ 2 * Q1 2 * cV2 R Λ cm + 2 * Q1 2 * cV2 R Λ cm +
    ((L : ℝ) ^ 2 * Q1 2 ^ 2 * cV2 R Λ cm ^ 2 + Q1 2 * (cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD)) +
    CKN * (cRN R Λ κ cm cT C₂ CD ^ 3 + 8 * cKL R Λ κ cm cT C₂ CK)

section Congr

variable {N' : ℕ} {R : RGPar 2 L N} {R' : RGPar 2 L N'}

theorem cNuL_congr (h : R.ℓ = R'.ℓ) (Λ cm : ℝ) : cNuL R Λ cm = cNuL R' Λ cm := by
  unfold cNuL; rw [h, cZ_congr h]
theorem cDL_congr (h : R.ℓ = R'.ℓ) (Λ κ cm cT C₂ CD : ℝ) :
    cDL R Λ κ cm cT C₂ CD = cDL R' Λ κ cm cT C₂ CD := by
  unfold cDL; rw [cV_congr h, cW_congr h]
theorem cKL_congr (h : R.ℓ = R'.ℓ) (Λ κ cm cT C₂ CK : ℝ) :
    cKL R Λ κ cm cT C₂ CK = cKL R' Λ κ cm cT C₂ CK := by
  unfold cKL; rw [cR_congr h]
theorem cMu_congr (h : R.ℓ = R'.ℓ) (Λ cm : ℝ) : cMu R Λ cm = cMu R' Λ cm := by
  unfold cMu; rw [cNuL_congr h]
theorem cV2_congr (h : R.ℓ = R'.ℓ) (Λ cm : ℝ) : cV2 R Λ cm = cV2 R' Λ cm := by
  unfold cV2; rw [cMu_congr h, cZ_congr h, h]
theorem cRN_congr (h : R.ℓ = R'.ℓ) (Λ κ cm cT C₂ CD : ℝ) :
    cRN R Λ κ cm cT C₂ CD = cRN R' Λ κ cm cT C₂ CD := by
  unfold cRN; rw [cV2_congr h, cW_congr h, cDL_congr h]
theorem cFin_congr (h : R.ℓ = R'.ℓ) (Λ κ cm cT C₂ CD CK CKN : ℝ) :
    cFin R Λ κ cm cT C₂ CD CK CKN = cFin R' Λ κ cm cT C₂ CD CK CKN := by
  unfold cFin
  rw [cZ_congr h, cMu_congr h, cW_congr h, cDL_congr h, cKL_congr h, cV2_congr h, cRN_congr h, h]

end Congr

/-- Nonnegativity of the constants. -/
theorem consts_nonneg (R : RGPar 2 L N) {Λ κ cm cT C₂ CD CK CKN : ℝ} (hcm : 0 ≤ cmu Λ cm)
    (hcx : 0 ≤ cx κ cT) (hC₂ : 0 ≤ C₂) (hCD : 0 ≤ CD) (hCK : 0 ≤ CK) (hCKN : 0 ≤ CKN) :
    0 ≤ cZ R ∧ 0 ≤ cMu R Λ cm ∧ 0 ≤ cW R Λ cm C₂ ∧ 0 ≤ cDL R Λ κ cm cT C₂ CD ∧
      0 ≤ cKL R Λ κ cm cT C₂ CK ∧ 0 ≤ cV2 R Λ cm ∧ 1 ≤ cRN R Λ κ cm cT C₂ CD ∧
      0 ≤ cNuL R Λ cm := by
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hz : 0 ≤ cZ R := by unfold cZ; positivity
  have hv : 0 ≤ cV R Λ cm := by unfold cV; positivity
  have hw : 0 ≤ cW R Λ cm C₂ := by unfold cW; positivity
  have hr : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
  have hnu : 0 ≤ cNuL R Λ cm := by unfold cNuL; positivity
  have hmu : 0 ≤ cMu R Λ cm := by unfold cMu; positivity
  have hd : 0 ≤ cDL R Λ κ cm cT C₂ CD := by unfold cDL; positivity
  have hk : 0 ≤ cKL R Λ κ cm cT C₂ CK := by unfold cKL; positivity
  have hv2 : 0 ≤ cV2 R Λ cm := by unfold cV2; positivity
  have hrn : 1 ≤ cRN R Λ κ cm cT C₂ CD := by unfold cRN; linarith
  exact ⟨hz, hmu, hw, hd, hk, hv2, hrn, hnu⟩

theorem le_cFin (R : RGPar 2 L N) {Λ κ cm cT C₂ CD CK CKN : ℝ} (hcm : 0 ≤ cmu Λ cm)
    (hcx : 0 ≤ cx κ cT) (hC₂ : 0 ≤ C₂) (hCD : 0 ≤ CD) (hCK : 0 ≤ CK) (hCKN : 0 ≤ CKN) :
    cZ R ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧ cMu R Λ cm ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    3 ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧ cW R Λ cm C₂ ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    cDL R Λ κ cm cT C₂ CD ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    cKL R Λ κ cm cT C₂ CK ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    3 * R.ℓ ^ 2 / 14 ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    (L : ℝ) ^ 2 * cMu R Λ cm + 16 / 7 * (L : ℝ) ^ 2 * cZ R + 3 * R.ℓ ^ 2 / 7 ≤
      cFin R Λ κ cm cT C₂ CD CK CKN ∧
    24 / 7 ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    (L : ℝ) ^ 2 * Q1 2 * cV2 R Λ cm ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    2 * Q1 2 * cV2 R Λ cm ≤ cFin R Λ κ cm cT C₂ CD CK CKN ∧
    (L : ℝ) ^ 2 * Q1 2 ^ 2 * cV2 R Λ cm ^ 2 + Q1 2 * (cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD) ≤
      cFin R Λ κ cm cT C₂ CD CK CKN ∧
    CKN * (cRN R Λ κ cm cT C₂ CD ^ 3 + 8 * cKL R Λ κ cm cT C₂ CK) ≤
      cFin R Λ κ cm cT C₂ CD CK CKN := by
  obtain ⟨hz, hmu, hw, hd, hk, hv2, hrn, -⟩ := consts_nonneg R hcm hcx hC₂ hCD hCK hCKN
  have hQ : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hℓ2 : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  have t1 : 0 ≤ 3 * R.ℓ ^ 2 / 14 := by positivity
  have t2 : 0 ≤ (L : ℝ) ^ 2 * cMu R Λ cm + 16 / 7 * (L : ℝ) ^ 2 * cZ R + 3 * R.ℓ ^ 2 / 7 := by
    positivity
  have hQ0 : 0 ≤ Q1 2 := by linarith only [hQ]
  have t3 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 * cV2 R Λ cm := mul_nonneg (mul_nonneg (sq_nonneg _) hQ0) hv2
  have t4 : 0 ≤ 2 * Q1 2 * cV2 R Λ cm := mul_nonneg (mul_nonneg (by norm_num) hQ0) hv2
  have t5 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 * cV2 R Λ cm ^ 2 +
      Q1 2 * (cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg hQ0 (add_nonneg hw hd))
  have t6 : 0 ≤ CKN * (cRN R Λ κ cm cT C₂ CD ^ 3 + 8 * cKL R Λ κ cm cT C₂ CK) := by
    have : 0 ≤ cRN R Λ κ cm cT C₂ CD := by linarith
    positivity
  unfold cFin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hz, hmu, hw, hd, hk, t1, t2, t3, t4, t5, t6]

set_option maxHeartbeats 4000000 in
/-- **The last step fed by the output of the step `j = N - 2`.** -/
theorem glue_last {εsN CKN C₂ CD CK : ℝ} (R : RGPar 2 L N) {Λ κ cm cT : ℝ}
    (hLB : LastN.BoundsP L R.A εsN CKN) {j : ℕ} (hVN : LastN.ValidLast R j)
    {st : RawSt 2 L N} (HI : RawInv R j st) {D : Fam 2 L N} {K : Act 2 L N}
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hcm : 0 ≤ cmu Λ cm) (hcx : 0 ≤ cx κ cT) (hC₂ : 0 ≤ C₂) (hCD : 0 ≤ CD) (hCK : 0 ≤ CK)
    (hCKN : 0 ≤ CKN)
    {g g' μ' : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1) (hg'0 : 0 ≤ g') (hg' : g' ≤ 3 * g)
    (hμ' : |μ'| ≤ cMu R Λ cm * g)
    (hz : ‖st.z / st.Z‖ ≤ cZ R * g) (hy : ‖st.y / st.Z‖ ≤ cZ R * g)
    (hη : 2 * (cZ R * g) ≤ R.ρ) (hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2)
    (hWl : Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2))
    (hDd : Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal (cDL R Λ κ cm cT C₂ CD * g ^ 2))
    (hKk : Knorm j (fscale st.Z * R.ℓ) R.A K ≤
      ENNReal.ofReal (cKL R Λ κ cm cT C₂ CK * g ^ 3))
    (hrε : cRN R Λ κ cm cT C₂ CD * g ≤ εsN)
    (hkε : 8 * (cKL R Λ κ cm cT C₂ CK * g ^ 3) ≤ εsN) :
    ‖(LastN.rawStepN R j st g' μ' D K).κ.z / (LastN.rawStepN R j st g' μ' D K).Z‖ ≤
      cFin R Λ κ cm cT C₂ CD CK CKN * g ∧
    ‖(LastN.rawStepN R j st g' μ' D K).κ.y / (LastN.rawStepN R j st g' μ' D K).Z‖ ≤
      cFin R Λ κ cm cT C₂ CD CK CKN * g ∧
    ‖(L : ℂ) ^ (2 * (j + 1)) * (LastN.rawStepN R j st g' μ' D K).κ.nu /
        (LastN.rawStepN R j st g' μ' D K).Z‖ ≤ cFin R Λ κ cm cT C₂ CD CK CKN * g ∧
    ‖(LastN.rawStepN R j st g' μ' D K).κ.g / (LastN.rawStepN R j st g' μ' D K).Z ^ 2‖ ≤
      cFin R Λ κ cm cT C₂ CD CK CKN * g ∧
    ‖(LastN.rawStepN R j st g' μ' D K).u‖ ≤ cFin R Λ κ cm cT C₂ CD CK CKN * g ∧
    (∀ b ∈ blockIdx (L := L) (N := N) j,
      ((LastN.rawStepN R j st g' μ' D K).V b : Alg 2 L N) =
        Vcoup (LastN.rawStepN R j st g' μ' D K).κ (blockSet j b) ∧
      Grassmann.Tj 2 (L : ℝ) (j + 1) (fscale (LastN.rawStepN R j st g' μ' D K).Z * R.ℓ)
        ((LastN.rawStepN R j st g' μ' D K).V b : Alg 2 L N) ≤
        ENNReal.ofReal (cFin R Λ κ cm cT C₂ CD CK CKN * g) ∧
      Grassmann.Tj 2 (L : ℝ) (j + 1) (fscale (LastN.rawStepN R j st g' μ' D K).Z * R.ℓ)
        ((LastN.rawStepN R j st g' μ' D K).W b : Alg 2 L N) ≤
        ENNReal.ofReal (cFin R Λ κ cm cT C₂ CD CK CKN * g ^ 2)) ∧
    Grassmann.Tj 2 (L : ℝ) (j + 1) (fscale (LastN.rawStepN R j st g' μ' D K).Z * R.ℓ)
      ((LastN.rawStepN R j st g' μ' D K).K : Alg 2 L N) ≤
      ENNReal.ofReal (cFin R Λ κ cm cT C₂ CD CK CKN * g ^ 3) := by
  obtain ⟨hz0, hmu0, hw0, hd0, hk0, hv20, hrn1, -⟩ := consts_nonneg R hcm hcx hC₂ hCD hCK hCKN
  obtain ⟨-, -, -, -, -, -, f7, f8, f9, f10, f11, f12, f13⟩ :=
    le_cFin R hcm hcx hC₂ hCD hCK hCKN
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hQ : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hℓ4 : 0 ≤ R.ℓ ^ 4 := by positivity
  -- the radius
  have hv : cM * R.ℓ ^ 2 * (2 * |μ'| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g' ≤ cV2 R Λ cm * g := by
    unfold cV2
    have a1 : 2 * |μ'| + 2 * (cZ R * g) ≤ (2 * cMu R Λ cm + 2 * cZ R) * g := by
      linarith only [hμ', show (2 * cMu R Λ cm + 2 * cZ R) * g =
        2 * (cMu R Λ cm * g) + 2 * (cZ R * g) by ring]
    have a2 := mul_le_mul_of_nonneg_left a1 (mul_nonneg hM (sq_nonneg R.ℓ))
    have a3 := mul_le_mul_of_nonneg_left hg' (by positivity : (0 : ℝ) ≤ 8 * R.ℓ ^ 4)
    linarith only [a2, a3, show (cM * R.ℓ ^ 2 * (2 * cMu R Λ cm + 2 * cZ R) + 24 * R.ℓ ^ 4) * g =
      cM * R.ℓ ^ 2 * ((2 * cMu R Λ cm + 2 * cZ R) * g) + 8 * R.ℓ ^ 4 * (3 * g) by ring]
  have hv0 : 0 ≤ cM * R.ℓ ^ 2 * (2 * |μ'| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g' := by positivity
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ'| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g' ≤
      cRN R Λ κ cm cT C₂ CD * g := by
    refine hv.trans (mul_le_mul_of_nonneg_right ?_ hg)
    unfold cRN; linarith only [hw0, hd0]
  have hwr : cW R Λ cm C₂ * g ^ 2 + cDL R Λ κ cm cT C₂ CD * g ^ 2 ≤
      (cRN R Λ κ cm cT C₂ CD * g) ^ 2 := by
    have h1 : cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD ≤ cRN R Λ κ cm cT C₂ CD ^ 2 := by
      have : cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD ≤ cRN R Λ κ cm cT C₂ CD := by
        unfold cRN; linarith only [hv20]
      nlinarith
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg g)
    linarith only [this, show (cRN R Λ κ cm cT C₂ CD * g) ^ 2 =
      cRN R Λ κ cm cT C₂ CD ^ 2 * g ^ 2 by ring]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hLB N R j hVN st HI g' μ' D K hD hK hm hg'0
    (cZ R * g) hz hy hη hηs (cW R Λ cm C₂ * g ^ 2) (cDL R Λ κ cm cT C₂ CD * g ^ 2)
    (cKL R Λ κ cm cT C₂ CK * g ^ 3) (cRN R Λ κ cm cT C₂ CD * g) (by positivity) (by positivity)
    (by positivity) hWl hDd hKk hvr hwr hrε hkε
  have hℓ2 : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, fun b hb => ?_, ?_⟩
  · refine c1.trans ?_
    have a1 := mul_le_mul_of_nonneg_left hg' (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 / 14)
    have a2 := mul_le_mul_of_nonneg_right f7 hg
    linarith only [a1, a2]
  · refine c2.trans ?_
    have a1 := mul_le_mul_of_nonneg_left hg' (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 / 14)
    have a2 := mul_le_mul_of_nonneg_right f7 hg
    linarith only [a1, a2]
  · have hμn : ‖(L : ℂ) ^ 2 * (μ' : ℂ)‖ = (L : ℝ) ^ 2 * |μ'| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_le_insert' ((L : ℂ) ^ (2 * (j + 1)) *
      (LastN.rawStepN R j st g' μ' D K).κ.nu / (LastN.rawStepN R j st g' μ' D K).Z)
      ((L : ℂ) ^ 2 * (μ' : ℂ))
    rw [hμn] at h1
    refine (h1.trans (add_le_add le_rfl c3)).trans ?_
    have a1 := mul_le_mul_of_nonneg_left hμ' (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    have a2 := mul_le_mul_of_nonneg_left hg' (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 / 7)
    have a3 := mul_le_mul_of_nonneg_right f8 hg
    linarith only [a1, a2, a3]
  · refine c4.trans ?_
    have := mul_le_mul_of_nonneg_right f9 hg
    linarith only [this, hg']
  · refine c5.trans ?_
    have a1 := mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg _) (by linarith only [hQ]) : (0 : ℝ) ≤ (L : ℝ) ^ 2 * Q1 2)
    have a2 := mul_le_mul_of_nonneg_right f10 hg
    linarith only [a1, a2, show (L : ℝ) ^ 2 * (Q1 2 * (cM * R.ℓ ^ 2 * (2 * |μ'| + 2 * (cZ R * g)) +
      8 * R.ℓ ^ 4 * g')) = (L : ℝ) ^ 2 * Q1 2 * (cM * R.ℓ ^ 2 * (2 * |μ'| + 2 * (cZ R * g)) +
      8 * R.ℓ ^ 4 * g') by ring, show (L : ℝ) ^ 2 * Q1 2 * (cV2 R Λ cm * g) =
      (L : ℝ) ^ 2 * Q1 2 * cV2 R Λ cm * g by ring]
  · obtain ⟨b1, -, b3, b4⟩ := c6 b hb
    refine ⟨b1, b3.trans (ENNReal.ofReal_le_ofReal ?_), b4.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · have a1 := mul_le_mul_of_nonneg_left hv (by linarith only [hQ] : (0 : ℝ) ≤ 2 * Q1 2)
      have a2 := mul_le_mul_of_nonneg_right f11 hg
      linarith only [a1, a2, show 2 * (Q1 2 * (cM * R.ℓ ^ 2 * (2 * |μ'| + 2 * (cZ R * g)) +
        8 * R.ℓ ^ 4 * g')) = 2 * Q1 2 * (cM * R.ℓ ^ 2 * (2 * |μ'| + 2 * (cZ R * g)) +
        8 * R.ℓ ^ 4 * g') by ring, show 2 * Q1 2 * (cV2 R Λ cm * g) =
        2 * Q1 2 * cV2 R Λ cm * g by ring]
    · have hv2 := pow_le_pow_left₀ hv0 hv 2
      have a1 := mul_le_mul_of_nonneg_left hv2 (mul_nonneg (sq_nonneg _) (sq_nonneg _) : (0 : ℝ) ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2)
      have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
      have a2 := mul_le_mul_of_nonneg_right f12 hg2
      linarith only [a1, a2, show (L : ℝ) ^ 2 * Q1 2 ^ 2 * (cV2 R Λ cm * g) ^ 2 +
        Q1 2 * (cW R Λ cm C₂ * g ^ 2 + cDL R Λ κ cm cT C₂ CD * g ^ 2) =
        ((L : ℝ) ^ 2 * Q1 2 ^ 2 * cV2 R Λ cm ^ 2 +
          Q1 2 * (cW R Λ cm C₂ + cDL R Λ κ cm cT C₂ CD)) * g ^ 2 by ring]
  · refine c7.trans (ENNReal.ofReal_le_ofReal ?_)
    have hg3 : 0 ≤ g ^ 3 := by positivity
    have a2 := mul_le_mul_of_nonneg_right f13 hg3
    linarith only [a2, show CKN * ((cRN R Λ κ cm cT C₂ CD * g) ^ 3 +
      8 * (cKL R Λ κ cm cT C₂ CK * g ^ 3)) =
      CKN * (cRN R Λ κ cm cT C₂ CD ^ 3 + 8 * cKL R Λ κ cm cT C₂ CK) * g ^ 3 by ring]

end

end Step2
