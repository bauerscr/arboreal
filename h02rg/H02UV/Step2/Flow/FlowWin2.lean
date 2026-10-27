import Step2.Last.FlowGlueHist
import Step2.Last.F2SharpGlue

/-!
# Route (a1): the sharp `ν`-relation through the last two steps

`glue_hist` bounds the final mass coupling only crudely (`|L^{2N}ν_N/Z_N| ≤ C ǧ`, `GlueOut`). The
mass flow at `h = 0` needs its relation to the windowed target `μ_{N_h}`:

* **`glue_last_nu`**: the third bound of `LastN.BoundsP` at the inputs of `glue_last`:
  `|L^{2N}ν_N/Z_N - L²μ_{N-1}| ≤ (16/7)L²c_Zǧ + (ℓ²/7)ǧ'` (`μ_{N-1} = Re ν_{N-1}`, `ǧ' = Re ǧ_{N-1}`);
* **`glue_hist_nu`** (hypotheses of `glue_hist`): with the sharp step-`(N-2)` bound
  `glue_step_nu_sharp`,
  `|L^{2N}ν_N/Z_N - L⁴μ_{N_h}| ≤ cNuLast·ǧ_{N_h}`,
  `cNuLast = L²cNuLs + (16/7)L²c_Z + 3ℓ²/7`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- The constant of the sharp `ν`-relation through the last two steps. -/
def cNuLast (R : RGPar 2 L N) (Λ cm ε : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * cNuLs R Λ cm ε + 16 / 7 * (L : ℝ) ^ 2 * cZ R + 3 * R.ℓ ^ 2 / 7

set_option maxHeartbeats 4000000 in
theorem glue_last_nu {εsN CKN C₂ CD CK : ℝ} (R : RGPar 2 L N) {Λ κ cm cT : ℝ}
    (hLB : LastN.BoundsP L R.A εsN CKN) {j : ℕ} (hVN : LastN.ValidLast R j)
    {st : RawSt 2 L N} (HI : RawInv R j st) {D : Fam 2 L N} {K : Act 2 L N}
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hcm : 0 ≤ cmu Λ cm) (hcx : 0 ≤ cx κ cT) (hC₂ : 0 ≤ C₂) (hCD : 0 ≤ CD) (hCK : 0 ≤ CK)
    (hCKN : 0 ≤ CKN)
    {g g' μ' : ℝ} (hg : 0 ≤ g) (_hg1 : g ≤ 1) (hg'0 : 0 ≤ g') (hg' : g' ≤ 3 * g)
    (hμ' : |μ'| ≤ cMu R Λ cm * g)
    (hz : ‖st.z / st.Z‖ ≤ cZ R * g) (hy : ‖st.y / st.Z‖ ≤ cZ R * g)
    (hη : 2 * (cZ R * g) ≤ R.ρ) (hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2)
    (hWl : Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2))
    (hDd : Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal (cDL R Λ κ cm cT C₂ CD * g ^ 2))
    (hKk : Knorm j (fscale st.Z * R.ℓ) R.A K ≤
      ENNReal.ofReal (cKL R Λ κ cm cT C₂ CK * g ^ 3))
    (hrε : cRN R Λ κ cm cT C₂ CD * g ≤ εsN)
    (hkε : 8 * (cKL R Λ κ cm cT C₂ CK * g ^ 3) ≤ εsN) :
    ‖(L : ℂ) ^ (2 * (j + 1)) * (LastN.rawStepN R j st g' μ' D K).κ.nu /
        (LastN.rawStepN R j st g' μ' D K).Z - (L : ℂ) ^ 2 * (μ' : ℂ)‖ ≤
      16 / 7 * (L : ℝ) ^ 2 * (cZ R * g) + R.ℓ ^ 2 / 7 * g' := by
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
  exact c3

set_option maxHeartbeats 4000000 in
/-- **The sharp `ν`-relation through the last two steps** along a regular history. -/
theorem glue_hist_nu {C₀ η εs CK C₂ CD Cq Cl cS Cqg Clg cSg εsN CKN : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS) (hGB : GStepBound L R.A Cqg Clg cSg)
    (hLB : LastN.BoundsP L R.A εsN CKN)
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hVN : LastN.ValidLast R (Nh + 1))
    (hm : ∀ j ≤ Nh + 1, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hκ₁ : kap1 L R.A C₀ η ≤ 1) (hCK : 0 ≤ CK) (hCD : 0 ≤ CD) (hCKN : 0 ≤ CKN)
    (hCqg : 0 ≤ Cqg) (hClg : 0 ≤ Clg) (hcSg : 1 ≤ cSg)
    (hcE : cE R Λ κ cm cT C₂ Cqg Clg cSg * ε ≤ R.ℓ ^ 2 / 24) (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1)
    (hrN : cRN R Λ κ cm cT C₂ CD * ε ≤ εsN) (hkN : 8 * cKL R Λ κ cm cT C₂ CK * ε ≤ εsN)
    (t : Hist.Seq (Xs R)) (ht : Hist.InDh Λ β δ κ cg cm cT ε Nh t) :
    ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh t).κ.nu / (lastOut R Nh t).Z -
        (L : ℂ) ^ 4 * ((t Nh).2.1 : ℂ)‖ ≤ cNuLast R Λ cm ε * (t Nh).1 := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := glue_step R hSB hGB hV hVL
    (fun j hj => hm j (by omega)) hβ hδ1 H hκ₁ hCK hCD hCqg hClg hcSg hcE hr1 hk1 t ht
  obtain ⟨hg, hgε, hμ, -⟩ := ht.1 Nh le_rfl
  have hg1 : (t Nh).1 ≤ 1 := hgε.trans H.hε1
  have HI := rawInv_hist R hVL.2.2.2.2.1 Nh hV t
  obtain ⟨HI', hD', hK'⟩ := RawInv.stepL hVL HI (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
    (rawK_mem R _ _)
  have hcm := H.hcmu
  have hcx := H.hcx
  have hC₂ := H.hC₂
  obtain ⟨hz0, hmu0, hw0, hd0, hk0, -, -, hnu0⟩ := consts_nonneg R hcm hcx hC₂ hCD hCK hCKN
  obtain ⟨f1, f2, f3, f4, f5, f6, -⟩ := le_cFin R hcm hcx hC₂ hCD hCK hCKN
  have hg0 : 0 ≤ (t Nh).1 := hg.le
  -- `ν'` and `μ' = Re ν'`
  have hnu : ‖(histOut R Nh t).nu‖ ≤ cMu R Λ cm * (t Nh).1 := by
    have h1 := norm_le_insert' (histOut R Nh t).nu ((L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ))
    have e : ‖(L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ)‖ = (L : ℝ) ^ 2 * |(t Nh).2.1| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [e] at h1
    have a1 := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    unfold cMu
    linarith only [h1, o3, a1]
  have hμ' : |(histOut R Nh t).nu.re| ≤ cMu R Λ cm * (t Nh).1 :=
    (Complex.abs_re_le_norm _).trans hnu
  -- `ǧ' = Re ǧ'`
  have hg'0 : 0 ≤ (histOut R Nh t).g.re := le_trans (by positivity) o8
  have hg' : (histOut R Nh t).g.re ≤ 3 * (t Nh).1 :=
    (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans o7
  -- the clamps and radii at the last step
  have hη : 2 * (cZ R * (t Nh).1) ≤ R.ρ := by
    have := mul_le_mul_of_nonneg_left hgε (by positivity : (0 : ℝ) ≤ 2 * cZ R)
    linarith only [this, H.h1]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t Nh).1) ≤ 1 / 2 := by
    have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hgε
      (by positivity : (0 : ℝ) ≤ 8 * cM * R.ℓ ^ 2 * cZ R)
    linarith only [this, H.h2]
  have hrε : cRN R Λ κ cm cT C₂ CD * (t Nh).1 ≤ εsN := by
    have : 0 ≤ cRN R Λ κ cm cT C₂ CD := by
      have := (consts_nonneg R hcm hcx hC₂ hCD hCK hCKN).2.2.2.2.2.2.1; linarith
    exact (mul_le_mul_of_nonneg_left hgε this).trans hrN
  have hkε : 8 * (cKL R Λ κ cm cT C₂ CK * (t Nh).1 ^ 3) ≤ εsN := by
    have hg3 : (t Nh).1 ^ 3 ≤ ε := by
      have : (t Nh).1 ^ 3 ≤ (t Nh).1 := by
        nlinarith [pow_le_one₀ hg0 hg1 (n := 2)]
      linarith
    have := mul_le_mul_of_nonneg_left hg3 (by positivity : (0 : ℝ) ≤ 8 * cKL R Λ κ cm cT C₂ CK)
    linarith only [this, hkN]
  have l3 : ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh t).κ.nu / (lastOut R Nh t).Z -
      (L : ℂ) ^ 2 * (((histOut R Nh t).nu.re : ℝ) : ℂ)‖ ≤
      16 / 7 * (L : ℝ) ^ 2 * (cZ R * (t Nh).1) + R.ℓ ^ 2 / 7 * (histOut R Nh t).g.re :=
    glue_last_nu R hLB hVN HI' hD' hK' (hm (Nh + 1) le_rfl)
    hcm hcx hC₂ hCD hCK hCKN hg0 hg1 hg'0 hg' hμ' o1 o2 hη hηs o4 o5 o6 hrε hkε
  have s := glue_step_nu_sharp R hSB hV hVL (fun j hj => hm j (by omega)) hβ hδ1 H t ht
  have hre : |(histOut R Nh t).nu.re - (L : ℝ) ^ 2 * (t Nh).2.1| ≤
      ‖(histOut R Nh t).nu - (L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ)‖ := by
    have := Complex.abs_re_le_norm ((histOut R Nh t).nu - (L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ))
    have e : ((histOut R Nh t).nu - (L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ)).re =
        (histOut R Nh t).nu.re - (L : ℝ) ^ 2 * (t Nh).2.1 := by
      simp [Complex.sub_re, Complex.mul_re, pow_two]
    rwa [e] at this
  have hsplit : (L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh t).κ.nu / (lastOut R Nh t).Z -
      (L : ℂ) ^ 4 * ((t Nh).2.1 : ℂ) =
      ((L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh t).κ.nu / (lastOut R Nh t).Z -
        (L : ℂ) ^ 2 * (((histOut R Nh t).nu.re : ℝ) : ℂ)) +
      (((L : ℝ) ^ 2 * ((histOut R Nh t).nu.re - (L : ℝ) ^ 2 * (t Nh).2.1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)]
  have a1 := mul_le_mul_of_nonneg_left (hre.trans s) (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
  have a2 := mul_le_mul_of_nonneg_left hg' (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 / 7)
  unfold cNuLast
  linarith [l3, a1, a2]

end

end Step2
