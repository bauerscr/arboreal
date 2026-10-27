import Step2.Last.FlowLastBand

/-!
# The last two steps: a weak band

* `Zw1_step`, `Zw1_hist`: `|Z_{j+1} w^{(1)}_j| ≤ ℓ² L^{2j}` (copy of `norm_Zw1_le`) along the
  flow up to `N_h` (with `ValidAt`) and one step further (with `ValidCore`, e.g. `ValidAtL`).
* `band_core`: at the step `j = N - 2` (under `ValidAtL`), for inputs as in `glue_core`,
  `|ǧ' - ǧ| ≤ c_{B1} ǧ²`; the three clamped factors are `O(ǧ)`, the remainder is `O(ǧ²)`.
* `lastG`, `gFin`: the final quartic coupling `ǧ_N = κ_N.g/Z_N²` and its real part.
  `lastG_eq`: `ǧ_N = ǧ_{N-1}/(1 + n_{N-1})` (the last map has no localisation, so the
  `g`-coefficient of `V_N = V_{κ_N}` is the first-order term only; the second order of the last
  step sits in `𝒲_N`). `stGr_sub_leN`: `|ǧ_N - ǧ_{N-1}| ≤ (8/7)·4 ǧ_{N-1} |μ_{N-1}| ℓ²`.
* `BandOut`, `band_hist`: along a regular history, `|ǧ_{N-1} - ǧ_{N-2}| ≤ C ǧ_{N-2}²` and
  `|ǧ_N - Re ǧ_{N-1}| ≤ C ǧ_{N-2}²`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-! ### The accumulated zero mode -/

/-- **One step of `|Z_{j+1} w^{(1)}_j| ≤ ℓ² L^{2j}`** (cf. `norm_Zw1_le`), under `ValidCore`. -/
theorem Zw1_step {R : RGPar 2 L N} {j : ℕ} (hV : ValidCore R j) {st : RawSt 2 L N}
    (H : RawInv R j st) (ih : ‖stZ' R st * st.w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2)
    (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N) :
    ‖stZ' R (rawStep R j st g μ D K).st * (rawStep R j st g μ D K).st.w1‖ ≤
      R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 := by
  have hV' := hV
  obtain ⟨hj2, -, hL8, hρ, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hζ : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ st).trans hρ8
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hZ'n : 0 < ‖stZ' R st‖ := norm_pos_iff.2 hZ'
  obtain ⟨hC, -⟩ := H.covL hV
  have hz := zero_mode_le (C := stCov R j st) hj2 hC
  have hℓC : (fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) * R.ℓ / 4) ^ 2 =
      R.ℓ ^ 2 / (16 * ‖stZ' R st‖) := by
    rw [div_pow, mul_pow, show fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) ^ 2 =
      ‖stZ' R st‖⁻¹ from by unfold fscale; rw [Real.sq_sqrt (inv_nonneg.2 (norm_nonneg _))]; rfl]
    field_simp; ring
  rw [hℓC] at hz
  have hzZ : ‖stZ' R st * ∑ x, stCov R j st x 0‖ ≤
      9 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 := by
    rw [norm_mul]
    calc ‖stZ' R st‖ * ‖∑ x, stCov R j st x 0‖
        ≤ ‖stZ' R st‖ * (9 * ((L : ℝ) ^ (j + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * ‖stZ' R st‖))) :=
          mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = _ := by field_simp
  set st' := (rawStep R j st g μ D K).st
  have hst'Z : st'.Z = stZ' R st := rfl
  have hζ' : ‖stZeta R st'‖ ≤ 1 / 8 := (norm_stZeta_le hρ st').trans hρ8
  have e : stZ' R st' * st'.w1 = (1 + stZeta R st') *
      (stZ' R st * st.w1 + stZ' R st * ∑ x, stCov R j st x 0) := by
    show st'.Z * (1 + stZeta R st') * (st.w1 + ∑ x, stCov R j st x 0) = _
    rw [hst'Z]; ring
  rw [e, norm_mul]
  have h1 : ‖1 + stZeta R st'‖ ≤ 9 / 8 := by
    refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have h2 := (norm_add_le _ _).trans (add_le_add ih hzZ)
  have hL2 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
    nlinarith
  have hP : ((L : ℝ) ^ (j + 1)) ^ 2 = (L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2 := by ring
  rw [hP] at h2 ⊢
  have hl : 0 ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2 := by positivity
  calc ‖1 + stZeta R st'‖ * ‖stZ' R st * st.w1 + stZ' R st * ∑ x, stCov R j st x 0‖
      ≤ 9 / 8 * (R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2 +
          9 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) := by nlinarith

/-- **`|Z_{j+1} w^{(1)}_j| ≤ ℓ² L^{2j}` along histories**, with `ValidAt` below `j` only. -/
theorem Zw1_hist (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hρ : 0 ≤ R.ρ) :
    ∀ j, (∀ i < j, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
      ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2
  | 0, _, t => by
    have : (rawHist R 0 t).w1 = 0 := rfl
    rw [this, mul_zero, norm_zero]; positivity
  | j + 1, hV, t => Zw1_step (hV j (by omega)).toValidCore
      (rawInv_hist R hρ j (fun i hi => hV i (by omega)) t)
      (Zw1_hist R hρ j (fun i hi => hV i (by omega)) t) _ _ _ _

/-- `|n| ≤ 4 |μ| |Z' w^{(1)}| / L^{2j}` for the clamped factor `n = nCor(ν♭, w^{(1)})`. -/
theorem norm_nCor_stNu_le (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (μ : ℝ) :
    ‖nCor (stNu R j st μ) st.w1‖ ≤ 4 * |μ| * ‖stZ' R st * st.w1‖ / ((L : ℝ) ^ j) ^ 2 := by
  unfold nCor
  refine (norm_clampDisk_le_self (by norm_num) _).trans (le_of_eq ?_)
  have e : 4 * stNu R j st μ * st.w1 = 4 * (μ : ℂ) * (stZ' R st * st.w1) / (L : ℂ) ^ (2 * j) := by
    unfold stNu; ring
  rw [e, norm_div, norm_mul, norm_mul, Complex.norm_real, norm_pow, Complex.norm_natCast,
    Real.norm_eq_abs, show ‖(4 : ℂ)‖ = 4 by simp, show (L : ℝ) ^ (2 * j) = ((L : ℝ) ^ j) ^ 2 by
      ring]

/-! ### The step `j = N - 2` -/

/-- The constant of the band at the step `j = N - 2`. -/
def cB1 (R : RGPar 2 L N) (Λ κ cm cT C₂ Cqb Clb cSb : ℝ) : ℝ :=
  4 * (4 * R.ℓ ^ 2 * cmu Λ cm + 2 * cZ R + 4 * R.ℓ ^ 2 * cMu R Λ cm) +
    2 * (cE R Λ κ cm cT C₂ Cqb Clb cSb / R.ℓ ^ 2)

set_option maxHeartbeats 4000000 in
/-- **The weak band of one step under `ValidAtL`**: for inputs as in `glue_core` and with
`|Z_{j+1} w^{(1)}_j| ≤ ℓ² L^{2j}`, `|ǧ' - ǧ| ≤ c_{B1} ǧ²`. -/
theorem band_core {C₀ η εs CK C₂ CD Cq Cl cS Cqg Clg cSg Cqb Clb cSb : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS) (hGB : GStepBound L R.A Cqg Clg cSg)
    (hGBd : GStepBand L R.A Cqb Clb cSb)
    {j : ℕ} (hVL : ValidAtL R j) {st : RawSt 2 L N} (HI : RawInv R j st)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ κ cg cm cT ε : ℝ} (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hκ₁ : kap1 L R.A C₀ η ≤ 1) (hCK : 0 ≤ CK) (hCD : 0 ≤ CD)
    (hCqg : 0 ≤ Cqg) (hClg : 0 ≤ Clg) (hcSg : 1 ≤ cSg)
    (hCqb : 0 ≤ Cqb) (hClb : 0 ≤ Clb) (hcSb : 1 ≤ cSb)
    (hcE : cE R Λ κ cm cT C₂ Cqg Clg cSg * ε ≤ R.ℓ ^ 2 / 24) (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1)
    {g μ : ℝ} (x : Xs R j) (hg : 0 < g) (hgε : g ≤ ε) (hμ : |μ| ≤ cmu Λ cm * g)
    (hx : ‖x‖ ≤ cx κ cT * g ^ 3)
    (hz : ‖st.z / st.Z‖ ≤ cZ R * g) (hy : ‖st.y / st.Z‖ ≤ cZ R * g)
    (hWl : Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2))
    (hw1 : ‖stZ' R st * st.w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2) :
    ‖(rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).g - g‖ ≤
      cB1 R Λ κ cm cT C₂ Cqb Clb cSb * g ^ 2 := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hρ8 : R.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hρ1 : R.ρ < 1 := by linarith
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcr : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
  have hcmu := H.hcmu
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg3' : g ^ 3 ≤ ε * g := by nlinarith [pow_le_one₀ hg.le hg1 (n := 2)]
  have hg3g : g ^ 3 ≤ g * g := by nlinarith [pow_le_one₀ hg.le hg1 (n := 2)]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤
      cR R Λ cm C₂ * g := by
    refine hv.trans ?_; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ (cR R Λ cm C₂ * g) ^ 2 := by
    have hdd : ‖x.1‖ ≤ g ^ 2 := by
      have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
        rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
      have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
    unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hr1' : cR R Λ cm C₂ * g ≤ 1 := (mul_le_mul_of_nonneg_left hgε hcr).trans hr1
  have hk8 : 8 * ‖x.2‖ ≤ 1 := by
    have hk3 : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
      have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
      exact mul_le_mul_of_nonneg_left this H.hcx
    linarith
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hv0 : 0 ≤ cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g := by
    have hM : 0 ≤ cM := Nat.cast_nonneg _; positivity
  -- the output couplings
  obtain ⟨o1, o2, o3, -, -, -, -, -⟩ := glue_core R hSB hGB hVL HI hm H hκ₁ hCK hCD hCqg hClg
    hcSg hcE hr1 hk1 x hg hgε hμ hx hz hy hWl
  -- the band of the step
  have b := hGBd N R j hVL st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) hm hg.le (cZ R * g) hz hy hη hηs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ (cR R Λ cm C₂ * g) (by positivity) (norm_nonneg _)
    (norm_nonneg _) hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x))
    hvr hwr hr1' hk8
  -- the remainder `E = O(ǧ²)`
  have hk' : ‖x.2‖ ≤ cx κ cT * (g * g) :=
    hx2.trans (mul_le_mul_of_nonneg_left hg3g H.hcx)
  have hEg := rem_bound_cE R hCqb hClb (le_trans zero_le_one hcSb) H.hcx hg.le hg.le hk' hv0 hvr
    hwr (le_of_eq (sq g)) (Cq := Cqb) (Cl := Clb) (cS := cSb)
  have hgE : gErr L Cqb Clb cSb R.ℓ ‖x.2‖ (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) +
      8 * R.ℓ ^ 4 * g) (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖) ≤
      cE R Λ κ cm cT C₂ Cqb Clb cSb / R.ℓ ^ 2 * g ^ 2 := by
    unfold gErr
    rw [div_div, div_le_iff₀ (by positivity)]
    have e : cE R Λ κ cm cT C₂ Cqb Clb cSb / R.ℓ ^ 2 * g ^ 2 * (R.ℓ ^ 2 * R.ℓ ^ 2) =
        cE R Λ κ cm cT C₂ Cqb Clb cSb * g * R.ℓ ^ 2 * g := by
      field_simp
    rw [e]; exact hEg
  -- `n`
  have hn : ‖nCor (stNu R j st μ) st.w1‖ ≤ 4 * R.ℓ ^ 2 * cmu Λ cm * g := by
    refine (norm_nCor_stNu_le R j st μ).trans ?_
    have hL : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    rw [div_le_iff₀ hL]
    have := mul_le_mul hμ hw1 (norm_nonneg _) (by positivity)
    nlinarith
  -- `ζ'`
  have hζ2 : ‖stZeta2 R j st g μ (rawD R st.u x) (rawK R st.u x)‖ ≤ 2 * cZ R * g := by
    have o1' : ‖stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 0 / stZ' R st‖ ≤ cZ R * g := o1
    have o2' : ‖stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 1 / stZ' R st‖ ≤ cZ R * g := o2
    unfold stZeta2 absorbZeta
    refine (norm_clampDisk_le_self hρ0 _).trans ?_
    rw [add_div]
    refine (norm_add_le _ _).trans ?_
    linarith
  -- `n'`
  have hst' := Zw1_step hVL.2 HI hw1 g μ (rawD R st.u x) (rawK R st.u x)
  have hZ2 : stZ2 R j st g μ (rawD R st.u x) (rawK R st.u x) ≠ 0 := by
    have hζ : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ0 st).trans hρ8
    have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
    exact mul_ne_zero hZ' (one_add_ne_zero ((absorb_le R hρ0 _ _).trans_lt hρ1))
  have hst'' : ‖stZ2 R j st g μ (rawD R st.u x) (rawK R st.u x) *
      stW1 R j st‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 := hst'
  have hnu' : ‖(rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).nu‖ ≤ cMu R Λ cm * g := by
    have h1 := norm_le_insert' (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).nu
      ((L : ℂ) ^ 2 * (μ : ℂ))
    have e : ‖(L : ℂ) ^ 2 * (μ : ℂ)‖ = (L : ℝ) ^ 2 * |μ| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [e] at h1
    have a1 := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    unfold cMu
    linarith only [h1, o3, a1]
  have hn' : ‖nCor (stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 2) (stW1 R j st)‖ ≤
      4 * R.ℓ ^ 2 * cMu R Λ cm * g := by
    unfold nCor
    refine (norm_clampDisk_le_self (by norm_num) _).trans ?_
    have e : 4 * stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 2 * stW1 R j st =
        4 * (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).nu *
          (stZ2 R j st g μ (rawD R st.u x) (rawK R st.u x) * stW1 R j st) /
          (L : ℂ) ^ (2 * (j + 1)) := by
      rw [rawStep_nu]
      have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
      field_simp
    have hL : (0 : ℝ) < ((L : ℝ) ^ (j + 1)) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    rw [e, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
      show ‖(4 : ℂ)‖ = 4 by simp, show (L : ℝ) ^ (2 * (j + 1)) = ((L : ℝ) ^ (j + 1)) ^ 2 by ring,
      div_le_iff₀ hL]
    have hcM : 0 ≤ cMu R Λ cm * g := (norm_nonneg _).trans hnu'
    have := mul_le_mul hnu' hst'' (norm_nonneg _) hcM
    nlinarith
  -- assembly
  have hsum := add_le_add (add_le_add hn hζ2) hn'
  have h4 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 4 * g)
  unfold cB1
  have e : (4 * (4 * R.ℓ ^ 2 * cmu Λ cm + 2 * cZ R + 4 * R.ℓ ^ 2 * cMu R Λ cm) +
      2 * (cE R Λ κ cm cT C₂ Cqb Clb cSb / R.ℓ ^ 2)) * g ^ 2 =
      4 * g * (4 * R.ℓ ^ 2 * cmu Λ cm * g + 2 * cZ R * g + 4 * R.ℓ ^ 2 * cMu R Λ cm * g) +
        2 * (cE R Λ κ cm cT C₂ Cqb Clb cSb / R.ℓ ^ 2 * g ^ 2) := by ring
  rw [e]
  linarith only [b, h4, hgE]

/-! ### The last step `j = N - 1` -/

/-- **The final quartic coupling** `ǧ_N = κ_N.g/Z_N²` (complex). -/
def lastG (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ)
    (t : Hist.Seq (Xs R)) : ℂ :=
  (lastOut R Nh t).κ.g / (lastOut R Nh t).Z ^ 2

/-- **The final real quartic coupling** `Re ǧ_N` (the coordinate on which the shooting is done). -/
def gFin (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ)
    (t : Hist.Seq (Xs R)) : ℝ :=
  (lastG R Nh t).re

/-- `ǧ_N = ǧ_{N-1}/(1 + n_{N-1})`: the `g`-coefficient of `V_N = V_{κ_N}` is the first-order
term only (no localisation at the last step). -/
theorem lastG_eq (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ)
    (t : Hist.Seq (Xs R)) (hZ : stZ' R (histOut R Nh t).st ≠ 0) :
    lastG R Nh t = stGr R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re
      (histOut R Nh t).nu.re := by
  show (stKap R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re
      (histOut R Nh t).nu.re).g / stZ' R (histOut R Nh t).st ^ 2 = _
  show stGr R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re *
      stZ' R (histOut R Nh t).st ^ 2 / stZ' R (histOut R Nh t).st ^ 2 = _
  field_simp

/-- `|ǧ/(1 + n) - ǧ| ≤ (8/7) ǧ |n|`, `|n| ≤ 4|μ| |Z' w^{(1)}|/L^{2j}`. -/
theorem stGr_sub_leN (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) {g : ℝ} (hg : 0 ≤ g) (μ : ℝ) :
    ‖stGr R j st g μ - g‖ ≤
      8 / 7 * g * (4 * |μ| * ‖stZ' R st * st.w1‖ / ((L : ℝ) ^ j) ^ 2) := by
  have h7 := norm_one_add_nCor (stNu R j st μ) st.w1
  have hne : 1 + nCor (stNu R j st μ) st.w1 ≠ 0 := fun h => by
    rw [h, norm_zero] at h7; linarith
  have e : stGr R j st g μ - g = -(g : ℂ) * nCor (stNu R j st μ) st.w1 /
      (1 + nCor (stNu R j st μ) st.w1) := by
    unfold stGr; field_simp; ring
  rw [e, norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg,
    div_le_iff₀ (by linarith)]
  have hn := norm_nCor_stNu_le R j st μ
  have h0 : 0 ≤ 4 * |μ| * ‖stZ' R st * st.w1‖ / ((L : ℝ) ^ j) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hn hg
  nlinarith [mul_le_mul_of_nonneg_left h7 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 7)
    (mul_nonneg hg h0))]

/-! ### Along a regular history -/

/-- The constant of the weak band of the last two steps. -/
def cBand (R : RGPar 2 L N) (Λ κ cm cT C₂ Cqb Clb cSb : ℝ) : ℝ :=
  cB1 R Λ κ cm cT C₂ Cqb Clb cSb + 96 / 7 * R.ℓ ^ 2 * cMu R Λ cm

/-- **The weak band of the last two steps along the history `t`**, in terms of `ǧ = ǧ_{N_h}`:
`|ǧ_{N_h+1} - ǧ| ≤ C ǧ²` (complex `ǧ_{N_h+1}`) and `|ǧ_N - Re ǧ_{N_h+1}| ≤ C ǧ²`. -/
def BandOut (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (C : ℝ)
    (t : Hist.Seq (Xs R)) : Prop :=
  ‖(histOut R Nh t).g - (t Nh).1‖ ≤ C * (t Nh).1 ^ 2 ∧
    ‖lastG R Nh t - (histOut R Nh t).g.re‖ ≤ C * (t Nh).1 ^ 2

theorem BandOut.gFin_sub {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {C : ℝ}
    {t : Hist.Seq (Xs R)} (h : BandOut R Nh C t) :
    |gFin R Nh t - (t Nh).1| ≤ 2 * C * (t Nh).1 ^ 2 := by
  have h1 : |(histOut R Nh t).g.re - (t Nh).1| ≤ C * (t Nh).1 ^ 2 := by
    have := Complex.abs_re_le_norm ((histOut R Nh t).g - (t Nh).1)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans h.1
  have h2 : |gFin R Nh t - (histOut R Nh t).g.re| ≤ C * (t Nh).1 ^ 2 := by
    have := Complex.abs_re_le_norm (lastG R Nh t - (histOut R Nh t).g.re)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans h.2
  have := abs_sub_le (gFin R Nh t) (histOut R Nh t).g.re (t Nh).1
  linarith

set_option maxHeartbeats 4000000 in
/-- **The weak band of the last two steps along a regular history.** -/
theorem band_hist {C₀ η εs CK C₂ CD Cq Cl cS Cqg Clg cSg Cqb Clb cSb C : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS) (hGB : GStepBound L R.A Cqg Clg cSg)
    (hGBd : GStepBand L R.A Cqb Clb cSb)
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j ≤ Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hκ₁ : kap1 L R.A C₀ η ≤ 1) (hCK : 0 ≤ CK) (hCD : 0 ≤ CD)
    (hCqg : 0 ≤ Cqg) (hClg : 0 ≤ Clg) (hcSg : 1 ≤ cSg)
    (hCqb : 0 ≤ Cqb) (hClb : 0 ≤ Clb) (hcSb : 1 ≤ cSb)
    (hcE : cE R Λ κ cm cT C₂ Cqg Clg cSg * ε ≤ R.ℓ ^ 2 / 24) (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1) (hC : cBand R Λ κ cm cT C₂ Cqb Clb cSb ≤ C)
    (t : Hist.Seq (Xs R)) (ht : Hist.InDh Λ β δ κ cg cm cT ε Nh t) :
    BandOut R Nh C t := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hρ8 : R.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hSB' := hSB.toStepBounds hVL.1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB' hV (fun j hj => hm j hj.le) hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 Nh le_rfl
  have HI := rawInv_hist R hρ0 Nh hV t
  have hw1 := Zw1_hist R hρ0 Nh hV t
  have hb1 := band_core R hSB hGB hGBd hVL HI (hm Nh le_rfl) H hκ₁ hCK hCD hCqg hClg hcSg hCqb
    hClb hcSb hcE hr1 hk1 (t Nh).2.2 hg hgε hμ hx hz hy hWl hw1
  obtain ⟨-, -, o3, -, -, -, o7, o8⟩ := glue_step R hSB hGB hV hVL
    (fun j hj => hm j hj) hβ hδ1 H hκ₁ hCK hCD hCqg hClg hcSg hcE hr1 hk1 t ht
  have hcmu := H.hcmu
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  -- `ν'`
  have hnu : ‖(histOut R Nh t).nu‖ ≤ cMu R Λ cm * (t Nh).1 := by
    have h1 := norm_le_insert' (histOut R Nh t).nu ((L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ))
    have e : ‖(L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ)‖ = (L : ℝ) ^ 2 * |(t Nh).2.1| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [e] at h1
    have a1 := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    unfold cMu
    linarith only [h1, o3, a1]
  have hcMu : 0 ≤ cMu R Λ cm := by
    have := (norm_nonneg _).trans hnu
    exact nonneg_of_mul_nonneg_left this hg
  have hμ' : |(histOut R Nh t).nu.re| ≤ cMu R Λ cm * (t Nh).1 :=
    (Complex.abs_re_le_norm _).trans hnu
  have hg'0 : 0 ≤ (histOut R Nh t).g.re := le_trans (by positivity) o8
  have hg' : (histOut R Nh t).g.re ≤ 3 * (t Nh).1 :=
    (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans o7
  -- the last step
  have HI' : RawInv R (Nh + 1) (histOut R Nh t).st :=
    (RawInv.stepL hVL HI (t Nh).1 (t Nh).2.1 (rawD_mem R _ _) (rawK_mem R _ _)).1
  have hZ' : stZ' R (histOut R Nh t).st ≠ 0 := by
    have hζ : ‖stZeta R (histOut R Nh t).st‖ ≤ 1 / 8 :=
      (norm_stZeta_le hρ0 _).trans hρ8
    exact mul_ne_zero (HI'.Z_ne_zero (by linarith)) (one_add_ne_zero (by linarith))
  have hw1' : ‖stZ' R (histOut R Nh t).st * (histOut R Nh t).st.w1‖ ≤
      R.ℓ ^ 2 * ((L : ℝ) ^ (Nh + 1)) ^ 2 := Zw1_step hVL.2 HI hw1 _ _ _ _
  have hlast := stGr_sub_leN R (Nh + 1) (histOut R Nh t).st hg'0 (histOut R Nh t).nu.re
  rw [← lastG_eq R Nh t hZ'] at hlast
  have hL : (0 : ℝ) < ((L : ℝ) ^ (Nh + 1)) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hq : 4 * |(histOut R Nh t).nu.re| * ‖stZ' R (histOut R Nh t).st * (histOut R Nh t).st.w1‖ /
      ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 4 * R.ℓ ^ 2 * (cMu R Λ cm * (t Nh).1) := by
    rw [div_le_iff₀ hL]
    have := mul_le_mul hμ' hw1' (norm_nonneg _) (by positivity)
    nlinarith
  have hq0 : 0 ≤ 4 * |(histOut R Nh t).nu.re| *
      ‖stZ' R (histOut R Nh t).st * (histOut R Nh t).st.w1‖ / ((L : ℝ) ^ (Nh + 1)) ^ 2 := by
    positivity
  have hl2 : ‖lastG R Nh t - (histOut R Nh t).g.re‖ ≤
      96 / 7 * R.ℓ ^ 2 * cMu R Λ cm * (t Nh).1 ^ 2 := by
    refine hlast.trans ?_
    have a1 := mul_le_mul hg' hq hq0 (by positivity)
    have a2 := mul_le_mul_of_nonneg_left a1 (by norm_num : (0 : ℝ) ≤ 8 / 7)
    nlinarith
  have hC1 : cB1 R Λ κ cm cT C₂ Cqb Clb cSb ≤ C := by
    unfold cBand at hC
    have : 0 ≤ 96 / 7 * R.ℓ ^ 2 * cMu R Λ cm := by positivity
    linarith
  have hC2 : 96 / 7 * R.ℓ ^ 2 * cMu R Λ cm ≤ C := by
    have h0 : 0 ≤ cB1 R Λ κ cm cT C₂ Cqb Clb cSb * (t Nh).1 ^ 2 := (norm_nonneg _).trans hb1
    have h1 := nonneg_of_mul_nonneg_left h0 (by positivity)
    unfold cBand at hC; linarith
  exact ⟨hb1.trans (mul_le_mul_of_nonneg_right hC1 (sq_nonneg _)),
    hl2.trans (mul_le_mul_of_nonneg_right hC2 (sq_nonneg _))⟩

end

end Step2
