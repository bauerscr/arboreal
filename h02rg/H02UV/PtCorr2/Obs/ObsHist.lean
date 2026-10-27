import PtCorr2.Obs.KObsHist
import PtCorr2.Obs.VObsStep

/-!
# The coupled observable recursion along the history (Case (1), the `σ_a` part)

The three one-step bounds (`kobs_raw_step`, `wobs_raw_step`, `beta_raw_step`) are combined along a
regular history, with the weights `Obs2.wA = (1,0,0)`:

* `WObsBounds`, `BetaBounds`: the conclusions of `wobs_raw_step`, `beta_raw_step` as named
  properties of the constants (as `KObsBounds`);
* `wobs_hist_step`, `beta_hist_step`: one step along the history (plumbing as `kobs_hist_step`);
* **`obs_hist`**: with `r_j = c_R g_j`, `s_j` the causal field scale,
  `q_j = max(1, s_{j+1}/s_j)`, `c_W = 2C₁ + 1` and the comparison sequence
  `M_{j+1} = M_j q_j (1 + C_M r_j)` (`Mseq`), by a joint induction,

    `s_j ∑_B |m₁(V_j(B)_a)| ≤ M_j`, `‖𝒲^{obs}_j(B)‖ ≤ c_W r_j M_j`,
    `A^{(|𝓑_j(X)|-4)_+}‖K^{obs}_j(X)‖ ≤ kseq(8θ̄) B r (c_W M) j`.

  This discharges the observable size inputs `m_j = c_W M_j` of `kobs_hist` (`m_j ≤ m_{j+1}`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The conclusion of `wobs_raw_step` for given constants. -/
def WObsBounds (L : ℕ) [NeZero L] (Kw C₁ ε₁ : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.ab = 0 →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o →
    ∀ wl dd r mV mW : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ ε₁ → 0 ≤ mV → 0 ≤ mW →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ) ((obsStep R P j st g μ D K o).W c') ≤
          ENNReal.ofReal ((Kw / L + C₁ * r) * mW + C₁ * r * mV)

theorem wobs_bounds : ∃ (Kw : ℝ) (L₀ : ℕ), 0 ≤ Kw ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBounds L Kw C₁ ε₁ :=
  wobs_raw_step

/-- The conclusion of `beta_raw_step` for given constants. -/
def BetaBounds (L : ℕ) [NeZero L] (Cm : ℝ) (cs cn : ℕ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (P : ObsPts 2 L N) (o : ObsSt .one L N), o.IsObs → ObsLocInv P j o → ObsSymInv j o →
      (∀ b, (o.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) →
    ∀ wl dd r mV mW k : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ 1 → 0 ≤ mV → 0 ≤ mW → 0 ≤ k →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      (∀ X, IsSmall j X → oTo Obs2.wA j (fscale st.Z * R.ℓ) (o.K X) ≤ ENNReal.ofReal k) →
      ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          ‖mass1L (-1) ((obsStep R P j st g μ D K o).V c' : SA .one (Lam 2 L N)).a‖ ≤
        ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass1L (-1) (o.V b : SA .one (Lam 2 L N)).a‖ +
          cs * Cm * (fscale st.Z * R.ℓ)⁻¹ * (8 * k) +
          Cm * (fscale (stZ' R st) * R.ℓ)⁻¹ * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 * r *
            (fscale st.Z * R.ℓ) *
            ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass1L (-1) (o.V b : SA .one (Lam 2 L N)).a‖ +
            cn * Step2.Q1 2 * mW)

theorem beta_bounds : ∃ (Cm : ℝ) (cs cn : ℕ) (L₀ : ℕ), 0 ≤ Cm ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → BetaBounds L Cm cs cn :=
  beta_raw_step

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- The raw data of step `j` of a regular history (the plumbing of `kobs_hist_step`). -/
theorem hist_raw (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) :
    let st := rawHist R j t
    let g := (t j).1
    let x := (t j).2.2
    let r := cR R Λ cm C₂ * g
    ValidCore R j ∧ RawInv R j st ∧ 0 ≤ g ∧ g ≤ ε ∧
    ‖st.z / st.Z‖ ≤ cZ R * g ∧ ‖st.y / st.Z‖ ≤ cZ R * g ∧ 2 * (cZ R * g) ≤ R.ρ ∧
    8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 ∧
    Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2) ∧
    Fnorm j (fscale st.Z * R.ℓ) (rawD R st.u x) ≤ ENNReal.ofReal ‖x.1‖ ∧
    cM * R.ℓ ^ 2 * (2 * |(t j).2.1| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r ∧
    cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 ∧ 0 < r ∧ r ≤ cR R Λ cm C₂ * ε ∧
    0 ≤ cW R Λ cm C₂ ∧ 0 < fscale st.Z * R.ℓ ∧ 0 < fscale (stZ' R st) * R.ℓ := by
  intro st g x r
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set μ := (t j).2.1
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; show _ ≤ cR R Λ cm C₂ * g; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    show _ ≤ (cR R Λ cm C₂ * g) ^ 2; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hr0 : 0 < r := by show 0 < cR R Λ cm C₂ * g; positivity
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε (by linarith)
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by
    rw [hζ]; exact hzy.trans (by linarith [hVj.2.2.2.2.1])
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  exact ⟨hVj.toValidCore, HI, hg.le, hgε, hz, hy, hη, hηs, hWl, le_of_eq (Fnorm_rawD R HI.hu hZ x),
    hvr, hwr, hr0, hrε, hcw, mul_pos (fscale_pos hZ) hℓ, mul_pos (fscale_pos hZ') hℓ⟩

/-- **One step of `𝒲^{obs}` along the history.** -/
theorem wobs_hist_step {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) (histS R (j + 1) t) ((obsHist R P o₀ (j + 1) t).W c') ≤
        ENNReal.ofReal ((Kw / L + C₁ * (cR R Λ cm C₂ * (t j).1)) * mW +
          C₁ * (cR R Λ cm C₂ * (t j).1) * mV) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hsym := obsSymInv_hist R P o₀ hs0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  exact hWB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 _ _ (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs c P w hw0 (obsHist R P o₀ j t) hobs hloc hsym _ _ _ mV mW
    (by positivity) (norm_nonneg _) hr0.le (hrε.trans hε₁) hmV hmW hWl hDd hvr hwr hVo hWo

/-- **One step of the `ℓ¹` coupling along the history** (Case (1)). -/
theorem beta_hist_step {Cm : ℝ} {cs cn : ℕ} (hBB : BetaBounds L Cm cs cn)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀)
    (hs0 : ObsSymInv 0 o₀) (hf0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a))
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (mV mW k : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW) (hk : 0 ≤ k)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).W b) ≤ ENNReal.ofReal mW)
    (hKo : ∀ X, IsSmall j X → oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).K X) ≤
      ENNReal.ofReal k) :
    ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        ‖mass1L (-1) ((obsHist R P o₀ (j + 1) t).V c' : SA .one (Lam 2 L N)).a‖ ≤
      ∑ b ∈ blockIdx (L := L) (N := N) j,
          ‖mass1L (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖ +
        cs * Cm * (histS R j t)⁻¹ * (8 * k) +
        Cm * (histS R (j + 1) t)⁻¹ * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 *
          (cR R Λ cm C₂ * (t j).1) * histS R j t *
          ∑ b ∈ blockIdx (L := L) (N := N) j,
            ‖mass1L (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖ +
          cn * Step2.Q1 2 * mW) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hsym := obsSymInv_hist R P o₀ hs0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  have hform : ∀ b, ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a) :=
    fun b => by rw [← histVO_a]; exact obsHist_hform R P o₀ t hf0 j b
  exact hBB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 _ _ (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs P (obsHist R P o₀ j t) hobs hloc hsym hform _ _ _ mV mW k
    (by positivity) (norm_nonneg _) hr0.le (hrε.trans hε1) hmV hmW hk hWl hDd hvr hwr hVo hWo hKo

end Hist

end

end PtCorr2
