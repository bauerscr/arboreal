import PtCorr2.Obs.ObsHistU
import Obs2.Est.WObsU

/-!
# The `𝒲^{obs}` step for unreduced states at the raw level (crude, full `ab` part)

**`wobs_raw_fullWU`** (`WObsBoundsU L C_W`): for the unreduced observable state (`ObsLocInv`;
no coalescence hypothesis), finite or infinite weights with `w.Sub`, `‖V^{obs}‖_w ≤ m`,
`‖𝒲^{obs}‖_w ≤ rm`, `r ≤ m`, `r ≤ 1`, the bulk radius `r` (as in `kobs_raw_stepU`):

  `‖𝒲_{j+1}(B_+)‖^{obs}_w ≤ e^{L²C_W(r + m²)} − 1`

for every `(j+1)`-block. In particular in the weights `wM M_aM_b` (`m ≍ 1`) the `ab` part of
`𝒲_{j+1}` is `O(1)·M_aM_b`. From `Obs2.wpO_fullWU`, `Obs2.Wnext2O_full_le`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The conclusion of `wobs_raw_fullWU` for a given constant. -/
def WObsBoundsU (L : ℕ) [NeZero L] (Cw : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o →
    ∀ wl dd r m : ℝ, 0 ≤ wl → 0 ≤ dd → 0 < r → r ≤ 1 → r ≤ m →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal (r * m)) →
      ∀ c' : Fin 2 → ℕ,
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ) ((obsStep R P j st g μ D K o).W c') ≤
          ENNReal.ofReal (Real.exp ((L : ℝ) ^ 2 * (Cw * (r + m ^ 2))) - 1)

set_option maxHeartbeats 2000000 in
/-- **The `𝒲^{obs}` step at the raw level, unreduced states, full norm.** -/
theorem wobs_raw_fullWU : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ Cw : ℝ, 0 ≤ Cw ∧ WObsBoundsU L Cw := by
  obtain ⟨L₀, h⟩ := wpO_fullWU 2 le_rfl
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨Cw, hCw, h⟩ := h L hL
  refine ⟨Cw, hCw, ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ c P w hwS o ho hloc wl dd r m hwl0 hdd0
    hr0 hr1 hrm hWl hDd hvr hwr hVo hWo c'
  have hV' := hV
  obtain ⟨hj1, -, hL8, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ ηz := (norm_nonneg _).trans hz
  have hjN : j < N := by omega
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * ηz := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  set s' := fscale (stZ' R st)
  have hs := fscale_pos hZ
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hs' : 0 < s' := fscale_pos hZ'
  have hsc := scale_ok hZ hζ8 hℓ
  have hsc' : s' * R.ℓ + s' * R.ℓ / 4 ≤ 3 / 2 * (fscale st.Z * R.ℓ) := hsc
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  have hsum : s' * R.ℓ + s' * R.ℓ / 4 ≤ 2 * (fscale st.Z * R.ℓ) := by linarith
  obtain ⟨hC0, -, -, -⟩ := H.covL hV
  have hC : GoodCov2 j (s' * R.ℓ / 4) (stCov R j st) := hC0
  obtain ⟨hVv, -⟩ := rg_inputs R j hV st H g μ hm hg0 ηz hz hy hηρ
  have hVf_mem : stVf R j st g μ ∈ BSub (L := L) (N := N) j := by
    rw [stVf_eq_kap]
    exact VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN (stKap R j st g μ).toVec
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  have hVo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullV R j st g μ o b) ≤ ENNReal.ofReal m :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hVo b hb)
  have hWo' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (fscale st.Z * R.ℓ) (fullW st D o b) ≤ ENNReal.ofReal (r * m) :=
    fun b hb => (oTo_emb_add_le w j _ _ _).trans (hWo b hb)
  have HL := olocS_full R P g μ hV H hD hK hloc
  have hWp := h N j (by omega) (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) hsℓ
    (mul_pos hs' hℓ) (by positivity) hsum (stCov R j st) hC c P w hwS
    (fullV R j st g μ o) (fullW st D o)
    (fun b => cmpInA_of_osub (HL.hV b)) (fun b => cmpInA_of_osub (HL.hW b))
    (by rw [bulkF_fullV R j st g μ ho]; exact hVf_mem.1)
    (by rw [bulkF_fullW st D ho]; exact (add_mem H.hWl hD).1)
    (by rw [bulkF_fullV R j st g μ ho]; exact fun b => eps_VfamL j _ b)
    r m hr0 hr1 hrm
    (by rw [bulkF_fullV R j st g μ ho]; exact hVv.trans (ENNReal.ofReal_le_ofReal hvr))
    (by rw [bulkF_fullW st D ho]; exact hw.trans (ENNReal.ofReal_le_ofReal hwr))
    hVo' hWo'
  have hW := Wnext2O_full_le (c' := c') hwS (mul_pos hs' hℓ)
    (by have := sq_nonneg m; positivity) hWp
  show oTo w (j + 1) (s' * R.ℓ) (πobs (Wnext2O P j (stCov R j st) (fullV R j st g μ o)
    (fullW st D o) c')) ≤ _
  rw [oTo_πobs]
  exact (oTo_le w _ _ _).trans hW

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 2000000 in
/-- **The `𝒲^{obs}` step along the history, unreduced states, full norm.** -/
theorem wobs_hist_fullWU {Cw : ℝ} (hWB : WObsBoundsU L Cw)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (m : ℝ) (hrm : cR R Λ cm C₂ * (t j).1 ≤ m) (hr1 : cR R Λ cm C₂ * (t j).1 ≤ 1)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (c' : Fin 2 → ℕ) :
    oTo w (j + 1) (histS R (j + 1) t) ((obsHist R P o₀ (j + 1) t).W c') ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) ^ 2 * (Cw * (cR R Λ cm C₂ * (t j).1 + m ^ 2))) - 1) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R Λ cm C₂ * g with hr
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    have := H.h3
    nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hg3 H.hcx]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hr0 : 0 < r := by rw [hr]; unfold cR; positivity
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  have key := hWB N R j hVj.toValidCore st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj)
    hg.le (cZ R * g) hz hy hη c P w hw (obsHist R P o₀ j t) hobs hloc
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ r m (by positivity) (norm_nonneg _) hr0 hr1 hrm hWl
    (le_of_eq (Fnorm_rawD R HI.hu hZ x)) hvr hwr hVo hWo c'
  rw [obsHist_succ]
  exact key

end Hist

end

end PtCorr2
