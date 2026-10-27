import Step2.Flow.FlowSharp1
import Step2.Last.FlowLastBand2

/-!
# (F1) at the step `j = N - 2`: the history inputs under `ValidAtL`

The one-loop inputs of the sharp (F1) chain (`FlowF1`, `FlowF1d`, `FlowHV`, `FlowSharp1`,
`FlowHor2Aux`) are stated along histories with `∀ i ≤ j, ValidAt R i`. At the step `j = N - 2`
only `ValidAt` below `j` and `ValidAtL R j` hold. All those inputs use the validity at the step `j`
only through the covariance part (`RawInv.cov`, the same as `RawInv.covL` for `ValidCore`) and
through `RawInv R (j + 1)` (`RawInv.stepL`). This file contains the copies with the hypotheses
`(∀ i < j, ValidAt R i)` and `ValidAtL R j`:

* `rawInv_histU`, `covU`: the invariants and the covariance properties up to `j + 1`;
* `histFS_goodU`, `hist_LS_gU`, `hist_S_decompU` (copies of `histFS_good`, `hist_LS_g`,
  `hist_S_decomp`);
* `stZ'_eq_dDataU`, `hbTil_eqU`, `hqTil_eqU`, `hcTil_eqU`, `f1Coef_eqU`, `hist_dData_hypsU`,
  `HV_histU`, `HD_histU`, `S01_histU`, `htad_eqU`, `HVs_histU` (copies of `FlowHV`, `FlowSharp1`);
* `HS_zetaU` (copy of `HS_zeta`) and `Mz_histU` (the `Mz` part of `HS_of_S01`).

The one-loop values (`HV`, `HV_sharp`, `HD`, `S0S1`) themselves hold for every `j + 1 < N`, in
particular at `j = N - 2`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Step2.D2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-! ### Invariants and covariances up to `j + 1` -/

/-- **The invariants along histories up to `j + 1`**, with `ValidAt` below `j` and `ValidAtL` at
`j`. -/
theorem rawInv_histU {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVL : ValidAtL R j)
    (t : Hist.Seq (Xs R)) : ∀ i ≤ j + 1, RawInv R i (rawHist R i t) := by
  have hρ : 0 ≤ R.ρ := hVL.2.2.2.2.1
  intro i hi
  rcases Nat.lt_or_ge i (j + 1) with h | h
  · exact rawInv_hist R hρ i (fun i' hi' => hV i' (by omega)) t
  · obtain rfl : i = j + 1 := by omega
    exact (RawInv.stepL hVL (rawInv_hist R hρ j hV t) (t j).1 (t j).2.1 (rawD_mem R _ _)
      (rawK_mem R _ _)).1

omit [Fact (0 < R.ℓ)] [Fact (0 < R.A)] in
/-- **The covariance properties up to `j`** (`RawInv.cov` below `j`, `RawInv.covL` at `j`). -/
theorem covU {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVL : ValidAtL R j) {i : ℕ} (hi : i ≤ j)
    {st : RawSt 2 L N} (H : RawInv R i st) :
    GoodCov2 i (fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) * R.ℓ / 4)
        (rawCov R i (RawInv.zeta' R i st)) ∧ TInv (rawCov R i (RawInv.zeta' R i st)) ∧
      CSym (rawCov R i (RawInv.zeta' R i st)) ∧
      ∀ x y, rawCov R i (RawInv.zeta' R i st) x y = rawCov R i (RawInv.zeta' R i st) y x := by
  rcases Nat.lt_or_ge i j with h | h
  · exact H.cov (hV i h)
  · obtain rfl : i = j := by omega
    exact H.covL hVL.2

/-! ### The flow sequence of a history -/

theorem histFS_goodU {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVL : ValidAtL R j)
    (t : Flow2.Hist.Seq (Xs R)) : ∀ i, GoodCov2 i (ellM R j t) ((histFS R j t).C i) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hnn : ∀ i ∈ range (j + 1), 0 ≤ fscale (stZ' R (rawHist R i t)) * R.ℓ / 4 := fun i _ => by
    unfold fscale; positivity
  intro i
  by_cases hi : i ≤ j
  · rw [histFS_C R t hi]
    have H := rawInv_histU R hV hVL t i (by omega)
    exact (covU R hV hVL hi H).1.mono (single_le_sum hnn (mem_range.2 (by omega)))
  · simp only [histFS, if_neg hi]
    exact goodCov2_zero i (sum_nonneg hnn)

/-- `hist_LS_g` with `ValidAtL` at `j`. -/
theorem hist_LS_gU {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVL : ValidAtL R j)
    (t : Flow2.Hist.Seq (Xs R)) :
    ∃ c₀ δ : ℂ, (∀ x, stCov R j (rawHist R j t) x x = c₀) ∧
      (∀ x e, stCov R j (rawHist R j t) (x + dirVec e) x = c₀ + δ) ∧
      cvec4 (blockSet (L := L) (N := N) j 0) R.i₀
        (LS j (stCov R j (rawHist R j t)) (stVf R j (rawHist R j t) (t j).1 (t j).2.1)
          (rawHist R j t).Wl 0 : Alg 2 L N) 3 =
        ∑ k ∈ range j, ((histFS R j t).κ k).g ^ 2 *
            (histFS R j t).beta j k 0 R.i₀ (eC 3) (eC 3) 3 +
          ((histFS R j t).κ j).g ^ 2 * (histFS R j t).betaQ j j 0 R.i₀ (eC 3) (eC 3) 3 +
          4 * (∑ x, stCov R j (rawHist R j t) x 0) * ((histFS R j t).κ j).g *
            (((histFS R j t).κ j).nu + 2 * (2 : ℕ) * ((histFS R j t).κ j).g * δ) := by
  have hVL' := hVL
  obtain ⟨-, hj2, hd, hL, -⟩ := hVL'
  have H := rawInv_histU R hV hVL t j (by omega)
  obtain ⟨-, -, hCs, hsym⟩ := covU R hV hVL le_rfl H
  set D := histFS R j t
  have hCj : D.C j = stCov R j (rawHist R j t) := histFS_C R t le_rfl
  have hCs' : CSym (D.C j) := by rw [hCj]; exact hCs
  have hsym' : ∀ x y, D.C j x y = D.C j y x := by rw [hCj]; exact hsym
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num) hCs' hsym'
  have h0 := zero_mem_blockIdx (d := 2) (L := L) (N := N) j
  have hk := D.kappaS_g (by norm_num) hL hj2 (histFS_goodU R hV hVL t) h0 R.i₀
    (covH_of_good hL hj2 (histFS_goodU R hV hVL t j) hCs' hsym')
    (region_of_size (by norm_num) hL hj2 h0) hc₀ hδ hδ'
  refine ⟨c₀, δ, fun x => by rw [← hCj]; exact hc₀ x, fun x e => by rw [← hCj]; exact hδ x e, ?_⟩
  have hW : (fun b' => sigE (D.s j) (D.Wlin j b')) = (rawHist R j t).Wl := by
    funext b'
    rw [histFS_Wlin R j t j (by omega)]
    exact sigE_one' _
  rw [hW, histFS_Vin, hCj] at hk
  rw [hk, ← hCj]

/-- `hist_S_decomp` with `ValidAt` below `j` only. -/
theorem hist_S_decompU {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (t : Hist.Seq (Xs R))
    {Λ β δ κ cg cm cT ε cZ' cn : ℝ} (ht : Hist.InDh Λ β δ κ cg cm cT ε j t) (hβ : 0 ≤ β)
    (hδ1 : δ ≤ 1 / 2) (hcg : 0 ≤ cg) (hcgβ : cg * ε ≤ β / 2) (hcg1 : cg * ε ≤ 1) (hε1 : ε ≤ 1)
    (hcZ : 0 ≤ cZ') (hcn : 0 ≤ cn)
    (hζ : ∀ i ≤ j, ‖stZeta R (rawHist R i t)‖ ≤ cZ' * (t i).1)
    (hn : ∀ k < j, ‖nCor (stNu R k (rawHist R k t) (t k).2.1) (rawHist R k t).w1‖ ≤ cn * (t k).1) :
    let z := stZ' R (rawHist R j t)
    let S := ∑ k ∈ range j, ((histFS R j t).κ k).g ^ 2 *
      (histFS R j t).beta j k 0 R.i₀ (eC 3) (eC 3) 3
    let ES := ∑ k ∈ range j, (stGr R k (rawHist R k t) (t k).1 (t k).2.1 ^ 2 *
      (stZ' R (rawHist R k t) / z) ^ 4 - ((t j).1 : ℂ) ^ 2) * hbTil R j t k
    S = z ^ 2 * (((t j).1 : ℂ) ^ 2 * ∑ k ∈ range j, hbTil R j t k + ES) ∧
      ‖ES‖ ≤ (24 * cZ' + 3 * cn + 2 * (2 * β + 1)) *
        (∑ k ∈ range j, ((j : ℝ) - k + 1) * 2 ^ (j - k) * ‖hbTil R j t k‖) * (t j).1 ^ 3 := by
  intro z S ES
  have hzne : ∀ i ≤ j, stZ' R (rawHist R i t) ≠ 0 := fun i hi => by
    have H := rawInv_hist R hρ i (fun i' hi' => hV i' (by omega)) t
    have hZ : (rawHist R i t).Z ≠ 0 := H.Z_ne_zero (by linarith)
    have hζ8 : ‖stZeta R (rawHist R i t)‖ ≤ 1 / 8 := (norm_stZeta_le hρ _).trans hρ8
    exact mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hz0 : z ≠ 0 := hzne j le_rfl
  refine ⟨?_, ?_⟩
  · simp only [S, ES, hbTil]
    rw [mul_add, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ j := (mem_range.1 hk).le
    have hzk := hzne k hk'
    have e : ((histFS R j t).κ k).g = stGr R k (rawHist R k t) (t k).1 (t k).2.1 *
        stZ' R (rawHist R k t) ^ 2 := rfl
    rw [e]
    field_simp
    ring
  · have hg := (ht.1 j le_rfl).1
    have hgε := (ht.1 j le_rfl).2.1
    have hg1 : (t j).1 ≤ 1 := hgε.trans hε1
    have hmon : ∀ i ≤ j, (t i).1 ≤ (t j).1 := fun i hi => by
      have h := (g_mono ht hβ hδ1 hcg hcgβ hcg1 i (j - i) (by omega)).1
      rwa [show i + (j - i) = j by omega] at h
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum, sum_mul]
    refine sum_le_sum fun k hk => ?_
    have hkj : k < j := mem_range.1 hk
    obtain ⟨hmono, hdiff⟩ := g_mono ht hβ hδ1 hcg hcgβ hcg1 k (j - k) (by omega)
    rw [show k + (j - k) = j by omega] at hmono hdiff
    have hdiff' : (t j).1 - (t k).1 ≤ ((j : ℝ) - k) * (2 * β + 1) * (t j).1 ^ 2 := by
      have e : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by push_cast [Nat.cast_sub hkj.le]; ring
      rw [← e]; exact hdiff
    have hgk := (ht.1 k (by omega)).1
    have hnk : ‖nCor (stNu R k (rawHist R k t) (t k).2.1) (rawHist R k t).w1‖ ≤ cn * (t j).1 :=
      (hn k hkj).trans (mul_le_mul_of_nonneg_left hmono hcn)
    have hz := stZ'_ratio R t k j hkj.le
    have hpc := past_coef_le (ζ := fun i => stZeta R (rawHist R i t)) hkj.le hg.le hg1 hgk.le hmono
      hdiff' hβ hcZ hcn rfl hnk (norm_nCor_le _ _) (hzne k hkj.le) hz
      (fun i hi => (hζ i (mem_Ioc.1 hi).2).trans
        (mul_le_mul_of_nonneg_left (hmon i (mem_Ioc.1 hi).2) hcZ))
      (fun i hi => (norm_stZeta_le hρ _).trans hρ8)
    rw [norm_mul]
    have h0 := norm_nonneg (hbTil R j t k)
    calc ‖stGr R k (rawHist R k t) (t k).1 (t k).2.1 ^ 2 * (stZ' R (rawHist R k t) / z) ^ 4 -
          ((t j).1 : ℂ) ^ 2‖ * ‖hbTil R j t k‖ ≤
        ((j : ℝ) - k + 1) * 2 ^ (j - k) * (24 * cZ' + 3 * cn + 2 * (2 * β + 1)) * (t j).1 ^ 3 *
          ‖hbTil R j t k‖ := mul_le_mul_of_nonneg_right hpc h0
      _ = _ := by ring

/-! ### The dressed data of a history (copies of `FlowHV`) -/

theorem stZ'_eq_dDataU {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVL : ValidAtL R j)
    (t : Hist.Seq (Xs R)) :
    stZ' R (rawHist R j t) = (dData L N R.msq (zh R j t)).Z (j + 1) := by
  have H := rawInv_histU R hV hVL t (j + 1) le_rfl
  rw [show stZ' R (rawHist R j t) = (rawHist R (j + 1) t).Z from rfl, H.hZprod]
  rfl

theorem hbTil_eqU (hP : R.P = Pc) (hi0 : R.i₀ = 0) {j : ℕ} (hV : ∀ i < j, ValidAt R i)
    (hVL : ValidAtL R j) (t : Hist.Seq (Xs R)) {k : ℕ} (hk : k < j) :
    hbTil R j t k = bTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j k := by
  unfold hbTil bTil
  rw [stZ'_eq_dDataU R hV hVL t, hi0]
  rw [FlowSeq.beta_congr (D := histFS R j t)
    (D' := gFS (dData L N R.msq (zh R j t)) (histFS R j t).κ) hk.le
    (fun i _ hij => by rw [histFS_C R t hij, stCov_eq_dData R hP t hij]) (fun i _ _ => rfl)]

theorem hqTil_eqU (hP : R.P = Pc) (hi0 : R.i₀ = 0) {j : ℕ} (hV : ∀ i < j, ValidAt R i)
    (hVL : ValidAtL R j) (t : Hist.Seq (Xs R)) :
    hqTil R j t = qTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j := by
  unfold hqTil qTil
  rw [stZ'_eq_dDataU R hV hVL t, hi0]
  have hC : (histFS R j t).C j = (gFS (dData L N R.msq (zh R j t)) (histFS R j t).κ).C j := by
    rw [histFS_C R t le_rfl, stCov_eq_dData R hP t le_rfl]
  have hB : (histFS R j t).betaQ j j 0 0 =
      (gFS (dData L N R.msq (zh R j t)) (histFS R j t).κ).betaQ j j 0 0 := by
    unfold FlowSeq.betaQ
    rw [if_pos rfl, if_pos rfl, hC]
  rw [hB]

theorem hcTil_eqU (hP : R.P = Pc) {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVL : ValidAtL R j)
    (t : Hist.Seq (Xs R)) :
    hcTil R j t = cTil (dData L N R.msq (zh R j t)) j := by
  unfold hcTil cTil
  rw [stZ'_eq_dDataU R hV hVL t, stCov_eq_dData R hP t le_rfl]
  simp only [DressedFRD.kmat, sub_zero]
  rfl

theorem f1Coef_eqU (hP : R.P = Pc) (hi0 : R.i₀ = 0) {j : ℕ} (hV : ∀ i < j, ValidAt R i)
    (hVL : ValidAtL R j) (t : Hist.Seq (Xs R)) :
    f1Coef R j t = 2 * cTil (dData L N R.msq (zh R j t)) j -
      (qTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j +
        ∑ k ∈ range j, bTil (dData L N R.msq (zh R j t)) (histFS R j t).κ j k) := by
  unfold f1Coef
  rw [hcTil_eqU R hP hV hVL t, hqTil_eqU R hP hi0 hV hVL t,
    sum_congr rfl fun k hk => hbTil_eqU R hP hi0 hV hVL t (mem_range.1 hk)]

theorem hist_dData_hypsU {j : ℕ} (hP : R.P = Pc) (hV : ∀ i < j, ValidAt R i)
    (hVL : ValidAtL R j) (t : Hist.Seq (Xs R)) :
    (∀ i, ‖zh R j t i‖ ≤ R.ρ) ∧
      ∀ i ≤ j, GoodCov2 i (ellM R j t) (DressedFRD.kmat ((dData L N R.msq (zh R j t)).Gint i)) := by
  have H := rawInv_histU R hV hVL t (j + 1) le_rfl
  refine ⟨H.hζ, fun i hi => ?_⟩
  rw [← stCov_eq_dData R hP t hi, ← histFS_C R t hi]
  exact histFS_goodU R hV hVL t i

/-- **(HV) along histories**, with `ValidAtL` at `j`. -/
theorem HV_histU : ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ E1 : ℝ, 0 ≤ E1 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, (∀ i < j, ValidAt R i) → ValidAtL R j → ∀ t : Hist.Seq (Xs R),
        |(f1Coef R j t).re - 3 * (Real.log L / (2 * Real.pi))| ≤
          E0 + E1 * (dData L N R.msq (zh R j t)).Mz (j + 1) := by
  obtain ⟨E0, hE0, h⟩ := HV
  refine ⟨E0, hE0, fun L _ hL => ?_⟩
  obtain ⟨ζbar, hζ, E1, hE1, h'⟩ := h L hL
  refine ⟨ζbar, hζ, E1, hE1, fun N R _ _ hP hi0 hN hm0 hm hρ j hV hVL t => ?_⟩
  obtain ⟨hz, hG⟩ := hist_dData_hypsU R hP hV hVL t
  rw [f1Coef_eqU R hP hi0 hV hVL t]
  exact h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hVL.2.1 (ellM R j t)
    (ellM_nonneg R t) hG (histFS R j t).κ

/-- **(HD) along histories**, with `ValidAtL` at `j`. -/
theorem HD_histU : ∀ (L : ℕ) [NeZero L], 49 ≤ L → ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ KB : ℝ, 0 ≤ KB ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, (∀ i < j, ValidAt R i) → ValidAtL R j → ∀ t : Hist.Seq (Xs R),
        ‖hqTil R j t‖ ≤ KB ∧ ∑ k ∈ range j, ((j : ℝ) - k + 1) * 2 ^ (j - k) * ‖hbTil R j t k‖ ≤ KB := by
  intro L _ hL
  obtain ⟨ζbar, hζ, KB, hKB, h'⟩ := HD L hL
  refine ⟨ζbar, hζ, KB, hKB, fun N R _ _ hP hi0 hN hm0 hm hρ j hV hVL t => ?_⟩
  obtain ⟨hz, hG⟩ := hist_dData_hypsU R hP hV hVL t
  obtain ⟨h1, h2⟩ := h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hVL.2.1
    (ellM R j t) (ellM_nonneg R t) hG (histFS R j t).κ
  refine ⟨by rw [hqTil_eqU R hP hi0 hV hVL t]; exact h1, le_trans (le_of_eq ?_) h2⟩
  refine sum_congr rfl fun k hk => ?_
  have hkj := mem_range.1 hk
  rw [hbTil_eqU R hP hi0 hV hVL t hkj,
    show ((j : ℝ) - k + 1) = ((j - k + 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hkj.le]; ring]

/-- **The sharp zero mode and first difference along histories**, with `ValidAtL` at `j`. -/
theorem S01_histU : ∃ M₀ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₂ ∧ ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, (∀ i < j, ValidAt R i) → ValidAtL R j → ∀ t : Hist.Seq (Xs R),
        ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ (M₀ + 1) * ((L : ℝ) ^ j) ^ 2 ∧
        ‖stZ' R (rawHist R j t) * (stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0 -
          stCov R j (rawHist R j t) 0 0)‖ ≤ (M₂ + 1) / ((L : ℝ) ^ j) ^ 2 := by
  obtain ⟨M₀, M₂, hM₀, hM₂, h⟩ := S0S1
  refine ⟨M₀, M₂, hM₀, hM₂, fun L _ hL => ?_⟩
  obtain ⟨ζbar, hζ, h'⟩ := h L hL
  refine ⟨ζbar, hζ, fun N R _ _ hP hN hm0 hm hρ j hV hVL t => ?_⟩
  obtain ⟨hz, -⟩ := hist_dData_hypsU R hP hV hVL t
  obtain ⟨h1, h2⟩ := h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hVL.2.1
  refine ⟨le_trans (le_of_eq ?_) h1, le_trans (le_of_eq ?_) h2⟩
  · have e : ∑ k ∈ range j, ∑ x, stCov R k (rawHist R k t) x 0 =
        ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern ((dData L N R.msq (zh R j t)).Gint k) x :=
      sum_congr rfl fun k hk => sum_congr rfl fun x _ => by
        rw [stCov_eq_dData R hP t (mem_range.1 hk).le]
        simp only [DressedFRD.kmat, sub_zero]
    rw [rawHist_w1_eq, stZ'_eq_dDataU R hV hVL t, e]
  · rw [stZ'_eq_dDataU R hV hVL t, stCov_eq_dData R hP t le_rfl]
    simp only [DressedFRD.kmat, sub_zero]
    rfl

/-- **The history tadpole is the dressed tadpole**, with `ValidAtL` at `j`. -/
theorem htad_eqU (hP : R.P = Pc) {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hVL : ValidAtL R j)
    (t : Hist.Seq (Xs R)) :
    htad R j t = tadTil (dData L N R.msq (zh R j t)) j := by
  obtain ⟨hz, -⟩ := hist_dData_hypsU R hP hV hVL t
  have hρ8 : R.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  set D := dData L N R.msq (zh R j t) with hD
  have hZ : ∀ i, D.Z i ≠ 0 :=
    DressedFRD.Data.Z_ne_zero (fun i => (hz i).trans (by linarith only [hρ8]))
  have e1 : (rawHist R j t).w1 = ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern (D.Gint k) x := by
    rw [rawHist_w1_eq]
    refine sum_congr rfl fun k hk => sum_congr rfl fun x _ => ?_
    rw [stCov_eq_dData R hP t (mem_range.1 hk).le]
    simp only [DressedFRD.kmat, sub_zero]
    rfl
  unfold htad tadTil
  rw [e1, stZ'_eq_dDataU R hV hVL t, stCov_eq_dData R hP t le_rfl, wp_eq_smul D hZ j]
  simp only [DressedFRD.kmat, sub_zero, Cp, Nat.add_sub_cancel, DressedFRD.kern_smul,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [show (∑ k ∈ range j, D.Gint k 0) = ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern (D.Gint k) x
    from sum_congr rfl fun k _ => (sum_kern_eq _).symm]
  ring

/-- **`HV_sharp` along histories**, with `ValidAtL` at `j`. -/
theorem HVs_histU : ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ E1 : ℝ, 0 ≤ E1 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, 1 ≤ j → (∀ i < j, ValidAt R i) → ValidAtL R j → ∀ t : Hist.Seq (Xs R),
        |(f1Coef R j t + htad R j t).re - 3 * (Real.log L / (2 * Real.pi))| ≤
          C0sh * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) +
            E1 * (dData L N R.msq (zh R j t)).Mz (j + 1) := by
  intro L _ hL
  obtain ⟨ζbar, hζ, E1, hE1, h'⟩ := HV_sharp L hL
  refine ⟨ζbar, hζ, E1, hE1, fun N R _ _ hP hi0 hN hm0 hm hρ j hj1 hV hVL t => ?_⟩
  obtain ⟨hz, hG⟩ := hist_dData_hypsU R hP hV hVL t
  rw [f1Coef_eqU R hP hi0 hV hVL t, htad_eqU R hP hV hVL t]
  exact h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hj1 hVL.2.1 (ellM R j t)
    (ellM_nonneg R t) hG (histFS R j t).κ

/-! ### The mass term and `Mz` -/

/-- `HS_zeta` with `ValidAt` below `j` only. -/
theorem HS_zetaU {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (t : Hist.Seq (Xs R)) {cζ mf M₀ g : ℝ} (hg : 0 ≤ g)
    (hcζ : 0 ≤ cζ) (hM₀ : 0 ≤ M₀) (hζ : ‖stZeta R (rawHist R j t)‖ ≤ cζ * g)
    (hmf : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ mf)
    (hS0 : ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ (M₀ + 1) * ((L : ℝ) ^ j) ^ 2) :
    ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤
      8 / 7 * cζ * (M₀ + 1) * mf * g := by
  have hρ1 : R.ρ < 1 := by linarith
  have HI := rawInv_hist R hρ j hV t
  set st := rawHist R j t
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ st).trans hρ8
  have h1ζ : 7 / 8 ≤ ‖1 + stZeta R st‖ := by linarith [norm_one_add_ge (ζ := stZeta R st)]
  have e : stA R st * (R.msq : ℂ) * st.w1 =
      stZeta R st / (1 + stZeta R st) * (R.msq : ℂ) * (stZ' R st * st.w1) := by
    have h1 : (1 + stZeta R st) ≠ 0 := one_add_ne_zero (by linarith)
    show st.Z * stZeta R st * (R.msq : ℂ) * st.w1 = _
    unfold stZ'; field_simp
  rw [e, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hz1 : ‖stZeta R st‖ / ‖1 + stZeta R st‖ ≤ 8 / 7 * (cζ * g) := by
    rw [div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ cζ * g := by positivity
    nlinarith
  calc ‖stZeta R st‖ / ‖1 + stZeta R st‖ * |R.msq| * ‖stZ' R st * st.w1‖
      ≤ 8 / 7 * (cζ * g) * |R.msq| * ((M₀ + 1) * ((L : ℝ) ^ j) ^ 2) := by gcongr
    _ = 8 / 7 * cζ * (M₀ + 1) * g * (|R.msq| * ((L : ℝ) ^ j) ^ 2) := by ring
    _ ≤ 8 / 7 * cζ * (M₀ + 1) * g * mf := by gcongr
    _ = _ := by ring

/-- **`Mz` at the step `j`** (the `Mz` part of `HS_of_S01`) with `ValidAt` below `j` only:
`Mz(j + 1) ≤ 2 C_z g_j` along regular histories. -/
theorem Mz_histU {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    {j : ℕ} (hV : ∀ i < j, ValidAt R i) (hm : ∀ i < j, |R.msq| * ((L : ℝ) ^ i) ^ 2 ≤ 1)
    (hρ : 0 ≤ R.ρ)
    {Λ β δ κ cg cm cT ε : ℝ} (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS) (hβ : 0 ≤ β)
    (hδ1 : δ ≤ 1 / 2) (hcgβ : cg * ε ≤ β / 2)
    (t : Hist.Seq (Xs R)) (ht : Hist.InDh Λ β δ κ cg cm cT ε j t) :
    (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cZ R * (t j).1 := by
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcg1 : cg * ε ≤ 1 := by linarith [H.h6]
  have hζ : ∀ i ≤ j, ‖stZeta R (rawHist R i t)‖ ≤ 2 * cZ R * (t j).1 := fun i hi => by
    obtain ⟨hzi, hyi, -⟩ := apriori R hSB hV hm hβ (by linarith) H i hi t
      ⟨fun i' hi' => ht.1 i' (by omega), fun i' hi' => ht.2 i' (by omega)⟩
    have hmon := (g_mono ht hβ hδ1 H.hcg hcgβ hcg1 i (j - i) (by omega)).1
    rw [show i + (j - i) = j by omega] at hmon
    unfold stZeta absorbZeta
    refine (norm_clampDisk_le_self hρ _).trans ?_
    rw [add_div]; refine (norm_add_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hmon hcz]
  have hg := (ht.1 j le_rfl).1
  refine DressedFRD.Data.Mz_le (by positivity) fun i hi => ?_
  show ‖zh R j t i‖ ≤ _
  rw [zh_eq_stZeta R t (by omega)]
  exact hζ i (by omega)

end

end Step2
