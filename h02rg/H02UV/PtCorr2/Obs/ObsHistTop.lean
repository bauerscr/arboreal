import PtCorr2.Obs.GamWKBd
import PtCorr2.Obs.ProdBd2Hist
import Obs2.Flow.RelRecTop

/-!
# The observable recursion at the top scale `j = N_h` (`ValidAtL`)

At `j = N_h` only `ValidAtL R N_h` holds (`ValidCore`, `j + 1 < N`). The lemmas of the relative
recursion used at a scale `j` need `ValidAt` at `j` only through `ValidCore R j`, `0 ≤ ρ ≤ 1/8`,
`RawInv` along the history, the a priori bounds (valid for `j ≤ N_h`) and `|m²|L^{2j} ≤ 1`.
Copies at `j = N_h`:

* `hist_validL` (`ValidCore ∧ RawInv` for all `i ≤ N_h`);
* `kobs_EK2L`, `kobs_EK2_epsL` (the activity terms in `ℓ¹`), `goodCov2_histSL`,
  **`gamWK2_leL`** (the `K`/`𝒲` part of `ρ_{N_h}` from the block bounds at `N_h`);
* **`obs_hist_rel2_top`**: the hypotheses of `obs_hist_rel2_base` at horizon `n = N_h`, plus at
  the index `N_h` the tadpole decay `|tadInc2 k N_h|`, `|𝔫^{(2)}_{N_h}| ≤ 1/7`, `ProdBd2` up to
  `N_h + 1`, `|m²|L^{2N_h} ≤ 1`, `ValidAtL R N_h`: the error of the step `N_h` satisfies
  `‖∑_{B_+}err_{N_h}‖ ≤ c_δr_{N_h}²‖β_{N_h}(1 − 𝔫^{(2)}_{N_h})‖` (`RelRec.E_top`); the block
  bounds at `N_h` (`RelRec.close`) are exported as well.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Top

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- `ValidCore ∧ RawInv` for all `i ≤ N_h`. -/
theorem hist_validL (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (t : Flow2.Hist.Seq (Xs R)) : ∀ i ≤ Nh, ValidCore R i ∧ RawInv R i (rawHist R i t) := by
  intro i hi
  rcases Nat.lt_or_ge i Nh with h | h
  · exact hist_valid R hV t (n := Nh) le_rfl i h
  · obtain rfl : i = Nh := by omega
    exact ⟨hVL.2, rawInv_hist R hVL.2.2.2.2.1 i hV t⟩

set_option maxHeartbeats 2000000 in
/-- `kobs_EK2` at `j = N_h`. -/
theorem kobs_EK2L (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (w : Wt) (hw0 : w.ab = 0) (wa : ℝ) (hwa0 : 0 < wa) (hwa : w.a = ENNReal.ofReal wa)
    (k : ℝ) (hk0 : 0 ≤ k)
    (hKo : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
        oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).K X) ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) Nh,
        ‖mass2 (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) * (histS R Nh t)⁻¹ ^ 2 := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hVL.2
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 Nh hV t
  have hZ : (rawHist R Nh t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 Nh le_rfl
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hη : 2 * (cZ R * (t Nh).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t Nh).1) ≤ 1 / 2 := by
    have := H.h2
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hΔ := (rg_inputs R Nh hVj _ HI (t Nh).1 (t Nh).2.1 hmN hg.le _ hz hy hη).2
  have hs : 0 < histS R Nh t := mul_pos (fscale_pos hZ) hℓ
  have hval := hist_validL R hV hVL t
  have hA : 0 < R.A := Fact.out
  refine histKO2_hK1 R P o₀ t Nh hl0 hval hs hwa0
    (by positivity : (0 : ℝ) ≤ 8 * k) (fun X hX => ?_)
  have hXc : IsConn Nh X := ⟨hX.1, hX.2.1⟩
  have hnb : nb Nh X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R Nh (rawHist R Nh t) (rawK R (rawHist R Nh t).u (t Nh).2.2)
    (obsHist R P o₀ Nh t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) Nh (histS R Nh t)
        (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a
      ≤ oTo w Nh (histS R Nh t) (histKO2 R P o₀ t Nh X) := wa_Tj_a_le_oTo w hwa Nh _ _
    _ ≤ ENNReal.ofReal 8 * oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

set_option maxHeartbeats 2000000 in
/-- `kobs_EK2_eps` at `j = N_h`. -/
theorem kobs_EK2_epsL (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (w : Wt) (hw0 : w.ab = 0) (wa : ℝ) (hwa0 : 0 < wa) (hwa : w.a = ENNReal.ofReal wa)
    (k : ℝ) (hk0 : 0 ≤ k)
    (hKo : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
        oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).K X) ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) Nh,
        ‖Grassmann.ε (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hVL.2
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 Nh hV t
  have hZ : (rawHist R Nh t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 Nh le_rfl
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hη : 2 * (cZ R * (t Nh).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t Nh).1) ≤ 1 / 2 := by
    have := H.h2
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hΔ := (rg_inputs R Nh hVj _ HI (t Nh).1 (t Nh).2.1 hmN hg.le _ hz hy hη).2
  have hs : 0 < histS R Nh t := mul_pos (fscale_pos hZ) hℓ
  have hval := hist_validL R hV hVL t
  have hA : 0 < R.A := Fact.out
  refine histKO2_hK1_eps R P o₀ t Nh hl0 hval hs hwa0
    (by positivity : (0 : ℝ) ≤ 8 * k) (fun X hX => ?_)
  have hXc : IsConn Nh X := ⟨hX.1, hX.2.1⟩
  have hnb : nb Nh X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R Nh (rawHist R Nh t) (rawK R (rawHist R Nh t).u (t Nh).2.2)
    (obsHist R P o₀ Nh t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) Nh (histS R Nh t)
        (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a
      ≤ oTo w Nh (histS R Nh t) (histKO2 R P o₀ t Nh X) := wa_Tj_a_le_oTo w hwa Nh _ _
    _ ≤ ENNReal.ofReal 8 * oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

/-- `goodCov2_histS` at `k = N_h`. -/
theorem goodCov2_histSL (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t) :
    GoodCov2 Nh (histS R Nh t) (histCovO R t Nh) := by
  have hVc := hVL.2
  have HI := rawInv_hist R hVc.2.2.2.1 Nh hV t
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 Nh le_rfl
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hηρ : 2 * (cZ R * (t Nh).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  set st := rawHist R Nh t with hst
  have hVc' := hVc
  obtain ⟨-, -, -, -, hρ8, hℓ, -⟩ := hVc'
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero (by linarith)
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by
    rw [hζ, add_div]
    exact (norm_add_le _ _).trans (by linarith)
  have hs := fscale_pos hZ
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hs' : 0 < fscale (stZ' R st) := fscale_pos hZ'
  have hsc : fscale (stZ' R st) * R.ℓ + fscale (stZ' R st) * R.ℓ / 4 ≤
      3 / 2 * (fscale st.Z * R.ℓ) := scale_ok hZ hζ8 hℓ
  have hCℓ : fscale (stZ' R st) * R.ℓ / 4 ≤ fscale st.Z * R.ℓ := by
    have : 0 < fscale (stZ' R st) * R.ℓ := mul_pos hs' hℓ
    have : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
    linarith
  obtain ⟨hC0, -, -, -⟩ := HI.covL hVc
  have hC : GoodCov2 Nh (fscale (stZ' R st) * R.ℓ / 4) (stCov R Nh st) := hC0
  exact hC.mono hCℓ

set_option maxHeartbeats 4000000 in
/-- **`gamWK2_le` at `k = N_h`**. -/
theorem gamWK2_leL (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hLp : pauliL0 2 ≤ L) (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (hkN : Nh + 1 < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    {w kk : ℝ} (hw : 0 ≤ w) (hkk : 0 ≤ kk) (hW : WbHc R P o₀ t Nh w) (hK : KbHc R P o₀ t Nh kk) :
    ‖gamWK2 R P o₀ t Nh‖ ≤ csN 2 * (8 * kk) +
      ‖histCovO R t Nh P.a P.a‖ * (csN 2 * (8 * kk) * (histS R Nh t)⁻¹ ^ 2) +
      (cBn : ℝ) * (Q1 2 * w) := by
  classical
  have hℓ : 0 < R.ℓ := Fact.out
  have hVk := hVL.2
  have hρ1 : R.ρ < 1 := by linarith [hVk.2.2.2.2.1]
  have HI := rawInv_hist R hVk.2.2.2.1 Nh hV t
  have hZ : (rawHist R Nh t).Z ≠ 0 := HI.Z_ne_zero hρ1
  have hs : 0 < histS R Nh t := mul_pos (fscale_pos hZ) hℓ
  have hC := goodCov2_histSL R hSB hV hm hVL hβ hδ1 H t ht
  have hval := hist_validL R hV hVL t
  have ho := obsLocInv_hist R P o₀ hl0 t Nh fun i hi => hval i hi.le
  have hwa : Obs2.wA.a = ENNReal.ofReal 1 := by simp [Obs2.wA]
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  have hKe := kobs_EK2_epsL R hSB hV hm hVL hmN hβ hδ1 H P o₀ hl0 t ht Obs2.wA hw0 1 one_pos hwa
    kk hkk hK
  have hKm := kobs_EK2L R hSB hV hm hVL hmN hβ hδ1 H P o₀ hl0 t ht Obs2.wA hw0 1 one_pos hwa
    kk hkk hK
  rw [div_one] at hKe hKm
  unfold gamWK2
  rw [sum_eps_expLC_Q2O P Nh _ _ hkN]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    have e : ∀ X ∈ smallSets (L := L) (N := N) Nh,
        ‖Grassmann.ε (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a + histCovO R t Nh P.a P.a *
          mass2 (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a‖ ≤
        ‖Grassmann.ε (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a‖ +
          ‖histCovO R t Nh P.a P.a‖ *
          ‖mass2 (histKO2 R P o₀ t Nh X : SA .two (Lam 2 L N)).a‖ := fun X _ =>
      (norm_add_le _ _).trans (by rw [norm_mul])
    refine (sum_le_sum e).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    exact add_le_add hKe (mul_le_mul_of_nonneg_left hKm (norm_nonneg _))
  · have e : ∀ b, Grassmann.ε (EthO (histCovO R t Nh) (histWO2 R P o₀ t Nh b) :
        SA .two (Lam 2 L N)).a =
        Grassmann.ε (expLC (histCovO R t Nh)
          ((obsHist R P o₀ Nh t).W b : SA .two (Lam 2 L N)).a) := by
      intro b; rw [EthO_a_eq, histWO2_a]
    simp only [e]
    refine (norm_sum_le _ _).trans ?_
    set S := blockIdx (L := L) (N := N) Nh
    set S' := S.filter (fun b => P.a ∈ nbhd Nh (blockSet (L := L) (N := N) Nh b))
    have hsplit : ∑ b ∈ S, ‖Grassmann.ε (expLC (histCovO R t Nh)
        ((obsHist R P o₀ Nh t).W b : SA .two (Lam 2 L N)).a)‖ =
        ∑ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t Nh)
          ((obsHist R P o₀ Nh t).W b : SA .two (Lam 2 L N)).a)‖ := by
      refine (sum_subset (filter_subset _ _) fun b hb hb' => ?_).symm
      have hna : P.a ∉ nbhd Nh (blockSet (L := L) (N := N) Nh b) := fun h =>
        hb' (mem_filter.2 ⟨hb, h⟩)
      rw [((ho.W b).2.2.2.2.1 hna).1, map_zero, map_zero, norm_zero]
    rw [hsplit]
    have hterm : ∀ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t Nh)
        ((obsHist R P o₀ Nh t).W b : SA .two (Lam 2 L N)).a)‖ ≤ Q1 2 * w := by
      intro b hb
      have hbS := (mem_filter.1 hb).1
      refine (norm_eps_expLC_le (by norm_num) hLp (by omega) hs hC (ho.W b).2.1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by have := one_le_Q1 (d := 2) (by norm_num); linarith)
      have h := hW b hbS
      rw [Obs2.oTo_wA] at h
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal hw] at h2
    have hc : (S'.card : ℝ) ≤ cBn := by
      exact_mod_cast Classical.choose_spec (Obs2.card_blocks_near 2) L N Nh P.a S subset_rfl
    calc ∑ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t Nh)
          ((obsHist R P o₀ Nh t).W b : SA .two (Lam 2 L N)).a)‖
        ≤ ∑ _b ∈ S', Q1 2 * w := sum_le_sum hterm
      _ = S'.card * (Q1 2 * w) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ cBn * (Q1 2 * w) := mul_le_mul_of_nonneg_right hc (mul_nonneg (by
          have := one_le_Q1 (d := 2) (by norm_num); linarith) hw)

set_option maxHeartbeats 8000000 in
/-- **The step `N_h` of the relative recursion** (Case (2), `γ_a = 0`): the block bounds of
`obs_hist_rel2_base` at horizon `N_h` and `‖∑_{B_+}err_{N_h}‖ ≤ c_δr_{N_h}²‖β_{N_h}(1 − 𝔫^{(2)}_{N_h})‖`. -/
theorem obs_hist_rel2_top {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (hmu : OCoup2.mua V ≠ 0)
    (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (hn : n ≤ Nh) (hnN : n < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (hβp : 0 < β) (hδ2 : δ ≤ 1 / 2) (hcgε : cg * ε ≤ β / 4)
    {cgb cP cδ Bτ qq : ℝ} (hcg : 0 ≤ cgb) (hcP : 0 ≤ cP) (hcδ0 : 0 ≤ cδ) (hBτ : 0 ≤ Bτ)
    (hqq0 : 0 ≤ qq) (hqq4 : qq ≤ 1 / 4)
    (hcg1 : 1 ≤ cgb * cR R Λ cm C₂) (hcgε' : cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 7)
    (hcδ : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁ + 1) * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) +
        3 * cP * (3 * C₁ + 1) + 4 * Bτ * cgb * (1 + cgb) +
        4 * Bτ * cgb * cδ * (cR R Λ cm C₂ * ε) ≤ 6 / 7 * cδ)
    (hsumε : cδ * (cR R Λ cm C₂ ^ 2 * (ε / (β / 4))) ≤ 1 / 8)
    (hT : ∀ k j, k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) k j‖ ≤
        Bτ * qq ^ (j - k) * (t k).1)
    (hnn : ∀ i < n, ‖frakN2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) i‖ ≤
      cgb * (cR R Λ cm C₂ * (t i).1))
    (hnh : n = Nh) (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hN1 : Nh + 1 < N)
    (hTN : ∀ k < Nh,
      ‖tadInc2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) k Nh‖ ≤
        Bτ * qq ^ (Nh - k) * (t k).1)
    (hnN7 : ‖frakN2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) Nh‖ ≤ 1 / 7)
    (hPrN : ProdBd2 R P (obsInit .two V P) t (Nh + 1) (fun j => cR R Λ cm C₂ * (t j).1) cP qq) :

    (∀ j ≤ n, 0 < ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖ ∧
      WbHc R P (obsInit .two V P) t j ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t j).1) *
        (2 * histS R j t ^ 2 *
          ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖)) ∧
      KbHc R P (obsInit .two V P) t j (16 * (3 * C₁ + 1) * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) *
        (cR R Λ cm C₂ * (t j).1) ^ 2 * (histS R j t ^ 2 *
          ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖))) ∧
    ‖∑ c' ∈ blockIdx (L := L) (N := N) (Nh + 1),
        shareErr2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t)
          (histWO2 R P (obsInit .two V P) t) (histKO2 R P (obsInit .two V P) t) Nh
          (blockSet (L := L) (N := N) (Nh + 1) c')‖ ≤
      cδ * (cR R Λ cm C₂ * (t Nh).1) ^ 2 *
        ‖betaTot2 (L := L) (N := N) Nh (histVO2 R P (obsInit .two V P) t Nh) *
          (1 - frakN2 P (histCovO R t) (histVO2 R P (obsInit .two V P) t) Nh)‖ := by
  subst hnh
  set o₀ := obsInit .two V P with ho₀
  set B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
  set rr : ℕ → ℝ := fun j => cR R Λ cm C₂ * (t j).1 with hrr
  set cWo := 3 * C₁ + 1
  have h0 : o₀.IsObs := obsInit_isObs .two V P
  have hl0 : ObsLocInv P 0 o₀ := obsLocInv_init .two V P
  have hs0 : ObsSymInv 0 o₀ := obsSymInv_init .two V P
  have HC := muChain2_obsHist R P o₀ t hnN (fun b => obsInit_two_W P V b)
    (fun b => obsInit_two_form P V b)
  have hβ' : 0 < β / 4 := by linarith
  -- the band along the history
  have hcg0 : 0 ≤ cg := H.hcg
  have hinc : ∀ k < n, (t k).1 + β / 4 * (t k).1 ^ 2 ≤ (t (k + 1)).1 := by
    intro k hk
    have hr := ht.2 k hk
    obtain ⟨hg, hgε, -, -⟩ := ht.1 k hk.le
    have h3 : cg * (t k).1 ^ 3 ≤ β / 4 * (t k).1 ^ 2 := by
      have : cg * (t k).1 ≤ cg * ε := mul_le_mul_of_nonneg_left hgε hcg0
      have e : cg * (t k).1 ^ 3 = (cg * (t k).1) * (t k).1 ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right (this.trans hcgε) (sq_nonneg _)
    have hδβ : δ * β * (t k).1 ^ 2 ≤ 1 / 2 * β * (t k).1 ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ2 hβ) (sq_nonneg _)
    rw [abs_le] at hr
    linarith [hr.1]
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  have hwa : Obs2.wA.a ≠ ⊤ := by simp [Obs2.wA]
  have hwb : Obs2.wA.b ≠ ⊤ := by simp [Obs2.wA]
  have hcx := H.hcx
  have hcb : 0 ≤ 8 * cx κ cT := by positivity
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L R.A C₀ η * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hC1 : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) := by positivity
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hr0 : ∀ j ≤ n, 0 ≤ rr j := fun j hj => mul_nonneg hcR (ht.1 j hj).1.le
  have hrε : ∀ j ≤ n, rr j ≤ cR R Λ cm C₂ * ε := fun j hj =>
    mul_le_mul_of_nonneg_left (ht.1 j hj).2.1 hcR
  -- positivity of the field scales
  have hsj : ∀ j ≤ n, 0 < histS R j t := fun j _ => histS_pos' R hρ0 hρ t j
  -- the block bound of `V^{obs}_j` from the `ℓ¹` size
  have hVo : ∀ j ≤ n, ∀ m, histS R j t ^ 2 * shA2 (histVO2 R P o₀ t) j ≤ m →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m := by
    intro j hj m hsm b hb'
    have hs := hsj j hj
    rw [Obs2.oTo_wA, obsHist2_pure R P t V hga j b]
    refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hsm))
    have h1 : ‖mass2 ((obsHist R P o₀ j t).V b : SA .two (Lam 2 L N)).a‖ ≤
        shA2 (histVO2 R P o₀ t) j := by
      rw [← histVO2_a R P o₀ t j b]
      exact single_le_sum (f := fun b => ‖mass2
        (histVO2 R P o₀ t j b : SA .two (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hgm : ∀ k < n, (t k).1 ≤ (t (k + 1)).1 := fun k hk => by
    have := hinc k hk; have : 0 ≤ β / 4 * (t k).1 ^ 2 := by positivity
    linarith
  have hgmono : ∀ k i, k ≤ i → i ≤ n → (t k).1 ≤ (t i).1 := by
    intro k i hki hin
    induction i, hki using Nat.le_induction with
    | base => exact le_rfl
    | succ i hki ih => exact (ih (by omega)).trans (hgm i (by omega))
  let Tt : ℕ → ℕ → ℝ := fun k j => Bτ * qq ^ (j - k)
  let G : ℕ → ℝ := fun i => (t i).1
  have hG : ∀ i < n, 0 ≤ G i := fun i hi => (ht.1 i hi.le).1.le
  have hTt : ∀ k j, k < j → j < n → ∀ i ∈ Ico k j,
      ‖tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k j‖ ≤ Tt k j * G i := by
    intro k j hkj hj i hi
    have hi' := mem_Ico.1 hi
    refine (hT k j hkj hj).trans (mul_le_mul_of_nonneg_left (hgmono k i hi'.1 (by omega))
      (mul_nonneg hBτ (pow_nonneg hqq0 _)))
  have I : RelIn n (fun j => ‖betaTot2 (L := L) (N := N) j (histVO2 R P o₀ t j)‖)
      (shA2 (histVO2 R P o₀ t)) (fun j => shareDev2 P.a j (histVO2 R P o₀ t j))
      (fun j => shareErrL1_2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t)
        (histKO2 R P o₀ t) j)
      (fun j => ‖1 - frakN2 P (histCovO R t) (histVO2 R P o₀ t) j‖)
      (fun j => histS R j t ^ 2) rr
      (shKt2 (histKO2 R P o₀ t))
      (shPr2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t))
      (fun _ => 0) G (fun i => ‖frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖)
      (fun j => Kw / L + C₁ * rr j)
      (fun j => kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * rr j)
      Tt (WbHc R P o₀ t) (KbHc R P o₀ t)
      C₁ cWo B (8 * (csN 2 : ℝ)) cP cgb Bτ qq (cR R Λ cm C₂ * ε) cδ := {
    hC₁ := hC₁
    hcW1 := by show (1 : ℝ) ≤ 3 * C₁ + 1; linarith
    hcWC := by show 3 * C₁ ≤ 3 * C₁ + 1; linarith
    hBk := hB
    hcK := by positivity
    hcP := hcP
    hcg := hcg
    hBτ := hBτ
    hq0 := hqq0
    hq := hqq4
    hcδ0 := hcδ0
    hcδ := hcδ
    hsum := by
      have h1 := Step2.sum_sq_le hβ' n hinc
      have h2 : ∑ k ∈ range n, rr k ^ 2 = cR R Λ cm C₂ ^ 2 * ∑ k ∈ range n, (t k).1 ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by rw [hrr]; ring
      have h3 : ((t n).1 - (t 0).1) / (β / 4) ≤ ε / (β / 4) := by
        have := (ht.1 n le_rfl).2.1; have := (ht.1 0 (Nat.zero_le _)).1
        exact div_le_div_of_nonneg_right (by linarith) hβ'.le
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg (cR R Λ cm C₂))
      have h5 := mul_le_mul_of_nonneg_left h4 hcδ0
      linarith
    hr0 := hr0
    hrb := hrε
    hrm := fun j hj => mul_le_mul_of_nonneg_left (hgm j hj) hcR
    hs := fun j hj => pow_pos (hsj j hj) 2
    hss := by
      intro j hj
      have e : histS R (j + 1) t = histS R j t * fscale (1 + zetaH R j t) := by
        unfold histS
        rw [rawHist_succ_Z, fscale_mul]; ring
      have hz : ‖zetaH R j t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
      have h1 := fscale_one_add_ge hz
      have h2 := hsj j hj.le
      have h3 : histS R j t ≤ 15 / 14 * histS R (j + 1) t := by rw [e]; nlinarith
      have h4 : 0 ≤ histS R (j + 1) t := by rw [e]; nlinarith
      show histS R j t ^ 2 ≤ 6 / 5 * histS R (j + 1) t ^ 2
      nlinarith
    ha := by
      intro j hj
      have h1 := (hnn j hj).trans ((mul_le_mul_of_nonneg_left (hrε j hj.le) hcg).trans hcgε')
      have h2 := norm_sub_norm_le (1 : ℂ) (frakN2 P (histCovO R t) (histVO2 R P o₀ t) j)
      have h3 := norm_sub_le (1 : ℂ) (frakN2 P (histCovO R t) (histVO2 R P o₀ t) j)
      rw [norm_one] at h2 h3
      constructor <;> linarith
    hb0 := by
      show 0 < ‖betaTot2 (L := L) (N := N) 0 (histVO2 R P o₀ t 0)‖
      rw [betaTot2_obsInit]; exact norm_pos_iff.2 (neg_ne_zero.2 hmu)
    hD0 := shareDev2_obsInit R P t V
    hWm := fun j x y hx hxy b hb' => (hx b hb').trans (ENNReal.ofReal_le_ofReal hxy)
    hKm := fun j x y hx hxy X hX => (hx X hX).trans (ENNReal.ofReal_le_ofReal hxy)
    hW0 := fun b _ => by
      show oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) ≤ _
      have : o₀.W b = 0 := rfl
      rw [this, oTo_zero']; exact zero_le
    hK0 := fun X _ => by
      show _ * oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) ≤ _
      have : o₀.K X = 0 := rfl
      rw [this, oTo_zero', mul_zero]; exact zero_le
    hθW := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC₁
      show Kw / L + C₁ * rr j ≤ 1 / 6
      linarith
    hθK := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC1
      show kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * rr j ≤ 1 / 16
      linarith
    hW := fun j hj m w hm0 hw0' hsA hWj =>
      wobs_hist_step R hWB hSB hV hm hβ hδ1 H P Obs2.wA hw0 o₀ h0 hl0 hs0 t j (by omega)
        (hDh j hj.le) hε₁ m w hm0 hw0' (hVo j hj.le m hsA) hWj
    hK := fun j hj m k hm0 hk0 hsA hWj hKj hk8 =>
      kobs_hist_step R hKB hSB hV hm hβ hδ1 H P Obs2.wA hw0 hwa hwb o₀ h0 hl0 hs0 t j (by omega)
        (hDh j hj.le) (64 * B) m k (by positivity) hm0 hk0 hε1 hεε hεk hk8
        (hVo j hj.le m hsA) hWj hKj
    hKt := fun j hj k hk0 hKj => by
      have h := kobs_EK2 R hSB hV hm hβ hδ1 H P o₀ hl0 t j (by omega) (hDh j hj.le) Obs2.wA hw0
        1 one_pos (by simp [Obs2.wA]) k hk0 hKj
      refine h.trans (le_of_eq ?_)
      rw [div_one, inv_pow]; ring
    hPr := fun j hj => hPrN j (by omega)
    hT := fun k j _ _ => ⟨mul_nonneg hBτ (pow_nonneg hqq0 _), le_rfl⟩
    hdg := fun i _ => ⟨le_rfl, mul_nonneg hcg (sq_nonneg _)⟩
    hG := fun i hi => ⟨hG i hi, by
      show (t i).1 ≤ cgb * (cR R Λ cm C₂ * (t i).1)
      rw [← mul_assoc]
      have := (ht.1 i hi.le).1.le
      nlinarith⟩
    hnn := fun i hi => ⟨norm_nonneg _, hnn i hi⟩ }
  have RR := HC.relRec2 Tt hG hTt I
  refine ⟨fun j hj => ?_, ?_⟩
  · obtain ⟨hb, -, hW, hK⟩ := (RR.close n le_rfl).1 j hj
    exact ⟨hb, hW, hK⟩
  -- the step `n = N_h`
  have HC' := muChain2_obsHist R P o₀ t (n := n + 1) hN1 (fun b => obsInit_two_W P V b)
    (fun b => obsInit_two_form P V b)
  have hEn : shareErrL1_2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t)
      (histKO2 R P o₀ t) n ≤
      shKt2 (histKO2 R P o₀ t) n + ∑ k ∈ range n, Tt k n *
        ∑ i ∈ Ico k n, ((fun _ => (0 : ℝ)) i * shA2 (histVO2 R P o₀ t) (i + 1) + G i *
          ((fun i => ‖frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖) i *
              shA2 (histVO2 R P o₀ t) i +
            shareErrL1_2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t)
              (histKO2 R P o₀ t) i)) +
      shPr2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) n := by
    refine (HC'.hE2_raw (Nat.lt_succ_self n)).trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
    refine sum_le_sum fun k hk => ?_
    have hkj := mem_range.1 hk
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_Ico.1 hi
    have hGi := hG i (by omega)
    have hT : ‖tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k n‖ ≤ Tt k n * G i :=
      (hTN k hkj).trans (mul_le_mul_of_nonneg_left (hgmono k i hi'.1 (by omega))
        (mul_nonneg hBτ (pow_nonneg hqq0 _)))
    set x := ‖frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖ * shA2 (histVO2 R P o₀ t) i +
      shareErrL1_2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) (histKO2 R P o₀ t) i
    have hx0 : 0 ≤ x := by
      have h2 : 0 ≤ shA2 (histVO2 R P o₀ t) i := sum_nonneg fun _ _ => norm_nonneg _
      have h3 : 0 ≤ shareErrL1_2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t)
          (histKO2 R P o₀ t) i := sum_nonneg fun _ _ => norm_nonneg _
      have := norm_nonneg (frakN2 P (histCovO R t) (histVO2 R P o₀ t) i)
      positivity
    have e : (0 : ℝ) * shA2 (histVO2 R P o₀ t) (i + 1) + G i * x = G i * x := by ring
    show _ ≤ Tt k n * ((0 : ℝ) * shA2 (histVO2 R P o₀ t) (i + 1) + G i * x)
    rw [e]
    calc ‖tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k n‖ * x ≤ (Tt k n * G i) * x :=
          mul_le_mul_of_nonneg_right hT hx0
      _ = Tt k n * (G i * x) := by ring
  have han : 6 / 7 ≤ ‖1 - frakN2 P (histCovO R t) (histVO2 R P o₀ t) n‖ := by
    have h2 := norm_sub_norm_le (1 : ℂ) (frakN2 P (histCovO R t) (histVO2 R P o₀ t) n)
    rw [norm_one] at h2
    linarith
  have hKtn : ∀ k, 0 ≤ k → KbHc R P o₀ t n k →
      shKt2 (histKO2 R P o₀ t) n ≤ 8 * (csN 2 : ℝ) * k / histS R n t ^ 2 := by
    intro k hk0 hKj
    have h := kobs_EK2L R hSB hV hm hVL hmN hβ hδ1 H P o₀ hl0 t ht Obs2.wA hw0
      1 one_pos (by simp [Obs2.wA]) k hk0 hKj
    refine h.trans (le_of_eq ?_)
    rw [div_one, inv_pow]; ring
  have hE := RR.E_top (fun k _ => ⟨mul_nonneg hBτ (pow_nonneg hqq0 _), le_rfl⟩) hEn han hKtn
    (fun mm hmm => hPrN n (Nat.lt_succ_self n) mm hmm)
  refine (norm_sum_le _ _).trans (hE.trans (le_of_eq ?_))
  rw [norm_mul]; ring


end Top

end

end PtCorr2
