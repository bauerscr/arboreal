import PtCorr2.Restart.RestartPairGam
import PtCorr2.Obs.GamWKBd
import PtCorr2.Obs.ObsHistTop

/-!
# T5: the `K`/`𝒲` part of the restarted `γ`-flow, steps `m ≤ k ≤ N_h`

Copies of `histKO2_hK1_eps`, `kobs_EK2_eps`, `gamWK2_le` along `obsHistFrom R P m δ`, for every
`m ≤ k ≤ N_h` (`ValidAt` below `N_h`, `ValidAtL` at `N_h`, `goodCov2_histSL` at the top):

* **`rpg_gamWKF_le`**: with the block bounds `WbHF k w`, `KbHF k κ` of the restarted flow,
  `|gamWKF_k| ≤ c_N·8κ + |C_k(a,a)|c_N·8κ s_k^{-2} + c_BQ₁w`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Bd

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

theorem rpg_KF_eps (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))
    (j : ℕ) (hmj : m ≤ j) (hl0 : ObsLocInv P m o')
    (h : ∀ i ≤ j, ValidCore R i ∧ RawInv R i (rawHist R i t))
    {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa) (hk : 0 ≤ k)
    (hK : ∀ X, IsSmall j X → ENNReal.ofReal wa *
      Tj 2 (L : ℝ) j ℓ (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
      ‖Grassmann.ε (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a‖ ≤ csN 2 * (k / wa) := by
  have ho := obsLocInv_histFrom' R P hl0 t hmj fun i _ hi => h i hi.le
  have HL := olocS_full R P (t j).1 (t j).2.1 (st := rawHist R j t)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2)
    (h j le_rfl).1 (h j le_rfl).2 (rawD_mem R _ _) (rawK_mem R _ _) ho
  refine sum_norm_eps_le_K P.a (histKF2 R P m o' t j) hℓ hwa hk (fun X hX ha => ?_) hK
  exact ((HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.2.1 ha).1

set_option maxHeartbeats 2000000 in
/-- **The `ε`-activity term along the restarted history**, `m ≤ j ≤ N_h`. -/
theorem rpg_EK_eps (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N) (hl0 : ObsLocInv P m o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : m ≤ j) (hj : j ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (w : Wt) (hw0 : w.ab = 0) (wa : ℝ) (hwa0 : 0 < wa) (hwa : w.a = ENNReal.ofReal wa)
    (k : ℝ) (hk0 : 0 ≤ k)
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHistFrom R P m o' j t).K X) ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
        ‖Grassmann.ε (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have hval := hist_validL R hV hVL t
  have HI := (hval j hj).2
  have hZ : (rawHist R j t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H j hj t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 j le_rfl
  have hmj' : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact hm j h
    · obtain rfl : j = Nh := by omega
      exact hmNh
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hη : 2 * (cZ R * (t j).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t j).1) ≤ 1 / 2 := by
    have := H.h2
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hΔ := (rg_inputs R j (hval j hj).1 _ HI (t j).1 (t j).2.1 hmj' hg.le _ hz hy hη).2
  have hs : 0 < histS R j t := mul_pos (fscale_pos hZ) hℓ
  have hA : 0 < R.A := Fact.out
  refine rpg_KF_eps R P o' t j hmj hl0 (fun i hi => hval i (by omega)) hs hwa0
    (by positivity : (0 : ℝ) ≤ 8 * k) (fun X hX => ?_)
  have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hnb : nb j X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2)
    (obsHistFrom R P m o' j t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) j (histS R j t)
        (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a
      ≤ oTo w j (histS R j t) (histKF2 R P m o' t j X) := wa_Tj_a_le_oTo w hwa j _ _
    _ ≤ ENNReal.ofReal 8 * oTo w j (histS R j t) ((obsHistFrom R P m o' j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

set_option maxHeartbeats 2000000 in
/-- The `m₂`-activity term along the restarted history, `m ≤ j ≤ N_h` (`kobs_EK2F` at the top
included). -/
theorem rpg_EK_m2 (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N) (hl0 : ObsLocInv P m o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : m ≤ j) (hj : j ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (w : Wt) (hw0 : w.ab = 0) (wa : ℝ) (hwa0 : 0 < wa) (hwa : w.a = ENNReal.ofReal wa)
    (k : ℝ) (hk0 : 0 ≤ k)
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHistFrom R P m o' j t).K X) ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
        ‖mass2 (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) * (histS R j t)⁻¹ ^ 2 := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have hval := hist_validL R hV hVL t
  have HI := (hval j hj).2
  have hZ : (rawHist R j t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H j hj t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 j le_rfl
  have hmj' : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact hm j h
    · obtain rfl : j = Nh := by omega
      exact hmNh
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hη : 2 * (cZ R * (t j).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t j).1) ≤ 1 / 2 := by
    have := H.h2
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hΔ := (rg_inputs R j (hval j hj).1 _ HI (t j).1 (t j).2.1 hmj' hg.le _ hz hy hη).2
  have hs : 0 < histS R j t := mul_pos (fscale_pos hZ) hℓ
  have hA : 0 < R.A := Fact.out
  refine histKF2_hK1 R P o' t j hmj hl0 (fun i hi => hval i (by omega)) hs hwa0
    (by positivity : (0 : ℝ) ≤ 8 * k) (fun X hX => ?_)
  have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hnb : nb j X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2)
    (obsHistFrom R P m o' j t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) j (histS R j t)
        (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a
      ≤ oTo w j (histS R j t) (histKF2 R P m o' t j X) := wa_Tj_a_le_oTo w hwa j _ _
    _ ≤ ENNReal.ofReal 8 * oTo w j (histS R j t) ((obsHistFrom R P m o' j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

set_option maxHeartbeats 4000000 in
/-- **The `K`/`𝒲` part of the restarted `γ`-remainder from the block bounds**, `m ≤ k ≤ N_h`. -/
theorem rpg_gamWKF_le (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hLp : pauliL0 2 ≤ L) (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N)
    (hl0 : ObsLocInv P m o')
    (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) (hmk : m ≤ k) (hk : k ≤ Nh) (hkN : k + 1 < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t)
    {w kk : ℝ} (hw : 0 ≤ w) (hkk : 0 ≤ kk) (hW : WbHF R P m o' t k w) (hK : KbHF R P m o' t k kk) :
    ‖gamWKF R P m o' t k‖ ≤ csN 2 * (8 * kk) +
      ‖histCovO R t k P.a P.a‖ * (csN 2 * (8 * kk) * (histS R k t)⁻¹ ^ 2) +
      (cBn : ℝ) * (Q1 2 * w) := by
  classical
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have hval := hist_validL R hV hVL t
  have HI := (hval k hk).2
  have hZ : (rawHist R k t).Z ≠ 0 := HI.Z_ne_zero hρ1
  have hs : 0 < histS R k t := mul_pos (fscale_pos hZ) hℓ
  have hC : GoodCov2 k (histS R k t) (histCovO R t k) := by
    rcases Nat.lt_or_ge k Nh with h | h
    · exact goodCov2_histS R hSB hV hm hβ hδ1 H t k h ht
    · obtain rfl : k = Nh := by omega
      exact goodCov2_histSL R hSB hV hm hVL hβ hδ1 H t ht
  have ho := obsLocInv_histFrom' R P hl0 t hmk fun i _ hi => hval i (by omega)
  have hwa : Obs2.wA.a = ENNReal.ofReal 1 := by simp [Obs2.wA]
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  have hKe := rpg_EK_eps R hSB hV hVL hm hmNh hβ hδ1 H P o' hl0 t k hmk hk ht Obs2.wA hw0 1
    one_pos hwa kk hkk hK
  have hKm := rpg_EK_m2 R hSB hV hVL hm hmNh hβ hδ1 H P o' hl0 t k hmk hk ht Obs2.wA hw0 1
    one_pos hwa kk hkk hK
  rw [div_one] at hKe hKm
  unfold gamWKF
  rw [sum_eps_expLC_Q2O P k _ _ hkN]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    have e : ∀ X ∈ smallSets (L := L) (N := N) k,
        ‖Grassmann.ε (histKF2 R P m o' t k X : SA .two (Lam 2 L N)).a + histCovO R t k P.a P.a *
          mass2 (histKF2 R P m o' t k X : SA .two (Lam 2 L N)).a‖ ≤
        ‖Grassmann.ε (histKF2 R P m o' t k X : SA .two (Lam 2 L N)).a‖ +
          ‖histCovO R t k P.a P.a‖ *
          ‖mass2 (histKF2 R P m o' t k X : SA .two (Lam 2 L N)).a‖ := fun X _ =>
      (norm_add_le _ _).trans (by rw [norm_mul])
    refine (sum_le_sum e).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    exact add_le_add hKe (mul_le_mul_of_nonneg_left hKm (norm_nonneg _))
  · have e : ∀ b, Grassmann.ε (EthO (histCovO R t k) (histWF2 R P m o' t k b) :
        SA .two (Lam 2 L N)).a =
        Grassmann.ε (expLC (histCovO R t k)
          ((obsHistFrom R P m o' k t).W b : SA .two (Lam 2 L N)).a) := by
      intro b; rw [EthO_a_eq, histWF2_a]
    simp only [e]
    refine (norm_sum_le _ _).trans ?_
    set S := blockIdx (L := L) (N := N) k
    set S' := S.filter (fun b => P.a ∈ nbhd k (blockSet (L := L) (N := N) k b))
    have hsplit : ∑ b ∈ S, ‖Grassmann.ε (expLC (histCovO R t k)
        ((obsHistFrom R P m o' k t).W b : SA .two (Lam 2 L N)).a)‖ =
        ∑ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t k)
          ((obsHistFrom R P m o' k t).W b : SA .two (Lam 2 L N)).a)‖ := by
      refine (sum_subset (filter_subset _ _) fun b hb hb' => ?_).symm
      have hna : P.a ∉ nbhd k (blockSet (L := L) (N := N) k b) := fun h =>
        hb' (mem_filter.2 ⟨hb, h⟩)
      rw [((ho.W b).2.2.2.2.1 hna).1, map_zero, map_zero, norm_zero]
    rw [hsplit]
    have hterm : ∀ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t k)
        ((obsHistFrom R P m o' k t).W b : SA .two (Lam 2 L N)).a)‖ ≤ Q1 2 * w := by
      intro b hb
      have hbS := (mem_filter.1 hb).1
      refine (norm_eps_expLC_le (by norm_num) hLp (by omega) hs hC (ho.W b).2.1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by have := one_le_Q1 (d := 2) (by norm_num); linarith)
      have h := hW b hbS
      rw [Obs2.oTo_wA] at h
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal hw] at h2
    have hc : (S'.card : ℝ) ≤ cBn := by
      exact_mod_cast Classical.choose_spec (Obs2.card_blocks_near 2) L N k P.a S subset_rfl
    calc ∑ b ∈ S', ‖Grassmann.ε (expLC (histCovO R t k)
          ((obsHistFrom R P m o' k t).W b : SA .two (Lam 2 L N)).a)‖
        ≤ ∑ _b ∈ S', Q1 2 * w := sum_le_sum hterm
      _ = S'.card * (Q1 2 * w) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ cBn * (Q1 2 * w) := mul_le_mul_of_nonneg_right hc (mul_nonneg (by
          have := one_le_Q1 (d := 2) (by norm_num); linarith) hw)

end Bd

end

end PtCorr2
