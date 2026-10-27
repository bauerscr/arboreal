import PtCorr2.Restart.RestartHist

/-!
# The restart theorem without named inputs (B3, T4)

The two size inputs of `obs_hist_restart` are discharged along the history:

* `prod_hist_stepF`: the product part of a step of the restarted flow (`PObsBounds`, the state
  at scale `j` along `obsHistFrom`);
* **`prodBd2F_hist`**: `ProdBd2F` with ratio `2/L` and constant `prodCP2 L C_P` (copy of
  `prodBd2_hist`, indices shifted by `m`);
* **`initBd2F_hist`**: `InitBd2F` with `x_h = c_bn(1280K²·8/(7L) + 1)·w₀/(s_m²M₀)` for a datum
  with `‖𝒲_m(B)‖_{T_m(s_m)} ≤ w₀` (`m ≥ 1`): the tadpoles of the initial `𝒲_m` against the later
  covariances decay like `(8/(7L))^{j−m+1}` (`delta_hist_le2` at `k + 1 = m`), and the datum's own
  `𝒲`-mass enters once;
* **`obs_hist_restartP`**: `obs_hist_restart` with these inputs discharged, the `𝒲` datum
  `w₀ = c_W r_m·2s_m²M₀`, hence `x_h = c_bn(1280K²·8/(7L) + 1)·2c_W r_m`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The product part along the restarted history.** -/
theorem prod_hist_stepF {Cp εp : ℝ} (hPB : PObsBounds L Cp εp)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0)
    {m : ℕ} (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o') (hs0 : ObsSymInv m o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : m ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hεp : cR R Λ cm C₂ * ε ≤ εp) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P m o' j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P m o' j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) (histS R (j + 1) t)
        (prodO P j (stCov R j (rawHist R j t))
          (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHistFrom R P m o' j t))
          (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2)
            (obsHistFrom R P m o' j t)) c') ≤
        ENNReal.ofReal (Cp * (cR R Λ cm C₂ * (t j).1) * (cR R Λ cm C₂ * (t j).1 * mV + mW)) ∧
      prodO P j (stCov R j (rawHist R j t))
          (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHistFrom R P m o' j t))
          (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2)
            (obsHistFrom R P m o' j t)) c' ∈
        osub P (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c')) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  obtain ⟨hobs, hloc, hsym⟩ := histFrom_inv R hV P h0 hl0 hs0 t hmj hj
  exact hPB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2) (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs c P w hw0 _ hobs hloc hsym _ _ _ mV mW
    (by positivity) (norm_nonneg _) hr0.le (hrε.trans hεp) hmV hmW hWl hDd hvr hwr hVo hWo

/-- The block bound of `V^{obs}` along the restarted history from the `ℓ¹` size. -/
theorem hVo_F (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (P : ObsPts 2 L N) {m : ℕ}
    (o' : ObsSt .two L N) (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a) (t : Flow2.Hist.Seq (Xs R))
    (j : ℕ) (hmj : m ≤ j) (mm : ℝ) (hsm : histS R j t ^ 2 * shA2 (histVF2 R P m o' t) j ≤ mm) :
    ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo Obs2.wA j (histS R j t) ((obsHistFrom R P m o' j t).V b) ≤ ENNReal.ofReal mm := by
  intro b hb'
  have hs := histS_pos' R hρ0 hρ t j
  rw [Obs2.oTo_wA, obsHistF2_pure R P m o' t hf0 hp0 j hmj b]
  refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hsm))
  have h1 : ‖mass2 ((obsHistFrom R P m o' j t).V b : SA .two (Lam 2 L N)).a‖ ≤
      shA2 (histVF2 R P m o' t) j := by
    rw [← histVF2_a R P m o' t j b]
    exact single_le_sum (f := fun b => ‖mass2
      (histVF2 R P m o' t j b : SA .two (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

set_option maxHeartbeats 2000000 in
/-- **`ProdBd2F` along the restarted history** (ratio `2/L`, constant `prodCP2 L C_P`). -/
theorem prodBd2F_hist {Cp εp : ℝ} (hPB : PObsBounds L Cp εp) (hCp : 0 ≤ Cp)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o')
    (hs0 : ObsSymInv m o') (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hmn : m ≤ n) (hn : n ≤ Nh) (hnN : n < N)
    (hVL : ValidAtL R n) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hεp : cR R Λ cm C₂ * ε ≤ εp) (hL : prodLb ≤ L) :
    ProdBd2F R P m o' t n (fun i => cR R Λ cm C₂ * (t (m + i)).1) (prodCP2 L Cp) (2 / L) := by
  intro j hj0 hj mm hmm
  set rr : ℕ → ℝ := fun i => cR R Λ cm C₂ * (t (m + i)).1 with hrr
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  have hVn : ∀ i < n, ValidAt R i := fun i hi => hV i (by omega)
  have HC := muChain2F_histFrom R P m o' t hmn hnN hf0
  have hDh : ∀ k ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t := fun k hk =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hr0 : ∀ k ≤ n - m, 0 ≤ rr k := fun k hk => mul_nonneg hcR (ht.1 (m + k) (by omega)).1.le
  have hs : ∀ i, 0 < histS R i t := histS_pos' R hρ0 hρ t
  have hm0 : ∀ k ≤ j, 0 ≤ mm k := fun k hk => (hmm k hk).1
  -- the product parts of the steps `m + i`, `i < j`
  have hPk : ∀ i < j, ∀ c'' ∈ blockIdx (L := L) (N := N) (m + i + 1),
      Tj 2 (L : ℝ) (m + i + 1) (histS R (m + i + 1) t)
        ((prodO P (m + i) (histCovO R t (m + i)) (histVF2 R P m o' t (m + i))
          (histWF2 R P m o' t (m + i)) c'' : SA .two (Lam 2 L N)).a) ≤
        ENNReal.ofReal (2 * Cp * rr i ^ 2 * mm i) ∧
      prodO P (m + i) (histCovO R t (m + i)) (histVF2 R P m o' t (m + i))
          (histWF2 R P m o' t (m + i)) c'' ∈
        osub P (nbhd (m + i + 1) (blockSet (L := L) (N := N) (m + i + 1) c'')) := by
    intro i hi c'' hc''
    have hrk := hr0 i (by omega)
    obtain ⟨h1, h2⟩ := prod_hist_stepF R hPB hSB hV hm hβ hδ1 H P Obs2.wA Obs2.wA_ab o' h0 hl0
      hs0 t (m + i) (by omega) (by omega) (hDh (m + i) (by omega)) hεp (mm i) (rr i * mm i)
      (hm0 i hi.le) (mul_nonneg hrk (hm0 i hi.le))
      (hVo_F R hρ0 hρ P o' hf0 hp0 t (m + i) (by omega) (mm i) (hmm i hi.le).2.1)
      (hmm i hi.le).2.2 c'' hc''
    refine ⟨?_, h2⟩
    rw [← Obs2.oTo_wA]
    refine h1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [hrr]; ring
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 2 / L := by
    rw [hx, div_le_div_iff₀ (by positivity) hL0]; nlinarith
  have hss1 : ∀ k, (histS R (k + 1) t)⁻¹ ≤ 15 / 14 * (histS R k t)⁻¹ := by
    intro k
    have e : histS R (k + 1) t = histS R k t * fscale (1 + zetaH R k t) := by
      unfold histS; rw [rawHist_succ_Z, fscale_mul]; ring
    have hz : ‖zetaH R k t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
    have h1 := fscale_one_add_ge hz
    have hf : 0 < fscale (1 + zetaH R k t) := by linarith
    have hfi : (fscale (1 + zetaH R k t))⁻¹ ≤ 15 / 14 := by
      rw [inv_le_iff_one_le_mul₀ hf]; nlinarith
    rw [e, mul_inv]
    calc (histS R k t)⁻¹ * (fscale (1 + zetaH R k t))⁻¹ ≤ (histS R k t)⁻¹ * (15 / 14) :=
          mul_le_mul_of_nonneg_left hfi (inv_nonneg.2 (hs k).le)
      _ = _ := by ring
  set J := m + j with hJ
  set gterm : (Fin 2 → ℕ) → ℝ := fun c'' =>
    if P.a ∈ nbhd J (blockSet (L := L) (N := N) J c'') then
      2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R J t ^ 2 else 0 with hgterm
  set dterm : ℕ → (Fin 2 → ℕ) → ℝ := fun i c'' =>
    if P.a ∈ nbhd (m + i + 1) (blockSet (L := L) (N := N) (m + i + 1) c'') then
      1280 * K ^ 2 * x ^ (j - i) * (2 * Cp * rr i ^ 2 * mm i) / histS R (m + i + 1) t ^ 2
    else 0 with hdterm
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  -- the term `G_J(B_+; 0)`
  have hG : ∀ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖wTadX J mass2L (histWF2 R P m o' t J) (blockSet (L := L) (N := N) (J + 1) c') 0‖ ≤
        ∑ c'' ∈ blocks J (blockSet (L := L) (N := N) (J + 1) c'), gterm c'' := by
    intro c' hc'
    have hX : IsPolymer (m + j' + 1) (blockSet (L := L) (N := N) (J + 1) c') :=
      IsPolymer.of_succ (isPolymer_blockSet _ c')
    have hJ' : J = m + j' + 1 := by rw [hJ]; ring
    rw [hJ'] at hX ⊢
    rw [HC.wTadX_succ (by omega) (by omega) hX 0, tau2, expLC_zero, sub_self, mul_zero, zero_add,
      zero_add, sub_self, add_zero, wProdX_eq_prodO]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
    rw [expLC_zero]
    have hc''I := mem_blockIdx_of_mem_blocks hc''
    obtain ⟨hT, hmem⟩ := hPk j' (by omega) c'' hc''I
    simp only [hgterm, hJ', Nat.add_sub_cancel]
    split_ifs with ha
    · show ‖mass2 _‖ ≤ _
      refine (norm_mass2_le (hs (m + j' + 1)) (m + j' + 1) _).trans ?_
      have hB : 0 ≤ 2 * Cp * rr j' ^ 2 * mm j' := by
        have := hm0 j' (by omega); positivity
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
      rw [ENNReal.toReal_ofReal hB] at this
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · rw [osub_a_zero hmem ha, map_zero, norm_zero]
  -- the increments
  have hD : ∀ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖muProdIncX2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m J
          (blockSet (L := L) (N := N) (J + 1) c')‖ ≤
        ∑ i ∈ range (j' + 1), ∑ c'' ∈ blocks (m + i + 1) (blockSet (L := L) (N := N) (J + 1) c'),
          dterm i c'' := by
    intro c' hc'
    unfold muProdIncX2F
    rw [sum_Ico_eq_sum_range, show J - m = j' + 1 by omega]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
    rw [wProdX_eq_prodO, wProdX_eq_prodO, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
    have hi' : i < j' + 1 := mem_range.1 hi
    have hc''I := mem_blockIdx_of_mem_blocks hc''
    obtain ⟨hT, hmem⟩ := hPk i hi' c'' hc''I
    simp only [hdterm]
    split_ifs with ha
    · have hB : 0 ≤ 2 * Cp * rr i ^ 2 * mm i := by
        have := hm0 i hi'.le; have := hr0 i (by omega); positivity
      have h := delta_hist_le2 R hρ0 hρ hnN hVn hVL t P (k := m + i) (j := J) (by omega)
        (by omega) hL hc''I hmem.2.1 ha hB hT
      rw [show J - (m + i) = j' + 1 - i by omega] at h
      exact h
    · rw [osub_a_zero hmem ha]; simp
  -- the sum over the `(J+1)`-blocks
  show ∑ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖wTadX J mass2L (histWF2 R P m o' t J) (blockSet (L := L) (N := N) (J + 1) c') 0 +
        muProdIncX2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m J
          (blockSet (L := L) (N := N) (J + 1) c')‖ ≤ _
  have hS1 : ∑ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖wTadX J mass2L (histWF2 R P m o' t J) (blockSet (L := L) (N := N) (J + 1) c') 0 +
        muProdIncX2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m J
          (blockSet (L := L) (N := N) (J + 1) c')‖ ≤
      ∑ c'' ∈ blockIdx (L := L) (N := N) J, gterm c'' +
        ∑ i ∈ range (j' + 1), ∑ c'' ∈ blockIdx (L := L) (N := N) (m + i + 1), dterm i c'' := by
    refine (sum_le_sum fun c' hc' => (norm_add_le _ _).trans
      (add_le_add (hG c' hc') (hD c' hc'))).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_blockIdx_le gterm (by omega : J ≤ J + 1), sum_comm]
    congr 1
    exact sum_congr rfl fun i hi => sum_blockIdx_le (dterm i) (by have := mem_range.1 hi; omega)
  have hS2 : ∑ c'' ∈ blockIdx (L := L) (N := N) J, gterm c'' ≤
      cbnC * (2 * Cp * (rr j' ^ 2 * mm j')) / histS R (m + (j' + 1)) t ^ 2 := by
    simp only [hgterm, Nat.add_sub_cancel]
    have hv : 0 ≤ 2 * Cp * rr j' ^ 2 * mm j' / histS R J t ^ 2 := by
      have := hm0 j' (by omega); have := hs J; positivity
    refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
    rw [hJ]; ring
  have hS3 : ∑ i ∈ range (j' + 1), ∑ c'' ∈ blockIdx (L := L) (N := N) (m + i + 1), dterm i c'' ≤
      ∑ i ∈ range (j' + 1), cbnC * (1280 * K ^ 2 * x ^ (j' + 1 - i) * (2 * Cp * (rr i ^ 2 * mm i)) /
        histS R (m + (i + 1)) t ^ 2) := by
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.1 hi
    have hv : 0 ≤ 1280 * K ^ 2 * x ^ (j' + 1 - i) * (2 * Cp * rr i ^ 2 * mm i) /
        histS R (m + i + 1) t ^ 2 := by
      have := hm0 i hi'.le; have := hs (m + i + 1); positivity
    refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
    rw [← add_assoc]; ring
  have hss : ∀ k, (histS R (m + (k + 1)) t ^ 2)⁻¹ ≤ 6 / 5 * (histS R (m + k) t ^ 2)⁻¹ := by
    intro k
    have h1 := hss1 (m + k)
    have h2 : 0 ≤ (histS R (m + k + 1) t)⁻¹ := inv_nonneg.2 (hs _).le
    rw [← inv_pow, ← inv_pow, ← add_assoc]
    have h3 : (histS R (m + k + 1) t)⁻¹ ^ 2 ≤ (15 / 14 * (histS R (m + k) t)⁻¹) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h4 : 0 ≤ (histS R (m + k) t)⁻¹ ^ 2 := sq_nonneg _
    nlinarith
  have hfin := prodBd_real2 (K := K) hL0 (Nat.cast_nonneg cbnC) hCp (by positivity) hx0 hx2
    (j' + 1) (fun k => rr k ^ 2 * mm k) (fun k => histS R (m + k) t ^ 2)
    (fun k hk => mul_nonneg (sq_nonneg _) (hm0 k hk)) (fun k => pow_pos (hs (m + k)) 2) hss
  rw [if_neg (Nat.succ_ne_zero j'), Nat.add_sub_cancel] at hfin
  refine hS1.trans ((add_le_add hS2 hS3).trans (hfin.trans (le_of_eq ?_)))
  rw [prodCP2]

set_option maxHeartbeats 1000000 in
/-- **`InitBd2F` along the restarted history** (`m ≥ 1`, datum `‖𝒲_m(B)‖ ≤ w₀`). -/
theorem initBd2F_hist (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) {m : ℕ} (hm1 : 0 < m) (o' : ObsSt .two L N) (hl0 : ObsLocInv P m o')
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hnN : n < N) (hVn : ∀ i < n, ValidAt R i)
    (hVL : ValidAtL R n) (hL : prodLb ≤ L) {w₀ M₀ : ℝ} (hw₀ : 0 ≤ w₀) (hM0 : 0 < M₀)
    (hW0 : WbHF R P m o' t m w₀) :
    InitBd2F R P m o' t n (cbnC * (1280 * locK 2 ^ 2 * (8 / (7 * L)) + 1) * w₀ /
      (histS R m t ^ 2 * M₀)) M₀ := by
  intro i hi
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ (by positivity)]; nlinarith
  have hs := histS_pos' R hρ0 hρ t m
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- the datum's `𝒲`: local and bounded
  have hWb : ∀ b, (o'.W b : OE .two (Lam 2 L N)) ∈ osub P
      (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b)) := hl0.W
  have hWT : ∀ b ∈ blockIdx (L := L) (N := N) (k + 1),
      Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) (histWF2 R P (k + 1) o' t (k + 1) b :
        SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal w₀ := by
    intro b hb
    have h := hW0 b hb
    rw [Obs2.oTo_wA, obsHistFrom_self] at h
    rw [histWF2_a, obsHistFrom_self]
    exact h
  have hWa : ∀ b, (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a =
      (o'.W b : SA .two (Lam 2 L N)).a := fun b => by rw [histWF2_a, obsHistFrom_self]
  -- the tadpole term at `J = m + i`
  set J := k + 1 + i with hJ
  have hcum : cumFrom (histCovO R t) (k + 1) J = cumBetween (histCovO R t) k J := by
    unfold cumFrom cumBetween
    congr 1
  have hterm : ∀ b ∈ blockIdx (L := L) (N := N) (k + 1),
      ‖mass2L (expLC (histCovO R t J + cumFrom (histCovO R t) (k + 1) J)
          (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a) -
        mass2L (expLC (cumFrom (histCovO R t) (k + 1) J)
          (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a)‖ ≤
      (if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b) then
        1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 else 0) := by
    intro b hb
    rw [hcum]
    split_ifs with ha
    · rw [hWa]
      have hF := (hWb b).2.1
      have h := delta_hist_le2 R hρ0 hρ hnN hVn hVL t P (k := k) (j := J) (by omega) (by omega)
        hL hb hF ha hw₀ (by rw [← hWa]; exact hWT b hb)
      exact h
    · rw [hWa, osub_a_zero (hWb b) ha]; simp
  have hinit : shInit2 (histCovO R t) (histWF2 R P (k + 1) o' t) (k + 1) J ≤
      cbnC * (1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2) := by
    unfold shInit2 wInitX2 wTadX
    have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (J + 1),
        ‖∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (J + 1) c'),
            mass2L (expLC (histCovO R t J + cumFrom (histCovO R t) (k + 1) J)
              (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a) -
          ∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (J + 1) c'),
            mass2L (expLC (cumFrom (histCovO R t) (k + 1) J)
              (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a)‖ ≤
        ∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (J + 1) c'),
          (if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b) then
            1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 else 0) := by
      intro c' _
      rw [← sum_sub_distrib]
      exact (norm_sum_le _ _).trans (sum_le_sum fun b hb =>
        hterm b (mem_blockIdx_of_mem_blocks hb))
    refine (sum_le_sum h1).trans ?_
    rw [sum_blockIdx_le _ (by omega : k + 1 ≤ J + 1)]
    have hv : 0 ≤ 1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 := by positivity
    exact sum_ite_near_le P.a hv
  have hxp : x ^ (J - k) ≤ x * (1 / 2) ^ i := by
    rw [show J - k = i + 1 by omega, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 i) hx0
  have hcb : (0 : ℝ) ≤ cbnC := Nat.cast_nonneg _
  have hinit' : shInit2 (histCovO R t) (histWF2 R P (k + 1) o' t) (k + 1) J ≤
      cbnC * (1280 * K ^ 2 * x) * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i := by
    refine hinit.trans (le_of_eq_of_le rfl ?_)
    have h2 : 1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 ≤
        1280 * K ^ 2 * (x * (1 / 2) ^ i) * w₀ / histS R (k + 1) t ^ 2 := by
      gcongr
    have := mul_le_mul_of_nonneg_left h2 hcb
    calc _ ≤ _ := this
      _ = _ := by ring
  -- the `𝒲`-mass of the datum
  have hmass : (if i = 0 then shPr2F P (histCovO R t) (histVF2 R P (k + 1) o' t)
      (histWF2 R P (k + 1) o' t) (k + 1) (k + 1) else 0) ≤
      cbnC * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i := by
    split_ifs with hi0
    · subst hi0
      rw [pow_zero, mul_one]
      unfold shPr2F muProdIncX2F
      simp only [Ico_self, sum_empty, add_zero]
      unfold wTadX
      have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (k + 1 + 1),
          ‖∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (k + 1 + 1) c'),
              mass2L (expLC 0 (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a)‖ ≤
            ∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (k + 1 + 1) c'),
              (if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b) then
                w₀ / histS R (k + 1) t ^ 2 else 0) := by
        intro c' _
        refine (norm_sum_le _ _).trans (sum_le_sum fun b hb => ?_)
        rw [expLC_zero]
        split_ifs with ha
        · show ‖mass2 _‖ ≤ _
          refine (norm_mass2_le hs (k + 1) _).trans ?_
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hWT b (mem_blockIdx_of_mem_blocks hb))
          rw [ENNReal.toReal_ofReal hw₀] at this
          rw [div_eq_mul_inv, ← inv_pow]
          exact mul_le_mul_of_nonneg_right this (by positivity)
        · rw [hWa, osub_a_zero (hWb b) ha]; simp
      refine (sum_le_sum h1).trans ?_
      rw [sum_blockIdx_le _ (by omega : k + 1 ≤ k + 1 + 1)]
      have hv : 0 ≤ w₀ / histS R (k + 1) t ^ 2 := by positivity
      refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
      ring
    · positivity
  have e : cbnC * (1280 * locK 2 ^ 2 * (8 / (7 * L)) + 1) * w₀ / (histS R (k + 1) t ^ 2 * M₀) *
      (1 / 2) ^ i * M₀ = cbnC * (1280 * K ^ 2 * x) * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i +
        cbnC * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i := by
    rw [hx]; field_simp; ring
  rw [e]
  exact add_le_add hinit' hmass

end Hist

end

end PtCorr2
