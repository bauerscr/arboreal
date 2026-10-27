import PtCorr2.Obs.ProdBdHist
import PtCorr2.Obs.ObsHistRelE

/-!
# The Case-(2) product bound `ProdBd2` along the history

Case-(2) analogue of `prodBd_hist`: the product parts `G_j(B_+;0)` and the increments
`muProdIncX2` are bounded with the Pauli-invariant Lipschitz bound of `m₂` (`delta_hist_le2`,
field scale `s²`) and the generic `prod_hist_step`. **`prodBd2_hist`**: `ProdBd2` with ratio
`2/L` and constant `prodCP2 L C_P = c_bn C_P((6/5)L + 3072K²)` along every regular history from
`obsInit .two V P` with `γ_a = 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The constant `c_P` of `prodBd2_hist`. -/
def prodCP2 (L : ℕ) (Cp : ℝ) : ℝ := cbnC * Cp * (6 / 5 * L + 3072 * locK 2 ^ 2)

/-- The final real inequality of `prodBd2_hist` (ratio `6/5` of the inverse scales). -/
theorem prodBd_real2 {L : ℕ} (hL0 : (0 : ℝ) < L) {K cb Cp x : ℝ} (hcb : 0 ≤ cb) (hCp : 0 ≤ Cp)
    (hK : 0 ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ 2 / L) (j : ℕ) (a s : ℕ → ℝ) (ha : ∀ k ≤ j, 0 ≤ a k)
    (hs : ∀ k, 0 < s k) (hss : ∀ k, (s (k + 1))⁻¹ ≤ 6 / 5 * (s k)⁻¹) :
    (if j = 0 then 0 else cb * (2 * Cp * a (j - 1)) / s j) +
        ∑ k ∈ range j, cb * (1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * a k) / s (k + 1)) ≤
      cb * Cp * (6 / 5 * L + 3072 * K ^ 2) *
        ∑ i ∈ range (j + 1), (2 / L : ℝ) ^ (j - i) * (a i / s i) := by
  set q : ℝ := 2 / L with hq
  have hq0 : 0 ≤ q := by positivity
  have hX : ∀ k ≤ j, 0 ≤ a k / s k := fun k hk => div_nonneg (ha k hk) (hs k).le
  have h1 : ∑ k ∈ range j, cb * (1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * a k) / s (k + 1)) ≤
      ∑ k ∈ range j, cb * Cp * (3072 * K ^ 2) * (q ^ (j - k) * (a k / s k)) := by
    refine sum_le_sum fun k hkr => ?_
    have hkj : k ≤ j := (mem_range.1 hkr).le
    have hxq : x ^ (j - k) ≤ q ^ (j - k) := pow_le_pow_left₀ hx0 hx _
    have hsk := hss k
    have e1 : cb * (1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * a k) / s (k + 1)) =
        (cb * Cp * K ^ 2 * a k) * (2560 * x ^ (j - k)) * (s (k + 1))⁻¹ := by ring
    have e2 : cb * Cp * (3072 * K ^ 2) * (q ^ (j - k) * (a k / s k)) =
        (cb * Cp * K ^ 2 * a k) * (3072 * q ^ (j - k)) * (s k)⁻¹ := by ring
    rw [e1, e2]
    have hA : 0 ≤ cb * Cp * K ^ 2 * a k := by have := ha k hkj; positivity
    have hB : 0 ≤ 2560 * x ^ (j - k) := by positivity
    calc (cb * Cp * K ^ 2 * a k) * (2560 * x ^ (j - k)) * (s (k + 1))⁻¹
        ≤ (cb * Cp * K ^ 2 * a k) * (2560 * x ^ (j - k)) * (6 / 5 * (s k)⁻¹) :=
          mul_le_mul_of_nonneg_left hsk (mul_nonneg hA hB)
      _ = (cb * Cp * K ^ 2 * a k) * (3072 * x ^ (j - k)) * (s k)⁻¹ := by ring
      _ ≤ (cb * Cp * K ^ 2 * a k) * (3072 * q ^ (j - k)) * (s k)⁻¹ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA)
            (inv_nonneg.2 (hs k).le)
          have : 0 ≤ q ^ (j - k) := pow_nonneg hq0 _
          nlinarith
  have h2 : (if j = 0 then 0 else cb * (2 * Cp * a (j - 1)) / s j) ≤
      ∑ k ∈ range j, cb * Cp * (6 / 5 * L) * (q ^ (j - k) * (a k / s k)) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [if_neg (by omega)]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hmem : j' ∈ range (j' + 1) := mem_range.2 (by omega)
      refine le_trans ?_ (single_le_sum (f := fun k => cb * Cp * (6 / 5 * L) *
        (q ^ (j' + 1 - k) * (a k / s k))) (fun k hk => by
          have := hX k (mem_range.1 hk).le; have : 0 ≤ q ^ (j' + 1 - k) := pow_nonneg hq0 _
          positivity) hmem)
      simp only [show j' + 1 - 1 = j' by omega, show j' + 1 - j' = 1 by omega, pow_one]
      have hsj := hss j'
      have e1 : cb * Cp * (6 / 5 * L) * (q * (a j' / s j')) = cb * Cp * (12 / 5) * a j' * (s j')⁻¹ := by
        rw [hq]; field_simp; ring
      rw [e1]
      have e2 : cb * (2 * Cp * a j') / s (j' + 1) = cb * Cp * 2 * a j' * (s (j' + 1))⁻¹ := by ring
      rw [e2]
      have hA : 0 ≤ cb * Cp * 2 * a j' := by have := ha j' (by omega); positivity
      calc cb * Cp * 2 * a j' * (s (j' + 1))⁻¹ ≤ cb * Cp * 2 * a j' * (6 / 5 * (s j')⁻¹) :=
            mul_le_mul_of_nonneg_left hsj hA
        _ = _ := by ring
  have h3 : ∑ k ∈ range j, cb * Cp * (6 / 5 * L) * (q ^ (j - k) * (a k / s k)) +
      ∑ k ∈ range j, cb * Cp * (3072 * K ^ 2) * (q ^ (j - k) * (a k / s k)) ≤
      cb * Cp * (6 / 5 * L + 3072 * K ^ 2) * ∑ i ∈ range (j + 1), q ^ (j - i) * (a i / s i) := by
    rw [← sum_add_distrib, mul_sum]
    have e : ∀ k ∈ range j, cb * Cp * (6 / 5 * L) * (q ^ (j - k) * (a k / s k)) +
        cb * Cp * (3072 * K ^ 2) * (q ^ (j - k) * (a k / s k)) =
        cb * Cp * (6 / 5 * L + 3072 * K ^ 2) * (q ^ (j - k) * (a k / s k)) := fun k _ => by ring
    rw [sum_congr rfl e]
    refine sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun i hi _ => ?_
    have := hX i (Nat.lt_succ_iff.1 (mem_range.1 hi)); have : 0 ≤ q ^ (j - i) := pow_nonneg hq0 _
    have : 0 ≤ (L : ℝ) := hL0.le
    positivity
  linarith

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 2000000 in
/-- **`ProdBd2` along the history** (Case (2), `γ_a = 0`; ratio `2/L`, constant `prodCP2 L C_P`). -/
theorem prodBd2_hist {Cp εp : ℝ} (hPB : PObsBounds L Cp εp) (hCp : 0 ≤ Cp)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n ≤ Nh) (hnN : n < N) (hVL : ValidAtL R n)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hεp : cR R Λ cm C₂ * ε ≤ εp) (hL : prodLb ≤ L) :
    ProdBd2 R P (obsInit .two V P) t n (fun j => cR R Λ cm C₂ * (t j).1) (prodCP2 L Cp) (2 / L) := by
  intro j hj mm hmm
  set o₀ := obsInit .two V P with ho₀
  have h0 : o₀.IsObs := obsInit_isObs .two V P
  have hl0 : ObsLocInv P 0 o₀ := obsLocInv_init .two V P
  have hs0 : ObsSymInv 0 o₀ := obsSymInv_init .two V P
  set rr : ℕ → ℝ := fun j => cR R Λ cm C₂ * (t j).1 with hrr
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  have hVn : ∀ i < n, ValidAt R i := fun i hi => hV i (by omega)
  have HC := muChain2_obsHist R P o₀ t hnN (fun b => obsInit_two_W P V b)
    (fun b => obsInit_two_form P V b)
  have hDh : ∀ k ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t := fun k hk =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hr0 : ∀ k ≤ n, 0 ≤ rr k := fun k hk => mul_nonneg hcR (ht.1 k hk).1.le
  have hs : ∀ i, 0 < histS R i t := histS_pos' R hρ0 hρ t
  have hm0 : ∀ k ≤ j, 0 ≤ mm k := fun k hk => (hmm k hk).1
  -- the block bound of `V^{obs}_k`
  have hVo : ∀ k ≤ j, ∀ b ∈ blockIdx (L := L) (N := N) k,
      oTo Obs2.wA k (histS R k t) ((obsHist R P o₀ k t).V b) ≤ ENNReal.ofReal (mm k) := by
    intro k hk b hb'
    have hsm := (hmm k hk).2.1
    rw [Obs2.oTo_wA, obsHist2_pure R P t V hga k b]
    refine (Tj_smul_pbp_le k (hs k) _ _).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hsm))
    have h1 : ‖mass2 ((obsHist R P o₀ k t).V b : SA .two (Lam 2 L N)).a‖ ≤
        shA2 (histVO2 R P o₀ t) k := by
      rw [← histVO2_a R P o₀ t k b]
      exact single_le_sum (f := fun b => ‖mass2
        (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- the product parts of the steps `k < j`
  have hPk : ∀ k < j, ∀ c'' ∈ blockIdx (L := L) (N := N) (k + 1),
      Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t)
        ((prodO P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) c'' :
          SA .two (Lam 2 L N)).a) ≤ ENNReal.ofReal (2 * Cp * rr k ^ 2 * mm k) ∧
      prodO P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) c'' ∈
        osub P (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'')) := by
    intro k hk c'' hc''
    have hkn : k < n := by omega
    have hrk := hr0 k hkn.le
    obtain ⟨h1, h2⟩ := prod_hist_step R hPB hSB hV hm hβ hδ1 H P Obs2.wA Obs2.wA_ab o₀ h0 hl0 hs0 t k
      (by omega) (hDh k hkn.le) hεp (mm k) (rr k * mm k) (hm0 k hk.le)
      (mul_nonneg hrk (hm0 k hk.le)) (hVo k hk.le) (hmm k hk.le).2.2 c'' hc''
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
  set gterm : (Fin 2 → ℕ) → ℝ := fun c'' => if j = 0 then 0 else
    if P.a ∈ nbhd j (blockSet (L := L) (N := N) j c'') then
      2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R j t ^ 2 else 0 with hgterm
  set dterm : ℕ → (Fin 2 → ℕ) → ℝ := fun k c'' =>
    if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) c'') then
      1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * rr k ^ 2 * mm k) / histS R (k + 1) t ^ 2 else 0 with hdterm
  -- the term `G_j(B_+; 0)`
  have hG : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j mass2L (histWO2 R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0‖ ≤
        ∑ c'' ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), gterm c'' := by
    intro c' hc'
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have : wTadX 0 mass2L (histWO2 R P o₀ t 0) (blockSet (L := L) (N := N) (0 + 1) c') 0
          = 0 := by
        unfold wTadX
        refine sum_eq_zero fun b _ => ?_
        rw [HC.hW0 b, map_zero, map_zero]
      rw [this, norm_zero]
      exact sum_nonneg fun c'' _ => by simp [hgterm]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hX : IsPolymer (j' + 1) (blockSet (L := L) (N := N) (j' + 1 + 1) c') :=
        IsPolymer.of_succ (isPolymer_blockSet _ c')
      rw [HC.wTadX_succ (by omega) hX 0, tau2, expLC_zero, sub_self, mul_zero, zero_add, zero_add,
        sub_self, add_zero, wProdX_eq_prodO]
      refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
      rw [expLC_zero]
      have hc''I := mem_blockIdx_of_mem_blocks hc''
      obtain ⟨hT, hmem⟩ := hPk j' (by omega) c'' hc''I
      simp only [hgterm, if_neg (Nat.succ_ne_zero j'), Nat.add_sub_cancel]
      split_ifs with ha
      · show ‖mass2 _‖ ≤ _
        refine (norm_mass2_le (hs (j' + 1)) (j' + 1) _).trans ?_
        have hB : 0 ≤ 2 * Cp * rr j' ^ 2 * mm j' := by
          have := hm0 j' (by omega); positivity
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
        rw [ENNReal.toReal_ofReal hB] at this
        rw [div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_right this (by positivity)
      · rw [osub_a_zero hmem ha, map_zero, norm_zero]
  -- the increments
  have hD : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖muProdIncX2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
        ∑ k ∈ range j, ∑ c'' ∈ blocks (k + 1) (blockSet (L := L) (N := N) (j + 1) c'),
          dterm k c'' := by
    intro c' hc'
    unfold muProdIncX2
    refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
    rw [wProdX_eq_prodO, wProdX_eq_prodO, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
    have hk' : k < j := mem_range.1 hk
    have hc''I := mem_blockIdx_of_mem_blocks hc''
    obtain ⟨hT, hmem⟩ := hPk k hk' c'' hc''I
    simp only [hdterm]
    split_ifs with ha
    · have hB : 0 ≤ 2 * Cp * rr k ^ 2 * mm k := by
        have := hm0 k hk'.le; have := hr0 k (by omega); positivity
      exact delta_hist_le2 R hρ0 hρ hnN hVn hVL t P hk' hj hL hc''I hmem.2.1 ha hB hT
    · rw [osub_a_zero hmem ha]; simp
  -- the sum over the `(j+1)`-blocks
  show ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j mass2L (histWO2 R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
        muProdIncX2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤ _
  have hS1 : ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖wTadX j mass2L (histWO2 R P o₀ t j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
        muProdIncX2 P (histCovO R t) (histVO2 R P o₀ t) (histWO2 R P o₀ t) j
          (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
      ∑ c'' ∈ blockIdx (L := L) (N := N) j, gterm c'' +
        ∑ k ∈ range j, ∑ c'' ∈ blockIdx (L := L) (N := N) (k + 1), dterm k c'' := by
    refine (sum_le_sum fun c' hc' => (norm_add_le _ _).trans
      (add_le_add (hG c' hc') (hD c' hc'))).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_blockIdx_le gterm (by omega : j ≤ j + 1), sum_comm]
    congr 1
    exact sum_congr rfl fun k hk => sum_blockIdx_le (dterm k) (by have := mem_range.1 hk; omega)
  have hS2 : ∑ c'' ∈ blockIdx (L := L) (N := N) j, gterm c'' ≤
      (if j = 0 then 0 else cbnC * (2 * Cp * (rr (j - 1) ^ 2 * mm (j - 1))) / histS R j t ^ 2) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hgterm]
    · simp only [hgterm, if_neg (by omega : j ≠ 0)]
      have hv : 0 ≤ 2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R j t ^ 2 := by
        have := hm0 (j - 1) (by omega); have := hs j; positivity
      refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
      ring
  have hS3 : ∑ k ∈ range j, ∑ c'' ∈ blockIdx (L := L) (N := N) (k + 1), dterm k c'' ≤
      ∑ k ∈ range j, cbnC * (1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * (rr k ^ 2 * mm k)) /
        histS R (k + 1) t ^ 2) := by
    refine sum_le_sum fun k hk => ?_
    have hk' := mem_range.1 hk
    have hv : 0 ≤ 1280 * K ^ 2 * x ^ (j - k) * (2 * Cp * rr k ^ 2 * mm k) / histS R (k + 1) t ^ 2 := by
      have := hm0 k hk'.le; have := hs (k + 1); positivity
    refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
    ring
  have hss : ∀ k, (histS R (k + 1) t ^ 2)⁻¹ ≤ 6 / 5 * (histS R k t ^ 2)⁻¹ := by
    intro k
    have h1 := hss1 k
    have h2 : 0 ≤ (histS R (k + 1) t)⁻¹ := inv_nonneg.2 (hs _).le
    rw [← inv_pow, ← inv_pow]
    have h3 : (histS R (k + 1) t)⁻¹ ^ 2 ≤ (15 / 14 * (histS R k t)⁻¹) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h4 : 0 ≤ (histS R k t)⁻¹ ^ 2 := sq_nonneg _
    nlinarith
  have hfin := prodBd_real2 (K := K) hL0 (Nat.cast_nonneg cbnC) hCp (by positivity) hx0 hx2 j
    (fun k => rr k ^ 2 * mm k) (fun k => histS R k t ^ 2)
    (fun k hk => mul_nonneg (sq_nonneg _) (hm0 k hk)) (fun k => pow_pos (hs k) 2) hss
  refine hS1.trans ((add_le_add hS2 hS3).trans (hfin.trans (le_of_eq ?_)))
  rw [prodCP2]

end Hist

end

end PtCorr2
