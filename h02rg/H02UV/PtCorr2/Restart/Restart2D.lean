import PtCorr2.Obs.ObsHistLast

/-!
# The share deviation of the one-point flow is `O(ǧ_j)` (B3, T6 input)

**`obs_hist_rel2_baseXD`** (copy of `obs_hist_rel2_baseX`, other conclusion): along the one-point
history from `obsInit .two V P` (`γ_a = 0`),
`D_j = shareDev2 P.a j V_j ≤ 6c_δ c_R²(ǧ_j/(β/4))|β_j|`,
from `D_j ≤ 6c_δ∑_{k<j}r_k²b_j` (`RelRec.close`) and `∑_{k<j}ǧ_k² ≤ (ǧ_j − ǧ_0)/(β/4)`
(`Step2.sum_sq_le`, the coupling grows along the band).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Main

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **`obs_hist_rel2_base` with the `ℓ¹` size of `V^{obs}`** (copy): in addition
`∑_B|m₂(V_j(B)_a)| ≤ 2|β_j|` for `j ≤ n` (`A_j ≤ b_j + D_j`, `D_j ≤ 6c_δ∑r²b_j ≤ (3/4)b_j`). -/
theorem obs_hist_rel2_baseXD {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (hmu : OCoup2.mua V ≠ 0)
    (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (hn : n ≤ Nh) (hNh : 0 < Nh) (hnN : n < N)
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
    (hPr : ProdBd2 R P (obsInit .two V P) t n (fun j => cR R Λ cm C₂ * (t j).1) cP qq) :
    ∀ j ≤ n, shareDev2 P.a j (histVO2 R P (obsInit .two V P) t j) ≤
      6 * (cδ * (cR R Λ cm C₂ ^ 2 * ((t j).1 / (β / 4)))) *
        ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖ := by
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
  have hsj : ∀ j ≤ n, 0 < histS R j t := by
    intro j hj
    rcases Nat.lt_or_ge j Nh with h | h
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩ :=
        hist_raw R hSB hV hm hβ hδ1 H t j h (hDh j hj)
      exact hs
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs'⟩ :=
        hist_raw R hSB hV hm hβ hδ1 H t i (by omega) (hDh i (by omega))
      exact hs'
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
    hPr := hPr
    hT := fun k j _ _ => ⟨mul_nonneg hBτ (pow_nonneg hqq0 _), le_rfl⟩
    hdg := fun i _ => ⟨le_rfl, mul_nonneg hcg (sq_nonneg _)⟩
    hG := fun i hi => ⟨hG i hi, by
      show (t i).1 ≤ cgb * (cR R Λ cm C₂ * (t i).1)
      rw [← mul_assoc]
      have := (ht.1 i hi.le).1.le
      nlinarith⟩
    hnn := fun i hi => ⟨norm_nonneg _, hnn i hi⟩ }
  have RR := HC.relRec2 Tt hG hTt I
  intro j hj
  obtain ⟨hb, hD, -, -⟩ := (RR.close n le_rfl).1 j hj
  simp only at hD hb
  have h1 := Step2.sum_sq_le hβ' j (fun k hk => hinc k (by omega))
  have hg0 := (ht.1 0 (Nat.zero_le _)).1
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have h2 : ∑ k ∈ range j, rr k ^ 2 = cR R Λ cm C₂ ^ 2 * ∑ k ∈ range j, (t k).1 ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by rw [hrr]; ring
  have h3 : ((t j).1 - (t 0).1) / (β / 4) ≤ (t j).1 / (β / 4) :=
    div_le_div_of_nonneg_right (by linarith) hβ'.le
  have h4 : cδ * ∑ k ∈ range j, rr k ^ 2 ≤ cδ * (cR R Λ cm C₂ ^ 2 * ((t j).1 / (β / 4))) := by
    rw [h2]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg _)) hcδ0
  have h5 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 6))
    hb.le
  exact hD.trans h5

end Main

end

end PtCorr2
