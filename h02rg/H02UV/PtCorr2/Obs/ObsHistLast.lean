import PtCorr2.Obs.ObsHistTop
import Obs2.Flow.GamTop

/-!
# The observable data of the last step `j = N_h + 1 = N - 1`

* **`obs_hist_rel2_baseX`** (copy of `obs_hist_rel2_base`): the block bounds of the relative
  recursion and, in addition, the `ℓ¹` size of `V^{obs}`: `∑_B|m₂(V_j(B)_a)| ≤ 2|β_j|`
  (`A_j ≤ b_j + D_j`, `D_j ≤ 6c_δ∑_{k<j}r_k²b_j ≤ (3/4)b_j`).
* `vobs2_block_le`: `‖V^{obs}_j(B)‖ ≤ s_j²∑_B|m₂(V_j(B)_a)|` (`γ_a = 0`).
* `hist_rawL`, **`wobs_hist_stepL`**: the raw data and one `𝒲^{obs}` step at `j = N_h` (`ValidAtL`):
  the block bound of `𝒲^{obs}_{N_h+1}`.
* **`gamRemG_last_split`**: at `j + 1 = N`, `Q = 0` (`Q2O`), hence
  `ρ = ∑_Bε(𝔼θ𝒲(B))_a + β·ε(F_C(ψ̄_aψ_a, V'(Λ)_∅))` (no `K` term).
* **`eps_EthO_W_le`**: `|∑_Bε(e^{ℒ_C}𝒲^{obs}(B)_a)| ≤ c_BQ₁w` for any `GoodCov2` covariance at
  scale `j < N` (only the blocks near `a` contribute).
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
theorem obs_hist_rel2_baseX {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
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
    ∀ j ≤ n, 0 < ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖ ∧
      shA2 (histVO2 R P (obsInit .two V P) t) j ≤
        2 * ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖ ∧
      WbHc R P (obsInit .two V P) t j ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t j).1) *
        (2 * histS R j t ^ 2 *
          ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖)) ∧
      KbHc R P (obsInit .two V P) t j (16 * (3 * C₁ + 1) * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) *
        (cR R Λ cm C₂ * (t j).1) ^ 2 * (histS R j t ^ 2 *
          ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖)) := by
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
  obtain ⟨hb, hD, hW, hK⟩ := (RR.close n le_rfl).1 j hj
  refine ⟨hb, ?_, hW, hK⟩
  have hA := RR.hA j hj
  have hS := RR.sum_le hj
  simp only at hA hD hb
  have h6 : 6 * (cδ * ∑ k ∈ range j, rr k ^ 2) *
      ‖betaTot2 (L := L) (N := N) j (histVO2 R P o₀ t j)‖ ≤
      6 * (1 / 8) * ‖betaTot2 (L := L) (N := N) j (histVO2 R P o₀ t j)‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hb.le
  linarith

/-- `‖V^{obs}_j(B)‖ ≤ s_j²∑_B|m₂(V_j(B)_a)|` (`γ_a = 0`). -/
theorem vobs2_block_le (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hs : 0 < histS R j t) (b : Fin 2 → ℕ)
    (hb' : b ∈ blockIdx (L := L) (N := N) j) :
    oTo Obs2.wA j (histS R j t) ((obsHist R P (obsInit .two V P) j t).V b) ≤
      ENNReal.ofReal (histS R j t ^ 2 * shA2 (histVO2 R P (obsInit .two V P) t) j) := by
  rw [Obs2.oTo_wA, obsHist2_pure R P t V hga j b]
  refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : ‖mass2 ((obsHist R P (obsInit .two V P) j t).V b : SA .two (Lam 2 L N)).a‖ ≤
      shA2 (histVO2 R P (obsInit .two V P) t) j := by
    rw [← histVO2_a R P (obsInit .two V P) t j b]
    exact single_le_sum (f := fun b => ‖mass2
      (histVO2 R P (obsInit .two V P) t j b : SA .two (Lam 2 L N)).a‖)
      (fun _ _ => norm_nonneg _) hb'
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

theorem hist_rawL (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hVL : ValidAtL R Nh)
    (t : Flow2.Hist.Seq (Xs R))
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t) :
    let st := rawHist R Nh t
    let g := (t Nh).1
    let x := (t Nh).2.2
    let r := cR R Λ cm C₂ * g
    ValidCore R Nh ∧ RawInv R Nh st ∧ 0 ≤ g ∧ g ≤ ε ∧
    ‖st.z / st.Z‖ ≤ cZ R * g ∧ ‖st.y / st.Z‖ ≤ cZ R * g ∧ 2 * (cZ R * g) ≤ R.ρ ∧
    8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 ∧
    Fnorm Nh (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2) ∧
    Fnorm Nh (fscale st.Z * R.ℓ) (rawD R st.u x) ≤ ENNReal.ofReal ‖x.1‖ ∧
    cM * R.ℓ ^ 2 * (2 * |(t Nh).2.1| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r ∧
    cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 ∧ 0 < r ∧ r ≤ cR R Λ cm C₂ * ε ∧
    0 ≤ cW R Λ cm C₂ ∧ 0 < fscale st.Z * R.ℓ ∧ 0 < fscale (stZ' R st) * R.ℓ := by
  intro st g x r
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hVL.2
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 Nh hV t
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 Nh le_rfl
  set μ := (t Nh).2.1
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
  exact ⟨hVj, HI, hg.le, hgε, hz, hy, hη, hηs, hWl, le_of_eq (Fnorm_rawD R HI.hu hZ x),
    hvr, hwr, hr0, hrε, hcw, mul_pos (fscale_pos hZ) hℓ, mul_pos (fscale_pos hZ') hℓ⟩

/-- **One step of `𝒲^{obs}` at `j = N_h`** (`ValidAtL`; copy of `wobs_hist_step`). -/
theorem wobs_hist_stepL {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R))
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      oTo w (Nh + 1) (histS R (Nh + 1) t) ((obsHist R P o₀ (Nh + 1) t).W c') ≤
        ENNReal.ofReal ((Kw / L + C₁ * (cR R Λ cm C₂ * (t Nh).1)) * mW +
          C₁ * (cR R Λ cm C₂ * (t Nh).1) * mV) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_rawL R hSB hV hm hβ hδ1 H hVL t ht
  have hval := hist_validL R hV hVL t
  have hloc := obsLocInv_hist R P o₀ hl0 t Nh fun i hi => hval i hi.le
  have hsym := obsSymInv_hist R P o₀ hs0 t Nh fun i hi => hval i hi.le
  have hobs := obsHist_isObs R P o₀ h0 Nh t
  exact hWB N R Nh hVc (rawHist R Nh t) HI (t Nh).1 (t Nh).2.1 _ _ (rawD_mem R _ _)
    (rawK_mem R _ _) hmN hg _ hz hy hη hηs c P w hw0 (obsHist R P o₀ Nh t) hobs hloc hsym _ _ _
    mV mW (by positivity) (norm_nonneg _) hr0.le (hrε.trans hε₁) hmV hmW hWl hDd hvr hwr hVo hWo

end Main

/-! ### The last step: the split of `ρ` and the `𝒲` term -/

section Last

variable {d : ℕ}

/-- At `j + 1 = N` there is no `Q`. -/
theorem Q2O_last {c : Obs.Case} (P : ObsPts d L N) {j : ℕ} (hj : j + 1 = N) (K : OAct c d L N)
    (b : Fin d → ℕ) : Q2O P j K b = 0 := by
  unfold Q2O; rw [if_neg (by omega)]

/-- **The `γ` remainder of the last step** (`j + 1 = N`): no activity term,
`ρ = ∑_Bε(𝔼θ𝒲(B))_a + β·ε(F_C(ψ̄_aψ_a, V'(Λ)_∅))`. -/
theorem gamRemG_last_split (P : ObsPts d L N) {j : ℕ} (hj : j + 1 = N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam .two d L N) (K : OAct .two d L N)
    (hV : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    gamRemG P j C V W K =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (EthO C (W b) : SA .two (Lam d L N)).a +
        betaTot2 j V * ε (FC C (pbp P.a) (VprLO j C V : SA .two (Lam d L N)).e) := by
  unfold gamRemG
  rw [sum_add_distrib, eps_total_LS, eps_SbO_sum, eps_FC_VprLO P j C V hV]
  have h0 : ∑ b ∈ blockIdx (L := L) (N := N) j,
      ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).a) = 0 := by
    refine sum_eq_zero fun b _ => ?_
    rw [Q2O_last P hj K b]
    simp
  rw [h0]
  ring

end Last

section LastW

/-- **The `𝒲` term of a step** at any scale `j < N` with a `GoodCov2` covariance at the field
scale `s`: only the `c_B` blocks near `a` contribute, `|∑_Bε(e^{ℒ_C}𝒲^{obs}(B)_a)| ≤ c_BQ₁w`. -/
theorem eps_EthO_W_le (P : ObsPts 2 L N) {j : ℕ} (hj : j < N) (hLp : pauliL0 2 ≤ L) {s : ℝ}
    (hs : 0 < s) {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 j s C)
    (o : ObsSt .two L N) (ho : ObsLocInv P j o) (st : RawSt 2 L N) (D : Fam 2 L N) {w : ℝ}
    (hw : 0 ≤ w)
    (hW : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j s (o.W b) ≤ ENNReal.ofReal w) :
    ‖∑ b ∈ blockIdx (L := L) (N := N) j,
        ε (EthO C (fullW st D o b) : SA .two (Lam 2 L N)).a‖ ≤ cBn * (Q1 2 * w) := by
  classical
  have e : ∀ b, ε (EthO C (fullW st D o b) : SA .two (Lam 2 L N)).a =
      ε (expLC C (o.W b : SA .two (Lam 2 L N)).a) := by
    intro b
    rw [EthO_a_eq]
    congr 2
    exact emb_add_cmp true _ _
  simp only [e]
  refine (norm_sum_le _ _).trans ?_
  set S := blockIdx (L := L) (N := N) j
  set S' := S.filter (fun b => P.a ∈ nbhd j (blockSet (L := L) (N := N) j b))
  have hsplit : ∑ b ∈ S, ‖ε (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖ =
      ∑ b ∈ S', ‖ε (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖ := by
    refine (sum_subset (filter_subset _ _) fun b hb hb' => ?_).symm
    have hna : P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) := fun h =>
      hb' (mem_filter.2 ⟨hb, h⟩)
    rw [((ho.W b).2.2.2.2.1 hna).1, map_zero, map_zero, norm_zero]
  rw [hsplit]
  have hQ : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
  have hterm : ∀ b ∈ S', ‖ε (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖ ≤ Q1 2 * w := by
    intro b hb
    have hbS := (mem_filter.1 hb).1
    refine (norm_eps_expLC_le (by norm_num) hLp hj hs hC (ho.W b).2.1).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hQ
    have h := hW b hbS
    rw [Obs2.oTo_wA] at h
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal hw] at h2
  have hc : (S'.card : ℝ) ≤ cBn := by
    exact_mod_cast Classical.choose_spec (Obs2.card_blocks_near 2) L N j P.a S subset_rfl
  calc ∑ b ∈ S', ‖ε (expLC C (o.W b : SA .two (Lam 2 L N)).a)‖
      ≤ ∑ _b ∈ S', Q1 2 * w := sum_le_sum hterm
    _ = S'.card * (Q1 2 * w) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ cBn * (Q1 2 * w) := mul_le_mul_of_nonneg_right hc (mul_nonneg hQ hw)

end LastW

end

end PtCorr2
