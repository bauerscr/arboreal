import PtCorr2.Restart.Restart2Thm

set_option autoImplicit false

/-!
# B3, T6 (a) wiring: the share sum along the restart with large transients

`obs_hist_restartT`/`PT`/`BT` (`PtCorr2/Restart/Restart2Hist`, `Restart2Thm`) export only the `β` bound
and the `𝒲`/`K` envelopes. The restart recursion (`Obs2.RelRecT.close`) also bounds the share
deviation `D_j`; this gives the `ℓ¹` share sum `shA2F_{m+j} ≤ |β| + D ≤ 2M_j`
(`Obs2.RelRecT.cw2_A_le`), and the transient ratio `s_m²M₀ ≤ (7/5)^j s_{m+j}²M_j` (`sM_le'`).

* **`cw2_obs_hist_restartT`**, **`cw2_obs_hist_restartPT`**, **`cw2_obs_hist_restartBT`**: the
  hypotheses of the originals (copies), conclusion for `j ≤ n − m`:
  `shA2 (histVF2 R P m o' t) (m+j) ≤ 2·rkEnv M₀ a j` and
  `s_m²M₀ ≤ (7/5)^j·s_{m+j}²·rkEnv M₀ a j`, `0 < rkEnv M₀ a j`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset

namespace RelRecT

variable {n : ℕ} {b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ} {T : ℕ → ℕ → ℝ}
  {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp : ℝ}

/-- **The share sum along the restart**: `A_j ≤ b_j + D_j ≤ 2M_j`. -/
theorem cw2_A_le (H : RelRecT n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ
    q rb cδ M₀ k₀ xh tn w₀ κb xp) {j : ℕ} (hj : j ≤ n) : A j ≤ 2 * rkEnv M₀ a j := by
  obtain ⟨hbj, hDj, -, -⟩ := (H.close j hj).1 j le_rfl
  have hM := H.hM0
  have hct0 := H.ct_nonneg
  have hctb := H.hct
  have hS := H.sum_le hj
  have hT := rk_geom_rho j
  have henv := H.env_pos hj
  have hA := H.hA j hj
  have hbD := H.hbD0
  set ct := cK * k₀ / (s 0 * M₀) + xh + tn + xp
  set Gs := ∑ k ∈ range j, (3 / 4 : ℝ) ^ k
  set Sm := cδ * ∑ k ∈ range j, r k ^ 2
  have hG0 : 0 ≤ Gs := sum_nonneg fun _ _ => by positivity
  have hS0 : 0 ≤ Sm := mul_nonneg H.hcδ0 (sum_nonneg fun _ _ => sq_nonneg _)
  have h1 : b 0 / M₀ + D 0 / M₀ ≤ 1 := by rw [← add_div, div_le_one hM]; exact hbD
  have hctG : ct * Gs ≤ 1 / 48 * 4 := mul_le_mul hctb hT hG0 (by norm_num)
  have hsum : (b 0 / M₀ + Sm + 7 / 3 * ct * Gs) + (D 0 / M₀ + 2 * Sm + 14 / 3 * ct * Gs) ≤ 2 := by
    nlinarith
  calc A j ≤ b j + D j := hA
    _ ≤ (b 0 / M₀ + Sm + 7 / 3 * ct * Gs) * rkEnv M₀ a j +
        (D 0 / M₀ + 2 * Sm + 14 / 3 * ct * Gs) * rkEnv M₀ a j := add_le_add hbj hDj
    _ = ((b 0 / M₀ + Sm + 7 / 3 * ct * Gs) + (D 0 / M₀ + 2 * Sm + 14 / 3 * ct * Gs)) *
        rkEnv M₀ a j := by ring
    _ ≤ 2 * rkEnv M₀ a j := mul_le_mul_of_nonneg_right hsum henv.le

end RelRecT

end

end Obs2

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Main

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- `obs_hist_restartT` (copy), conclusion: the share sum `shA2F_{m+j} ≤ 2M_j` and the transient
ratio `s_m²M₀ ≤ (7/5)^j s_{m+j}²M_j`, `M_j > 0`. -/
theorem cw2_obs_hist_restartT {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (hn : n ≤ Nh) (hnN : n < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    -- the datum
    {m : ℕ} (hmn : m ≤ n) (o' : ObsSt .two L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o')
    (hs0 : ObsSymInv m o') (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a)
    -- the constants of the `K` step
    (ck : ℝ) (hck : 60 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) ≤ ck)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    {κb : ℝ} (hκb : 0 < κb) (h64 : 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) ≤ κb)
    (hκC : C₁k * κb ≤ 1 / 45)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hκε : (ε₀ + κb) * (cR R Λ cm C₂ * ε) ^ 2 ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (hβp : 0 < β) (hδ2 : δ ≤ 1 / 2) (hcgε : cg * ε ≤ β / 4)
    {cgb cP cδ Bτ qq : ℝ} (hcg : 0 ≤ cgb) (hcP : 0 ≤ cP) (hcδ0 : 0 ≤ cδ) (hBτ : 0 ≤ Bτ)
    (hqq0 : 0 ≤ qq) (hqq4 : qq ≤ 1 / 4)
    (hcg1 : 1 ≤ cgb * cR R Λ cm C₂)
    (hcδ : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁ + 1) * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) +
        3 * cP * (3 * C₁ + 1) + 4 * Bτ * cgb * (1 + cgb) +
        4 * Bτ * cgb * cδ * (cR R Λ cm C₂ * ε) ≤ 6 / 7 * cδ)
    (hτ : 2 * Bτ * cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 2)
    (hsumε : cδ * (cR R Λ cm C₂ ^ 2 * (ε / (β / 4))) ≤ 1 / 8)
    -- the envelope and the transient
    {M₀ k₀ xh tn w₀ xp : ℝ} (hM0 : 0 < M₀) (hk₀ : 0 ≤ k₀) (hxh : 0 ≤ xh) (htn : 0 ≤ tn)
    (hw₀ : 0 ≤ w₀)
    (hkw : 120 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) * w₀ ≤ k₀)
    (hxp : 5 * cP * (cR R Λ cm C₂ * ε) * w₀ / (histS R m t ^ 2 * M₀) ≤ xp)
    (hct : 8 * (csN 2 : ℝ) * k₀ / (histS R m t ^ 2 * M₀) + xh + tn + xp ≤ 1 / 48)
    (hbD0 : ‖betaTot2 (L := L) (N := N) m (histVF2 R P m o' t m)‖ +
      shareDev2 P.a m (histVF2 R P m o' t m) ≤ M₀)
    (hW0 : WbHF R P m o' t m ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀) +
      w₀))
    (hK0 : KbHF R P m o' t m k₀)
    -- the bulk inputs
    (hT : ∀ k j, m ≤ k → k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVF2 R P m o' t) k j‖ ≤ Bτ * qq ^ (j - k) * (t k).1)
    (hnn : ∀ i, m ≤ i → i < n → ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i‖ ≤
      cgb * (cR R Λ cm C₂ * (t i).1) + tn * (1 / 2) ^ (i - m))
    (hn7 : ∀ i, m ≤ i → i < n → ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i‖ ≤ 1 / 7)
    -- the product parts and the initial tadpoles
    (hPr : ProdBd2F R P m o' t n (fun i => cR R Λ cm C₂ * (t (m + i)).1) cP qq)
    (hX : InitBd2F R P m o' t n xh M₀) :
    let a := fun i => ‖1 - frakN2F P (histCovO R t) (histVF2 R P m o' t) m (m + i)‖
    ∀ j ≤ n - m, shA2 (histVF2 R P m o' t) (m + j) ≤ 2 * rkEnv M₀ a j ∧
      histS R m t ^ 2 * M₀ ≤ (7 / 5) ^ j * (histS R (m + j) t ^ 2 * rkEnv M₀ a j) ∧
      0 < rkEnv M₀ a j := by
  intro a
  set B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
  set rr : ℕ → ℝ := fun i => cR R Λ cm C₂ * (t (m + i)).1 with hrr
  set cWo := 3 * C₁ + 1
  set n' := n - m with hn'
  have HC := muChain2F_histFrom R P m o' t hmn hnN hf0
  have hβ' : 0 < β / 4 := by linarith
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
  have hck0 : 0 ≤ ck := le_trans (by positivity) hck
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hC1 : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + ck) := by positivity
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hr0 : ∀ j ≤ n', 0 ≤ rr j := fun j hj => mul_nonneg hcR (ht.1 (m + j) (by omega)).1.le
  have hrε : ∀ j ≤ n', rr j ≤ cR R Λ cm C₂ * ε := fun j hj =>
    mul_le_mul_of_nonneg_left (ht.1 (m + j) (by omega)).2.1 hcR
  have hsj : ∀ j, 0 < histS R j t := histS_pos' R hρ0 hρ t
  -- the block bound of `V^{obs}_j` from the `ℓ¹` size
  have hVo : ∀ j, m ≤ j → ∀ mm, histS R j t ^ 2 * shA2 (histVF2 R P m o' t) j ≤ mm →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHistFrom R P m o' j t).V b) ≤ ENNReal.ofReal mm := by
    intro j hmj mm hsm' b hb'
    have hs := hsj j
    rw [Obs2.oTo_wA, obsHistF2_pure R P m o' t hf0 hp0 j hmj b]
    refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hsm'))
    have h1 : ‖mass2 ((obsHistFrom R P m o' j t).V b : SA .two (Lam 2 L N)).a‖ ≤
        shA2 (histVF2 R P m o' t) j := by
      rw [← histVF2_a R P m o' t j b]
      exact single_le_sum (f := fun b => ‖mass2
        (histVF2 R P m o' t j b : SA .two (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
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
  let G : ℕ → ℝ := fun i => (t (m + i)).1
  have hG : ∀ i < n', 0 ≤ G i := fun i hi => (ht.1 (m + i) (by omega)).1.le
  have hTt : ∀ k j, k < j → j < n' → ∀ i ∈ Ico k j,
      ‖tadInc2 P (histCovO R t) (histVF2 R P m o' t) (m + k) (m + j)‖ ≤ Tt k j * G i := by
    intro k j hkj hj i hi
    have hi' := mem_Ico.1 hi
    refine (hT (m + k) (m + j) (by omega) (by omega) (by omega)).trans ?_
    rw [show m + j - (m + k) = j - k by omega]
    exact mul_le_mul_of_nonneg_left (hgmono (m + k) (m + i) (by omega) (by omega))
      (mul_nonneg hBτ (pow_nonneg hqq0 _))
  have hε₀0 : 0 ≤ ε₀ := le_trans (mul_nonneg hcR (by have := (ht.1 0 (Nat.zero_le _)).1; have := (ht.1 0 (Nat.zero_le _)).2.1; linarith)) hεε
  have I : RelInT n' (fun i => ‖betaTot2 (L := L) (N := N) (m + i) (histVF2 R P m o' t (m + i))‖)
      (fun i => shA2 (histVF2 R P m o' t) (m + i))
      (fun i => shareDev2 P.a (m + i) (histVF2 R P m o' t (m + i)))
      (fun i => shareErrL1_2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t)
        (histKF2 R P m o' t) m (m + i))
      a (fun i => histS R (m + i) t ^ 2) rr (fun i => shKt2 (histKF2 R P m o' t) (m + i))
      (fun i => if i = 0 then 0 else
        shPr2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m (m + i))
      (fun i => shInit2 (histCovO R t) (histWF2 R P m o' t) m (m + i) + if i = 0 then
        shPr2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m m else 0)
      G (fun i => ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m (m + i)‖)
      (fun j => Kw / L + C₁ * rr j)
      (fun j => kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * rr j + C₁k * κb)
      Tt (fun i x => WbHF R P m o' t (m + i) x) (fun i x => KbHF R P m o' t (m + i) x)
      C₁ cWo B ck (8 * (csN 2 : ℝ)) cP cgb Bτ qq (cR R Λ cm C₂ * ε) cδ M₀ k₀ xh tn w₀ κb xp := {
    hC₁ := hC₁
    hcW1 := by show (1 : ℝ) ≤ 3 * C₁ + 1; linarith
    hcWC := by show 3 * C₁ ≤ 3 * C₁ + 1; linarith
    hBk := hB
    hck := hck
    hcK := by positivity
    hcP := hcP
    hcg := hcg
    hBτ := hBτ
    hq0 := hqq0
    hq := hqq4
    hcδ0 := hcδ0
    hcδ := hcδ
    hτ := hτ
    hsum := by
      have h1 := Step2.sum_sq_le hβ' n hinc
      have h2 : ∑ k ∈ range n', rr k ^ 2 ≤ cR R Λ cm C₂ ^ 2 * ∑ k ∈ range n, (t k).1 ^ 2 := by
        have e : ∑ k ∈ range n', rr k ^ 2 =
            cR R Λ cm C₂ ^ 2 * ∑ k ∈ Ico m n, (t k).1 ^ 2 := by
          rw [sum_Ico_eq_sum_range, mul_sum]
          exact sum_congr rfl fun k _ => by rw [hrr]; ring
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.2 (mem_Ico.1 hk).2)
          fun _ _ _ => sq_nonneg _
      have h3 : ((t n).1 - (t 0).1) / (β / 4) ≤ ε / (β / 4) := by
        have := (ht.1 n le_rfl).2.1; have := (ht.1 0 (Nat.zero_le _)).1
        exact div_le_div_of_nonneg_right (by linarith) hβ'.le
      have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg (cR R Λ cm C₂))
      have h5 := mul_le_mul_of_nonneg_left (h2.trans h4) hcδ0
      linarith
    hr0 := hr0
    hrb := hrε
    hrm := fun j hj => mul_le_mul_of_nonneg_left (hgm (m + j) (by omega)) hcR
    hs := fun j _ => pow_pos (hsj (m + j)) 2
    hss := by
      intro j hj
      have e : histS R (m + j + 1) t = histS R (m + j) t * fscale (1 + zetaH R (m + j) t) := by
        unfold histS
        rw [rawHist_succ_Z, fscale_mul]; ring
      have hz : ‖zetaH R (m + j) t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
      have h1 := fscale_one_add_ge hz
      have h2 := hsj (m + j)
      have h3 : histS R (m + j) t ≤ 15 / 14 * histS R (m + j + 1) t := by rw [e]; nlinarith
      have h4 : 0 ≤ histS R (m + j + 1) t := by rw [e]; nlinarith
      show histS R (m + j) t ^ 2 ≤ 6 / 5 * histS R (m + (j + 1)) t ^ 2
      rw [← add_assoc]
      nlinarith
    ha := by
      intro j hj
      have h1 := hn7 (m + j) (by omega) (by omega)
      have h2 := norm_sub_norm_le (1 : ℂ) (frakN2F P (histCovO R t) (histVF2 R P m o' t) m (m + j))
      have h3 := norm_sub_le (1 : ℂ) (frakN2F P (histCovO R t) (histVF2 R P m o' t) m (m + j))
      rw [norm_one] at h2 h3
      constructor <;> linarith
    hM0 := hM0
    hk₀ := hk₀
    hxh := hxh
    htn := htn
    hw₀ := hw₀
    hκb := hκb
    h64 := h64
    hr0p := by
      show 0 < cR R Λ cm C₂ * (t (m + 0)).1
      have hcz : 0 ≤ cZ R := by unfold cZ; positivity
      have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
      have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
      have hc1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
      exact mul_pos (by linarith) (ht.1 (m + 0) (by omega)).1
    hkw := hkw
    hxp := by simpa only [add_zero] using hxp
    hct := by simpa only [add_zero] using hct
    hbD0 := by simpa only [add_zero] using hbD0
    hWm := fun j x y hx hxy b hb' => (hx b hb').trans (ENNReal.ofReal_le_ofReal hxy)
    hKm := fun j x y hx hxy X hX => (hx X hX).trans (ENNReal.ofReal_le_ofReal hxy)
    hW0 := by
      rw [show rr 0 = cR R Λ cm C₂ * (t m).1 by simp [hrr]]; simpa only [add_zero] using hW0
    hK0 := by simpa only [add_zero] using hK0
    hθW := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC₁
      show Kw / L + C₁ * rr j ≤ 1 / 6
      linarith
    hθK := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC1
      show kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * rr j + C₁k * κb ≤ 1 / 20
      linarith
    hW := fun j hj mm w hm0 hw0' hsA hWj => by
      have h := wobs_hist_stepF R hWB hSB hV hm hβ hδ1 H P Obs2.wA hw0 o' h0 hl0 hs0 t (m + j)
        (by omega) (by omega) (hDh (m + j) (by omega)) hε₁ mm w hm0 hw0'
        (hVo (m + j) (by omega) mm hsA) hWj
      intro c' hc'
      refine (h c' hc').trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      show (Kw / L + C₁ * (cR R Λ cm C₂ * (t (m + j)).1)) * w +
        C₁ * (cR R Λ cm C₂ * (t (m + j)).1) * mm = (Kw / L + C₁ * rr j) * w + C₁ * rr j * mm
      rfl
    hK := fun j hj mm k cc hm0 hk0 hcc0 hccr hsA hWj hKj hk8 => by
      have hWj' : ∀ b ∈ blockIdx (L := L) (N := N) (m + j),
          oTo Obs2.wA (m + j) (histS R (m + j) t) ((obsHistFrom R P m o' (m + j) t).W b) ≤
            ENNReal.ofReal (cR R Λ cm C₂ * (t (m + j)).1 * mm) := hWj
      have hr := hr0 j (by omega)
      have hrE := hrε j (by omega)
      have hrr : rr j = cR R Λ cm C₂ * (t (m + j)).1 := rfl
      -- the per-step smallness from `c r_j ≤ c_k r_j + κ̄`
      have hεk3 : (8 * cx κ cT + cc) * (cR R Λ cm C₂ * (t (m + j)).1) ^ 3 ≤ ε₀ := by
        rw [← hrr]
        have a1 : (8 * cx κ cT + ck) * rr j ≤ ε₀ :=
          (mul_le_mul_of_nonneg_left hrE (by positivity)).trans hεk
        have a2 : (8 * cx κ cT + cc) * rr j ^ 3 =
            ((8 * cx κ cT + ck) * rr j) * rr j ^ 2 + (cc * rr j - ck * rr j) * rr j ^ 2 := by ring
        have a3 : ((8 * cx κ cT + ck) * rr j) * rr j ^ 2 ≤ ε₀ * rr j ^ 2 :=
          mul_le_mul_of_nonneg_right a1 (sq_nonneg _)
        have a4 : (cc * rr j - ck * rr j) * rr j ^ 2 ≤ κb * rr j ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        have a5 : (ε₀ + κb) * rr j ^ 2 ≤ (ε₀ + κb) * (cR R Λ cm C₂ * ε) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrE 2) (by linarith)
        linarith
      have h := kobs_hist_stepF2 R hKB hSB hV hm hβ hδ1 H P Obs2.wA hw0 hwa hwb o' h0 hl0 hs0 t
        (m + j) (by omega) (by omega) (hDh (m + j) (by omega)) cc mm k hcc0 hm0 hk0 hε1 hεε hεk3
        hk8 (hVo (m + j) (by omega) mm hsA) hWj' hKj
      intro U hU
      refine (h U hU).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hrr]
      have hcoef : kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + cc) * rr j ≤
          kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + ck) * rr j + C₁k * κb := by
        have : C₁k * (cc * rr j) ≤ C₁k * (ck * rr j + κb) := mul_le_mul_of_nonneg_left hccr hC₁k
        nlinarith
      have := mul_le_mul_of_nonneg_right hcoef (by positivity : (0 : ℝ) ≤ 8 * k)
      linarith
    hKt := fun j hj k hk0 hKj => by
      have h := kobs_EK2F R hSB hV hm hβ hδ1 H P o' hl0 t (m + j) (by omega) (by omega)
        (hDh (m + j) (by omega)) Obs2.wA hw0 1 one_pos (by simp [Obs2.wA]) k hk0 hKj
      refine h.trans (le_of_eq ?_)
      rw [div_one, inv_pow]; ring
    hPr := fun j hj mm hmm => by
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [if_true]
        refine mul_nonneg hcP (sum_nonneg fun i hi => ?_)
        have hi0 : i = 0 := by have := mem_range.1 hi; omega
        subst hi0
        have := (hmm 0 le_rfl).1
        have := hsj (m + 0)
        positivity
      · rw [if_neg (by omega)]
        exact hPr j hj0 hj mm hmm
    hX := fun i hi => hX i hi
    hT := fun k j _ _ => ⟨mul_nonneg hBτ (pow_nonneg hqq0 _), le_rfl⟩
    hG := fun i hi => ⟨hG i hi, by
      show (t (m + i)).1 ≤ cgb * (cR R Λ cm C₂ * (t (m + i)).1)
      rw [← mul_assoc]
      have := (ht.1 (m + i) (by omega)).1.le
      nlinarith⟩
    hnn := fun i hi => ⟨norm_nonneg _, by
      have h := hnn (m + i) (by omega) (by omega)
      rwa [Nat.add_sub_cancel_left] at h⟩ }
  have HR := HC.relRecT2 Tt hG hTt I
  intro j hj
  exact ⟨by simpa only [add_zero] using HR.cw2_A_le hj, by simpa only [add_zero] using HR.sM_le' hj,
    HR.env_pos hj⟩

set_option maxHeartbeats 1000000 in
/-- `obs_hist_restartPT` (copy) with the conclusion of `cw2_obs_hist_restartT`. -/
theorem cw2_obs_hist_restartPT {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (hn : n ≤ Nh) (hnN : n < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    -- the datum
    {m : ℕ} (hmn : m ≤ n) (o' : ObsSt .two L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o')
    (hs0 : ObsSymInv m o') (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a)
    -- the constants of the `K` step
    (ck : ℝ) (hck : 60 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) ≤ ck)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    {κb : ℝ} (hκb : 0 < κb) (h64 : 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) ≤ κb)
    (hκC : C₁k * κb ≤ 1 / 45)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hκε : (ε₀ + κb) * (cR R Λ cm C₂ * ε) ^ 2 ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (hβp : 0 < β) (hδ2 : δ ≤ 1 / 2) (hcgε : cg * ε ≤ β / 4)
    {cgb cP cδ Bτ qq : ℝ} (hcg : 0 ≤ cgb) (hcP : 0 ≤ cP) (hcδ0 : 0 ≤ cδ) (hBτ : 0 ≤ Bτ)
    (hqq0 : 0 ≤ qq) (hqq4 : qq ≤ 1 / 4)
    (hcg1 : 1 ≤ cgb * cR R Λ cm C₂)
    (hcδ : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁ + 1) * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) +
        3 * cP * (3 * C₁ + 1) + 4 * Bτ * cgb * (1 + cgb) +
        4 * Bτ * cgb * cδ * (cR R Λ cm C₂ * ε) ≤ 6 / 7 * cδ)
    (hτ : 2 * Bτ * cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 2)
    (hsumε : cδ * (cR R Λ cm C₂ ^ 2 * (ε / (β / 4))) ≤ 1 / 8)
    -- the envelope and the transient
    {M₀ k₀ xh tn w₀ xp : ℝ} (hM0 : 0 < M₀) (hk₀ : 0 ≤ k₀) (htn : 0 ≤ tn) (hw₀ : 0 ≤ w₀)
    (hkw : 120 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) * w₀ ≤ k₀)
    (hxp : 5 * cP * (cR R Λ cm C₂ * ε) * w₀ / (histS R m t ^ 2 * M₀) ≤ xp)
    (hct : 8 * (csN 2 : ℝ) * k₀ / (histS R m t ^ 2 * M₀) + xh + tn + xp ≤ 1 / 48)
    (hxhv : xh = cbnC * (1280 * locK 2 ^ 2 * (8 / (7 * L)) + 1) *
      ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀) + w₀) /
        (histS R m t ^ 2 * M₀))
    (hbD0 : ‖betaTot2 (L := L) (N := N) m (histVF2 R P m o' t m)‖ +
      shareDev2 P.a m (histVF2 R P m o' t m) ≤ M₀)
    (hW0 : WbHF R P m o' t m ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀) +
      w₀))
    (hK0 : KbHF R P m o' t m k₀)
    -- the bulk inputs
    (hT : ∀ k j, m ≤ k → k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVF2 R P m o' t) k j‖ ≤ Bτ * qq ^ (j - k) * (t k).1)
    (hnn : ∀ i, m ≤ i → i < n → ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i‖ ≤
      cgb * (cR R Λ cm C₂ * (t i).1) + tn * (1 / 2) ^ (i - m))
    (hn7 : ∀ i, m ≤ i → i < n → ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i‖ ≤ 1 / 7)
    -- the product parts and the initial tadpoles
    {Cp εp : ℝ} (hPB : PObsBounds L Cp εp) (hCp : 0 ≤ Cp) (hεp : cR R Λ cm C₂ * ε ≤ εp)
    (hL : prodLb ≤ L) (hVL : ValidAtL R n) (hm1 : 0 < m) (hcPv : cP = prodCP2 L Cp)
    (hqv : qq = 2 / L) :
    let a := fun i => ‖1 - frakN2F P (histCovO R t) (histVF2 R P m o' t) m (m + i)‖
    ∀ j ≤ n - m, shA2 (histVF2 R P m o' t) (m + j) ≤ 2 * rkEnv M₀ a j ∧
      histS R m t ^ 2 * M₀ ≤ (7 / 5) ^ j * (histS R (m + j) t ^ 2 * rkEnv M₀ a j) ∧
      0 < rkEnv M₀ a j := by
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hs := histS_pos' R hρ0 hρ t m
  have hw₀' : 0 ≤ (3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀) + w₀ := by
    have := (ht.1 m hmn).1.le; positivity
  have hxh : 0 ≤ xh := by
    rw [hxhv]; have := one_le_locK 2; have : (0 : ℝ) ≤ cbnC := Nat.cast_nonneg _; positivity
  have hPr := prodBd2F_hist R hPB hCp hSB hV hm hβ hδ1 H hρ0 hρ P o' h0 hl0 hs0 hf0 hp0 t n hmn hn
    hnN hVL ht hεp hL
  have hX := initBd2F_hist R hρ0 hρ P hm1 o' hl0 t n hnN (fun i hi => hV i (by omega)) hVL hL hw₀'
    hM0 hW0
  rw [← hxhv] at hX
  subst hcPv hqv
  exact cw2_obs_hist_restartT R hKB hC₁k hWB hC₁ hSB hV hm hβ hδ1 H hρ0 hρ P t n hn hnN ht hmn o' h0 hl0
    hs0 hf0 hp0 ck hck hθ0 hθ hsm hκb h64 hκC hε1 hεε hεk hκε hLw hC₁ε hε₁ hβp hδ2 hcgε hcg hcP hcδ0 hBτ hqq0 hqq4
    hcg1 hcδ hτ hsumε hM0 hk₀ hxh htn hw₀ hkw hxp hct hbD0 hW0 hK0 hT hnn hn7 hPr hX


/-- `obs_hist_restartBT` (copy) with the conclusion of `cw2_obs_hist_restartT`. -/
theorem cw2_obs_hist_restartBT {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (hn : n ≤ Nh) (hnN : n < N)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    -- the datum
    {m : ℕ} (hmn : m ≤ n) (o' : ObsSt .two L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o')
    (hs0 : ObsSymInv m o') (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a)
    -- the constants of the `K` step
    (ck : ℝ) (hck : 60 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) ≤ ck)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + ck) * (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    {κb : ℝ} (hκb : 0 < κb) (h64 : 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) ≤ κb)
    (hκC : C₁k * κb ≤ 1 / 45)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hκε : (ε₀ + κb) * (cR R Λ cm C₂ * ε) ^ 2 ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (hβp : 0 < β) (hδ2 : δ ≤ 1 / 2) (hcgε : cg * ε ≤ β / 4)
    {cgb cP cδ Bτ qq : ℝ} (hcg : 0 ≤ cgb) (hcP : 0 ≤ cP) (hcδ0 : 0 ≤ cδ) (hBτ : 0 ≤ Bτ)
    (hqq0 : 0 ≤ qq) (hqq4 : qq ≤ 1 / 4)
    (hcg1 : 1 ≤ cgb * cR R Λ cm C₂)
    (hcδ : 16 * (8 * (csN 2 : ℝ)) * (3 * C₁ + 1) * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) +
        3 * cP * (3 * C₁ + 1) + 4 * Bτ * cgb * (1 + cgb) +
        4 * Bτ * cgb * cδ * (cR R Λ cm C₂ * ε) ≤ 6 / 7 * cδ)
    (hτ : 2 * Bτ * cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 2)
    (hsumε : cδ * (cR R Λ cm C₂ ^ 2 * (ε / (β / 4))) ≤ 1 / 8)
    -- the envelope and the transient
    {M₀ k₀ xh w₀ xp : ℝ} (hM0 : 0 < M₀) (hk₀ : 0 ≤ k₀) (hw₀ : 0 ≤ w₀)
    (hkw : 120 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * ε) * w₀ ≤ k₀)
    (hxp : 5 * cP * (cR R Λ cm C₂ * ε) * w₀ / (histS R m t ^ 2 * M₀) ≤ xp)
    (hct : 8 * (csN 2 : ℝ) * k₀ / (histS R m t ^ 2 * M₀) + xh + 4 / 3 * qq + xp ≤ 1 / 48)
    (hxhv : xh = cbnC * (1280 * locK 2 ^ 2 * (8 / (7 * L)) + 1) *
      ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀) + w₀) /
        (histS R m t ^ 2 * M₀))
    (hbD0 : ‖betaTot2 (L := L) (N := N) m (histVF2 R P m o' t m)‖ +
      shareDev2 P.a m (histVF2 R P m o' t m) ≤ M₀)
    (hW0 : WbHF R P m o' t m ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀) +
      w₀))
    (hK0 : KbHF R P m o' t m k₀)
    -- the bulk inputs, for any observable history from scale `0` at the same point
    (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs)
    (hT : ∀ k j, k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k j‖ ≤ Bτ * qq ^ (j - k) * (t k).1)
    (hBg : ∀ k < n, Bτ * (t k).1 ≤ 1)
    (hnn : ∀ i < n, ‖frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖ ≤
      cgb * (cR R Λ cm C₂ * (t i).1))
    (hn8 : ∀ i < n, ‖frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖ ≤ 1 / 8)
    (hq56 : 4 / 3 * qq ≤ 1 / 56)
    -- the product parts and the initial tadpoles
    {Cp εp : ℝ} (hPB : PObsBounds L Cp εp) (hCp : 0 ≤ Cp) (hεp : cR R Λ cm C₂ * ε ≤ εp)
    (hL : prodLb ≤ L) (hVL : ValidAtL R n) (hm1 : 0 < m) (hcPv : cP = prodCP2 L Cp)
    (hqv : qq = 2 / L) :
    let a := fun i => ‖1 - frakN2F P (histCovO R t) (histVF2 R P m o' t) m (m + i)‖
    ∀ j ≤ n - m, shA2 (histVF2 R P m o' t) (m + j) ≤ 2 * rkEnv M₀ a j ∧
      histS R m t ^ 2 * M₀ ≤ (7 / 5) ^ j * (histS R (m + j) t ^ 2 * rkEnv M₀ a j) ∧
      0 < rkEnv M₀ a j := by
  have hgm : ∀ k < n, (t k).1 ≤ (t (k + 1)).1 := fun k hk => restart_gmono hβ hδ2 hcgε H ht k hk
  have hT' : ∀ k j, m ≤ k → k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVF2 R P m o' t) k j‖ ≤ Bτ * qq ^ (j - k) * (t k).1 :=
    fun k j _ hkj hjn => by
      rw [tadInc2_histVF2_eq R P m o' t h0 o₀ ho₀]; exact hT k j hkj hjn
  have hmem := fun (i : ℕ) (hmi : m ≤ i) (hin : i < n) =>
    frakN2F_mem_le R P m o' t h0 o₀ ho₀ hqq0 hqq4 hT hBg hmi hin
  have hnn' : ∀ i, m ≤ i → i < n → ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i‖ ≤
      cgb * (cR R Λ cm C₂ * (t i).1) + 4 / 3 * qq * (1 / 2) ^ (i - m) := fun i hmi hin =>
    (hmem i hmi hin).trans (by have := hnn i hin; linarith)
  have hn7 : ∀ i, m ≤ i → i < n → ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i‖ ≤ 1 / 7 :=
    fun i hmi hin => by
      have h1 := hmem i hmi hin
      have h2 := hn8 i hin
      have h3 : (1 / 2 : ℝ) ^ (i - m) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h4 : 4 / 3 * qq * (1 / 2) ^ (i - m) ≤ 4 / 3 * qq :=
        mul_le_of_le_one_right (by positivity) h3
      linarith
  exact cw2_obs_hist_restartPT R hKB hC₁k hWB hC₁ hSB hV hm hβ hδ1 H hρ0 hρ P t n hn hnN ht hmn o' h0
    hl0 hs0 hf0 hp0 ck hck hθ0 hθ hsm hκb h64 hκC hε1 hεε hεk hκε hLw hC₁ε hε₁ hβp hδ2 hcgε hcg hcP hcδ0 hBτ hqq0
    hqq4 hcg1 hcδ hτ hsumε hM0 hk₀ (by positivity) hw₀ hkw hxp hct hxhv hbD0 hW0 hK0 hT' hnn' hn7 hPB hCp hεp
    hL hVL hm1 hcPv hqv


end Main

end

end PtCorr2
