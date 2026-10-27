import PtCorr2.Restart.Restart2Hist
import PtCorr2.Restart.RestartThm
import PtCorr2.Restart.RestartBulk

/-!
# The restart theorem with large transients, without named inputs (B3, T4′)

* **`obs_hist_restartPT`**: `obs_hist_restartT` with `ProdBd2F` (`prodBd2F_hist`) and `InitBd2F`
  (`initBd2F_hist` with the `𝒲` datum `c_W r_m·2s_m²M₀ + w₀`) discharged,
  `x_h = c_bn(1280K²·8/(7L) + 1)(c_W r_m·2s_m²M₀ + w₀)/(s_m²M₀)`.
* **`obs_hist_restartBT`**: the bulk inputs from the standard history (as `obs_hist_restartB`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Main

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The restart theorem for the one-point flow** (Case (2)), no named inputs. -/
theorem obs_hist_restartPT {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
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
    let ct := 8 * (csN 2 : ℝ) * k₀ / (histS R m t ^ 2 * M₀) + xh + tn + xp
    (∀ j ≤ n - m,
      ‖betaTot2 (L := L) (N := N) (m + j) (histVF2 R P m o' t (m + j))‖ ≤
        (‖betaTot2 (L := L) (N := N) m (histVF2 R P m o' t m)‖ + (1 / 8 + 10 * ct) * M₀) *
          ∏ k ∈ range j, a k) ∧
    (∀ j ≤ n - m,
      WbHF R P m o' t (m + j) ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t (m + j)).1) *
        (2 * histS R (m + j) t ^ 2 * rkEnv M₀ a j) + (1 / 6) ^ j * w₀) ∧
      KbHF R P m o' t (m + j) ((8 / 15) ^ j * k₀ + 15 * (3 * C₁ + 1) *
        kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * (t (m + j)).1) ^ 2 *
          (histS R (m + j) t ^ 2 * rkEnv M₀ a j))) := by
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
  exact obs_hist_restartT R hKB hC₁k hWB hC₁ hSB hV hm hβ hδ1 H hρ0 hρ P t n hn hnN ht hmn o' h0 hl0
    hs0 hf0 hp0 ck hck hθ0 hθ hsm hκb h64 hκC hε1 hεε hεk hκε hLw hC₁ε hε₁ hβp hδ2 hcgε hcg hcP hcδ0 hBτ hqq0 hqq4
    hcg1 hcδ hτ hsumε hM0 hk₀ hxh htn hw₀ hkw hxp hct hbD0 hW0 hK0 hT hnn hn7 hPr hX


set_option maxHeartbeats 1000000 in
/-- **The restart theorem for the one-point flow** (Case (2)), with the bulk inputs of the
standard history. -/
theorem obs_hist_restartBT {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
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
    let ct := 8 * (csN 2 : ℝ) * k₀ / (histS R m t ^ 2 * M₀) + xh + 4 / 3 * qq + xp
    (∀ j ≤ n - m,
      ‖betaTot2 (L := L) (N := N) (m + j) (histVF2 R P m o' t (m + j))‖ ≤
        (‖betaTot2 (L := L) (N := N) m (histVF2 R P m o' t m)‖ + (1 / 8 + 10 * ct) * M₀) *
          ∏ k ∈ range j, a k) ∧
    (∀ j ≤ n - m,
      WbHF R P m o' t (m + j) ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t (m + j)).1) *
        (2 * histS R (m + j) t ^ 2 * rkEnv M₀ a j) + (1 / 6) ^ j * w₀) ∧
      KbHF R P m o' t (m + j) ((8 / 15) ^ j * k₀ + 15 * (3 * C₁ + 1) *
        kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT) * (cR R Λ cm C₂ * (t (m + j)).1) ^ 2 *
          (histS R (m + j) t ^ 2 * rkEnv M₀ a j))) := by
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
  exact obs_hist_restartPT R hKB hC₁k hWB hC₁ hSB hV hm hβ hδ1 H hρ0 hρ P t n hn hnN ht hmn o' h0
    hl0 hs0 hf0 hp0 ck hck hθ0 hθ hsm hκb h64 hκC hε1 hεε hεk hκε hLw hC₁ε hε₁ hβp hδ2 hcgε hcg hcP hcδ0 hBτ hqq0
    hqq4 hcg1 hcδ hτ hsumε hM0 hk₀ (by positivity) hw₀ hkw hxp hct hxhv hbD0 hW0 hK0 hT' hnn' hn7 hPB hCp hεp
    hL hVL hm1 hcPv hqv


end Main

end

end PtCorr2
