import PtCorr2.Restart.RestartThm
import PtCorr2.Pair.PairChainAB

/-!
# The restart theorem with the bulk inputs of the standard history (B3, T4)

The tadpole increments `tadInc2` and the one-loop coefficient `ν̄^{(2)}` only see the bulk part
of `V'_k(Λ)` (`VprLO_e_fullV_indep`), so they are the same along the restarted history
`obsHistFrom R P m o'` and along any observable history `obsHist R P o₀` from scale `0`
(same trajectory, same point `P.a`):

* `tadInc2_histVF2_eq`, `nuBar2_histVF2_eq`;
* `frakN2F_eq_sub`: `𝔫F_j = 𝔫^{(2)}_j − ∑_{k<m} tadInc2 k j` (`m ≤ j`);
* **`frakN2F_mem_le`**: from `|tadInc2 k j| ≤ B_τq^{j−k}ǧ_k` (`q ≤ 1/4`) and `B_τǧ_k ≤ 1`,
  `|𝔫F_i| ≤ |𝔫^{(2)}_i| + (4/3)q·2^{-(i−m)}` (the memory of the scales `< m` is a transient);
* **`obs_hist_restartB`**: `obs_hist_restartP` with the bulk hypotheses `hT`, `hnn` stated for
  the standard history (`histVO2 R P o₀`, e.g. `o₀ = obsInit .two V P`) — the inputs of
  `obs_hist_rel2` (`TadConcl`: `B_τ = c_e`, `q = 2/L`, `c_eǧ ≤ 1`; `LoopConcl`: `|𝔫| ≤ 1/8`,
  `|𝔫| ≤ c_gr`), available from the master construction at every point `P`, with the **same**
  constants `c_g`, `c_δ` as `obs_hist_rel2` (the transient `t_n = (4/3)q` enters only `c_t`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Bulk

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (m : ℕ)
  (o' : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))

theorem bulkE2_histVF2_eq (h0 : o'.IsObs) (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) (k : ℕ) :
    bulkE2 (histCovO R t) (histVF2 R P m o' t) k = bulkE2 (histCovO R t) (histVO2 R P o₀ t) k := by
  unfold bulkE2 histVF2 histVO2
  exact VprLO_e_fullV_indep R k _ _ _ _ (obsHistFrom_isObs h0 t k) (obsHist_isObs R P o₀ ho₀ k t)

theorem tadInc2_histVF2_eq (h0 : o'.IsObs) (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) (k j : ℕ) :
    tadInc2 P (histCovO R t) (histVF2 R P m o' t) k j =
      tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k j := by
  unfold tadInc2; rw [bulkE2_histVF2_eq R P m o' t h0 o₀ ho₀]

theorem nuBar2_histVF2_eq (h0 : o'.IsObs) (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) (j : ℕ) :
    nuBar2 P (histCovO R t) (histVF2 R P m o' t) j =
      nuBar2 P (histCovO R t) (histVO2 R P o₀ t) j := by
  unfold nuBar2; rw [bulkE2_histVF2_eq R P m o' t h0 o₀ ho₀]

omit [Fact (0 < R.ℓ)] [Fact (0 < R.A)] in
theorem frakN2F_eq_sub {d : ℕ} (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V : ℕ → OFam .two d L N) {m j : ℕ} (hmj : m ≤ j) :
    frakN2F P C V m j = frakN2 P C V j - ∑ k ∈ range m, tadInc2 P C V k j := by
  unfold frakN2F frakN2
  rw [← sum_range_add_sum_Ico _ hmj]; ring

/-- `∑_{k<m} y^{m−k} ≤ (4/3)y` for `0 ≤ y ≤ 1/4`. -/
theorem rs_geom_small {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 4) :
    ∀ m : ℕ, ∑ k ∈ range m, y ^ (m - k) ≤ 4 / 3 * y := by
  intro m
  induction m with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ m ih =>
    have e : ∑ k ∈ range (m + 1), y ^ (m + 1 - k) = y * (∑ k ∈ range m, y ^ (m - k) + 1) := by
      rw [sum_range_succ, Nat.add_sub_cancel_left, pow_one, mul_add, mul_sum, mul_one]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      have hk' := mem_range.1 hk
      rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]; ring
    rw [e]
    have h1 : ∑ k ∈ range m, y ^ (m - k) + 1 ≤ 4 / 3 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hy0
    linarith

/-- **The one-loop coefficient of the restarted flow**: `|𝔫F_i| ≤ |𝔫^{(2)}_i| + (4/3)q·2^{-(i−m)}`
from `|tadInc2 k j| ≤ B_τq^{j−k}ǧ_k` and `B_τǧ_k ≤ 1`. -/
theorem frakN2F_mem_le (h0 : o'.IsObs) (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) {n : ℕ}
    {Bτ qq : ℝ} (hqq0 : 0 ≤ qq) (hqq4 : qq ≤ 1 / 4)
    (hT : ∀ k j, k < j → j < n →
      ‖tadInc2 P (histCovO R t) (histVO2 R P o₀ t) k j‖ ≤ Bτ * qq ^ (j - k) * (t k).1)
    (hBg : ∀ k < n, Bτ * (t k).1 ≤ 1) {i : ℕ} (hmi : m ≤ i) (hin : i < n) :
    ‖frakN2F P (histCovO R t) (histVF2 R P m o' t) m i‖ ≤
      ‖frakN2 P (histCovO R t) (histVO2 R P o₀ t) i‖ + 4 / 3 * qq * (1 / 2) ^ (i - m) := by
  rw [frakN2F_eq_sub _ _ _ hmi]
  have e1 : frakN2 P (histCovO R t) (histVF2 R P m o' t) i =
      frakN2 P (histCovO R t) (histVO2 R P o₀ t) i := by
    rw [frakN2, frakN2, nuBar2_histVF2_eq R P m o' t h0 o₀ ho₀,
      sum_congr rfl fun k _ => tadInc2_histVF2_eq R P m o' t h0 o₀ ho₀ k i]
  rw [e1]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ k ∈ range m, ‖tadInc2 P (histCovO R t) (histVF2 R P m o' t) k i‖ ≤
      qq ^ (i - m) * qq ^ (m - k) := by
    intro k hk
    have hk' := mem_range.1 hk
    rw [tadInc2_histVF2_eq R P m o' t h0 o₀ ho₀]
    refine (hT k i (by omega) hin).trans ?_
    have hq : 0 ≤ qq ^ (i - k) := pow_nonneg hqq0 _
    have := hBg k (by omega)
    calc Bτ * qq ^ (i - k) * (t k).1 = qq ^ (i - k) * (Bτ * (t k).1) := by ring
      _ ≤ qq ^ (i - k) * 1 := mul_le_mul_of_nonneg_left this hq
      _ = qq ^ (i - m) * qq ^ (m - k) := by rw [mul_one, ← pow_add]; congr 1; omega
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  have h2 := rs_geom_small hqq0 hqq4 m
  have h3 : qq ^ (i - m) ≤ (1 / 2) ^ (i - m) := pow_le_pow_left₀ hqq0 (by linarith) _
  have h4 : 0 ≤ ∑ k ∈ range m, qq ^ (m - k) := sum_nonneg fun _ _ => pow_nonneg hqq0 _
  calc qq ^ (i - m) * ∑ k ∈ range m, qq ^ (m - k) ≤ (1 / 2) ^ (i - m) * (4 / 3 * qq) :=
        mul_le_mul h3 h2 h4 (by positivity)
    _ = 4 / 3 * qq * (1 / 2) ^ (i - m) := by ring

end Bulk

/-- The band along a history in `D_ε` is nondecreasing (`ǧ_k ≤ ǧ_{k+1}`). -/
theorem restart_gmono {C₀' εs C₂ Cq Cl cS : ℝ} {R : RGPar 2 L N} [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ2 : δ ≤ 1 / 2) (hcgε : cg * ε ≤ β / 4)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS) {n : ℕ} {t : Flow2.Hist.Seq (Xs R)}
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t) (k : ℕ) (hk : k < n) :
    (t k).1 ≤ (t (k + 1)).1 := by
  have hcg0 : 0 ≤ cg := H.hcg
  have hr := ht.2 k hk
  obtain ⟨hg, hgε, -, -⟩ := ht.1 k hk.le
  have h3 : cg * (t k).1 ^ 3 ≤ β / 4 * (t k).1 ^ 2 := by
    have : cg * (t k).1 ≤ cg * ε := mul_le_mul_of_nonneg_left hgε hcg0
    have e : cg * (t k).1 ^ 3 = (cg * (t k).1) * (t k).1 ^ 2 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right (this.trans hcgε) (sq_nonneg _)
  have hδβ : δ * β * (t k).1 ^ 2 ≤ 1 / 2 * β * (t k).1 ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ2 hβ) (sq_nonneg _)
  rw [abs_le] at hr
  have : 0 ≤ β / 4 * (t k).1 ^ 2 := by positivity
  linarith [hr.1]

section Main

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The restart theorem for the one-point flow** (Case (2)), with the bulk inputs of the
standard history. -/
theorem obs_hist_restartB {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
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
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
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
    {M₀ k₀ xh : ℝ} (hM0 : 0 < M₀) (hk₀ : 0 ≤ k₀)
    (hct : 8 * (csN 2 : ℝ) * k₀ / (histS R m t ^ 2 * M₀) + xh + 4 / 3 * qq ≤ 1 / 48)
    (hxhv : xh = cbnC * (1280 * locK 2 ^ 2 * (8 / (7 * L)) + 1) *
      ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀)) /
        (histS R m t ^ 2 * M₀))
    (hbD0 : ‖betaTot2 (L := L) (N := N) m (histVF2 R P m o' t m)‖ +
      shareDev2 P.a m (histVF2 R P m o' t m) ≤ M₀)
    (hW0 : WbHF R P m o' t m ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t m).1) * (2 * histS R m t ^ 2 * M₀)))
    (hK0 : KbHF R P m o' t m k₀)
    (h8 : 8 * k₀ ≤ (ck - 60 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) *
      (cR R Λ cm C₂ * (t m).1) ^ 2 * ((3 * C₁ + 1) * (2 * histS R m t ^ 2 * M₀)))
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
    let ct := 8 * (csN 2 : ℝ) * k₀ / (histS R m t ^ 2 * M₀) + xh + 4 / 3 * qq
    (∀ j ≤ n - m,
      ‖betaTot2 (L := L) (N := N) (m + j) (histVF2 R P m o' t (m + j))‖ ≤
        (‖betaTot2 (L := L) (N := N) m (histVF2 R P m o' t m)‖ + (1 / 8 + 10 * ct) * M₀) *
          ∏ k ∈ range j, a k) ∧
    (∀ j ≤ n - m,
      WbHF R P m o' t (m + j) ((3 * C₁ + 1) * (cR R Λ cm C₂ * (t (m + j)).1) *
        (2 * histS R (m + j) t ^ 2 * rkEnv M₀ a j)) ∧
      KbHF R P m o' t (m + j) ((1 / 2) ^ j * k₀ + 15 * (3 * C₁ + 1) *
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
  exact obs_hist_restartP R hKB hC₁k hWB hC₁ hSB hV hm hβ hδ1 H hρ0 hρ P t n hn hnN ht hmn o' h0
    hl0 hs0 hf0 hp0 ck hck hθ0 hθ hsm hε1 hεε hεk hLw hC₁ε hε₁ hβp hδ2 hcgε hcg hcP hcδ0 hBτ hqq0
    hqq4 hcg1 hcδ hτ hsumε hM0 hk₀ (by positivity) hct hxhv hbD0 hW0 hK0 h8 hT' hnn' hn7 hPB hCp hεp
    hL hVL hm1 hcPv hqv

end Main

end

end PtCorr2
