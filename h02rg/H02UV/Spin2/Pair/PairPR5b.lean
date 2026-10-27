import Spin2.Pair.PairPR5

/-!
# PR5: the `ε_k` half of `PairSrcRelR` — the reduced `r'` flow in the `𝔫^{(2)}` split

The Gronwall step `pairRRelR_of_src` compares the reduced `r'` flow with the vertex flow
`β_{a,k+1} = (1 - n_{a,k})β_{a,k} - e_{a,k}` (`Obs2.betaA_hist_succ`, `n_a = ν̄^{(2)}`). This
split is **not** the one-loop split of the `μ^{(2)}` flow: exactly (`nn2_sub_nA2h`)
`𝔫^{(2)}_k - n_{a,k} = ∑_{i<k} tadInc2 i k` (the `𝒲`-tadpoles of the earlier steps), so
`e_{a,k} = err2_k + β_{a,k}∑_{i<k}tadInc2 i k` (`eA2h_eq_err2`). The tadpole sum is `O(ǧ_k)`
(`|tadInc2 i k| ≲ (2/L)^{k-i}ǧ_i`), not `O(ǧ_k²)`, so `∑_kε_k` in `PairSrcRelR` is of order
`∑_kǧ_k` and **not** uniformly bounded. The `ε_k` half of `PairSrcRelR` cannot hold with uniform
constants.

The correct comparison uses `𝔫^{(2)}` for both flows:

* `β_{a,k+1} = (1 - 𝔫^{(2)}_k)β_{a,k} - err2_k` (`bt2_flow`; `Case2Rel` gives
  `‖err2_k‖ ≤ c_δǧ_k²‖β(1-𝔫)‖`, `Case2TopStep` the step `N_h`);
* `r'_{k+1} = (1 - 𝔫^{(2)}_k)r'_k + σ̃_k`, **`σ̃_k = σ'_k + (𝔫^{(2)}_k - n_{a,k})r'_k`** (`srcRT`):
  the `𝒲'`-tadpole part `-e_{ab}` of `σ'_k` and the drift `(𝔫^{(2)} - n_a)r'` combine into the
  `ab` analogue of `err2` (drift `∑_{i<k}(r'_i - r'_k)tadInc2 i k`, `muDriftX2`), which is
  `O(ǧ²)` relative.

Results:
* `rel_step_pure`, **`hBeta_ne_zero_of`** (`β_{a,k} ≠ 0`, `k ≤ N_h + 1`, from `Case2Rel`,
  `‖𝔫‖ ≤ 1/8`, `Case2TopStep`).
* **`PairSrcRelR2 c_σ`** (named input, only the reduced source part: `‖σ̃_k‖ ≤ s_k‖β_{a,k+1}‖`,
  `∑s_k ≤ c_σ‖M_j‖ǧ_j`).
* **`pairRRelR_of_src2`**: `PairSectRed`, `PairRedSeed`, `PairSrcRelR2 c_σ`, `Case2Rel c_δ`,
  `‖𝔫_k‖ ≤ 1/8`, `Case2TopStep`, `∑_{k<N_h}ǧ_k² ≤ G₂` give
  `PairRRelR (c_σ exp((8/7)c_δG₂ + 1/7))`. The `ε_k` are `(8/7)c_δǧ_k²` (`k < N_h`) and `1/7`
  (`k = N_h`): no named `ε` input remains.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- One relative step: `‖𝔫‖ ≤ 1/8`, `‖e‖ ≤ u‖β(1-𝔫)‖`, `u ≤ 1/8`, `β ≠ 0` give
`β(1-𝔫) - e ≠ 0` and `‖e‖ ≤ (8/7)u‖β(1-𝔫) - e‖`. -/
theorem rel_step_pure {β n e : ℂ} {u : ℝ} (hn : ‖n‖ ≤ 1 / 8) (he : ‖e‖ ≤ u * ‖β * (1 - n)‖)
    (hu : u ≤ 1 / 8) (hβ : β ≠ 0) :
    β * (1 - n) - e ≠ 0 ∧ ‖e‖ ≤ 8 / 7 * u * ‖β * (1 - n) - e‖ := by
  have h1n : 7 / 8 ≤ ‖(1 : ℂ) - n‖ := by
    have := norm_sub_norm_le (1 : ℂ) n
    rw [norm_one] at this; linarith
  have hb : 0 < ‖β‖ := norm_pos_iff.2 hβ
  have hbn : 0 < ‖β * (1 - n)‖ := by
    rw [norm_mul]; exact mul_pos hb (by linarith)
  have hu0 : 0 ≤ u := by
    by_contra h
    have : u * ‖β * (1 - n)‖ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) hbn
    linarith [norm_nonneg e]
  have hlow : 7 / 8 * ‖β * (1 - n)‖ ≤ ‖β * (1 - n) - e‖ := by
    have h2 := norm_sub_norm_le (β * (1 - n)) e
    have h3 : u * ‖β * (1 - n)‖ ≤ 1 / 8 * ‖β * (1 - n)‖ :=
      mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    linarith
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, norm_zero] at hlow; linarith
  · have h4 : u * ‖β * (1 - n)‖ ≤ u * (8 / 7 * ‖β * (1 - n) - e‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0
    calc ‖e‖ ≤ u * ‖β * (1 - n)‖ := he
      _ ≤ u * (8 / 7 * ‖β * (1 - n) - e‖) := h4
      _ = 8 / 7 * u * ‖β * (1 - n) - e‖ := by ring

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem hBeta_eq_bt2 (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) :
    hBeta R m b μ₀ x k = bt2 R (ptsX x) (zV b) m b μ₀ k := rfl

/-- **The two one-loop splits differ by the earlier tadpoles** (exact):
`𝔫^{(2)}_k - n_{a,k} = ∑_{i<k} tadInc2 i k`. -/
theorem nn2_sub_nA2h (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (m b μ₀ : ℝ) (k : ℕ) :
    nn2 R P V m b μ₀ k - Obs2.nA2h (R.withMsq m) P (Obs2.obsInit .two V P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k =
      ∑ i ∈ range k, Obs2.tadInc2 P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) i k := by
  unfold nn2 Obs2.frakN2 Obs2.nA2h Obs2.nA2 Obs2.nuBar2 Obs2.bulkE2
  ring

/-- **`β_{a,k} ≠ 0` for `k ≤ N_h + 1`**, and the relative size of `err2_k`, from `Case2Rel`,
`‖𝔫_k‖ ≤ 1/8` (`k < N_h`) and `Case2TopStep`. -/
theorem hBeta_rel_of {Nh : ℕ} (hN : Nh + 2 = N) {m b μ₀ cδ : ℝ} (hb : 0 < b) (x : Lam 2 L N)
    (hrel : Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀) :
    ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 ∧
      hBeta R m b μ₀ x (k + 1) =
        (1 - nn2 R (ptsX x) (zV b) m b μ₀ k) * hBeta R m b μ₀ x k - err2 R (ptsX x) (zV b) m b μ₀ k ∧
      ‖err2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
        (if k < Nh then 8 / 7 * (cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2)
          else 1 / 7) * ‖hBeta R m b μ₀ x (k + 1)‖ := by
  intro k
  induction k with
  | zero =>
    intro h0
    have hb0 : hBeta R m b μ₀ x 0 ≠ 0 := by
      rw [hBeta_eq_bt2, bt2_zV_zero]; exact_mod_cast hb.ne'
    exact step 0 h0 hb0
  | succ k ih =>
    intro hk
    exact step (k + 1) hk (ih (by omega)).2.1
where
  step (k : ℕ) (hk : k ≤ Nh) (hb0 : hBeta R m b μ₀ x k ≠ 0) :
      hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 ∧
      hBeta R m b μ₀ x (k + 1) =
        (1 - nn2 R (ptsX x) (zV b) m b μ₀ k) * hBeta R m b μ₀ x k - err2 R (ptsX x) (zV b) m b μ₀ k ∧
      ‖err2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
        (if k < Nh then 8 / 7 * (cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2)
          else 1 / 7) * ‖hBeta R m b μ₀ x (k + 1)‖ := by
    have hfl : hBeta R m b μ₀ x (k + 1) =
        hBeta R m b μ₀ x k * (1 - nn2 R (ptsX x) (zV b) m b μ₀ k) -
          err2 R (ptsX x) (zV b) m b μ₀ k :=
      bt2_flow R (ptsX x) (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (by omega)
    have key : ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8 ∧
        ∃ u : ℝ, u ≤ 1 / 8 ∧ ‖err2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
          u * ‖hBeta R m b μ₀ x k * (1 - nn2 R (ptsX x) (zV b) m b μ₀ k)‖ ∧
          8 / 7 * u = (if k < Nh then 8 / 7 * (cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2)
            else 1 / 7) := by
      by_cases hkN : k < Nh
      · obtain ⟨h1, h2⟩ := hrel k hkN
        refine ⟨hn k hkN, _, h2, h1, ?_⟩
        rw [if_pos hkN]
      · have hk' : k = Nh := by omega
        subst hk'
        refine ⟨htop.1, 1 / 8, le_rfl, htop.2, ?_⟩
        rw [if_neg hkN]; norm_num
    obtain ⟨hnk, u, hu, he, hu'⟩ := key
    obtain ⟨hne, hle⟩ := rel_step_pure hnk he hu hb0
    rw [← hfl] at hne hle
    rw [← hu']
    exact ⟨hb0, hne, by rw [hfl]; ring, hle⟩

/-- The source of the reduced `r'` flow in the `𝔫^{(2)}` split:
`σ̃_k = σ'_k + (𝔫^{(2)}_k - n_{a,k})r'_k` (`srcR` plus the tadpole drift). -/
def srcRT (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  srcR R m b μ₀ oR x k + (nn2 R (ptsX x) (zV b) m b μ₀ k -
    Obs2.nA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) * hRR R m b μ₀ oR x k

/-- **Named input (PR5, the reduced source only)**: the source `σ̃_k` of the reduced `r'` flow in
the `𝔫^{(2)}` split is small relative to `β_{a,k+1}`: `‖σ̃_k‖ ≤ s_k‖β_{a,k+1}‖`,
`∑_{j≤k≤N_h}s_k ≤ c_σ‖M_j‖ǧ_j`. (Replaces `PairSrcRelR`, whose `ε_k` half fails.) -/
def PairSrcRelR2 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cσ : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ s : ℕ → ℝ, (∀ k, 0 ≤ s k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ‖srcRT R m b μ₀ oR x k‖ ≤ s k * ‖hBeta R m b μ₀ x (k + 1)‖) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), s k ≤
        cσ * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

set_option maxHeartbeats 1000000 in
/-- **`PairRRelR` from the reduced source in the `𝔫^{(2)}` split** (discrete Gronwall): the `ε_k`
are discharged by `Case2Rel`/`Case2TopStep` and `∑_{k<N_h}ǧ_k² ≤ G₂`. -/
theorem pairRRelR_of_src2 {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cσ cδ G2 : ℝ} (hcσ : 0 ≤ cσ)
    (hcδ : 0 ≤ cδ)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hG2 : ∑ k ∈ range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ G2)
    (hRd : PairSectRed R Nh m b μ₀ oR) (hSeed : PairRedSeed R Nh m b μ₀ oR)
    (hrel : ∀ x : Lam 2 L N, x ≠ 0 → Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hS : PairSrcRelR2 R Nh m b μ₀ lam oR cσ) :
    PairRRelR R Nh m b μ₀ lam oR (cσ * Real.exp (8 / 7 * cδ * G2 + 1 / 7)) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨s, hs0, hk, hsum⟩ := hS x hx h1 hj
  rw [← hjd] at hk hsum
  obtain ⟨ho', -, hab', -⟩ := hRd x hx h1 hj
  rw [← hjd] at hab'
  obtain ⟨-, hr0⟩ := hSeed x hx h1 hj
  rw [← hjd] at hr0
  have HB := hBeta_rel_of R hN hb x (hrel x hx) (hn x hx) (htop x hx h1 hj)
  set εf : ℕ → ℝ := fun k => if k < Nh then 8 / 7 * (cδ * (t k).1 ^ 2) else 1 / 7 with hεf
  have hε0 : ∀ k, 0 ≤ εf k := fun k => by
    simp only [hεf]; split_ifs
    · exact mul_nonneg (by norm_num) (mul_nonneg hcδ (sq_nonneg _))
    · norm_num
  have hn' : ∀ k, j ≤ k → Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) t k)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t k) =
      Obs2.nA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t k := fun k _ =>
    PtCorr2.nA2_fullV_indep (R.withMsq m) (ptsX x) k _ _ _ _
      (PtCorr2.obsHistFrom_isObs (R := R.withMsq m) (P := ptsX x) (j := j) ho' t k)
      (Obs2.obsHist_isObs (R.withMsq m) (ptsX x) _ (Obs2.obsInit_isObs .two (zV b) (ptsX x)) k t)
  have hG := Obs2.rel_gronwall (fun k => hRR R m b μ₀ oR x k) (fun k => hBeta R m b μ₀ x k)
    (nn2 R (ptsX x) (zV b) m b μ₀) (fun k => srcRT R m b μ₀ oR x k)
    (err2 R (ptsX x) (zV b) m b μ₀) s εf j (Nh + 1) hr0 hs0 hε0
    (fun k hk1 _ => by
      have h := PtCorr2.rR_succ (R := R.withMsq m) (P := ptsX x) (o' := oR x) (t := t) hab' hk1
      rw [hn' k hk1] at h
      show hRR R m b μ₀ oR x (k + 1) = _
      unfold srcRT hRR srcR
      dsimp only
      rw [h]; ring)
    (fun k _ hk2 => (HB k (by omega)).2.2.1)
    (fun k _ hk2 => (HB k (by omega)).2.1)
    (fun k hk1 hk2 => hk k (mem_Ico.2 ⟨hk1, hk2⟩))
    (fun k _ hk2 => (HB k (by omega)).2.2.2)
  have hεsum : ∑ i ∈ Finset.Ico j (Nh + 1), εf i ≤ 8 / 7 * cδ * G2 + 1 / 7 := by
    rw [Finset.sum_Ico_succ_top (by omega)]
    have e1 : εf Nh = 1 / 7 := by simp [hεf]
    have e2 : ∑ i ∈ Finset.Ico j Nh, εf i = 8 / 7 * cδ * ∑ i ∈ Finset.Ico j Nh, (t i).1 ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      simp only [hεf, if_pos (mem_Ico.1 hi).2]; ring
    have e3 : ∑ i ∈ Finset.Ico j Nh, (t i).1 ^ 2 ≤ G2 := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => sq_nonneg _) hG2
      intro i hi; rw [Finset.mem_range]; exact (mem_Ico.1 hi).2
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left e3 (show 0 ≤ 8 / 7 * cδ by positivity)
    linarith
  set cε := 8 / 7 * cδ * G2 + 1 / 7
  have bnd : ∀ k, j ≤ k → k ≤ Nh + 1 → ‖hRR R m b μ₀ oR x k‖ ≤
      cσ * Real.exp cε * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 *
        ‖hBeta R m b μ₀ x k‖ := by
    intro k hk1 hk2
    refine (hG k hk1 hk2).trans ?_
    have hsub : Finset.Ico j k ⊆ Finset.Ico j (Nh + 1) := Ico_subset_Ico_right hk2
    have hS1 : ∑ i ∈ Finset.Ico j k, s i ≤ cσ * ‖Mmag R m b μ₀ lam j‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 :=
      (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hs0 i).trans hsum
    have hP1 : ∏ i ∈ Finset.Ico j k, (1 + εf i) ≤ Real.exp cε :=
      (prod_one_add_le_exp _ _ fun i _ => hε0 i).trans (Real.exp_le_exp.2
        ((sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hε0 i).trans hεsum))
    have hP0 : 0 ≤ ∏ i ∈ Finset.Ico j k, (1 + εf i) := prod_nonneg fun i _ => by linarith [hε0 i]
    have := mul_le_mul hS1 hP1 hP0 (mul_nonneg (mul_nonneg hcσ (norm_nonneg _)) (hg j hj))
    have := mul_le_mul_of_nonneg_right this (norm_nonneg (hBeta R m b μ₀ x k))
    calc (∑ i ∈ Finset.Ico j k, s i) * (∏ i ∈ Finset.Ico j k, (1 + εf i)) *
          ‖hBeta R m b μ₀ x k‖
        ≤ cσ * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 *
            Real.exp cε * ‖hBeta R m b μ₀ x k‖ := this
      _ = _ := by ring
  refine ⟨fun k hk => bnd k (mem_Ico.1 hk).1 (mem_Ico.1 hk).2.le, ?_⟩
  rw [rRN_eq, (rTilN_eq R Nh m b μ₀ x j).2]
  exact bnd (Nh + 1) (by omega) le_rfl

end Traj

end

end Spin2
