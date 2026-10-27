import Spin2.Pair.PairErrAB
import Obs2.Flow.MuChainAB2
import Obs2.Flow.MemGronwall2

/-!
# The `𝒲'` tadpole settled: the mass of `𝒲'` is a product term; `PairRRelR` with
`r'`-proportional errors

`errAB` contains `wTadAB_k(𝒲'_k, 0)`, the full mass of `𝒲'_{k,ab}`. Its crude size has an
`r'`-proportional part `≈ ǧ_k|r'_k|` that is not summable relative to `β` (`∑ǧ_k = ∞`). The exact
identity `Obs2.wTadAB_zero_succ` shows that this part vanishes: the mass of `𝒲_{k}` is the mass of
the product part `∏(1 + 𝒲'_{k-1}(B)) − 1 − ∑𝒲'_{k-1}(B)` of the previous step
(`Obs2.MuChainAB.errAB_eq2`, `wMassAB`), whose size is linear in the `ab` size of `𝒲'_{k-1}` times
its bulk size: `O(ǧ³)|r'_{k-1}|` relative. No new drift term is needed; it suffices to allow
`r'`-proportional errors with summable coefficients in the Gronwall step:

* **`PairErrRelR2 c_e c_a`**: `‖err'_k‖ ≤ s_k‖β_{a,k+1}‖ + ∑_{j≤i≤k}η_{ik}‖r'_i‖`, `∑s ≤ c_e‖M_j‖ǧ_j`,
  `∑_k∑_i(64/49)^{k+1-i}η_{ik} ≤ c_a`; `pairErrRelR2_of_errRelR` (`PairErrRelR` is the case `η = 0`).
* **`pairRRelR_of_err2`** (copy of `pairRRelR_of_err`, via `Obs2.rel_gronwall_geomR`): constant
  `crErr2 = 2c_e·exp(2(… + c_a + …))`.
* `hErrR2` (`errAB2` along the reduced history), **`hErrR_eq2`**.
* **`PairErrSizesR3 c_e c_a`** (named input; replaces `PairErrSizesR`): as `PairErrSizesR`, but the
  `𝒲'` term is the product term — bulk and `ab` sizes `e_k`, `o_k` of `𝒲'_{k-1}(B)` in
  `T_k(ℓ_k)` with `2L²o_k((1+e_k)^{L²} − 1)ℓ_k^{-2} ≤ s^w_k‖β_{a,k+1}‖ + η^w_k‖r'_{k-1}‖` — and the
  memory terms may be `r'`-proportional (`≤ s^m_k‖β‖ + ∑_iη^m_{ik}‖r'_i‖`).
* **`pairErrRelR2_of_sizes3`**: `PairAnchR` + `PairErrSizesR3` ⇒ `PairErrRelR2`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Named input (PR5, the error of the reduced `r'` flow, `r'`-proportional parts allowed).** -/
def PairErrRelR2 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (ce ca : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (s : ℕ → ℝ) (η : ℕ → ℕ → ℝ), (∀ k, 0 ≤ s k) ∧ (∀ i k, 0 ≤ η i k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ‖hErrR R m b μ₀ oR x k‖ ≤ s k * ‖hBeta R m b μ₀ x (k + 1)‖ +
          ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, η i k * ‖hRR R m b μ₀ oR x i‖) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), s k ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k ≤ ca

/-- The constant of `pairRRelR_of_err2`. -/
def crErr2 (ce cδ G2 ct B' ca : ℝ) : ℝ :=
  2 * ce * Real.exp (2 * ((8 / 7 * cδ * G2 + 1 / 7) + ca +
    1 / 16 * ((64 / 49 * B' * ct + 8 / 7 * cδ) * G2) + 64 / 49 / 16))

set_option maxHeartbeats 2000000 in
/-- **`PairRRelR` from the error of the reduced flow, `r'`-proportional errors allowed**
(`Obs2.rel_gronwall_geomR`). Copy of `pairRRelR_of_err`. -/
theorem pairRRelR_of_err2 {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce cδ G2 ct B' ca : ℝ} (hce : 0 ≤ ce)
    (hcδ : 0 ≤ cδ) (hct : 0 ≤ ct) (hB' : 0 ≤ B') (hL : 49 ≤ L)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hG2 : ∑ k ∈ range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ G2)
    (hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1)
    (hcg : ∀ i ≤ Nh, ct * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤ 1)
    (hRd : PairSectRed R Nh m b μ₀ oR) (hSeed : PairRedSeed R Nh m b μ₀ oR)
    (hW0 : ∀ x : Lam 2 L N, ∀ B, ((oR x).W B : Obs.SA .two (Lam 2 L N)).ab = 0)
    (hrel : ∀ x : Lam 2 L N, x ≠ 0 → Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (hnB : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
      B' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (ht : ∀ x : Lam 2 L N, x ≠ 0 → ∀ i k, i < k → k ≤ Nh →
      ‖tadO R m b μ₀ x i k‖ ≤ ct * (2 / (L : ℝ)) ^ (k - i) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1)
    (hE : PairErrRelR2 R Nh m b μ₀ lam oR ce ca) :
    PairRRelR R Nh m b μ₀ lam oR (crErr2 ce cδ G2 ct B' ca) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨s, η, hs0, hη0, hk, hsum, hηsum⟩ := hE x hx h1 hj
  rw [← hjd] at hk hsum hηsum
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
  set g : ℕ → ℝ := fun i => max (t i).1 0 with hgd
  have hgle : ∀ i ≤ Nh, g i = (t i).1 := fun i hi => max_eq_left (hg i hi)
  have hn' : ∀ k, j ≤ k → Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) t k)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t k) =
      Obs2.nA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t k := fun k _ =>
    PtCorr2.nA2_fullV_indep (R.withMsq m) (ptsX x) k _ _ _ _
      (PtCorr2.obsHistFrom_isObs (R := R.withMsq m) (P := ptsX x) (j := j) ho' t k)
      (Obs2.obsHist_isObs (R.withMsq m) (ptsX x) _ (Obs2.obsInit_isObs .two (zV b) (ptsX x)) k t)
  have hflow : ∀ k, j ≤ k → hRR R m b μ₀ oR x (k + 1) =
      (1 - nn2 R (ptsX x) (zV b) m b μ₀ k) * hRR R m b μ₀ oR x k -
        ∑ i ∈ range k, ((if j ≤ i then hRR R m b μ₀ oR x i else 0) - hRR R m b μ₀ oR x k) *
          tadO R m b μ₀ x i k - hErrR R m b μ₀ oR x k := by
    intro k hk1
    have h0 : hRR R m b μ₀ oR x (k + 1) =
        (1 - nn2 R (ptsX x) (zV b) m b μ₀ k) * hRR R m b μ₀ oR x k + srcRT R m b μ₀ oR x k := by
      have h := PtCorr2.rR_succ (R := R.withMsq m) (P := ptsX x) (o' := oR x) (t := t) hab' hk1
      rw [hn' k hk1] at h
      show hRR R m b μ₀ oR x (k + 1) = _
      unfold srcRT hRR srcR
      dsimp only
      rw [h]; ring
    rw [h0, srcRT_eq R m b μ₀ oR x ho' hab' (hW0 x) hk1]
    ring
  have hL' : (49 : ℝ) ≤ L := by exact_mod_cast hL
  have hG := Obs2.rel_gronwall_geomR (fun k => hRR R m b μ₀ oR x k) (fun k => hBeta R m b μ₀ x k)
    (nn2 R (ptsX x) (zV b) m b μ₀) (err2 R (ptsX x) (zV b) m b μ₀)
    (fun k => hErrR R m b μ₀ oR x k) (fun i k => tadO R m b μ₀ x i k) s εf g η ct B' (2 / (L : ℝ))
    j (Nh + 1) h1 hr0 hs0 hε0 hη0 hct hB' (by positivity)
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL')
    (fun k hk1 _ => hflow k hk1)
    (fun k _ hk2 => (HB k (by omega)).2.2.1)
    (fun k hk1 hk2 => by
      rcases Nat.lt_or_ge k (Nh + 1) with h | h
      · exact (HB k (by omega)).1
      · obtain rfl : k = Nh + 1 := by omega
        exact (HB Nh le_rfl).2.1)
    (fun k hk1 hk2 => hk k (mem_Ico.2 ⟨hk1, hk2⟩))
    (fun k _ hk2 => (HB k (by omega)).2.2.2)
    (fun k _ hk2 => by
      simp only [hεf]; split_ifs with hkN
      · have h' : cδ * (t k).1 ^ 2 ≤ 1 / 8 := (hrel x hx k hkN).2
        linarith
      · exact le_rfl)
    (fun k _ hk2 => by
      rcases Nat.lt_or_ge k Nh with h | h
      · exact hn x hx k h
      · obtain rfl : k = Nh := by omega
        exact (htop x hx h1 hj).1)
    (fun k _ hk2 => (hnB x hx k (by omega)).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hB'))
    (fun k _ hk2 i hi => (ht x hx i k hi (by omega)).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_nonneg hct (by positivity))))
    (fun i => le_max_right _ _)
    (fun i hi => by rw [hgle i (by omega)]; exact hcg i (by omega))
    (fun i l hil hl => by
      rw [hgle i (by omega), hgle l (by omega)]; exact hgm i l hil (by omega))
  -- the weight
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
  have hhsum : ∑ l ∈ Ico j (Nh + 1), (if l + 1 < Nh + 1 then 64 / 49 * B' * ct * g l ^ 2 + εf l
      else 0) ≤ (64 / 49 * B' * ct + 8 / 7 * cδ) * G2 := by
    rw [Finset.sum_Ico_succ_top (by omega), if_neg (by omega), add_zero]
    have e2 : ∑ l ∈ Finset.Ico j Nh, (if l + 1 < Nh + 1 then 64 / 49 * B' * ct * g l ^ 2 + εf l
        else 0) = (64 / 49 * B' * ct + 8 / 7 * cδ) * ∑ i ∈ Finset.Ico j Nh, (t i).1 ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := (mem_Ico.1 hi).2
      simp only [if_pos (show i + 1 < Nh + 1 by omega), hεf, if_pos hi', hgle i hi'.le]; ring
    have e3 : ∑ i ∈ Finset.Ico j Nh, (t i).1 ^ 2 ≤ G2 := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => sq_nonneg _) hG2
      intro i hi; rw [Finset.mem_range]; exact (mem_Ico.1 hi).2
    rw [e2]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)
  have hW : 2 * (∑ i ∈ Ico j (Nh + 1), εf i +
      ∑ k ∈ Ico j (Nh + 1), ∑ i ∈ Icc j k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k +
      1 / 16 * ∑ l ∈ Ico j (Nh + 1), (if l + 1 < Nh + 1 then 64 / 49 * B' * ct * g l ^ 2 + εf l
        else 0) + 64 / 49 / 16) ≤
      2 * ((8 / 7 * cδ * G2 + 1 / 7) + ca + 1 / 16 * ((64 / 49 * B' * ct + 8 / 7 * cδ) * G2) +
        64 / 49 / 16) := by
    have := mul_le_mul_of_nonneg_left hhsum (show (0 : ℝ) ≤ 1 / 16 by norm_num)
    linarith
  have bnd : ∀ k, j ≤ k → k ≤ Nh + 1 → ‖hRR R m b μ₀ oR x k‖ ≤
      crErr2 ce cδ G2 ct B' ca * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 *
        ‖hBeta R m b μ₀ x k‖ := by
    intro k hk1 hk2
    refine (hG k hk1 hk2).trans ?_
    have hS1 : 2 * ∑ i ∈ Finset.Ico j (Nh + 1), s i ≤
        2 * (ce * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) := by
      linarith
    have hP1 := Real.exp_le_exp.2 hW
    have := mul_le_mul hS1 hP1 (Real.exp_pos _).le
      (by have := hg j hj; positivity)
    have := mul_le_mul_of_nonneg_right this (norm_nonneg (hBeta R m b μ₀ x k))
    refine this.trans (le_of_eq ?_)
    unfold crErr2; ring
  refine ⟨fun k hk => bnd k (mem_Ico.1 hk).1 (mem_Ico.1 hk).2.le, ?_⟩
  rw [rRN_eq, (rTilN_eq R Nh m b μ₀ x j).2]
  exact bnd (Nh + 1) (by omega) le_rfl

/-- The error `err'_k` written with the mass of `𝒲'` as a product term (`Obs2.errAB2`). -/
def hErrR2 (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.errAB2 (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (Obs.coal L (0 : Lam 2 L N) x) k

/-- **`err'_k = errAB2`** along the reduced history (`k ≥ j_x`). -/
theorem hErrR_eq2 (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (hab : PtCorr2.ObsAbInv (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (hW0 : ∀ B, ((oR x).W B : Obs.SA .two (Lam 2 L N)).ab = 0) {k : ℕ}
    (hk : Obs.coal L (0 : Lam 2 L N) x ≤ k) :
    hErrR R m b μ₀ oR x k = hErrR2 R m b μ₀ oR x k :=
  (PtCorr2.muChainAB_hR (R := R.withMsq m) (P := ptsX x)
    (t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hab hW0 k).errAB_eq2 _ hk le_rfl

/-- **Named input: the `ab` sizes of the reduced history, product form of the `𝒲'` mass.**
As `PairErrSizesR`, with the `𝒲'` term replaced by the bulk and `ab` sizes `e_k`, `o_k` of the
`𝒲'` of the previous step (the product term), and with `r'`-proportional parts allowed in the
`𝒲'` and memory terms. -/
def PairErrSizesR3 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (ce ca : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (ℓs sq se so sw sp sg sm ηw : ℕ → ℝ) (ηm : ℕ → ℕ → ℝ),
      (∀ k, 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sg k ∧
        0 ≤ sm k ∧ 0 ≤ ηw k) ∧ (∀ i k, 0 ≤ ηm i k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
        let C := Obs2.histCovO (R.withMsq m) t
        let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let K := PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let β := ‖hBeta R m b μ₀ x (k + 1)‖
        GoodCov2 k (ℓs k) (C k) ∧
        (∀ B, (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ∈
          NX (nbhd k (blockSet (L := L) (N := N) k B) : Set (Lam 2 L N))) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sq k * β)) ∧
        (Obs.coal L (0 : Lam 2 L N) x < k →
          (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
            (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (se k)) ∧
          (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
            (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (so k)) ∧
          2 * ((L : ℝ) ^ 2 * so k * ((1 + se k) ^ (L ^ 2) - 1) * (ℓs k)⁻¹ ^ 2) ≤
            sw k * β + ηw k * ‖hRR R m b μ₀ oR x (k - 1)‖) ∧
        ‖Obs2.pdefM2 k (C k) (V k)‖ * ‖1 - Obs2.nA2 (ptsX x) k (C k) (V k)‖ ≤ sp k * β ∧
        ‖Obs.LocObs.mass2 (Grassmann.FC (C k) (Obs2.dAB (ptsX x) k (C k) (V k))
          (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sg k * β ∧
        ∑ i ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) k, ‖Obs2.memAB (ptsX x) C V W i k‖ ≤
          sm k * β + ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k,
            ηm i k * ‖hRR R m b μ₀ oR x i‖) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + sw k + sp k + sg k + sm k) ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k,
            (64 / 49 : ℝ) ^ (k + 1 - i) * ηm i k + (64 / 49 : ℝ) ^ 2 * ηw k) ≤ ca

set_option maxHeartbeats 1000000 in
/-- **`PairErrRelR2` from the `ab` sizes** (product form of the `𝒲'` mass). -/
theorem pairErrRelR2_of_sizes3 {Nh : ℕ} (hN : Nh + 2 = N) (hL : pauliL0 2 ≤ L) (m b μ₀ : ℝ)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce ca : ℝ}
    (hRd : PairSectRed R Nh m b μ₀ oR)
    (hW0 : ∀ x : Lam 2 L N, ∀ B, ((oR x).W B : Obs.SA .two (Lam 2 L N)).ab = 0)
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hS : PairErrSizesR3 R Nh m b μ₀ lam oR ce ca) :
    PairErrRelR2 R Nh m b μ₀ lam oR ce ca := by
  intro x hx h1 hj
  obtain ⟨ℓs, sq, se, so, sw, sp, sg, sm, ηw, ηm, h0, hηm0, hk, hsum, hηsum⟩ := hS x hx h1 hj
  have hanc := hA x hx h1 hj
  obtain ⟨-, -, hab, -⟩ := hRd x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  refine ⟨fun k => 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + sw k + sp k + sg k + sm k,
    fun i k => ηm i k + if i = k - 1 then ηw k else 0, fun k => ?_, fun i k => ?_,
    fun k hk' => ?_, hsum, ?_⟩
  · obtain ⟨hl, hq, -, -, hw, hp, hg, hm, -⟩ := h0 k
    have hQ := one_le_Q1 (d := 2) one_le_two
    have a1 : 0 ≤ Q1 2 * sq k * (ℓs k)⁻¹ ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith) hq) (sq_nonneg _)
    linarith
  · show 0 ≤ ηm i k + (if i = k - 1 then ηw k else 0)
    have := hηm0 i k
    have := (h0 k).2.2.2.2.2.2.2.2
    split_ifs <;> linarith
  · -- the per-scale bound
    obtain ⟨hl, hq, he0, ho0, hw, hp, hg, hm, hηw⟩ := h0 k
    obtain ⟨hC, hloc, hQ, hWk, hP, hG, hM⟩ := hk k hk'
    set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    set β := ‖hBeta R m b μ₀ x (k + 1)‖
    have hβ : 0 ≤ β := norm_nonneg _
    have hjk : j ≤ k := (Finset.mem_Ico.1 hk').1
    have hkN : k < N := by have := (Finset.mem_Ico.1 hk').2; omega
    have H := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hjk
    have hf := PtCorr2.farABm_hR_eq_zero (R.withMsq m) (ptsX x) hanc t hjk
    have hq' := Obs2.norm_qAB_le one_le_two hL (ptsX x) hkN hl (mul_nonneg hq hβ) hC H hloc hQ
    have he := Obs2.norm_errAB2_le (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oR x) t)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) j (oR x) t) j k hf
    set rs : ℕ → ℝ := fun i => ‖hRR R m b μ₀ oR x i‖ with hrs
    have hrs0 : ∀ i, 0 ≤ rs i := fun i => norm_nonneg _
    -- the product term
    have hWm : ‖Obs2.wMassAB (ptsX x) (Obs2.histCovO (R.withMsq m) t)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t)
        (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oR x) t) j k‖ ≤
        sw k * β + ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i := by
      have hsum0 : 0 ≤ ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i :=
        sum_nonneg fun i _ => mul_nonneg (by split_ifs <;> linarith) (hrs0 i)
      unfold Obs2.wMassAB
      split_ifs with hlt
      · obtain ⟨hWe, hWo, hWs⟩ := hWk hlt
        have hj1 : j ≤ k - 1 := by omega
        have H1 := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hj1
        rw [PtCorr2.farABm_hR_eq_zero (R.withMsq m) (ptsX x) hanc t hj1, zero_add]
        refine (Obs2.norm_wProdAB0_le H1 k hl he0 ho0 hWe hWo).trans (hWs.trans ?_)
        have hmem : k - 1 ∈ Finset.Icc j k := Finset.mem_Icc.2 ⟨hj1, by omega⟩
        have := Finset.single_le_sum (f := fun i => (if i = k - 1 then ηw k else 0) * rs i)
          (fun i _ => mul_nonneg (by split_ifs <;> linarith) (hrs0 i)) hmem
        simp only [if_true] at this
        have e : rs (k - 1) = ‖hRR R m b μ₀ oR x (k - 1)‖ := rfl
        rw [e] at this
        linarith
      · rw [norm_zero]
        have := mul_nonneg hw hβ
        linarith
    show ‖hErrR R m b μ₀ oR x k‖ ≤ _
    rw [hErrR_eq2 R m b μ₀ oR x hab (hW0 x) hjk]
    refine he.trans ?_
    have e1 : 2 * (Q1 2 * (sq k * β) * (ℓs k)⁻¹ ^ 2) = 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) * β := by
      ring
    rw [e1] at hq'
    have hsplit : ∑ i ∈ Finset.Icc j k, (ηm i k + if i = k - 1 then ηw k else 0) * rs i =
        ∑ i ∈ Finset.Icc j k, ηm i k * rs i +
          ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
    show _ ≤ _ + ∑ i ∈ Finset.Icc j k, (ηm i k + if i = k - 1 then ηw k else 0) * rs i
    rw [hsplit]
    have hM' : ∑ i ∈ Finset.Ico j k, ‖Obs2.memAB (ptsX x) (Obs2.histCovO (R.withMsq m) t)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t)
        (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oR x) t) i k‖ ≤
        sm k * β + ∑ i ∈ Finset.Icc j k, ηm i k * rs i := hM
    have hP' := hP
    have hG' := hG
    calc _ ≤ 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) * β +
          (sw k * β + ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i) +
          sp k * β + sg k * β + (sm k * β + ∑ i ∈ Finset.Icc j k, ηm i k * rs i) := by
          gcongr
      _ = _ := by ring
  · -- the weight
    refine le_trans (sum_le_sum fun k hk' => ?_) hηsum
    have hjk : j ≤ k := (Finset.mem_Ico.1 hk').1
    rw [show ∑ i ∈ Finset.Icc j k, (64 / 49 : ℝ) ^ (k + 1 - i) *
        (ηm i k + if i = k - 1 then ηw k else 0) =
        ∑ i ∈ Finset.Icc j k, (64 / 49 : ℝ) ^ (k + 1 - i) * ηm i k +
          ∑ i ∈ Finset.Icc j k, (if i = k - 1 then (64 / 49 : ℝ) ^ (k + 1 - i) * ηw k else 0) by
      rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by split_ifs <;> ring]
    gcongr
    rw [Finset.sum_ite_eq']
    have hηw := (h0 k).2.2.2.2.2.2.2.2
    split_ifs with hmem
    · have hk1 : 1 ≤ k := by have := (Finset.mem_Ico.1 hk').1; omega
      rw [show k + 1 - (k - 1) = 2 by omega]
    · positivity

/-- **`PairRRelR` from the `ab` sizes, product form of the `𝒲'` mass**
(`pairErrRelR2_of_sizes3` + `pairRRelR_of_err2`). -/
theorem pairRRelR_of_sizes3 {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce cδ G2 ct B' ca : ℝ} (hce : 0 ≤ ce)
    (hcδ : 0 ≤ cδ) (hct : 0 ≤ ct) (hB' : 0 ≤ B') (hL : 49 ≤ L)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hG2 : ∑ k ∈ range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ G2)
    (hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1)
    (hcg : ∀ i ≤ Nh, ct * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤ 1)
    (hRd : PairSectRed R Nh m b μ₀ oR) (hSeed : PairRedSeed R Nh m b μ₀ oR)
    (hW0 : ∀ x : Lam 2 L N, ∀ B, ((oR x).W B : Obs.SA .two (Lam 2 L N)).ab = 0)
    (hrel : ∀ x : Lam 2 L N, x ≠ 0 → Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (hnB : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
      B' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (ht : ∀ x : Lam 2 L N, x ≠ 0 → ∀ i k, i < k → k ≤ Nh →
      ‖tadO R m b μ₀ x i k‖ ≤ ct * (2 / (L : ℝ)) ^ (k - i) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1)
    (hLp : pauliL0 2 ≤ L) (hA : PairAnchR (L := L) (N := N) Nh oR)
    (hS : PairErrSizesR3 R Nh m b μ₀ lam oR ce ca) :
    PairRRelR R Nh m b μ₀ lam oR (crErr2 ce cδ G2 ct B' ca) :=
  pairRRelR_of_err2 R hN m hb lam oR hce hcδ hct hB' hL hg hG2 hgm hcg hRd hSeed hW0 hrel hn hnB
    htop ht (pairErrRelR2_of_sizes3 R hN hLp m b μ₀ lam oR hRd hW0 hA hS)

end Traj

end

end Spin2
