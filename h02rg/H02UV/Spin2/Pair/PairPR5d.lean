import Spin2.Pair.PairPR5b
import Spin2.Case2.Case2RelPairLI
import PtCorr2.Pair.PairChainAB
import Obs2.Flow.MemGronwall

/-!
# PR5 (cont.): the reduced source unrolled; the drift handled; `PairRRelR` from the error

Along the reduced history from `j = j_x` (`Obs2/Flow/MuChainAB`, `PtCorr2/Pair/PairChainAB`):

* **`srcRT_eq`** (exact): `σ̃_k = -(∑_{i<k}(r̂'_i - r'_k)tadInc2 i k + err'_k)` with `r̂'_i = r'_i`
  (`i ≥ j`), `0` (`i < j`), `tadInc2` of the original history (`tadO`), and
  `err'_k = errAB` (`hErrR`): activity, `𝒲'_k(0)`, Pauli/gradient defects, far blocks, memory
  terms (Pauli defect × tadpole, gradient tadpoles, tadpoles of `loc^{ab}`, product increments).
  The drift contains `r'` itself, so `PairSrcRelR2` (a bound on `σ̃`) is circular; it is replaced by
* **`PairErrRelR c_e`** (named input): `‖err'_k‖ ≤ s_k‖β_{a,k+1}‖`, `∑_{j≤k≤N_h}s_k ≤ c_e‖M_j‖ǧ_j`;
* **`pairRRelR_of_err`**: `PairErrRelR c_e` and the bulk bounds `‖tadInc2 i k‖ ≤ c_t(2/L)^{k-i}ǧ_i`,
  `c_tǧ_i ≤ 1`, `‖𝔫_k‖ ≤ B'ǧ_k`, `ǧ` nondecreasing, `L ≥ 49` (with `Case2Rel`, `Case2TopStep`,
  `‖𝔫‖ ≤ 1/8`, `∑ǧ² ≤ G₂`, as in `pairRRelR_of_src2`) give `PairRRelR` via
  `Obs2.rel_gronwall_geom` (relative Gronwall with memory: the drift increments `r'_i/β_i - r'_k/β_k`
  are absorbed by the geometric kernel, the vertex increments `β_i - β_k = O(ǧ)` give `O(ǧ²)` weights).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The tadpole increments of the original history at the pair vertex `0`. -/
def tadO (m b μ₀ : ℝ) (x : Lam 2 L N) (i k : ℕ) : ℂ :=
  Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) i k

/-- The error `err'_k` of the reduced `r'` flow (`Obs2.errAB` along the reduced history). -/
def hErrR (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.errAB (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (Obs.coal L (0 : Lam 2 L N) x) k

/-- **The reduced source in the `𝔫^{(2)}` split, unrolled** (exact, `k ≥ j_x`). -/
theorem srcRT_eq (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (ho' : (oR x).IsObs) (hab : PtCorr2.ObsAbInv (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (hW0 : ∀ B, ((oR x).W B : Obs.SA .two (Lam 2 L N)).ab = 0) {k : ℕ}
    (hk : Obs.coal L (0 : Lam 2 L N) x ≤ k) :
    srcRT R m b μ₀ oR x k =
      -(∑ i ∈ range k, ((if Obs.coal L (0 : Lam 2 L N) x ≤ i then hRR R m b μ₀ oR x i else 0) -
          hRR R m b μ₀ oR x k) * tadO R m b μ₀ x i k + hErrR R m b μ₀ oR x k) := by
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have h1 := nn2_sub_nA2h R (ptsX x) (zV b) m b μ₀ k
  have h2 := PtCorr2.srcAB_hR_eq (R := R.withMsq m) (P := ptsX x) (t := t) hab hW0 hk
  have hti : ∀ i, Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t) i k =
      tadO R m b μ₀ x i k := fun i =>
    PtCorr2.tadInc2_hR_eq ho' (Obs2.obsInit_isObs .two (zV b) (ptsX x)) i k
  simp only [hti] at h2
  unfold Obs2.driftAB at h2
  simp only [hti] at h2
  have e : srcR R m b μ₀ oR x k = Obs2.srcAB (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t) k := rfl
  unfold srcRT
  rw [h1, e]
  unfold tadO at h2 ⊢
  unfold PtCorr2.rR at h2
  unfold hErrR hRR PtCorr2.rR
  linear_combination h2

/-- **Named input (PR5, the error of the reduced `r'` flow)**: `‖err'_k‖ ≤ s_k‖β_{a,k+1}‖`,
`∑_{j≤k≤N_h}s_k ≤ c_e‖M_j‖ǧ_j`. Unlike `PairSrcRelR2`, `err'` contains no `r'`-drift. -/
def PairErrRelR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (ce : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ s : ℕ → ℝ, (∀ k, 0 ≤ s k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ‖hErrR R m b μ₀ oR x k‖ ≤ s k * ‖hBeta R m b μ₀ x (k + 1)‖) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), s k ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- The constant of `pairRRelR_of_err`. -/
def crErr (ce cδ G2 ct B' : ℝ) : ℝ :=
  2 * ce * Real.exp (2 * ((8 / 7 * cδ * G2 + 1 / 7) +
    1 / 16 * ((64 / 49 * B' * ct + 8 / 7 * cδ) * G2) + 64 / 49 / 16))

set_option maxHeartbeats 2000000 in
/-- **`PairRRelR` from the error of the reduced flow** (relative Gronwall with memory). -/
theorem pairRRelR_of_err {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce cδ G2 ct B' : ℝ} (hce : 0 ≤ ce)
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
    (hE : PairErrRelR R Nh m b μ₀ lam oR ce) :
    PairRRelR R Nh m b μ₀ lam oR (crErr ce cδ G2 ct B') := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨s, hs0, hk, hsum⟩ := hE x hx h1 hj
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
  have hG := Obs2.rel_gronwall_geom (fun k => hRR R m b μ₀ oR x k) (fun k => hBeta R m b μ₀ x k)
    (nn2 R (ptsX x) (zV b) m b μ₀) (err2 R (ptsX x) (zV b) m b μ₀)
    (fun k => hErrR R m b μ₀ oR x k) (fun i k => tadO R m b μ₀ x i k) s εf g ct B' (2 / (L : ℝ))
    j (Nh + 1) h1 hr0 hs0 hε0 hct hB' (by positivity)
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
      1 / 16 * ∑ l ∈ Ico j (Nh + 1), (if l + 1 < Nh + 1 then 64 / 49 * B' * ct * g l ^ 2 + εf l
        else 0) + 64 / 49 / 16) ≤
      2 * ((8 / 7 * cδ * G2 + 1 / 7) + 1 / 16 * ((64 / 49 * B' * ct + 8 / 7 * cδ) * G2) +
        64 / 49 / 16) := by
    have := mul_le_mul_of_nonneg_left hhsum (show (0 : ℝ) ≤ 1 / 16 by norm_num)
    linarith
  have bnd : ∀ k, j ≤ k → k ≤ Nh + 1 → ‖hRR R m b μ₀ oR x k‖ ≤
      crErr ce cδ G2 ct B' * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 *
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
    unfold crErr; ring
  refine ⟨fun k hk => bnd k (mem_Ico.1 hk).1 (mem_Ico.1 hk).2.le, ?_⟩
  rw [rRN_eq, (rTilN_eq R Nh m b μ₀ x j).2]
  exact bnd (Nh + 1) (by omega) le_rfl

end Traj

end

end Spin2
