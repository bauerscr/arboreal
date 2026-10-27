import Spin2.Pair.PairErrAB3
import PtCorr2.Pair.ShareABHist1

/-!
# Per-block pair masses along the reduced history: the relative Gronwall bound for regions

`PairRRelR` bounds the total pair mass `r'_k = ∑_Bm₂(V'_k(B)_{ab})`. The block bounds need the
masses of the single blocks carrying `ab` parts (the blocks of `a` and of `b`, which may be
different at every scale). By `Obs2.MuChainAB.rABX_flow` / `PtCorr2.rRX_flow` the pair mass
`r'_k(X)` of any `M`-polymer `X` obeys, for `j_x ≤ k < M`, the same relative recursion as the total
mass (leading factor `1 − 𝔫^{(2)}_k`, the same tadpole increments `tadO`), with the region error
`errABX2`. Hence:

* **`PairErrRelRX c_e c_a`** (named input; the region version of `PairErrRelR2`): for every
  `j_x ≤ M ≤ N_h + 1` and every `M`-polymer `X`,
  `‖err'_k(X)‖ ≤ s_k‖β_{a,k+1}‖ + ∑_{j≤i≤k}η_{ik}‖r'_i(X)‖` (`k < M`), `∑s ≤ c_e‖M_j‖ǧ_j`,
  `∑∑(64/49)^{k+1-i}η_{ik} ≤ c_a`;
* **`pairRRelRX_of_err2`** (copy of `pairRRelR_of_err2` with a general top `M` and region `X`,
  via `Obs2.rel_gronwall_geomR`): `‖r'_k(X)‖ ≤ crErr2·‖M_j‖ǧ_j·‖β_{a,k}‖`, `j_x ≤ k ≤ M`,
  **uniformly in `X`**, with the same constant `crErr2` as the total mass;
* **`pairBlockMass_of_err2`**: for every `k ∈ [j_x, N_h + 1]` and every `k`-block `B`,
  `‖m₂(V'_k(B)_{ab})‖ ≤ crErr2·‖M_j‖ǧ_j·‖β_{a,k}‖` (take `X = B`, `M = k`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `r'_k(X)` along the reduced history from `j_x`. -/
def hRRX (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (X : Finset (Lam 2 L N)) (k : ℕ) : ℂ :=
  PtCorr2.rRX (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) X k

/-- The error `err'_k(X)` of the region flow along the reduced history. -/
def hErrRX (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (X : Finset (Lam 2 L N)) (k : ℕ) : ℂ :=
  Obs2.errABX2 (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) X (Obs.coal L (0 : Lam 2 L N) x) k

/-- **Named input (the error of the region flow, `r'(X)`-proportional parts allowed).** -/
def PairErrRelRX (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (ce ca : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ M, Obs.coal L (0 : Lam 2 L N) x ≤ M → M ≤ Nh + 1 → ∀ X : Finset (Lam 2 L N), IsPolymer M X →
    ∃ (s : ℕ → ℝ) (η : ℕ → ℕ → ℝ), (∀ k, 0 ≤ s k) ∧ (∀ i k, 0 ≤ η i k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
        ‖hErrRX R m b μ₀ oR x X k‖ ≤ s k * ‖hBeta R m b μ₀ x (k + 1)‖ +
          ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, η i k * ‖hRRX R m b μ₀ oR x X i‖) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M, s k ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k ≤ ca

/-- **Conclusion: the pair masses of all regions are relatively small.** -/
def PairRRelRX (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ M, Obs.coal L (0 : Lam 2 L N) x ≤ M → M ≤ Nh + 1 → ∀ X : Finset (Lam 2 L N), IsPolymer M X →
    ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k ≤ M →
      ‖hRRX R m b μ₀ oR x X k‖ ≤
        cr * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖hBeta R m b μ₀ x k‖

set_option maxHeartbeats 2000000 in
/-- **The region masses from the region error** (relative Gronwall, `Obs2.rel_gronwall_geomR`).
Copy of `pairRRelR_of_err2` with a general top scale `M` and region `X`. -/
theorem pairRRelRX_of_err2 {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce cδ G2 ct B' ca : ℝ} (hce : 0 ≤ ce)
    (hcδ : 0 ≤ cδ) (hct : 0 ≤ ct) (hB' : 0 ≤ B') (hL : 49 ≤ L)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hG2 : ∑ k ∈ range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ G2)
    (hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1)
    (hcg : ∀ i ≤ Nh, ct * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤ 1)
    (hRd : PairSectRed R Nh m b μ₀ oR)
    (hV0 : ∀ x : Lam 2 L N, ∀ B, ((oR x).V B : Obs.SA .two (Lam 2 L N)).ab = 0)
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
    (hE : PairErrRelRX R Nh m b μ₀ lam oR ce ca) :
    PairRRelRX R Nh m b μ₀ lam oR (crErr2 ce cδ G2 ct B' ca) := by
  intro x hx h1 hj M hjM hMN X hX
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨s, η, hs0, hη0, hk, hsum, hηsum⟩ := hE x hx h1 hj M hjM hMN X hX
  rw [← hjd] at hk hsum hηsum
  obtain ⟨ho', -, hab', -⟩ := hRd x hx h1 hj
  rw [← hjd] at hab'
  have hr0 : hRRX R m b μ₀ oR x X j = 0 := PtCorr2.rRX_self (hV0 x) X
  have HB := hBeta_rel_of R hN hb x (hrel x hx) (hn x hx) (htop x hx h1 hj)
  set εf : ℕ → ℝ := fun k => if k < Nh then 8 / 7 * (cδ * (t k).1 ^ 2) else 1 / 7 with hεf
  have hε0 : ∀ k, 0 ≤ εf k := fun k => by
    simp only [hεf]; split_ifs
    · exact mul_nonneg (by norm_num) (mul_nonneg hcδ (sq_nonneg _))
    · norm_num
  set g : ℕ → ℝ := fun i => max (t i).1 0 with hgd
  have hgle : ∀ i ≤ Nh, g i = (t i).1 := fun i hi => max_eq_left (hg i hi)
  have hflow : ∀ k, j ≤ k → k < M → hRRX R m b μ₀ oR x X (k + 1) =
      (1 - nn2 R (ptsX x) (zV b) m b μ₀ k) * hRRX R m b μ₀ oR x X k -
        ∑ i ∈ range k, ((if j ≤ i then hRRX R m b μ₀ oR x X i else 0) - hRRX R m b μ₀ oR x X k) *
          tadO R m b μ₀ x i k - hErrRX R m b μ₀ oR x X k := by
    intro k hk1 hk2
    have h := PtCorr2.rRX_flow (R := R.withMsq m) (P := ptsX x) (o' := oR x) (t := t) hab'
      (hW0 x) hX hk1 hk2
    rw [PtCorr2.frakN2_hR_eq ho' (Obs2.obsInit_isObs .two (zV b) (ptsX x))] at h
    have hti : ∀ i, Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t) i k = tadO R m b μ₀ x i k := fun i =>
      PtCorr2.tadInc2_hR_eq ho' (Obs2.obsInit_isObs .two (zV b) (ptsX x)) i k
    unfold Obs2.driftABX at h
    simp only [hti] at h
    unfold hRRX hErrRX
    rw [h]
    rfl
  have hL' : (49 : ℝ) ≤ L := by exact_mod_cast hL
  have hG := Obs2.rel_gronwall_geomR (fun k => hRRX R m b μ₀ oR x X k)
    (fun k => hBeta R m b μ₀ x k)
    (nn2 R (ptsX x) (zV b) m b μ₀) (err2 R (ptsX x) (zV b) m b μ₀)
    (fun k => hErrRX R m b μ₀ oR x X k) (fun i k => tadO R m b μ₀ x i k) s εf g η ct B'
    (2 / (L : ℝ)) j M h1 hr0 hs0 hε0 hη0 hct hB' (by positivity)
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL')
    (fun k hk1 hk2 => hflow k hk1 hk2)
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
  -- the weights (top `M ≤ N_h + 1`)
  have e3 : ∑ i ∈ Finset.Ico j Nh, (t i).1 ^ 2 ≤ G2 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => sq_nonneg _) hG2
    intro i hi; rw [Finset.mem_range]; exact (mem_Ico.1 hi).2
  have hεsumN : ∑ i ∈ Finset.Ico j (Nh + 1), εf i ≤ 8 / 7 * cδ * G2 + 1 / 7 := by
    rw [Finset.sum_Ico_succ_top (by omega)]
    have e1 : εf Nh = 1 / 7 := by simp [hεf]
    have e2 : ∑ i ∈ Finset.Ico j Nh, εf i = 8 / 7 * cδ * ∑ i ∈ Finset.Ico j Nh, (t i).1 ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      simp only [hεf, if_pos (mem_Ico.1 hi).2]; ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left e3 (show 0 ≤ 8 / 7 * cδ by positivity)
    linarith
  have hεsum : ∑ i ∈ Finset.Ico j M, εf i ≤ 8 / 7 * cδ * G2 + 1 / 7 :=
    le_trans (sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hMN)
      fun i _ _ => hε0 i) hεsumN
  set hA : ℕ → ℝ := fun l => 64 / 49 * B' * ct * g l ^ 2 + εf l with hAd
  have hA0 : ∀ l, 0 ≤ hA l := fun l =>
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB') hct) (sq_nonneg _)) (hε0 l)
  have hhsumN : ∑ l ∈ Ico j (Nh + 1), (if l + 1 < Nh + 1 then hA l else 0) ≤
      (64 / 49 * B' * ct + 8 / 7 * cδ) * G2 := by
    rw [Finset.sum_Ico_succ_top (by omega), if_neg (by omega), add_zero]
    have e2 : ∑ l ∈ Finset.Ico j Nh, (if l + 1 < Nh + 1 then hA l else 0) =
        (64 / 49 * B' * ct + 8 / 7 * cδ) * ∑ i ∈ Finset.Ico j Nh, (t i).1 ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := (mem_Ico.1 hi).2
      simp only [hAd, if_pos (show i + 1 < Nh + 1 by omega), hεf, if_pos hi', hgle i hi'.le]; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)
  have hhsum : ∑ l ∈ Ico j M, (if l + 1 < M then hA l else 0) ≤
      (64 / 49 * B' * ct + 8 / 7 * cδ) * G2 := by
    refine le_trans ?_ hhsumN
    refine le_trans (sum_le_sum fun l hl => ?_) (sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_right hMN) fun l _ _ => by split_ifs <;> simp [hA0 l])
    split_ifs with h1 h2
    · exact le_rfl
    · omega
    · exact hA0 l
    · exact le_rfl
  have hW : 2 * (∑ i ∈ Ico j M, εf i +
      ∑ k ∈ Ico j M, ∑ i ∈ Icc j k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k +
      1 / 16 * ∑ l ∈ Ico j M, (if l + 1 < M then 64 / 49 * B' * ct * g l ^ 2 + εf l
        else 0) + 64 / 49 / 16) ≤
      2 * ((8 / 7 * cδ * G2 + 1 / 7) + ca + 1 / 16 * ((64 / 49 * B' * ct + 8 / 7 * cδ) * G2) +
        64 / 49 / 16) := by
    have := mul_le_mul_of_nonneg_left hhsum (show (0 : ℝ) ≤ 1 / 16 by norm_num)
    linarith
  intro k hk1 hk2
  refine (hG k hk1 hk2).trans ?_
  have hS1 : 2 * ∑ i ∈ Finset.Ico j M, s i ≤
      2 * (ce * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) := by
    linarith
  have hP1 := Real.exp_le_exp.2 hW
  have := mul_le_mul hS1 hP1 (Real.exp_pos _).le
    (by have := hg j hj; positivity)
  have := mul_le_mul_of_nonneg_right this (norm_nonneg (hBeta R m b μ₀ x k))
  refine this.trans (le_of_eq ?_)
  unfold crErr2; ring

/-- **The mass of every block carrying `ab` parts** (in particular the blocks of `a` and `b`):
for `k ∈ [j_x, N_h + 1]` and every `k`-block `B`,
`‖m₂(V'_k(B)_{ab})‖ ≤ c_r‖M_j‖ǧ_j‖β_{a,k}‖`. -/
theorem pairBlockMass_of_relRX {Nh : ℕ} {m b μ₀ : ℝ} {lam : ℕ → ℂ}
    {oR : Lam 2 L N → Obs2.ObsSt .two L N} {cr : ℝ} (h : PairRRelRX R Nh m b μ₀ lam oR cr)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) {k : ℕ} (hk1 : Obs.coal L (0 : Lam 2 L N) x ≤ k)
    (hk2 : k ≤ Nh + 1) (c : Fin 2 → ℕ) (hne : (blockSet (L := L) (N := N) k c).Nonempty) :
    ‖Obs.LocObs.mass2 (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k c : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      cr * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖hBeta R m b μ₀ x k‖ := by
  have := h x hx h1 hj k hk1 hk2 (blockSet (L := L) (N := N) k c) (isPolymer_blockSet k c) k hk1
    le_rfl
  unfold hRRX at this
  rwa [PtCorr2.rRX_blockSet k c hne] at this

/-- **`pairRRelRX_of_err2` + `pairBlockMass_of_relRX`.** -/
theorem pairBlockMass_of_err2 {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce cδ G2 ct B' ca : ℝ} (hce : 0 ≤ ce)
    (hcδ : 0 ≤ cδ) (hct : 0 ≤ ct) (hB' : 0 ≤ B') (hL : 49 ≤ L)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hG2 : ∑ k ∈ range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ G2)
    (hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1)
    (hcg : ∀ i ≤ Nh, ct * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤ 1)
    (hRd : PairSectRed R Nh m b μ₀ oR)
    (hV0 : ∀ x : Lam 2 L N, ∀ B, ((oR x).V B : Obs.SA .two (Lam 2 L N)).ab = 0)
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
    (hE : PairErrRelRX R Nh m b μ₀ lam oR ce ca)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) {k : ℕ} (hk1 : Obs.coal L (0 : Lam 2 L N) x ≤ k)
    (hk2 : k ≤ Nh + 1) (c : Fin 2 → ℕ) (hne : (blockSet (L := L) (N := N) k c).Nonempty) :
    ‖Obs.LocObs.mass2 (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k c : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      crErr2 ce cδ G2 ct B' ca * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖hBeta R m b μ₀ x k‖ :=
  pairBlockMass_of_relRX R (pairRRelRX_of_err2 R hN m hb lam oR hce hcδ hct hB' hL hg hG2 hgm hcg
    hRd hV0 hW0 hrel hn hnB htop ht hE) x hx h1 hj hk1 hk2 c hne

end Traj

end

end Spin2
