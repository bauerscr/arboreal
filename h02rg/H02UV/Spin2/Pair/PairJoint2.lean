import Spin2.Pair.PairShareAB1
import Obs2.Est.ErrABX

/-!
# The joint scale-by-scale induction for the region masses (the skeleton)

The region error `err'_k(X)` at scale `k` depends on the `V'`-block sizes at the scales `≤ k`
(through `K'`, `𝒲'`, `M₄`, the gradient part), and these depend on the block masses at the scales
`≤ k`, which are bounded by the relative Gronwall bound of the region flow from the errors at the
scales `< k`. The circularity is broken by one induction over the scale `n`:

* **`regionMass_of_err`**: the region Gronwall bound for one point `x`, one top `M` and one
  `M`-polymer `X` from error bounds on `Ico j_x M` only (copy of `pairRRelRX_of_err2`, which needs
  the errors of all regions);
* **`pairJoint_x`** (the induction): with a predicate `VB n` ("the `V'` block sizes are fine on
  `[j_x, n)`") and target masses `ρ̄_k = crErr2·‖M_j‖ǧ_j·‖β_{a,k}‖`,
  - `VB j_x`,
  - **(V-step)** `VB n` and the block masses `≤ ρ̄` on `[j_x, n]` ⇒ `VB (n+1)` (`n ≤ N_h`),
  - **(E-step)** `VB n` and the block masses `≤ ρ̄` on `[j_x, n)` ⇒ the region error bounds
    `‖err'_k(X)‖ ≤ s_k‖β_{k+1}‖ + ∑η_{ik}‖r'_i(X)‖` for all `M ≤ n`, `M`-polymers `X`,
    `k ∈ [j_x, M)`, with **fixed** `s`, `η` (summable as in `PairErrRelRX`),
  give `VB (N_h + 1)`, all region masses, and the region error bounds up to `N_h + 1`;
* **`PairJointStep c_e c_a`** (the two steps for every `x`, as one named input) and
  **`pairErrRelRX_of_joint`**: `PairJointStep ⇒ PairErrRelRX`;
* **`pairRRelR_of_relRX`**: the region bound at `X = Λ`, `M = N_h + 1` is the total bound
  `PairRRelR` (so `PairErrRelR2` / `PairErrSizesR3` are subsumed by the region route).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 2000000 in
/-- **The region Gronwall bound for one region** from the errors of that region on `Ico j_x M`
(copy of `pairRRelRX_of_err2`). -/
theorem regionMass_of_err {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
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
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (M : ℕ) (hjM : Obs.coal L (0 : Lam 2 L N) x ≤ M)
    (hMN : M ≤ Nh + 1) (X : Finset (Lam 2 L N)) (hX : IsPolymer M X)
    (s : ℕ → ℝ) (η : ℕ → ℕ → ℝ) (hs0 : ∀ k, 0 ≤ s k) (hη0 : ∀ i k, 0 ≤ η i k)
    (hk : ∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
        ‖hErrRX R m b μ₀ oR x X k‖ ≤ s k * ‖hBeta R m b μ₀ x (k + 1)‖ +
          ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, η i k * ‖hRRX R m b μ₀ oR x X i‖)
    (hsum : ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M, s k ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1)
    (hηsum : ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k ≤
          ca) :
    ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k ≤ M →
      ‖hRRX R m b μ₀ oR x X k‖ ≤
        crErr2 ce cδ G2 ct B' ca * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖hBeta R m b μ₀ x k‖ := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
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

/-- The region masses up to scale `n`: `‖r'_k(X)‖ ≤ c_r‖M_j‖ǧ_j‖β_{a,k}‖` for all `M`-polymers `X`,
`j_x ≤ k ≤ M ≤ n`. -/
def PairMassUpTo (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (cr : ℝ)
    (x : Lam 2 L N) (n : ℕ) : Prop :=
  ∀ M, Obs.coal L (0 : Lam 2 L N) x ≤ M → M ≤ n → ∀ X : Finset (Lam 2 L N), IsPolymer M X →
    ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k ≤ M →
      ‖hRRX R m b μ₀ oR x X k‖ ≤
        cr * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖hBeta R m b μ₀ x k‖

/-- The region error bounds up to scale `n` with fixed sequences `s`, `η`. -/
def PairErrUpTo (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (s : ℕ → ℝ)
    (η : ℕ → ℕ → ℝ) (x : Lam 2 L N) (n : ℕ) : Prop :=
  ∀ M, Obs.coal L (0 : Lam 2 L N) x ≤ M → M ≤ n → ∀ X : Finset (Lam 2 L N), IsPolymer M X →
    ∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
      ‖hErrRX R m b μ₀ oR x X k‖ ≤ s k * ‖hBeta R m b μ₀ x (k + 1)‖ +
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, η i k * ‖hRRX R m b μ₀ oR x X i‖

/-- **The joint induction for one point `x`.** From the base `VB j_x`, the `V`-step and the
`E`-step (each using only the scales below), all region masses and region errors up to
`N_h + 1`. -/
theorem pairJoint_x {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce cδ G2 ct B' ca cr : ℝ}
    (hce : 0 ≤ ce) (hcδ : 0 ≤ cδ) (hct : 0 ≤ ct) (hB' : 0 ≤ B') (hL : 49 ≤ L)
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
    (hcr : crErr2 ce cδ G2 ct B' ca ≤ cr)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    (VB : ℕ → Prop) (s : ℕ → ℝ) (η : ℕ → ℕ → ℝ) (hs0 : ∀ k, 0 ≤ s k) (hη0 : ∀ i k, 0 ≤ η i k)
    (hsum : ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), s k ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1)
    (hηsum : ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k ≤
          ca)
    (hVB0 : VB (Obs.coal L (0 : Lam 2 L N) x))
    (hVstep : ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
      PairMassUpTo R m b μ₀ lam oR cr x n → VB (n + 1))
    (hEstep : ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
      (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') → PairErrUpTo R m b μ₀ oR s η x n) :
    VB (Nh + 1) ∧ PairMassUpTo R m b μ₀ lam oR cr x (Nh + 1) ∧
      PairErrUpTo R m b μ₀ oR s η x (Nh + 1) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hG0 : 0 ≤ ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 :=
    mul_nonneg (norm_nonneg _) (hg j hj)
  -- monotonicity of the mass statement in the top scale
  have hmono : ∀ n n', n ≤ n' → PairMassUpTo R m b μ₀ lam oR cr x n' →
      PairMassUpTo R m b μ₀ lam oR cr x n := fun n n' h H M h1 h2 => H M h1 (h2.trans h)
  have key : ∀ d, j + d ≤ Nh + 1 → VB (j + d) ∧ PairMassUpTo R m b μ₀ lam oR cr x (j + d) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨hVB0, fun M hM1 hM2 X hX k hk1 hk2 => ?_⟩
      obtain rfl : k = j := by omega
      have h0 : hRRX R m b μ₀ oR x X j = 0 := PtCorr2.rRX_self (hV0 x) X
      rw [h0, norm_zero]
      have : 0 ≤ cr := (show 0 ≤ crErr2 ce cδ G2 ct B' ca by
        unfold crErr2; exact mul_nonneg (mul_nonneg (by norm_num) hce) (Real.exp_pos _).le).trans hcr
      have := mul_nonneg (mul_nonneg this hG0) (norm_nonneg (hBeta R m b μ₀ x j))
      simpa [mul_assoc] using this
    | succ d ih =>
      intro hd
      obtain ⟨hVB, hMs⟩ := ih (by omega)
      have hVB' : VB (j + d + 1) := hVstep (j + d) (by omega) (by omega) hVB hMs
      have hE := hEstep (j + d + 1) (by omega) (by omega) hVB'
        (fun n' hn' => hmono n' (j + d) (by omega) hMs)
      refine ⟨hVB', fun M hM1 hM2 X hX k hk1 hk2 => ?_⟩
      rcases Nat.lt_or_ge M (j + d + 1) with hlt | hge
      · exact hMs M hM1 (by omega) X hX k hk1 hk2
      · obtain rfl : M = j + d + 1 := by omega
        have hsumM : ∑ k ∈ Finset.Ico j (j + d + 1), s k ≤
            ce * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 :=
          le_trans (sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hd)
            fun k _ _ => hs0 k) hsum
        have hηM : ∑ k ∈ Finset.Ico j (j + d + 1),
            ∑ i ∈ Finset.Icc j k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k ≤ ca :=
          le_trans (sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hd)
            fun k _ _ => sum_nonneg fun i _ => mul_nonneg (by positivity) (hη0 i k)) hηsum
        have hR := regionMass_of_err R hN m hb lam oR hce hcδ hct hB' hL hg hG2 hgm hcg hRd hV0
          hW0 hrel hn hnB htop ht x hx h1 hj (j + d + 1) hM1 hd X hX s η hs0 hη0
          (hE (j + d + 1) hM1 le_rfl X hX) hsumM hηM k hk1 hk2
        refine hR.trans ?_
        have := mul_nonneg hG0 (norm_nonneg (hBeta R m b μ₀ x k))
        have h' := mul_le_mul_of_nonneg_right hcr this
        simpa [mul_assoc] using h'
  obtain ⟨hVB, hMs⟩ := key (Nh + 1 - j) (by omega)
  rw [show j + (Nh + 1 - j) = Nh + 1 by omega] at hVB hMs
  refine ⟨hVB, hMs, hEstep (Nh + 1) (by omega) le_rfl hVB fun n' hn' => hmono n' (Nh + 1)
    hn'.le hMs⟩

/-- **Named input: the two forward steps of the joint induction**, for every point `x`: a
predicate `VB` on the scales (the `V'` block sizes on `[j_x, n)`), fixed error sequences `s`, `η`
(summable), `VB j_x`, the `V`-step and the `E`-step. -/
def PairJointStep (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (ce ca cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (VB : ℕ → Prop) (s : ℕ → ℝ) (η : ℕ → ℕ → ℝ), (∀ k, 0 ≤ s k) ∧ (∀ i k, 0 ≤ η i k) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), s k ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k, (64 / 49 : ℝ) ^ (k + 1 - i) * η i k ≤
          ca ∧
      VB (Obs.coal L (0 : Lam 2 L N) x) ∧
      (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
        PairMassUpTo R m b μ₀ lam oR cr x n → VB (n + 1)) ∧
      (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
        (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
          PairErrUpTo R m b μ₀ oR s η x n)

/-- **`PairErrRelRX` and `PairRRelRX` from the joint induction.** -/
theorem pairRelRX_of_joint {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) {b μ₀ : ℝ} (hb : 0 < b)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce cδ G2 ct B' ca cr : ℝ}
    (hce : 0 ≤ ce) (hcδ : 0 ≤ cδ) (hct : 0 ≤ ct) (hB' : 0 ≤ B') (hL : 49 ≤ L)
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
    (hcr : crErr2 ce cδ G2 ct B' ca ≤ cr) (hJ : PairJointStep R Nh m b μ₀ lam oR ce ca cr) :
    PairErrRelRX R Nh m b μ₀ lam oR ce ca ∧ PairRRelRX R Nh m b μ₀ lam oR cr := by
  refine ⟨fun x hx h1 hj M hjM hMN X hX => ?_, fun x hx h1 hj M hjM hMN X hX => ?_⟩
  · obtain ⟨VB, s, η, hs0, hη0, hsum, hηsum, hVB0, hVs, hEs⟩ := hJ x hx h1 hj
    have H := (pairJoint_x R hN m hb lam oR hce hcδ hct hB' hL hg hG2 hgm hcg hRd hV0 hW0 hrel hn
      hnB htop ht hcr x hx h1 hj VB s η hs0 hη0 hsum hηsum hVB0 hVs hEs).2.2
    refine ⟨s, η, hs0, hη0, H M hjM hMN X hX, ?_, ?_⟩
    · exact le_trans (sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hMN)
        fun k _ _ => hs0 k) hsum
    · exact le_trans (sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hMN)
        fun k _ _ => sum_nonneg fun i _ => mul_nonneg (by positivity) (hη0 i k)) hηsum
  · obtain ⟨VB, s, η, hs0, hη0, hsum, hηsum, hVB0, hVs, hEs⟩ := hJ x hx h1 hj
    exact (pairJoint_x R hN m hb lam oR hce hcδ hct hB' hL hg hG2 hgm hcg hRd hV0 hW0 hrel hn
      hnB htop ht hcr x hx h1 hj VB s η hs0 hη0 hsum hηsum hVB0 hVs hEs).2.1 M hjM hMN X hX

/-- **The total pair mass from the region masses** (`X = Λ`, `M = N_h + 1`). -/
theorem pairRRelR_of_relRX {Nh : ℕ} {m b μ₀ : ℝ} {lam : ℕ → ℂ}
    {oR : Lam 2 L N → Obs2.ObsSt .two L N} {cr : ℝ} (h : PairRRelRX R Nh m b μ₀ lam oR cr) :
    PairRRelR R Nh m b μ₀ lam oR cr := by
  intro x hx h1 hj
  have H := h x hx h1 hj (Nh + 1) (by omega) le_rfl univ (isPolymer_univ (Nh + 1))
  refine ⟨fun k hk => H k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2.le, ?_⟩
  rw [rRN_eq, (rTilN_eq R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)).2]
  exact H (Nh + 1) (by omega) le_rfl

end Traj

end

end Spin2
