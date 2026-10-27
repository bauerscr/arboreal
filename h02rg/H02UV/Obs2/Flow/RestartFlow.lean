import Obs2.Flow.RestartChain
import Obs2.Flow.RestartRec
import Obs2.Flow.BlockFlowE

/-!
# The restarted `μ^{(2)}` flow in `ℓ¹` and the restart recursion (B3, T4)

Copy of the `ℓ¹` share machinery of `Obs2/Flow/BlockFlowE` along a `MuChain2F` (the flow restarted at
scale `m` from a general datum):

* `shareErrL1_2F` (`E_j = ∑_{B_+}|errF_j(B_+)|`), `shPr2F` (product parts `G_j(B_+;0) +
  prodIncF_j(B_+)`), `shInit2` (`∑_{B_+}|wInitX2|`, the tadpole of the initial `𝒲_m`);
* `shareErrL1_2F_le`, `MuChain2F.shareDev2_succ_leF`, **`MuChain2F.norm_betaTot2_succ_le`**
  (the upper bound `b_{j+1} ≤ |1 − 𝔫F_j|b_j + E_j`), `drift2_step_l1F`, **`hE2_rawF`**:
  `E_j ≤ Kt_j + ∑_{m≤k<j}|tadInc2 k j|∑_{k≤i<j}(|𝔫F_i|A_i + E_i) + Pr_j + Init_j`;
* **`MuChain2F.relRecK2`**: `RelInK` for the sequences shifted to start at `m`
  (`b_i = |β_{m+i}|`, …, `Pr_i = shPr2F_{m+i}` for `i > 0`, `X_i = shInit2_{m+i}` plus the
  datum's own `𝒲` mass `shPr2F_m` at `i = 0`) gives `RelRecK`;
* **`MuChain2F.restart_flow2`**: the restart estimate along the chain,
  `|β_{m+j}| ≤ (|β_m| + (1/8 + 10c_t)M₀) ∏_{k<j}|1 − 𝔫F_{m+k}|`, together with the conclusions of
  `RelRecK.close` (the `𝒲`/`K` sizes in the envelope).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L]

/-- The `ℓ¹` error of the restarted per-block flow at step `j`. -/
def shareErrL1_2F (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (m j : ℕ) : ℝ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    ‖shareErr2F P C V W K m j (blockSet (L := L) (N := N) (j + 1) c')‖

/-- The `ℓ¹` product parts of the restarted flow. -/
def shPr2F (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (m j : ℕ) : ℝ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    ‖wTadX j mass2L (W j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
      muProdIncX2F P C V W m j (blockSet (L := L) (N := N) (j + 1) c')‖

/-- The `ℓ¹` tadpole of the initial `𝒲_m` at step `j`. -/
def shInit2 (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (W : ℕ → OFam .two d L N) (m j : ℕ) : ℝ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    ‖wInitX2 C W m j (blockSet (L := L) (N := N) (j + 1) c')‖

theorem shareErrL1_2F_le (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (m j : ℕ) (hjN : j + 1 < N) :
    shareErrL1_2F P C V W K m j ≤ shKt2 K j +
      ∑ k ∈ Ico m j, ‖tadInc2 P C V k j‖ *
        ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          ‖betaX2 k (V k) (blockSet (L := L) (N := N) (j + 1) c') -
            betaX2 j (V j) (blockSet (L := L) (N := N) (j + 1) c')‖ +
      shPr2F P C V W m j + shInit2 C W m j := by
  unfold shareErrL1_2F
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖shareErr2F P C V W K m j (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
          ‖mass2 (EthO (C j) (Q2O P j (K j) b) : SA .two (Lam d L N)).a‖ +
        ∑ k ∈ Ico m j, ‖tadInc2 P C V k j‖ *
          ‖betaX2 k (V k) (blockSet (L := L) (N := N) (j + 1) c') -
            betaX2 j (V j) (blockSet (L := L) (N := N) (j + 1) c')‖ +
        ‖wTadX j mass2L (W j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
          muProdIncX2F P C V W m j (blockSet (L := L) (N := N) (j + 1) c')‖ +
        ‖wInitX2 C W m j (blockSet (L := L) (N := N) (j + 1) c')‖ := by
    intro c' _
    rw [shareErr2F]
    set X := blockSet (L := L) (N := N) (j + 1) c'
    have e : muQX2 P C K j X + (muDriftX2F P C V m j X + wTadX j mass2L (W j) X 0 +
        muProdIncX2F P C V W m j X + wInitX2 C W m j X) =
        muQX2 P C K j X + muDriftX2F P C V m j X +
          (wTadX j mass2L (W j) X 0 + muProdIncX2F P C V W m j X) + wInitX2 C W m j X := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) ?_)) le_rfl)) le_rfl)
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
    rw [norm_mul, mul_comm]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_blockIdx_succ j
    (fun b => ‖mass2 (EthO (C j) (Q2O P j (K j) b) : SA .two (Lam d L N)).a‖), sum_comm]
  refine add_le_add (add_le_add (add_le_add ?_ (le_of_eq (sum_congr rfl fun k _ => by
    rw [mul_sum]))) le_rfl) le_rfl
  exact sum_norm_EthQ_le P j (C j) (K j) hjN mass2L (locMass_two P.a)

namespace MuChain2F

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {K : ℕ → OAct .two d L N} {m n : ℕ} (H : MuChain2F P C V W K m n)
include H

/-- `D_{j+1} ≤ |1 − 𝔫F_j| D_j + 2 E_j`. -/
theorem shareDev2_succ_leF {j : ℕ} (hmj : m ≤ j) (hj : j < n) :
    shareDev2 P.a (j + 1) (V (j + 1)) ≤
      ‖1 - frakN2F P C V m j‖ * shareDev2 P.a j (V j) + 2 * shareErrL1_2F P C V W K m j := by
  classical
  set β := betaTot2 (L := L) (N := N) j (V j)
  set a' := 1 - frakN2F P C V m j
  set e : (Fin d → ℕ) → ℂ := fun c' =>
    shareErr2F P C V W K m j (blockSet (L := L) (N := N) (j + 1) c')
  set δ : (Fin d → ℕ) → ℂ := fun b => mass2 (V j b : SA .two (Lam d L N)).a -
    (if P.a ∈ blockSet (L := L) (N := N) j b then β else 0)
  have hE0 : 0 ≤ shareErrL1_2F P C V W K m j := sum_nonneg fun _ _ => norm_nonneg _
  have key : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      mass2 (V (j + 1) c' : SA .two (Lam d L N)).a -
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          betaTot2 (L := L) (N := N) (j + 1) (V (j + 1)) else 0) =
      a' * ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), δ b - e c' +
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          ∑ c'' ∈ blockIdx (L := L) (N := N) (j + 1), e c'' else 0) := by
    intro c' hc'
    rw [H.share2_flow_exactF hmj hj hc', H.betaTot2_succ_eqF hmj hj]
    have hX : betaX2 j (V j) (blockSet (L := L) (N := N) (j + 1) c') =
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), δ b +
          (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then β else 0) := by
      rw [betaX2, ← sum_ite_mem_blockSet P.a j c' β, ← sum_add_distrib]
      exact sum_congr rfl fun b _ => by simp only [δ]; ring
    rw [hX]
    split_ifs <;> simp only [e, a'] <;> ring
  unfold shareDev2
  rw [sum_congr rfl fun c' hc' => by rw [key c' hc']]
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖a' * ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), δ b - e c' +
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          ∑ c'' ∈ blockIdx (L := L) (N := N) (j + 1), e c'' else 0)‖ ≤
      ‖a'‖ * ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), ‖δ b‖ + ‖e c'‖ +
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then shareErrL1_2F P C V W K m j
          else 0) := by
    intro c' _
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ?_ le_rfl)) ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    · split_ifs
      · exact norm_sum_le _ _
      · rw [norm_zero]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_blockIdx_succ j (fun b => ‖δ b‖)]
  have h2 := norm_sum_ite_mem_le P.a (j + 1) (shareErrL1_2F P C V W K m j) hE0
  have h3 : ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1), ‖e c'‖ = shareErrL1_2F P C V W K m j := rfl
  rw [h3]
  have h4 : ∑ b ∈ blockIdx (L := L) (N := N) j, ‖δ b‖ = shareDev2 P.a j (V j) := rfl
  rw [h4]
  linarith

/-- **The upper bound of the coupling**: `b_{j+1} ≤ |1 − 𝔫F_j| b_j + E_j`. -/
theorem norm_betaTot2_succ_le {j : ℕ} (hmj : m ≤ j) (hj : j < n) :
    ‖betaTot2 (L := L) (N := N) (j + 1) (V (j + 1))‖ ≤
      ‖1 - frakN2F P C V m j‖ * ‖betaTot2 (L := L) (N := N) j (V j)‖ +
        shareErrL1_2F P C V W K m j := by
  rw [H.betaTot2_succ_eqF hmj hj]
  refine (norm_sub_le _ _).trans (add_le_add (le_of_eq ?_) (norm_sum_le _ _))
  rw [norm_mul, mul_comm]

theorem betaX2_succ_eqF {i : ℕ} (hmi : m ≤ i) (hi : i < n) {X : Finset (Lam d L N)}
    (hX : IsPolymer (i + 1) X) :
    betaX2 (i + 1) (V (i + 1)) X = betaX2 i (V i) X * (1 - frakN2F P C V m i) -
      ∑ c'' ∈ blocks (i + 1) X,
        shareErr2F P C V W K m i (blockSet (L := L) (N := N) (i + 1) c'') := by
  unfold betaX2
  rw [sum_congr rfl fun c'' hc'' =>
    H.share2_flow_exactF hmi hi (mem_blockIdx_of_mem_blocks hc''), sum_sub_distrib, ← sum_mul]
  congr 2
  unfold betaX2
  exact Step2.sum_blocks_succ hX _

/-- The per-step drift of the regions in `ℓ¹`, restarted flow. -/
theorem drift2_step_l1F {i k : ℕ} (hmi : m ≤ i) (hi : i < n) (hik : i + 1 ≤ k) :
    ∑ c' ∈ blockIdx (L := L) (N := N) k,
        ‖betaX2 (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) k c') -
          betaX2 i (V i) (blockSet (L := L) (N := N) k c')‖ ≤
      ‖frakN2F P C V m i‖ *
          ∑ b ∈ blockIdx (L := L) (N := N) i, ‖mass2 (V i b : SA .two (Lam d L N)).a‖ +
        shareErrL1_2F P C V W K m i := by
  have hpol : ∀ c' : Fin d → ℕ, IsPolymer (i + 1) (blockSet (L := L) (N := N) k c') := fun c' =>
    Step2.isPolymer_of_le (isPolymer_blockSet k c') (i + 1) hik
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) k,
      ‖betaX2 (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) k c') -
          betaX2 i (V i) (blockSet (L := L) (N := N) k c')‖ ≤
        ‖frakN2F P C V m i‖ * ‖betaX2 i (V i) (blockSet (L := L) (N := N) k c')‖ +
          ∑ c'' ∈ blocks (i + 1) (blockSet (L := L) (N := N) k c'),
            ‖shareErr2F P C V W K m i (blockSet (L := L) (N := N) (i + 1) c'')‖ := by
    intro c' _
    set X := blockSet (L := L) (N := N) k c'
    have e : betaX2 (i + 1) (V (i + 1)) X - betaX2 i (V i) X =
        -(betaX2 i (V i) X * frakN2F P C V m i) -
          ∑ c'' ∈ blocks (i + 1) X,
            shareErr2F P C V W K m i (blockSet (L := L) (N := N) (i + 1) c'') := by
      rw [H.betaX2_succ_eqF hmi hi (hpol c')]; ring
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
    rw [norm_neg, norm_mul, mul_comm]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have h3 := sum_norm_betaX2_le (show i ≤ k by omega) (V i)
  have h4 : ∑ c' ∈ blockIdx (L := L) (N := N) k,
      ∑ c'' ∈ blocks (i + 1) (blockSet (L := L) (N := N) k c'),
        ‖shareErr2F P C V W K m i (blockSet (L := L) (N := N) (i + 1) c'')‖ =
      shareErrL1_2F P C V W K m i :=
    sum_blockIdx_le _ hik
  rw [h4]
  have := mul_le_mul_of_nonneg_left h3 (norm_nonneg (frakN2F P C V m i))
  linarith

/-- **The unscaled split of `E_j`**, restarted flow. -/
theorem hE2_rawF {j : ℕ} (_hmj : m ≤ j) (hj : j < n) :
    shareErrL1_2F P C V W K m j ≤ shKt2 K j + ∑ k ∈ Ico m j, ‖tadInc2 P C V k j‖ *
      ∑ i ∈ Ico k j, (‖frakN2F P C V m i‖ * shA2 V i + shareErrL1_2F P C V W K m i) +
      shPr2F P C V W m j + shInit2 C W m j := by
  have hjN : j + 1 < N := by have := H.hN; omega
  refine (shareErrL1_2F_le P C V W K m j hjN).trans
    (add_le_add (add_le_add (add_le_add le_rfl ?_) le_rfl) le_rfl)
  refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hk' := mem_Ico.1 hk
  refine le_trans ?_ (sum_le_sum fun i hi => H.drift2_step_l1F (k := j + 1)
    (by have := (mem_Ico.1 hi).1; omega) (by have := (mem_Ico.1 hi).2; omega)
    (by have := (mem_Ico.1 hi).2; omega))
  rw [sum_comm]
  exact sum_le_sum fun c' _ => norm_sub_le_sum_Ico
    (fun i => betaX2 i (V i) (blockSet (L := L) (N := N) (j + 1) c')) hk'.2.le

/-- **The restarted per-block flow gives `RelRecK`** (sequences shifted to start at `m`). -/
theorem relRecK2 {s rr θW θK G : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn : ℝ} (Tt : ℕ → ℕ → ℝ)
    (hG : ∀ i < n - m, 0 ≤ G i)
    (hTt : ∀ k j, k < j → j < n - m → ∀ i ∈ Ico k j,
      ‖tadInc2 P C V (m + k) (m + j)‖ ≤ Tt k j * G i)
    (I : RelInK (n - m) (fun i => ‖betaTot2 (L := L) (N := N) (m + i) (V (m + i))‖)
      (fun i => shA2 V (m + i)) (fun i => shareDev2 P.a (m + i) (V (m + i)))
      (fun i => shareErrL1_2F P C V W K m (m + i))
      (fun i => ‖1 - frakN2F P C V m (m + i)‖) s rr (fun i => shKt2 K (m + i))
      (fun i => if i = 0 then 0 else shPr2F P C V W m (m + i))
      (fun i => shInit2 C W m (m + i) + if i = 0 then shPr2F P C V W m m else 0)
      G (fun i => ‖frakN2F P C V m (m + i)‖)
      θW θK Tt Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn) :
    RelRecK (n - m) (fun i => ‖betaTot2 (L := L) (N := N) (m + i) (V (m + i))‖)
      (fun i => shA2 V (m + i)) (fun i => shareDev2 P.a (m + i) (V (m + i)))
      (fun i => shareErrL1_2F P C V W K m (m + i))
      (fun i => ‖1 - frakN2F P C V m (m + i)‖) s rr (fun i => shKt2 K (m + i))
      (fun i => if i = 0 then 0 else shPr2F P C V W m (m + i))
      (fun i => shInit2 C W m (m + i) + if i = 0 then shPr2F P C V W m m else 0)
      G (fun i => ‖frakN2F P C V m (m + i)‖)
      θW θK Tt Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn where
  toRelInK := I
  hb := fun _ _ => norm_nonneg _
  hD0' := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hA0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hE0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hDstep := fun j hj => by
    have := H.shareDev2_succ_leF (j := m + j) (by omega) (by omega)
    simpa only [add_assoc] using this
  hbup := fun j hj => by
    have := H.norm_betaTot2_succ_le (j := m + j) (by omega) (by omega)
    simpa only [add_assoc] using this
  hA := fun j _ => sum_norm_share2_le P.a (m + j) (V (m + j))
  hE := by
    intro j hj
    refine (H.hE2_rawF (j := m + j) (by omega) (by omega)).trans ?_
    have hsplit : shPr2F P C V W m (m + j) + shInit2 C W m (m + j) =
        (if j = 0 then 0 else shPr2F P C V W m (m + j)) +
          (shInit2 C W m (m + j) + if j = 0 then shPr2F P C V W m m else 0) := by
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · simp only [add_zero, if_true]; ring
      · rw [if_neg (by omega), if_neg (by omega)]; ring
    have hdr : ∑ k ∈ Ico m (m + j), ‖tadInc2 P C V k (m + j)‖ *
        ∑ i ∈ Ico k (m + j), (‖frakN2F P C V m i‖ * shA2 V i + shareErrL1_2F P C V W K m i) ≤
        ∑ k ∈ range j, Tt k j * ∑ i ∈ Ico k j, G i *
          (‖frakN2F P C V m (m + i)‖ * shA2 V (m + i) + shareErrL1_2F P C V W K m (m + i)) := by
      rw [sum_Ico_eq_sum_range, show m + j - m = j by omega]
      refine sum_le_sum fun k hk => ?_
      have hkj := mem_range.1 hk
      have e : ∑ i ∈ Ico (m + k) (m + j),
          (‖frakN2F P C V m i‖ * shA2 V i + shareErrL1_2F P C V W K m i) =
          ∑ i ∈ Ico k j, (‖frakN2F P C V m (m + i)‖ * shA2 V (m + i) +
            shareErrL1_2F P C V W K m (m + i)) := by
        rw [sum_Ico_add (fun i => ‖frakN2F P C V m i‖ * shA2 V i +
          shareErrL1_2F P C V W K m i) k j m, add_comm k m, add_comm j m]
      rw [e, mul_sum, mul_sum]
      refine sum_le_sum fun i hi => ?_
      have hi' := mem_Ico.1 hi
      have hGi := hG i (by omega)
      have hT := hTt k j hkj (by omega) i hi
      set x := ‖frakN2F P C V m (m + i)‖ * shA2 V (m + i) + shareErrL1_2F P C V W K m (m + i)
      have hx0 : 0 ≤ x := by
        have h2 : 0 ≤ shA2 V (m + i) := sum_nonneg fun _ _ => norm_nonneg _
        have h3 : 0 ≤ shareErrL1_2F P C V W K m (m + i) := sum_nonneg fun _ _ => norm_nonneg _
        have := norm_nonneg (frakN2F P C V m (m + i))
        positivity
      calc ‖tadInc2 P C V (m + k) (m + j)‖ * x ≤ (Tt k j * G i) * x :=
            mul_le_mul_of_nonneg_right hT hx0
        _ = Tt k j * (G i * x) := by ring
    linarith

/-- **The restart estimate along the restarted chain**: the conclusions of `RelRecK.close`
and `|β_{m+j}| ≤ (|β_m| + (1/8 + 10c_t)M₀) ∏_{k<j}|1 − 𝔫F_{m+k}|`. -/
theorem restart_flow2 {s rr θW θK G : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn : ℝ} (Tt : ℕ → ℕ → ℝ)
    (hG : ∀ i < n - m, 0 ≤ G i)
    (hTt : ∀ k j, k < j → j < n - m → ∀ i ∈ Ico k j,
      ‖tadInc2 P C V (m + k) (m + j)‖ ≤ Tt k j * G i)
    (I : RelInK (n - m) (fun i => ‖betaTot2 (L := L) (N := N) (m + i) (V (m + i))‖)
      (fun i => shA2 V (m + i)) (fun i => shareDev2 P.a (m + i) (V (m + i)))
      (fun i => shareErrL1_2F P C V W K m (m + i))
      (fun i => ‖1 - frakN2F P C V m (m + i)‖) s rr (fun i => shKt2 K (m + i))
      (fun i => if i = 0 then 0 else shPr2F P C V W m (m + i))
      (fun i => shInit2 C W m (m + i) + if i = 0 then shPr2F P C V W m m else 0)
      G (fun i => ‖frakN2F P C V m (m + i)‖)
      θW θK Tt Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn) :
    (∀ j ≤ n - m,
      ‖betaTot2 (L := L) (N := N) (m + j) (V (m + j))‖ ≤
        (‖betaTot2 (L := L) (N := N) m (V m)‖ +
          (1 / 8 + 10 * (cK * k₀ / (s 0 * M₀) + xh + tn)) * M₀) *
          ∏ k ∈ range j, ‖1 - frakN2F P C V m (m + k)‖) ∧
    (∀ j ≤ n - m,
      Wb j (cW * rr j * (2 * s j * rkEnv M₀ (fun i => ‖1 - frakN2F P C V m (m + i)‖) j)) ∧
      Kb j ((1 / 2) ^ j * k₀ + 15 * cW * Bk * rr j ^ 2 *
        (s j * rkEnv M₀ (fun i => ‖1 - frakN2F P C V m (m + i)‖) j))) := by
  have R := H.relRecK2 Tt hG hTt I
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h := R.restart_le hj
    simpa only [add_zero] using h
  · obtain ⟨-, -, hW, hK⟩ := (R.close j hj).1 j le_rfl
    exact ⟨hW, hK⟩

end MuChain2F

end

end Obs2
