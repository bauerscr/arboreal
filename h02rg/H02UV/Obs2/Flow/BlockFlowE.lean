import Obs2.Flow.MuChain2
import Obs2.Flow.RelRec

/-!
# The per-block `μ^{(2)}` flow in `ℓ¹` and the relative recursion (Case (2), sharp splitting)

Case-(2) analogue of `Obs2/Flow/BlockFlow` (`ℓ¹` share machinery), `Obs2/Flow/BlockFlow2`/`BlockFlow3`
(`RelRec` from the per-block flow relations). Along a `MuChain2`, with the shares
`c_k(B) = m₂(V_k(B)_a)`, `β_k = ∑_B c_k(B)` (`betaTot2`):

* `shareDev2` (`D_k = ∑_B |c_k(B) − β_k1_{a∈B}|`), `shareErrL1_2` (`E_j = ∑_{B_+}|err_j(B_+)|`),
  `shA2`, `shKt2` (`∑_X|m₂(K_j(X)_a)|`), `shPr2` (the product parts in `ℓ¹`);
* `MuChain2.shareDev2_succ_le` (`D_{j+1} ≤ |1−𝔫_j|D_j + 2E_j`), `norm_betaTot2_succ_ge`,
  `sum_norm_share2_le`, **`MuChain2.hE2_raw`**: `E_j ≤ Kt_j + ∑_{k<j}|tadInc2 k j|
  ∑_{k≤i<j}(|𝔫_i|A_i + E_i) + Pr_j`. In Case (2) the quartic coupling `g_k` sits inside
  `tadInc2 k j` (`= g_k(2dδ_j rowS_{C_k} − 𝔩_{C_k,C_j})`), so the drift of the regions is the drift
  of the couplings `β_k(B_+)` alone (`drift2_step_l1`: `∑_{B_+}|β_{i+1}(B_+) − β_i(B_+)| ≤
  |𝔫_i|A_i + E_i`);
* **`MuChain2.relRec2`**: `RelIn` with `dg = 0`, a rescaled size `G_i` and `T̃_{kj}` such that
  `|tadInc2 k j| ≤ T̃_{kj}G_i` (`k ≤ i < j`) gives `RelRec`; **`MuChain2.rel_step2`**: the relative
  one-step bound `‖∑_{B_+}err_j(B_+)‖ ≤ c_δr_j²‖β_j(1−𝔫^{(2)}_j)‖` and `c_δr_j² ≤ 1/8`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L]

/-- The deviation of the Case-(2) shares from the block of `a`. -/
def shareDev2 (a : Lam d L N) (k : ℕ) (V : OFam .two d L N) : ℝ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k,
    ‖mass2 (V b : SA .two (Lam d L N)).a -
      (if a ∈ blockSet (L := L) (N := N) k b then betaTot2 (L := L) (N := N) k V else 0)‖

/-- The `ℓ¹` error of the per-block `μ^{(2)}` flow at step `j`. -/
def shareErrL1_2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (j : ℕ) : ℝ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    ‖shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c')‖

/-- The `ℓ¹` sizes of the Case-(2) shares. -/
abbrev shA2 (V : ℕ → OFam .two d L N) (j : ℕ) : ℝ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass2 (V j b : SA .two (Lam d L N)).a‖

/-- The `ℓ¹` activity term (Case (2)). -/
abbrev shKt2 (K : ℕ → OAct .two d L N) (j : ℕ) : ℝ :=
  ∑ X ∈ smallSets (L := L) (N := N) j, ‖mass2 (K j X : SA .two (Lam d L N)).a‖

/-- The `ℓ¹` product parts (Case (2)). -/
abbrev shPr2 (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (j : ℕ) : ℝ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    ‖wTadX j mass2L (W j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
      muProdIncX2 P C V W j (blockSet (L := L) (N := N) (j + 1) c')‖

/-- `|β_k| ≤ ∑_B |c_k(B)| ≤ |β_k| + D_k` (Case (2)). -/
theorem sum_norm_share2_le (a : Lam d L N) (k : ℕ) (V : OFam .two d L N) :
    ∑ b ∈ blockIdx (L := L) (N := N) k, ‖mass2 (V b : SA .two (Lam d L N)).a‖ ≤
      ‖betaTot2 (L := L) (N := N) k V‖ + shareDev2 a k V := by
  classical
  have h : ∀ b ∈ blockIdx (L := L) (N := N) k, ‖mass2 (V b : SA .two (Lam d L N)).a‖ ≤
      ‖mass2 (V b : SA .two (Lam d L N)).a -
        (if a ∈ blockSet (L := L) (N := N) k b then betaTot2 (L := L) (N := N) k V else 0)‖ +
        (if a ∈ blockSet (L := L) (N := N) k b then ‖betaTot2 (L := L) (N := N) k V‖ else 0) := by
    intro b _
    refine (norm_le_norm_sub_add (mass2 (V b : SA .two (Lam d L N)).a)
      ((if a ∈ blockSet (L := L) (N := N) k b then
      betaTot2 (L := L) (N := N) k V else (0 : ℂ)))).trans (le_of_eq ?_)
    split_ifs <;> simp
  refine (sum_le_sum h).trans ?_
  rw [sum_add_distrib, add_comm]
  exact add_le_add (norm_sum_ite_mem_le a k _ (norm_nonneg (betaTot2 (L := L) (N := N) k V)))
    le_rfl

/-- `∑_{B_+ ∈ 𝓑_m} |β_k(B_+)| ≤ ∑_{B ∈ 𝓑_k} |c_k(B)|` for `k ≤ m` (Case (2)). -/
theorem sum_norm_betaX2_le {k m : ℕ} (hkm : k ≤ m) (V : OFam .two d L N) :
    ∑ c' ∈ blockIdx (L := L) (N := N) m, ‖betaX2 k V (blockSet (L := L) (N := N) m c')‖ ≤
      ∑ b ∈ blockIdx (L := L) (N := N) k, ‖mass2 (V b : SA .two (Lam d L N)).a‖ := by
  rw [← sum_blockIdx_le (fun b => ‖mass2 (V b : SA .two (Lam d L N)).a‖) hkm]
  exact sum_le_sum fun c' _ => norm_sum_le _ _

/-- **The `ℓ¹` error split** (Case (2)): activity, drift, product parts. -/
theorem shareErrL1_2_le (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .two d L N) (K : ℕ → OAct .two d L N) (j : ℕ) (hjN : j + 1 < N) :
    shareErrL1_2 P C V W K j ≤ shKt2 K j +
      ∑ k ∈ range j, ‖tadInc2 P C V k j‖ *
        ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          ‖betaX2 k (V k) (blockSet (L := L) (N := N) (j + 1) c') -
            betaX2 j (V j) (blockSet (L := L) (N := N) (j + 1) c')‖ +
      shPr2 P C V W j := by
  unfold shareErrL1_2
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      ‖shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
          ‖mass2 (EthO (C j) (Q2O P j (K j) b) : SA .two (Lam d L N)).a‖ +
        ∑ k ∈ range j, ‖tadInc2 P C V k j‖ *
          ‖betaX2 k (V k) (blockSet (L := L) (N := N) (j + 1) c') -
            betaX2 j (V j) (blockSet (L := L) (N := N) (j + 1) c')‖ +
        ‖wTadX j mass2L (W j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
          muProdIncX2 P C V W j (blockSet (L := L) (N := N) (j + 1) c')‖ := by
    intro c' _
    rw [shareErr2, add_assoc (muDriftX2 _ _ _ _ _)]
    refine (norm_add_le _ _).trans ?_
    rw [add_assoc]
    refine add_le_add (norm_sum_le _ _) ((norm_add_le _ _).trans (add_le_add ?_ le_rfl))
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
    rw [norm_mul, mul_comm]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_blockIdx_succ j
    (fun b => ‖mass2 (EthO (C j) (Q2O P j (K j) b) : SA .two (Lam d L N)).a‖), sum_comm]
  refine add_le_add (add_le_add ?_ (le_of_eq (sum_congr rfl fun k _ => by rw [mul_sum]))) le_rfl
  exact sum_norm_EthQ_le P j (C j) (K j) hjN mass2L (locMass_two P.a)

namespace MuChain2

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {K : ℕ → OAct .two d L N} {n : ℕ} (H : MuChain2 P C V W K n)
include H

/-- **The `ℓ¹` step of the deviation** (Case (2)): `D_{j+1} ≤ |1 − 𝔫_j| D_j + 2 E_j`. -/
theorem shareDev2_succ_le {j : ℕ} (hj : j < n) :
    shareDev2 P.a (j + 1) (V (j + 1)) ≤
      ‖1 - frakN2 P C V j‖ * shareDev2 P.a j (V j) + 2 * shareErrL1_2 P C V W K j := by
  classical
  set β := betaTot2 (L := L) (N := N) j (V j)
  set a' := 1 - frakN2 P C V j
  set e : (Fin d → ℕ) → ℂ := fun c' =>
    shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c')
  set δ : (Fin d → ℕ) → ℂ := fun b => mass2 (V j b : SA .two (Lam d L N)).a -
    (if P.a ∈ blockSet (L := L) (N := N) j b then β else 0)
  have hE0 : 0 ≤ shareErrL1_2 P C V W K j := sum_nonneg fun _ _ => norm_nonneg _
  have key : ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      mass2 (V (j + 1) c' : SA .two (Lam d L N)).a -
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          betaTot2 (L := L) (N := N) (j + 1) (V (j + 1)) else 0) =
      a' * ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), δ b - e c' +
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then
          ∑ c'' ∈ blockIdx (L := L) (N := N) (j + 1), e c'' else 0) := by
    intro c' hc'
    rw [H.share2_flow_exact hj hc', H.betaTot2_succ_eq hj]
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
        (if P.a ∈ blockSet (L := L) (N := N) (j + 1) c' then shareErrL1_2 P C V W K j
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
  have h2 := norm_sum_ite_mem_le P.a (j + 1) (shareErrL1_2 P C V W K j) hE0
  have h3 : ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1), ‖e c'‖ = shareErrL1_2 P C V W K j := rfl
  rw [h3]
  have h4 : ∑ b ∈ blockIdx (L := L) (N := N) j, ‖δ b‖ = shareDev2 P.a j (V j) := rfl
  rw [h4]
  linarith

theorem norm_betaTot2_succ_ge {j : ℕ} (hj : j < n) :
    ‖1 - frakN2 P C V j‖ * ‖betaTot2 (L := L) (N := N) j (V j)‖ - shareErrL1_2 P C V W K j ≤
      ‖betaTot2 (L := L) (N := N) (j + 1) (V (j + 1))‖ := by
  rw [H.betaTot2_succ_eq hj]
  have h1 := norm_sub_norm_le (betaTot2 (L := L) (N := N) j (V j) * (1 - frakN2 P C V j))
    (∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c'))
  have h2 := norm_sum_le (blockIdx (L := L) (N := N) (j + 1))
    (fun c' => shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c'))
  rw [norm_mul, mul_comm] at h1
  unfold shareErrL1_2
  linarith

/-- The flow of the coupling of a region `X` (an `(i+1)`-polymer), Case (2). -/
theorem betaX2_succ_eq {i : ℕ} (hi : i < n) {X : Finset (Lam d L N)}
    (hX : IsPolymer (i + 1) X) :
    betaX2 (i + 1) (V (i + 1)) X = betaX2 i (V i) X * (1 - frakN2 P C V i) -
      ∑ c'' ∈ blocks (i + 1) X, shareErr2 P C V W K i (blockSet (L := L) (N := N) (i + 1) c'') := by
  unfold betaX2
  rw [sum_congr rfl fun c'' hc'' =>
    H.share2_flow_exact hi (mem_blockIdx_of_mem_blocks hc''), sum_sub_distrib, ← sum_mul]
  congr 2
  unfold betaX2
  exact Step2.sum_blocks_succ hX _

/-- **The per-step drift of the regions in `ℓ¹`** (Case (2)):
`∑_{B_+ ∈ 𝓑_m} |β_{i+1}(B_+) − β_i(B_+)| ≤ |𝔫_i| A_i + E_i`. -/
theorem drift2_step_l1 {i m : ℕ} (hi : i < n) (him : i + 1 ≤ m) :
    ∑ c' ∈ blockIdx (L := L) (N := N) m,
        ‖betaX2 (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) m c') -
          betaX2 i (V i) (blockSet (L := L) (N := N) m c')‖ ≤
      ‖frakN2 P C V i‖ *
          ∑ b ∈ blockIdx (L := L) (N := N) i, ‖mass2 (V i b : SA .two (Lam d L N)).a‖ +
        shareErrL1_2 P C V W K i := by
  have hpol : ∀ c' : Fin d → ℕ, IsPolymer (i + 1) (blockSet (L := L) (N := N) m c') := fun c' =>
    Step2.isPolymer_of_le (isPolymer_blockSet m c') (i + 1) him
  have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) m,
      ‖betaX2 (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) m c') -
          betaX2 i (V i) (blockSet (L := L) (N := N) m c')‖ ≤
        ‖frakN2 P C V i‖ * ‖betaX2 i (V i) (blockSet (L := L) (N := N) m c')‖ +
          ∑ c'' ∈ blocks (i + 1) (blockSet (L := L) (N := N) m c'),
            ‖shareErr2 P C V W K i (blockSet (L := L) (N := N) (i + 1) c'')‖ := by
    intro c' _
    set X := blockSet (L := L) (N := N) m c'
    have e : betaX2 (i + 1) (V (i + 1)) X - betaX2 i (V i) X =
        -(betaX2 i (V i) X * frakN2 P C V i) -
          ∑ c'' ∈ blocks (i + 1) X, shareErr2 P C V W K i (blockSet (L := L) (N := N) (i + 1) c'') := by
      rw [H.betaX2_succ_eq hi (hpol c')]; ring
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
    rw [norm_neg, norm_mul, mul_comm]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have h3 := sum_norm_betaX2_le (show i ≤ m by omega) (V i)
  have h4 : ∑ c' ∈ blockIdx (L := L) (N := N) m,
      ∑ c'' ∈ blocks (i + 1) (blockSet (L := L) (N := N) m c'),
        ‖shareErr2 P C V W K i (blockSet (L := L) (N := N) (i + 1) c'')‖ =
      shareErrL1_2 P C V W K i :=
    sum_blockIdx_le _ him
  rw [h4]
  have := mul_le_mul_of_nonneg_left h3 (norm_nonneg (frakN2 P C V i))
  linarith

/-- The drift of the regions between scales `k ≤ j` (Case (2)). -/
theorem drift2_l1_le {k j m : ℕ} (hkj : k ≤ j) :
    ∑ c' ∈ blockIdx (L := L) (N := N) m,
        ‖betaX2 k (V k) (blockSet (L := L) (N := N) m c') -
          betaX2 j (V j) (blockSet (L := L) (N := N) m c')‖ ≤
      ∑ i ∈ Ico k j, ∑ c' ∈ blockIdx (L := L) (N := N) m,
        ‖betaX2 (i + 1) (V (i + 1)) (blockSet (L := L) (N := N) m c') -
          betaX2 i (V i) (blockSet (L := L) (N := N) m c')‖ := by
  rw [sum_comm]
  exact sum_le_sum fun c' _ => norm_sub_le_sum_Ico
    (fun i => betaX2 i (V i) (blockSet (L := L) (N := N) m c')) hkj

/-- **The unscaled split of `E_j`** (Case (2)). -/
theorem hE2_raw {j : ℕ} (hj : j < n) :
    shareErrL1_2 P C V W K j ≤ shKt2 K j + ∑ k ∈ range j, ‖tadInc2 P C V k j‖ *
      ∑ i ∈ Ico k j, (‖frakN2 P C V i‖ * shA2 V i + shareErrL1_2 P C V W K i) +
      shPr2 P C V W j := by
  have hjN : j + 1 < N := by have := H.hN; omega
  refine (shareErrL1_2_le P C V W K j hjN).trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
  refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hkj := (mem_range.1 hk).le
  refine (H.drift2_l1_le (m := j + 1) hkj).trans (sum_le_sum fun i hi => ?_)
  have hi' := mem_Ico.1 hi
  exact H.drift2_step_l1 (by omega) (by omega)

/-- **The per-block flow relations give `RelRec`** (Case (2)): `dg = 0`, rescaled sizes `G_i`
with `|tadInc2 k j| ≤ T̃_{kj} G_i` for `k ≤ i < j`. -/
theorem relRec2 {s rr θW θK G : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ} (Tt : ℕ → ℕ → ℝ)
    (hG : ∀ i < n, 0 ≤ G i)
    (hTt : ∀ k j, k < j → j < n → ∀ i ∈ Ico k j, ‖tadInc2 P C V k j‖ ≤ Tt k j * G i)
    (I : RelIn n (fun j => ‖betaTot2 (L := L) (N := N) j (V j)‖) (shA2 V)
      (fun j => shareDev2 P.a j (V j)) (fun j => shareErrL1_2 P C V W K j)
      (fun j => ‖1 - frakN2 P C V j‖) s rr (shKt2 K) (shPr2 P C V W)
      (fun _ => 0) G (fun i => ‖frakN2 P C V i‖)
      θW θK Tt Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ) :
    RelRec n (fun j => ‖betaTot2 (L := L) (N := N) j (V j)‖) (shA2 V)
      (fun j => shareDev2 P.a j (V j)) (fun j => shareErrL1_2 P C V W K j)
      (fun j => ‖1 - frakN2 P C V j‖) s rr (shKt2 K) (shPr2 P C V W)
      (fun _ => 0) G (fun i => ‖frakN2 P C V i‖)
      θW θK Tt Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ where
  toRelIn := I
  hb := fun _ _ => norm_nonneg _
  hA0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hE0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hDstep := fun _ hj => H.shareDev2_succ_le hj
  hbstep := fun _ hj => H.norm_betaTot2_succ_ge hj
  hA := fun j _ => sum_norm_share2_le P.a j (V j)
  hE := by
    intro j hj
    refine (H.hE2_raw hj).trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
    refine sum_le_sum fun k hk => ?_
    have hkj := mem_range.1 hk
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_Ico.1 hi
    have hGi := hG i (by omega)
    have hT := hTt k j hkj hj i hi
    set x := ‖frakN2 P C V i‖ * shA2 V i + shareErrL1_2 P C V W K i
    have hx0 : 0 ≤ x := by
      have h2 : 0 ≤ shA2 V i := sum_nonneg fun _ _ => norm_nonneg _
      have h3 : 0 ≤ shareErrL1_2 P C V W K i := sum_nonneg fun _ _ => norm_nonneg _
      have := norm_nonneg (frakN2 P C V i)
      positivity
    have e : (0 : ℝ) * shA2 V (i + 1) + G i * x = G i * x := by ring
    rw [e]
    calc ‖tadInc2 P C V k j‖ * x ≤ (Tt k j * G i) * x := mul_le_mul_of_nonneg_right hT hx0
      _ = Tt k j * (G i * x) := by ring

/-- **The relative one-step bound of the `μ^{(2)}` flow** along a `MuChain2`:
`‖∑_{B_+}err_j(B_+)‖ ≤ c_δr_j²‖β_j(1 − 𝔫^{(2)}_j)‖` and `c_δr_j² ≤ 1/8` for `j < n`. -/
theorem rel_step2 {s rr θW θK G : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ} (Tt : ℕ → ℕ → ℝ)
    (hG : ∀ i < n, 0 ≤ G i)
    (hTt : ∀ k j, k < j → j < n → ∀ i ∈ Ico k j, ‖tadInc2 P C V k j‖ ≤ Tt k j * G i)
    (I : RelIn n (fun j => ‖betaTot2 (L := L) (N := N) j (V j)‖) (shA2 V)
      (fun j => shareDev2 P.a j (V j)) (fun j => shareErrL1_2 P C V W K j)
      (fun j => ‖1 - frakN2 P C V j‖) s rr (shKt2 K) (shPr2 P C V W)
      (fun _ => 0) G (fun i => ‖frakN2 P C V i‖)
      θW θK Tt Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ) :
    ∀ j < n, ‖∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        shareErr2 P C V W K j (blockSet (L := L) (N := N) (j + 1) c')‖ ≤
      cδ * rr j ^ 2 * ‖betaTot2 (L := L) (N := N) j (V j) * (1 - frakN2 P C V j)‖ ∧
      cδ * rr j ^ 2 ≤ 1 / 8 := by
  have R := H.relRec2 Tt hG hTt I
  intro j hj
  have hE := (R.close (j + 1) hj).2 j (Nat.lt_succ_self j)
  refine ⟨(norm_sum_le _ _).trans (hE.trans (le_of_eq ?_)), R.rsq_le hj⟩
  rw [norm_mul]; ring

end MuChain2

end

end Obs2
