import Obs2.Flow.BlockFlow
import Obs2.Flow.RelRec

/-!
# The relative per-block flow along a `MuChain` (Case (1), sharp splitting)

The per-block flow relations of `Obs2/Flow/BlockFlow` (`shareDev_succ_le`, `norm_betaTot_succ_ge`,
`sum_norm_share_le`, `shareErrL1_le` with `drift_l1_le`, `drift_step_l1`) are exactly the flow
fields of `RelRec` for

* `b_j = |β_j|`, `A_j = ∑_B |c_j(B)|`, `D_j = shareDev`, `E_j = shareErrL1`,
  `a_j = |1 − 𝔫_j|`, `nn_j = |𝔫_j|`,
* `dg_i = |g'_{i+1} − g'_i|`, `G_i = |g'_i|`, `T_{kj} = |τ(C_k, C_j)(a)|`,
* `Kt_j = ∑_{X ∈ 𝒮_j} |m₁(K_j(X)_a)|` (activity term in `ℓ¹`),
* `Pr_j = ∑_{B_+} |G_j(B_+; 0) + prodInc_j(B_+)|` (the product parts in `ℓ¹`).

**`MuChain.relRec`**: `RelIn` (the inputs) gives `RelRec`. Hence (**`MuChain.rel_flow`**) along the
chain: `|β_j| > 0`, phase alignment `∑_B |c_j(B) − β_j1_{a∈B}| ≤ 6c_δ(∑_{k<j} r_k²)|β_j|`, the
observable sizes proportional to `s_j|β_j|`, the relative error `|β_{j+1} − β_j(1−𝔫_j)| ≤
c_δ r_j² |β_j(1−𝔫_j)|`, and the product formula
`|β_j − β_0∏_{k<j}(1−𝔫_k)| ≤ (e^{c_δ∑_{k<j} r_k²} − 1)|β_0∏_{k<j}(1−𝔫_k)|`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L]

namespace MuChain

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .one d L N} {K : ℕ → OAct .one d L N} {κ : ℕ → Step2.Coup} {r : ℕ → ℂ}
  {n : ℕ} (H : MuChain P C V W K κ r n)
include H

/-- The `ℓ¹` sizes of the shares. -/
abbrev shA (V : ℕ → OFam .one d L N) (j : ℕ) : ℝ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass1 (-1) (V j b : SA .one (Lam d L N)).a‖

/-- The `ℓ¹` activity term. -/
abbrev shKt (K : ℕ → OAct .one d L N) (j : ℕ) : ℝ :=
  ∑ X ∈ smallSets (L := L) (N := N) j, ‖mass1 (-1) (K j X : SA .one (Lam d L N)).a‖

/-- The `ℓ¹` product parts. -/
abbrev shPr (P : ObsPts d L N) (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : ℕ → OFam .one d L N) (j : ℕ) : ℝ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    ‖wTadX j (mass1L (-1)) (W j) (blockSet (L := L) (N := N) (j + 1) c') 0 +
      muProdIncX P C V W j (blockSet (L := L) (N := N) (j + 1) c')‖

/-- **The per-block flow relations give `RelRec`.** -/
theorem relRec {s rr θW θK : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ}
    (I : RelIn n (fun j => ‖betaTot (L := L) (N := N) j (V j)‖) (shA V)
      (fun j => shareDev P.a j (V j)) (fun j => shareErrL1 P C V W K κ j)
      (fun j => ‖1 - frakN C κ P.a j‖) s rr (shKt K) (shPr P C V W)
      (fun i => ‖(κ (i + 1)).g - (κ i).g‖) (fun i => ‖(κ i).g‖) (fun i => ‖frakN C κ P.a i‖)
      θW θK (fun k j => ‖tauC (C k) (C j) P.a‖) Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ) :
    RelRec n (fun j => ‖betaTot (L := L) (N := N) j (V j)‖) (shA V)
      (fun j => shareDev P.a j (V j)) (fun j => shareErrL1 P C V W K κ j)
      (fun j => ‖1 - frakN C κ P.a j‖) s rr (shKt K) (shPr P C V W)
      (fun i => ‖(κ (i + 1)).g - (κ i).g‖) (fun i => ‖(κ i).g‖) (fun i => ‖frakN C κ P.a i‖)
      θW θK (fun k j => ‖tauC (C k) (C j) P.a‖) Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ where
  toRelIn := I
  hb := fun _ _ => norm_nonneg _
  hA0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hE0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hDstep := fun _ hj => H.shareDev_succ_le hj
  hbstep := fun _ hj => H.norm_betaTot_succ_ge hj
  hA := fun j _ => sum_norm_share_le P.a j (V j)
  hE := by
    intro j hj
    have hjN : j + 1 < N := by have := H.hN; omega
    refine (shareErrL1_le P C V W K κ j hjN).trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
    refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hkj := (mem_range.1 hk).le
    refine (H.drift_l1_le (m := j + 1) hkj).trans (sum_le_sum fun i hi => ?_)
    have hi' := mem_Ico.1 hi
    exact H.drift_step_l1 (by omega) (by omega)

/-- **The relative `μ^{(1)}` flow along a `MuChain`.** -/
theorem rel_flow {s rr θW θK : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ}
    (I : RelIn n (fun j => ‖betaTot (L := L) (N := N) j (V j)‖) (shA V)
      (fun j => shareDev P.a j (V j)) (fun j => shareErrL1 P C V W K κ j)
      (fun j => ‖1 - frakN C κ P.a j‖) s rr (shKt K) (shPr P C V W)
      (fun i => ‖(κ (i + 1)).g - (κ i).g‖) (fun i => ‖(κ i).g‖) (fun i => ‖frakN C κ P.a i‖)
      θW θK (fun k j => ‖tauC (C k) (C j) P.a‖) Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ) :
    ∀ j ≤ n, 0 < ‖betaTot (L := L) (N := N) j (V j)‖ ∧
      shareDev P.a j (V j) ≤ 6 * (cδ * ∑ k ∈ range j, rr k ^ 2) *
        ‖betaTot (L := L) (N := N) j (V j)‖ ∧
      Wb j (cW * rr j * (2 * s j * ‖betaTot (L := L) (N := N) j (V j)‖)) ∧
      Kb j (16 * cW * Bk * rr j ^ 2 * (s j * ‖betaTot (L := L) (N := N) j (V j)‖)) ∧
      (j < n → ‖betaTot (L := L) (N := N) (j + 1) (V (j + 1)) -
          betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j)‖ ≤
        cδ * rr j ^ 2 * ‖betaTot (L := L) (N := N) j (V j) * (1 - frakN C κ P.a j)‖) ∧
      ‖betaTot (L := L) (N := N) j (V j) -
          betaTot (L := L) (N := N) 0 (V 0) * ∏ k ∈ range j, (1 - frakN C κ P.a k)‖ ≤
        (Real.exp (cδ * ∑ k ∈ range j, rr k ^ 2) - 1) *
          ‖betaTot (L := L) (N := N) 0 (V 0) * ∏ k ∈ range j, (1 - frakN C κ P.a k)‖ := by
  have R := H.relRec I
  have hstep : ∀ k < n, ‖betaTot (L := L) (N := N) (k + 1) (V (k + 1)) -
      betaTot (L := L) (N := N) k (V k) * (1 - frakN C κ P.a k)‖ ≤
      cδ * rr k ^ 2 * ‖betaTot (L := L) (N := N) k (V k) * (1 - frakN C κ P.a k)‖ := by
    intro k hk
    have hE := (R.close (k + 1) hk).2 k (Nat.lt_succ_self k)
    rw [H.betaTot_succ_eq hk, norm_mul, mul_comm ‖betaTot (L := L) (N := N) k (V k)‖]
    have e : betaTot (L := L) (N := N) k (V k) * (1 - frakN C κ P.a k) -
        ∑ c' ∈ blockIdx (L := L) (N := N) (k + 1),
          shareErr P C V W K κ k (blockSet (L := L) (N := N) (k + 1) c') -
        betaTot (L := L) (N := N) k (V k) * (1 - frakN C κ P.a k) =
        -∑ c' ∈ blockIdx (L := L) (N := N) (k + 1),
          shareErr P C V W K κ k (blockSet (L := L) (N := N) (k + 1) c') := by ring
    rw [e, norm_neg]
    exact (norm_sum_le _ _).trans hE
  have hδ : ∀ k < n, 0 ≤ cδ * rr k ^ 2 := fun k _ => mul_nonneg R.hcδ0 (sq_nonneg _)
  intro j hj
  obtain ⟨hb, hD, hW, hK⟩ := (R.close j hj).1 j le_rfl
  refine ⟨hb, hD, hW, hK, fun hjn => hstep j hjn, ?_⟩
  have hp := rel_prod_le (x := fun k => betaTot (L := L) (N := N) k (V k))
    (u := fun k => 1 - frakN C κ P.a k) hδ hstep j hj
  refine hp.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have := prod_one_add_le_exp (δ := fun k => cδ * rr k ^ 2) j fun k hk => hδ k (by omega)
  rw [← mul_sum] at this
  linarith

end MuChain

end

end Obs2
