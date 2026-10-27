import Obs2.Flow.BlockFlow2

/-!
# The relative per-block flow with weights (Case (1), sharp splitting)

`MuChain.relRec` uses the absolute sizes `T_{kj} = |τ(C_k, C_j)(a)|`, `G_i = |g'_i|`,
`dg_i = |g'_{i+1} − g'_i|`, with uniform constants `B_τ`, `c_g`. Along the flow these are not
uniform separately: `C_k` lives at the field scale `|Z_{k+1}|^{-1/2}ℓ`, so `T_{kj} ∼ |Z_{k+1}Z_{j+1}|^{-1}`,
while `g'_i = ǧ_i Z_{i+1}²/(1 + n_i)`; only the products `T_{kj} G_i` (`k ≤ i < j`) are uniform.

**`MuChain.relRec_w`**, **`MuChain.rel_flow_w`**: the same conclusions with weights `w_i > 0`:
`T̃_{kj} ≥ T_{kj} w_i` for `k ≤ i < j` and the rescaled bulk sizes `dg_i/w_i`, `G_i/w_i`
in `RelIn` (with `w_i = |Z_{i+1}|²` along the history, `T̃_{kj} = O(q^{j-k})` and
`G_i/w_i = |ǧ_i/(1+n_i)|` are uniform).
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

/-- The unscaled split of `E_j` (the field `hE` of `relRec`). -/
theorem hE_raw {j : ℕ} (hj : j < n) :
    shareErrL1 P C V W K κ j ≤ shKt K j + ∑ k ∈ range j, ‖tauC (C k) (C j) P.a‖ *
      ∑ i ∈ Ico k j, (‖(κ (i + 1)).g - (κ i).g‖ * shA V (i + 1) +
        ‖(κ i).g‖ * (‖frakN C κ P.a i‖ * shA V i + shareErrL1 P C V W K κ i)) +
      shPr P C V W j := by
  have hjN : j + 1 < N := by have := H.hN; omega
  refine (shareErrL1_le P C V W K κ j hjN).trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
  refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hkj := (mem_range.1 hk).le
  refine (H.drift_l1_le (m := j + 1) hkj).trans (sum_le_sum fun i hi => ?_)
  have hi' := mem_Ico.1 hi
  exact H.drift_step_l1 (by omega) (by omega)

/-- **The per-block flow relations give `RelRec`, with weights.** -/
theorem relRec_w {s rr θW θK : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ} (w : ℕ → ℝ) (Tt : ℕ → ℕ → ℝ)
    (hw : ∀ i < n, 0 < w i)
    (hTt : ∀ k j, k < j → j < n → ∀ i ∈ Ico k j, ‖tauC (C k) (C j) P.a‖ * w i ≤ Tt k j)
    (I : RelIn n (fun j => ‖betaTot (L := L) (N := N) j (V j)‖) (shA V)
      (fun j => shareDev P.a j (V j)) (fun j => shareErrL1 P C V W K κ j)
      (fun j => ‖1 - frakN C κ P.a j‖) s rr (shKt K) (shPr P C V W)
      (fun i => ‖(κ (i + 1)).g - (κ i).g‖ / w i) (fun i => ‖(κ i).g‖ / w i)
      (fun i => ‖frakN C κ P.a i‖)
      θW θK Tt Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ) :
    RelRec n (fun j => ‖betaTot (L := L) (N := N) j (V j)‖) (shA V)
      (fun j => shareDev P.a j (V j)) (fun j => shareErrL1 P C V W K κ j)
      (fun j => ‖1 - frakN C κ P.a j‖) s rr (shKt K) (shPr P C V W)
      (fun i => ‖(κ (i + 1)).g - (κ i).g‖ / w i) (fun i => ‖(κ i).g‖ / w i)
      (fun i => ‖frakN C κ P.a i‖)
      θW θK Tt Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ where
  toRelIn := I
  hb := fun _ _ => norm_nonneg _
  hA0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hE0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hDstep := fun _ hj => H.shareDev_succ_le hj
  hbstep := fun _ hj => H.norm_betaTot_succ_ge hj
  hA := fun j _ => sum_norm_share_le P.a j (V j)
  hE := by
    intro j hj
    refine (H.hE_raw hj).trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
    refine sum_le_sum fun k hk => ?_
    have hkj := mem_range.1 hk
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_Ico.1 hi
    have hwi := hw i (by omega)
    have hT := hTt k j hkj hj i hi
    set x := ‖(κ (i + 1)).g - (κ i).g‖ * shA V (i + 1) +
      ‖(κ i).g‖ * (‖frakN C κ P.a i‖ * shA V i + shareErrL1 P C V W K κ i)
    have hx0 : 0 ≤ x := by
      have h1 : 0 ≤ shA V (i + 1) := sum_nonneg fun _ _ => norm_nonneg _
      have h2 : 0 ≤ shA V i := sum_nonneg fun _ _ => norm_nonneg _
      have h3 : 0 ≤ shareErrL1 P C V W K κ i := sum_nonneg fun _ _ => norm_nonneg _
      have := norm_nonneg ((κ (i + 1)).g - (κ i).g)
      have := norm_nonneg (κ i).g
      have := norm_nonneg (frakN C κ P.a i)
      positivity
    have e : ‖(κ (i + 1)).g - (κ i).g‖ / w i * shA V (i + 1) +
        ‖(κ i).g‖ / w i * (‖frakN C κ P.a i‖ * shA V i + shareErrL1 P C V W K κ i) = x / w i := by
      simp only [x]; field_simp
    rw [e]
    calc ‖tauC (C k) (C j) P.a‖ * x = (‖tauC (C k) (C j) P.a‖ * w i) * (x / w i) := by
          field_simp
      _ ≤ Tt k j * (x / w i) := mul_le_mul_of_nonneg_right hT (div_nonneg hx0 hwi.le)

/-- **The relative `μ^{(1)}` flow along a `MuChain`, with weights.** -/
theorem rel_flow_w {s rr θW θK : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ} (w : ℕ → ℝ) (Tt : ℕ → ℕ → ℝ)
    (hw : ∀ i < n, 0 < w i)
    (hTt : ∀ k j, k < j → j < n → ∀ i ∈ Ico k j, ‖tauC (C k) (C j) P.a‖ * w i ≤ Tt k j)
    (I : RelIn n (fun j => ‖betaTot (L := L) (N := N) j (V j)‖) (shA V)
      (fun j => shareDev P.a j (V j)) (fun j => shareErrL1 P C V W K κ j)
      (fun j => ‖1 - frakN C κ P.a j‖) s rr (shKt K) (shPr P C V W)
      (fun i => ‖(κ (i + 1)).g - (κ i).g‖ / w i) (fun i => ‖(κ i).g‖ / w i)
      (fun i => ‖frakN C κ P.a i‖)
      θW θK Tt Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ) :
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
  have R := H.relRec_w w Tt hw hTt I
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
