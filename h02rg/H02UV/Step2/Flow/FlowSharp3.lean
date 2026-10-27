import Step2.Flow.FlowSharp2

/-!
# The marginal coupling along the sharp flow

`thm_flow_sharp_sum`: along the admissible trajectories of `thm_flow_sharp`, for `1 ≤ n ≤ N_h`,
`|1/ǧ_n - 1/b + β n| ≤ C_sh (1 + 2ϑ) + (1+β)β + (C_sh + C) ∑_{j<n} ǧ_j`,
i.e. `ǧ_n⁻¹ = b⁻¹ - β n + O(1 + ∑_{j<n} ǧ_j)` (`h02uv-outline.tex`, Expected result `thm:flow` (i),
with `b = 1/β_ε`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

/-- Summing the sharp steps `1 ≤ j < n` and the band step `j = 0`. -/
theorem ginv_sum_of_steps {x g : ℕ → ℝ} {β Csh Cg L msq ϑ c0 : ℝ} {Nh n : ℕ} (hL : 2 ≤ L)
    (hmsq : 0 ≤ msq) (hCsh : 0 ≤ Csh) (hCg : 0 ≤ Cg) (hg : ∀ j, 0 ≤ g j) (hn1 : 1 ≤ n)
    (hn : n ≤ Nh) (hϑ : msq * (L ^ (Nh + 1)) ^ 2 ≤ ϑ)
    (h0 : |x 1 - x 0 + β| ≤ c0 + Cg * g 0)
    (hs : ∀ j, 1 ≤ j → j < n →
      |x (j + 1) - x j + β| ≤ Csh * (((L ^ j) ^ 2)⁻¹ + msq * (L ^ (j + 1)) ^ 2) + Csh * g j) :
    |x n - x 0 + β * n| ≤ Csh * (1 + 2 * ϑ) + c0 + (Csh + Cg) * ∑ j ∈ range n, g j := by
  have ht := tele_sum (x := x) (a := fun j => ((L ^ j) ^ 2)⁻¹ + msq * (L ^ (j + 1)) ^ 2) (g := g)
    (β := β) (C := Csh) (m := 1) n hn1 hs
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at ht
  have hL0 : 0 < L := by linarith
  -- the geometric sums
  have hI := geom_inv_le hL n
  have hsub : Ico 1 n ⊆ range n := by
    rw [range_eq_Ico]; exact Ico_subset_Ico (Nat.zero_le 1) le_rfl
  have hM1 : ∑ j ∈ Ico 1 n, (L ^ (j + 1)) ^ 2 ≤ ∑ j ∈ range n, (L ^ (j + 1)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
  have hM2 := geom_Lsq_le hL n
  have hM3 : (L ^ n) ^ 2 ≤ (L ^ (Nh + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
  have hM : msq * ∑ j ∈ Ico 1 n, (L ^ (j + 1)) ^ 2 ≤ 2 * ϑ := by
    have := mul_le_mul_of_nonneg_left (hM1.trans (hM2.trans (mul_le_mul_of_nonneg_left hM3
      (by norm_num)))) hmsq
    linarith only [this, hϑ]
  have hA : ∑ j ∈ Ico 1 n, ((L ^ j) ^ 2)⁻¹ + msq * ∑ j ∈ Ico 1 n, (L ^ (j + 1)) ^ 2 ≤ 1 + 2 * ϑ := by
    linarith only [hI, hM]
  -- the sum of `g`
  have hG : ∑ j ∈ range n, g j = g 0 + ∑ j ∈ Ico 1 n, g j := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  have hGs : 0 ≤ ∑ j ∈ Ico 1 n, g j := sum_nonneg fun j _ => hg j
  -- assembling
  have e : x n - x 0 + β * n = (x n - x 1 + β * ((n : ℝ) - ((1 : ℕ) : ℝ))) + (x 1 - x 0 + β) := by
    push_cast; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have k1 := mul_le_mul_of_nonneg_left hA hCsh
  have k2 := mul_nonneg hCg hGs
  have k3 := mul_nonneg hCsh (hg 0)
  have e2 : (Csh + Cg) * ∑ j ∈ range n, g j =
      Csh * g 0 + Csh * ∑ j ∈ Ico 1 n, g j + Cg * g 0 + Cg * ∑ j ∈ Ico 1 n, g j := by
    rw [hG]; ring
  have e3 : Csh * (∑ j ∈ Ico 1 n, ((L ^ j) ^ 2)⁻¹ + msq * ∑ j ∈ Ico 1 n, (L ^ (j + 1)) ^ 2) =
      Csh * ∑ j ∈ Ico 1 n, ((L ^ j) ^ 2)⁻¹ + Csh * (msq * ∑ j ∈ Ico 1 n, (L ^ (j + 1)) ^ 2) := by
    ring
  rw [e2]
  have e4 : Csh * (∑ j ∈ Ico 1 n, ((L ^ j) ^ 2)⁻¹ + msq * ∑ j ∈ Ico 1 n, (L ^ (j + 1)) ^ 2 +
      ∑ j ∈ Ico 1 n, g j) = Csh * (∑ j ∈ Ico 1 n, ((L ^ j) ^ 2)⁻¹ +
        msq * ∑ j ∈ Ico 1 n, (L ^ (j + 1)) ^ 2) + Csh * ∑ j ∈ Ico 1 n, g j := by ring
  rw [e4] at ht
  refine (add_le_add ht h0).trans ?_
  linarith only [k1, k2, k3]

set_option maxHeartbeats 1000000 in
/-- **The marginal coupling along the flow** (Expected result `thm:flow` (i), sharp form):
`|1/ǧ_n - 1/b + β n| ≤ C_sh (1 + 2ϑ) + (1+β)β + (C_sh + C) ∑_{j<n} ǧ_j` for `1 ≤ n ≤ N_h`,
with `C = 2(β² + (1+β) c_g)`. -/
theorem thm_flow_sharp_sum : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ ϑ κ cg cm cT ε Csh : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ϑ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Csh ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ ϑ →
      (∀ b ∈ Set.Ioc 0 (bmax (betaL L) (1 / 2) cg Nh ε),
          ∃! μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) ∧
      (∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → ∀ n, 1 ≤ n → n ≤ Nh →
        |1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ n).1 - 1 / b + betaL L * n| ≤
          Csh * (1 + 2 * ϑ) + 2 * (1 + betaL L) * (1 / 2) * betaL L +
            (Csh + Cgu (betaL L) cg) * ∑ j ∈ range n, (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1) := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_sharp
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, ϑ, κ, cg, cm, cT, ε, Csh, hℓ, hA, hρ, hϑ, hε, hκ0, hκ1, hcg, hcm, hcT, hCsh,
    h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, ϑ, κ, cg, cm, cT, ε, Csh, hℓ, hA, hρ, hϑ, hε, hκ0, hκ1, hcg, hcm, hcT, hCsh,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh hmass => ?_⟩
  obtain ⟨r1, r2, -, -, r5⟩ := h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh hmass
  refine ⟨r1, fun b μ₀ hadm n hn1 hn => ?_⟩
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hβ : 0 ≤ betaL L := by
    unfold betaL
    have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have := Real.pi_pos
    positivity
  have hCg : 0 ≤ Cgu (betaL L) cg := by unfold Cgu; positivity
  have hg : ∀ j, j ≤ Nh → 0 < (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 := fun j hj =>
    (hadm.1 j hj).1
  have h0 := r2 b μ₀ hadm 0 (by omega)
  -- `g` extended by `0` beyond the horizon
  have key := ginv_sum_of_steps (x := fun j => 1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1)
    (g := fun j => if j ≤ Nh then (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 else 0)
    (β := betaL L) (Csh := Csh) (Cg := Cgu (betaL L) cg) (msq := R.msq) (ϑ := ϑ)
    (c0 := 2 * (1 + betaL L) * (1 / 2) * betaL L) hL2 hm0.le hCsh hCg
    (fun j => by split_ifs with hj; exacts [(hg j hj).le, le_rfl]) hn1 hn hmass
    (by simp only [if_pos (Nat.zero_le Nh)]; exact h0)
    (fun j hj1 hj2 => by
      simp only [if_pos (show j ≤ Nh by omega)]
      exact r5 b μ₀ hadm j hj1 (by omega))
  have hS : ∑ j ∈ range n, (fun j => if j ≤ Nh then (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1
      else 0) j = ∑ j ∈ range n, (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1 :=
    sum_congr rfl fun j hj => if_pos (by have := mem_range.1 hj; omega)
  rw [hS] at key
  have hb : 1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ 0).1 = 1 / b := by rw [Hist.traj_zero]
  rw [← hb]
  exact key

end

end Step2
