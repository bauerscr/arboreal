import Flow2.FixedR2
import Flow2.DiffHist

/-!
# Differentiability in `b` at fixed `β_R` (`thm:flow`(iii) on `Ufix`)

The differentiability theorem `Flow2.Hist.fh_flow_hist_diff` is stated on `(0, b_max)`, where
`traj_g_lt` (`b < b_max`) keeps the admissible trajectory in the open part `InDhs` of the domain.
Here it is transferred to the open set `Ufix` of `Flow2.FixedR*` (an admissible trajectory with
`ǧ_N < ε`):

* `traj_g_lt_fixed`: on `Ufix`, `g_j ≤ g_N < ε` for all `j ≤ N` (`traj_le_N`, the coupling is
  nondecreasing);
* `traj_diffAt_fixed`: `(b, μ₀) ↦ s_j(b, μ₀)` is differentiable at admissible data with `ǧ_N < ε`;
* `eventually_traj_InD3_fixed`: near the admissible `μ₀` the trajectories from the same `b` stay in
  `D_ε` (from the open condition `OKR` on a box, `OKR_box`, instead of the clamped flow);
* `differentiableAt_muc_fixed`: `μ₀(b)` is differentiable at every `b ∈ Ufix`
  (`Flow2.hasDerivAt_implicit`, with the continuity `continuousAt_muc_fixed` and the expansion
  `traj_expand`);
* `fh_flow_fixedR_diff`: `μ₀`, `ǧ_N` and all coordinates `s_j(b, μ₀(b))`, `j ≤ N`, are
  differentiable on `Ufix`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace ℝ (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

section Diff

variable {N : ℕ} {A a ε : ℝ}

omit [∀ j, NormedSpace ℝ (X j)] in
/-- Along an admissible trajectory with `ǧ_N < ε`, all couplings are `< ε`. -/
lemma traj_g_lt_fixed (H : HHyp F Λ β δ κ cg cm cT N A a ε) (hgβ : cg * ε ≤ (1 - δ) * β)
    {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) (hg : (traj F Λ b μ₀ N).1 < ε) :
    ∀ j ≤ N, (traj F Λ b μ₀ j).1 < ε :=
  fun j hj => (traj_le_N H hgβ h j hj).trans_lt hg

/-- **The trajectory is differentiable in `(b, μ₀)`** at admissible data with `ǧ_N < ε`. -/
theorem traj_diffAt_fixed (H : HHyp F Λ β δ κ cg cm cT N A a ε) (hgβ : cg * ε ≤ (1 - δ) * β)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b₀ μ₀)
    (hg : (traj F Λ b₀ μ₀ N).1 < ε) :
    ∀ j ≤ N, DifferentiableAt ℝ (fun p : ℝ × ℝ => traj F Λ p.1 p.2 j) (b₀, μ₀) := by
  have hlt := traj_g_lt_fixed H hgβ h hg
  have key : ∀ k ≤ N, ∀ i ≤ k,
      DifferentiableAt ℝ (fun p : ℝ × ℝ => traj F Λ p.1 p.2 i) (b₀, μ₀) := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      obtain rfl : i = 0 := by omega
      simp only [traj_zero]
      exact differentiableAt_fst.prodMk (differentiableAt_snd.prodMk (differentiableAt_const _))
    | succ k ih =>
      intro hk i hi
      rcases (show i = k + 1 ∨ i ≤ k by omega) with rfl | hik
      · have hkN : k < N := by omega
        have IH := ih (by omega)
        have hs : InDhs F Λ β δ κ cg cm cT ε k (traj F Λ b₀ μ₀) := by
          refine ⟨admissible_InDh H h k (by omega), fun i hi => hlt i (by omega), ?_⟩
          have := hlt (k + 1) hk
          rw [traj_succ H b₀ μ₀ hkN] at this
          exact this
        have e : (fun p : ℝ × ℝ => traj F Λ p.1 p.2 (k + 1)) = fun p =>
            (F.G k (trajF F Λ p), Λ * (trajF F Λ p k).2.1 + F.m k (trajF F Λ p),
              F.T k (trajF F Λ p)) := funext fun p => traj_succ H p.1 p.2 hkN
        rw [e]
        have dG := HD.G k hkN _ hs (trajF F Λ) (b₀, μ₀) rfl IH
        have dm := HD.m k hkN _ hs (trajF F Λ) (b₀, μ₀) rfl IH
        have dT := HD.T k hkN _ hs (trajF F Λ) (b₀, μ₀) rfl IH
        exact dG.prodMk ((((IH k le_rfl).snd.fst).const_mul Λ).add dm |>.prodMk dT)
      · exact ih (by omega) i hik
  exact fun j hj => key j hj j le_rfl

omit [∀ j, NormedSpace ℝ (X j)] in
/-- Near an admissible `μ₀` with `ǧ_N < ε`, the trajectories from the same `b` stay in `D_ε`. -/
lemma eventually_traj_InD3_fixed (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) {b μs : ℝ}
    (h : Admissible F Λ κ cm cT N ε b μs) (hg : (traj F Λ b μs N).1 < ε) :
    ∀ᶠ μ in 𝓝 μs, ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ j) := by
  obtain ⟨r, hr, hbox⟩ := OKR_box H he hgβ h hg
  filter_upwards [Metric.ball_mem_nhds μs hr] with μ hμ
  rw [Metric.mem_ball, Real.dist_eq] at hμ
  have hO := hbox b μ (by rw [sub_self, abs_zero]; exact hr) hμ
  exact fun j hj => (inDh_of_OKR H he le_rfl hO j hj).1 j le_rfl

/-- **`μ₀(b)` is differentiable** at every `b ∈ Ufix`. -/
theorem differentiableAt_muc_fixed (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ : ℝ} (hb : b₀ ∈ Ufix F Λ κ cm cT N ε) :
    DifferentiableAt ℝ (muc F Λ κ cm cT N ε) b₀ := by
  obtain ⟨μ₁, h₁, hg₁⟩ := hb
  have hadm := muc_spec_of H ha0 h₁
  have hg : (traj F Λ b₀ (muc F Λ κ cm cT N ε b₀) N).1 < ε := by
    rw [muc_eq_of_adm H ha0 h₁]; exact hg₁
  have hnhds : Ufix F Λ κ cm cT N ε ∈ 𝓝 b₀ :=
    (isOpen_Ufix H he hgβ ha0).mem_nhds ⟨μ₁, h₁, hg₁⟩
  refine differentiableAt_implicit (φ := fun p : ℝ × ℝ => (traj F Λ p.1 p.2 N).2.1) one_pos
    (traj_diffAt_fixed H hgβ HD hadm hg N le_rfl).snd.fst
    (continuousAt_muc_fixed H he hgβ ha0 h₁ hg₁) ?_ ?_
  · filter_upwards [hnhds] with b hb
    obtain ⟨μ, h, -⟩ := hb
    exact (muc_spec_of H ha0 h).2
  · filter_upwards [eventually_traj_InD3_fixed H he hgβ hadm hg] with μ hμ
    have h1 := traj_expand H ha0 hμ hadm.1
    rw [hadm.2, sub_zero] at h1
    simpa only [one_mul] using h1

/-- **All coordinates along the admissible flow are differentiable** on `Ufix`. -/
theorem differentiableAt_traj_muc_fixed (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ : ℝ} (hb : b₀ ∈ Ufix F Λ κ cm cT N ε) {j : ℕ}
    (hj : j ≤ N) :
    DifferentiableAt ℝ (fun b => traj F Λ b (muc F Λ κ cm cT N ε b) j) b₀ := by
  obtain ⟨μ₁, h₁, hg₁⟩ := hb
  have hadm := muc_spec_of H ha0 h₁
  have hg : (traj F Λ b₀ (muc F Λ κ cm cT N ε b₀) N).1 < ε := by
    rw [muc_eq_of_adm H ha0 h₁]; exact hg₁
  have h1 := traj_diffAt_fixed H hgβ HD hadm hg j hj
  have h2 : DifferentiableAt ℝ (fun b => ((b, muc F Λ κ cm cT N ε b) : ℝ × ℝ)) b₀ :=
    differentiableAt_id.prodMk (differentiableAt_muc_fixed H he hgβ ha0 HD ⟨μ₁, h₁, hg₁⟩)
  exact h1.comp b₀ h2

/-- **`thm:flow`(iii), differentiability on `Ufix`**: `μ₀`, `ǧ_N` and every coordinate
`s_j(b, μ₀(b))`, `j ≤ N`, are differentiable on `Ufix`. -/
theorem fh_flow_fixedR_diff (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) :
    DifferentiableOn ℝ (muc F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) ∧
    DifferentiableOn ℝ (gN F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) ∧
    ∀ j ≤ N, DifferentiableOn ℝ (fun b => traj F Λ b (muc F Λ κ cm cT N ε b) j)
      (Ufix F Λ κ cm cT N ε) :=
  ⟨fun _ hb => (differentiableAt_muc_fixed H he hgβ ha0 HD hb).differentiableWithinAt,
    fun _ hb => (differentiableAt_traj_muc_fixed H he hgβ ha0 HD hb le_rfl).fst.differentiableWithinAt,
    fun _ hj _ hb => (differentiableAt_traj_muc_fixed H he hgβ ha0 HD hb hj).differentiableWithinAt⟩

end Diff

end Hist

end Flow2
