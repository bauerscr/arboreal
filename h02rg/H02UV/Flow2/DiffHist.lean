import Flow2.History
import Flow2.DiffImplicit

/-!
# Differentiability in `b₀` of the history-dependent flow (`h02uv-outline.tex`, `thm:flow`(iii))

The irrelevant spaces `X_j` are real normed spaces. A map `f : Seq X → Y` of histories is
*differentiable at `t` up to `j`* (`HDiffAt`) if `p ↦ f(u(p))` is differentiable at `p₀` for every
two-parameter family of histories `u : ℝ × ℝ → Seq X` with `u(p₀) = t` whose coordinates
`u(·)_0, …, u(·)_j` are differentiable at `p₀`. The hypothesis `HDiff`: `G_j`, `m_j`, `T_j` are
differentiable at every history in the *open part* of the domain (`InDhs`: `InDh`, `g_i < ε` for
`i ≤ j` and `G_j < ε`). For the RG map this is where all clamps are inactive.

Results, under `HHyp`, `ε ≤ ε₀`, `a ≤ a₀` and `HDiff`, for `b₀ ∈ (0, b_max)`:
* `traj_g_lt`: along admissible data `g_j < ε` for `j ≤ N` (strictly, since `b < b_max`);
* `traj_diffAt`: `(b, μ₀) ↦ s_j(b, μ₀)` is differentiable at `(b₀, μ₀^c(b₀))`;
* `traj_expand`, `eventually_traj_InD3`: the relevant coordinate expands,
  `|μ₀ - μ₁| ≤ |μ_N(b, μ₀) - μ_N(b, μ₁)|`, for initial data near `μ₀^c(b)`;
* `differentiableAt_muc`: `μ₀^c` is differentiable at `b₀` (by `Flow2.hasDerivAt_implicit`);
* `fh_flow_hist_diff`: `μ₀^c`, `ǧ_N` and all coordinates `s_j(b, μ₀^c(b))`, `j ≤ N`, are
  differentiable on `(0, b_max)`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] [∀ j, NormedSpace ℝ (X j)]

/-- **Differentiability of a map of histories at `t`, through the coordinates `0, …, j`.** -/
def HDiffAt {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (j : ℕ) (f : Seq X → Y)
    (t : Seq X) : Prop :=
  ∀ (u : ℝ × ℝ → Seq X) (p₀ : ℝ × ℝ), u p₀ = t →
    (∀ i ≤ j, DifferentiableAt ℝ (fun p => u p i) p₀) → DifferentiableAt ℝ (fun p => f (u p)) p₀

variable (F : HData X) (Λ β δ κ cg cm cT : ℝ)

/-- The open part of the domain at step `j`: `InDh`, `g_i < ε` for `i ≤ j`, and `G_j < ε`. -/
def InDhs (ε : ℝ) (j : ℕ) (t : Seq X) : Prop :=
  InDh Λ β δ κ cg cm cT ε j t ∧ (∀ i ≤ j, (t i).1 < ε) ∧ F.G j t < ε

/-- **The differentiability hypothesis**: `G_j`, `m_j`, `T_j` are differentiable on the open part of
the domain, for `j < N`. -/
structure HDiff (N : ℕ) (ε : ℝ) : Prop where
  G : ∀ j < N, ∀ t, InDhs F Λ β δ κ cg cm cT ε j t → HDiffAt j (F.G j) t
  m : ∀ j < N, ∀ t, InDhs F Λ β δ κ cg cm cT ε j t → HDiffAt j (F.m j) t
  T : ∀ j < N, ∀ t, InDhs F Λ β δ κ cg cm cT ε j t → HDiffAt j (F.T j) t

variable {F Λ β δ κ cg cm cT}

section Diff

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hε : 0 < ε)

include H he hε in
/-- Along admissible data with `b < b_max`, `g_j < ε` for `j ≤ N`. -/
lemma traj_g_lt {b μ₀ : ℝ} (hb : b ∈ Ioo 0 (bmax β δ cg N ε))
    (h : Admissible F Λ κ cm cT N ε b μ₀) : ∀ j ≤ N, (traj F Λ b μ₀ j).1 < ε := by
  intro j hj
  have hb' : b ∈ Ioc 0 (bmax β δ cg N ε) := ⟨hb.1, hb.2.le⟩
  have h1 := (trajc_InDh H he hε hb' μ₀ N le_rfl).2 j hj
  rw [trajc_eq_traj H h N le_rfl j hj] at h1
  have hg : 0 < (traj F Λ b μ₀ j).1 := (h.1 j hj).1
  have hbp : 0 ≤ betap β δ cg := by
    have := H.hδ; have := H.hβ; have := H.hcg; unfold betap; positivity
  have hp : 0 < 1 / ε + N * betap β δ cg := by positivity
  have hlt : 1 / ε + N * betap β δ cg < 1 / b := by
    have h2 := hb.2
    unfold bmax at h2
    exact (lt_one_div hb.1 hp).1 h2
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
  have h3 : (j : ℝ) * betap β δ cg ≤ N * betap β δ cg := mul_le_mul_of_nonneg_right hj' hbp
  have h4 : 1 / ε < 1 / (traj F Λ b μ₀ j).1 := by linarith
  exact (one_div_lt_one_div hε hg).1 h4

/-- The trajectory `traj` as a two-parameter family of histories. -/
abbrev trajF (F : HData X) (Λ : ℝ) : ℝ × ℝ → Seq X := fun p => traj F Λ p.1 p.2

include H he hε in
/-- **The trajectory is differentiable in `(b, μ₀)`** at admissible data with `b < b_max`. -/
theorem traj_diffAt (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ μ₀ : ℝ}
    (hb : b₀ ∈ Ioo 0 (bmax β δ cg N ε)) (h : Admissible F Λ κ cm cT N ε b₀ μ₀) :
    ∀ j ≤ N, DifferentiableAt ℝ (fun p : ℝ × ℝ => traj F Λ p.1 p.2 j) (b₀, μ₀) := by
  have hlt := traj_g_lt H he hε hb h
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
include H in
/-- Trajectories in `D_ε` up to `N` are regular histories. -/
lemma traj_InDh_of {b μ₀ : ℝ} (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) :
    ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨fun i hi => h i (by omega), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    refine ⟨fun i hi => h i (by omega), fun i hi => ?_⟩
    rcases (show i = j ∨ i < j by omega) with rfl | hij
    · rw [traj_succ H b μ₀ (by omega)]; exact H.F1 i (by omega) _ hs
    · exact hs.2 i hij

omit [∀ j, NormedSpace ℝ (X j)] in
include H in
/-- **Expansion of the relevant coordinate**: for two trajectories in `D_ε` up to `N` with the
same `b`, `|μ₀ - μ₁| ≤ |μ_N - μ'_N|`. -/
theorem traj_expand (ha0 : a ≤ a0h Λ κ A) {b μ₀ μ₁ : ℝ}
    (h₀ : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j))
    (h₁ : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₁ j)) :
    |μ₀ - μ₁| ≤ |(traj F Λ b μ₀ N).2.1 - (traj F Λ b μ₁ N).2.1| := by
  obtain ⟨hp0, hq0, eg, ex, em⟩ := coef_h H.hΛ H.hκ1 H.hA H.ha ha0
  have H₀ := traj_InDh_of H h₀
  have H₁ := traj_InDh_of H h₁
  set p := Kh Λ κ A * a
  set q := Qh κ * a
  set t := traj F Λ b μ₀
  set t' := traj F Λ b μ₁
  have key : ∀ k ≤ N,
      |(t k).1 - (t' k).1| ≤ p * |(t k).2.1 - (t' k).2.1| ∧
      ‖(t k).2.2 - (t' k).2.2‖ ≤ q * |(t k).2.1 - (t' k).2.1| ∧
      (∀ i < k, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t k).2.1 - (t' k).2.1|) ∧
      |μ₀ - μ₁| ≤ |(t k).2.1 - (t' k).2.1| := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [t, t', traj_zero, sub_self, abs_zero, norm_zero, le_refl, and_true]
      exact ⟨mul_nonneg hp0 (abs_nonneg _), mul_nonneg hq0 (abs_nonneg _),
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      obtain ⟨ig, ix, ih', iμ⟩ := ih (by omega)
      obtain ⟨s1, s2, s3, s4⟩ := unique_step H hp0 hq0 eg ex em hkN
        (H₀ k (by omega)) (H₁ k (by omega)) ig ix ih'
      have e0 := traj_succ H b μ₀ hkN
      have e1 := traj_succ H b μ₁ hkN
      simp only [t, t'] at s1 s2 s3 s4 ih' ig ix ⊢
      rw [e0, e1]
      refine ⟨s2, s3, fun i hi => ?_, iμ.trans s4⟩
      rcases (show i = k ∨ i < k by omega) with rfl | hik
      · have : dist3 (traj F Λ b μ₀ i) (traj F Λ b μ₁ i) ≤
            (1 + p + q) * |(traj F Λ b μ₀ i).2.1 - (traj F Λ b μ₁ i).2.1| := by
          unfold dist3
          nlinarith [abs_nonneg ((traj F Λ b μ₀ i).2.1 - (traj F Λ b μ₁ i).2.1)]
        exact this.trans (mul_le_mul_of_nonneg_left s4 (by positivity))
      · exact (ih' i hik).trans (mul_le_mul_of_nonneg_left s4 (by positivity))
  exact (key N le_rfl).2.2.2

omit [∀ j, NormedSpace ℝ (X j)] in
include H he hε in
/-- Near admissible initial data, the trajectories stay in `D_ε` up to `N` (the clamps of the
clamped flow are inactive there). -/
lemma eventually_traj_InD3 {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μs : ℝ}
    (h : Admissible F Λ κ cm cT N ε b μs) :
    ∀ᶠ μ in 𝓝 μs, ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ j) := by
  have h0 : (trajc F Λ cm b μs N).2.1 = 0 := by
    rw [trajc_eq_traj H h N le_rfl N le_rfl]; exact h.2
  have hs := trajc_strict H he hε hb h0
  have hev : ∀ᶠ μ in 𝓝 μs, ∀ k ∈ Finset.range (N + 1),
      |(trajc F Λ cm b μ k).2.1| < cmu Λ cm * (trajc F Λ cm b μ k).1 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hk' : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hc : Continuous (fun μ => trajc F Λ cm b μ k) :=
      (continuous_trajc H hk').comp (continuous_const.prodMk continuous_id)
    exact ContinuousAt.eventually_lt
      (continuous_abs.comp (continuous_fst.comp (continuous_snd.comp hc))).continuousAt
      (continuous_const.mul (continuous_fst.comp hc)).continuousAt (hs k hk')
  filter_upwards [hev] with μ hμ
  have hs' : ∀ k ≤ N, |(trajc F Λ cm b μ k).2.1| < cmu Λ cm * (trajc F Λ cm b μ k).1 :=
    fun k hk => hμ k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  have e : ∀ k ≤ N, ∀ i ≤ k, trajc F Λ cm b μ i = traj F Λ b μ i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      obtain rfl : i = 0 := by omega
      have h := hs' 0 (Nat.zero_le _)
      rw [trajc_zero, traj_zero, clamp_eq_of_abs_lt (r := cmu Λ cm * b) h]
    | succ k ih =>
      intro hk i hi
      rcases (show i = k + 1 ∨ i ≤ k by omega) with rfl | hik
      · have hall := ih (by omega)
        have h := hs' (k + 1) hk
        have hkN : k < N := by omega
        rw [trajc_succ H b μ hkN] at h ⊢
        rw [clamp_eq_of_abs_lt h, traj_succ H b μ hkN, H.causG k hkN _ _ hall,
          H.causm k hkN _ _ hall, H.causT k hkN _ _ hall, hall k le_rfl]
      · exact ih (by omega) i hik
  intro j hj
  rw [← e N le_rfl j hj]
  exact trajc_InD H he hε hb μ hj

include H he hε in
/-- **`μ₀^c` is differentiable** at every `b₀ ∈ (0, b_max)`. -/
theorem differentiableAt_muc (ha0 : a ≤ a0h Λ κ A) (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ : ℝ}
    (hb : b₀ ∈ Ioo 0 (bmax β δ cg N ε)) : DifferentiableAt ℝ (muc F Λ κ cm cT N ε) b₀ := by
  have hb' : b₀ ∈ Ioc 0 (bmax β δ cg N ε) := ⟨hb.1, hb.2.le⟩
  have hadm := muc_spec H he hε hb'
  have hnhds : Ioc 0 (bmax β δ cg N ε) ∈ 𝓝 b₀ :=
    Filter.mem_of_superset (Ioo_mem_nhds hb.1 hb.2) Ioo_subset_Ioc_self
  refine differentiableAt_implicit (φ := fun p : ℝ × ℝ => (traj F Λ p.1 p.2 N).2.1) one_pos
    (traj_diffAt H he hε HD hb hadm N le_rfl).snd.fst
    ((continuousOn_muc H he hε ha0).continuousAt hnhds) ?_ ?_
  · filter_upwards [hnhds] with b hb
    exact (muc_spec H he hε hb).2
  · filter_upwards [eventually_traj_InD3 H he hε hb' hadm] with μ hμ
    have h1 := traj_expand H ha0 hμ hadm.1
    rw [hadm.2, sub_zero] at h1
    simpa only [one_mul] using h1

include H he hε in
/-- **All coordinates along the admissible flow are differentiable in `b`.** -/
theorem differentiableAt_traj_muc (ha0 : a ≤ a0h Λ κ A) (HD : HDiff F Λ β δ κ cg cm cT N ε)
    {b₀ : ℝ} (hb : b₀ ∈ Ioo 0 (bmax β δ cg N ε)) {j : ℕ} (hj : j ≤ N) :
    DifferentiableAt ℝ (fun b => traj F Λ b (muc F Λ κ cm cT N ε b) j) b₀ := by
  have hb' : b₀ ∈ Ioc 0 (bmax β δ cg N ε) := ⟨hb.1, hb.2.le⟩
  have h1 := traj_diffAt H he hε HD hb (muc_spec H he hε hb') j hj
  have h2 : DifferentiableAt ℝ (fun b => ((b, muc F Λ κ cm cT N ε b) : ℝ × ℝ)) b₀ :=
    differentiableAt_id.prodMk (differentiableAt_muc H he hε ha0 HD hb)
  exact h1.comp b₀ h2

include H he hε in
/-- **`ǧ_N` is differentiable** on `(0, b_max)`. -/
theorem differentiableAt_gN (ha0 : a ≤ a0h Λ κ A) (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ : ℝ}
    (hb : b₀ ∈ Ioo 0 (bmax β δ cg N ε)) : DifferentiableAt ℝ (gN F Λ κ cm cT N ε) b₀ :=
  (differentiableAt_traj_muc H he hε ha0 HD hb le_rfl).fst

include H he hε in
/-- **Proposition `prop:C6`, differentiability (`thm:flow`(iii))**: `μ₀^c`, `ǧ_N` and every
coordinate `s_j(b, μ₀^c(b))`, `j ≤ N`, are differentiable on `(0, b_max)`. -/
theorem fh_flow_hist_diff (ha0 : a ≤ a0h Λ κ A) (HD : HDiff F Λ β δ κ cg cm cT N ε) :
    DifferentiableOn ℝ (muc F Λ κ cm cT N ε) (Ioo 0 (bmax β δ cg N ε)) ∧
    DifferentiableOn ℝ (gN F Λ κ cm cT N ε) (Ioo 0 (bmax β δ cg N ε)) ∧
    ∀ j ≤ N, DifferentiableOn ℝ (fun b => traj F Λ b (muc F Λ κ cm cT N ε b) j)
      (Ioo 0 (bmax β δ cg N ε)) :=
  ⟨fun _ hb => (differentiableAt_muc H he hε ha0 HD hb).differentiableWithinAt,
    fun _ hb => (differentiableAt_gN H he hε ha0 HD hb).differentiableWithinAt,
    fun _ hj _ hb => (differentiableAt_traj_muc H he hε ha0 HD hb hj).differentiableWithinAt⟩

end Diff

end Hist

end Flow2
