import Flow2.FixedR3
import Flow2.FixedRParamZ1

/-!
# Shooting at fixed `β_R`, generic form (signed cone and monotonicity as hypotheses)

Copies of `Flow2/FixedR2.lean`, `Flow2/FixedR3.lean` in which the smallness `a ≤ a0h` of the
`HHyp` constant is replaced by the signed cone `ConeS` (`Flow2/FixedRParamZ1.lean`), and
`MonoHyp`/`MonoCoef` by the strict monotonicity of `ǧ_N` on the admissible `b`. So `HHyp` may have
large constants (as in `Step2.thm_flow_hor2`), and the cone and the monotonicity may come from a
separate channel (`ZHyp`, `MonoZHyp`).

`local_adm_g`, `muc_eq_of_adm_g`, `continuousAt_muc_fixed_g`, `isOpen_Ufix_g`,
`Icc_subset_SetLe_g`, `exists_traj_eq_g`, `ordConnected_Ufix_g`, `fh_flow_fixedR_g`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

section Cont

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
include H he hgβ hC

omit hC in
/-- `OKR` holds on a box around an admissible point with `ǧ_N < y`. -/
lemma OKR_box_g {y b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
    (hg₁ : (traj F Λ b₁ μ₁ N).1 < y) :
    ∃ r > 0, ∀ b μ, |b - b₁| < r → |μ - μ₁| < r → OKR F Λ cm N y b μ := by
  have hO := OKR_of_adm H he hgβ h₁ hg₁
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (b₁, μ₁), OKR F Λ cm N y p.1 p.2 := by
    refine (continuousAt_const.eventually_lt continuous_fst.continuousAt hO.1).and ?_
    refine (eventually_all_finite (finite_le_nat N)).2 fun j hj => ?_
    have hc := continuous_traj H (show j ≤ N from hj)
    have hg : Continuous fun p : ℝ × ℝ => (traj F Λ p.1 p.2 j).1 := continuous_fst.comp hc
    have hμ : Continuous fun p : ℝ × ℝ => |(traj F Λ p.1 p.2 j).2.1| :=
      (continuous_fst.comp (continuous_snd.comp hc)).abs
    exact (hg.continuousAt.eventually_lt continuousAt_const (hO.2 j hj).1).and
      (hμ.continuousAt.eventually_lt (continuousAt_const.mul hg.continuousAt) (hO.2 j hj).2)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r, hr, fun b μ hb hμ => hball (y := (b, μ)) ?_⟩
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt hb hμ

/-- **Local continuation of the admissible `μ₀`.** -/
theorem local_adm_g {y : ℝ} (hy : y ≤ ε) {b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
    (hg₁ : (traj F Λ b₁ μ₁ N).1 < y) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ b, |b - b₁| < r → ∃ μ, |μ - μ₁| < η ∧ Admissible F Λ κ cm cT N ε b μ ∧
      (traj F Λ b μ N).1 < y := by
  obtain ⟨r₀, hr₀, hbox⟩ := OKR_box_g H he hgβ h₁ hg₁
  obtain ⟨η', hη'⟩ : ∃ η', η' = min η r₀ / 2 := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; exact half_pos (lt_min hη hr₀)
  have hη'1 : η' < η := by rw [hη']; linarith [min_le_left η r₀]
  have hη'2 : η' < r₀ := by rw [hη']; linarith [min_le_right η r₀]
  have hb0 : |b₁ - b₁| < r₀ := by rw [sub_self, abs_zero]; exact hr₀
  have hp : OKR F Λ cm N y b₁ (μ₁ + η') :=
    hbox _ _ hb0 (by rw [add_sub_cancel_left, abs_of_pos hη'0]; exact hη'2)
  have hm : OKR F Λ cm N y b₁ (μ₁ - η') :=
    hbox _ _ hb0 (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη'0]; exact hη'2)
  have h1D := admissible_InDh H h₁
  have cp := hC b₁ _ _ (show μ₁ ≤ μ₁ + η' by linarith)
    (inDh_of_OKR H he hy hp) h1D
  have cm' := hC b₁ _ _ (show μ₁ - η' ≤ μ₁ by linarith) h1D
    (inDh_of_OKR H he hy hm)
  rw [h₁.2] at cp cm'
  have hpos : 0 < (traj F Λ b₁ (μ₁ + η') N).2.1 := by linarith
  have hneg : (traj F Λ b₁ (μ₁ - η') N).2.1 < 0 := by linarith
  have e1 : ∀ᶠ b in 𝓝 b₁, 0 < (traj F Λ b (μ₁ + η') N).2.1 :=
    (continuous_traj_b H _).continuousAt.eventually (lt_mem_nhds hpos)
  have e2 : ∀ᶠ b in 𝓝 b₁, (traj F Λ b (μ₁ - η') N).2.1 < 0 :=
    (continuous_traj_b H _).continuousAt.eventually (gt_mem_nhds hneg)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun b hb => ?_⟩
  obtain ⟨h1, h2⟩ := hball (show dist b b₁ < r₁ by
    rw [Real.dist_eq]; exact hb.trans_le (min_le_right _ _))
  obtain ⟨μ, hmem, hz⟩ := intermediate_value_Icc (by linarith : μ₁ - η' ≤ μ₁ + η')
    (continuous_traj_mu H b).continuousOn ⟨h2.le, h1.le⟩
  have hμ : |μ - μ₁| ≤ η' := abs_le.2 ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hO := hbox b μ (hb.trans_le (min_le_left _ _)) (hμ.trans_lt hη'2)
  exact ⟨μ, hμ.trans_lt hη'1, adm_of_OKR H he hy hO hz, (hO.2 N le_rfl).1⟩

omit he hgβ in
/-- `μ₀(b)` is the admissible `μ₀` whenever there is one. -/
lemma muc_eq_of_adm_g {b μ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ) :
    muc F Λ κ cm cT N ε b = μ := by
  have hex : ∃ μ₀, Admissible F Λ κ cm cT N ε b μ₀ := ⟨μ, h⟩
  have hs : Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := by
    simp only [muc, dif_pos hex]; exact hex.choose_spec
  exact unique_of_coneS H hC hs h

omit he hgβ in
lemma gN_eq_of_adm_g {b μ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ) :
    gN F Λ κ cm cT N ε b = (traj F Λ b μ N).1 := by
  unfold gN; rw [muc_eq_of_adm_g H hC h]

omit he hgβ in
lemma muc_spec_of_g {b μ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ) :
    Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := by
  rw [muc_eq_of_adm_g H hC h]; exact h

/-- **Continuity of `μ₀(b)`** at every `b` with an admissible trajectory and `ǧ_N < ε`. -/
theorem continuousAt_muc_fixed_g {b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
    (hg₁ : (traj F Λ b₁ μ₁ N).1 < ε) : ContinuousAt (muc F Λ κ cm cT N ε) b₁ := by
  rw [Metric.continuousAt_iff]
  intro η hη
  obtain ⟨r, hr, hloc⟩ := local_adm_g H he hgβ hC le_rfl h₁ hg₁ hη
  refine ⟨r, hr, fun b hb => ?_⟩
  rw [Real.dist_eq] at hb
  obtain ⟨μ, hμ, hadm, -⟩ := hloc b hb
  rw [muc_eq_of_adm_g H hC hadm, muc_eq_of_adm_g H hC h₁, Real.dist_eq]
  exact hμ

/-- **Continuity of `ǧ_N(b)`** at every `b` with an admissible trajectory and `ǧ_N < ε`. -/
theorem continuousAt_gN_fixed_g {b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
    (hg₁ : (traj F Λ b₁ μ₁ N).1 < ε) : ContinuousAt (gN F Λ κ cm cT N ε) b₁ := by
  have hm := continuousAt_muc_fixed_g H he hgβ hC h₁ hg₁
  have hc : Continuous fun p : ℝ × ℝ => (traj F Λ p.1 p.2 N).1 :=
    continuous_fst.comp (continuous_traj H le_rfl)
  exact hc.continuousAt.comp (f := fun b => (b, muc F Λ κ cm cT N ε b))
    (continuousAt_id.prodMk hm)

/-- `Ufix` is open. -/
theorem isOpen_Ufix_g : IsOpen (Ufix F Λ κ cm cT N ε) := by
  rw [Metric.isOpen_iff]
  rintro b₁ ⟨μ₁, h₁, hg₁⟩
  obtain ⟨r, hr, hloc⟩ := local_adm_g H he hgβ hC le_rfl h₁ hg₁ one_pos
  refine ⟨r, hr, fun b hb => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hb
  obtain ⟨μ, -, hadm, hlt⟩ := hloc b hb
  exact ⟨μ, hadm, hlt⟩

theorem continuousOn_muc_Ufix_g : ContinuousOn (muc F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) :=
  fun _ ⟨_, h₁, hg₁⟩ => (continuousAt_muc_fixed_g H he hgβ hC h₁ hg₁).continuousWithinAt

theorem continuousOn_gN_Ufix_g : ContinuousOn (gN F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) :=
  fun _ ⟨_, h₁, hg₁⟩ => (continuousAt_gN_fixed_g H he hgβ hC h₁ hg₁).continuousWithinAt

end Cont

section Induct

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
include H he hgβ hC

/-- **Continuous induction in `b`.** -/
theorem Icc_subset_SetLe_g {b₀ b₂ y : ℝ} (hb₀ : 0 < b₀) (hy : y ≤ ε)
    (h0 : b₀ ∈ SetLe F Λ κ cm cT N ε y)
    (hne : ∀ x ∈ Ico b₀ b₂, ∀ μ, Admissible F Λ κ cm cT N ε x μ → (traj F Λ x μ N).1 ≠ y) :
    Icc b₀ b₂ ⊆ SetLe F Λ κ cm cT N ε y := by
  refine (isClosed_SetLe H hgβ hb₀).Icc_subset_of_forall_exists_gt h0 ?_
  rintro x ⟨⟨μ, hadm, hle⟩, hx⟩ z hz
  have hlt : (traj F Λ x μ N).1 < y := lt_of_le_of_ne hle (hne x hx μ hadm)
  obtain ⟨r, hr, hloc⟩ := local_adm_g H he hgβ hC hy hadm hlt one_pos
  have hz' : x < z := hz
  obtain ⟨b', hb'⟩ : ∃ b', b' = min (x + r / 2) z := ⟨_, rfl⟩
  have h1 : x < b' := by rw [hb']; exact lt_min (by linarith) hz'
  have h2 : b' ≤ z := by rw [hb']; exact min_le_right _ _
  have h3 : b' ≤ x + r / 2 := by rw [hb']; exact min_le_left _ _
  have h4 : |b' - x| < r := by rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨μ', -, hadm', hlt'⟩ := hloc b' h4
  exact ⟨b', ⟨μ', hadm', hlt'.le⟩, h1, h2⟩

omit hgβ hC in
include he in
/-- A starting point: `b₀ = (1/y + N β₊)⁻¹` has an admissible trajectory with `ǧ_N ≤ y`. -/
lemma start_SetLe_g (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y ≤ ε) :
    0 < 1 / (1 / y + N * betap β δ cg) ∧ 1 / (1 / y + N * betap β δ cg) ≤ y ∧
      1 / (1 / y + N * betap β δ cg) ∈ SetLe F Λ κ cm cT N ε y := by
  have hbp : 0 ≤ (N : ℝ) * betap β δ cg := by
    have := H.hβ; have := H.hδ; have := H.hcg; unfold betap; positivity
  have hd : 0 < 1 / y + N * betap β δ cg := by positivity
  have hb0 : 0 < 1 / (1 / y + N * betap β δ cg) := one_div_pos.2 hd
  have hinv : 1 / (1 / (1 / y + N * betap β δ cg)) = 1 / y + N * betap β δ cg := one_div_one_div _
  have hyε : 1 / ε ≤ 1 / y := one_div_le_one_div_of_le hy0 hy
  have hbm : 1 / (1 / y + N * betap β δ cg) ≤ bmax β δ cg N ε := by
    unfold bmax
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmem : 1 / (1 / y + N * betap β δ cg) ∈ Ioc 0 (bmax β δ cg N ε) := ⟨hb0, hbm⟩
  have hle : 1 / (1 / y + N * betap β δ cg) ≤ y := by
    rw [div_le_iff₀ hd]
    have : 1 = y * (1 / y) := by rw [mul_one_div_cancel hy0.ne']
    nlinarith
  refine ⟨hb0, hle, muc F Λ κ cm cT N ε _, muc_spec H he hε hmem, ?_⟩
  have h := gN_le H he hε hmem
  rw [hinv, add_sub_cancel_right, one_div_one_div] at h
  exact h

include he in
/-- **Every final coupling `y ∈ (0, ε]` is attained** by an admissible trajectory from some
`b ∈ (0, y]`. -/
theorem exists_traj_eq_g (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y ≤ ε) :
    ∃ b ∈ Ioc 0 y, ∃ μ, Admissible F Λ κ cm cT N ε b μ ∧ (traj F Λ b μ N).1 = y := by
  obtain ⟨hb0, hby, h0⟩ := start_SetLe_g H he hε hy0 hy
  by_contra hcon
  push Not at hcon
  have hsub := Icc_subset_SetLe_g H he hgβ hC hb0 hy h0 fun x hx μ hadm =>
    hcon x ⟨hb0.trans_le hx.1, hx.2.le⟩ μ hadm
  obtain ⟨μ, hadm, hle⟩ := hsub ⟨hby, le_rfl⟩
  have hge := b_le_traj_fst H hgβ hadm N le_rfl
  exact hcon y ⟨hy0, le_rfl⟩ μ hadm (le_antisymm hle hge)

end Induct

/-! ### With strict monotonicity -/

section Fixed

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
  (hM : StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ})
include H he hgβ hC hM

/-- `Ufix` is order connected. -/
theorem ordConnected_Ufix_g : (Ufix F Λ κ cm cT N ε).OrdConnected := by
  refine ⟨fun b₁ hb₁ b₂ hb₂ b hb => ?_⟩
  obtain ⟨μ₁, h₁, -⟩ := hb₁
  obtain ⟨μ₂, h₂, hg₂⟩ := hb₂
  have hmono := hM
  have hb₁0 : 0 < b₁ := by have := (h₁.1 0 (Nat.zero_le _)).1; rwa [traj_zero] at this
  have hy : (traj F Λ b₂ μ₂ N).1 ≤ ε := hg₂.le
  have h0 : b₁ ∈ SetLe F Λ κ cm cT N ε (traj F Λ b₂ μ₂ N).1 := by
    refine ⟨μ₁, h₁, ?_⟩
    rw [← gN_eq_of_adm_g H hC h₁, ← gN_eq_of_adm_g H hC h₂]
    exact hmono.monotoneOn ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩ (hb.1.trans hb.2)
  have hsub := Icc_subset_SetLe_g H he hgβ hC hb₁0 hy h0 fun x hx μ hadm heq => by
    have := hmono ⟨μ, hadm⟩ ⟨μ₂, h₂⟩ hx.2
    rw [gN_eq_of_adm_g H hC hadm, gN_eq_of_adm_g H hC h₂, heq] at this
    exact lt_irrefl _ this
  obtain ⟨μ, hadm, hle⟩ := hsub hb
  exact ⟨μ, hadm, hle.trans_lt hg₂⟩

/-- **Shooting at fixed `β_R`** (abstract form, generic). Under `HHyp` (any constants), the
signed cone `ConeS`, strict monotonicity of `ǧ_N` on the admissible `b` and `c_g ε ≤ (1-δ)β`:
* for every `μ₀`-admissible `b` the admissible `μ₀` is unique;
* for every `y ∈ (0, ε]` there is a unique `b` with an admissible trajectory and `ǧ_N(b) = y`,
  and `b ≤ y`;
* `Ufix = {b : admissible trajectory, ǧ_N < ε}` is open and order connected, `μ₀(b)` and `ǧ_N(b)`
  are continuous on it, `ǧ_N` is strictly increasing on all `b` with an admissible trajectory,
  and `ǧ_N` maps `Ufix` onto `(0, ε)`. -/
theorem fh_flow_fixedR_g (hε : 0 < ε) :
    (∀ b μ μ', Admissible F Λ κ cm cT N ε b μ → Admissible F Λ κ cm cT N ε b μ' → μ = μ') ∧
    (∀ y, 0 < y → y ≤ ε → ∃! b, (∃ μ, Admissible F Λ κ cm cT N ε b μ) ∧
      gN F Λ κ cm cT N ε b = y) ∧
    (∀ y, 0 < y → y ≤ ε → ∀ b, (∃ μ, Admissible F Λ κ cm cT N ε b μ) →
      gN F Λ κ cm cT N ε b = y → b ∈ Ioc 0 y) ∧
    IsOpen (Ufix F Λ κ cm cT N ε) ∧ (Ufix F Λ κ cm cT N ε).OrdConnected ∧
    ContinuousOn (muc F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) ∧
    ContinuousOn (gN F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) ∧
    StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ} ∧
    gN F Λ κ cm cT N ε '' Ufix F Λ κ cm cT N ε = Ioo 0 ε := by
  have hmono := hM
  have hle : ∀ b μ, Admissible F Λ κ cm cT N ε b μ →
      0 < b ∧ b ≤ gN F Λ κ cm cT N ε b := fun b μ h => by
    refine ⟨?_, ?_⟩
    · have := (h.1 0 (Nat.zero_le _)).1; rwa [traj_zero] at this
    · rw [gN_eq_of_adm_g H hC h]; exact b_le_traj_fst H hgβ h N le_rfl
  refine ⟨fun b μ μ' h h' => unique_of_coneS H hC h h', fun y hy0 hy => ?_,
    fun y _ _ b ⟨μ, h⟩ hb => ?_, isOpen_Ufix_g H he hgβ hC, ordConnected_Ufix_g H he hgβ hC hM,
    continuousOn_muc_Ufix_g H he hgβ hC, continuousOn_gN_Ufix_g H he hgβ hC, hmono, ?_⟩
  · obtain ⟨b, -, μ, hadm, heq⟩ := exists_traj_eq_g H he hgβ hC hε hy0 hy
    refine ⟨b, ⟨⟨μ, hadm⟩, by rw [gN_eq_of_adm_g H hC hadm, heq]⟩, fun b' ⟨hb', hg'⟩ => ?_⟩
    exact unique_of_strictMonoOn hmono hb' ⟨μ, hadm⟩ hg'
      (by rw [gN_eq_of_adm_g H hC hadm, heq])
  · obtain ⟨h1, h2⟩ := hle b μ h
    exact ⟨h1, hb ▸ h2⟩
  · ext y
    constructor
    · rintro ⟨b, ⟨μ, h, hlt⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hle b μ h
      rw [gN_eq_of_adm_g H hC h] at h2 ⊢
      exact ⟨h1.trans_le h2, hlt⟩
    · rintro ⟨hy0, hy⟩
      obtain ⟨b, -, μ, hadm, heq⟩ := exists_traj_eq_g H he hgβ hC hε hy0 hy.le
      exact ⟨b, ⟨μ, hadm, heq ▸ hy⟩, by rw [gN_eq_of_adm_g H hC hadm, heq]⟩

end Fixed

end Hist

end Flow2
