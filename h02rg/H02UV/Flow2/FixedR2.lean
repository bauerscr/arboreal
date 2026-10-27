import Flow2.FixedR

/-!
# Shooting at fixed `β_R`: continuation in `b`

* `local_adm`: if `μ₁` is admissible for `b₁` with `ǧ_N < y ≤ ε`, then for every `η > 0`, every
  `b` near `b₁` has an admissible `μ` with `|μ - μ₁| < η` and `ǧ_N < y`;
* `muc_eq_of_adm`, `gN_eq_of_adm`: by uniqueness, `μ₀(b)` and `ǧ_N(b)` are those of any
  admissible trajectory from `b`;
* `continuousAt_muc_fixed`, `continuousAt_gN_fixed`, `isOpen_Ufix`: `Ufix` (an admissible
  trajectory with `ǧ_N < ε`) is open and `μ₀`, `ǧ_N` are continuous on it.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

section Cont

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
include H he hgβ ha0

omit ha0 in
/-- `OKR` holds on a box around an admissible point with `ǧ_N < y`. -/
lemma OKR_box {y b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
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
theorem local_adm {y : ℝ} (hy : y ≤ ε) {b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
    (hg₁ : (traj F Λ b₁ μ₁ N).1 < y) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ b, |b - b₁| < r → ∃ μ, |μ - μ₁| < η ∧ Admissible F Λ κ cm cT N ε b μ ∧
      (traj F Λ b μ N).1 < y := by
  obtain ⟨r₀, hr₀, hbox⟩ := OKR_box H he hgβ h₁ hg₁
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
  have cp := cone_signed H ha0 (show μ₁ ≤ μ₁ + η' by linarith)
    (inDh_of_OKR H he hy hp) h1D
  have cm' := cone_signed H ha0 (show μ₁ - η' ≤ μ₁ by linarith) h1D
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
lemma muc_eq_of_adm {b μ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ) :
    muc F Λ κ cm cT N ε b = μ := by
  have hex : ∃ μ₀, Admissible F Λ κ cm cT N ε b μ₀ := ⟨μ, h⟩
  have hs : Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := by
    simp only [muc, dif_pos hex]; exact hex.choose_spec
  exact admissible_unique H ha0 hs h

omit he hgβ in
lemma gN_eq_of_adm {b μ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ) :
    gN F Λ κ cm cT N ε b = (traj F Λ b μ N).1 := by
  unfold gN; rw [muc_eq_of_adm H ha0 h]

omit he hgβ in
lemma muc_spec_of {b μ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ) :
    Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := by
  rw [muc_eq_of_adm H ha0 h]; exact h

/-- **Continuity of `μ₀(b)`** at every `b` with an admissible trajectory and `ǧ_N < ε`. -/
theorem continuousAt_muc_fixed {b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
    (hg₁ : (traj F Λ b₁ μ₁ N).1 < ε) : ContinuousAt (muc F Λ κ cm cT N ε) b₁ := by
  rw [Metric.continuousAt_iff]
  intro η hη
  obtain ⟨r, hr, hloc⟩ := local_adm H he hgβ ha0 le_rfl h₁ hg₁ hη
  refine ⟨r, hr, fun b hb => ?_⟩
  rw [Real.dist_eq] at hb
  obtain ⟨μ, hμ, hadm, -⟩ := hloc b hb
  rw [muc_eq_of_adm H ha0 hadm, muc_eq_of_adm H ha0 h₁, Real.dist_eq]
  exact hμ

/-- **Continuity of `ǧ_N(b)`** at every `b` with an admissible trajectory and `ǧ_N < ε`. -/
theorem continuousAt_gN_fixed {b₁ μ₁ : ℝ} (h₁ : Admissible F Λ κ cm cT N ε b₁ μ₁)
    (hg₁ : (traj F Λ b₁ μ₁ N).1 < ε) : ContinuousAt (gN F Λ κ cm cT N ε) b₁ := by
  have hm := continuousAt_muc_fixed H he hgβ ha0 h₁ hg₁
  have hc : Continuous fun p : ℝ × ℝ => (traj F Λ p.1 p.2 N).1 :=
    continuous_fst.comp (continuous_traj H le_rfl)
  exact hc.continuousAt.comp (f := fun b => (b, muc F Λ κ cm cT N ε b))
    (continuousAt_id.prodMk hm)

/-- `Ufix` is open. -/
theorem isOpen_Ufix : IsOpen (Ufix F Λ κ cm cT N ε) := by
  rw [Metric.isOpen_iff]
  rintro b₁ ⟨μ₁, h₁, hg₁⟩
  obtain ⟨r, hr, hloc⟩ := local_adm H he hgβ ha0 le_rfl h₁ hg₁ one_pos
  refine ⟨r, hr, fun b hb => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hb
  obtain ⟨μ, -, hadm, hlt⟩ := hloc b hb
  exact ⟨μ, hadm, hlt⟩

theorem continuousOn_muc_Ufix : ContinuousOn (muc F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) :=
  fun _ ⟨_, h₁, hg₁⟩ => (continuousAt_muc_fixed H he hgβ ha0 h₁ hg₁).continuousWithinAt

theorem continuousOn_gN_Ufix : ContinuousOn (gN F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) :=
  fun _ ⟨_, h₁, hg₁⟩ => (continuousAt_gN_fixed H he hgβ ha0 h₁ hg₁).continuousWithinAt

end Cont

end Hist

end Flow2
