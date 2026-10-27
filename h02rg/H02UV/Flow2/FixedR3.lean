import Flow2.FixedR2
import Flow2.Mono

/-!
# Shooting at fixed `β_R`: every final coupling `ǧ_N = y ∈ (0, ε]` is attained

* `isClosed_SetLe`: the set of `b ∈ [b₀, b₂]` with an admissible trajectory and `ǧ_N ≤ y` is
  closed (`b₀ > 0`; projection of a compact set of `(b, μ₀)`);
* `Icc_subset_SetLe` (continuous induction): if `b₀` has an admissible trajectory with `ǧ_N ≤ y`
  (`y ≤ ε`), and no `x ∈ [b₀, b₂)` has an admissible trajectory with `ǧ_N = y`, then every
  `b ∈ [b₀, b₂]` has an admissible trajectory with `ǧ_N ≤ y` (by `local_adm`);
* `exists_traj_eq`: **for every `y ∈ (0, ε]` there are `b ∈ (0, y]` and an admissible `μ₀`
  with `ǧ_N = y`**. Start at `b₀ = (1/y + N β₊)⁻¹ ≤ b_max`, where `ǧ_N(b₀) ≤ y`, and use
  `ǧ_N(y) ≥ y`;
* `fh_flow_fixedR`: with strict monotonicity (`MonoHyp`, `MonoCoef`): for every `y ∈ (0, ε]`
  a unique `b` with an admissible trajectory and `ǧ_N(b) = y`; `Ufix` is an open interval
  `(0, b*)` on which `μ₀(b)`, `ǧ_N(b)` are continuous and `ǧ_N` is strictly increasing, and
  `ǧ_N` maps `Ufix` onto `(0, ε)`.
The threshold `β_R ≥ 1/ε` is independent of `N`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

variable (F Λ κ cm cT) in
/-- The initial couplings with an admissible trajectory and `ǧ_N ≤ y`. -/
def SetLe (N : ℕ) (ε y : ℝ) : Set ℝ :=
  {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ ∧ (traj F Λ b μ N).1 ≤ y}

section Closed

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (hgβ : cg * ε ≤ (1 - δ) * β)
include H hgβ

variable (F Λ κ cm cT) in
/-- The closed conditions on `(b, μ₀)`. -/
def KSet (N : ℕ) (ε y b₀ : ℝ) : Set (ℝ × ℝ) :=
  (⋂ j ∈ {j : ℕ | j ≤ N},
    ({p : ℝ × ℝ | b₀ ≤ (traj F Λ p.1 p.2 j).1} ∩ {p | (traj F Λ p.1 p.2 j).1 ≤ ε} ∩
      {p | |(traj F Λ p.1 p.2 j).2.1| ≤ cmu Λ cm * (traj F Λ p.1 p.2 j).1} ∩
      {p | ‖(traj F Λ p.1 p.2 j).2.2‖ ≤ cx κ cT * (traj F Λ p.1 p.2 j).1 ^ 3})) ∩
    {p | (traj F Λ p.1 p.2 N).2.1 = 0} ∩ {p | (traj F Λ p.1 p.2 N).1 ≤ y}

omit hgβ in
lemma isClosed_KSet (y b₀ : ℝ) : IsClosed (KSet F Λ κ cm cT N ε y b₀) := by
  have hg : ∀ j ≤ N, Continuous fun p : ℝ × ℝ => (traj F Λ p.1 p.2 j).1 :=
    fun j hj => continuous_fst.comp (continuous_traj H hj)
  have hμ : ∀ j ≤ N, Continuous fun p : ℝ × ℝ => (traj F Λ p.1 p.2 j).2.1 :=
    fun j hj => continuous_fst.comp (continuous_snd.comp (continuous_traj H hj))
  have hx : ∀ j ≤ N, Continuous fun p : ℝ × ℝ => (traj F Λ p.1 p.2 j).2.2 :=
    fun j hj => continuous_snd.comp (continuous_snd.comp (continuous_traj H hj))
  refine ((isClosed_biInter fun j hj => ?_).inter
    (isClosed_eq (hμ N le_rfl) continuous_const)).inter
    (isClosed_le (hg N le_rfl) continuous_const)
  have hj' : j ≤ N := hj
  exact (((isClosed_le continuous_const (hg j hj')).inter
    (isClosed_le (hg j hj') continuous_const)).inter
    (isClosed_le (hμ j hj').abs (continuous_const.mul (hg j hj')))).inter
    (isClosed_le (hx j hj').norm (continuous_const.mul ((hg j hj').pow 3)))

lemma SetLe_eq {b₀ b₂ y : ℝ} (hb₀ : 0 < b₀) :
    SetLe F Λ κ cm cT N ε y ∩ Icc b₀ b₂ = Prod.fst ''
      (Icc b₀ b₂ ×ˢ Icc (-(cmu Λ cm * b₂)) (cmu Λ cm * b₂) ∩ KSet F Λ κ cm cT N ε y b₀) := by
  ext b
  constructor
  · rintro ⟨⟨μ, hadm, hle⟩, hb⟩
    refine ⟨(b, μ), ⟨⟨hb, ?_⟩, ?_⟩, rfl⟩
    · have h0 := (hadm.1 0 (Nat.zero_le _)).2.2.1
      rw [traj_zero] at h0
      have : cmu Λ cm * b ≤ cmu Λ cm * b₂ :=
        mul_le_mul_of_nonneg_left hb.2 (cmu_pos H.hΛ H.hcm).le
      exact abs_le.1 (h0.trans this)
    · refine ⟨⟨?_, hadm.2⟩, hle⟩
      simp only [mem_iInter, mem_setOf_eq]
      intro j hj
      have hD := hadm.1 j hj
      exact ⟨⟨⟨hb.1.trans (b_le_traj_fst H hgβ hadm j hj), hD.2.1⟩, hD.2.2.1⟩, hD.2.2.2⟩
  · rintro ⟨⟨b', μ⟩, ⟨⟨hb, -⟩, ⟨hK, h0⟩, hle⟩, rfl⟩
    simp only [mem_iInter, mem_setOf_eq] at hK
    refine ⟨⟨μ, ⟨fun j hj => ?_, h0⟩, hle⟩, hb⟩
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hK j hj
    exact ⟨hb₀.trans_le h1, h2, h3, h4⟩

/-- The set of `b ∈ [b₀, b₂]` with an admissible trajectory and `ǧ_N ≤ y` is closed. -/
theorem isClosed_SetLe {b₀ b₂ y : ℝ} (hb₀ : 0 < b₀) :
    IsClosed (SetLe F Λ κ cm cT N ε y ∩ Icc b₀ b₂) := by
  rw [SetLe_eq H hgβ hb₀]
  exact (((isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_KSet H y b₀)).image
    continuous_fst).isClosed

end Closed

section Induct

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
include H he hgβ ha0

/-- **Continuous induction in `b`.** -/
theorem Icc_subset_SetLe {b₀ b₂ y : ℝ} (hb₀ : 0 < b₀) (hy : y ≤ ε)
    (h0 : b₀ ∈ SetLe F Λ κ cm cT N ε y)
    (hne : ∀ x ∈ Ico b₀ b₂, ∀ μ, Admissible F Λ κ cm cT N ε x μ → (traj F Λ x μ N).1 ≠ y) :
    Icc b₀ b₂ ⊆ SetLe F Λ κ cm cT N ε y := by
  refine (isClosed_SetLe H hgβ hb₀).Icc_subset_of_forall_exists_gt h0 ?_
  rintro x ⟨⟨μ, hadm, hle⟩, hx⟩ z hz
  have hlt : (traj F Λ x μ N).1 < y := lt_of_le_of_ne hle (hne x hx μ hadm)
  obtain ⟨r, hr, hloc⟩ := local_adm H he hgβ ha0 hy hadm hlt one_pos
  have hz' : x < z := hz
  obtain ⟨b', hb'⟩ : ∃ b', b' = min (x + r / 2) z := ⟨_, rfl⟩
  have h1 : x < b' := by rw [hb']; exact lt_min (by linarith) hz'
  have h2 : b' ≤ z := by rw [hb']; exact min_le_right _ _
  have h3 : b' ≤ x + r / 2 := by rw [hb']; exact min_le_left _ _
  have h4 : |b' - x| < r := by rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨μ', -, hadm', hlt'⟩ := hloc b' h4
  exact ⟨b', ⟨μ', hadm', hlt'.le⟩, h1, h2⟩

omit hgβ ha0 in
include he in
/-- A starting point: `b₀ = (1/y + N β₊)⁻¹` has an admissible trajectory with `ǧ_N ≤ y`. -/
lemma start_SetLe (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y ≤ ε) :
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
theorem exists_traj_eq (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y ≤ ε) :
    ∃ b ∈ Ioc 0 y, ∃ μ, Admissible F Λ κ cm cT N ε b μ ∧ (traj F Λ b μ N).1 = y := by
  obtain ⟨hb0, hby, h0⟩ := start_SetLe H he hε hy0 hy
  by_contra hcon
  push Not at hcon
  have hsub := Icc_subset_SetLe H he hgβ ha0 hb0 hy h0 fun x hx μ hadm =>
    hcon x ⟨hb0.trans_le hx.1, hx.2.le⟩ μ hadm
  obtain ⟨μ, hadm, hle⟩ := hsub ⟨hby, le_rfl⟩
  have hge := b_le_traj_fst H hgβ hadm N le_rfl
  exact hcon y ⟨hy0, le_rfl⟩ μ hadm (le_antisymm hle hge)

end Induct

/-! ### With strict monotonicity -/

section Fixed

variable {N : ℕ} {A a ε w p q r p₂ q₂ r₂ : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w) (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
include H HM hC ha0

omit HM hC in
lemma adm_muc {S : Set ℝ} (hS : ∀ b ∈ S, ∃ μ, Admissible F Λ κ cm cT N ε b μ) :
    ∀ b ∈ S, Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := fun b hb => by
  obtain ⟨μ, h⟩ := hS b hb
  exact muc_spec_of H ha0 h

/-- `ǧ_N` is strictly increasing on the set of `b` with an admissible trajectory. -/
theorem gN_strictMono_adm :
    StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ} :=
  strictMonoOn_of_admissible H HM hC (adm_muc H ha0 fun _ hb => hb)

include he hgβ

/-- `Ufix` is order connected. -/
theorem ordConnected_Ufix : (Ufix F Λ κ cm cT N ε).OrdConnected := by
  refine ⟨fun b₁ hb₁ b₂ hb₂ b hb => ?_⟩
  obtain ⟨μ₁, h₁, -⟩ := hb₁
  obtain ⟨μ₂, h₂, hg₂⟩ := hb₂
  have hmono := gN_strictMono_adm H HM hC ha0
  have hb₁0 : 0 < b₁ := by have := (h₁.1 0 (Nat.zero_le _)).1; rwa [traj_zero] at this
  have hy : (traj F Λ b₂ μ₂ N).1 ≤ ε := hg₂.le
  have h0 : b₁ ∈ SetLe F Λ κ cm cT N ε (traj F Λ b₂ μ₂ N).1 := by
    refine ⟨μ₁, h₁, ?_⟩
    rw [← gN_eq_of_adm H ha0 h₁, ← gN_eq_of_adm H ha0 h₂]
    exact hmono.monotoneOn ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩ (hb.1.trans hb.2)
  have hsub := Icc_subset_SetLe H he hgβ ha0 hb₁0 hy h0 fun x hx μ hadm heq => by
    have := hmono ⟨μ, hadm⟩ ⟨μ₂, h₂⟩ hx.2
    rw [gN_eq_of_adm H ha0 hadm, gN_eq_of_adm H ha0 h₂, heq] at this
    exact lt_irrefl _ this
  obtain ⟨μ, hadm, hle⟩ := hsub hb
  exact ⟨μ, hadm, hle.trans_lt hg₂⟩

/-- **Shooting at fixed `β_R`** (abstract form). Under `HHyp`, `MonoHyp`, `MonoCoef` and
`c_g ε ≤ (1-δ)β`:
* for every `μ₀`-admissible `b` the admissible `μ₀` is unique;
* for every `y ∈ (0, ε]` there is a unique `b` with an admissible trajectory and `ǧ_N(b) = y`,
  and `b ≤ y`;
* `Ufix = {b : admissible trajectory, ǧ_N < ε}` is open and order connected, `μ₀(b)` and `ǧ_N(b)`
  are continuous on it, `ǧ_N` is strictly increasing on all `b` with an admissible trajectory,
  and `ǧ_N` maps `Ufix` onto `(0, ε)`. -/
theorem fh_flow_fixedR (hε : 0 < ε) :
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
  have hmono := gN_strictMono_adm H HM hC ha0
  have hle : ∀ b μ, Admissible F Λ κ cm cT N ε b μ →
      0 < b ∧ b ≤ gN F Λ κ cm cT N ε b := fun b μ h => by
    refine ⟨?_, ?_⟩
    · have := (h.1 0 (Nat.zero_le _)).1; rwa [traj_zero] at this
    · rw [gN_eq_of_adm H ha0 h]; exact b_le_traj_fst H hgβ h N le_rfl
  refine ⟨fun b μ μ' h h' => admissible_unique H ha0 h h', fun y hy0 hy => ?_,
    fun y _ _ b ⟨μ, h⟩ hb => ?_, isOpen_Ufix H he hgβ ha0, ordConnected_Ufix H HM hC he hgβ ha0,
    continuousOn_muc_Ufix H he hgβ ha0, continuousOn_gN_Ufix H he hgβ ha0, hmono, ?_⟩
  · obtain ⟨b, -, μ, hadm, heq⟩ := exists_traj_eq H he hgβ ha0 hε hy0 hy
    refine ⟨b, ⟨⟨μ, hadm⟩, by rw [gN_eq_of_adm H ha0 hadm, heq]⟩, fun b' ⟨hb', hg'⟩ => ?_⟩
    exact unique_of_strictMonoOn hmono hb' ⟨μ, hadm⟩ hg'
      (by rw [gN_eq_of_adm H ha0 hadm, heq])
  · obtain ⟨h1, h2⟩ := hle b μ h
    exact ⟨h1, hb ▸ h2⟩
  · ext y
    constructor
    · rintro ⟨b, ⟨μ, h, hlt⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hle b μ h
      rw [gN_eq_of_adm H ha0 h] at h2 ⊢
      exact ⟨h1.trans_le h2, hlt⟩
    · rintro ⟨hy0, hy⟩
      obtain ⟨b, -, μ, hadm, heq⟩ := exists_traj_eq H he hgβ ha0 hε hy0 hy.le
      exact ⟨b, ⟨μ, hadm, heq ▸ hy⟩, by rw [gN_eq_of_adm H ha0 hadm, heq]⟩

end Fixed

end Hist

end Flow2
