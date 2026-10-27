import Flow2.FixedRParamG1
import Flow2.FixedRDiff2

/-!
# Generic fixed-`β_R` flow: differentiability, parameters, consolidated conclusions

Copies of `Flow2/FixedRDiff.lean`, `Flow2/FixedRParam.lean` and `fh_flow_final`,
`fh_flow_final_param` (`Flow2/FixedRDiff2.lean`) with `a ≤ a0h` replaced by the signed cone
`ConeS` and `MonoHyp`/`MonoCoef` by the strict monotonicity of `ǧ_N` (as in
`Flow2/FixedRParamG1.lean`). The conclusions are the same structures `FixedConcl`, `ParamConcl`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]

section Shoot


variable {F : HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ} {A a ε : ℝ}

/-- `bsh` solves the shooting problem for `y ∈ (0, ε]`. -/
lemma bsh_spec_g (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
    (hM : StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ})
    (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y ≤ ε) :
    (∃ μ, Admissible F Λ κ cm cT N ε (bsh F Λ κ cm cT N ε y) μ) ∧
      gN F Λ κ cm cT N ε (bsh F Λ κ cm cT N ε y) = y := by
  have hex := ((fh_flow_fixedR_g H he hgβ hC hM hε).2.1 y hy0 hy).exists
  unfold bsh
  rw [dif_pos hex]
  exact hex.choose_spec

/-- For `y < ε` the shooting solution lies in `Ufix`. -/
lemma bsh_mem_Ufix_g (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
    (hM : StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ})
    (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y < ε) :
    bsh F Λ κ cm cT N ε y ∈ Ufix F Λ κ cm cT N ε := by
  obtain ⟨⟨μ, h⟩, hg⟩ := bsh_spec_g H he hgβ hC hM hε hy0 hy.le
  refine ⟨μ, h, ?_⟩
  rw [← gN_eq_of_adm_g H hC h, hg]; exact hy

end Shoot

section Param

variable {P : Type*} [TopologicalSpace P]
variable {F : P → HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ}

section Local

variable {A a ε : ℝ}

/-- **Parametric local continuation of the admissible `μ₀`.** -/
theorem local_adm_param_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hc : ParamCont F N) {y : ℝ} (hy : y ≤ ε) {p₁ : P} {b₁ μ₁ : ℝ}
    (h₁ : Admissible (F p₁) Λ κ cm cT N ε b₁ μ₁) (hg₁ : (traj (F p₁) Λ b₁ μ₁ N).1 < y)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : P × ℝ in 𝓝 (p₁, b₁), ∃ μ, |μ - μ₁| < η ∧
      Admissible (F q.1) Λ κ cm cT N ε q.2 μ ∧ (traj (F q.1) Λ q.2 μ N).1 < y := by
  obtain ⟨V, hV, r₀, hr₀, hbox⟩ := OKR_box_param hc (OKR_of_adm (H p₁) he hgβ h₁ hg₁)
  have hp₁ : p₁ ∈ V := mem_of_mem_nhds hV
  obtain ⟨η', hη'⟩ : ∃ η', η' = min η r₀ / 2 := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; exact half_pos (lt_min hη hr₀)
  have hη'1 : η' < η := by rw [hη']; linarith [min_le_left η r₀]
  have hη'2 : η' < r₀ := by rw [hη']; linarith [min_le_right η r₀]
  have hb0 : |b₁ - b₁| < r₀ := by rw [sub_self, abs_zero]; exact hr₀
  have hp : OKR (F p₁) Λ cm N y b₁ (μ₁ + η') :=
    hbox p₁ hp₁ _ _ hb0 (by rw [add_sub_cancel_left, abs_of_pos hη'0]; exact hη'2)
  have hm : OKR (F p₁) Λ cm N y b₁ (μ₁ - η') :=
    hbox p₁ hp₁ _ _ hb0 (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη'0]; exact hη'2)
  have h1D := admissible_InDh (H p₁) h₁
  have cp := hC p₁ b₁ _ _ (show μ₁ ≤ μ₁ + η' by linarith)
    (inDh_of_OKR (H p₁) he hy hp) h1D
  have cm' := hC p₁ b₁ _ _ (show μ₁ - η' ≤ μ₁ by linarith) h1D
    (inDh_of_OKR (H p₁) he hy hm)
  rw [h₁.2] at cp cm'
  have hpos : 0 < (traj (F p₁) Λ b₁ (μ₁ + η') N).2.1 := by linarith
  have hneg : (traj (F p₁) Λ b₁ (μ₁ - η') N).2.1 < 0 := by linarith
  have c1 : Continuous fun q : P × ℝ => (traj (F q.1) Λ q.2 (μ₁ + η') N).2.1 :=
    continuous_fst.comp (continuous_snd.comp (continuous_traj_param2 hc le_rfl _))
  have c2 : Continuous fun q : P × ℝ => (traj (F q.1) Λ q.2 (μ₁ - η') N).2.1 :=
    continuous_fst.comp (continuous_snd.comp (continuous_traj_param2 hc le_rfl _))
  have e1 : ∀ᶠ q : P × ℝ in 𝓝 (p₁, b₁), 0 < (traj (F q.1) Λ q.2 (μ₁ + η') N).2.1 :=
    c1.continuousAt.eventually (lt_mem_nhds hpos)
  have e2 : ∀ᶠ q : P × ℝ in 𝓝 (p₁, b₁), (traj (F q.1) Λ q.2 (μ₁ - η') N).2.1 < 0 :=
    c2.continuousAt.eventually (gt_mem_nhds hneg)
  have e3 : ∀ᶠ q : P × ℝ in 𝓝 (p₁, b₁), q.1 ∈ V :=
    (continuous_fst.tendsto ((p₁, b₁) : P × ℝ)).eventually hV
  have e4 : ∀ᶠ q : P × ℝ in 𝓝 (p₁, b₁), |q.2 - b₁| < r₀ := by
    have : ∀ᶠ b in 𝓝 b₁, |b - b₁| < r₀ := by
      filter_upwards [Metric.ball_mem_nhds b₁ hr₀] with b hb
      rwa [Metric.mem_ball, Real.dist_eq] at hb
    exact (continuous_snd.tendsto ((p₁, b₁) : P × ℝ)).eventually this
  filter_upwards [e1, e2, e3, e4] with q h1 h2 h3 h4
  obtain ⟨μ, hmem, hz⟩ := intermediate_value_Icc (by linarith : μ₁ - η' ≤ μ₁ + η')
    (continuous_traj_mu (H q.1) q.2).continuousOn ⟨h2.le, h1.le⟩
  have hμ : |μ - μ₁| ≤ η' := abs_le.2 ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hO := hbox q.1 h3 q.2 μ h4 (hμ.trans_lt hη'2)
  exact ⟨μ, hμ.trans_lt hη'1, adm_of_OKR (H q.1) he hy hO hz, (hO.2 N le_rfl).1⟩

/-- **`UfixP` is open.** -/
theorem isOpen_UfixP_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hc : ParamCont F N) : IsOpen (UfixP F Λ κ cm cT N ε) := by
  refine isOpen_iff_mem_nhds.2 fun q hq => ?_
  obtain ⟨p₁, b₁⟩ := q
  obtain ⟨μ₁, h₁, hg₁⟩ := hq
  filter_upwards [local_adm_param_g H he hgβ hC hc le_rfl h₁ hg₁ one_pos] with q' hq'
  obtain ⟨μ, -, h, hg⟩ := hq'
  exact ⟨μ, h, hg⟩

/-- **Joint continuity of `μ₀`** at every point of `UfixP`. -/
theorem continuousAt_muc_UfixP_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hc : ParamCont F N) {q₁ : P × ℝ} (hq : q₁ ∈ UfixP F Λ κ cm cT N ε) :
    ContinuousAt (fun q : P × ℝ => muc (F q.1) Λ κ cm cT N ε q.2) q₁ := by
  obtain ⟨p₁, b₁⟩ := q₁
  obtain ⟨μ₁, h₁, hg₁⟩ := hq
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro η hη
  filter_upwards [local_adm_param_g H he hgβ hC hc le_rfl h₁ hg₁ hη] with q hq
  obtain ⟨μ, hμ, h, -⟩ := hq
  rw [muc_eq_of_adm_g (H q.1) (hC q.1) h, muc_eq_of_adm_g (H p₁) (hC p₁) h₁, Real.dist_eq]
  exact hμ

/-- **Joint continuity of the admissible trajectory** at every point of `UfixP`. -/
theorem continuousAt_traj_UfixP_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hc : ParamCont F N) {q₁ : P × ℝ} (hq : q₁ ∈ UfixP F Λ κ cm cT N ε) {j : ℕ} (hj : j ≤ N) :
    ContinuousAt (fun q : P × ℝ => traj (F q.1) Λ q.2 (muc (F q.1) Λ κ cm cT N ε q.2) j) q₁ :=
  (continuous_traj_param3 hc hj).continuousAt.comp
    (f := fun q : P × ℝ => (q.1, q.2, muc (F q.1) Λ κ cm cT N ε q.2))
    (continuousAt_fst.prodMk (continuousAt_snd.prodMk
      (continuousAt_muc_UfixP_g H he hgβ hC hc hq)))

theorem continuousOn_muc_UfixP_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hc : ParamCont F N) :
    ContinuousOn (fun q : P × ℝ => muc (F q.1) Λ κ cm cT N ε q.2) (UfixP F Λ κ cm cT N ε) :=
  fun _ hq => (continuousAt_muc_UfixP_g H he hgβ hC hc hq).continuousWithinAt

theorem continuousOn_traj_UfixP_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hc : ParamCont F N) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (fun q : P × ℝ => traj (F q.1) Λ q.2 (muc (F q.1) Λ κ cm cT N ε q.2) j)
      (UfixP F Λ κ cm cT N ε) :=
  fun _ hq => (continuousAt_traj_UfixP_g H he hgβ hC hc hq hj).continuousWithinAt

theorem continuousOn_gN_UfixP_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hc : ParamCont F N) :
    ContinuousOn (fun q : P × ℝ => gN (F q.1) Λ κ cm cT N ε q.2) (UfixP F Λ κ cm cT N ε) :=
  fun _ hq => (continuousAt_traj_UfixP_g H he hgβ hC hc hq le_rfl).fst.continuousWithinAt

/-! ### Continuity of the shooting solution -/

/-- **Joint continuity of the shooting solution** `(p, y) ↦ b(p, y)` on `P × (0, ε)`. -/
theorem continuousOn_bsh_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hM : ∀ p, StrictMonoOn (gN (F p) Λ κ cm cT N ε) {b | ∃ μ, Admissible (F p) Λ κ cm cT N ε b μ})
    (hε : 0 < ε) (hc : ParamCont F N) :
    ContinuousOn (fun x : P × ℝ => bsh (F x.1) Λ κ cm cT N ε x.2) (univ ×ˢ Ioo 0 ε) := by
  rintro ⟨p₁, y₁⟩ ⟨-, hy₁⟩
  have hU := bsh_mem_Ufix_g (H p₁) he hgβ (hC p₁) (hM p₁) hε hy₁.1 hy₁.2
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = bsh (F p₁) Λ κ cm cT N ε y₁ := ⟨_, rfl⟩
  rw [← hb₁] at hU
  have hg₁ : gN (F p₁) Λ κ cm cT N ε b₁ = y₁ := by
    rw [hb₁]; exact (bsh_spec_g (H p₁) he hgβ (hC p₁) (hM p₁) hε hy₁.1 hy₁.2.le).2
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 (isOpen_Ufix_g (H p₁) he hgβ (hC p₁)) b₁ hU
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro η hη
  obtain ⟨d, hd⟩ : ∃ d, d = min η δ₀ / 2 := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact half_pos (lt_min hη hδ₀)
  have hdη : d < η := by rw [hd]; linarith [min_le_left η δ₀]
  have hdδ : d < δ₀ := by rw [hd]; linarith [min_le_right η δ₀]
  have hlo : b₁ - d ∈ Ufix (F p₁) Λ κ cm cT N ε := hball (by
    rw [Metric.mem_ball, Real.dist_eq, show b₁ - d - b₁ = -d by ring, abs_neg, abs_of_pos hd0]
    exact hdδ)
  have hhi : b₁ + d ∈ Ufix (F p₁) Λ κ cm cT N ε := hball (by
    rw [Metric.mem_ball, Real.dist_eq, show b₁ + d - b₁ = d by ring, abs_of_pos hd0]
    exact hdδ)
  have hmono := hM p₁
  have adm : ∀ {p : P} {b : ℝ}, b ∈ Ufix (F p) Λ κ cm cT N ε →
      b ∈ {b | ∃ μ, Admissible (F p) Λ κ cm cT N ε b μ} := fun ⟨μ, h, _⟩ => ⟨μ, h⟩
  have glo : gN (F p₁) Λ κ cm cT N ε (b₁ - d) < y₁ := by
    rw [← hg₁]; exact hmono (adm hlo) (adm hU) (by linarith)
  have ghi : y₁ < gN (F p₁) Λ κ cm cT N ε (b₁ + d) := by
    rw [← hg₁]; exact hmono (adm hU) (adm hhi) (by linarith)
  obtain ⟨c, hc'⟩ : ∃ c, c = min (y₁ - gN (F p₁) Λ κ cm cT N ε (b₁ - d))
      (gN (F p₁) Λ κ cm cT N ε (b₁ + d) - y₁) / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc']; exact half_pos (lt_min (by linarith) (by linarith))
  have hc1 : c < y₁ - gN (F p₁) Λ κ cm cT N ε (b₁ - d) := by
    rw [hc']; linarith [min_le_left (y₁ - gN (F p₁) Λ κ cm cT N ε (b₁ - d))
      (gN (F p₁) Λ κ cm cT N ε (b₁ + d) - y₁)]
  have hc2 : c < gN (F p₁) Λ κ cm cT N ε (b₁ + d) - y₁ := by
    rw [hc']; linarith [min_le_right (y₁ - gN (F p₁) Λ κ cm cT N ε (b₁ - d))
      (gN (F p₁) Λ κ cm cT N ε (b₁ + d) - y₁)]
  -- continuity in `p` at the two ends
  have hend : ∀ b ∈ Ufix (F p₁) Λ κ cm cT N ε,
      ContinuousAt (fun p : P => gN (F p) Λ κ cm cT N ε b) p₁ ∧
        ∀ᶠ p in 𝓝 p₁, b ∈ Ufix (F p) Λ κ cm cT N ε := fun b hb => by
    have hq : (p₁, b) ∈ UfixP F Λ κ cm cT N ε := hb
    have h1 := (continuousAt_traj_UfixP_g H he hgβ hC hc hq le_rfl).fst
    have h2 : ∀ᶠ x : P × ℝ in 𝓝 (p₁, b), x ∈ UfixP F Λ κ cm cT N ε :=
      (isOpen_UfixP_g H he hgβ hC hc).mem_nhds hq
    have hγ : Continuous fun p : P => ((p, b) : P × ℝ) := continuous_id.prodMk continuous_const
    exact ⟨h1.comp (f := fun p : P => ((p, b) : P × ℝ)) hγ.continuousAt,
      hγ.continuousAt.eventually h2⟩
  obtain ⟨clo, ulo⟩ := hend _ hlo
  obtain ⟨chi, uhi⟩ := hend _ hhi
  have e1 : ∀ᶠ p in 𝓝 p₁, gN (F p) Λ κ cm cT N ε (b₁ - d) < y₁ - c :=
    clo.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ p in 𝓝 p₁, y₁ + c < gN (F p) Λ κ cm cT N ε (b₁ + d) :=
    chi.eventually (lt_mem_nhds (by linarith))
  have e3 : ∀ᶠ x : P × ℝ in 𝓝 (p₁, y₁), |x.2 - y₁| < c := by
    have : ∀ᶠ y in 𝓝 y₁, |y - y₁| < c := by
      filter_upwards [Metric.ball_mem_nhds y₁ hc0] with y hy
      rwa [Metric.mem_ball, Real.dist_eq] at hy
    exact (continuous_snd.tendsto ((p₁, y₁) : P × ℝ)).eventually this
  have e4 := (continuous_fst.tendsto ((p₁, y₁) : P × ℝ)).eventually
    (e1.and (e2.and (ulo.and uhi)))
  filter_upwards [eventually_mem_nhdsWithin, (e3.and e4).filter_mono nhdsWithin_le_nhds]
    with x hx ⟨h3, h1, h2, hlo', hhi'⟩
  obtain ⟨-, hy⟩ := hx
  have hspec := bsh_spec_g (H x.1) he hgβ (hC x.1) (hM x.1) hε hy.1 hy.2.le
  have hmono' := hM x.1
  obtain ⟨y1, y2⟩ := abs_lt.1 h3
  have hl : b₁ - d < bsh (F x.1) Λ κ cm cT N ε x.2 := by
    by_contra hcon
    push Not at hcon
    have := hmono'.monotoneOn hspec.1 (adm hlo') hcon
    rw [hspec.2] at this
    linarith
  have hr : bsh (F x.1) Λ κ cm cT N ε x.2 < b₁ + d := by
    by_contra hcon
    push Not at hcon
    have := hmono'.monotoneOn (adm hhi') hspec.1 hcon
    rw [hspec.2] at this
    linarith
  rw [Real.dist_eq, ← hb₁, abs_lt]
  constructor <;> linarith

end Local

end Param

section Diff

variable [∀ j, NormedSpace ℝ (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ} {A a ε : ℝ}

/-- **`μ₀(b)` is differentiable** at every `b ∈ Ufix`. -/
theorem differentiableAt_muc_fixed_g (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ : ℝ} (hb : b₀ ∈ Ufix F Λ κ cm cT N ε) :
    DifferentiableAt ℝ (muc F Λ κ cm cT N ε) b₀ := by
  obtain ⟨μ₁, h₁, hg₁⟩ := hb
  have hadm := muc_spec_of_g H hC h₁
  have hg : (traj F Λ b₀ (muc F Λ κ cm cT N ε b₀) N).1 < ε := by
    rw [muc_eq_of_adm_g H hC h₁]; exact hg₁
  have hnhds : Ufix F Λ κ cm cT N ε ∈ 𝓝 b₀ :=
    (isOpen_Ufix_g H he hgβ hC).mem_nhds ⟨μ₁, h₁, hg₁⟩
  refine differentiableAt_implicit (φ := fun p : ℝ × ℝ => (traj F Λ p.1 p.2 N).2.1) one_pos
    (traj_diffAt_fixed H hgβ HD hadm hg N le_rfl).snd.fst
    (continuousAt_muc_fixed_g H he hgβ hC h₁ hg₁) ?_ ?_
  · filter_upwards [hnhds] with b hb
    obtain ⟨μ, h, -⟩ := hb
    exact (muc_spec_of_g H hC h).2
  · filter_upwards [eventually_traj_InD3_fixed H he hgβ hadm hg] with μ hμ
    have h1 := expand_of_coneS H hC hμ hadm.1
    rw [hadm.2, sub_zero] at h1
    simpa only [one_mul] using h1

/-- **All coordinates along the admissible flow are differentiable** on `Ufix`. -/
theorem differentiableAt_traj_muc_fixed_g (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) {b₀ : ℝ} (hb : b₀ ∈ Ufix F Λ κ cm cT N ε) {j : ℕ}
    (hj : j ≤ N) :
    DifferentiableAt ℝ (fun b => traj F Λ b (muc F Λ κ cm cT N ε b) j) b₀ := by
  obtain ⟨μ₁, h₁, hg₁⟩ := hb
  have hadm := muc_spec_of_g H hC h₁
  have hg : (traj F Λ b₀ (muc F Λ κ cm cT N ε b₀) N).1 < ε := by
    rw [muc_eq_of_adm_g H hC h₁]; exact hg₁
  have h1 := traj_diffAt_fixed H hgβ HD hadm hg j hj
  have h2 : DifferentiableAt ℝ (fun b => ((b, muc F Λ κ cm cT N ε b) : ℝ × ℝ)) b₀ :=
    differentiableAt_id.prodMk (differentiableAt_muc_fixed_g H he hgβ hC HD ⟨μ₁, h₁, hg₁⟩)
  exact h1.comp b₀ h2

/-- **`thm:flow`(iii), differentiability on `Ufix`**: `μ₀`, `ǧ_N` and every coordinate
`s_j(b, μ₀(b))`, `j ≤ N`, are differentiable on `Ufix`. -/
theorem fh_flow_fixedR_diff_g (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (hC : ConeS F Λ β δ κ cg cm cT N ε)
    (HD : HDiff F Λ β δ κ cg cm cT N ε) :
    DifferentiableOn ℝ (muc F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) ∧
    DifferentiableOn ℝ (gN F Λ κ cm cT N ε) (Ufix F Λ κ cm cT N ε) ∧
    ∀ j ≤ N, DifferentiableOn ℝ (fun b => traj F Λ b (muc F Λ κ cm cT N ε b) j)
      (Ufix F Λ κ cm cT N ε) :=
  ⟨fun _ hb => (differentiableAt_muc_fixed_g H he hgβ hC HD hb).differentiableWithinAt,
    fun _ hb => (differentiableAt_traj_muc_fixed_g H he hgβ hC HD hb le_rfl).fst.differentiableWithinAt,
    fun _ hj _ hb => (differentiableAt_traj_muc_fixed_g H he hgβ hC HD hb hj).differentiableWithinAt⟩

end Diff

section Final

variable [∀ j, NormedSpace ℝ (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ} {A a ε E : ℝ} {e : ℕ → ℝ}

/-- **The consolidated abstract flow theorem at fixed `β_R`**, generic form. -/
theorem fh_flow_final_g (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (hC : ConeS F Λ β δ κ cg cm cT N ε)
    (hM : StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ})
    (HD : HDiff F Λ β δ κ cg cm cT N ε) (S : SharpHyp F Λ β δ κ cg cm cT N ε cg E e)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β)
    (hgβ' : cg * ε ≤ (1 - δ) * β / 2) (hε : 0 < ε) :
    FixedConcl F Λ β κ cg cm cT N ε E := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := fh_flow_fixedR_g H he hgβ hC hM hε
  obtain ⟨d1, d2, d3⟩ := fh_flow_fixedR_diff_g H he hgβ hC HD
  refine ⟨r1, r2, fun y hy0 hy => ?_, fun y hy0 hy => bsh_mem_Ufix_g H he hgβ hC hM hε hy0 hy,
    r4, r5, r8, r9, r6, r7, d1, d2, d3, fun b μ h j hj => ?_, fun b hb j hj => ?_,
    fun b μ h n hn => ginv_log H he hgβ' S h hn⟩
  · obtain ⟨h1, h2⟩ := bsh_spec_g H he hgβ hC hM hε hy0 hy
    exact ⟨h1, h2, r3 y hy0 hy _ h1 h2⟩
  · exact ⟨h.1 j hj, b_le_traj_fst H hgβ h j hj, traj_le_N H hgβ h j hj⟩
  · obtain ⟨μ₁, h₁, hg₁⟩ := hb
    have hadm := muc_spec_of_g H hC h₁
    have hg : (traj F Λ b (muc F Λ κ cm cT N ε b) N).1 < ε := by
      rw [muc_eq_of_adm_g H hC h₁]; exact hg₁
    exact ⟨traj_g_lt_fixed H hgβ hadm hg j hj, adm_strict H he hadm j hj⟩

end Final

section ParamFinal

variable {P : Type*} [TopologicalSpace P]
variable {F : P → HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ} {A a ε : ℝ}

/-- **The parametric flow theorem at fixed `β_R`**, generic form. -/
theorem fh_flow_final_param_g (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (hC : ∀ p, ConeS (F p) Λ β δ κ cg cm cT N ε)
    (hM : ∀ p, StrictMonoOn (gN (F p) Λ κ cm cT N ε) {b | ∃ μ, Admissible (F p) Λ κ cm cT N ε b μ})
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β)
    (hε : 0 < ε) (hc : ParamCont F N) : ParamConcl F Λ κ cm cT N ε :=
  ⟨isOpen_UfixP_g H he hgβ hC hc, continuousOn_muc_UfixP_g H he hgβ hC hc,
    continuousOn_gN_UfixP_g H he hgβ hC hc, fun _ hj => continuousOn_traj_UfixP_g H he hgβ hC hc hj,
    continuousOn_bsh_g H he hgβ hC hM hε hc⟩

end ParamFinal

end Hist

end Flow2
