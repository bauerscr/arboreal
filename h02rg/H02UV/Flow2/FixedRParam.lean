import Flow2.FixedR3
import Flow2.Param

/-!
# Shooting at fixed `β_R` with a parameter (continuity in `m²` on `Ufix`)

A family `F : P → HData X` (in the application `P` is a set of masses `m²`) such that every
`F p` satisfies `HHyp` with the same constants and `(p, t) ↦ G_j, m_j, T_j` are jointly
continuous (`ParamCont`).

* `continuous_traj_param3`: the unclamped flow is jointly continuous in `(p, b, μ₀)`;
* `local_adm_param`: **parametric `local_adm`**: if `μ₁` is admissible for `(p₁, b₁)` with
  `ǧ_N < y ≤ ε`, then every `(p, b)` near `(p₁, b₁)` has an admissible `μ` near `μ₁` with
  `ǧ_N < y`;
* `UfixP = {(p, b) : b ∈ Ufix(F p)}` is open (`isOpen_UfixP`), and `μ₀`, `ǧ_N` and all
  coordinates of the admissible trajectory are jointly continuous on it
  (`continuousOn_muc_UfixP`, `continuousOn_traj_UfixP`, `continuousOn_gN_UfixP`);
* `bsh F … y`: the shooting solution, the `b` with an admissible trajectory and `ǧ_N(b) = y`;
  with `MonoHyp`/`MonoCoef` for every `p` (strict monotonicity of `ǧ_N`), `(p, y) ↦ bsh (F p) y`
  is jointly continuous on `P × (0, ε)` (`continuousOn_bsh`): strict monotonicity plus joint
  continuity of `ǧ_N`, the standard argument for monotone continuous families.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]

/-! ### The shooting solution -/

open Classical in
variable (F : HData X) (Λ κ cm cT : ℝ) in
/-- The shooting solution: the `b` with an admissible trajectory and `ǧ_N(b) = y` (`0` if there
is none). -/
def bsh (N : ℕ) (ε y : ℝ) : ℝ :=
  if h : ∃ b, (∃ μ, Admissible F Λ κ cm cT N ε b μ) ∧ gN F Λ κ cm cT N ε b = y then h.choose
  else 0

section Shoot

variable {F : HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ} {A a ε w p q r p₂ q₂ r₂ : ℝ}

/-- `bsh` solves the shooting problem for `y ∈ (0, ε]`. -/
lemma bsh_spec (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w) (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y ≤ ε) :
    (∃ μ, Admissible F Λ κ cm cT N ε (bsh F Λ κ cm cT N ε y) μ) ∧
      gN F Λ κ cm cT N ε (bsh F Λ κ cm cT N ε y) = y := by
  have hex := ((fh_flow_fixedR H HM hC he hgβ ha0 hε).2.1 y hy0 hy).exists
  unfold bsh
  rw [dif_pos hex]
  exact hex.choose_spec

/-- For `y < ε` the shooting solution lies in `Ufix`. -/
lemma bsh_mem_Ufix (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w) (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hε : 0 < ε) {y : ℝ} (hy0 : 0 < y) (hy : y < ε) :
    bsh F Λ κ cm cT N ε y ∈ Ufix F Λ κ cm cT N ε := by
  obtain ⟨⟨μ, h⟩, hg⟩ := bsh_spec H HM hC he hgβ ha0 hε hy0 hy.le
  refine ⟨μ, h, ?_⟩
  rw [← gN_eq_of_adm H ha0 h, hg]; exact hy

end Shoot

/-! ### The parametric flow -/

variable {P : Type*} [TopologicalSpace P]
variable {F : P → HData X} {Λ β δ κ cg cm cT : ℝ} {N : ℕ}

/-- The unclamped flow is jointly continuous in `(p, b, μ₀)`. -/
lemma continuous_traj_param3 (hc : ParamCont F N) {j : ℕ} (hj : j ≤ N) :
    Continuous (fun q : P × ℝ × ℝ => traj (F q.1) Λ q.2.1 q.2.2 j) := by
  refine continuous_tr_param
    (s0 := fun q : P × ℝ × ℝ => fun _ => (q.2.1, q.2.2, 0))
    (st := fun q => stepS (F q.1) Λ) ?_ (fun k hk => ?_) hj
  · exact continuous_pi fun _ => (continuous_fst.comp continuous_snd).prodMk
      ((continuous_snd.comp continuous_snd).prodMk continuous_const)
  · have hG : Continuous fun q : (P × ℝ × ℝ) × Seq X => (F q.1.1).G k q.2 :=
      (hc.G k hk).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hm : Continuous fun q : (P × ℝ × ℝ) × Seq X => (F q.1.1).m k q.2 :=
      (hc.m k hk).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hT : Continuous fun q : (P × ℝ × ℝ) × Seq X => (F q.1.1).T k q.2 :=
      (hc.T k hk).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact hG.prodMk (((continuous_const.mul (continuous_fst.comp (continuous_snd.comp
      ((continuous_apply k).comp continuous_snd)))).add hm).prodMk hT)

/-- The flow at fixed `μ₀` is jointly continuous in `(p, b)`. -/
lemma continuous_traj_param2 (hc : ParamCont F N) {j : ℕ} (hj : j ≤ N) (μ : ℝ) :
    Continuous (fun q : P × ℝ => traj (F q.1) Λ q.2 μ j) :=
  (continuous_traj_param3 hc hj).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

variable (F Λ κ cm cT) in
/-- The parameters and initial couplings with an admissible trajectory and `ǧ_N < ε`. -/
def UfixP (N : ℕ) (ε : ℝ) : Set (P × ℝ) := {q | q.2 ∈ Ufix (F q.1) Λ κ cm cT N ε}

section Local

variable {A a ε : ℝ}

/-- `OKR` on a product neighbourhood `V × (b₁ - r, b₁ + r) × (μ₁ - r, μ₁ + r)`. -/
lemma OKR_box_param (hc : ParamCont F N) {y : ℝ} {p₁ : P} {b₁ μ₁ : ℝ}
    (hO : OKR (F p₁) Λ cm N y b₁ μ₁) :
    ∃ V : Set P, V ∈ 𝓝 p₁ ∧ ∃ r > 0, ∀ p ∈ V, ∀ b μ, |b - b₁| < r → |μ - μ₁| < r →
      OKR (F p) Λ cm N y b μ := by
  have hev : ∀ᶠ q : P × ℝ × ℝ in 𝓝 (p₁, b₁, μ₁), OKR (F q.1) Λ cm N y q.2.1 q.2.2 := by
    refine (continuousAt_const.eventually_lt
      (continuous_fst.comp continuous_snd).continuousAt hO.1).and ?_
    refine (eventually_all_finite (finite_le_nat N)).2 fun j hj => ?_
    have hc3 := continuous_traj_param3 (Λ := Λ) hc (show j ≤ N from hj)
    have hg : Continuous fun q : P × ℝ × ℝ => (traj (F q.1) Λ q.2.1 q.2.2 j).1 :=
      continuous_fst.comp hc3
    have hμ : Continuous fun q : P × ℝ × ℝ => |(traj (F q.1) Λ q.2.1 q.2.2 j).2.1| :=
      (continuous_fst.comp (continuous_snd.comp hc3)).abs
    exact (hg.continuousAt.eventually_lt continuousAt_const (hO.2 j hj).1).and
      (hμ.continuousAt.eventually_lt (continuousAt_const.mul hg.continuousAt) (hO.2 j hj).2)
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := hev
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hpb
  refine ⟨{p | pa p}, hpa, r, hr, fun p hp b μ hb hμ => ?_⟩
  refine hall (x := p) hp (y := (b, μ)) (hball ?_)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt hb hμ

/-- **Parametric local continuation of the admissible `μ₀`.** -/
theorem local_adm_param (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
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
  have cp := cone_signed (H p₁) ha0 (show μ₁ ≤ μ₁ + η' by linarith)
    (inDh_of_OKR (H p₁) he hy hp) h1D
  have cm' := cone_signed (H p₁) ha0 (show μ₁ - η' ≤ μ₁ by linarith) h1D
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
theorem isOpen_UfixP (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hc : ParamCont F N) : IsOpen (UfixP F Λ κ cm cT N ε) := by
  refine isOpen_iff_mem_nhds.2 fun q hq => ?_
  obtain ⟨p₁, b₁⟩ := q
  obtain ⟨μ₁, h₁, hg₁⟩ := hq
  filter_upwards [local_adm_param H he hgβ ha0 hc le_rfl h₁ hg₁ one_pos] with q' hq'
  obtain ⟨μ, -, h, hg⟩ := hq'
  exact ⟨μ, h, hg⟩

/-- **Joint continuity of `μ₀`** at every point of `UfixP`. -/
theorem continuousAt_muc_UfixP (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hc : ParamCont F N) {q₁ : P × ℝ} (hq : q₁ ∈ UfixP F Λ κ cm cT N ε) :
    ContinuousAt (fun q : P × ℝ => muc (F q.1) Λ κ cm cT N ε q.2) q₁ := by
  obtain ⟨p₁, b₁⟩ := q₁
  obtain ⟨μ₁, h₁, hg₁⟩ := hq
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro η hη
  filter_upwards [local_adm_param H he hgβ ha0 hc le_rfl h₁ hg₁ hη] with q hq
  obtain ⟨μ, hμ, h, -⟩ := hq
  rw [muc_eq_of_adm (H q.1) ha0 h, muc_eq_of_adm (H p₁) ha0 h₁, Real.dist_eq]
  exact hμ

/-- **Joint continuity of the admissible trajectory** at every point of `UfixP`. -/
theorem continuousAt_traj_UfixP (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hc : ParamCont F N) {q₁ : P × ℝ} (hq : q₁ ∈ UfixP F Λ κ cm cT N ε) {j : ℕ} (hj : j ≤ N) :
    ContinuousAt (fun q : P × ℝ => traj (F q.1) Λ q.2 (muc (F q.1) Λ κ cm cT N ε q.2) j) q₁ :=
  (continuous_traj_param3 hc hj).continuousAt.comp
    (f := fun q : P × ℝ => (q.1, q.2, muc (F q.1) Λ κ cm cT N ε q.2))
    (continuousAt_fst.prodMk (continuousAt_snd.prodMk
      (continuousAt_muc_UfixP H he hgβ ha0 hc hq)))

theorem continuousOn_muc_UfixP (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hc : ParamCont F N) :
    ContinuousOn (fun q : P × ℝ => muc (F q.1) Λ κ cm cT N ε q.2) (UfixP F Λ κ cm cT N ε) :=
  fun _ hq => (continuousAt_muc_UfixP H he hgβ ha0 hc hq).continuousWithinAt

theorem continuousOn_traj_UfixP (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hc : ParamCont F N) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (fun q : P × ℝ => traj (F q.1) Λ q.2 (muc (F q.1) Λ κ cm cT N ε q.2) j)
      (UfixP F Λ κ cm cT N ε) :=
  fun _ hq => (continuousAt_traj_UfixP H he hgβ ha0 hc hq hj).continuousWithinAt

theorem continuousOn_gN_UfixP (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hc : ParamCont F N) :
    ContinuousOn (fun q : P × ℝ => gN (F q.1) Λ κ cm cT N ε q.2) (UfixP F Λ κ cm cT N ε) :=
  fun _ hq => (continuousAt_traj_UfixP H he hgβ ha0 hc hq le_rfl).fst.continuousWithinAt

/-! ### Continuity of the shooting solution -/

variable {w p q r p₂ q₂ r₂ : ℝ}

/-- **Joint continuity of the shooting solution** `(p, y) ↦ b(p, y)` on `P × (0, ε)`. -/
theorem continuousOn_bsh (H : ∀ p, HHyp (F p) Λ β δ κ cg cm cT N A a ε)
    (HM : ∀ p, MonoHyp (F p) Λ β δ κ cg cm cT N A a ε w)
    (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂)
    (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β) (ha0 : a ≤ a0h Λ κ A)
    (hε : 0 < ε) (hc : ParamCont F N) :
    ContinuousOn (fun x : P × ℝ => bsh (F x.1) Λ κ cm cT N ε x.2) (univ ×ˢ Ioo 0 ε) := by
  rintro ⟨p₁, y₁⟩ ⟨-, hy₁⟩
  have hU := bsh_mem_Ufix (H p₁) (HM p₁) hC he hgβ ha0 hε hy₁.1 hy₁.2
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = bsh (F p₁) Λ κ cm cT N ε y₁ := ⟨_, rfl⟩
  rw [← hb₁] at hU
  have hg₁ : gN (F p₁) Λ κ cm cT N ε b₁ = y₁ := by
    rw [hb₁]; exact (bsh_spec (H p₁) (HM p₁) hC he hgβ ha0 hε hy₁.1 hy₁.2.le).2
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 (isOpen_Ufix (H p₁) he hgβ ha0) b₁ hU
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
  have hmono := gN_strictMono_adm (H p₁) (HM p₁) hC ha0
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
    have h1 := (continuousAt_traj_UfixP H he hgβ ha0 hc hq le_rfl).fst
    have h2 : ∀ᶠ x : P × ℝ in 𝓝 (p₁, b), x ∈ UfixP F Λ κ cm cT N ε :=
      (isOpen_UfixP H he hgβ ha0 hc).mem_nhds hq
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
  have hspec := bsh_spec (H x.1) (HM x.1) hC he hgβ ha0 hε hy.1 hy.2.le
  have hmono' := gN_strictMono_adm (H x.1) (HM x.1) hC ha0
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

end Hist

end Flow2
