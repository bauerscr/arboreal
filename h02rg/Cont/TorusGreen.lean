import Cont.TorusLog

/-!
# The zero-mode-free Green function of `-Δ` on the torus `𝕋² = UnitAddTorus (Fin 2)` (B1)

`torusGreen x = (4π)⁻¹ ∫₀^∞ (Θ_s(x) - 1) ds = ∫₀^∞ (p_t(x) - 1) dt`, where
`p_t = Θ_{4πt}` is the heat kernel of `e^{tΔ}` on `𝕋²` (periodised Gaussian, see
`b1_cosK_eq_evenK`), i.e. formally `G(x) = ∑_{k ≠ 0} e^{2πik·x}/(4π²|k|²)`.

Main results:
* `torusGreen_integrableOn` : the defining integral converges for `x ≠ 0`;
* `torusGreen_continuousAt`, `torusGreen_continuousOn` : continuity on `𝕋² ∖ {0}`;
* `torusGreen_neg`, `torusGreen_perm`, `torusGreen_reflect` : point-group invariance;
* `torusGreen_log_singularity` : `G(x) = -(2π)⁻¹ log |x| + c + o(1)` as `x → 0`.
-/

open Real Set Filter Topology MeasureTheory HurwitzZeta

noncomputable section

namespace Cont

/-- Coordinate projection `ℝ² → 𝕋²`. -/
def torusProj (y : Fin 2 → ℝ) : UnitAddTorus (Fin 2) := fun i ↦ (y i : UnitAddCircle)

/-- The zero-mode-free Green function of `-Δ` on `𝕋²` (heat-kernel definition). -/
def torusGreen (x : UnitAddTorus (Fin 2)) : ℝ := (4 * π)⁻¹ * ∫ s in Ioi 0, (torusHeat s x - 1)

/-- Euclidean torus distance to `0`. -/
def torusNorm (x : UnitAddTorus (Fin 2)) : ℝ := Real.sqrt (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)

/-- Heat-time form: `G(x) = ∫₀^∞ (p_t(x) - 1) dt` with `p_t = Θ_{4πt}`. -/
lemma torusGreen_eq_heat (x : UnitAddTorus (Fin 2)) :
    torusGreen x = ∫ t in Ioi 0, (torusHeat (4 * π * t) x - 1) := by
  rw [integral_comp_mul_left_Ioi (fun s ↦ torusHeat s x - 1) 0 (by positivity : 0 < 4 * π),
    mul_zero, smul_eq_mul, torusGreen]

lemma b1_torusHeat_continuousOn (x : UnitAddTorus (Fin 2)) :
    ContinuousOn (fun s ↦ torusHeat s x) (Ioi 0) := by
  have : (fun s ↦ torusHeat s x) = fun s ↦ cosKernel (x 0) s * cosKernel (x 1) s :=
    funext fun s ↦ torusHeat_two s x
  rw [this]; exact (continuousOn_cosKernel _).mul (continuousOn_cosKernel _)

lemma b1_torusHeat_proj (s : ℝ) (y : Fin 2 → ℝ) :
    torusHeat s (torusProj y) = cosKernel (y 0 : UnitAddCircle) s * cosKernel (y 1 : UnitAddCircle) s :=
  torusHeat_two _ _

lemma b1_continuous_heat_proj {s : ℝ} (hs : 0 < s) :
    Continuous fun y : Fin 2 → ℝ ↦ torusHeat s (torusProj y) := by
  simp only [b1_torusHeat_proj]
  exact ((b1_continuous_cosK hs).comp (continuous_apply 0)).mul
    ((b1_continuous_cosK hs).comp (continuous_apply 1))

lemma b1_integrableOn_large (x : UnitAddTorus (Fin 2)) :
    IntegrableOn (fun s ↦ torusHeat s x - 1) (Ioi 1) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 pi_pos).const_mul b1C)
    ((((b1_torusHeat_continuousOn x).sub continuousOn_const).mono
      (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs ↦ ?_)
  rw [Real.norm_eq_abs]; exact b1_torusHeat_large x (mem_Ioi.mp hs).le

/-- Large-time part. -/
def b1I2 (y : Fin 2 → ℝ) : ℝ := ∫ s in Ioi 1, (torusHeat s (torusProj y) - 1)

lemma b1I2_continuous : Continuous b1I2 := by
  refine continuous_of_dominated (bound := fun s ↦ b1C * rexp (-π * s))
    (fun y ↦ (b1_integrableOn_large _).aestronglyMeasurable) (fun y ↦ ?_)
    ((exp_neg_integrableOn_Ioi 1 pi_pos).const_mul b1C) ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs ↦ ?_)
    rw [Real.norm_eq_abs]; exact b1_torusHeat_large _ (mem_Ioi.mp hs).le
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs ↦ ?_)
    exact (b1_continuous_heat_proj (lt_trans one_pos (mem_Ioi.mp hs))).sub continuous_const

/-- `|y|²`. -/
def b1r2 (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2

lemma b1r2_continuous : Continuous b1r2 := by unfold b1r2; fun_prop

lemma b1r2_pos {y : Fin 2 → ℝ} (hy : y ≠ 0) : 0 < b1r2 y := by
  by_contra h
  apply hy
  have h0 : y 0 = 0 := by unfold b1r2 at h; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  have h1 : y 1 = 0 := by unfold b1r2 at h; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  funext i; fin_cases i <;> simp [h0, h1]

/-- The singular heat term `s⁻¹ e^{-π|y|²/s}`. -/
def b1sing (s : ℝ) (y : Fin 2 → ℝ) : ℝ := rexp (-π * b1r2 y / s) / s

/-- The box `|yᵢ| ≤ 3/4`. -/
def b1box (y : Fin 2 → ℝ) : Prop := |y 0| ≤ 3 / 4 ∧ |y 1| ≤ 3 / 4

lemma b1_small_proj {y : Fin 2 → ℝ} (hy : b1box y) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ torusHeat s (torusProj y) - b1sing s y ∧ torusHeat s (torusProj y) - b1sing s y ≤ b1M := by
  rw [b1_torusHeat_proj]; exact b1_torusHeat_small hy.1 hy.2 hs hs1

lemma b1sing_nonneg {s : ℝ} (hs : 0 < s) (y : Fin 2 → ℝ) : 0 ≤ b1sing s y :=
  div_nonneg (exp_pos _).le hs.le

lemma b1sing_le {s : ℝ} (hs : 0 < s) {y : Fin 2 → ℝ} {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ b1r2 y) :
    b1sing s y ≤ 1 / (π * δ) := by
  have h1 := b1_exp_div_le (c := π * b1r2 y) (mul_pos pi_pos (lt_of_lt_of_le hδ hr)) hs
  have e : -π * b1r2 y / s = -(π * b1r2 y) / s := by ring
  unfold b1sing; rw [e]
  refine h1.trans ?_
  gcongr

lemma b1sing_continuousOn (y : Fin 2 → ℝ) : ContinuousOn (fun s ↦ b1sing s y) (Ioi 0) := by
  intro s hs
  have hs' : s ≠ 0 := ne_of_gt hs
  exact ((continuousAt_const.div continuousAt_id hs').rexp.div continuousAt_id hs').continuousWithinAt

lemma b1_abs_heat_sub_one_le {y : Fin 2 → ℝ} (hy : b1box y) {δ : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ b1r2 y) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    |torusHeat s (torusProj y) - 1| ≤ 1 / (π * δ) + b1M + 1 := by
  obtain ⟨h1, h2⟩ := b1_small_proj hy hs.1 hs.2
  have h3 := b1sing_le hs.1 hδ hr
  have h4 := b1sing_nonneg hs.1 y
  rw [abs_le]; constructor <;> linarith

lemma b1_integrableOn_small {y : Fin 2 → ℝ} (hy : b1box y) (hr : 0 < b1r2 y) :
    IntegrableOn (fun s ↦ torusHeat s (torusProj y) - 1) (Ioc 0 1) :=
  b1_integrableOn_Ioc_of_bdd ((b1_torusHeat_continuousOn _).sub continuousOn_const) _
    fun _ hs ↦ b1_abs_heat_sub_one_le hy hr le_rfl hs

/-- Small-time part. -/
def b1I1 (y : Fin 2 → ℝ) : ℝ := ∫ s in Ioc 0 1, (torusHeat s (torusProj y) - 1)

lemma b1_green_split {y : Fin 2 → ℝ} (hy : b1box y) (hr : 0 < b1r2 y) :
    torusGreen (torusProj y) = (4 * π)⁻¹ * (b1I1 y + b1I2 y) := by
  unfold torusGreen b1I1 b1I2
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi (b1_integrableOn_small hy hr) (b1_integrableOn_large _)]

lemma b1_eventually_box {y₀ : Fin 2 → ℝ} (h0 : |y₀ 0| < 3 / 4) (h1 : |y₀ 1| < 3 / 4) :
    ∀ᶠ y in 𝓝 y₀, b1box y := by
  have e0 := (((continuous_apply 0).abs).tendsto y₀).eventually_lt_const h0
  have e1 := (((continuous_apply 1).abs).tendsto y₀).eventually_lt_const h1
  filter_upwards [e0, e1] with y a b using ⟨a.le, b.le⟩

lemma b1I1_continuousAt {y₀ : Fin 2 → ℝ} (h0 : |y₀ 0| < 3 / 4) (h1 : |y₀ 1| < 3 / 4)
    (hr : 0 < b1r2 y₀) : ContinuousAt b1I1 y₀ := by
  have hδ : 0 < b1r2 y₀ / 2 := by positivity
  have er := (b1r2_continuous.tendsto y₀).eventually_const_lt
    (by linarith : b1r2 y₀ / 2 < b1r2 y₀)
  refine continuousAt_of_dominated (bound := fun _ ↦ 1 / (π * (b1r2 y₀ / 2)) + b1M + 1)
    (Eventually.of_forall fun y ↦ ((((b1_torusHeat_continuousOn _).sub
      continuousOn_const).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)) ?_
    (integrable_const _) ?_
  · filter_upwards [b1_eventually_box h0 h1, er] with y hy hy'
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs ↦ by
      rw [Real.norm_eq_abs]; exact b1_abs_heat_sub_one_le hy hδ hy'.le hs)
  · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs ↦
      ((b1_continuous_heat_proj hs.1).sub continuous_const).continuousAt)

lemma b1_torusProj_sub_int (y : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    torusProj (fun i ↦ y i - k i) = torusProj y := by
  funext i
  simp only [torusProj]
  exact (QuotientAddGroup.eq).mpr ⟨k i, by simp⟩

lemma b1_torusProj_zero : torusProj 0 = 0 := by
  funext i; simp [torusProj]

/-- Continuity of `y ↦ G(π y)` at every `y` with `π y ≠ 0`. -/
theorem torusGreen_proj_continuousAt {y₀ : Fin 2 → ℝ} (h : torusProj y₀ ≠ 0) :
    ContinuousAt (fun y ↦ torusGreen (torusProj y)) y₀ := by
  set k : Fin 2 → ℤ := fun i ↦ round (y₀ i)
  set z₀ : Fin 2 → ℝ := fun i ↦ y₀ i - k i
  have hz : ∀ i, |z₀ i| ≤ 1 / 2 := fun i ↦ abs_sub_round (y₀ i)
  have hz0 : z₀ ≠ 0 := by
    intro h'; apply h; rw [← b1_torusProj_sub_int y₀ k]
    change torusProj z₀ = 0; rw [h', b1_torusProj_zero]
  have hr := b1r2_pos hz0
  have h0 : |z₀ 0| < 3 / 4 := lt_of_le_of_lt (hz 0) (by norm_num)
  have h1 : |z₀ 1| < 3 / 4 := lt_of_le_of_lt (hz 1) (by norm_num)
  have hc : ContinuousAt (fun y ↦ torusGreen (torusProj y)) z₀ := by
    have er := (b1r2_continuous.tendsto z₀).eventually_const_lt hr
    have hev : (fun y ↦ (4 * π)⁻¹ * (b1I1 y + b1I2 y)) =ᶠ[𝓝 z₀]
        fun y ↦ torusGreen (torusProj y) := by
      filter_upwards [b1_eventually_box h0 h1, er] with y hy hy'
      exact (b1_green_split hy hy').symm
    exact (continuousAt_const.mul ((b1I1_continuousAt h0 h1 hr).add
      b1I2_continuous.continuousAt)).congr hev
  have heq : (fun y ↦ torusGreen (torusProj y)) =
      (fun y ↦ torusGreen (torusProj y)) ∘ (fun (y : Fin 2 → ℝ) (i : Fin 2) ↦ y i - (k i : ℝ)) :=
    funext fun y ↦ by simp only [Function.comp, b1_torusProj_sub_int]
  rw [heq]
  exact ContinuousAt.comp (f := fun (y : Fin 2 → ℝ) (i : Fin 2) ↦ y i - (k i : ℝ)) hc
    (continuous_pi fun i ↦ (continuous_apply i).sub continuous_const).continuousAt

lemma b1_half_ne_zero (b : ℝ) (x : UnitAddCircle) (hb : (b : UnitAddCircle) = x) :
    x ≠ ((b + 1 / 2 : ℝ) : UnitAddCircle) := by
  intro h
  rw [QuotientAddGroup.mk_add, hb] at h
  have : ((1 / 2 : ℝ) : UnitAddCircle) = 0 := by
    have := congrArg (fun z ↦ z - x) h; simpa using this.symm
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp this
  simp only [zsmul_eq_mul, mul_one] at hn
  have : (2 * n : ℝ) = 1 := by rw [hn]; norm_num
  have : 2 * n = 1 := by exact_mod_cast this
  omega

/-- Continuity of the torus Green function on `𝕋² ∖ {0}`. -/
theorem torusGreen_continuousAt {x₀ : UnitAddTorus (Fin 2)} (hx : x₀ ≠ 0) :
    ContinuousAt torusGreen x₀ := by
  set b : Fin 2 → ℝ := fun i ↦ (AddCircle.equivIco 1 0 (x₀ i) : ℝ) + 1 / 2
  have hb : ∀ i, x₀ i ≠ ((b i : ℝ) : UnitAddCircle) := fun i ↦
    b1_half_ne_zero _ _ AddCircle.coe_equivIco
  set σ : UnitAddTorus (Fin 2) → (Fin 2 → ℝ) := fun x i ↦ (AddCircle.equivIco 1 (b i) (x i) : ℝ)
  have hσ : ∀ x, torusProj (σ x) = x := fun x ↦ funext fun i ↦ AddCircle.coe_equivIco
  have hσc : ContinuousAt σ x₀ := continuousAt_pi.2 fun i ↦
    continuous_subtype_val.continuousAt.comp
      (ContinuousAt.comp (f := fun x : UnitAddTorus (Fin 2) ↦ x i)
        (AddCircle.continuousAt_equivIco 1 (b i) (hb i)) (continuous_apply i).continuousAt)
  have heq : torusGreen = (fun y ↦ torusGreen (torusProj y)) ∘ σ := funext fun x ↦ by simp [hσ]
  rw [heq]
  exact ContinuousAt.comp (g := fun y ↦ torusGreen (torusProj y))
    (torusGreen_proj_continuousAt (by rw [hσ]; exact hx)) hσc

theorem torusGreen_continuousOn : ContinuousOn torusGreen {0}ᶜ :=
  fun _ hx ↦ (torusGreen_continuousAt hx).continuousWithinAt

/-! ### Point-group invariance -/

lemma torusHeat_neg (s : ℝ) (x : UnitAddTorus (Fin 2)) : torusHeat s (-x) = torusHeat s x := by
  simp [torusHeat]

lemma torusHeat_perm (s : ℝ) (x : UnitAddTorus (Fin 2)) (σ : Equiv.Perm (Fin 2)) :
    torusHeat s (x ∘ σ) = torusHeat s x :=
  Equiv.prod_comp σ (fun i ↦ cosKernel (x i) s)

lemma torusHeat_reflect (s : ℝ) (x : UnitAddTorus (Fin 2)) (i : Fin 2) :
    torusHeat s (Function.update x i (-x i)) = torusHeat s x := by
  unfold torusHeat
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Function.update_of_ne h]

theorem torusGreen_neg (x : UnitAddTorus (Fin 2)) : torusGreen (-x) = torusGreen x := by
  simp [torusGreen, torusHeat_neg]

theorem torusGreen_perm (x : UnitAddTorus (Fin 2)) (σ : Equiv.Perm (Fin 2)) :
    torusGreen (x ∘ σ) = torusGreen x := by
  simp [torusGreen, torusHeat_perm]

/-- Invariance under the coordinate swap. -/
theorem torusGreen_swap (x : UnitAddTorus (Fin 2)) :
    torusGreen (x ∘ Equiv.swap 0 1) = torusGreen x := torusGreen_perm x _

/-- Invariance under the reflection `xᵢ ↦ -xᵢ`. -/
theorem torusGreen_reflect (x : UnitAddTorus (Fin 2)) (i : Fin 2) :
    torusGreen (Function.update x i (-x i)) = torusGreen x := by
  simp [torusGreen, torusHeat_reflect]

/-- Symmetry of the Green kernel `𝒢(x, y) = G(x - y)`. -/
theorem torusGreen_sub_comm (x y : UnitAddTorus (Fin 2)) :
    torusGreen (x - y) = torusGreen (y - x) := by
  rw [← neg_sub, torusGreen_neg]

/-! ### Representatives and convergence of the defining integral -/

/-- Representative in `[-1/2, 1/2)²`. -/
def torusRep (x : UnitAddTorus (Fin 2)) : Fin 2 → ℝ :=
  fun i ↦ (AddCircle.equivIco 1 (-1 / 2) (x i) : ℝ)

lemma torusProj_torusRep (x : UnitAddTorus (Fin 2)) : torusProj (torusRep x) = x :=
  funext fun _ ↦ AddCircle.coe_equivIco

lemma abs_torusRep_le (x : UnitAddTorus (Fin 2)) (i : Fin 2) : |torusRep x i| ≤ 1 / 2 := by
  have h := (AddCircle.equivIco 1 (-1 / 2) (x i)).2
  show |(AddCircle.equivIco 1 (-1 / 2) (x i) : ℝ)| ≤ 1 / 2
  rw [abs_le]; constructor <;> [linarith [h.1]; linarith [h.2]]

lemma torusRep_ne_zero {x : UnitAddTorus (Fin 2)} (hx : x ≠ 0) : torusRep x ≠ 0 := by
  intro h; apply hx; rw [← torusProj_torusRep x, h, b1_torusProj_zero]

lemma b1_box_of_rep (x : UnitAddTorus (Fin 2)) : b1box (torusRep x) :=
  ⟨(abs_torusRep_le x 0).trans (by norm_num), (abs_torusRep_le x 1).trans (by norm_num)⟩

/-- Convergence of the defining integral `∫₀^∞ (Θ_s(x) - 1) ds` for `x ≠ 0`. -/
theorem torusGreen_integrableOn {x : UnitAddTorus (Fin 2)} (hx : x ≠ 0) :
    IntegrableOn (fun s ↦ torusHeat s x - 1) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ (b1_integrableOn_large x)
  have := b1_integrableOn_small (b1_box_of_rep x) (b1r2_pos (torusRep_ne_zero hx))
  rwa [torusProj_torusRep] at this

/-! ### Logarithmic singularity -/

/-- Regular part of the small-time integral. -/
def b1J (y : Fin 2 → ℝ) : ℝ := ∫ s in Ioc 0 1, (torusHeat s (torusProj y) - 1 - b1sing s y)

lemma b1J_continuousAt_zero : ContinuousAt b1J 0 := by
  have h0 : |(0 : Fin 2 → ℝ) 0| < 3 / 4 := by norm_num
  have h1 : |(0 : Fin 2 → ℝ) 1| < 3 / 4 := by norm_num
  refine continuousAt_of_dominated (bound := fun _ ↦ b1M + 1)
    (Eventually.of_forall fun y ↦ (((((b1_torusHeat_continuousOn _).sub
      continuousOn_const).sub (b1sing_continuousOn y)).mono Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc)) ?_ (integrable_const _) ?_
  · filter_upwards [b1_eventually_box h0 h1] with y hy
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs ↦ ?_)
    obtain ⟨a, b⟩ := b1_small_proj hy hs.1 hs.2
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs ↦ ?_)
    have hc : Continuous fun y : Fin 2 → ℝ ↦ b1sing s y := by
      unfold b1sing; have := b1r2_continuous; fun_prop
    exact (((b1_continuous_heat_proj hs.1).sub continuous_const).sub hc).continuousAt

lemma b1_I1_eq {y : Fin 2 → ℝ} (hy : b1box y) (hr : 0 < b1r2 y) :
    b1I1 y = (∫ s in Ioc (0 : ℝ) 1, rexp (-π * b1r2 y / s) / s) + b1J y := by
  have hs1 : IntegrableOn (fun s ↦ b1sing s y) (Ioc 0 1) :=
    b1_integrableOn_Ioc_of_bdd (b1sing_continuousOn y) (1 / (π * b1r2 y)) fun s hs ↦ by
      rw [abs_of_nonneg (b1sing_nonneg hs.1 y)]; exact b1sing_le hs.1 hr le_rfl
  have hs2 : IntegrableOn (fun s ↦ torusHeat s (torusProj y) - 1 - b1sing s y) (Ioc 0 1) :=
    (b1_integrableOn_small hy hr).sub hs1
  unfold b1I1 b1J
  show _ = (∫ s in Ioc (0 : ℝ) 1, b1sing s y) + _
  rw [← integral_add hs1 hs2]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ ?_
  ring

/-- The constant in the logarithmic singularity. -/
def torusGreenConst : ℝ := (4 * π)⁻¹ * (b1c0 + b1J 0 + b1I2 0)

lemma b1_tendsto_r2 : Tendsto b1r2 (𝓝[≠] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := b1r2_continuous.tendsto (0 : Fin 2 → ℝ)
    simp only [b1r2, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy using b1r2_pos hy

/-- Logarithmic singularity on `ℝ²`: `G(π y) + (4π)⁻¹ log |y|² → c` as `y → 0`. -/
theorem torusGreen_proj_log :
    Tendsto (fun y ↦ torusGreen (torusProj y) + (4 * π)⁻¹ * Real.log (b1r2 y)) (𝓝[≠] 0)
      (𝓝 torusGreenConst) := by
  have hJ := b1J_continuousAt_zero.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hI := (b1I2_continuous.tendsto (0 : Fin 2 → ℝ)).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have h := (((b1_tendsto_sing_add_log.comp b1_tendsto_r2).add hJ).add hI).const_mul (4 * π)⁻¹
  refine Tendsto.congr' ?_ h
  have h0 : |(0 : Fin 2 → ℝ) 0| < 3 / 4 := by norm_num
  have h1 : |(0 : Fin 2 → ℝ) 1| < 3 / 4 := by norm_num
  filter_upwards [nhdsWithin_le_nhds (b1_eventually_box h0 h1), self_mem_nhdsWithin]
    with y hy hy0
  have hr := b1r2_pos hy0
  simp only [Function.comp]
  rw [b1_green_split hy hr, b1_I1_eq hy hr]
  ring

/-- **Logarithmic singularity** of the torus Green function:
`G(x) = -(2π)⁻¹ log |x| + c + o(1)` as `x → 0` in `𝕋²`, `|x|` the torus distance. -/
theorem torusGreen_log_singularity :
    Tendsto (fun x ↦ torusGreen x + (2 * π)⁻¹ * Real.log (torusNorm x)) (𝓝[≠] 0)
      (𝓝 torusGreenConst) := by
  have hb : (0 : UnitAddCircle) ≠ ((-1 / 2 : ℝ) : UnitAddCircle) := by
    have := b1_half_ne_zero (-1) 0 (by
      rw [show ((-1 : ℝ) : UnitAddCircle) = -((1 : ℝ) : UnitAddCircle) by rfl]
      rw [AddCircle.coe_period, neg_zero])
    convert this using 2; norm_num
  have hσc : ContinuousAt torusRep 0 := continuousAt_pi.2 fun i ↦
    continuous_subtype_val.continuousAt.comp
      (ContinuousAt.comp (f := fun x : UnitAddTorus (Fin 2) ↦ x i)
        (AddCircle.continuousAt_equivIco 1 (-1 / 2) hb) (continuous_apply i).continuousAt)
  have hσ0 : torusRep 0 = 0 := by
    funext i
    have : (0 : Fin 2 → ℝ) i ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1) := by norm_num
    have h := AddCircle.equivIco_coe_of_mem (p := 1) this
    simpa [torusRep] using h
  have ht : Tendsto torusRep (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hσc.tendsto; rw [hσ0] at this; exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx using torusRep_ne_zero hx
  refine (torusGreen_proj_log.comp ht).congr fun x ↦ ?_
  simp only [Function.comp, torusProj_torusRep]
  have hn : ∀ i, ‖x i‖ = |torusRep x i| := fun i ↦ by
    conv_lhs => rw [← torusProj_torusRep x]
    exact (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr (by
      rw [abs_one]; exact abs_torusRep_le x i)
  have : torusNorm x = Real.sqrt (b1r2 (torusRep x)) := by
    rw [torusNorm, hn, hn, sq_abs, sq_abs]; rfl
  rw [this, Real.log_sqrt (by unfold b1r2; positivity)]
  ring

end Cont
