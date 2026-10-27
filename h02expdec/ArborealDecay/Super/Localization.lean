module

public import ArborealDecay.Super.IntQ

/-!
# The localization theorem (BCHS Theorem 2.8, BHS Appendix B)

For `F : ℝ^{2N} → SG N P` with all Grassmann coordinates `C¹` and, together with their first
partial derivatives, rapidly decreasing (`SDecay F`), and `Q F = 0`,
`∫_{ℝ^{2N|2N}} F = F_0(0)` (`superIntegral_eq_pi0`), where `F_0 = pi0 ∘ F` is the part of `F`
of degree zero in the integrated generators `ξ, η` (parameters `P` are kept).

Proof (BHS App. B).  Let `J(γ) = ∫ ℓ(∫dξdη F e^{-γ S})` with `S = Q λ = sfun - ω`.
1. For `γ > 0`, `J' (γ) = -∫ ℓ (∫dξdη Q(λ F e^{-γ S})) = 0` (`hasDerivAt_J`), by
   differentiation under the integral sign and `integral_berezin_Q`.
2. `J(γ) → J(0) = ∫ ℓ (∫dξdη F)` as `γ ↓ 0` (dominated convergence).
3. `J(γ) → (2π)^N ℓ (F_0(0))` as `γ → ∞` (`tendsto_J_atTop`): after the substitution
   `p = γ^{-1/2} q`, `J(γ) = ∫ e^{-sfun q} ℓ (∏_i (γ⁻¹ ∂_{η_i}∂_{ξ_i} + π_i) F(γ^{-1/2} q)) dq`
   and dominated convergence applies.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory Filter Topology CliffordAlgebra Grassmann

set_option linter.unusedSectionVars false

variable {N P : Type*} [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P]

/-! ### The derivative of `W γ = e^{γ ω}` in `γ` -/

theorem hasDerivAt_dual_WL (l : List N) (ℓ : Module.Dual ℝ (SG N P)) (γ : ℝ) :
    HasDerivAt (fun γ => ℓ (WL γ l)) (ℓ (ωL l * WL γ l)) γ := by
  induction l generalizing ℓ with
  | nil => simpa [WL, ωL] using hasDerivAt_const γ (ℓ 1)
  | cons i l ih =>
    have e : (fun γ => ℓ (WL γ (i :: l) : SG N P)) =
        fun γ => ℓ (WL γ l) + γ * (ℓ ∘ₗ LinearMap.mulLeft ℝ (aa i)) (WL γ l) := by
      funext γ
      rw [WL_cons, wpair, add_mul, one_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul]
      rfl
    rw [e]
    have h : HasDerivAt (fun γ => ℓ (WL γ l) + γ * (ℓ ∘ₗ LinearMap.mulLeft ℝ (aa i)) (WL γ l))
        (ℓ (ωL l * WL γ l) + (1 * (ℓ ∘ₗ LinearMap.mulLeft ℝ (aa i)) (WL γ l) +
          γ * (ℓ ∘ₗ LinearMap.mulLeft ℝ (aa i)) (ωL l * WL γ l))) γ :=
      (ih ℓ).add ((hasDerivAt_id γ).mul (ih (ℓ ∘ₗ LinearMap.mulLeft ℝ (aa i))))
    convert h using 1
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, one_mul]
    have : (aa i + ωL l) * (wpair γ i * WL γ l) =
        ωL l * WL γ l + (aa i * WL γ l + γ • (aa i * (ωL l * WL γ l)) : SG N P) := by
      rw [wpair]
      simp only [add_mul, mul_add, one_mul, smul_mul_assoc, mul_smul_comm, ← mul_assoc,
        aa_mul_aa, zero_mul]
      rw [← aa_comm i (ωL l)]
      abel_nf
    rw [ωL_cons, WL_cons, this, map_add, map_add, map_smul, smul_eq_mul]

theorem hasDerivAt_dual_W (ℓ : Module.Dual ℝ (SG N P)) (γ : ℝ) :
    HasDerivAt (fun γ => ℓ (W γ)) (ℓ (ω * W γ)) γ :=
  hasDerivAt_dual_WL _ ℓ γ

theorem continuous_dual_W (ℓ : Module.Dual ℝ (SG N P)) : Continuous fun γ => ℓ (W γ) :=
  continuous_iff_continuousAt.2 fun γ => (hasDerivAt_dual_W ℓ γ).continuousAt

theorem continuous_anorm_W : Continuous fun γ => anorm (W γ : SG N P) :=
  continuous_anorm_comp fun m => continuous_dual_W (crd m)

theorem continuous_anorm_ωW : Continuous fun γ => anorm (ω * W γ : SG N P) :=
  continuous_anorm_comp fun m => continuous_dual_W (crd m ∘ₗ LinearMap.mulLeft ℝ ω)

/-! ### Continuity of `TL t 1` in `t` -/

theorem continuous_dual_TL (l : List N) (ℓ : Module.Dual ℝ (SG N P)) (x : SG N P) :
    Continuous fun t => ℓ (TL t 1 l x) := by
  induction l generalizing ℓ with
  | nil => exact continuous_const (y := ℓ x)
  | cons i l ih =>
    have e : (fun t => ℓ (TL t 1 (i :: l) x)) = fun t =>
        t * (ℓ ∘ₗ bpair i) (TL t 1 l x) + (ℓ ∘ₗ (piPair i).toLinearMap) (TL t 1 l x) := by
      funext t; rw [TL_cons]; simp
    rw [e]
    exact ((by fun_prop : Continuous fun t : ℝ => t).mul (ih (ℓ ∘ₗ bpair i))).add
      (ih (ℓ ∘ₗ (piPair i).toLinearMap))

/-! ### The Gaussian integral -/

theorem gauss_one_eq_prod (q : Pt N) :
    gauss 1 q = ∏ k, Real.exp (-(1 / 2 : ℝ) * q k ^ 2) := by
  rw [gauss, sfun, ← Real.exp_sum, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem integrable_gauss_one : Integrable (gauss 1 : Pt N → ℝ) := by
  rw [show (gauss 1 : Pt N → ℝ) = fun q => ∏ k, Real.exp (-(1 / 2 : ℝ) * q k ^ 2) from
    funext gauss_one_eq_prod]
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun _ x => Real.exp (-(1 / 2 : ℝ) * x ^ 2))
    fun _ => integrable_exp_neg_mul_sq (by norm_num)

theorem integral_gauss_one : ∫ q : Pt N, gauss 1 q = (2 * Real.pi) ^ Fintype.card N := by
  simp_rw [gauss_one_eq_prod]
  rw [volume_pi, integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (f := fun _ x => Real.exp (-(1 / 2 : ℝ) * x ^ 2))]
  simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_sum]
  rw [← two_mul, pow_mul, show Real.pi / (1 / 2) = 2 * Real.pi by ring,
    Real.sq_sqrt (by positivity)]

/-! ### The regularised integrand -/

variable (F : Pt N → SG N P) (ℓ : Module.Dual ℝ (SG N P))

/-- `ℓ (∫dξdη F e^{-γS})` at the point `p`. -/
def jint (γ : ℝ) (p : Pt N) : ℝ := gauss γ p * ℓ (berezin (F p * W γ))

/-- The `γ`-derivative of `jint`. -/
def jder (γ : ℝ) (p : Pt N) : ℝ :=
  gauss γ p * (-sfun p * ℓ (berezin (F p * W γ)) + ℓ (berezin (F p * (ω * W γ))))

/-- The regularised integral `J(γ) = ∫ ℓ (∫dξdη F e^{-γS})`. -/
def J (γ : ℝ) : ℝ := ∫ p, jint F ℓ γ p

variable {F ℓ}

theorem jint_eq (γ : ℝ) (p : Pt N) : jint F ℓ γ p = ℓ (berezin (F p * Egam γ p)) := by
  rw [jint, Egam, mul_smul_comm, map_smul, map_smul, smul_eq_mul]

theorem jint_zero (p : Pt N) : jint F ℓ 0 p = ℓ (berezin (F p)) := by
  simp [jint, gauss, W]

theorem hasDerivAt_jint (γ : ℝ) (p : Pt N) :
    HasDerivAt (fun γ => jint F ℓ γ p) (jder F ℓ γ p) γ := by
  have hg : HasDerivAt (fun γ => gauss γ p) (gauss γ p * (-sfun p)) γ := by
    have h := ((hasDerivAt_neg γ).mul_const (sfun p)).exp
    have e : gauss γ p * -sfun p = Real.exp (-γ * sfun p) * (-1 * sfun p) := by
      rw [gauss]; ring
    rw [e]; exact h
  have hw := hasDerivAt_dual_W (ℓ ∘ₗ berezin ∘ₗ LinearMap.mulLeft ℝ (F p)) γ
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply] at hw
  show HasDerivAt (fun γ => gauss γ p * ℓ (berezin (F p * W γ)))
    (gauss γ p * (-sfun p * ℓ (berezin (F p * W γ)) + ℓ (berezin (F p * (ω * W γ))))) γ
  convert hg.mul hw using 1
  ring

/-- The `γ`-derivative is minus the integrand of a `Q`-exact form. -/
theorem jder_eq (hF : SDiff F) (hQ : ∀ p, Q F p = 0) (γ : ℝ) (p : Pt N) :
    jder F ℓ γ p = -ℓ (berezin (Q (fun q => lam q * (F q * Egam γ q)) p)) := by
  rw [Q_mul sdiff_lam (hF.mul (sdiff_Egam γ)), Q_mul hF (sdiff_Egam γ), hQ, Q_Egam, Q_lam]
  simp only [zero_mul, mul_zero, add_zero]
  have hS : S p * F p = F p * (S p : SG N P) := by
    refine mul_comm_of_even' ?_ _
    rw [S, map_sub, map_smul, map_one, inv'_ω]
  rw [← mul_assoc, hS, mul_assoc, S, Egam]
  simp only [sub_mul, smul_mul_assoc, one_mul, mul_smul_comm, mul_sub, map_sub, map_smul,
    smul_eq_mul, jder, ← mul_assoc]
  ring

/-- `λ F e^{-γS}` written through `Temp` multipliers. -/
theorem lam_mul_eq (γ : ℝ) (q : Pt N) :
    lam q * (F q * Egam γ q) = ∑ i, ((q (Sum.inr i) / 2 * gauss γ q) • (ξ i * (F q * W γ)) -
      (q (Sum.inl i) / 2 * gauss γ q) • (η i * (F q * W γ))) := by
  rw [lam, Egam, mul_smul_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_smul,
    smul_smul]

theorem temp_coord_half (k : N ⊕ N) : Temp fun q : Pt N => q k / 2 := by
  have h := Temp.clm ((1 / 2 : ℝ) • ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : N ⊕ N => ℝ) k)
  convert h using 2 with q
  simp; ring

theorem sdecay_theta (hF : SDecay F) {γ : ℝ} (hγ : 0 ≤ γ) :
    SDecay fun q => lam q * (F q * Egam γ q) := by
  simp_rw [lam_mul_eq]
  refine SDecay.sum _ fun i _ => SDecay.sub ?_ ?_
  · exact (hF.map (LinearMap.mulLeft ℝ (ξ i) ∘ₗ LinearMap.mulRight ℝ (W γ))).smul
      ((temp_coord_half _).mul (temp_gauss hγ))
  · exact (hF.map (LinearMap.mulLeft ℝ (η i) ∘ₗ LinearMap.mulRight ℝ (W γ))).smul
      ((temp_coord_half _).mul (temp_gauss hγ))

theorem integral_jder_eq_zero (hF : SDecay F) (hQ : ∀ p, Q F p = 0) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∫ p, jder F ℓ γ p = 0 := by
  simp_rw [jder_eq hF.sdiff hQ γ]
  rw [integral_neg, integral_berezin_Q (sdecay_theta hF hγ), neg_zero]

/-! ### Bounds -/

/-- The bilinear form `(x, y) ↦ ℓ (∫dξdη x y)`. -/
def bil (ℓ : Module.Dual ℝ (SG N P)) : SG N P →ₗ[ℝ] SG N P →ₗ[ℝ] ℝ :=
  (LinearMap.mul ℝ (SG N P)).compr₂ (ℓ ∘ₗ berezin)

theorem bil_apply (x y : SG N P) : bil ℓ x y = ℓ (berezin (x * y)) := rfl

/-- The constant in `|ℓ (∫dξdη x y)| ≤ Kb ℓ · |x| · |y|`. -/
def Kb (ℓ : Module.Dual ℝ (SG N P)) : ℝ :=
  ∑ m, ∑ n, |bil ℓ (fb (SG N P) m) (fb (SG N P) n)|

theorem Kb_nonneg : 0 ≤ Kb ℓ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_dual_berezin_mul_le (x y : SG N P) :
    |ℓ (berezin (x * y))| ≤ Kb ℓ * anorm x * anorm y := abs_bilin_le (bil ℓ) x y

theorem continuous_jint_p (hF : SDecay F) (γ : ℝ) : Continuous (jint F ℓ γ) :=
  (Real.continuous_exp.comp (continuous_const.mul (differentiable_sfun.continuous))).mul
    (hF.continuous (ℓ ∘ₗ berezin ∘ₗ LinearMap.mulRight ℝ (W γ)))

theorem continuous_jder_p (hF : SDecay F) (γ : ℝ) : Continuous (jder F ℓ γ) :=
  (Real.continuous_exp.comp (continuous_const.mul (differentiable_sfun.continuous))).mul
    ((differentiable_sfun.continuous.neg.mul
      (hF.continuous (ℓ ∘ₗ berezin ∘ₗ LinearMap.mulRight ℝ (W γ)))).add
      (hF.continuous (ℓ ∘ₗ berezin ∘ₗ LinearMap.mulRight ℝ (ω * W γ))))

/-- `p ↦ C (sfun p + 1) |F p|` is integrable. -/
theorem integrable_bound (hF : SDecay F) (C : ℝ) :
    Integrable fun p => (sfun p + 1) * (C * anorm (F p)) :=
  ((hF.rdec_anorm.const_mul C).mul (differentiable_sfun.continuous.add continuous_const)
    (temp_sfun.2.1.add (PolyBd.const 1))).integrable

theorem abs_jint_le {γ : ℝ} (hγ : 0 ≤ γ) (p : Pt N) :
    |jint F ℓ γ p| ≤ Kb ℓ * anorm (F p) * anorm (W γ : SG N P) := by
  rw [jint, abs_mul, abs_of_pos (gauss_pos γ p)]
  have h1 := gauss_le_one hγ p
  have h2 := abs_dual_berezin_mul_le (ℓ := ℓ) (F p) (W γ)
  have h3 : 0 ≤ |ℓ (berezin (F p * W γ))| := abs_nonneg _
  nlinarith

theorem abs_jder_le {γ : ℝ} (hγ : 0 ≤ γ) {M : ℝ} (hW : anorm (W γ : SG N P) ≤ M)
    (hωW : anorm (ω * W γ : SG N P) ≤ M) (p : Pt N) :
    |jder F ℓ γ p| ≤ (sfun p + 1) * (Kb ℓ * M * anorm (F p)) := by
  rw [jder, abs_mul, abs_of_pos (gauss_pos γ p)]
  have h1 := gauss_le_one hγ p
  have hs := sfun_nonneg p
  have hK := Kb_nonneg (ℓ := ℓ)
  have hF0 := anorm_nonneg (F p)
  have e1 := abs_dual_berezin_mul_le (ℓ := ℓ) (F p) (W γ)
  have e2 := abs_dual_berezin_mul_le (ℓ := ℓ) (F p) (ω * W γ)
  have hM : 0 ≤ M := (anorm_nonneg _).trans hW
  have b1 : |ℓ (berezin (F p * W γ))| ≤ Kb ℓ * M * anorm (F p) := by
    refine e1.trans ?_
    calc Kb ℓ * anorm (F p) * anorm (W γ) ≤ Kb ℓ * anorm (F p) * M := by gcongr
      _ = _ := by ring
  have b2 : |ℓ (berezin (F p * (ω * W γ)))| ≤ Kb ℓ * M * anorm (F p) := by
    refine e2.trans ?_
    calc Kb ℓ * anorm (F p) * anorm (ω * W γ) ≤ Kb ℓ * anorm (F p) * M := by gcongr
      _ = _ := by ring
  have b3 : |-sfun p * ℓ (berezin (F p * W γ)) + ℓ (berezin (F p * (ω * W γ)))| ≤
      (sfun p + 1) * (Kb ℓ * M * anorm (F p)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_neg, abs_of_nonneg hs]
    nlinarith [abs_nonneg (ℓ (berezin (F p * W γ)))]
  have b4 : 0 ≤ |-sfun p * ℓ (berezin (F p * W γ)) + ℓ (berezin (F p * (ω * W γ)))| :=
    abs_nonneg _
  nlinarith

/-! ### Step 1: `J` is constant on `(0, ∞)` -/

theorem integrable_jint (hF : SDecay F) {γ : ℝ} (hγ : 0 ≤ γ) : Integrable (jint F ℓ γ) := by
  refine (integrable_bound hF (Kb ℓ * anorm (W γ : SG N P))).mono'
    (continuous_jint_p hF γ).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_jint_le hγ p).trans ?_
  have := Kb_nonneg (ℓ := ℓ)
  have := anorm_nonneg (F p)
  have := anorm_nonneg (W γ : SG N P)
  have := sfun_nonneg p
  nlinarith [mul_nonneg (mul_nonneg ‹0 ≤ Kb ℓ› ‹0 ≤ anorm (F p)›) ‹0 ≤ anorm (W γ : SG N P)›]

theorem hasDerivAt_J (hF : SDecay F) (hQ : ∀ p, Q F p = 0) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    HasDerivAt (J F ℓ) 0 γ₀ := by
  set K := Metric.closedBall γ₀ (γ₀ / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (((continuous_anorm_W (N := N) (P := P)).add
      (continuous_anorm_ωW (N := N) (P := P))).continuousOn (s := K))
  have hpos : ∀ γ ∈ Metric.ball γ₀ (γ₀ / 2), 0 ≤ γ := fun γ hγ => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hγ; linarith
  have hMb : ∀ γ ∈ Metric.ball γ₀ (γ₀ / 2),
      anorm (W γ : SG N P) ≤ M ∧ anorm (ω * W γ : SG N P) ≤ M := fun γ hγ => by
    have h := hM γ (Metric.ball_subset_closedBall hγ)
    simp only [Pi.add_apply] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (anorm_nonneg _) (anorm_nonneg _))] at h
    exact ⟨by linarith [anorm_nonneg (ω * W γ : SG N P)], by
      linarith [anorm_nonneg (W γ : SG N P)]⟩
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun γ p => jint F ℓ γ p) (F' := fun γ p => jder F ℓ γ p) (x₀ := γ₀)
    (bound := fun p => (sfun p + 1) * (Kb ℓ * M * anorm (F p)))
    (Metric.ball_mem_nhds γ₀ (half_pos hγ₀))
    (Eventually.of_forall fun γ => (continuous_jint_p hF γ).aestronglyMeasurable)
    (integrable_jint hF hγ₀.le)
    (continuous_jder_p hF γ₀).aestronglyMeasurable
    (Eventually.of_forall fun p γ hγ => by
      rw [Real.norm_eq_abs]
      exact abs_jder_le (hpos γ hγ) (hMb γ hγ).1 (hMb γ hγ).2 p)
    (integrable_bound hF _)
    (Eventually.of_forall fun p γ _ => hasDerivAt_jint γ p)
  rw [integral_jder_eq_zero hF hQ hγ₀.le] at h
  exact h.2

theorem J_eq_J_one (hF : SDecay F) (hQ : ∀ p, Q F p = 0) {γ : ℝ} (hγ : 0 < γ) :
    J F ℓ γ = J F ℓ 1 := by
  refine isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
    (fun γ hγ => (hasDerivAt_J hF hQ hγ).differentiableAt.differentiableWithinAt)
    (fun γ hγ => (hasDerivAt_J hF hQ hγ).deriv) hγ (Set.mem_Ioi.2 one_pos)

/-! ### Step 2: `γ ↓ 0` -/

theorem tendsto_J_zero (hF : SDecay F) :
    Tendsto (J F ℓ) (𝓝[>] 0) (𝓝 (∫ p, ℓ (berezin (F p)))) := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_anorm_W (N := N) (P := P)).continuousOn
  simp_rw [← jint_zero (F := F) (ℓ := ℓ)]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => (sfun p + 1) * (Kb ℓ * M * anorm (F p))) ?_ ?_ (integrable_bound hF _) ?_
  · exact Eventually.of_forall fun γ => (continuous_jint_p hF γ).aestronglyMeasurable
  · have : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Set.Icc (0 : ℝ) 1 := by
      have h1 : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
      filter_upwards [h1] with γ hγ using ⟨hγ.1.le, hγ.2.le⟩
    filter_upwards [this] with γ hγ
    refine Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs]
    refine (abs_jint_le hγ.1 p).trans ?_
    have hb := hM γ hγ
    rw [Real.norm_eq_abs, abs_of_nonneg (anorm_nonneg _)] at hb
    have := Kb_nonneg (ℓ := ℓ)
    have := anorm_nonneg (F p)
    have := sfun_nonneg p
    have h0 : 0 ≤ Kb ℓ * anorm (F p) := by positivity
    calc Kb ℓ * anorm (F p) * anorm (W γ) ≤ Kb ℓ * anorm (F p) * M := by gcongr
      _ ≤ (sfun p + 1) * (Kb ℓ * M * anorm (F p)) := by
          have hM0 : 0 ≤ M := (anorm_nonneg _).trans hb
          nlinarith [mul_nonneg h0 hM0]
  · refine Eventually.of_forall fun p => ?_
    have hc : Continuous fun γ => jint F ℓ γ p :=
      continuous_iff_continuousAt.2 fun γ => (hasDerivAt_jint γ p).continuousAt
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-! ### Step 3: `γ → ∞` -/

theorem J_eq_scaled {γ : ℝ} (hγ : 0 < γ) :
    J F ℓ γ = ∫ q, gauss 1 q *
      ℓ (TL γ⁻¹ 1 (Finset.univ : Finset N).toList (F ((√γ)⁻¹ • q))) := by
  set R := (√γ)⁻¹
  have hsq : 0 < √γ := Real.sqrt_pos.2 hγ
  have hR : R ^ 2 = γ⁻¹ := by rw [inv_pow, Real.sq_sqrt hγ.le]
  have hfin : Module.finrank ℝ (Pt N) = 2 * Fintype.card N := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, two_mul]
  have hlen : (Finset.univ : Finset N).toList.length = Fintype.card N := by
    rw [Finset.length_toList, Finset.card_univ]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Pt N))) (jint F ℓ γ) R
  have hpt : ∀ q : Pt N, jint F ℓ γ (R • q) = γ ^ Fintype.card N * (gauss 1 q *
      ℓ (TL γ⁻¹ 1 (Finset.univ : Finset N).toList (F (R • q)))) := fun q => by
    rw [jint, berezin_mul_W]
    have hT := TL_smul (N := N) (P := P) γ γ⁻¹ 1 (Finset.univ : Finset N).toList (F (R • q))
    rw [mul_inv_cancel₀ hγ.ne', mul_one] at hT
    rw [hT, map_smul, hlen, smul_eq_mul, gauss, gauss, sfun_smul, hR]
    rw [show -γ * (γ⁻¹ * sfun q) = -1 * sfun q by field_simp]
    ring
  simp_rw [hpt] at h
  rw [integral_const_mul, hfin, pow_mul, hR] at h
  have hγn : (γ ^ Fintype.card N : ℝ) ≠ 0 := pow_ne_zero _ hγ.ne'
  rw [inv_pow, inv_inv, abs_of_pos (pow_pos hγ _), smul_eq_mul] at h
  exact (mul_left_cancel₀ hγn h).symm

theorem tendsto_J_atTop (hF : SDecay F) :
    Tendsto (J F ℓ) atTop (𝓝 ((2 * Real.pi) ^ Fintype.card N * ℓ (pi0 (F 0)))) := by
  set L := (Finset.univ : Finset N).toList
  -- uniform bound on `ℓ ∘ TL t 1` for `t ∈ [0, 1]`
  have hcont : Continuous fun t => ∑ m, |ℓ (TL t 1 L (fb (SG N P) m))| :=
    continuous_finsetSum _ fun m _ => (continuous_dual_TL L ℓ _).abs
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨CF, hCF⟩ := hF.anorm_bounded
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : SG N P, |ℓ (TL t 1 L x)| ≤ M * anorm x := by
    intro t ht x
    have h1 := abs_dual_le (ℓ ∘ₗ TL t 1 L) x
    have h2 := hM t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h2
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (anorm_nonneg x))
  -- the limit of the integrand
  have hlim : ∀ q : Pt N, Tendsto (fun γ : ℝ => gauss 1 q * ℓ (TL γ⁻¹ 1 L (F ((√γ)⁻¹ • q))))
      atTop (𝓝 (gauss 1 q * ℓ (pi0 (F 0)))) := by
    intro q
    refine Tendsto.const_mul _ ?_
    have ht : Tendsto (fun γ : ℝ => γ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hs : Tendsto (fun γ : ℝ => (√γ)⁻¹ • q) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).smul_const q
      simpa using this
    have e : ∀ γ : ℝ, ℓ (TL γ⁻¹ 1 L (F ((√γ)⁻¹ • q))) =
        ∑ m, crd m (F ((√γ)⁻¹ • q)) * ℓ (TL γ⁻¹ 1 L (fb (SG N P) m)) := fun γ =>
      dual_eq_sum (ℓ ∘ₗ TL γ⁻¹ 1 L) _
    simp_rw [e]
    have e0 : ℓ (pi0 (F 0)) = ∑ m, crd m (F 0) * ℓ (TL 0 1 L (fb (SG N P) m)) := by
      rw [← TL_zero_one (F 0)]; exact dual_eq_sum (ℓ ∘ₗ TL 0 1 L) (F 0)
    rw [e0]
    refine tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_
    · exact ((hF.continuous (crd m)).tendsto 0).comp hs
    · exact ((continuous_dual_TL L ℓ _).tendsto 0).comp ht
  have hlimJ : Tendsto (fun γ : ℝ => ∫ q, gauss 1 q * ℓ (TL γ⁻¹ 1 L (F ((√γ)⁻¹ • q))))
      atTop (𝓝 (∫ q : Pt N, gauss 1 q * ℓ (pi0 (F 0)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun q : Pt N => gauss 1 q * (M * CF)) ?_ ?_ ((integrable_gauss_one (N := N)).mul_const _)
      (Eventually.of_forall hlim)
    · refine Eventually.of_forall fun γ => ?_
      refine ((Real.continuous_exp.comp (continuous_const.mul
        differentiable_sfun.continuous)).mul ?_).aestronglyMeasurable
      exact (hF.continuous (ℓ ∘ₗ TL γ⁻¹ 1 L)).comp (continuous_const_smul _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
      refine Eventually.of_forall fun q => ?_
      have ht : γ⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨inv_nonneg.2 (by linarith), inv_le_one_of_one_le₀ hγ⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gauss_pos 1 q)]
      refine mul_le_mul_of_nonneg_left ?_ (gauss_pos 1 q).le
      refine (hbd _ ht _).trans ?_
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
      exact mul_le_mul_of_nonneg_left (hCF _) hM0
  rw [integral_mul_const, integral_gauss_one] at hlimJ
  refine hlimJ.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
  exact (J_eq_scaled hγ).symm

/-! ### The localization theorem -/

/-- Scalar form of the localization theorem:
`∫ ℓ (∫ dξ dη F) dx dy = (2π)^N ℓ (F_0(0))`. -/
theorem integral_dual_berezin_eq (hF : SDecay F) (hQ : ∀ p, Q F p = 0)
    (ℓ : Module.Dual ℝ (SG N P)) :
    ∫ p, ℓ (berezin (F p)) = (2 * Real.pi) ^ Fintype.card N * ℓ (pi0 (F 0)) := by
  have h1 : J F ℓ 1 = (2 * Real.pi) ^ Fintype.card N * ℓ (pi0 (F 0)) := by
    refine tendsto_nhds_unique ?_ (tendsto_J_atTop hF)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
    exact (J_eq_J_one hF hQ hγ).symm
  have h0 : ∫ p, ℓ (berezin (F p)) = J F ℓ 1 := by
    refine tendsto_nhds_unique (tendsto_J_zero hF) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact (J_eq_J_one hF hQ hγ).symm
  rw [h0, h1]

/-- **Localization theorem** (BCHS Theorem 2.8; BHS Appendix B).  If every Grassmann coordinate
of `F : ℝ^{2N} → SG N P` is `C¹` and, with its first partial derivatives, rapidly decreasing,
and `Q F = 0`, then
`∫_{ℝ^{2N|2N}} F = (2π)^{-N} ∫ dx dy ∏_i ∂_{η_i}∂_{ξ_i} F = F_0(0)`,
where `F_0(0) = pi0 (F 0)` is the degree-zero part (in the integrated generators) of `F` at the
origin.  Parameter generators indexed by `P` are allowed and are carried along. -/
theorem superIntegral_eq_pi0 {F : Pt N → SG N P} (hF : SDecay F) (hQ : ∀ p, Q F p = 0) :
    superIntegral F = pi0 (F 0) := by
  refine ext_dual fun ℓ => ?_
  have hint : SInt (fun p => berezin (F p)) volume := (hF.map berezin).sint
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ Fintype.card N := by positivity
  rw [superIntegral, map_smul, dual_sint hint, integral_dual_berezin_eq hF hQ ℓ, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]

end

end ArborealDecay.Super

end
