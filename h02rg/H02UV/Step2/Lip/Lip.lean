import Step2.Map.HolC
import Step2.Coup.Est4

/-!
# Lipschitz bounds for the step map (Expected result `thm:step-rest`)

* `wnorm_sub_le_of_hol`: the Cauchy estimate `‖F(1) - F(0)‖ ≤ B/(R-1)` for a holomorphic
  family bounded by `B` on the circle of radius `R > 1`;
* `Kplus_cauchy`: the same for `K_{j+1}` along a holomorphic family `z ↦ (C(z), V(z), 𝒲(z), K(z))`
  satisfying the hypotheses of `stepK` on the circle;
* `Kplus_lip`: Lipschitz continuity of `K_{j+1}` in `(V, 𝒲, K)` at fixed `C`;
* `Kplus_lip_cov`: Lipschitz continuity of `K_{j+1}` along a holomorphic family of covariances
  (e.g. in the history `ζ_0, …, ζ_j`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- **Cauchy estimate for a holomorphic family.** -/
theorem wnorm_sub_le_of_hol {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 < A) (U : Finset (Lam d L N))
    {F : ℂ → EvR (Lam d L N)} (hF : HolE F) {R B : ℝ} (hR : 1 < R) (hB0 : 0 ≤ B)
    (hB : ∀ z : ℂ, ‖z‖ = R → wnorm j ℓ A U (F z) ≤ ENNReal.ofReal B) :
    wnorm j ℓ A U (F 1 - F 0) ≤ ENNReal.ofReal (B / (R - 1)) := by
  refine wnorm_le_of_wpair hA U _ fun g hg => ?_
  have hw : 0 ≤ wt j A U := pow_nonneg hA.le _
  set φ : ℂ → ℂ := fun z => (wt j A U : ℂ) * pairL g (F z : Alg d L N) with hφdef
  have hφ : Differentiable ℂ φ := (differentiable_const _).mul (hF.lin (pairL g))
  have hM : ∀ z : ℂ, ‖z‖ = R → ‖φ z‖ ≤ B := by
    intro z hz
    have h1 := wpair_le_wnorm hℓ hA.le U (F z) hg
    rw [hφdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    exact h1.trans (ENNReal.toReal_le_of_le_ofReal hB0 (hB z hz))
  have h := (norm_taylor_le hφ hR hM).1
  have e : φ 1 - φ 0 = (wt j A U : ℂ) * pair ((F 1 - F 0 : EvR (Lam d L N)) : Alg d L N) g := by
    simp only [hφdef, AddSubgroupClass.coe_sub]
    rw [← mul_sub]
    congr 1
    exact (map_sub (pairL g) _ _).symm
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw] at h
  exact h

/-! ### Cauchy estimates on a closed disc -/

theorem norm_taylor_le_on {φ : ℂ → ℂ} {R M : ℝ} (hR : 1 < R)
    (hφ : DifferentiableOn ℂ φ (Metric.closedBall 0 R)) (hM : ∀ ζ : ℂ, ‖ζ‖ = R → ‖φ ζ‖ ≤ M) :
    ‖φ 1 - φ 0‖ ≤ M / (R - 1) := by
  have hR0 : 0 < R := by linarith
  set R' : NNReal := ⟨R, hR0.le⟩
  have hR' : 0 < R' := hR0
  have hp := hφ.hasFPowerSeriesOnBall (R := R') hR'
  set p := cauchyPowerSeries φ 0 (R' : ℝ)
  have hs : HasSum (fun n => p n (fun _ => 1)) (φ 1) := by
    simpa using hp.hasSum (y := 1) (by simp [R']; exact_mod_cast hR)
  have h0 : p 0 (fun _ => 1) = φ 0 := hp.hasFPowerSeriesAt.coeff_zero _
  have hb : ∀ n, ‖p n (fun _ => 1)‖ ≤ M * R⁻¹ ^ n := by
    intro n
    refine ((cauchyPowerSeries φ 0 R n).le_opNorm _).trans ?_
    simp only [norm_one, Finset.prod_const_one, mul_one]
    refine (norm_cauchyPowerSeries_le φ 0 R n).trans ?_
    rw [abs_of_pos hR0]
    gcongr
    have hc : ContinuousOn (fun θ : ℝ => ‖φ (circleMap 0 R θ)‖) (Set.uIcc 0 (2 * Real.pi)) := by
      refine (hφ.continuousOn.comp (continuous_circleMap 0 R).continuousOn fun θ _ => ?_).norm
      simp [Metric.mem_closedBall, abs_of_pos hR0]
    have h1 : ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖φ (circleMap 0 R θ)‖ ≤
        ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, M := by
      refine intervalIntegral.integral_mono_on (by positivity) (hc.intervalIntegrable)
        intervalIntegrable_const fun θ _ => hM _ ?_
      rw [norm_circleMap_zero, abs_of_pos hR0]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    have hπ : 0 < 2 * Real.pi := by positivity
    calc (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖φ (circleMap 0 R θ)‖
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) := by gcongr
      _ = M := by field_simp
  have hr0 : 0 ≤ R⁻¹ := by positivity
  have hr1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hg : HasSum (fun n => M * R⁻¹ ^ (n + 1)) (M * R⁻¹ ^ 1 * (1 - R⁻¹)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (M * R⁻¹ ^ 1)
    simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using this
  have hne : R - 1 ≠ 0 := by linarith
  have hs1 := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.sum_range_one, h0] at hs1
  refine (hs1.norm_le_of_bounded hg fun n => hb _).trans (le_of_eq ?_)
  field_simp

/-- **Cauchy estimate on a closed disc.** -/
theorem wnorm_sub_le_of_holOn {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 < A)
    (U : Finset (Lam d L N)) {F : ℂ → EvR (Lam d L N)} {R B : ℝ} (hR : 1 < R)
    (hF : ∀ Λf : Alg d L N →ₗ[ℂ] ℂ,
      DifferentiableOn ℂ (fun z => Λf (F z : Alg d L N)) (Metric.closedBall 0 R)) (hB0 : 0 ≤ B)
    (hB : ∀ z : ℂ, ‖z‖ = R → wnorm j ℓ A U (F z) ≤ ENNReal.ofReal B) :
    wnorm j ℓ A U (F 1 - F 0) ≤ ENNReal.ofReal (B / (R - 1)) := by
  refine wnorm_le_of_wpair hA U _ fun g hg => ?_
  have hw : 0 ≤ wt j A U := pow_nonneg hA.le _
  set φ : ℂ → ℂ := fun z => (wt j A U : ℂ) * pairL g (F z : Alg d L N) with hφdef
  have hφ : DifferentiableOn ℂ φ (Metric.closedBall 0 R) :=
    (differentiableOn_const _).mul (hF (pairL g))
  have hM : ∀ z : ℂ, ‖z‖ = R → ‖φ z‖ ≤ B := by
    intro z hz
    have h1 := wpair_le_wnorm hℓ hA.le U (F z) hg
    rw [hφdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    exact h1.trans (ENNReal.toReal_le_of_le_ofReal hB0 (hB z hz))
  have h := norm_taylor_le_on hR hφ hM
  have e : φ 1 - φ 0 = (wt j A U : ℂ) * pair ((F 1 - F 0 : EvR (Lam d L N)) : Alg d L N) g := by
    simp only [hφdef, AddSubgroupClass.coe_sub]
    rw [← mul_sub]
    congr 1
    exact (map_sub (pairL g) _ _).symm
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw] at h
  exact h

theorem InK2.add {j : ℕ} {K K' : Act d L N} (hK : InK2 j K) (hK' : InK2 j K') : InK2 j (K + K') :=
  ⟨fun X hX => by rw [Pi.add_apply, Subalgebra.coe_add]; exact add_mem (hK.loc X hX) (hK'.loc X hX),
    fun X hX n z hz => by
      rw [Pi.add_apply, Subalgebra.coe_add, coeff_add, hK.sym X hX n z hz, hK'.sym X hX n z hz,
        add_zero]⟩

theorem InK2.sub {j : ℕ} {K K' : Act d L N} (hK : InK2 j K) (hK' : InK2 j K') : InK2 j (K - K') := by
  have := hK.add (hK'.smul (-1))
  simpa [sub_eq_add_neg] using this

theorem wnorm_sub_le' (j : ℕ) (ℓ A : ℝ) (U : Finset (Lam d L N)) (F G : EvR (Lam d L N)) :
    wnorm j ℓ A U (F - G) ≤ wnorm j ℓ A U F + wnorm j ℓ A U G := by
  unfold wnorm
  rw [← mul_add, AddSubgroupClass.coe_sub]
  gcongr
  exact Loc.tNorm_sub_le _ _

/-- The `stepK` bound in real form. -/
theorem ennreal_stepK {X Kn : ENNReal} {κ C₁ g k : ℝ} (hκ : 0 ≤ κ) (hC₁ : 0 ≤ C₁) (hg : 0 ≤ g)
    (hk : 0 ≤ k) (hKn : Kn ≤ ENNReal.ofReal k)
    (h : X ≤ ENNReal.ofReal κ * Kn + ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) +
      ENNReal.ofReal g * Kn + Kn ^ 2)) :
    X ≤ ENNReal.ofReal (κ * k + C₁ * (g ^ 3 + g * k + k ^ 2)) := by
  refine h.trans ?_
  calc ENNReal.ofReal κ * Kn + ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) +
        ENNReal.ofReal g * Kn + Kn ^ 2)
      ≤ ENNReal.ofReal κ * ENNReal.ofReal k + ENNReal.ofReal C₁ * (ENNReal.ofReal (g ^ 3) +
        ENNReal.ofReal g * ENNReal.ofReal k + ENNReal.ofReal k ^ 2) := by gcongr
    _ = ENNReal.ofReal (κ * k + C₁ * (g ^ 3 + g * k + k ^ 2)) := by
      rw [← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_pow hk,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC₁,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- Norm bounds along the segment `x + z (x' - x)` on the circle `|z| = R`. -/
theorem line_norms {j : ℕ} {ℓ A : ℝ} (V V' W W' : Fam d L N) (K K' : Act d L N) {e R a b c : ℝ}
    (he : 0 ≤ e) (hR0 : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (z : ℂ) (hz : ‖z‖ = R)
    (hVe : Fnorm j ℓ V ≤ ENNReal.ofReal e) (hWe : Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2))
    (hKe : Knorm j ℓ A K ≤ ENNReal.ofReal (e ^ 2))
    (hda : Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a) (hdb : Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b)
    (hdc : Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal c)
    (hRa : R * a ≤ e) (hRb : R * b ≤ e ^ 2) (hRc : R * c ≤ e ^ 2) :
    Fnorm j ℓ (V + z • (V' - V)) ≤ ENNReal.ofReal (2 * e) ∧
      Fnorm j ℓ (W + z • (W' - W)) ≤ ENNReal.ofReal ((2 * e) ^ 2) ∧
      Knorm j ℓ A (K + z • (K' - K)) ≤ ENNReal.ofReal (2 * e ^ 2) := by
  have hsm : ∀ (F : Fam d L N) (t : ℝ), 0 ≤ t → Fnorm j ℓ F ≤ ENNReal.ofReal t →
      Fnorm j ℓ (z • F) ≤ ENNReal.ofReal (R * t) := fun F t ht hF => by
    have h := Fnorm_smul j ℓ z F
    rw [hz] at h
    rw [show z • F = fun b => z • F b from rfl, h, ENNReal.ofReal_mul hR0]
    exact mul_le_mul_left' hF _
  refine ⟨?_, ?_, ?_⟩
  · refine (Fnorm_add_le _ _ he (mul_nonneg hR0 ha) hVe (hsm _ a ha hda)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    linarith
  · refine (Fnorm_add_le _ _ (sq_nonneg e) (mul_nonneg hR0 hb) hWe (hsm _ b hb hdb)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  · refine (Knorm_add_le j ℓ A K (z • (K' - K))).trans ?_
    rw [Knorm_smul, hz]
    calc Knorm j ℓ A K + ENNReal.ofReal R * Knorm j ℓ A (K' - K)
        ≤ ENNReal.ofReal (e ^ 2) + ENNReal.ofReal R * ENNReal.ofReal c :=
          add_le_add hKe (mul_le_mul_left' hdc _)
      _ = ENNReal.ofReal (e ^ 2 + R * c) := by
        rw [← ENNReal.ofReal_mul hR0, ← ENNReal.ofReal_add (sq_nonneg e) (mul_nonneg hR0 hc)]
      _ ≤ ENNReal.ofReal (2 * e ^ 2) := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Lipschitz bound from a bound on a ball** (abstract form). If `Φ` is holomorphic along affine
families and satisfies the `stepK`-type bound `κ k + C₁(g³ + g k + k²)` on the domain
`‖V‖ ≤ g`, `‖𝒲‖ ≤ g²`, `‖K‖ ≤ k`, then on `‖V‖ ≤ e`, `‖𝒲‖, ‖K‖ ≤ e²`,
`‖Φ(x') - Φ(x)‖ ≤ 4(κ + 8C₁e)(e‖δV‖ + ‖δ𝒲‖ + ‖δK‖)`. -/
theorem lip_of_bound {j : ℕ} {ℓ ℓ' A κ C₁ ε₀ : ℝ} (hℓ' : 0 < ℓ') (hA : 0 < A) (U : Finset (Lam d L N))
    (Φ : Fam d L N → Fam d L N → Act d L N → EvR (Lam d L N))
    (hhol : ∀ (Vf Wf : ℂ → Fam d L N) (Kf : ℂ → Act d L N), (∀ b, HolE (fun z => Vf z b)) →
      (∀ b, HolE (fun z => Wf z b)) → (∀ X, HolE (fun z => Kf z X)) →
      (∀ z b, ε (Vf z b : Alg d L N) = 0) → HolE (fun z => Φ (Vf z) (Wf z) (Kf z)))
    (hκ : 0 ≤ κ) (hC₁ : 0 ≤ C₁)
    (H : ∀ (V W : Fam d L N) (K : Act d L N) (g k : ℝ), InF j V → InF j W → InK2 j K →
      (∀ b, ε (V b : Alg d L N) = 0) → 0 ≤ g → g ≤ ε₀ → 0 ≤ k → k ≤ ε₀ →
      Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A K ≤ ENNReal.ofReal k →
      wnorm (j + 1) ℓ' A U (Φ V W K) ≤ ENNReal.ofReal (κ * k + C₁ * (g ^ 3 + g * k + k ^ 2)))
    {V V' W W' : Fam d L N} {K K' : Act d L N} (hV : InF j V) (hV' : InF j V') (hW : InF j W)
    (hW' : InF j W') (hK : InK2 j K) (hK' : InK2 j K') (hV0 : ∀ b, ε (V b : Alg d L N) = 0)
    (hV0' : ∀ b, ε (V' b : Alg d L N) = 0) {e : ℝ} (he : 0 < e) (he2 : e ≤ ε₀ / 2) (he1 : e ≤ 1)
    (hVe : Fnorm j ℓ V ≤ ENNReal.ofReal e) (hVe' : Fnorm j ℓ V' ≤ ENNReal.ofReal e)
    (hWe : Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2)) (hWe' : Fnorm j ℓ W' ≤ ENNReal.ofReal (e ^ 2))
    (hKe : Knorm j ℓ A K ≤ ENNReal.ofReal (e ^ 2)) (hKe' : Knorm j ℓ A K' ≤ ENNReal.ofReal (e ^ 2))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hda : Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a) (hdb : Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b)
    (hdc : Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal c) :
    wnorm (j + 1) ℓ' A U (Φ V' W' K' - Φ V W K) ≤
      ENNReal.ofReal (4 * (κ + 8 * C₁ * e) * (e * a + b + c)) := by
  have hs0 : 0 ≤ e * a + b + c := by positivity
  have he4 : e ^ 4 ≤ e ^ 3 := pow_le_pow_of_le_one he.le he1 (by norm_num)
  have hC4 : C₁ * e ^ 4 ≤ C₁ * e ^ 3 := mul_le_mul_of_nonneg_left he4 hC₁
  by_cases hbig : e ^ 2 < 2 * (e * a + b + c)
  · -- far apart: bound both terms
    have hk : e ^ 2 ≤ ε₀ := by nlinarith only [he2, he1, he]
    have h1 := H V' W' K' e (e ^ 2) hV' hW' hK' hV0' he.le (by linarith) (sq_nonneg e) hk hVe' hWe'
      hKe'
    have h2 := H V W K e (e ^ 2) hV hW hK hV0 he.le (by linarith) (sq_nonneg e) hk hVe hWe hKe
    refine (wnorm_sub_le' _ _ _ _ _ _).trans ((add_le_add h1 h2).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hκs : κ * e ^ 2 ≤ κ * (2 * (e * a + b + c)) := mul_le_mul_of_nonneg_left hbig.le hκ
    have hCs : C₁ * e ^ 3 ≤ C₁ * (e * (2 * (e * a + b + c))) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hbig, he]) hC₁
    nlinarith only [hκs, hCs, hC4, mul_nonneg (mul_nonneg hC₁ he.le) hs0]
  · push_neg at hbig
    have hB0 : 0 ≤ 2 * κ * e ^ 2 + 16 * C₁ * e ^ 3 := by positivity
    -- the affine family
    have hVf : ∀ b, HolE (fun z : ℂ => (V + z • (V' - V)) b) := fun b =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hWf : ∀ b, HolE (fun z : ℂ => (W + z • (W' - W)) b) := fun b =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hKf : ∀ X, HolE (fun z : ℂ => (K + z • (K' - K)) X) := fun X =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hVf0 : ∀ (z : ℂ) b, ε ((V + z • (V' - V)) b : Alg d L N) = 0 := fun z b => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Subalgebra.coe_add,
        Subalgebra.coe_smul, AddSubgroupClass.coe_sub, map_add, map_smul, map_sub, hV0, hV0',
        sub_self, smul_zero, add_zero]
    have hF := hhol (fun z => V + z • (V' - V)) (fun z => W + z • (W' - W))
      (fun z => K + z • (K' - K)) hVf hWf hKf hVf0
    have e1 : (V + (1 : ℂ) • (V' - V), W + (1 : ℂ) • (W' - W), K + (1 : ℂ) • (K' - K)) =
        (V', W', K') := by simp
    have e0 : (V + (0 : ℂ) • (V' - V), W + (0 : ℂ) • (W' - W), K + (0 : ℂ) • (K' - K)) =
        (V, W, K) := by simp
    have key : ∀ R : ℝ, 2 ≤ R → R * (e * a + b + c) ≤ e ^ 2 →
        wnorm (j + 1) ℓ' A U (Φ V' W' K' - Φ V W K) ≤
          ENNReal.ofReal (2 * (2 * κ * e ^ 2 + 16 * C₁ * e ^ 3) / R) := by
      intro R hR2 hRs
      have hR0 : 0 < R := by linarith
      have hRa : R * a ≤ e := by
        have h1 : R * (e * a) ≤ e ^ 2 := le_trans (mul_le_mul_of_nonneg_left (by linarith) hR0.le)
          hRs
        nlinarith only [h1, he]
      have hRb : R * b ≤ e ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left (by nlinarith only [he, ha, hc]) hR0.le) hRs
      have hRc : R * c ≤ e ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left (by nlinarith only [he, ha, hb]) hR0.le) hRs
      have hstep := wnorm_sub_le_of_hol (j := j + 1) hℓ' hA U hF (by linarith : (1 : ℝ) < R) hB0
        fun z hz => by
          obtain ⟨hVz, hWz, hKz⟩ := line_norms V V' W W' K K' he.le hR0.le ha hb hc z hz hVe hWe
            hKe hda hdb hdc hRa hRb hRc
          refine (H _ _ _ (2 * e) (2 * e ^ 2) (inF_add hV (inF_smul (inF_sub hV' hV) z))
            (inF_add hW (inF_smul (inF_sub hW' hW) z)) (hK.add ((hK'.sub hK).smul z)) (hVf0 z)
            (by positivity) (by linarith) (by positivity) (by nlinarith only [he2, he1, he])
            hVz hWz hKz).trans (ENNReal.ofReal_le_ofReal ?_)
          nlinarith only [hC4]
      simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hstep
      refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ (by linarith) hR0]
      have := mul_le_mul_of_nonneg_left hR2 hB0
      linarith
    rcases hs0.eq_or_lt with hs | hs
    · -- every radius is admissible
      refine le_trans ?_ zero_le
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      rw [zero_add]
      have hη0 : (0 : ℝ) < η := hη
      obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max 2 (2 * (2 * κ * e ^ 2 + 16 * C₁ * e ^ 3) / η + 1) :=
        ⟨_, rfl⟩
      have hR2 : 2 ≤ R := hR ▸ le_max_left _ _
      have hR1 : 2 * (2 * κ * e ^ 2 + 16 * C₁ * e ^ 3) / η + 1 ≤ R := hR ▸ le_max_right _ _
      refine (key R hR2 (by rw [← hs, mul_zero]; positivity)).trans ?_
      rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
      have hR0 : 0 < R := by linarith
      rw [div_le_iff₀ hR0]
      have h3 := (div_le_iff₀ hη0).1 (by linarith : 2 * (2 * κ * e ^ 2 + 16 * C₁ * e ^ 3) / η ≤ R - 1)
      nlinarith only [h3, hη0]
    · refine (key (e ^ 2 / (e * a + b + c)) ((le_div_iff₀ hs).2 (by linarith))
        (by rw [div_mul_cancel₀ _ hs.ne'])).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_div_eq_mul_div]
      have he0 : 0 < e ^ 2 := by positivity
      rw [div_le_iff₀ he0]
      exact le_of_eq (by ring)

/-- **Lipschitz continuity of `K_{j+1}` in `(V, 𝒲, K)`.** On the domain
`‖V‖ ≤ ε`, `‖𝒲‖ ≤ ε²`, `‖K‖ ≤ ε²`,
`‖K_{j+1}(x') - K_{j+1}(x)‖ ≤ 4(κ₀ + 8C₁ε)(ε‖δV‖ + ‖δ𝒲‖ + ‖δK‖)`,
with `κ₀ = C₀(L^{d-3} + A^{-η})` the contraction factor of `stepK`. -/
theorem Kplus_lip_ts (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₁ C₁ : ℝ, 0 < ε₁ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (V V' W W' : Fam d L N) (K K' : Act d L N), InF j V → InF j V' → InF j W → InF j W' →
    InK2 j K → InK2 j K' → (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ ε₁ →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ W' ≤ ENNReal.ofReal (e ^ 2) →
    Knorm j ℓ A K ≤ ENNReal.ofReal (e ^ 2) → Knorm j ℓ A K' ≤ ENNReal.ofReal (e ^ 2) →
    ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
    Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a → Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b →
    Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal c →
    ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ' A U (Kplus j C V' W' K' U - Kplus j C V W K U) ≤
        ENNReal.ofReal (4 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) + 8 * C₁ * e) *
          (e * a + b + c)) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, hS⟩ := stepK_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, hS⟩ := hS L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, hS⟩ := hS A hA
  refine ⟨min (ε₀ / 2) 1, C₁, lt_min (by positivity) one_pos, hC₁, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V V' W W' K K' hV hV' hW hW' hK hK' hV0 hV0' e he he1 hVe hVe' hWe hWe'
    hKe hKe' a b c ha hb hc hda hdb hdc U hU
  have hA0 : 0 < A := by linarith
  refine lip_of_bound hℓ' hA0 U (fun V W K => Kplus j C V W K U)
    (fun Vf Wf Kf hVf hWf hKf hV0 =>
      Kplus_holC (Cf := fun _ => C) j (fun _ _ => differentiable_const _) hVf hWf hKf hV0 U)
    (by positivity) hC₁ (fun V W K g k hV hW hK hV0 hg0 hgε hk0 hkε hVg hWg hKk =>
      ennreal_stepK (by positivity) hC₁ hg0 hk0 hKk
        (hS N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK g hg0 hgε hVg hWg
          (hKk.trans (ENNReal.ofReal_le_ofReal hkε)) U hU))
    hV hV' hW hW' hK hK' hV0 hV0' he (he1.trans (min_le_left _ _)) (he1.trans (min_le_right _ _))
    hVe hVe' hWe hWe' hKe hKe' ha hb hc hda hdb hdc

/-- **Lipschitz continuity of `K_{j+1}` in `(V, 𝒲, K)`.** On the domain
`‖V‖ ≤ ε`, `‖𝒲‖ ≤ ε²`, `‖K‖ ≤ ε²`,
`‖K_{j+1}(x') - K_{j+1}(x)‖ ≤ 4(κ₀ + 8C₁ε)(ε‖δV‖ + ‖δ𝒲‖ + ‖δK‖)`,
with `κ₀ = C₀(L^{d-3} + A^{-η})` the contraction factor of `stepK`. -/
theorem Kplus_lip (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₁ C₁ : ℝ, 0 < ε₁ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓ C →
    ∀ (V V' W W' : Fam d L N) (K K' : Act d L N), InF j V → InF j V' → InF j W → InF j W' →
    InK2 j K → InK2 j K' → (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ ε₁ →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ W' ≤ ENNReal.ofReal (e ^ 2) →
    Knorm j ℓ A K ≤ ENNReal.ofReal (e ^ 2) → Knorm j ℓ A K' ≤ ENNReal.ofReal (e ^ 2) →
    ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
    Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a → Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b →
    Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal c →
    ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ A U (Kplus j C V' W' K' U - Kplus j C V W K U) ≤
        ENNReal.ofReal (4 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) + 8 * C₁ * e) *
          (e * a + b + c)) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := Kplus_lip_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₁, C₁, hε, hC₁, h''⟩ := h' A hA
  exact ⟨ε₁, C₁, hε, hC₁, fun N j hj ℓ hℓ C hC =>
    h'' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith) C hC⟩

/-- **Lipschitz continuity of `K_{j+1}` along a holomorphic family of covariances.** If
`ζ ↦ C(ζ)` is holomorphic on the polydisc `|ζ_i| < ρ₁` and `GoodCov2` holds on `|ζ_i| ≤ ρ < ρ₁`,
then for `|ζ_i|, |ζ'_i| ≤ ρ/2` and `|ζ'_i - ζ_i| ≤ δ`,
`‖K_{j+1}(C(ζ')) - K_{j+1}(C(ζ))‖ ≤ 8 B δ/ρ`, with `B` the `stepK` bound. -/
theorem Kplus_lip_cov_ts (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ (m : ℕ) (Cf : (Fin m → ℂ) → Matrix (Lam d L N) (Lam d L N) ℂ) (ρ ρ₁ : ℝ), 0 < ρ → ρ < ρ₁ →
    (∀ x y, DifferentiableOn ℂ (fun ζ => Cf ζ x y) {ζ | ∀ i, ‖ζ i‖ < ρ₁}) →
    (∀ ζ : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ) → GoodCov2 j ℓC (Cf ζ)) →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → InK2 j K →
    (∀ b, ε (V b : Alg d L N) = 0) → ∀ g k : ℝ, 0 ≤ g → g ≤ ε₀ → 0 ≤ k → k ≤ ε₀ →
    Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
    Knorm j ℓ A K ≤ ENNReal.ofReal k →
    ∀ ζ ζ' : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ / 2) → (∀ i, ‖ζ' i‖ ≤ ρ / 2) →
    ∀ δ : ℝ, 0 ≤ δ → (∀ i, ‖ζ' i - ζ i‖ ≤ δ) →
    ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ' A U (Kplus j (Cf ζ') V W K U - Kplus j (Cf ζ) V W K U) ≤
        ENNReal.ofReal (8 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k +
          C₁ * (g ^ 3 + g * k + k ^ 2)) * δ / ρ) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, hS⟩ := stepK_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, hS⟩ := hS L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, hS⟩ := hS A hA
  refine ⟨ε₀, C₁, hε₀, hC₁, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum m Cf ρ ρ₁ hρ hρ₁ hCf hgood V W K hV hW hK hV0 g k hg0 hgε hk0 hkε hVg hWg hKk
    ζ ζ' hζ hζ' δ hδ hδζ U hU
  have hA0 : 0 < A := by linarith
  have hκ : 0 ≤ C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) := by positivity
  obtain ⟨B, hBdef⟩ : ∃ B, B = C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k +
      C₁ * (g ^ 3 + g * k + k ^ 2) := ⟨_, rfl⟩
  rw [← hBdef]
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hbd : ∀ ξ : Fin m → ℂ, (∀ i, ‖ξ i‖ ≤ ρ) →
      wnorm (j + 1) ℓ' A U (Kplus j (Cf ξ) V W K U) ≤ ENNReal.ofReal B := fun ξ hξ => by
    rw [hBdef]
    exact ennreal_stepK hκ hC₁ hg0 hk0 hKk (hS N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum (Cf ξ) (hgood ξ hξ) V W K hV hW hV0 hK
      g hg0 hgε hVg hWg (hKk.trans (ENNReal.ofReal_le_ofReal hkε)) U hU)
  have hle : ∀ ξ : Fin m → ℂ, (∀ i, ‖ξ i‖ ≤ ρ / 2) → ∀ i, ‖ξ i‖ ≤ ρ := fun ξ h i =>
    (h i).trans (by linarith)
  rcases hδ.eq_or_lt with h0 | hδ0
  · -- `δ = 0`: `ζ' = ζ`
    have : ζ' = ζ := funext fun i => by
      have := hδζ i; rw [← h0] at this; exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    rw [this, sub_self]
    refine le_trans (le_of_eq ?_) zero_le
    simp [wnorm, Step.Tj_zero]
  by_cases hbig : ρ < 4 * δ
  · refine (wnorm_sub_le' _ _ _ _ _ _).trans ((add_le_add (hbd ζ' (hle ζ' hζ'))
      (hbd ζ (hle ζ hζ))).trans ?_)
    rw [← ENNReal.ofReal_add hB0 hB0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hρ]
    nlinarith only [hbig, hB0]
  · push_neg at hbig
    set R := ρ / (2 * δ) with hRdef
    have hR2 : 2 ≤ R := by rw [hRdef, le_div_iff₀ (by positivity)]; linarith
    have hRδ : R * δ = ρ / 2 := by rw [hRdef]; field_simp
    set γ : ℂ → Fin m → ℂ := fun z => ζ + z • (ζ' - ζ) with hγ
    have hγn : ∀ z : ℂ, ‖z‖ ≤ R → ∀ i, ‖γ z i‖ ≤ ρ := fun z hz i => by
      simp only [hγ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      calc ‖ζ i + z * (ζ' i - ζ i)‖ ≤ ‖ζ i‖ + ‖z‖ * ‖ζ' i - ζ i‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ ρ / 2 + R * δ := by gcongr; exact hζ i; exact hδζ i
        _ = ρ := by rw [hRδ]; ring
    -- holomorphy of `K_{j+1}` in the matrix entries
    have hhol := Kplus_holC (E := Lam d L N → Lam d L N → ℂ) (Cf := fun M => M) j
      (fun x y => (differentiable_pi.1 (differentiable_pi.1 differentiable_id x) y))
      (Vf := fun _ => V) (Wf := fun _ => W) (Kf := fun _ => K) (fun b => HolE.const _)
      (fun b => HolE.const _) (fun X => HolE.const _) (fun _ b => hV0 b) U
    have hF : ∀ Λf : Alg d L N →ₗ[ℂ] ℂ, DifferentiableOn ℂ
        (fun z => Λf (Kplus j (Cf (γ z)) V W K U : Alg d L N)) (Metric.closedBall 0 R) := by
      intro Λf
      have h1 : Differentiable ℂ (fun M : Lam d L N → Lam d L N → ℂ =>
          Λf (Kplus j M V W K U : Alg d L N)) := hhol.lin Λf
      have h2 : DifferentiableOn ℂ (fun z => (Cf (γ z) : Lam d L N → Lam d L N → ℂ))
          (Metric.closedBall 0 R) := by
        refine differentiableOn_pi.2 fun x => differentiableOn_pi.2 fun y => ?_
        refine (hCf x y).comp (f := γ) ?_ fun z hz i => ?_
        · exact (differentiable_const _).add (differentiable_id.smul_const _) |>.differentiableOn
        · have := hγn z (by simpa using hz) i
          exact lt_of_le_of_lt this hρ₁
      exact h1.comp_differentiableOn h2
    have hstep := wnorm_sub_le_of_holOn (j := j + 1) hℓ' hA0 U
      (F := fun z => Kplus j (Cf (γ z)) V W K U) (by linarith : (1 : ℝ) < R) hF hB0
      fun z hz => hbd (γ z) (hγn z hz.le)
    have e1 : γ 1 = ζ' := by simp [hγ]
    have e0 : γ 0 = ζ := by simp [hγ]
    simp only [e1, e0] at hstep
    refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ (by linarith) hρ]
    have hRm : ρ = 2 * R * δ := by rw [hRdef]; field_simp
    rw [hRm]
    have : 0 ≤ B * δ := mul_nonneg hB0 hδ
    nlinarith only [this, hR2, mul_nonneg this (by linarith : (0 : ℝ) ≤ R - 2)]

/-- **Lipschitz continuity of `K_{j+1}` along a holomorphic family of covariances.** If
`ζ ↦ C(ζ)` is holomorphic on the polydisc `|ζ_i| < ρ₁` and `GoodCov2` holds on `|ζ_i| ≤ ρ < ρ₁`,
then for `|ζ_i|, |ζ'_i| ≤ ρ/2` and `|ζ'_i - ζ_i| ≤ δ`,
`‖K_{j+1}(C(ζ')) - K_{j+1}(C(ζ))‖ ≤ 8 B δ/ρ`, with `B` the `stepK` bound. -/
theorem Kplus_lip_cov (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ (m : ℕ) (Cf : (Fin m → ℂ) → Matrix (Lam d L N) (Lam d L N) ℂ) (ρ ρ₁ : ℝ), 0 < ρ → ρ < ρ₁ →
    (∀ x y, DifferentiableOn ℂ (fun ζ => Cf ζ x y) {ζ | ∀ i, ‖ζ i‖ < ρ₁}) →
    (∀ ζ : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ) → GoodCov2 j ℓ (Cf ζ)) →
    ∀ (V W : Fam d L N) (K : Act d L N), InF j V → InF j W → InK2 j K →
    (∀ b, ε (V b : Alg d L N) = 0) → ∀ g k : ℝ, 0 ≤ g → g ≤ ε₀ → 0 ≤ k → k ≤ ε₀ →
    Fnorm j ℓ V ≤ ENNReal.ofReal g → Fnorm j ℓ W ≤ ENNReal.ofReal (g ^ 2) →
    Knorm j ℓ A K ≤ ENNReal.ofReal k →
    ∀ ζ ζ' : Fin m → ℂ, (∀ i, ‖ζ i‖ ≤ ρ / 2) → (∀ i, ‖ζ' i‖ ≤ ρ / 2) →
    ∀ δ : ℝ, 0 ≤ δ → (∀ i, ‖ζ' i - ζ i‖ ≤ δ) →
    ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ A U (Kplus j (Cf ζ') V W K U - Kplus j (Cf ζ) V W K U) ≤
        ENNReal.ofReal (8 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k +
          C₁ * (g ^ 3 + g * k + k ^ 2)) * δ / ρ) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := Kplus_lip_cov_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h'⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε, hC₁, h''⟩ := h' A hA
  exact ⟨ε₀, C₁, hε, hC₁, fun N j hj ℓ hℓ =>
    h'' N j hj ℓ ℓ ℓ hℓ hℓ hℓ (by linarith)⟩

end

end Step2
