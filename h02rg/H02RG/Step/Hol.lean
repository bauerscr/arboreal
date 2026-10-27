import Step.ContinuityAux

/-!
# Coefficient-wise holomorphy of Grassmann-valued maps and Cauchy estimates

The analogue of `Step/ContinuityAux.lean` for holomorphy.  A map `f : E → 𝒩(I)` on a complex
normed space `E` is *coefficient-wise holomorphic* (`Hol f`) if every coefficient
`e ↦ (f e)_z` is complex differentiable on all of `E` (entire).  Since every linear functional
on `𝒩(I)` is a fixed linear combination of the coefficients (`expand`), this class is closed
under fixed linear maps, products, sums, linear combinations with holomorphic scalars, `θ`,
the inclusion, `𝔼_C`, and the exponential of even elements with vanishing constant term.

For `f : ℂ → 𝒩(I)` we define the coefficient-wise derivative `derivN f t`
(`coeff_derivN : (derivN f t)_z = d/dt (f t)_z`), and its even version `derivE`.

Finally we prove the one-variable Cauchy estimates used for the norm bounds:
`norm_taylor_le` (for an entire `φ : ℂ → ℂ` bounded by `M` on `|ζ| = R > 1`,
`|φ(1) - φ(0)| ≤ M/(R-1)` and `|φ(1) - φ(0) - φ'(0)| ≤ M/(R(R-1))`) and
`norm_deriv_le_of_sphere` (`|φ'(0)| ≤ M/R`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD Complex Metric

/-! ### Cauchy estimates for scalar entire functions -/

theorem norm_cauchyPowerSeries_apply_le {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {R M : ℝ}
    (hR : 0 < R) (hM : ∀ ζ : ℂ, ‖ζ‖ = R → ‖φ ζ‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries φ 0 R n (fun _ => 1)‖ ≤ M * R⁻¹ ^ n := by
  refine ((cauchyPowerSeries φ 0 R n).le_opNorm _).trans ?_
  simp only [norm_one, Finset.prod_const_one, mul_one]
  refine (norm_cauchyPowerSeries_le φ 0 R n).trans ?_
  rw [abs_of_pos hR]
  gcongr
  have hc : Continuous fun θ : ℝ => ‖φ (circleMap 0 R θ)‖ :=
    (hφ.continuous.comp (continuous_circleMap 0 R)).norm
  have h1 : ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖φ (circleMap 0 R θ)‖ ≤
      ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, M := by
    refine intervalIntegral.integral_mono_on (by positivity) (hc.intervalIntegrable _ _)
      intervalIntegrable_const fun θ _ => hM _ ?_
    rw [norm_circleMap_zero, abs_of_pos hR]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
  have hπ : 0 < 2 * Real.pi := by positivity
  calc (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖φ (circleMap 0 R θ)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) := by gcongr
    _ = M := by field_simp

/-- **Cauchy estimates for Taylor remainders.** If `φ` is entire and `‖φ‖ ≤ M` on the circle of
radius `R > 1`, then `‖φ 1 - φ 0‖ ≤ M/(R-1)` and `‖φ 1 - φ 0 - φ'(0)‖ ≤ M/(R(R-1))`. -/
theorem norm_taylor_le {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {R M : ℝ} (hR : 1 < R)
    (hM : ∀ ζ : ℂ, ‖ζ‖ = R → ‖φ ζ‖ ≤ M) :
    ‖φ 1 - φ 0‖ ≤ M / (R - 1) ∧ ‖φ 1 - φ 0 - deriv φ 0‖ ≤ M / (R * (R - 1)) := by
  have hR0 : 0 < R := by linarith
  set R' : NNReal := ⟨R, hR0.le⟩
  have hR' : 0 < R' := hR0
  have hp := hφ.hasFPowerSeriesOnBall 0 hR'
  set p := cauchyPowerSeries φ 0 (R' : ℝ)
  have hs : HasSum (fun n => p n (fun _ => 1)) (φ 1) := by
    simpa using hp.hasSum (y := 1) (by simp)
  have h0 : p 0 (fun _ => 1) = φ 0 := hp.hasFPowerSeriesAt.coeff_zero _
  have h1 : deriv φ 0 = p 1 (fun _ => 1) := hp.hasFPowerSeriesAt.deriv
  have hb : ∀ n, ‖p n (fun _ => 1)‖ ≤ M * R⁻¹ ^ n :=
    norm_cauchyPowerSeries_apply_le hφ hR0 hM
  have hr0 : 0 ≤ R⁻¹ := by positivity
  have hr1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hg : ∀ k : ℕ, HasSum (fun n => M * R⁻¹ ^ (n + k)) (M * R⁻¹ ^ k * (1 - R⁻¹)⁻¹) :=
    fun k => by
      have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (M * R⁻¹ ^ k)
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using this
  have hne : R - 1 ≠ 0 := by linarith
  constructor
  · have hs1 := (hasSum_nat_add_iff' 1).2 hs
    simp only [Finset.sum_range_one, h0] at hs1
    refine (hs1.norm_le_of_bounded (hg 1) fun n => hb _).trans (le_of_eq ?_)
    field_simp
  · have hs2 := (hasSum_nat_add_iff' 2).2 hs
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, ← h1] at hs2
    rw [sub_sub]
    refine (hs2.norm_le_of_bounded (hg 2) fun n => hb _).trans (le_of_eq ?_)
    field_simp

/-- Cauchy's estimate for the first derivative of an entire function. -/
theorem norm_deriv_le_of_sphere {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {R M : ℝ} (hR : 0 < R)
    (hM : ∀ ζ : ℂ, ‖ζ‖ = R → ‖φ ζ‖ ≤ M) : ‖deriv φ 0‖ ≤ M / R :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hφ.diffContOnCl fun ζ hζ =>
    hM ζ (by simpa using hζ)

/-! ### Coefficient-wise holomorphy -/

section Hol

variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Coefficient-wise holomorphy (on all of `E`). -/
def Hol (f : E → Grassmann.N I) : Prop :=
  ∀ n (z : Fin n → Sf I), Differentiable ℂ (fun e => coeff (f e) z)

theorem Hol.lin {f : E → Grassmann.N I} (hf : Hol f) (ℓ : Grassmann.N I →ₗ[ℂ] ℂ) :
    Differentiable ℂ (fun e => ℓ (f e)) := by
  have h : (fun e => ℓ (f e)) = fun e => ∑ n ∈ range (Nf I + 1), ∑ z : Fin n → Sf I,
      ((n.factorial : ℂ)⁻¹ * coeff (f e) z) • ℓ (psiPow z) := funext fun e => expand ℓ (f e)
  rw [h]
  refine Differentiable.fun_sum fun n _ => Differentiable.fun_sum fun z _ => ?_
  simp only [smul_eq_mul]
  exact ((differentiable_const _).mul (hf n z)).mul (differentiable_const _)

theorem Hol.bilin {f : E → Grassmann.N I} {g : E → Grassmann.N J} (hf : Hol f) (hg : Hol g)
    (B : Grassmann.N I →ₗ[ℂ] Grassmann.N J →ₗ[ℂ] ℂ) :
    Differentiable ℂ (fun e => B (f e) (g e)) := by
  have h : (fun e => B (f e) (g e)) = fun e => ∑ n ∈ range (Nf I + 1), ∑ z : Fin n → Sf I,
      ((n.factorial : ℂ)⁻¹ * coeff (f e) z) * B (psiPow z) (g e) := funext fun e => by
    rw [expand B (f e)]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [h]
  refine Differentiable.fun_sum fun n _ => Differentiable.fun_sum fun z _ => ?_
  exact ((differentiable_const _).mul (hf n z)).mul (hg.lin _)

theorem Hol.map {f : E → Grassmann.N I} (hf : Hol f) (T : Grassmann.N I →ₗ[ℂ] Grassmann.N J) :
    Hol (fun e => T (f e)) := fun _ z => hf.lin ((coeffL z).comp T)

theorem Hol.const (F : Grassmann.N I) : Hol (fun _ : E => F) := fun _ _ => differentiable_const _

theorem Hol.mul {f g : E → Grassmann.N I} (hf : Hol f) (hg : Hol g) :
    Hol (fun e => f e * g e) := fun _ z =>
  hf.bilin hg ((LinearMap.mul ℂ (Grassmann.N I)).compr₂ (coeffL z))

theorem Hol.add {f g : E → Grassmann.N I} (hf : Hol f) (hg : Hol g) :
    Hol (fun e => f e + g e) := fun n z => by
  simp only [coeff_add]; exact (hf n z).add (hg n z)

theorem Hol.smul {c : E → ℂ} {f : E → Grassmann.N I} (hc : Differentiable ℂ c) (hf : Hol f) :
    Hol (fun e => c e • f e) := fun n z => by
  simp only [coeff_smul]; exact hc.mul (hf n z)

theorem Hol.neg {f : E → Grassmann.N I} (hf : Hol f) : Hol (fun e => -f e) := by
  have := hf.smul (c := fun _ => -1) (differentiable_const _)
  simpa using this

theorem Hol.sub {f g : E → Grassmann.N I} (hf : Hol f) (hg : Hol g) :
    Hol (fun e => f e - g e) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem Hol.sum {ι : Type*} (s : Finset ι) {f : ι → E → Grassmann.N I}
    (hf : ∀ i ∈ s, Hol (f i)) : Hol (fun e => ∑ i ∈ s, f i e) := fun n z => by
  simp only [coeff_sum]; exact Differentiable.fun_sum fun i hi => hf i hi n z

theorem Hol.pow {f : E → Grassmann.N I} (hf : Hol f) (k : ℕ) : Hol (fun e => f e ^ k) := by
  induction k with
  | zero => simpa using Hol.const (E := E) (1 : Grassmann.N I)
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem Hol.congr {f g : E → Grassmann.N I} (hf : Hol f) (h : ∀ e, g e = f e) : Hol g := by
  have : g = f := funext h
  rwa [this]

theorem Hol.comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → Grassmann.N I}
    (hf : Hol f) {c : F → E} (hc : Differentiable ℂ c) : Hol (fun x => f (c x)) :=
  fun n z => (hf n z).comp hc

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem Hol.EC (C : Matrix Λ Λ ℝ) {f : E → Grassmann.N (Λ ⊕ Λ)} (hf : Hol f) :
    Hol (fun e => Grassmann.EC C (f e)) := hf.map _

/-! ### Even elements -/

/-- Coefficient-wise holomorphy of maps into the even subalgebra. -/
def HolE (f : E → EvR I) : Prop := Hol (fun e => (f e : Grassmann.N I))

theorem HolE.const (F : EvR I) : HolE (fun _ : E => F) := Hol.const _

theorem HolE.mul {f g : E → EvR I} (hf : HolE f) (hg : HolE g) : HolE (fun e => f e * g e) :=
  Hol.mul hf hg

theorem HolE.add {f g : E → EvR I} (hf : HolE f) (hg : HolE g) : HolE (fun e => f e + g e) :=
  Hol.add hf hg

theorem HolE.sub {f g : E → EvR I} (hf : HolE f) (hg : HolE g) : HolE (fun e => f e - g e) :=
  Hol.sub hf hg

theorem HolE.neg {f : E → EvR I} (hf : HolE f) : HolE (fun e => -f e) := Hol.neg hf

theorem HolE.smul {c : E → ℂ} {f : E → EvR I} (hc : Differentiable ℂ c) (hf : HolE f) :
    HolE (fun e => c e • f e) := Hol.smul hc hf

theorem HolE.sum {ι : Type*} (s : Finset ι) {f : ι → E → EvR I} (hf : ∀ i ∈ s, HolE (f i)) :
    HolE (fun e => ∑ i ∈ s, f i e) := by
  unfold HolE
  simp only [AddSubmonoidClass.coe_finsetSum]
  exact Hol.sum s hf

theorem HolE.prod {ι : Type*} (s : Finset ι) {f : ι → E → EvR I} (hf : ∀ i ∈ s, HolE (f i)) :
    HolE (fun e => ∏ i ∈ s, f i e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HolE.const (E := E) (1 : EvR I)
  | insert a s ha ih =>
    simp only [prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem HolE.map {f : E → EvR I} (hf : HolE f) (T : EvR I →ₗ[ℂ] EvR J) :
    HolE (fun e => T (f e)) := by
  -- the coefficients of `T (f e)` are linear functionals of `f e ∈ Ev I`; extend them to `𝒩(I)`
  intro n z
  set ℓ : EvR I →ₗ[ℂ] ℂ := (coeffL z).comp ((Ev J).val.toLinearMap.comp T)
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Grassmann.N I →ₗ[ℂ] ℂ, ∀ x : EvR I, ℓ' x = ℓ x := by
    obtain ⟨ℓ', h⟩ := LinearMap.exists_extend (K := ℂ) (V := Grassmann.N I)
      (p := Subalgebra.toSubmodule (Ev I)) ℓ
    exact ⟨ℓ', fun x => LinearMap.congr_fun h x⟩
  have h : (fun e => coeff ((T (f e) : EvR J) : Grassmann.N J) z) = fun e => ℓ' (f e) :=
    funext fun e => by rw [hℓ']; rfl
  show Differentiable ℂ (fun e => coeff ((T (f e) : EvR J) : Grassmann.N J) z)
  rw [h]
  exact hf.lin ℓ'

theorem HolE.thetaE {f : E → EvR Λ} (hf : HolE f) : HolE (fun e => thetaE (f e)) :=
  Hol.map hf theta.toLinearMap

theorem HolE.inclE {f : E → EvR Λ} (hf : HolE f) : HolE (fun e => inclE (f e)) :=
  Hol.map hf incl.toLinearMap

theorem HolE.ECE (C : Matrix Λ Λ ℝ) {f : E → EvR (Λ ⊕ Λ)} (hf : HolE f) :
    HolE (fun e => ECE C (f e)) :=
  Hol.EC C hf

theorem HolE.gexp {f : E → EvR I} (hf : HolE f) (h0 : ∀ e, ε (f e : Grassmann.N I) = 0) :
    HolE (fun e => gexp (f e)) := by
  refine Hol.congr (f := fun e => ∑ i ∈ range (Nf I + 1),
    ((i.factorial : ℂ)⁻¹) • (f e : Grassmann.N I) ^ i) ?_ fun e => ?_
  · exact Hol.sum _ fun i _ => Hol.smul (differentiable_const _) (Hol.pow hf i)
  · exact coe_gexp (pow_eq_zero_of_ε' (h0 e) (Nat.lt_succ_self _))

theorem HolE.comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → EvR I}
    (hf : HolE f) {c : F → E} (hc : Differentiable ℂ c) : HolE (fun x => f (c x)) :=
  Hol.comp hf hc

end Hol

/-! ### The coefficient-wise derivative -/

section Deriv

variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]

/-- The coefficient-wise derivative of `f : ℂ → 𝒩(I)` at `t`, rebuilt from its coefficients
via `e:Fzsum`. -/
def derivN (f : ℂ → Grassmann.N I) (t : ℂ) : Grassmann.N I :=
  ∑ n ∈ range (Nf I + 1), ∑ z : Fin n → Sf I,
    ((n.factorial : ℂ)⁻¹ * deriv (fun s => coeff (f s) z) t) • psiPow z

theorem coeff_derivN (f : ℂ → Grassmann.N I) (t : ℂ) {n : ℕ} (z : Fin n → Sf I) :
    coeff (derivN f t) z = deriv (fun s => coeff (f s) z) t := by
  by_cases hn : n ≤ Nf I
  · refine coeff_eq_of_antisymm (fun _ w => deriv (fun s => coeff (f s) w) t) ?_ _ hn z
    intro m w σ
    simp only [coeff_perm]
    rw [deriv_const_mul_field']
  · rw [not_le] at hn
    rw [coeff_eq_zero_of_lt _ _ hn]
    have : (fun s => coeff (f s) z) = fun _ => (0 : ℂ) :=
      funext fun s => coeff_eq_zero_of_lt _ _ hn
    rw [this, deriv_const]

/-- Linear functionals commute with the coefficient-wise derivative. -/
theorem lin_derivN {f : ℂ → Grassmann.N I} (hf : Hol f) (ℓ : Grassmann.N I →ₗ[ℂ] ℂ) (t : ℂ) :
    ℓ (derivN f t) = deriv (fun s => ℓ (f s)) t := by
  have h : (fun s => ℓ (f s)) = fun s => ∑ n ∈ range (Nf I + 1), ∑ z : Fin n → Sf I,
      ((n.factorial : ℂ)⁻¹ * coeff (f s) z) * ℓ (psiPow z) := funext fun s => by
    rw [expand ℓ (f s)]; simp only [smul_eq_mul]
  rw [h, expand ℓ (derivN f t)]
  simp only [smul_eq_mul, coeff_derivN]
  refine (HasDerivAt.fun_sum fun n _ => HasDerivAt.fun_sum fun z _ =>
    ((((hf n z) t).hasDerivAt).const_mul _).mul_const _).deriv.symm

theorem derivN_map {f : ℂ → Grassmann.N I} (hf : Hol f) (T : Grassmann.N I →ₗ[ℂ] Grassmann.N J)
    (t : ℂ) : derivN (fun s => T (f s)) t = T (derivN f t) := by
  refine ext_coeff fun n z => ?_
  rw [coeff_derivN, ← coeffL_apply z (T _), ← LinearMap.comp_apply, lin_derivN hf]
  rfl

theorem pair_derivN {f : ℂ → Grassmann.N I} (hf : Hol f) (g : TestFn I) (t : ℂ) :
    pair (derivN f t) g = deriv (fun s => pair (f s) g) t :=
  lin_derivN hf (pairL g) t

theorem derivN_mem_Ev {f : ℂ → EvR I} (hf : HolE f) (t : ℂ) :
    derivN (fun s => (f s : Grassmann.N I)) t ∈ Ev I := by
  refine mem_Ev.2 ?_
  have h := derivN_map hf (inv' : Grassmann.N I →ₐ[ℂ] Grassmann.N I).toLinearMap t
  simp only [AlgHom.toLinearMap_apply] at h
  rw [← h]
  congr 1
  funext s
  exact mem_Ev.1 (f s).2

open Classical in
/-- The derivative of a coefficient-wise holomorphic map `ℂ → Ev(I)` (and `0` otherwise). -/
def derivE (f : ℂ → EvR I) (t : ℂ) : EvR I :=
  if hf : HolE f then ⟨derivN (fun s => (f s : Grassmann.N I)) t, derivN_mem_Ev hf t⟩ else 0

theorem coe_derivE {f : ℂ → EvR I} (hf : HolE f) (t : ℂ) :
    (derivE f t : Grassmann.N I) = derivN (fun s => (f s : Grassmann.N I)) t := by
  simp [derivE, hf]

theorem pair_derivE {f : ℂ → EvR I} (hf : HolE f) (g : TestFn I) (t : ℂ) :
    pair (derivE f t : Grassmann.N I) g = deriv (fun s => pair (f s : Grassmann.N I) g) t := by
  rw [coe_derivE hf, pair_derivN hf]

theorem coeff_derivE {f : ℂ → EvR I} (hf : HolE f) (t : ℂ) {n : ℕ} (z : Fin n → Sf I) :
    coeff (derivE f t : Grassmann.N I) z = deriv (fun s => coeff (f s : Grassmann.N I) z) t := by
  rw [coe_derivE hf, coeff_derivN]

end Deriv

end

end Step
