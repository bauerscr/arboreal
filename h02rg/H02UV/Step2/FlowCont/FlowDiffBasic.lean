import Step2.FlowCont.FlowCont
import Flow2.DiffHist

/-!
# Differentiability of the RG flow data: generic tools (`thm:flow`(iii))

Real differentiability (in a real parameter `p ∈ P`) of the pieces of one RG step:
* `diffAt_clampDisk`: the radial clamp is the identity near a point strictly inside the disc, so
  it preserves differentiability there;
* `diffAt_csq`: the principal square root is holomorphic on the slit plane;
* `diffAt_of_coords`: a map into a finite-dimensional complex space is differentiable iff its
  coordinates for a separating family of linear functionals are (a finite separating subfamily
  exists); hence `BSp.diffAt_iff`, `ASp.diffAt_iff` (coefficient-wise differentiability `DF`, `DA`);
* `CovDiff`, `covDiff_of_small`, `rawCov_diff`: `Γ^int_{j+1}(p)` is holomorphic in
  `(ζ_0, …, ζ_j)` on the polydisc `|ζ_i| < ζ̄` (`DressedFRD.thm_main_hol`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Filter Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P}

/-! ### Scalar pieces -/

theorem diffAt_clampDisk {r : ℝ} {a : P → ℂ} (ha : DifferentiableAt ℝ a p₀) (hr : ‖a p₀‖ < r) :
    DifferentiableAt ℝ (fun p => clampDisk r (a p)) p₀ := by
  have hev : (fun p => clampDisk r (a p)) =ᶠ[𝓝 p₀] a := by
    filter_upwards [ha.continuousAt.norm.eventually_lt continuousAt_const hr] with p hp
    exact clampDisk_of_le hp.le
  exact ha.congr_of_eventuallyEq hev

theorem diffAt_csq {w : P → ℂ} (hw : DifferentiableAt ℝ w p₀) (h : w p₀ ∈ Complex.slitPlane) :
    DifferentiableAt ℝ (fun p => csq (w p)) p₀ := by
  unfold csq
  exact ((differentiableAt_id.cpow_const (c := (2⁻¹ : ℂ)) h).restrictScalars ℝ).comp p₀ hw

/-! ### Finite-dimensional targets -/

theorem diffAt_of_coords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {I : Type*} (c : I → E →ₗ[ℂ] ℂ)
    (hc : ∀ v : E, (∀ i, c i v = 0) → v = 0) {f : P → E}
    (hf : ∀ i, DifferentiableAt ℝ (fun p => c i (f p)) p₀) : DifferentiableAt ℝ f p₀ := by
  classical
  have key : ∀ n : ℕ, ∀ s : Finset I,
      Module.finrank ℂ (LinearMap.ker (LinearMap.pi fun i : s => c i)) ≤ n →
      ∃ s' : Finset I, LinearMap.ker (LinearMap.pi fun i : s' => c i) = ⊥ := by
    intro n
    induction n with
    | zero => intro s hs; exact ⟨s, Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hs)⟩
    | succ n ih =>
      intro s hs
      by_cases h0 : LinearMap.ker (LinearMap.pi fun i : s => c i) = ⊥
      · exact ⟨s, h0⟩
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      obtain ⟨i, hi⟩ : ∃ i, c i v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hv0 (hc v hcon)
      refine ih (insert i s) ?_
      have hlt : LinearMap.ker (LinearMap.pi fun k : (insert i s : Finset I) => c k) <
          LinearMap.ker (LinearMap.pi fun k : s => c k) := by
        refine lt_of_le_of_ne (fun w hw => ?_) (fun heq => ?_)
        · rw [LinearMap.mem_ker] at hw ⊢
          funext k
          have := congrFun hw ⟨k, Finset.mem_insert_of_mem k.2⟩
          simpa using this
        · have h1 : v ∈ LinearMap.ker (LinearMap.pi fun k : (insert i s : Finset I) => c k) :=
            heq ▸ hv
          rw [LinearMap.mem_ker] at h1
          have := congrFun h1 ⟨i, Finset.mem_insert_self i s⟩
          exact hi (by simpa using this)
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
  obtain ⟨s, hs⟩ := key _ ∅ (Submodule.finrank_le _)
  obtain ⟨ψ, hψ⟩ := (LinearMap.pi fun i : s => c i).exists_leftInverse_of_injective hs
  let ψL : (s → ℂ) →L[ℂ] E := ⟨ψ, LinearMap.continuous_of_finiteDimensional ψ⟩
  have hΦ : DifferentiableAt ℝ (fun p => (LinearMap.pi fun i : s => c i) (f p)) p₀ :=
    differentiableAt_pi.2 fun i => hf i
  have e : f = fun p => (ψL.restrictScalars ℝ) ((LinearMap.pi fun i : s => c i) (f p)) :=
    funext fun p => by
      show f p = ψ ((LinearMap.pi fun i : s => c i) (f p))
      rw [← LinearMap.comp_apply, hψ, LinearMap.id_apply]
  rw [e]
  exact (ψL.restrictScalars ℝ).differentiableAt.comp p₀ hΦ

/-- A complex-linear functional on a finite-dimensional space preserves differentiability. -/
theorem diffAt_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (c : E →ₗ[ℂ] ℂ) {f : P → E} (hf : DifferentiableAt ℝ f p₀) :
    DifferentiableAt ℝ (fun p => c (f p)) p₀ :=
  ((LinearMap.toContinuousLinearMap c).restrictScalars ℝ).differentiableAt.comp p₀ hf

variable {d L N : ℕ} [NeZero L]

/-- Coefficient-wise differentiability of a map into block families. -/
def DF (f : P → Fam d L N) (p₀ : P) : Prop :=
  ∀ b n (z : Fin n → Sf (Lam d L N)),
    DifferentiableAt ℝ (fun p => coeff ((f p b : EvR _) : Alg d L N) z) p₀

/-- Coefficient-wise differentiability of a map into activities. -/
def DA (f : P → Act d L N) (p₀ : P) : Prop :=
  ∀ X n (z : Fin n → Sf (Lam d L N)),
    DifferentiableAt ℝ (fun p => coeff ((f p X : EvR _) : Alg d L N) z) p₀

variable {j : ℕ} {ℓ A : ℝ}

theorem BSp.diffAt_iff [Fact (0 < ℓ)] (f : P → BSp d L N j ℓ) :
    DifferentiableAt ℝ f p₀ ↔ DF (fun p => (f p).toFam) p₀ := by
  let c : ((Fin d → ℕ) × (Σ n : ℕ, Fin n → Sf (Lam d L N))) → BSp d L N j ℓ →ₗ[ℂ] ℂ :=
    fun i => (LinearMap.proj i).comp (famCoefL.comp BSp.toFam)
  refine ⟨fun h b n z => diffAt_linear (c (b, ⟨n, z⟩)) h, fun h => ?_⟩
  refine diffAt_of_coords c (fun v hv => ?_) (fun i => h i.1 i.2.1 i.2.2)
  have : famCoefL (BSp.toFam v) = famCoefL (BSp.toFam (0 : BSp d L N j ℓ)) := by
    funext i; rw [map_zero, map_zero]; exact hv i
  exact BSp.toFam_injective (famCoefL_injective this)

theorem ASp.diffAt_iff [Fact (0 < ℓ)] [Fact (0 < A)] (f : P → ASp d L N j ℓ A) :
    DifferentiableAt ℝ f p₀ ↔ DA (fun p => (f p).toAct) p₀ := by
  let c : (Finset (Lam d L N) × (Σ n : ℕ, Fin n → Sf (Lam d L N))) → ASp d L N j ℓ A →ₗ[ℂ] ℂ :=
    fun i => (LinearMap.proj i).comp (actCoefL.comp ASp.toAct)
  refine ⟨fun h b n z => diffAt_linear (c (b, ⟨n, z⟩)) h, fun h => ?_⟩
  refine diffAt_of_coords c (fun v hv => ?_) (fun i => h i.1 i.2.1 i.2.2)
  have : actCoefL (ASp.toAct v) = actCoefL (ASp.toAct (0 : ASp d L N j ℓ A)) := by
    funext i; rw [map_zero, map_zero]; exact hv i
  exact ASp.toAct_injective (actCoefL_injective this)

omit [NeZero L] in
/-- Holomorphic coefficients along a differentiable family. -/
theorem diffAt_of_hol {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {h : E → EvR (Lam d L N)}
    (hh : HolE h) {φ : P → E} (hφ : DifferentiableAt ℝ φ p₀) (n : ℕ) (z : Fin n → Sf (Lam d L N)) :
    DifferentiableAt ℝ (fun p => coeff ((h (φ p) : EvR _) : Alg d L N) z) p₀ :=
  (((hh n z) (φ p₀)).restrictScalars ℝ).comp p₀ hφ

theorem diffAt_of_diffC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {h : E → ℂ}
    (hh : Differentiable ℂ h) {φ : P → E} (hφ : DifferentiableAt ℝ φ p₀) :
    DifferentiableAt ℝ (fun p => h (φ p)) p₀ :=
  ((hh (φ p₀)).restrictScalars ℝ).comp p₀ hφ

/-! ### The covariance -/

/-- **The differentiability hypothesis on the dressed covariance**: for each momentum `p`,
`Γ^int_{j+1}(p)` is holomorphic in `(ζ_0, …, ζ_j)` at every point of the closed polydisc of
radius `ρ`. -/
def CovDiff (R : RGPar d L N) (j : ℕ) : Prop :=
  ∀ z₀ : Fin (j + 1) → ℂ, (∀ i, ‖z₀ i‖ ≤ R.ρ) → ∀ m : Torus d (L ^ N),
    DifferentiableAt ℂ (fun z : Fin (j + 1) → ℂ => ((D0 R).Dz z).Gint j m) z₀

/-- **`CovCont` and `CovDiff` for small `ρ`** (`thm:main`(ii)). -/
theorem covDiff_of_small (P : PtFamily) (hd : 2 ≤ d) (hL : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∀ (N : ℕ) (R : RGPar d L N), R.P = P → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ < ζbar → ∀ j, j < N →
        CovCont R j ∧ CovDiff R j := by
  obtain ⟨cS, hcS, hS⟩ := DressedFRD.frd_stdFull P (d := d) hd hL (q := 2) (M := d + 3)
    (by omega)
  obtain ⟨ζbar, hζ, -, K, hK⟩ := DressedFRD.thm_main_hol (d := d) hd le_rfl hL (M := d + 3)
    (by omega) hcS
  refine ⟨ζbar, hζ, fun N R hP hN hm hm' hρ j hj => ?_⟩
  subst hP
  have hS' := hS (L ^ N) N R.msq hN rfl hm
  have hopen : IsOpen {z : Fin (j + 1) → ℂ | ∀ i, ‖z i‖ < ζbar} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  have hD : CovDiff R j := fun z₀ hz₀ m =>
    ((hK (L ^ N) (D0 R) rfl rfl hS' hm').2 j hj m).1.differentiableAt
      (hopen.mem_nhds fun i => (hz₀ i).trans_lt hρ)
  exact ⟨fun z₀ hz₀ m => (hD z₀ hz₀ m).continuousAt, hD⟩

/-- **The covariance is differentiable along differentiable admissible histories.** -/
theorem rawCov_diff {R : RGPar d L N} {j : ℕ} (hc : CovDiff R j) {ζ : P → ℕ → ℂ}
    (hζ : ∀ i ≤ j, DifferentiableAt ℝ (fun p => ζ p i) p₀) (hb : ∀ i, ‖ζ p₀ i‖ ≤ R.ρ)
    (h0 : ∀ p i, j < i → ζ p i = 0) (x y : Lam d L N) :
    DifferentiableAt ℝ (fun p => rawCov R j (ζ p) x y) p₀ := by
  let zz : P → Fin (j + 1) → ℂ := fun p i => ζ p i
  have hzz : DifferentiableAt ℝ zz p₀ :=
    differentiableAt_pi.2 fun i => hζ i (Nat.lt_succ_iff.1 i.2)
  have e : ∀ p, rawCov R j (ζ p) x y =
      DressedFRD.kern (((D0 R).Dz (zz p)).Gint j) (x - y) := by
    intro p
    have : ζ p = DressedFRD.Data.ext (zz p) := by
      funext i
      unfold DressedFRD.Data.ext
      split_ifs with hi
      · rfl
      · exact h0 p i (by omega)
    rw [rawCov, this]
    rfl
  simp only [e]
  have hG : ∀ m, DifferentiableAt ℝ (fun p => ((D0 R).Dz (zz p)).Gint j m) p₀ := fun m =>
    ((hc (zz p₀) (fun i => hb i) m).restrictScalars ℝ).comp p₀ hzz
  unfold DressedFRD.kern
  exact (differentiableAt_const _).mul
    (DifferentiableAt.fun_sum fun m _ => (hG m).mul (differentiableAt_const _))

end

end Step2
