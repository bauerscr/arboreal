import Mathlib

/-!
# An abstract stable manifold theorem for non-autonomous dynamical systems

We consider the non-autonomous dynamical system
```
v_{j+1} = E v_j + B_j w_j,
w_{j+1} = D_j w_j + g_j (v_j, w_j),
```
where `v_j ∈ V`, `w_j ∈ W j` (complex Banach spaces), `E : V ≃L[ℂ] V` with `‖E⁻¹‖ ≤ 1`
(the "neutral/expanding" directions), `‖B_j‖ ≤ β`, `‖D_j‖ ≤ δ` (the contracting directions),
and `g_j` is a nonlinearity vanishing to second order:
`g_j 0 = 0` and `‖g_j x - g_j y‖ ≤ γ · max ‖x‖ ‖y‖ · ‖x - y‖` on the `r`-ball.
(Norms on products are maximum norms.)

This is the dynamical system of the renormalisation group flow in Section `sec:flow` of
`h02rg.tex`, where the paper invokes Theorem 2.16 of Brydges' lecture notes (MR2523458).
We formulate and prove our own version.

## Main results

Fix `δ < θ < 1` and a radius `R` with `R ≤ r` and `2 γ R c ≤ θ - δ`, where
`c = max 1 (β / (1 - θ))` (this is `Flow.Admissible β δ γ r θ R`), and put
`ρ = (θ - δ) R / (2 θ c)` (`Flow.rho`). For `‖w₀‖ ≤ ρ`:

* `Flow.System.Bounds.existsUnique_stable`: there is a unique `v₀` (namely
  `S.stableMap w₀`) such that the orbit of `(v₀, w₀)` stays in the `R`-ball and decays
  like `θ^j`.
* `Flow.System.Bounds.norm_orbit_stableMap_le`: the orbit of `(S.stableMap w₀, w₀)` satisfies
  `‖v_j‖ + ‖w_j‖ ≤ (1 + β/(1-θ)) (2θ/(θ-δ)) θ^j ‖w₀‖`.
* `Flow.System.Bounds.norm_stableMap_sub_le`: `w₀ ↦ S.stableMap w₀` is Lipschitz with constant
  `β/(1-θ) · 2θ/(θ-δ)`.
* `Flow.continuous_stableMap`: continuity of the stable map with respect to a parameter on which
  the system depends (strongly) continuously, with uniform bounds.
* `Flow.System.Bounds.analyticAlongCurves_stableMap`: if the `g_j` are analytic along complex
  curves (the notion of analyticity of `h02rg.tex`), then so is `w₀ ↦ S.stableMap w₀`.
* `Flow.System.Bounds.differentiableOn_stableMap_smul`: consequently `λ ↦ S.stableMap (λ • ŵ)` is
  holomorphic on a disc, with an explicit bound on its derivative.

## Method

The orbit condition is rewritten as a fixed point problem for the sequence `(w_j)` alone:
`v_j = -∑_{k ≥ 0} E^{-(k+1)} B_{j+k} w_{j+k}` (`Flow.System.vOf`) and
`w_0 = w₀`, `w_{j+1} = D_j w_j + g_j(v_j, w_j)` (`Flow.System.F`). This map is a contraction
in the weighted sup norm `sup_j θ^{-j} ‖w_j‖`. Rather than building the weighted Banach space,
we run the Picard iteration (`Flow.System.picard`) by hand, and define the fixed point
(`Flow.System.fixedSeq`) as the componentwise limit. The estimates are uniform, so the
Picard iterates converge uniformly in parameters; this gives continuity and holomorphy.
-/

open Filter Topology Metric Set Finset

noncomputable section

namespace Flow

/-! ### Constants -/

/-- The constant `c(β, θ) = max 1 (β / (1 - θ))`; `β/(1-θ)` bounds the linear map
`(w_j) ↦ (v_j)` in the weighted norm. -/
def cst (β θ : ℝ) : ℝ := max 1 (β / (1 - θ))

/-- The contraction constant `K = (δ + γ R c) / θ` of the fixed point map. -/
def contr (β δ γ θ R : ℝ) : ℝ := (δ + γ * R * cst β θ) / θ

/-- The radius `ρ = (θ - δ) R / (2 θ c)` of initial data `w₀` for which the stable manifold
theorem is proved. -/
def rho (β δ θ R : ℝ) : ℝ := (θ - δ) * R / (2 * θ * cst β θ)

/-- Admissibility conditions on the constants: `0 ≤ β, δ, γ`, `δ < θ < 1`, `0 ≤ R ≤ r` and
`2 γ R c ≤ θ - δ`. Here `θ` is the decay rate and `R` is the (unweighted) radius in which the
orbit lives. -/
structure Admissible (β δ γ r θ R : ℝ) : Prop where
  beta_nonneg : 0 ≤ β
  delta_nonneg : 0 ≤ δ
  gamma_nonneg : 0 ≤ γ
  delta_lt : δ < θ
  theta_lt : θ < 1
  R_nonneg : 0 ≤ R
  R_le : R ≤ r
  small : 2 * γ * R * cst β θ ≤ θ - δ

namespace Admissible

variable {β δ γ r θ R : ℝ} (hc : Admissible β δ γ r θ R)
include hc

lemma theta_pos : 0 < θ := lt_of_le_of_lt hc.delta_nonneg hc.delta_lt

lemma one_le_cst : 1 ≤ cst β θ := le_max_left _ _

lemma cst_pos : 0 < cst β θ := lt_of_lt_of_le one_pos hc.one_le_cst

lemma kappa_le_cst : β / (1 - θ) ≤ cst β θ := le_max_right _ _

lemma kappa_nonneg : 0 ≤ β / (1 - θ) :=
  div_nonneg hc.beta_nonneg (sub_nonneg.2 hc.theta_lt.le)

lemma contr_nonneg : 0 ≤ contr β δ γ θ R :=
  div_nonneg (add_nonneg hc.delta_nonneg
    (mul_nonneg (mul_nonneg hc.gamma_nonneg hc.R_nonneg) hc.cst_pos.le)) hc.theta_pos.le

lemma contr_mul : contr β δ γ θ R * θ = δ + γ * R * cst β θ :=
  div_mul_cancel₀ _ hc.theta_pos.ne'

lemma le_one_sub_contr : (θ - δ) / (2 * θ) ≤ 1 - contr β δ γ θ R := by
  have hθ := hc.theta_pos
  rw [div_le_iff₀ (by positivity)]
  have e : (1 - contr β δ γ θ R) * (2 * θ) = 2 * θ - 2 * (contr β δ γ θ R * θ) := by ring
  rw [e, hc.contr_mul]
  linarith [hc.small]

lemma one_sub_contr_pos : 0 < 1 - contr β δ γ θ R :=
  lt_of_lt_of_le (div_pos (sub_pos.2 hc.delta_lt) (by linarith [hc.theta_pos]))
    hc.le_one_sub_contr

lemma contr_lt_one : contr β δ γ θ R < 1 := by linarith [hc.one_sub_contr_pos]

lemma inv_one_sub_contr_le : 1 / (1 - contr β δ γ θ R) ≤ 2 * θ / (θ - δ) := by
  have h := one_div_le_one_div_of_le
    (div_pos (sub_pos.2 hc.delta_lt) (by linarith [hc.theta_pos])) hc.le_one_sub_contr
  rwa [one_div_div] at h

lemma div_one_sub_contr_le {a : ℝ} (ha : 0 ≤ a) :
    a / (1 - contr β δ γ θ R) ≤ 2 * θ / (θ - δ) * a := by
  have := mul_le_mul_of_nonneg_left hc.inv_one_sub_contr_le ha
  calc a / (1 - contr β δ γ θ R) = a * (1 / (1 - contr β δ γ θ R)) := by ring
    _ ≤ a * (2 * θ / (θ - δ)) := this
    _ = 2 * θ / (θ - δ) * a := by ring

/-- The key smallness estimate: for `a ≤ ρ`, `c · a / (1 - K) ≤ R`. -/
lemma cst_mul_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ rho β δ θ R) :
    cst β θ * (a / (1 - contr β δ γ θ R)) ≤ R := by
  have hθ := hc.theta_pos
  have hc0 := hc.cst_pos
  have hδθ := sub_pos.2 hc.delta_lt
  calc cst β θ * (a / (1 - contr β δ γ θ R)) ≤ cst β θ * (2 * θ / (θ - δ) * rho β δ θ R) :=
        mul_le_mul_of_nonneg_left ((hc.div_one_sub_contr_le ha0).trans
          (mul_le_mul_of_nonneg_left ha (by positivity))) hc0.le
    _ = R := by
        rw [rho]; field_simp

lemma geom_le (n : ℕ) : ∑ i ∈ range n, contr β δ γ θ R ^ i ≤ (1 - contr β δ γ θ R)⁻¹ :=
  ((summable_geometric_of_lt_one hc.contr_nonneg hc.contr_lt_one).sum_le_tsum (range n)
    (fun i _ => pow_nonneg hc.contr_nonneg i)).trans
    (tsum_geometric_of_lt_one hc.contr_nonneg hc.contr_lt_one).le

lemma rho_pos (hR : 0 < R) : 0 < rho β δ θ R := by
  have := hc.theta_pos; have := hc.cst_pos; have := sub_pos.2 hc.delta_lt
  unfold rho; positivity

lemma tendsto_rate (j : ℕ) : Tendsto (fun n => rho β δ θ R * contr β δ γ θ R ^ n /
    (1 - contr β δ γ θ R) * θ ^ j) atTop (𝓝 0) := by
  have := (((tendsto_pow_atTop_nhds_zero_of_lt_one hc.contr_nonneg hc.contr_lt_one).const_mul
    (rho β δ θ R)).div_const (1 - contr β δ γ θ R)).mul_const (θ ^ j)
  simpa using this

end Admissible

/-- For any `0 ≤ β`, `0 ≤ δ < θ < 1`, `0 ≤ γ` and `0 < r` there is an admissible radius `R > 0`
(hence `ρ = rho β δ θ R > 0`). -/
lemma Admissible.exists {β δ γ r θ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hδθ : δ < θ)
    (hθ : θ < 1) (hr : 0 < r) : ∃ R, 0 < R ∧ Admissible β δ γ r θ R := by
  have hc1 : 1 ≤ cst β θ := le_max_left _ _
  have hc0 : 0 < cst β θ := lt_of_lt_of_le one_pos hc1
  have hd := sub_pos.2 hδθ
  refine ⟨min r ((θ - δ) / (2 * (γ + 1) * cst β θ)), lt_min hr (by positivity), ?_⟩
  refine ⟨hβ, hδ, hγ, hδθ, hθ, (lt_min hr (by positivity)).le, min_le_left _ _, ?_⟩
  have h1 : min r ((θ - δ) / (2 * (γ + 1) * cst β θ)) ≤ (θ - δ) / (2 * (γ + 1) * cst β θ) :=
    min_le_right _ _
  calc 2 * γ * min r ((θ - δ) / (2 * (γ + 1) * cst β θ)) * cst β θ
      ≤ 2 * γ * ((θ - δ) / (2 * (γ + 1) * cst β θ)) * cst β θ := by gcongr
    _ = γ / (γ + 1) * (θ - δ) := by field_simp
    _ ≤ 1 * (θ - δ) := by
        gcongr; rw [div_le_one (by positivity)]; linarith
    _ = θ - δ := one_mul _

/-! ### A real-variable lemma -/

/-- If a bound `f j ≤ N θ^j` always improves to `f j ≤ (ε + K N) θ^j` with `0 ≤ K < 1`, then
`f j ≤ ε / (1 - K) θ^j`. -/
lemma le_of_contraction {f : ℕ → ℝ} {θ K ε N₀ : ℝ} (hK0 : 0 ≤ K) (hK1 : K < 1)
    (h0 : ∀ j, f j ≤ N₀ * θ ^ j)
    (hstep : ∀ N, (∀ j, f j ≤ N * θ ^ j) → ∀ j, f j ≤ (ε + K * N) * θ ^ j) :
    ∀ j, f j ≤ ε / (1 - K) * θ ^ j := by
  have hK : 1 - K ≠ 0 := by linarith
  have key : ∀ n : ℕ, ∀ j, f j ≤ (K ^ n * N₀ + ε * (1 - K ^ n) / (1 - K)) * θ ^ j := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      intro j
      have := hstep _ ih j
      convert this using 2
      field_simp
      ring
  intro j
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1
  have hlim : Tendsto (fun n : ℕ => (K ^ n * N₀ + ε * (1 - K ^ n) / (1 - K)) * θ ^ j) atTop
      (𝓝 ((0 * N₀ + ε * (1 - 0) / (1 - K)) * θ ^ j)) :=
    ((hp.mul_const N₀).add (((tendsto_const_nhds.sub hp).const_mul ε).div_const _)).mul_const _
  rw [show (0 * N₀ + ε * (1 - 0) / (1 - K)) = ε / (1 - K) by ring] at hlim
  exact ge_of_tendsto' hlim (fun n => key n j)

/-- A sequence of functions converging with a rate independent of the point converges
uniformly. -/
lemma tendstoUniformlyOn_of_dist_le {α β : Type*} [PseudoMetricSpace β] {F : ℕ → α → β}
    {f : α → β} {s : Set α} {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0))
    (h : ∀ n, ∀ x ∈ s, dist (F n x) (f x) ≤ u n) : TendstoUniformlyOn F f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 hu).2 ε hε] with n hn x hx
  rw [dist_comm]
  exact (h n x hx).trans_lt hn

/-- Joint continuity from continuity in the parameter and a uniform Lipschitz bound. -/
lemma continuous_apply_of_lipschitz {P X Y : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : P → X → Y) (s : Set X) (L : ℝ)
    (hL : ∀ m, ∀ x ∈ s, ∀ y ∈ s, dist (f m x) (f m y) ≤ L * dist x y)
    (hf : ∀ x ∈ s, Continuous fun m => f m x) {u : P → X} (hu : Continuous u)
    (hus : ∀ m, u m ∈ s) : Continuous fun m => f m (u m) := by
  rw [continuous_iff_continuousAt]
  intro m₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have h1 := tendsto_iff_dist_tendsto_zero.1 (hu.tendsto m₀)
  have h2 := tendsto_iff_dist_tendsto_zero.1 ((hf (u m₀) (hus m₀)).tendsto m₀)
  refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) (by simpa using (h1.const_mul L).add h2)
  exact (dist_triangle _ (f m (u m₀)) _).trans (add_le_add_left (hL m _ (hus m) _ (hus m₀)) _)

section CLM

variable {P X Y : Type*} [TopologicalSpace P] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A strongly continuous, uniformly bounded family of operators applied to a continuous
curve is continuous. -/
lemma continuous_clm_apply (T : P → X →L[ℂ] Y) {C : ℝ} (hT : ∀ m, ‖T m‖ ≤ C)
    (hTc : ∀ x, Continuous fun m => T m x) {u : P → X} (hu : Continuous u) :
    Continuous fun m => T m (u m) :=
  continuous_apply_of_lipschitz (fun m x => T m x) univ C
    (fun m x _ y _ => by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact (T m).le_of_opNorm_le (hT m) _)
    (fun x _ => hTc x) hu (fun _ => mem_univ _)

lemma continuous_pow_clm_apply (T : P → X →L[ℂ] X) (hT : ∀ m, ‖T m‖ ≤ 1)
    (hTc : ∀ x, Continuous fun m => T m x) (n : ℕ) {u : P → X} (hu : Continuous u) :
    Continuous fun m => (T m ^ n) (u m) := by
  induction n generalizing u with
  | zero => simpa using hu
  | succ n ih =>
    simp only [pow_succ', ContinuousLinearMap.mul_apply]
    exact continuous_clm_apply T hT hTc (ih hu)

end CLM

/-! ### The dynamical system -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {W : ℕ → Type*} [∀ j, NormedAddCommGroup (W j)] [∀ j, NormedSpace ℂ (W j)]

/-- The data of the non-autonomous dynamical system
`v_{j+1} = E v_j + B_j w_j`, `w_{j+1} = D_j w_j + g_j (v_j, w_j)`
with `v_j ∈ V`, `w_j ∈ W j`. -/
structure System (V : Type*) (W : ℕ → Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [∀ j, NormedAddCommGroup (W j)] [∀ j, NormedSpace ℂ (W j)] where
  /-- The (invertible) linear part in the `v`-direction. -/
  E : V ≃L[ℂ] V
  /-- The coupling of `w_j` into `v_{j+1}`. -/
  B : ∀ j, W j →L[ℂ] V
  /-- The (contracting) linear part in the `w`-direction. -/
  D : ∀ j, W j →L[ℂ] W (j + 1)
  /-- The nonlinear part of `w_{j+1}`. -/
  g : ∀ j, V × W j → W (j + 1)

/-- A map is *analytic along complex curves* on a set `s` if its composition with every
holomorphic curve `c : ℂ → X` taking values in `s` on an open set `U` is holomorphic on `U`.
This is the notion of analyticity used in `h02rg.tex`. -/
def AnalyticAlongCurves {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (f : X → Y) (s : Set X) : Prop :=
  ∀ (U : Set ℂ) (c : ℂ → X), IsOpen U → DifferentiableOn ℂ c U → MapsTo c U s →
    DifferentiableOn ℂ (f ∘ c) U

/-- Weighted bound: `‖b j‖ ≤ N θ^j` for all `j`. -/
def WBound (θ : ℝ) (b : ∀ j, W j) (N : ℝ) : Prop := ∀ j, ‖b j‖ ≤ N * θ ^ j

section WBound

omit [∀ j, NormedSpace ℂ (W j)]

variable {θ N N' : ℝ} {b b' : ∀ j, W j}

lemma WBound.nonneg (h : WBound θ b N) : 0 ≤ N := by
  simpa using (norm_nonneg _).trans (h 0)

lemma WBound.mono (h : WBound θ b N) (hN : N ≤ N') (hθ : 0 ≤ θ) : WBound θ b N' :=
  fun j => (h j).trans (mul_le_mul_of_nonneg_right hN (pow_nonneg hθ j))

lemma WBound.sub (h : WBound θ b N) (h' : WBound θ b' N') : WBound θ (b - b') (N + N') :=
  fun j => (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (h j) (h' j))

end WBound

namespace System

variable (S : System V W)

/-- The inverse `E⁻¹` as a continuous linear map. -/
abbrev Einv : V →L[ℂ] V := S.E.symm

/-- The orbit of the initial condition `(v₀, w₀)`. -/
def orbit (v₀ : V) (w₀ : W 0) : ∀ j, V × W j
  | 0 => (v₀, w₀)
  | j + 1 => (S.E (orbit v₀ w₀ j).1 + S.B j (orbit v₀ w₀ j).2,
      S.D j (orbit v₀ w₀ j).2 + S.g j (orbit v₀ w₀ j))

/-- The (non-dependent) sequence `i ↦ B_i b_i`. -/
def Bb (b : ∀ j, W j) (i : ℕ) : V := S.B i (b i)

/-- The `v`-sequence determined by a `w`-sequence on the stable manifold:
`v_j = -∑_{k ≥ 0} E^{-(k+1)} B_{j+k} w_{j+k}`. -/
def vOf (b : ∀ j, W j) (j : ℕ) : V := -∑' k, (S.Einv ^ (k + 1)) (S.Bb b (j + k))

/-- The fixed point map: `F(w)_0 = w₀`, `F(w)_{j+1} = D_j w_j + g_j (v_j, w_j)` with
`v = vOf w`. -/
def F (w₀ : W 0) (b : ∀ j, W j) : ∀ j, W j
  | 0 => w₀
  | j + 1 => S.D j (b j) + S.g j (S.vOf b j, b j)

/-- The Picard iterates `F^n(0)`. -/
def picard (w₀ : W 0) : ℕ → ∀ j, W j
  | 0 => 0
  | n + 1 => S.F w₀ (picard w₀ n)

/-- The fixed point of `F`, defined as the componentwise limit of the Picard iterates. -/
def fixedSeq (w₀ : W 0) (j : ℕ) : W j := limUnder atTop fun n => S.picard w₀ n j

/-- The stable manifold map `w₀ ↦ v₀`. -/
def stableMap (w₀ : W 0) : V := S.vOf (S.fixedSeq w₀) 0

@[simp] lemma F_zero (w₀ : W 0) (b : ∀ j, W j) : S.F w₀ b 0 = w₀ := rfl

lemma F_succ (w₀ : W 0) (b : ∀ j, W j) (j : ℕ) :
    S.F w₀ b (j + 1) = S.D j (b j) + S.g j (S.vOf b j, b j) := rfl

@[simp] lemma picard_zero (w₀ : W 0) : S.picard w₀ 0 = 0 := rfl

lemma picard_succ (w₀ : W 0) (n : ℕ) : S.picard w₀ (n + 1) = S.F w₀ (S.picard w₀ n) := rfl

lemma orbit_succ (v₀ : V) (w₀ : W 0) (j : ℕ) : S.orbit v₀ w₀ (j + 1) =
    (S.E (S.orbit v₀ w₀ j).1 + S.B j (S.orbit v₀ w₀ j).2,
      S.D j (S.orbit v₀ w₀ j).2 + S.g j (S.orbit v₀ w₀ j)) := rfl

@[simp] lemma vOf_zero (j : ℕ) : S.vOf 0 j = 0 := by simp [vOf, Bb]

/-- The hypotheses of the stable manifold theorem, with explicit constants. -/
structure Bounds (β δ γ r : ℝ) : Prop where
  norm_Einv_le : ‖(S.E.symm : V →L[ℂ] V)‖ ≤ 1
  norm_B_le : ∀ j, ‖S.B j‖ ≤ β
  norm_D_le : ∀ j, ‖S.D j‖ ≤ δ
  g_zero : ∀ j, S.g j 0 = 0
  g_lipschitz : ∀ j (x y : V × W j), ‖x‖ ≤ r → ‖y‖ ≤ r →
    ‖S.g j x - S.g j y‖ ≤ γ * max ‖x‖ ‖y‖ * ‖x - y‖

variable {S}
variable {β δ γ r θ R : ℝ}
variable [CompleteSpace V] [∀ j, CompleteSpace (W j)]

namespace Bounds

variable (hS : S.Bounds β δ γ r)
include hS

omit [CompleteSpace V] [∀ j, CompleteSpace (W j)] in
lemma beta_nonneg : 0 ≤ β := (norm_nonneg _).trans (hS.norm_B_le 0)

omit [CompleteSpace V] [∀ j, CompleteSpace (W j)] in
lemma norm_Einv_pow_apply_le (n : ℕ) (x : V) : ‖(S.Einv ^ n) x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact (S.Einv.le_opNorm _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hS.norm_Einv_le).trans ih)

omit [CompleteSpace V] [∀ j, CompleteSpace (W j)] in
lemma norm_term_le {b : ∀ j, W j} {N : ℝ} (hb : WBound θ b N) (j k : ℕ) :
    ‖(S.Einv ^ (k + 1)) (S.Bb b (j + k))‖ ≤ β * N * θ ^ j * θ ^ k := by
  refine (hS.norm_Einv_pow_apply_le _ _).trans ?_
  refine ((S.B (j + k)).le_of_opNorm_le (hS.norm_B_le _) _).trans ?_
  calc β * ‖b (j + k)‖ ≤ β * (N * θ ^ (j + k)) :=
        mul_le_mul_of_nonneg_left (hb _) hS.beta_nonneg
    _ = β * N * θ ^ j * θ ^ k := by rw [pow_add]; ring

omit [∀ j, CompleteSpace (W j)] in
lemma summable_term (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {b : ∀ j, W j} {N : ℝ} (hb : WBound θ b N)
    (j : ℕ) : Summable fun k => (S.Einv ^ (k + 1)) (S.Bb b (j + k)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ0 hθ1).mul_left (β * N * θ ^ j))
    (hS.norm_term_le hb j)

omit [CompleteSpace V] [∀ j, CompleteSpace (W j)] in
lemma norm_vOf_le (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {b : ∀ j, W j} {N : ℝ} (hb : WBound θ b N)
    (j : ℕ) : ‖S.vOf b j‖ ≤ β / (1 - θ) * N * θ ^ j := by
  rw [vOf, norm_neg]
  refine (tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hθ0 hθ1).mul_left (β * N * θ ^ j))
    (hS.norm_term_le hb j)).trans (le_of_eq ?_)
  ring

omit [∀ j, CompleteSpace (W j)] in
lemma vOf_sub (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {b b' : ∀ j, W j} {N N' : ℝ} (hb : WBound θ b N)
    (hb' : WBound θ b' N') (j : ℕ) : S.vOf (b - b') j = S.vOf b j - S.vOf b' j := by
  have e : ∀ k, (S.Einv ^ (k + 1)) (S.Bb (b - b') (j + k)) =
      (S.Einv ^ (k + 1)) (S.Bb b (j + k)) - (S.Einv ^ (k + 1)) (S.Bb b' (j + k)) := by
    intro k; simp [Bb, map_sub]
  simp only [vOf, e]
  rw [(hS.summable_term hθ0 hθ1 hb j).tsum_sub (hS.summable_term hθ0 hθ1 hb' j)]
  abel

omit [∀ j, CompleteSpace (W j)] in
lemma vOf_succ (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {b : ∀ j, W j} {N : ℝ} (hb : WBound θ b N)
    (j : ℕ) : S.E (S.vOf b j) + S.B j (b j) = S.vOf b (j + 1) := by
  have hs := hS.summable_term hθ0 hθ1 hb j
  have hs' := hS.summable_term hθ0 hθ1 hb (j + 1)
  have e2 : ∑' k, (S.Einv ^ (k + 1 + 1)) (S.Bb b (j + (k + 1))) =
      S.Einv (∑' k, (S.Einv ^ (k + 1)) (S.Bb b (j + 1 + k))) := by
    rw [S.Einv.map_tsum hs']
    congr 1
    funext k
    rw [pow_succ' _ (k + 1), ContinuousLinearMap.mul_apply, show j + (k + 1) = j + 1 + k by ring]
  have e1 : S.vOf b j = -((S.Einv) (S.Bb b j) +
      S.Einv (∑' k, (S.Einv ^ (k + 1)) (S.Bb b (j + 1 + k)))) := by
    rw [vOf, hs.tsum_eq_zero_add, e2, zero_add, add_zero, pow_one]
  have hEE : ∀ x, S.E (S.Einv x) = x := fun x => S.E.apply_symm_apply x
  rw [e1, vOf, map_neg, S.E.map_add, hEE, hEE]
  simp only [Bb]
  abel

end Bounds

namespace Bounds

variable (hS : S.Bounds β δ γ r) (hc : Admissible β δ γ r θ R)
include hS hc

omit [CompleteSpace V] [∀ j, CompleteSpace (W j)] in
lemma norm_pair_le {b : ∀ j, W j} {N : ℝ} (hb : WBound θ b N) (j : ℕ) :
    ‖(S.vOf b j, b j)‖ ≤ cst β θ * N * θ ^ j := by
  have hN := hb.nonneg
  have hθj := pow_nonneg hc.theta_pos.le j
  rw [Prod.norm_mk, max_le_iff]
  constructor
  · exact (hS.norm_vOf_le hc.theta_pos.le hc.theta_lt hb j).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc.kappa_le_cst hN) hθj)
  · refine (hb j).trans ?_
    rw [mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg hN hθj) hc.one_le_cst

omit [CompleteSpace V] [∀ j, CompleteSpace (W j)] in
lemma pair_le_R {b : ∀ j, W j} {N : ℝ} (hb : WBound θ b N) (hN : cst β θ * N ≤ R) (j : ℕ) :
    ‖(S.vOf b j, b j)‖ ≤ R :=
  (hS.norm_pair_le hc hb j).trans ((mul_le_of_le_one_right
    (mul_nonneg hc.cst_pos.le hb.nonneg) (pow_le_one₀ hc.theta_pos.le hc.theta_lt.le)).trans hN)

omit [∀ j, CompleteSpace (W j)] in
/-- The contraction estimate for the fixed point map `F` in the weighted norm. -/
lemma F_sub {b b' : ∀ j, W j} {N₁ N₂ N : ℝ} (hb : WBound θ b N₁) (hb' : WBound θ b' N₂)
    (hx : ∀ j, ‖(S.vOf b j, b j)‖ ≤ R) (hx' : ∀ j, ‖(S.vOf b' j, b' j)‖ ≤ R)
    (hd : WBound θ (b - b') N) (w₀ w₀' : W 0) :
    WBound θ (S.F w₀ b - S.F w₀' b') (‖w₀ - w₀'‖ + contr β δ γ θ R * N) := by
  have hN := hd.nonneg
  have hK := hc.contr_nonneg
  have hθ := hc.theta_pos
  intro j
  cases j with
  | zero =>
    simp only [Pi.sub_apply, F_zero, pow_zero, mul_one]
    linarith [mul_nonneg hK hN]
  | succ j =>
    simp only [Pi.sub_apply, F_succ]
    have e1 : S.D j (b j) + S.g j (S.vOf b j, b j) - (S.D j (b' j) + S.g j (S.vOf b' j, b' j)) =
        S.D j ((b - b') j) + (S.g j (S.vOf b j, b j) - S.g j (S.vOf b' j, b' j)) := by
      simp only [Pi.sub_apply, map_sub]; abel
    have hdiff : (S.vOf b j, b j) - (S.vOf b' j, b' j) = (S.vOf (b - b') j, (b - b') j) := by
      rw [hS.vOf_sub hθ.le hc.theta_lt hb hb']; rfl
    have h1 : ‖S.D j ((b - b') j)‖ ≤ δ * (N * θ ^ j) :=
      ((S.D j).le_of_opNorm_le (hS.norm_D_le j) _).trans
        (mul_le_mul_of_nonneg_left (hd j) hc.delta_nonneg)
    have h2 : ‖S.g j (S.vOf b j, b j) - S.g j (S.vOf b' j, b' j)‖ ≤
        γ * R * (cst β θ * N * θ ^ j) := by
      refine (hS.g_lipschitz j _ _ ((hx j).trans hc.R_le) ((hx' j).trans hc.R_le)).trans ?_
      rw [hdiff]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (max_le (hx j) (hx' j)) hc.gamma_nonneg)
        (hS.norm_pair_le hc hd j) (norm_nonneg _)
        (mul_nonneg hc.gamma_nonneg hc.R_nonneg)
    rw [e1]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_sub_nonneg ?_))
    have e2 : (‖w₀ - w₀'‖ + contr β δ γ θ R * N) * θ ^ (j + 1) -
        (δ * (N * θ ^ j) + γ * R * (cst β θ * N * θ ^ j)) =
        ‖w₀ - w₀'‖ * θ ^ j * θ + (contr β δ γ θ R * θ - (δ + γ * R * cst β θ)) * N * θ ^ j := by
      ring
    rw [e2, hc.contr_mul, sub_self, zero_mul, zero_mul, add_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hθ.le j)) hθ.le

omit [∀ j, CompleteSpace (W j)] in
/-- Estimates on the Picard iterates. -/
lemma picard_est {w₀ : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R) (n : ℕ) :
    WBound θ (S.picard w₀ n) ((∑ i ∈ range n, contr β δ γ θ R ^ i) * ‖w₀‖) ∧
      WBound θ (S.picard w₀ (n + 1) - S.picard w₀ n) (contr β δ γ θ R ^ n * ‖w₀‖) := by
  have hK := hc.contr_nonneg
  have hθ := hc.theta_pos
  have hpair : ∀ (b : ∀ j, W j) (m : ℕ),
      WBound θ b ((∑ i ∈ range m, contr β δ γ θ R ^ i) * ‖w₀‖) →
      ∀ j, ‖(S.vOf b j, b j)‖ ≤ R := by
    intro b m hb
    refine hS.pair_le_R hc hb ((mul_le_mul_of_nonneg_left ?_ hc.cst_pos.le).trans
      (hc.cst_mul_le (norm_nonneg w₀) hw))
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (hc.geom_le m) (norm_nonneg _)
  induction n with
  | zero =>
    refine ⟨fun j => by simp, fun j => ?_⟩
    cases j with
    | zero => simp [picard_succ]
    | succ j =>
      have : S.g j (0, 0) = 0 := hS.g_zero j
      simp [picard_succ, F_succ, this]
      exact mul_nonneg (norm_nonneg _) (pow_nonneg hθ.le _)
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have h1' : WBound θ (S.picard w₀ (n + 1))
        ((∑ i ∈ range (n + 1), contr β δ γ θ R ^ i) * ‖w₀‖) := by
      intro j
      have e : S.picard w₀ (n + 1) j = S.picard w₀ n j +
          (S.picard w₀ (n + 1) - S.picard w₀ n) j := by simp
      rw [e, sum_range_succ]
      refine (norm_add_le _ _).trans ?_
      have := add_le_add (h1 j) (h2 j)
      linarith
    refine ⟨h1', ?_⟩
    have := hS.F_sub hc h1' h1 (hpair _ _ h1') (hpair _ _ h1) h2 w₀ w₀
    intro j
    convert this j using 2
    simp [pow_succ]; ring

/-- The fixed point: bounds, the fixed point equation, and convergence of the Picard
iterates. -/
theorem fixed {w₀ : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R) :
    WBound θ (S.fixedSeq w₀) (‖w₀‖ / (1 - contr β δ γ θ R)) ∧
      S.F w₀ (S.fixedSeq w₀) = S.fixedSeq w₀ ∧
      (∀ n j, ‖S.picard w₀ n j - S.fixedSeq w₀ j‖ ≤
        ‖w₀‖ * contr β δ γ θ R ^ n / (1 - contr β δ γ θ R) * θ ^ j) ∧
      ∀ n, WBound θ (S.picard w₀ n) (‖w₀‖ / (1 - contr β δ γ θ R)) := by
  set K := contr β δ γ θ R with hKdef
  have hK0 := hc.contr_nonneg
  have hK1 := hc.contr_lt_one
  have h1K := hc.one_sub_contr_pos
  have hθ := hc.theta_pos
  have hp := hS.picard_est hc hw
  have hpN : ∀ n, WBound θ (S.picard w₀ n) (‖w₀‖ / (1 - K)) := by
    intro n
    refine (hp n).1.mono ?_ hθ.le
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (hc.geom_le n) (norm_nonneg _)
  have hcau : ∀ j n, dist (S.picard w₀ n j) (S.picard w₀ (n + 1) j) ≤
      (‖w₀‖ * θ ^ j) * K ^ n := by
    intro j n
    rw [dist_eq_norm, norm_sub_rev]
    have := (hp n).2 j
    simp only [Pi.sub_apply] at this
    linarith
  have hlim : ∀ j, Tendsto (fun n => S.picard w₀ n j) atTop (𝓝 (S.fixedSeq w₀ j)) :=
    fun j => (cauchySeq_of_le_geometric K _ hK1 (hcau j)).tendsto_limUnder
  have hdist : ∀ n j, ‖S.picard w₀ n j - S.fixedSeq w₀ j‖ ≤
      ‖w₀‖ * K ^ n / (1 - K) * θ ^ j := by
    intro n j
    rw [← dist_eq_norm]
    refine (dist_le_of_le_geometric_of_tendsto K _ hK1 (hcau j) (hlim j) n).trans (le_of_eq ?_)
    ring
  have hfix : WBound θ (S.fixedSeq w₀) (‖w₀‖ / (1 - K)) := fun j =>
    le_of_tendsto' ((continuous_norm.tendsto _).comp (hlim j)) (fun n => hpN n j)
  have hkey := hc.cst_mul_le (norm_nonneg w₀) hw
  refine ⟨hfix, ?_, hdist, hpN⟩
  funext j
  refine tendsto_nhds_unique ?_ ((hlim j).comp (tendsto_add_atTop_nat 1))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hF := fun n => hS.F_sub hc (hpN n) hfix (hS.pair_le_R hc (hpN n) hkey)
    (hS.pair_le_R hc hfix hkey) (N := ‖w₀‖ * K ^ n / (1 - K)) (hdist n) w₀ w₀ j
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1
  have hb : Tendsto (fun n : ℕ => (‖w₀ - w₀‖ + K * (‖w₀‖ * K ^ n / (1 - K))) * θ ^ j) atTop
      (𝓝 ((‖w₀ - w₀‖ + K * (‖w₀‖ * 0 / (1 - K))) * θ ^ j)) :=
    (tendsto_const_nhds.add (((hpow.const_mul _).div_const _).const_mul _)).mul_const _
  rw [show (‖w₀ - w₀‖ + K * (‖w₀‖ * 0 / (1 - K))) * θ ^ j = 0 by simp] at hb
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hF n) hb

/-- The orbit starting at `(S.stableMap w₀, w₀)` is `(vOf w, w)` with `w = S.fixedSeq w₀`. -/
theorem orbit_stableMap {w₀ : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R) (j : ℕ) :
    S.orbit (S.stableMap w₀) w₀ j = (S.vOf (S.fixedSeq w₀) j, S.fixedSeq w₀ j) := by
  obtain ⟨hfix, hF, -, -⟩ := hS.fixed hc hw
  induction j with
  | zero =>
    refine Prod.ext rfl ?_
    rw [← hF]; rfl
  | succ j ih =>
    rw [orbit_succ, ih]
    refine Prod.ext (hS.vOf_succ hc.theta_pos.le hc.theta_lt hfix j) ?_
    conv_rhs => rw [← hF]
    rfl

/-- **Decay of the stable orbit.** For `‖w₀‖ ≤ ρ`, the orbit `(v_j, w_j)` starting at
`(S.stableMap w₀, w₀)` satisfies `‖v_j‖ + ‖w_j‖ ≤ (1 + β/(1-θ)) (2θ/(θ-δ)) θ^j ‖w₀‖`. -/
theorem norm_orbit_stableMap_le {w₀ : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R) (j : ℕ) :
    ‖(S.orbit (S.stableMap w₀) w₀ j).1‖ + ‖(S.orbit (S.stableMap w₀) w₀ j).2‖ ≤
      (1 + β / (1 - θ)) * (2 * θ / (θ - δ)) * θ ^ j * ‖w₀‖ := by
  obtain ⟨hfix, -, -, -⟩ := hS.fixed hc hw
  have hθ := hc.theta_pos
  rw [hS.orbit_stableMap hc hw j]
  have h1 := hS.norm_vOf_le hθ.le hc.theta_lt hfix j
  have h2 := hfix j
  have h3 := hc.div_one_sub_contr_le (norm_nonneg w₀)
  have hθj := pow_nonneg hθ.le j
  have hk := hc.kappa_nonneg
  calc ‖S.vOf (S.fixedSeq w₀) j‖ + ‖S.fixedSeq w₀ j‖
      ≤ (1 + β / (1 - θ)) * θ ^ j * (‖w₀‖ / (1 - contr β δ γ θ R)) := by
        linarith
    _ ≤ (1 + β / (1 - θ)) * θ ^ j * (2 * θ / (θ - δ) * ‖w₀‖) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hθj)
    _ = (1 + β / (1 - θ)) * (2 * θ / (θ - δ)) * θ ^ j * ‖w₀‖ := by ring

/-- **Uniqueness of the stable manifold.** If the orbit of `(v₀, w₀)` stays in the `R`-ball and
decays like `θ^j` (with any constant), then `v₀ = S.stableMap w₀`. -/
theorem stableMap_unique {w₀ : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R) {v₀ : V}
    (hdecay : ∃ M, ∀ j, ‖S.orbit v₀ w₀ j‖ ≤ M * θ ^ j) (hR : ∀ j, ‖S.orbit v₀ w₀ j‖ ≤ R) :
    v₀ = S.stableMap w₀ := by
  obtain ⟨M, hM⟩ := hdecay
  obtain ⟨hfix, hF, -, -⟩ := hS.fixed hc hw
  have hθ := hc.theta_pos
  have hK0 := hc.contr_nonneg
  have hK1 := hc.contr_lt_one
  set x := S.orbit v₀ w₀ with hx
  set b' : ∀ j, W j := fun j => (x j).2 with hb'
  have hb'M : WBound θ b' M := fun j => (norm_snd_le _).trans (hM j)
  -- telescoping: `v_j = E⁻ⁿ v_{j+n} - ∑_{k<n} E^{-(k+1)} B_{j+k} w_{j+k}`
  have hrec : ∀ i, (x i).1 = S.Einv (x (i + 1)).1 - S.Einv (S.Bb b' i) := by
    intro i
    show (x i).1 = S.Einv (S.E (x i).1 + S.B i (x i).2) - S.Einv (S.Bb b' i)
    simp [Bb, b']
  have htel : ∀ j n, (x j).1 = (S.Einv ^ n) (x (j + n)).1 -
      ∑ k ∈ range n, (S.Einv ^ (k + 1)) (S.Bb b' (j + k)) := by
    intro j n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, hrec (j + n), map_sub, ← ContinuousLinearMap.mul_apply,
        ← ContinuousLinearMap.mul_apply, ← pow_succ, sum_range_succ, add_assoc j n 1]
      abel
  have hv : ∀ j, (x j).1 = S.vOf b' j := by
    intro j
    have h1 : Tendsto (fun n => (S.Einv ^ n) (x (j + n)).1) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => (hS.norm_Einv_pow_apply_le n _).trans
        ((norm_fst_le _).trans (hM (j + n)))) ?_
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hc.theta_lt).const_mul (M * θ ^ j)
      rw [mul_zero] at this
      refine this.congr (fun n => ?_)
      rw [pow_add]; ring
    have h2 := (hS.summable_term hθ.le hc.theta_lt hb'M j).hasSum.tendsto_sum_nat
    have h3 : Tendsto (fun _ : ℕ => (x j).1) atTop
        (𝓝 (0 - ∑' k, (S.Einv ^ (k + 1)) (S.Bb b' (j + k)))) :=
      (h1.sub h2).congr (fun n => (htel j n).symm)
    rw [tendsto_nhds_unique tendsto_const_nhds h3, zero_sub]
    rfl
  have hxv : ∀ j, x j = (S.vOf b' j, b' j) := fun j => Prod.ext (hv j) rfl
  have hFb : S.F w₀ b' = b' := by
    funext j
    cases j with
    | zero => rfl
    | succ j =>
      rw [F_succ]
      show _ = (x (j + 1)).2
      rw [hx, orbit_succ, ← hx, hxv j]
  have hxR : ∀ j, ‖(S.vOf b' j, b' j)‖ ≤ R := fun j => hxv j ▸ hR j
  have hkey := hc.cst_mul_le (norm_nonneg w₀) hw
  have hfixR := hS.pair_le_R hc hfix hkey
  have hd := le_of_contraction (f := fun j => ‖(b' - S.fixedSeq w₀) j‖) (ε := 0) hK0 hK1
    (hb'M.sub hfix) (fun N hN => by
      have := hS.F_sub hc hb'M hfix hxR hfixR hN w₀ w₀
      rw [hFb, hF, sub_self, norm_zero] at this
      exact this)
  have hbeq : b' = S.fixedSeq w₀ := by
    funext j
    have := hd j
    simp only [zero_div, zero_mul, Pi.sub_apply] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  calc v₀ = (x 0).1 := rfl
    _ = S.vOf b' 0 := hv 0
    _ = S.stableMap w₀ := by rw [hbeq]; rfl

/-- **Existence and uniqueness.** For `‖w₀‖ ≤ ρ` there is a unique `v₀` such that the orbit of
`(v₀, w₀)` stays in the `R`-ball and decays like `θ^j`; it is `S.stableMap w₀`. -/
theorem existsUnique_stable {w₀ : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R) :
    ∃! v₀ : V, (∃ M, ∀ j, ‖S.orbit v₀ w₀ j‖ ≤ M * θ ^ j) ∧ ∀ j, ‖S.orbit v₀ w₀ j‖ ≤ R := by
  obtain ⟨hfix, -, -, -⟩ := hS.fixed hc hw
  refine ⟨S.stableMap w₀, ⟨⟨cst β θ * (‖w₀‖ / (1 - contr β δ γ θ R)), fun j => ?_⟩, fun j => ?_⟩,
    fun v₀ h => hS.stableMap_unique hc hw h.1 h.2⟩
  · rw [hS.orbit_stableMap hc hw j]; exact hS.norm_pair_le hc hfix j
  · rw [hS.orbit_stableMap hc hw j]
    exact hS.pair_le_R hc hfix (hc.cst_mul_le (norm_nonneg w₀) hw) j

/-- **Lipschitz continuity of the stable manifold.** -/
theorem norm_stableMap_sub_le {w₀ w₀' : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R)
    (hw' : ‖w₀'‖ ≤ rho β δ θ R) :
    ‖S.stableMap w₀ - S.stableMap w₀'‖ ≤ β / (1 - θ) * (2 * θ / (θ - δ)) * ‖w₀ - w₀'‖ := by
  obtain ⟨hfix, hF, -, -⟩ := hS.fixed hc hw
  obtain ⟨hfix', hF', -, -⟩ := hS.fixed hc hw'
  have hθ := hc.theta_pos
  have hd := le_of_contraction (f := fun j => ‖(S.fixedSeq w₀ - S.fixedSeq w₀') j‖)
    hc.contr_nonneg hc.contr_lt_one (hfix.sub hfix') (fun N hN => by
      have := hS.F_sub hc hfix hfix' (hS.pair_le_R hc hfix (hc.cst_mul_le (norm_nonneg _) hw))
        (hS.pair_le_R hc hfix' (hc.cst_mul_le (norm_nonneg _) hw')) hN w₀ w₀'
      rwa [hF, hF'] at this)
  have h := hS.norm_vOf_le hθ.le hc.theta_lt (b := S.fixedSeq w₀ - S.fixedSeq w₀') hd 0
  rw [hS.vOf_sub hθ.le hc.theta_lt hfix hfix'] at h
  refine h.trans ?_
  rw [pow_zero, mul_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hc.div_one_sub_contr_le (norm_nonneg _)) hc.kappa_nonneg

/-- Uniform convergence of the Picard iterates: the rate does not depend on `w₀`. -/
lemma dist_picard_fixedSeq_le {w₀ : W 0} (hw : ‖w₀‖ ≤ rho β δ θ R) (n j : ℕ) :
    dist (S.picard w₀ n j) (S.fixedSeq w₀ j) ≤
      rho β δ θ R * contr β δ γ θ R ^ n / (1 - contr β δ γ θ R) * θ ^ j := by
  rw [dist_eq_norm]
  refine ((hS.fixed hc hw).2.2.1 n j).trans ?_
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hw (pow_nonneg hc.contr_nonneg n)) hc.one_sub_contr_pos.le)
    (pow_nonneg hc.theta_pos.le j)

omit [∀ j, CompleteSpace (W j)] in
/-- A uniformly weighted-bounded family of holomorphic `w`-sequences gives holomorphic
`v`-sequences. -/
lemma differentiableOn_vOf {U : Set ℂ} (hU : IsOpen U) {b : ℂ → ∀ j, W j}
    (hb : ∀ i, DifferentiableOn ℂ (fun z => b z i) U) {N : ℝ} (hbN : ∀ z ∈ U, WBound θ (b z) N)
    (j : ℕ) : DifferentiableOn ℂ (fun z => S.vOf (b z) j) U := by
  have hθ := hc.theta_pos
  refine DifferentiableOn.neg (Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one hθ.le hc.theta_lt).mul_left (β * N * θ ^ j)) (fun k => ?_) hU
    (fun k z hz => hS.norm_term_le (hbN z hz) j k))
  exact (S.Einv ^ (k + 1)).differentiable.comp_differentiableOn
    ((S.B (j + k)).differentiable.comp_differentiableOn (hb (j + k)))

/-- **Holomorphic dependence on the initial datum.** If every `g_j` is analytic along complex
curves in the `r`-ball, then `w₀ ↦ S.stableMap w₀` is analytic along complex curves in the
`ρ`-ball: for every holomorphic curve `c` on an open `U ⊆ ℂ` with `‖c z‖ ≤ ρ`,
`z ↦ S.stableMap (c z)` is holomorphic on `U`. -/
theorem analyticAlongCurves_stableMap
    (hg : ∀ j, AnalyticAlongCurves (S.g j) (closedBall 0 r)) :
    AnalyticAlongCurves S.stableMap (closedBall 0 (rho β δ θ R)) := by
  intro U c hU hcd hcU
  have hw : ∀ z ∈ U, ‖c z‖ ≤ rho β δ θ R := fun z hz => mem_closedBall_zero_iff.1 (hcU hz)
  have hθ := hc.theta_pos
  have h1K := hc.one_sub_contr_pos
  set N := rho β δ θ R / (1 - contr β δ γ θ R)
  have hpN : ∀ n, ∀ z ∈ U, WBound θ (S.picard (c z) n) N := fun n z hz =>
    ((hS.fixed hc (hw z hz)).2.2.2 n).mono (div_le_div_of_nonneg_right (hw z hz) h1K.le) hθ.le
  have hfN : ∀ z ∈ U, WBound θ (S.fixedSeq (c z)) N := fun z hz =>
    (hS.fixed hc (hw z hz)).1.mono (div_le_div_of_nonneg_right (hw z hz) h1K.le) hθ.le
  have hpd : ∀ n j, DifferentiableOn ℂ (fun z => S.picard (c z) n j) U := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih =>
      intro j
      cases j with
      | zero => simpa [picard_succ] using hcd
      | succ j =>
        simp only [picard_succ, F_succ]
        refine DifferentiableOn.add ((S.D j).differentiable.comp_differentiableOn (ih j)) ?_
        refine hg j U (fun z => (S.vOf (S.picard (c z) n) j, S.picard (c z) n j)) hU
          ((hS.differentiableOn_vOf hc hU ih (hpN n) j).prodMk (ih j)) (fun z hz => ?_)
        exact mem_closedBall_zero_iff.2 (hS.pair_le_R hc ((hS.fixed hc (hw z hz)).2.2.2 n)
          (hc.cst_mul_le (norm_nonneg _) (hw z hz)) j |>.trans hc.R_le)
  have hfd : ∀ j, DifferentiableOn ℂ (fun z => S.fixedSeq (c z) j) U := fun j =>
    (tendstoUniformlyOn_of_dist_le (hc.tendsto_rate j)
      (fun n z hz => hS.dist_picard_fixedSeq_le hc (hw z hz) n j)).tendstoLocallyUniformlyOn
      |>.differentiableOn (Eventually.of_forall fun n => hpd n j) hU
  exact hS.differentiableOn_vOf hc hU hfd hfN 0

/-- **Holomorphy along a complex line, with a derivative bound.** For `ŵ ∈ W 0` and `R₀` with
`R₀ ‖ŵ‖ ≤ ρ`, the map `λ ↦ S.stableMap (λ • ŵ)` is holomorphic on the disc of radius `R₀`, and
its derivative there is bounded by `β/(1-θ) · 2θ/(θ-δ) · ‖ŵ‖`. -/
theorem differentiableOn_stableMap_smul
    (hg : ∀ j, AnalyticAlongCurves (S.g j) (closedBall 0 r)) (ŵ : W 0) {R₀ : ℝ}
    (hR₀ : R₀ * ‖ŵ‖ ≤ rho β δ θ R) :
    DifferentiableOn ℂ (fun z : ℂ => S.stableMap (z • ŵ)) (ball 0 R₀) ∧
      ∀ z ∈ ball (0 : ℂ) R₀, ‖deriv (fun z : ℂ => S.stableMap (z • ŵ)) z‖ ≤
        β / (1 - θ) * (2 * θ / (θ - δ)) * ‖ŵ‖ := by
  have hmem : ∀ z ∈ ball (0 : ℂ) R₀, ‖z • ŵ‖ ≤ rho β δ θ R := fun z hz => by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (mem_ball_zero_iff.1 hz).le (norm_nonneg _)).trans hR₀
  refine ⟨hS.analyticAlongCurves_stableMap hc hg _ (fun z => z • ŵ) isOpen_ball
    (differentiableOn_id.smul_const ŵ) (fun z hz => mem_closedBall_zero_iff.2 (hmem z hz)),
    fun z hz => ?_⟩
  have hL0 : 0 ≤ β / (1 - θ) * (2 * θ / (θ - δ)) * ‖ŵ‖ :=
    mul_nonneg (mul_nonneg hc.kappa_nonneg (div_nonneg (by linarith [hc.theta_pos])
      (sub_nonneg.2 hc.delta_lt.le))) (norm_nonneg _)
  have hlip : LipschitzOnWith (Real.toNNReal (β / (1 - θ) * (2 * θ / (θ - δ)) * ‖ŵ‖))
      (fun z : ℂ => S.stableMap (z • ŵ)) (ball 0 R₀) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
    refine (hS.norm_stableMap_sub_le hc (hmem x hx) (hmem y hy)).trans (le_of_eq ?_)
    rw [← sub_smul, norm_smul]; ring
  have := norm_deriv_le_of_lipschitzOn (isOpen_ball.mem_nhds hz) hlip
  rwa [Real.coe_toNNReal _ hL0] at this

end Bounds

end System

/-! ### Continuous dependence on a parameter -/

section Parameter

variable [CompleteSpace V] [∀ j, CompleteSpace (W j)]
variable {P : Type*} [TopologicalSpace P] {β δ γ r θ R : ℝ}

omit [CompleteSpace V] [∀ j, CompleteSpace (W j)] in
/-- Strong continuity of `E⁻¹` follows from strong continuity of `E` and `‖E⁻¹‖ ≤ 1`. -/
lemma continuous_Einv_apply (S : P → System V W) (hEinv : ∀ m, ‖(S m).Einv‖ ≤ 1)
    (hE : ∀ x, Continuous fun m => (S m).E x) (x : V) :
    Continuous fun m => (S m).Einv x := by
  rw [continuous_iff_continuousAt]
  intro m₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set z := (S m₀).Einv x
  have hz : (S m₀).E z = x := (S m₀).E.apply_symm_apply x
  have hb : ∀ m, ‖(S m).Einv x - (S m₀).Einv x‖ ≤ ‖(S m₀).E z - (S m).E z‖ := by
    intro m
    have e : (S m).Einv x - (S m₀).Einv x = (S m).Einv ((S m₀).E z - (S m).E z) := by
      rw [map_sub, hz]
      simp [z]
    rw [e]
    exact ((S m).Einv.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hEinv m))
  refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
  have := tendsto_iff_norm_sub_tendsto_zero.1 ((hE z).tendsto m₀)
  simpa only [norm_sub_rev] using this

omit [∀ j, CompleteSpace (W j)] in
lemma continuous_vOf (S : P → System V W) (hS : ∀ m, (S m).Bounds β δ γ r) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hEinv : ∀ x, Continuous fun m => (S m).Einv x)
    (hB : ∀ j w, Continuous fun m => (S m).B j w) {b : P → ∀ j, W j}
    (hb : ∀ i, Continuous fun m => b m i) {N : ℝ} (hbN : ∀ m, WBound θ (b m) N) (j : ℕ) :
    Continuous fun m => (S m).vOf (b m) j := by
  refine Continuous.neg (continuous_tsum (fun k => ?_)
    ((summable_geometric_of_lt_one hθ0 hθ1).mul_left (β * N * θ ^ j))
    (fun k m => (hS m).norm_term_le (hbN m) j k))
  exact continuous_pow_clm_apply (fun m => (S m).Einv) (fun m => (hS m).norm_Einv_le) hEinv _
    (continuous_clm_apply (fun m => (S m).B (j + k)) (fun m => (hS m).norm_B_le _) (hB _)
      (hb (j + k)))

/-- **Continuous dependence on parameters.** Let `S m` be a family of systems, depending on a
parameter `m` in a topological space, satisfying the hypotheses of the stable manifold theorem
with constants independent of `m`, such that `E`, `B_j`, `D_j` are strongly continuous in `m`
and `g_j x` is continuous in `m` for each `x` in the `r`-ball. Then for a continuous family of
initial data with `‖w₀ m‖ ≤ ρ`, the stable manifold `m ↦ (S m).stableMap (w₀ m)` is
continuous. -/
theorem continuous_stableMap (S : P → System V W) (hS : ∀ m, (S m).Bounds β δ γ r)
    (hc : Admissible β δ γ r θ R)
    (hE : ∀ x, Continuous fun m => (S m).E x)
    (hB : ∀ j w, Continuous fun m => (S m).B j w)
    (hD : ∀ j w, Continuous fun m => (S m).D j w)
    (hg : ∀ j x, ‖x‖ ≤ r → Continuous fun m => (S m).g j x)
    {w₀ : P → W 0} (hw₀ : Continuous w₀) (hw : ∀ m, ‖w₀ m‖ ≤ rho β δ θ R) :
    Continuous fun m => (S m).stableMap (w₀ m) := by
  have hθ := hc.theta_pos
  have h1K := hc.one_sub_contr_pos
  have hEinv := continuous_Einv_apply S (fun m => (hS m).norm_Einv_le) hE
  set N := rho β δ θ R / (1 - contr β δ γ θ R)
  have hpN : ∀ n m, WBound θ ((S m).picard (w₀ m) n) N := fun n m =>
    (((hS m).fixed hc (hw m)).2.2.2 n).mono (div_le_div_of_nonneg_right (hw m) h1K.le) hθ.le
  have hfN : ∀ m, WBound θ ((S m).fixedSeq (w₀ m)) N := fun m =>
    ((hS m).fixed hc (hw m)).1.mono (div_le_div_of_nonneg_right (hw m) h1K.le) hθ.le
  have hglip : ∀ j m, ∀ x ∈ closedBall (0 : V × W j) r, ∀ y ∈ closedBall (0 : V × W j) r,
      dist ((S m).g j x) ((S m).g j y) ≤ γ * r * dist x y := by
    intro j m x hx y hy
    rw [mem_closedBall_zero_iff] at hx hy
    rw [dist_eq_norm, dist_eq_norm]
    exact ((hS m).g_lipschitz j x y hx hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (max_le hx hy) hc.gamma_nonneg) (norm_nonneg _))
  have hpc : ∀ n j, Continuous fun m => (S m).picard (w₀ m) n j := by
    intro n
    induction n with
    | zero => intro j; simpa using continuous_const (y := (0 : W j))
    | succ n ih =>
      intro j
      cases j with
      | zero => simpa [System.picard_succ] using hw₀
      | succ j =>
        simp only [System.picard_succ, System.F_succ]
        refine Continuous.add (continuous_clm_apply (fun m => (S m).D j)
          (fun m => (hS m).norm_D_le j) (hD j) (ih j)) ?_
        refine continuous_apply_of_lipschitz (fun m x => (S m).g j x) (closedBall 0 r) (γ * r)
          (hglip j) (fun x hx => hg j x (mem_closedBall_zero_iff.1 hx))
          ((continuous_vOf S hS hθ.le hc.theta_lt hEinv hB ih (hpN n) j).prodMk (ih j))
          (fun m => ?_)
        exact mem_closedBall_zero_iff.2 ((hS m).pair_le_R hc (((hS m).fixed hc (hw m)).2.2.2 n)
          (hc.cst_mul_le (norm_nonneg _) (hw m)) j |>.trans hc.R_le)
  have hfc : ∀ j, Continuous fun m => (S m).fixedSeq (w₀ m) j := fun j =>
    (tendstoUniformlyOn_univ.1 (tendstoUniformlyOn_of_dist_le (hc.tendsto_rate j)
      (fun n m _ => (hS m).dist_picard_fixedSeq_le hc (hw m) n j))).continuous
      (Frequently.of_forall fun n => hpc n j)
  exact continuous_vOf S hS hθ.le hc.theta_lt hEinv hB hfc hfN 0

end Parameter

end Flow
