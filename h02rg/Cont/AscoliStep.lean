import Mathlib

/-!
# Asymptotic Arzelà–Ascoli (B3, task T7)

For a sequence `f N : X → ℝ` of (not necessarily continuous) functions on a compact
(pseudo)metric space that is uniformly bounded and *asymptotically equicontinuous*,
`∀ η > 0, ∃ δ > 0, ∃ N₀, ∀ N ≥ N₀, dist x y < δ → |f N x - f N y| ≤ η`,
there is a subsequence converging uniformly to a uniformly continuous limit.

Main results:
* `ascoli_asymp_finite_net` : for every `ε > 0` finitely many indices `I` with every `f N`
  `ε`-close in sup norm to some `f i`, `i ∈ I`;
* `ascoli_asymp_totallyBounded` : the range of `N ↦ f N` is totally bounded in `X →ᵤ ℝ`;
* `ascoli_asymp_uniformContinuous_of_tendstoUniformly` : uniform limits of asymptotically
  equicontinuous sequences are uniformly continuous;
* `ascoli_asymp_exists_subseq` : the compact-space theorem;
* `ascoli_asymp_exists_subseq_exhaust` : the version for a sequence of compact sets `K n`
  (one subsequence for all `n`; no explicit diagonal argument: Tychonoff in the countable
  product `∀ n, K n →ᵤ ℝ`, which is first countable);
* `ascoli_asymp_exists_subseq_punctured` : the version on `X ∖ {x₀}` for a compact metric
  space (e.g. `UnitAddTorus (Fin 2) ∖ {0}`, `ascoli_asymp_exists_subseq_torus`), with
  hypotheses on `{r ≤ dist x x₀}` for each `r > 0`; the limit is continuous on `{x₀}ᶜ` and the
  convergence is uniform on compact subsets of `{x₀}ᶜ`;
* `ascoli_asymp_limit_eq_of_tendsto_sub`, `ascoli_asymp_limit_abs_sub_le` : limits along a
  subsequence inherit asymptotic symmetries and pointwise bounds `|f N x - h| ≤ e + o(1)`.

The proof of total boundedness: with `δ, N₀` from the modulus at `ε/4` and a finite `δ`-net
`t` of `X`, the vectors `(f N s)_{s ∈ t}`, `N ≥ N₀`, lie in a bounded set of `t → ℝ`, hence
have a finite `ε/2`-net among themselves; the indices `N < N₀` are finitely many.
-/

namespace Cont

open Filter Topology Set Metric
open scoped UniformConvergence

section AscoliAsymp

variable {X : Type*} [PseudoMetricSpace X]

/-- Finite sup-norm nets of indices for a bounded asymptotically equicontinuous sequence. -/
theorem ascoli_asymp_finite_net [CompactSpace X] (f : ℕ → X → ℝ) (C : ℝ)
    (hb : ∀ N x, |f N x| ≤ C)
    (heq : ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y, dist x y < δ → |f N x - f N y| ≤ η)
    {ε : ℝ} (hε : 0 < ε) : ∃ I : Set ℕ, I.Finite ∧ ∀ N, ∃ i ∈ I, ∀ x, |f N x - f i x| ≤ ε := by
  obtain ⟨δ, hδ, N₀, hN₀⟩ := heq (ε / 4) (by positivity)
  obtain ⟨t, -, htf, ht⟩ := finite_cover_balls_of_compact (isCompact_univ (X := X)) hδ
  haveI : Fintype t := htf.fintype
  let ev : ℕ → (t → ℝ) := fun N s => f N s
  have htb : TotallyBounded (ev '' Ici N₀) := by
    refine (isCompact_closedBall (0 : t → ℝ) |C|).totallyBounded.subset ?_
    rintro _ ⟨N, -, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg C)).2 fun s => ?_
    rw [Real.norm_eq_abs]
    exact (hb N s).trans (le_abs_self C)
  obtain ⟨u, hus, huf, hcov⟩ :=
    totallyBounded_iff_subset.1 htb _ (dist_mem_uniformity (half_pos hε))
  have hpre : ∀ v ∈ u, ∃ M, N₀ ≤ M ∧ ev M = v := fun v hv => by
    obtain ⟨M, hM, h⟩ := hus hv
    exact ⟨M, hM, h⟩
  choose! M hM hMv using hpre
  refine ⟨Iio N₀ ∪ M '' u, (finite_Iio N₀).union (huf.image M), fun N => ?_⟩
  rcases lt_or_ge N N₀ with h | h
  · exact ⟨N, Or.inl h, fun x => by simp only [sub_self, abs_zero]; positivity⟩
  · obtain ⟨v, hv, hNv⟩ := mem_iUnion₂.1 (hcov ⟨N, h, rfl⟩)
    refine ⟨M v, Or.inr ⟨v, hv, rfl⟩, fun x => ?_⟩
    obtain ⟨s, hst, hxs⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 := hN₀ N h x s hxs
    have h2 := hN₀ (M v) (hM v hv) x s hxs
    have h3 : |f N s - f (M v) s| ≤ ε / 2 := by
      have hd : dist (ev N) (ev (M v)) < ε / 2 := by rw [hMv v hv]; exact hNv
      have := (dist_le_pi_dist (ev N) (ev (M v)) ⟨s, hst⟩).trans hd.le
      simpa only [ev, Real.dist_eq] using this
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- Total boundedness of the range in the space `X →ᵤ ℝ` of uniform convergence. -/
theorem ascoli_asymp_totallyBounded [CompactSpace X] (f : ℕ → X → ℝ) (C : ℝ)
    (hb : ∀ N x, |f N x| ≤ C)
    (heq : ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y, dist x y < δ → |f N x - f N y| ≤ η) :
    TotallyBounded (range fun N => UniformFun.ofFun (f N)) := by
  intro d hd
  obtain ⟨ε, hε, hεd⟩ :=
    (UniformFun.hasBasis_uniformity_of_basis X ℝ Metric.uniformity_basis_dist).mem_iff.1 hd
  obtain ⟨I, hIf, hI⟩ := ascoli_asymp_finite_net f C hb heq (half_pos hε)
  refine ⟨(fun i => UniformFun.ofFun (f i)) '' I, hIf.image _, ?_⟩
  rintro _ ⟨N, rfl⟩
  obtain ⟨i, hi, hNi⟩ := hI N
  refine mem_iUnion₂.2 ⟨_, ⟨i, hi, rfl⟩, hεd fun x => ?_⟩
  change dist (f N x) (f i x) < ε
  rw [Real.dist_eq]
  linarith [hNi x]

/-- Uniform limits of asymptotically equicontinuous sequences are uniformly continuous. -/
theorem ascoli_asymp_uniformContinuous_of_tendstoUniformly (F : ℕ → X → ℝ) (g : X → ℝ)
    (heq : ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y, dist x y < δ → |F N x - F N y| ≤ η)
    (hu : TendstoUniformly F g atTop) : UniformContinuous g := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, N₀, hN₀⟩ := heq (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {x y} hxy => ?_⟩
  obtain ⟨n, hn1, hn2⟩ :=
    ((Metric.tendstoUniformly_iff.1 hu (ε / 8) (by positivity)).and
      (eventually_ge_atTop N₀)).exists
  have h1 := hn1 x
  have h2 := hn1 y
  have h3 := hN₀ n hn2 x y hxy
  rw [Real.dist_eq] at h1 h2 ⊢
  rw [abs_lt] at h1 h2 ⊢
  rw [abs_le] at h3
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **Asymptotic Arzelà–Ascoli** on a compact space. -/
theorem ascoli_asymp_exists_subseq [CompactSpace X] (f : ℕ → X → ℝ) (C : ℝ)
    (hb : ∀ N x, |f N x| ≤ C)
    (heq : ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y, dist x y < δ → |f N x - f N y| ≤ η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ, UniformContinuous g ∧
      TendstoUniformly (fun n => f (φ n)) g atTop := by
  have hK : IsCompact (closure (range fun N => UniformFun.ofFun (f N))) :=
    isCompact_iff_totallyBounded_isComplete.2
      ⟨(ascoli_asymp_totallyBounded f C hb heq).closure, isClosed_closure.isComplete⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun N => subset_closure (mem_range_self N))
  have hu : TendstoUniformly (fun n => f (φ n)) (UniformFun.toFun a) atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.1 hlim
  refine ⟨φ, hφ, _, ascoli_asymp_uniformContinuous_of_tendstoUniformly _ _ ?_ hu, hu⟩
  intro η hη
  obtain ⟨δ, hδ, N₀, hN₀⟩ := heq η hη
  exact ⟨δ, hδ, N₀, fun n hn x y hxy => hN₀ (φ n) (hn.trans (hφ.id_le n)) x y hxy⟩

/-- **Asymptotic Arzelà–Ascoli** for a sequence of compact sets: a single subsequence converges
uniformly on every `K n`, to a limit that is uniformly continuous on every `K n`. -/
theorem ascoli_asymp_exists_subseq_exhaust (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (f : ℕ → X → ℝ) (hb : ∀ n, ∃ C, ∀ N, ∀ x ∈ K n, |f N x| ≤ C)
    (heq : ∀ n, ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K n, ∀ y ∈ K n,
      dist x y < δ → |f N x - f N y| ≤ η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ, ∀ n,
      UniformContinuousOn g (K n) ∧ TendstoUniformlyOn (fun m => f (φ m)) g atTop (K n) := by
  haveI : ∀ n, CompactSpace (K n) := fun n => isCompact_iff_compactSpace.1 (hK n)
  let fn : ∀ n, ℕ → K n → ℝ := fun n N x => f N x
  have hbn : ∀ n, ∃ C, ∀ N (x : K n), |fn n N x| ≤ C := fun n => by
    obtain ⟨C, hC⟩ := hb n
    exact ⟨C, fun N x => hC N x x.2⟩
  have heqn : ∀ n, ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y : K n,
      dist x y < δ → |fn n N x - fn n N y| ≤ η := fun n η hη => by
    obtain ⟨δ, hδ, N₀, hN₀⟩ := heq n η hη
    exact ⟨δ, hδ, N₀, fun N hN x y hxy => hN₀ N hN x x.2 y y.2 hxy⟩
  let S : ∀ n, Set (K n →ᵤ ℝ) := fun n => closure (range fun N => UniformFun.ofFun (fn n N))
  have hS : ∀ n, IsCompact (S n) := fun n => by
    obtain ⟨C, hC⟩ := hbn n
    exact isCompact_iff_totallyBounded_isComplete.2
      ⟨(ascoli_asymp_totallyBounded (fn n) C hC (heqn n)).closure, isClosed_closure.isComplete⟩
  let F : ℕ → ∀ n, K n →ᵤ ℝ := fun N n => UniformFun.ofFun (fn n N)
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_univ_pi hS).tendsto_subseq (x := F)
    (fun N => fun n _ => subset_closure (mem_range_self N))
  have hu : ∀ n, TendstoUniformly (fun m => fn n (φ m)) (UniformFun.toFun (a n)) atTop :=
    fun n => UniformFun.tendsto_iff_tendstoUniformly.1 (tendsto_pi_nhds.1 hlim n)
  have hpt : ∀ n x (hx : x ∈ K n),
      Tendsto (fun m => f (φ m) x) atTop (𝓝 (UniformFun.toFun (a n) ⟨x, hx⟩)) :=
    fun n x hx => (hu n).tendsto_at ⟨x, hx⟩
  classical
  let g : X → ℝ := fun x =>
    if h : ∃ n, x ∈ K n then UniformFun.toFun (a (Nat.find h)) ⟨x, Nat.find_spec h⟩ else 0
  have hg : ∀ n x (hx : x ∈ K n), g x = UniformFun.toFun (a n) ⟨x, hx⟩ := fun n x hx => by
    have h : ∃ n, x ∈ K n := ⟨n, hx⟩
    simp only [g, dif_pos h]
    exact tendsto_nhds_unique (hpt _ x (Nat.find_spec h)) (hpt n x hx)
  have hgc : ∀ n, (K n).restrict g = UniformFun.toFun (a n) := fun n => by
    funext x
    exact hg n x x.2
  refine ⟨φ, hφ, g, fun n => ⟨?_, ?_⟩⟩
  · rw [uniformContinuousOn_iff_restrict, hgc n]
    refine ascoli_asymp_uniformContinuous_of_tendstoUniformly _ _ ?_ (hu n)
    intro η hη
    obtain ⟨δ, hδ, N₀, hN₀⟩ := heqn n η hη
    exact ⟨δ, hδ, N₀, fun m hm x y hxy => hN₀ (φ m) (hm.trans (hφ.id_le m)) x y hxy⟩
  · rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have : g ∘ ((↑) : K n → X) = UniformFun.toFun (a n) := hgc n
    rw [this]
    exact hu n

end AscoliAsymp

section AscoliPunctured

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Asymptotic Arzelà–Ascoli** on `X ∖ {x₀}` for a compact metric space: hypotheses on each
`{r ≤ dist x x₀}`, `r > 0`; the limit is continuous on `{x₀}ᶜ`, uniformly continuous on each
`{r ≤ dist x x₀}`, and the convergence is uniform on every compact subset of `{x₀}ᶜ`. -/
theorem ascoli_asymp_exists_subseq_punctured (x₀ : X) (f : ℕ → X → ℝ)
    (hb : ∀ r > 0, ∃ C, ∀ N x, r ≤ dist x x₀ → |f N x| ≤ C)
    (heq : ∀ r > 0, ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y,
      r ≤ dist x x₀ → r ≤ dist y x₀ → dist x y < δ → |f N x - f N y| ≤ η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ, ContinuousOn g {x₀}ᶜ ∧
      (∀ r > 0, UniformContinuousOn g {x | r ≤ dist x x₀}) ∧
      ∀ K ⊆ ({x₀}ᶜ : Set X), IsCompact K → TendstoUniformlyOn (fun m => f (φ m)) g atTop K := by
  let K : ℕ → Set X := fun n => {x | 1 / ((n : ℝ) + 1) ≤ dist x x₀}
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hK : ∀ n, IsCompact (K n) := fun n =>
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  obtain ⟨φ, hφ, g, hg⟩ := ascoli_asymp_exists_subseq_exhaust K hK f
    (fun n => by
      obtain ⟨C, hC⟩ := hb _ (hpos n)
      exact ⟨C, fun N x hx => hC N x hx⟩)
    (fun n η hη => by
      obtain ⟨δ, hδ, N₀, hN₀⟩ := heq _ (hpos n) η hη
      exact ⟨δ, hδ, N₀, fun N hN x hx y hy hxy => hN₀ N hN x y hx hy hxy⟩)
  -- every `{r ≤ dist x x₀}` lies in some `K n`
  have hsub : ∀ r > 0, ∃ n, {x | r ≤ dist x x₀} ⊆ K n := fun r hr => by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    exact ⟨n, fun x hx => hn.le.trans hx⟩
  have huc : ∀ r > 0, UniformContinuousOn g {x | r ≤ dist x x₀} := fun r hr => by
    obtain ⟨n, hn⟩ := hsub r hr
    exact (hg n).1.mono hn
  refine ⟨φ, hφ, g, ?_, huc, ?_⟩
  · intro x hx
    have hx0 : 0 < dist x x₀ := dist_pos.2 hx
    have hmem : {y | dist x x₀ / 2 ≤ dist y x₀} ∈ 𝓝 x := by
      refine mem_of_superset ((isOpen_lt continuous_const
        (continuous_id.dist continuous_const)).mem_nhds (show dist x x₀ / 2 < dist x x₀ by
          linarith)) fun y (hy : dist x x₀ / 2 < dist y x₀) =>
        (show dist x x₀ / 2 ≤ dist y x₀ from hy.le)
    exact ((huc _ (half_pos hx0)).continuousOn.continuousAt hmem).continuousWithinAt
  · intro L hL hLc
    rcases L.eq_empty_or_nonempty with rfl | hne
    · exact tendstoUniformlyOn_empty
    obtain ⟨x₁, hx₁, hmin⟩ := hLc.exists_isMinOn hne (continuous_id.dist continuous_const).continuousOn
    obtain ⟨n, hn⟩ := hsub (dist x₁ x₀) (dist_pos.2 (hL hx₁))
    exact (hg n).2.mono fun y hy => hn (hmin hy)

/-- The torus instance `𝕋² ∖ {0}`, `𝕋² = UnitAddTorus (Fin 2)`. -/
theorem ascoli_asymp_exists_subseq_torus (f : ℕ → UnitAddTorus (Fin 2) → ℝ)
    (hb : ∀ r > 0, ∃ C, ∀ N x, r ≤ dist x 0 → |f N x| ≤ C)
    (heq : ∀ r > 0, ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y,
      r ≤ dist x 0 → r ≤ dist y 0 → dist x y < δ → |f N x - f N y| ≤ η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : UnitAddTorus (Fin 2) → ℝ, ContinuousOn g {0}ᶜ ∧
      (∀ r > 0, UniformContinuousOn g {x | r ≤ dist x 0}) ∧
      ∀ K ⊆ ({0}ᶜ : Set (UnitAddTorus (Fin 2))), IsCompact K →
        TendstoUniformlyOn (fun m => f (φ m)) g atTop K :=
  ascoli_asymp_exists_subseq_punctured 0 f hb heq

end AscoliPunctured

section AscoliInherit

variable {X : Type*}

/-- Limits along a subsequence inherit asymptotic symmetries: if `f N y - f N x → 0` then
`g y = g x` (apply with `y = σ x` for a symmetry `σ`). -/
theorem ascoli_asymp_limit_eq_of_tendsto_sub {f : ℕ → X → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {g : X → ℝ} {x y : X} (hx : Tendsto (fun m => f (φ m) x) atTop (𝓝 (g x)))
    (hy : Tendsto (fun m => f (φ m) y) atTop (𝓝 (g y)))
    (hxy : Tendsto (fun N => f N y - f N x) atTop (𝓝 0)) : g y = g x := by
  have h1 := hy.sub hx
  have h2 : Tendsto (fun m => f (φ m) y - f (φ m) x) atTop (𝓝 0) :=
    hxy.comp hφ.tendsto_atTop
  exact sub_eq_zero.1 (tendsto_nhds_unique h1 h2)

/-- Symmetry under a map `σ`, for a subsequence converging uniformly on a set `K` with
`σ '' K ⊆ K`. -/
theorem ascoli_asymp_limit_invariant {f : ℕ → X → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {g : X → ℝ} {K : Set X} (hu : TendstoUniformlyOn (fun m => f (φ m)) g atTop K)
    (σ : X → X) (hσ : ∀ x ∈ K, σ x ∈ K)
    (hsym : ∀ x ∈ K, Tendsto (fun N => f N (σ x) - f N x) atTop (𝓝 0)) :
    ∀ x ∈ K, g (σ x) = g x := fun x hx =>
  ascoli_asymp_limit_eq_of_tendsto_sub hφ (hu.tendsto_at hx) (hu.tendsto_at (hσ x hx))
    (hsym x hx)

/-- Limits along a subsequence inherit pointwise bounds `|f N x - h| ≤ e + o(1)`. -/
theorem ascoli_asymp_limit_abs_sub_le {f : ℕ → X → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {g : X → ℝ} {x : X} (hx : Tendsto (fun m => f (φ m) x) atTop (𝓝 (g x))) {h e : ℝ}
    (hfx : ∀ ε > 0, ∀ᶠ N in atTop, |f N x - h| ≤ e + ε) : |g x - h| ≤ e := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact le_of_tendsto (hx.sub_const h).abs (hφ.tendsto_atTop.eventually (hfx ε hε))

end AscoliInherit

end Cont
