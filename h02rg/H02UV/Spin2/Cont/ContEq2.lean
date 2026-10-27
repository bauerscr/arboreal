import Spin2.Cont.ContLimit
import Cont.AscoliOn

/-!
# B3, `r`-dependent form: subsequential limits on `{‖x‖ ≥ r}` given equicontinuity there

* `ClEquiOn f r`: `ClEqui` restricted to one radius, i.e. asymptotic equicontinuity on
  `{‖x‖ ≥ r}`; `clEqui_iff_on`: `ClEqui f ↔ ∀ r > 0, ClEquiOn f r`.
* `t6_sym_tendsto_on`: under `ClEquiOn f r`, `f_N(σx) − f_N(x) → 0` for `‖x‖ > r`.
* **`thm_limit_of_equiOn`**: the prefix of `thm_limit_of_equi`; for every `r > 0` and every
  admissible sequence with `ClEquiOn (clF L βR b) r`, a subsequence converges uniformly on
  `{‖x‖ ≥ r}` to a `G` uniformly continuous there, with `G ≥ 0`, point-group invariance on
  `{‖x‖ > r}`, a bound, and the short-distance law on `{‖x‖ ≥ r, |x| < δ₀}`.
* **`thm_limit_of_equiAnn`**: if `ClEquiOn (clF L βR b) r` for every `r > r₀ ≥ 0`, a subsequence
  converges uniformly on compacts of `{‖x‖ > r₀}` to a `G` continuous there (same properties).
-/

set_option autoImplicit false

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Filter Topology

/-- Asymptotic equicontinuity on `{‖x‖ ≥ r}` (one radius). -/
def ClEquiOn (f : ℕ → UnitAddTorus (Fin 2) → ℝ) (r : ℝ) : Prop :=
  ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y,
    r ≤ dist x 0 → r ≤ dist y 0 → dist x y < δ → |f N x - f N y| ≤ η

theorem clEqui_iff_on (f : ℕ → UnitAddTorus (Fin 2) → ℝ) : ClEqui f ↔ ∀ r > 0, ClEquiOn f r :=
  Iff.rfl

theorem ClEquiOn.mono {f : ℕ → UnitAddTorus (Fin 2) → ℝ} {r r' : ℝ} (h : ClEquiOn f r)
    (hr : r ≤ r') : ClEquiOn f r' := fun η hη => by
  obtain ⟨δ, hδ, N₀, hN⟩ := h η hη
  exact ⟨δ, hδ, N₀, fun N hN' x y hx hy hxy => hN N hN' x y (hr.trans hx) (hr.trans hy) hxy⟩

variable {L : ℕ} [NeZero L]

/-- Under `ClEquiOn f r`: `f_N(σx) − f_N(x) → 0` for `‖x‖ > r`. -/
lemma t6_sym_tendsto_on (hL : 2 ≤ L) {βR r : ℝ} {b : ℕ → ℝ} (hE : ClEquiOn (clF L βR b) r)
    (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) {x : UnitAddTorus (Fin 2)} (hx : r < ‖x‖) :
    Tendsto (fun N => clF L βR b N (clSgn τ s x) - clF L βR b N x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, N₂, hN₂⟩ := hE (η / 2) (by positivity)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1
    (t6_eventually_small hL (show 0 < min δ (‖x‖ - r) by
      exact lt_min hδ (by linarith)))
  refine ⟨max N₂ N₃, fun N hN => ?_⟩
  have hs := hN₃ N ((le_max_right _ _).trans hN)
  set z := latPtN L N x
  set y := latEmb (L ^ N) (Ward.sgnPerm 2 L N τ s z)
  have hfy : clF L βR b N y = clF L βR b N x := by
    unfold clF
    have : latPtN L N y = Ward.sgnPerm 2 L N τ s z := latPt_latEmb _ _
    rw [this, Pconn_sgnPerm]
  have hd : dist (clSgn τ s x) y ≤ 1 / (2 * (L : ℝ) ^ N) := by
    rw [show y = clSgn τ s (latEmb (L ^ N) z) from t6_latEmb_sgnPerm N τ s z, dist_clSgn,
      dist_comm]
    have := dist_latEmb_latPt_le (L ^ N) x
    push_cast at this; exact this
  have hdy : r ≤ dist y 0 := by
    rw [dist_zero_right]
    have h1 := norm_le_insert' (clSgn τ s x) y
    rw [norm_clSgn, ← dist_eq_norm] at h1
    have : 1 / (2 * (L : ℝ) ^ N) < ‖x‖ - r := hs.trans_le (min_le_right _ _)
    linarith
  have hσ : r ≤ dist (clSgn τ s x) 0 := by
    rw [dist_zero_right, norm_clSgn]; linarith
  have := hN₂ N ((le_max_left _ _).trans hN) _ _ hσ hdy
    (hd.trans_lt (hs.trans_le (min_le_left _ _)))
  rw [hfy] at this
  rw [Real.dist_eq, sub_zero]
  linarith

/-- The short-distance law at a limit point (shared by the two theorems below). -/
lemma t6_short_at {M : MasterFacts L} {N₀ : ℕ} {βR δ₀ K' : ℝ} (hL : 2 ≤ L)
    {R : ∀ N, RGPar 2 L N} {m b : ℕ → ℝ} (hA : ClAdm M N₀ βR R m b)
    (hlim : ∀ (Pk ℓk : ℕ → ℝ) (G ℓ : ℝ), 0 < ℓ → ℓ < δ₀ → Tendsto Pk atTop (𝓝 G) →
        Tendsto ℓk atTop (𝓝 ℓ) → (∀ᶠ k in atTop, CsPtX M N₀ βR (Pk k) (ℓk k)) →
        |G - csA βR ℓ| ≤ K' * csA βR ℓ * csRate ℓ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {G : UnitAddTorus (Fin 2) → ℝ} {x : UnitAddTorus (Fin 2)}
    (hx : x ≠ 0) (hxδ : torusNorm x < δ₀)
    (hpt : Tendsto (fun k => clF L βR b (φ k) x) atTop (𝓝 (G x))) :
    |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine hlim (fun k => clF L βR b (φ k) x)
    (fun k => eucl (latPtN L (φ k) x) / (L : ℝ) ^ (φ k)) (G x) (torusNorm x)
    (t6_torusNorm_pos hx) hxδ hpt ((t6_eucl_tendsto hL x).comp hφ.tendsto_atTop) ?_
  have h1 := hφ.tendsto_atTop.eventually (t6_eventually_small hL (show 0 < ‖x‖ / 2 by positivity))
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N₀), h1] with k hk hk2
  exact t6_csPtX hA hk (t6_latPt_far hL (φ k) x hk2.le hx0).1

/-- **Subsequential limits on `{‖x‖ ≥ r}`, given equicontinuity there.** Same constants as
`thm_limit_of_equi`. -/
theorem thm_limit_of_equiOn : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∀ r : ℝ, 0 < r → ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), ClAdm M N₀ βR R m b →
      ClEquiOn (clF L βR b) r →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ,
      UniformContinuousOn G {x | r ≤ dist x 0} ∧
      TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop {x | r ≤ dist x 0} ∧
      (∀ x, r ≤ ‖x‖ → 0 ≤ G x) ∧
      (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, r < ‖x‖ → G (clSgn τ s x) = G x) ∧
      (∃ C, ∀ x, r ≤ ‖x‖ → G x ≤ C) ∧
      (∀ x, r ≤ ‖x‖ → torusNorm x < δ₀ →
        |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  obtain ⟨L₀, h⟩ := t6_short_bound
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨M, g₀, N₀, hg, hF⟩ := h L ((le_max_left _ _).trans hL)
  refine ⟨M, g₀, N₀, hg, fun βR hβR hy => ?_⟩
  obtain ⟨hB, δ₀, K', hδ₀, hδ₁, hK', -, hlim⟩ := hF βR hβR hy
  refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun r hr R m b hA hE => ?_⟩
  have hbd := t6_bdd hL2 hβR hA hB
  have hKc : IsCompact {x : UnitAddTorus (Fin 2) | r ≤ dist x 0} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  obtain ⟨C, hC⟩ := hbd r hr
  obtain ⟨φ, hφ, G, hGc, hGu⟩ := ascoli_asymp_exists_subseq_on _ hKc (clF L βR b)
    ⟨C, fun N x hx => hC N x hx⟩
    (fun η hη => by
      obtain ⟨δ, hδ, N₁, hN₁⟩ := hE η hη
      exact ⟨δ, hδ, N₁, fun N hN x hx y hy hxy => hN₁ N hN x y hx hy hxy⟩)
  have hpt : ∀ x : UnitAddTorus (Fin 2), r ≤ ‖x‖ →
      Tendsto (fun k => clF L βR b (φ k) x) atTop (𝓝 (G x)) := fun x hx =>
    hGu.tendsto_at (show r ≤ dist x 0 by rwa [dist_zero_right])
  have hne : ∀ x : UnitAddTorus (Fin 2), r ≤ ‖x‖ → x ≠ 0 := fun x hx h0 => by
    rw [h0, norm_zero] at hx; linarith
  refine ⟨φ, hφ, G, hGc, hGu, ?_, ?_, ⟨C, ?_⟩, ?_⟩
  · intro x hx
    refine ge_of_tendsto (hpt x hx) ?_
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N₀)] with k hk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb0⟩ := hA (φ k) hk
    exact t6_clF_nonneg hβR hb0 x
  · intro τ s x hx
    exact ascoli_asymp_limit_eq_of_tendsto_sub hφ (hpt x hx.le)
      (hpt _ (by rw [norm_clSgn]; exact hx.le)) (t6_sym_tendsto_on hL2 hE τ s hx)
  · intro x hx
    refine le_of_tendsto (hpt x hx) (Eventually.of_forall fun k => ?_)
    exact (le_abs_self _).trans (hC _ x (by rwa [dist_zero_right]))
  · intro x hx hxδ
    exact t6_short_at hL2 hA hlim hφ (hne x hx) hxδ (hpt x hx)

/-- **Subsequential limits on `{‖x‖ > r₀}`, given equicontinuity on every `{‖x‖ ≥ r}`, `r > r₀`.**
For `r₀ = 0` this is `thm_limit_of_equi`. -/
theorem thm_limit_of_equiAnn : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∀ r₀ : ℝ, 0 ≤ r₀ → ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), ClAdm M N₀ βR R m b →
      (∀ r > r₀, ClEquiOn (clF L βR b) r) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ,
      ContinuousOn G {x | r₀ < dist x 0} ∧
      (∀ K ⊆ {x : UnitAddTorus (Fin 2) | r₀ < dist x 0}, IsCompact K →
        TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop K) ∧
      (∀ x, r₀ < ‖x‖ → 0 ≤ G x) ∧
      (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, r₀ < ‖x‖ → G (clSgn τ s x) = G x) ∧
      (∀ δ > r₀, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
      (∀ x, r₀ < ‖x‖ → torusNorm x < δ₀ →
        |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  obtain ⟨L₀, h⟩ := t6_short_bound
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨M, g₀, N₀, hg, hF⟩ := h L ((le_max_left _ _).trans hL)
  refine ⟨M, g₀, N₀, hg, fun βR hβR hy => ?_⟩
  obtain ⟨hB, δ₀, K', hδ₀, hδ₁, hK', -, hlim⟩ := hF βR hβR hy
  refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun r₀ hr₀ R m b hA hE => ?_⟩
  have hbd := t6_bdd hL2 hβR hA hB
  obtain ⟨φ, hφ, G, hGc, -, hGu⟩ := ascoli_asymp_exists_subseq_annulus (0 : UnitAddTorus (Fin 2))
    r₀ (clF L βR b) (fun r hr => hbd r (lt_of_le_of_lt hr₀ hr)) (fun r hr => hE r hr)
  have hpt : ∀ x : UnitAddTorus (Fin 2), r₀ < ‖x‖ →
      Tendsto (fun k => clF L βR b (φ k) x) atTop (𝓝 (G x)) := by
    intro x hx
    have hK : ({x} : Set (UnitAddTorus (Fin 2))) ⊆ {x | r₀ < dist x 0} := by
      intro y hy; rw [Set.mem_singleton_iff.1 hy]; show r₀ < dist x 0; rwa [dist_zero_right]
    exact (hGu _ hK isCompact_singleton).tendsto_at (Set.mem_singleton x)
  have hne : ∀ x : UnitAddTorus (Fin 2), r₀ < ‖x‖ → x ≠ 0 := fun x hx h0 => by
    rw [h0, norm_zero] at hx; linarith
  refine ⟨φ, hφ, G, hGc, hGu, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ge_of_tendsto (hpt x hx) ?_
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N₀)] with k hk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb0⟩ := hA (φ k) hk
    exact t6_clF_nonneg hβR hb0 x
  · intro τ s x hx
    have hr : r₀ < (r₀ + ‖x‖) / 2 := by linarith
    exact ascoli_asymp_limit_eq_of_tendsto_sub hφ (hpt x hx)
      (hpt _ (by rw [norm_clSgn]; exact hx))
      (t6_sym_tendsto_on hL2 (hE _ hr) τ s (by linarith))
  · intro δ hδ
    obtain ⟨C, hC⟩ := hbd δ (lt_of_le_of_lt hr₀ hδ)
    refine ⟨C, fun x hx => ?_⟩
    refine le_of_tendsto (hpt x (lt_of_lt_of_le hδ hx)) (Eventually.of_forall fun k => ?_)
    exact (le_abs_self _).trans (hC _ x (by rwa [dist_zero_right]))
  · intro x hx hxδ
    exact t6_short_at hL2 hA hlim hφ (hne x hx) hxδ (hpt x hx)

end

end Spin2
