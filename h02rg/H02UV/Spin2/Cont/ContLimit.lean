import Spin2.Cont.ContLimit1

/-!
# B3, T6 (c): the subsequential limit theorem, given asymptotic equicontinuity

See the header of `Spin2/Cont/ContLimit1.lean`. Main result: **`thm_limit_of_equi`**.
-/

set_option autoImplicit false

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Filter Topology

/-- `f_N(x) = ϑ_ε^{-2}P_ε(latPtN x)` on `𝕋²`, `P_ε = P_{1/b_N}[0 ↔ ·]`. -/
def clF (L : ℕ) [NeZero L] (βR : ℝ) (b : ℕ → ℝ) (N : ℕ) (x : UnitAddTorus (Fin 2)) : ℝ :=
  Pconn L N (1 / b N) (latPtN L N x) / thetaEpsSq βR (b N)

/-- Asymptotic equicontinuity on every `{‖x‖ ≥ r}` (hypothesis of
`ascoli_asymp_exists_subseq_torus`). -/
def ClEqui (f : ℕ → UnitAddTorus (Fin 2) → ℝ) : Prop :=
  ∀ r > 0, ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y,
    r ≤ dist x 0 → r ≤ dist y 0 → dist x y < δ → |f N x - f N y| ≤ η

/-- Admissible sequences: for `N ≥ N₀`, master parameters `R N`, a mass `m_N` in the window and
`b_N > 0` in the bracket. -/
def ClAdm {L : ℕ} [NeZero L] (M : MasterFacts L) (N₀ : ℕ) (βR : ℝ) (R : ∀ N, RGPar 2 L N)
    (m b : ℕ → ℝ) : Prop :=
  ∀ N, N₀ ≤ N → ∃ (_ : Fact (0 < (R N).ℓ)) (_ : Fact (0 < (R N).A)), (R N).P = Pc ∧
    (R N).i₀ = 0 ∧ (R N).ℓ = M.core.ℓ ∧ (R N).A = M.core.A ∧ (R N).ρ = M.core.ρ ∧
    0 < m N ∧ 4 * (m N * (L : ℝ) ^ (2 * N)) ≤ 1 / βR ∧ b N ∈ ctBracket M (R N) (m N) βR ∧
    0 < b N

/-! ### Lattice points of `𝕋²` -/

section Geom

variable {L : ℕ} [NeZero L]

lemma t6_latEmb_sgnPerm (N : ℕ) (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) (z : Lam 2 L N) :
    latEmb (L ^ N) (Ward.sgnPerm 2 L N τ s z) = clSgn τ s (latEmb (L ^ N) z) := by
  funext i
  rw [latEmb_apply, Ward.sgnPerm_apply, clSgn_apply, latEmb_apply]
  split_ifs <;> simp

omit [NeZero L] in
lemma t6_pow_pos (hL : 2 ≤ L) (N : ℕ) : (0 : ℝ) < (L : ℝ) ^ N :=
  pow_pos (by exact_mod_cast (show 0 < L by omega)) N

omit [NeZero L] in
/-- `1/(2L^N) → 0`. -/
lemma t6_inv_tendsto (hL : 2 ≤ L) :
    Tendsto (fun N : ℕ => 1 / (2 * (L : ℝ) ^ N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((L : ℝ) ^ N)) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1 < L by omega))
  have h2 := (h1.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).inv_tendsto_atTop
  exact h2.congr fun N => by simp [one_div]

omit [NeZero L] in
lemma t6_eventually_small (hL : 2 ≤ L) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, 1 / (2 * (L : ℝ) ^ N) < a :=
  (t6_inv_tendsto hL).eventually (gt_mem_nhds ha)

/-- For `1/(2L^N) ≤ ‖x‖/2`: `latPtN x ≠ 0` and `|latPtN x|/L^N ≥ ‖x‖/2`. -/
lemma t6_latPt_far (hL : 2 ≤ L) (N : ℕ) (x : UnitAddTorus (Fin 2))
    (hN : 1 / (2 * (L : ℝ) ^ N) ≤ ‖x‖ / 2) (hx : 0 < ‖x‖) :
    latPtN L N x ≠ 0 ∧ ‖x‖ / 2 ≤ eucl (latPtN L N x) / (L : ℝ) ^ N := by
  have hp := t6_pow_pos hL N
  have h1 := norm_le_supNorm_latPt (L ^ N) x
  push_cast at h1
  have h2 : ‖x‖ / 2 ≤ (supNorm (latPtN L N x) : ℝ) / (L : ℝ) ^ N := by
    unfold latPtN; linarith
  refine ⟨fun h0 => ?_, h2.trans (div_le_div_of_nonneg_right (supNorm_le_eucl _) hp.le)⟩
  rw [h0, supNorm_zero] at h2
  simp at h2; linarith

/-- `|latPtN x|/L^N → |x|` (Euclidean torus norm). -/
lemma t6_eucl_tendsto (hL : 2 ≤ L) (x : UnitAddTorus (Fin 2)) :
    Tendsto (fun N : ℕ => eucl (latPtN L N x) / (L : ℝ) ^ N) atTop (𝓝 (torusNorm x)) := by
  have hc : ∀ i : Fin 2, Tendsto (fun N : ℕ =>
      (zabs ((latPtN L N x : Fin 2 → ZMod (L ^ N)) i) : ℝ) / (L : ℝ) ^ N) atTop (𝓝 ‖x i‖) := by
    intro i
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (t6_inv_tendsto hL))
    have := abs_zabs_latPt_sub_le (L ^ N) x i
    push_cast at this
    exact this
  have hs := ((hc 0).pow 2).add ((hc 1).pow 2)
  have hq := hs.sqrt
  refine hq.congr fun N => ?_
  have hp := t6_pow_pos hL N
  unfold eucl
  rw [Fin.sum_univ_two, div_pow, div_pow, ← add_div, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hp.le]

lemma t6_torusNorm_pos {x : UnitAddTorus (Fin 2)} (hx : x ≠ 0) : 0 < torusNorm x := by
  have : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨i, hi⟩ : ∃ i, 0 < ‖x i‖ := by
    by_contra h
    push Not at h
    have : ‖x‖ ≤ 0 := (pi_norm_le_iff_of_nonneg le_rfl).2 h
    linarith
  unfold torusNorm
  refine Real.sqrt_pos.2 ?_
  have h1 : ‖x i‖ ^ 2 ≤ ∑ j : Fin 2, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [Fin.sum_univ_two] at h1
  have := pow_pos hi 2
  linarith

end Geom

/-! ### Boundedness, symmetry -/

section Main

variable {L : ℕ} [NeZero L]

lemma t6_clF_nonneg {βR : ℝ} (hβR : 0 < βR) {b : ℕ → ℝ} {N : ℕ} (hb : 0 < b N)
    (x : UnitAddTorus (Fin 2)) : 0 ≤ clF L βR b N x := by
  unfold clF thetaEpsSq
  exact div_nonneg (Pconn_mem (by positivity) _).1 (Real.rpow_nonneg (by positivity) _)

/-- A sample of `CsPtX` from an admissible sequence. -/
lemma t6_csPtX {M : MasterFacts L} {N₀ : ℕ} {βR : ℝ} {R : ∀ N, RGPar 2 L N} {m b : ℕ → ℝ}
    (hA : ClAdm M N₀ βR R m b) {N : ℕ} (hN : N₀ ≤ N) {x : UnitAddTorus (Fin 2)}
    (hx : latPtN L N x ≠ 0) :
    CsPtX M N₀ βR (clF L βR b N x) (eucl (latPtN L N x) / (L : ℝ) ^ N) := by
  obtain ⟨i1, i2, hPc, hi0, hRℓ, hRA, hRρ, hm, hmass, hb, -⟩ := hA N hN
  exact ⟨N, hN, R N, i1, i2, hPc, hi0, hRℓ, hRA, hRρ, m N, b N, hm, hmass, hb, latPtN L N x, hx,
    rfl, rfl⟩

/-- **Uniform boundedness on `{‖x‖ ≥ r}`, all `N`** (from `thm_bound_eps` for `N` large, finiteness
of the lattice for the finitely many small `N`). -/
lemma t6_bdd (hL : 2 ≤ L) {M : MasterFacts L} {N₀ : ℕ} {βR : ℝ} (hβR : 0 < βR)
    {R : ∀ N, RGPar 2 L N} {m b : ℕ → ℝ} (hA : ClAdm M N₀ βR R m b)
    (hB : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ P ℓ : ℝ, CsPtX M N₀ βR P ℓ → δ ≤ ℓ → P ≤ C) :
    ∀ r > 0, ∃ C, ∀ N x, r ≤ dist x 0 → |clF L βR b N x| ≤ C := by
  intro r hr
  obtain ⟨C₁, hC₁⟩ := hB (r / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (t6_eventually_small hL (show 0 < r / 2 by positivity))
  set N₁ := max N₀ N₂
  set F : ℕ → ℝ := fun N => ∑ z : Lam 2 L N, |Pconn L N (1 / b N) z / thetaEpsSq βR (b N)|
  refine ⟨max C₁ (∑ N ∈ Finset.range N₁, F N), fun N x hx => ?_⟩
  rw [dist_zero_right] at hx
  by_cases hN : N₁ ≤ N
  · have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
    have hN2 : N₂ ≤ N := (le_max_right _ _).trans hN
    have hs := hN₂ N hN2
    obtain ⟨hne, hl⟩ := t6_latPt_far hL N x (by linarith) (by linarith)
    have := hC₁ _ _ (t6_csPtX hA hN0 hne) (by linarith)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb0⟩ := hA N hN0
    rw [abs_of_nonneg (t6_clF_nonneg hβR hb0 x)]
    exact this.trans (le_max_left _ _)
  · push Not at hN
    refine le_trans ?_ (le_max_right _ _)
    have h1 : |clF L βR b N x| ≤ F N :=
      Finset.single_le_sum (f := fun z : Lam 2 L N => |Pconn L N (1 / b N) z /
        thetaEpsSq βR (b N)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (latPtN L N x))
    refine h1.trans (Finset.single_le_sum (f := F) (fun _ _ => ?_) (Finset.mem_range.2 hN))
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Under `ClEqui`: `f_N(σx) − f_N(x) → 0` for the point group (`Pconn_sgnPerm`, rounding
compared through `latEmb`). -/
lemma t6_sym_tendsto (hL : 2 ≤ L) {βR : ℝ} {b : ℕ → ℝ} (hE : ClEqui (clF L βR b))
    (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) {x : UnitAddTorus (Fin 2)} (hx : x ≠ 0) :
    Tendsto (fun N => clF L βR b N (clSgn τ s x) - clF L βR b N x) atTop (𝓝 0) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, N₂, hN₂⟩ := hE (‖x‖ / 2) (by positivity) (η / 2) (by positivity)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1
    (t6_eventually_small hL (show 0 < min δ (‖x‖ / 2) by positivity))
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
  have hdy : ‖x‖ / 2 ≤ dist y 0 := by
    rw [dist_zero_right]
    have h1 := norm_le_insert' (clSgn τ s x) y
    rw [norm_clSgn, ← dist_eq_norm] at h1
    have : 1 / (2 * (L : ℝ) ^ N) < ‖x‖ / 2 := hs.trans_le (min_le_right _ _)
    linarith
  have hσ : ‖x‖ / 2 ≤ dist (clSgn τ s x) 0 := by
    rw [dist_zero_right, norm_clSgn]; linarith
  have := hN₂ N ((le_max_left _ _).trans hN) _ _ hσ hdy
    (hd.trans_lt (hs.trans_le (min_le_left _ _)))
  rw [hfy] at this
  rw [Real.dist_eq, sub_zero]
  linarith

/-- **B3 (c): subsequential continuum limit, given asymptotic equicontinuity.** Constants
`M, g₀, N₀` depend on `L` only. For fixed `β_R` (`1/β_R ≤ g₀`) there are `δ₀ ∈ (0,1)` and
`K' ≥ 0` such that, for every admissible choice of `R_N`, `m_N` (window) and `b_N` (bracket) with
`x ↦ f_N(x) = ϑ_ε^{-2}P_ε(latPtN x)` asymptotically equicontinuous on each `{‖x‖ ≥ r}`, a
subsequence converges uniformly on compacts of `𝕋² ∖ {0}` to a `G` continuous on `𝕋² ∖ {0}`,
with `G ≥ 0`, point-group invariance, the bound `G ≤ C(δ)` on `{‖x‖ ≥ δ}` and the short-distance
law of `thm:short` at `|x| < δ₀`. -/
theorem thm_limit_of_equi : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ ∀ βR : ℝ, 0 < βR → 1 / βR ≤ g₀ →
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 ≤ K' ∧
    ∀ (R : ∀ N, RGPar 2 L N) (m b : ℕ → ℝ), ClAdm M N₀ βR R m b → ClEqui (clF L βR b) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : UnitAddTorus (Fin 2) → ℝ, ContinuousOn G {0}ᶜ ∧
      (∀ K ⊆ ({0}ᶜ : Set (UnitAddTorus (Fin 2))), IsCompact K →
        TendstoUniformlyOn (fun k => clF L βR b (φ k)) G atTop K) ∧
      (∀ x, x ≠ 0 → 0 ≤ G x) ∧
      (∀ (τ : Equiv.Perm (Fin 2)) (s : Fin 2 → Bool) x, x ≠ 0 → G (clSgn τ s x) = G x) ∧
      (∀ δ > 0, ∃ C, ∀ x, δ ≤ ‖x‖ → G x ≤ C) ∧
      (∀ x, x ≠ 0 → torusNorm x < δ₀ →
        |G x - csA βR (torusNorm x)| ≤ K' * csA βR (torusNorm x) * csRate (torusNorm x)) := by
  obtain ⟨L₀, h⟩ := t6_short_bound
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨M, g₀, N₀, hg, hF⟩ := h L ((le_max_left _ _).trans hL)
  refine ⟨M, g₀, N₀, hg, fun βR hβR hy => ?_⟩
  obtain ⟨hB, δ₀, K', hδ₀, hδ₁, hK', -, hlim⟩ := hF βR hβR hy
  refine ⟨δ₀, K', hδ₀, hδ₁, hK', fun R m b hA hE => ?_⟩
  have hbd := t6_bdd hL2 hβR hA hB
  obtain ⟨φ, hφ, G, hGc, -, hGu⟩ := ascoli_asymp_exists_subseq_torus (clF L βR b) hbd hE
  -- pointwise convergence off `0`
  have hpt : ∀ x : UnitAddTorus (Fin 2), x ≠ 0 →
      Tendsto (fun k => clF L βR b (φ k) x) atTop (𝓝 (G x)) := by
    intro x hx
    have hK : ({x} : Set (UnitAddTorus (Fin 2))) ⊆ {0}ᶜ := by
      intro y hy; rw [Set.mem_singleton_iff.1 hy]; exact hx
    exact (hGu _ hK isCompact_singleton).tendsto_at (Set.mem_singleton x)
  refine ⟨φ, hφ, G, hGc, hGu, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro x hx
    refine ge_of_tendsto (hpt x hx) ?_
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N₀)] with k hk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb0⟩ := hA (φ k) hk
    exact t6_clF_nonneg hβR hb0 x
  · -- point-group invariance
    intro τ s x hx
    have hσ : clSgn τ s x ≠ 0 := by
      intro h0; apply hx
      have := norm_clSgn τ s x
      rw [h0, norm_zero] at this
      exact norm_eq_zero.1 this.symm
    exact ascoli_asymp_limit_eq_of_tendsto_sub hφ (hpt x hx) (hpt _ hσ)
      (t6_sym_tendsto hL2 hE τ s hx)
  · -- the bound away from `0`
    intro δ hδ
    obtain ⟨C, hC⟩ := hbd δ hδ
    refine ⟨C, fun x hx => ?_⟩
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx; linarith
    refine le_of_tendsto (hpt x hx0) (Eventually.of_forall fun k => ?_)
    exact (le_abs_self _).trans (hC _ x (by rwa [dist_zero_right]))
  · -- the short-distance law
    intro x hx hxδ
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine hlim (fun k => clF L βR b (φ k) x)
      (fun k => eucl (latPtN L (φ k) x) / (L : ℝ) ^ (φ k)) (G x) (torusNorm x)
      (t6_torusNorm_pos hx) hxδ (hpt x hx) ((t6_eucl_tendsto hL2 x).comp hφ.tendsto_atTop) ?_
    have h1 := hφ.tendsto_atTop.eventually (t6_eventually_small hL2 (show 0 < ‖x‖ / 2 by positivity))
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N₀), h1] with k hk hk2
    exact t6_csPtX hA hk (t6_latPt_far hL2 (φ k) x hk2.le hx0).1

end Main

end

end Spin2
