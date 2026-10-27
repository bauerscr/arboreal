import Ward.FinVol
import Ward.ObsLimitP
import Ward.ObsLimitA

/-!
# Lemma `cor:anm0` (Tier 2 form)

For real `b ∈ (0, b̄]`, `N ≥ 2`, `β = β(b, 0)`, `c₀² = c²(b, 0)`, `ã₀ = ã_{N,N}(0, V₀^c(0, b))`:
```
1 = c₀² (γ + λ/(|Λ_N| ã₀) (1 + E)),   |E| ≤ C b L^{-κ₁ N},
```
with the `N`-independent `γ = Re γ^{(2)}_{a,∞}(0, b)` (`gamInf`), `λ = Re λ^{(2)}_{a,∞}(0, b)`
(`lamInf`) of `Ward.ObsLimit` and `κ₁ = min(κ, 1)` (`cor_anm0_of`). Both `γ^{(2)}_{a,∞}(0, b)` and
`λ^{(2)}_{a,∞}(0, b)` are real (`GamA_real`, `LamA_real`).

## Proof
* The Ward identity `⟨z_0⟩_{β,0} = 0`, i.e. `⟨ξ_0η_0⟩_{β,0} = 1` (from `H02.cor_spin_conn`), the
  bridge and `e:1pt-b-thm` at scale `N` give (`anm0_scaleN`), as `m² ↓ 0`,
  `1/c₀² = γ_N + (λ_N + e)/(|Λ| ã₀)`, `|e| ≤ C b L^{-κN}`, with the scale-`N` couplings at `m² = 0`.
* Replacing `γ_N, λ_N` by their limits (rates `gamA2_rate`, `lamA2_rate`) introduces the error
  `(γ_N - γ)|Λ|ã₀ = O(L^{-(d-2)N}) · O(b)` (the `γ` rate has no factor `b`, but
  `|Λ| ã₀ = O(b)`), hence `κ₁ ≤ d - 2`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- `γ = Re γ^{(2)}_{a,∞}(m² = 0, b)`. -/
def gamInf (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (lbar b : ℝ) : ℝ :=
  (GamA d L V₀c lbar 0 b).re

/-- `λ = Re λ^{(2)}_{a,∞}(m² = 0, b)`. -/
def lamInf (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (lbar b : ℝ) : ℝ :=
  (LamA d L V₀c lbar 0 b).re

/-- `⟨ξ_0η_0⟩_{β,0} = 1`. -/
theorem avg_ξη_self_zero {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) (a : Lam d L N) :
    H02.avg (nnW d L N β) (fun _ => 0) (H02.ξ a * H02.η a) = 1 := by
  obtain ⟨e1, e2, e3, -⟩ := H02.cor_spin_conn (nnW_symm (d := d) (L := L) (N := N) β)
    (nnW_nonneg hβ) a a
  have h1 := H02.arborealProb_true (nnW_symm (d := d) (L := L) (N := N) β) (nnW_nonneg hβ)
  have h2 : H02.arborealProb (nnW d L N β) (nnW_symm β) (fun F => F.Reachable a a) = 1 := by
    rw [← h1]; simp only [SimpleGraph.Reachable.refl]
  show H02.avg (nnW d L N β) 0 (H02.ξ a * H02.η a) = 1
  rw [← e3, ← e2, ← e1, h2]

/-! ### The scale-`N` identity -/

section ScaleN

variable (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) {bw K : ℝ}
  (hbw2 : bw ≤ lbar / 2) (hbw1 : bw ≤ 1) (hK0 : 0 ≤ K) (hKb : K * bw ≤ 1 / 2)
  (h48 : 48 * C * bw ≤ 1)
  (hall : ∀ b m, 0 < b → b ≤ bw → 0 ≤ m →
    |hF V₀c b m - m * betaF V₀c b m| ≤ K * b * (m * betaF V₀c b m))
  (hh0 : ∀ b, 0 < b → b ≤ bw → hF V₀c b 0 = 0)
  {Ct : ℝ} (hCt : 0 ≤ Ct) (HB : Psi4FullBody d L V₀c lbar Ct κ)
  {b : ℝ} (hb : 0 < b) (hbw : b ≤ bw)
include hd HW hbw2 hbw1 hK0 hKb h48 hall hh0 hCt HB hb hbw

set_option maxHeartbeats 4000000 in
/-- **The scale-`N` form of `cor:anm0`**: `1/c₀² = γ_N + (λ_N + e)/(|Λ|ã₀)`. -/
theorem anm0_scaleN {N : ℕ} (hN : 1 ≤ N) (ha0 : 0 < atR d L V₀c N b) {x : Lam d L N}
    (hx : x ≠ 0) :
    ‖gamA2 d L N 0 (V₀c 0 b) lbar x‖ ≤ 2 * ℓ₀ ^ 2 + Ct * b ∧
    ∃ e : ℂ, ‖e‖ ≤ Ct * b * (L : ℝ) ^ (-(κ * N)) ∧
      ((1 / c2F V₀c b 0 : ℝ) : ℂ) = gamA2 d L N 0 (V₀c 0 b) lbar x +
        (lamA2 d L N 0 (V₀c 0 b) lbar x + e) /
          ((Fintype.card (Lam d L N) : ℂ) * (atR d L V₀c N b : ℂ)) := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hL2 := HF.hL2
  have hl := HF.lbar_pos
  obtain ⟨hsb, hβpos, hhnn, cs, cβ, ch, cc2⟩ :=
    fv_model hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw
  have hs1 : ∀ m, 0 ≤ m → -1 < s0R V₀c b m := fun m hm => by linarith [(hsb m hm).1]
  have hbn : ‖(b : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith
  have hbnorm : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]
  obtain ⟨-, -, -, -, -, -, -, hZcorr⟩ := HB
  -- opaque abbreviations
  obtain ⟨card, hcard⟩ : ∃ c : ℝ, c = (Fintype.card (Lam d L N) : ℝ) := ⟨_, rfl⟩
  have hcard0 : 0 < card := hcard ▸ Suscept.card_lam_pos N
  obtain ⟨utr, hutr⟩ : ∃ f : ℝ → ℝ, f = fun m => (Suscept.utN d L N m (V₀c m b)).re := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ f : ℝ → ℝ, f = fun m => m * (1 + utr m) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ f : ℝ → ℂ, f = fun m => gamA2 d L N m (V₀c m b) lbar x := ⟨_, rfl⟩
  obtain ⟨l, hl'⟩ : ∃ f : ℝ → ℂ, f = fun m => lamA2 d L N m (V₀c m b) lbar x := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ f : ℝ → ℝ, f = fun m =>
      H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ 0 * H02.η 0) := ⟨_, rfl⟩
  obtain ⟨mt, hmt⟩ : ∃ f : ℝ → ℝ, f = fun m => m * Suscept.tNN d L N m := ⟨_, rfl⟩
  have hut : ∀ m, 0 < m → Suscept.utN d L N m (V₀c m b) = (utr m : ℂ) ∧ 0 < 1 + utr m :=
    fun m hm => by
      rw [hutr]; exact fv_one_add_utN hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw hN hm
  have hDpos : ∀ m, 0 < m → 0 < D m := fun m hm => by rw [hD]; exact mul_pos hm (hut m hm).2
  -- limits
  have tendsC : ∀ {f : ℝ → ℂ}, ContinuousOn f (Set.Ici 0) → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    fun hf => ((hf 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto
  have tendsR : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Ici 0) → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    fun hf => ((hf 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto
  have hgT : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := tendsC (by rw [hg]; exact HF.gamA2_cont hd1 hbn _ x)
  have hlT : Tendsto l (𝓝[>] 0) (𝓝 (l 0)) := tendsC (by rw [hl']; exact HF.lamA2_cont hd1 hbn _ x)
  have hXT : Tendsto X (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousOn X (Set.Ici 0) := by
      rw [hX]; exact contOn_avg_comp cβ ch (fun m hm => ⟨(hβpos m hm).le, hhnn m hm⟩) _
    have h0 : X 0 = 1 := by
      rw [hX]; simp only [hh0 b hb hbw]; exact avg_ξη_self_zero (hβpos 0 le_rfl).le 0
    rw [← h0]; exact tendsR hc
  have hcT : Tendsto (fun m => c2F V₀c b m) (𝓝[>] 0) (𝓝 (c2F V₀c b 0)) := tendsR cc2
  have hc0 : 0 < c2F V₀c b 0 := c2F_pos hb (hs1 0 le_rfl)
  have hDT : Tendsto D (𝓝[>] 0) (𝓝 (atR d L V₀c N b)) := by
    rw [hD, hutr]; exact fv_D_tendsto hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw N
  have hmtT : Tendsto mt (𝓝[>] 0) (𝓝 1) := by rw [hmt]; exact fv_mt_tendsto hd1 N
  -- the scale-`N` 1-point formula at `m² > 0`
  set θN : ℝ := (L : ℝ) ^ (-(κ * N))
  set σN : ℝ := (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N))
  have key : ∀ m, 0 < m → ‖((X m / c2F V₀c b m : ℝ) : ℂ) - g m -
        l m * ((mt m / card : ℝ) : ℂ) / (D m : ℂ)‖ ≤ Ct * b * (m * σN + θN / card) / D m ∧
      ‖g m‖ ≤ 2 * ℓ₀ ^ 2 + Ct * b := by
    intro m hm
    obtain ⟨hu, hu1⟩ := hut m hm
    have hu0 : 1 + Suscept.utN d L N m (V₀c m b) ≠ 0 := by
      rw [hu]; exact_mod_cast hu1.ne'
    obtain ⟨⟨-, a2, E, hE, hEq⟩, -, -⟩ := ((hZcorr N m b hN hm hbn).2 hu0).2 x hx
    have hc2m := c2F_pos hb (hs1 m hm.le)
    have hXc : ((X m : ℝ) : ℂ) = (c2F V₀c b m : ℂ) * avgM d L N V₀c m b (psibar 0 * psi 0) := by
      rw [hX]; exact avg_ξη_eq HW.conj hb (hs1 m hm.le) hm 0 0
    have hW : ‖(WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ 2 * ℓ₀ ^ 2 := by
      have h := norm_sum_covAt_le hd hL2 HF.hℓ₀ (HF.good N m hm.le) (0 : Lam d L N) 0
      rwa [sum_covAt_ofReal, sum_covAt_eq_WN hm hN, sub_zero] at h
    rw [hbnorm] at a2 hE
    refine ⟨?_, ?_⟩
    · have hD0 : (D m : ℂ) ≠ 0 := by exact_mod_cast (hDpos m hm).ne'
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have hcd0 : (card : ℂ) ≠ 0 := by exact_mod_cast hcard0.ne'
      have hc20 : (c2F V₀c b m : ℂ) ≠ 0 := by exact_mod_cast hc2m.ne'
      have e1 : ((X m / c2F V₀c b m : ℝ) : ℂ) - g m - l m * ((mt m / card : ℝ) : ℂ) / (D m : ℂ) =
          (m : ℂ) * E / (D m : ℂ) := by
        have hDc : (D m : ℂ) = (m : ℂ) * (1 + Suscept.utN d L N m (V₀c m b)) := by
          rw [hu, hD]; push_cast; ring
        have hmtc : ((mt m / card : ℝ) : ℂ) = (m : ℂ) * PtCorr.tau d L N m := by
          rw [hmt, hcard]; simp only [PtCorr.tau]; push_cast; ring
        rw [Complex.ofReal_div, hXc, hmtc, hDc, hg, hl']
        simp only
        rw [hEq]
        field_simp
        ring
      rw [e1, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hm.le,
        Real.norm_of_nonneg (hDpos m hm).le]
      refine div_le_div_of_nonneg_right ?_ (hDpos m hm).le
      calc m * ‖E‖ ≤ m * (Ct * b * (σN + θN / (m * Fintype.card (Lam d L N)))) :=
            mul_le_mul_of_nonneg_left hE hm.le
        _ = Ct * b * (m * σN + θN / card) := by rw [hcard]; field_simp
    · rw [hg]
      calc ‖gamA2 d L N m (V₀c m b) lbar x‖ ≤
            ‖gamA2 d L N m (V₀c m b) lbar x -
              (WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N (0 : Lam d L N) : ℂ)‖ +
            ‖(WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N (0 : Lam d L N) : ℂ)‖ := by
            have := norm_add_le (gamA2 d L N m (V₀c m b) lbar x -
              (WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N (0 : Lam d L N) : ℂ))
              (WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N (0 : Lam d L N) : ℂ)
            simpa using this
        _ ≤ 2 * ℓ₀ ^ 2 + Ct * b := by linarith
  -- the bound on `γ_N` at `m² = 0`
  have hg0 : ‖g 0‖ ≤ 2 * ℓ₀ ^ 2 + Ct * b :=
    le_of_tendsto hgT.norm (by filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
      using (key m hm).2)
  refine ⟨by rw [hg] at hg0; exact hg0, ?_⟩
  -- the limit of `Y`
  have hYT : Tendsto (fun m => ((X m / c2F V₀c b m : ℝ) : ℂ) - g m -
      l m * ((mt m / card : ℝ) : ℂ) / (D m : ℂ)) (𝓝[>] 0)
      (𝓝 (((1 / c2F V₀c b 0 : ℝ) : ℂ) - g 0 -
        l 0 * ((1 / card : ℝ) : ℂ) / (atR d L V₀c N b : ℂ))) := by
    have h1 : Tendsto (fun m => ((X m / c2F V₀c b m : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 ((1 / c2F V₀c b 0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (hXT.div hcT hc0.ne')
    have h2 : Tendsto (fun m => ((mt m / card : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((1 / card : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (hmtT.div_const card)
    have h3 : Tendsto (fun m => (D m : ℂ)) (𝓝[>] 0) (𝓝 (atR d L V₀c N b : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hDT
    exact (h1.sub hgT).sub ((hlT.mul h2).div h3 (by exact_mod_cast ha0.ne'))
  have hBT : Tendsto (fun m => Ct * b * (m * σN + θN / card) / D m) (𝓝[>] 0)
      (𝓝 (Ct * b * (0 * σN + θN / card) / atR d L V₀c N b)) := by
    have hid : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
    exact ((tendsto_const_nhds.mul ((hid.mul_const σN).add tendsto_const_nhds)).div hDT ha0.ne')
  have hY0 := le_of_tendsto_of_tendsto hYT.norm hBT
    (by filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m) using (key m hm).1)
  rw [zero_mul, zero_add] at hY0
  set Y₀ := ((1 / c2F V₀c b 0 : ℝ) : ℂ) - g 0 - l 0 * ((1 / card : ℝ) : ℂ) / (atR d L V₀c N b : ℂ)
  refine ⟨Y₀ * card * atR d L V₀c N b, ?_, ?_⟩
  · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hcard0.le,
      Real.norm_of_nonneg ha0.le]
    calc ‖Y₀‖ * card * atR d L V₀c N b ≤ Ct * b * (θN / card) / atR d L V₀c N b * card *
          atR d L V₀c N b := by gcongr
      _ = Ct * b * θN := by field_simp
  · have hcd0 : (card : ℂ) ≠ 0 := by exact_mod_cast hcard0.ne'
    have ha00 : (atR d L V₀c N b : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    simp only [Y₀, hg, hl']
    rw [hcard]
    push_cast
    field_simp
    ring

end ScaleN

/-! ### From scale `N` to `N = ∞` -/

/-- The algebra of the Tier 2 replacement. -/
theorem anm0_alg {c b M Kγ εl εe εg : ℝ} {γN lN e Γ Λ : ℂ} (hc : 0 < c) (hcb : c ≤ 2 * b)
    (hM : 0 < M) (heq : ((1 / c : ℝ) : ℂ) = γN + (lN + e) / M) (hγN : ‖γN‖ ≤ Kγ)
    (hbK : 4 * b * Kγ ≤ 1) (hl : ‖lN - Λ‖ ≤ εl) (he : ‖e‖ ≤ εe) (hle : εl + εe ≤ 1 / 2)
    (hg : ‖γN - Γ‖ ≤ εg) (hΛ : ‖Λ - 1‖ ≤ 1 / 2) :
    M ≤ 8 * b ∧ ∃ E : ℂ, ‖E‖ ≤ 2 * (εl + εe + 8 * b * εg) ∧
      (1 : ℂ) = c * (Γ + Λ / M * (1 + E)) := by
  have hb : 0 < b := by linarith
  have hKγ : 0 ≤ Kγ := (norm_nonneg _).trans hγN
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hΛ1 : 1 / 2 ≤ ‖Λ‖ := by
    have := norm_sub_norm_le (1 : ℂ) Λ
    rw [norm_one, norm_sub_rev] at this; linarith
  have hΛ0 : Λ ≠ 0 := fun h => by rw [h, norm_zero] at hΛ1; linarith
  have hsum : lN + e = M * (((1 / c : ℝ) : ℂ) - γN) := by
    rw [heq]; field_simp; ring
  have hlow : 1 / (4 * b) ≤ ‖((1 / c : ℝ) : ℂ) - γN‖ := by
    have h1 : 1 / (2 * b) ≤ 1 / c := one_div_le_one_div_of_le hc hcb
    have h2 := norm_sub_norm_le (((1 / c : ℝ) : ℂ)) γN
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h2
    have h3 : 1 / (4 * b) + Kγ ≤ 1 / (2 * b) := by
      rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hup : ‖lN + e‖ ≤ 2 := by
    have := norm_sub_norm_le lN Λ
    have h2 := norm_sub_norm_le Λ 1
    rw [norm_one] at h2
    calc ‖lN + e‖ ≤ ‖lN‖ + ‖e‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have hM8 : M ≤ 8 * b := by
    have h := congrArg norm hsum
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hM.le] at h
    have : M * (1 / (4 * b)) ≤ 2 := by
      rw [h] at hup
      calc M * (1 / (4 * b)) ≤ M * ‖((1 / c : ℝ) : ℂ) - γN‖ :=
            mul_le_mul_of_nonneg_left hlow hM.le
        _ ≤ 2 := hup
    rw [mul_one_div, div_le_iff₀ (by positivity)] at this
    linarith
  refine ⟨hM8, (lN - Λ + e + (γN - Γ) * M) / Λ, ?_, ?_⟩
  · rw [norm_div]
    rw [div_le_iff₀ (by linarith)]
    have h1 : ‖lN - Λ + e + (γN - Γ) * M‖ ≤ εl + εe + 8 * b * εg := by
      calc ‖lN - Λ + e + (γN - Γ) * M‖ ≤ ‖lN - Λ‖ + ‖e‖ + ‖(γN - Γ) * M‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ εl + εe + 8 * b * εg := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hM.le]
            have hεg : 0 ≤ εg := (norm_nonneg _).trans hg
            nlinarith [mul_le_mul hg hM8 hM.le hεg]
    have h2 : 0 ≤ εl + εe + 8 * b * εg := (norm_nonneg _).trans h1
    nlinarith
  · have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have h1 : γN = ((1 / c : ℝ) : ℂ) - (lN + e) / M := by rw [heq]; ring
    rw [h1]
    push_cast
    field_simp
    ring

set_option maxHeartbeats 4000000 in
/-- **`cor:anm0`, complex form** for a given `V₀c` with `FlowDataW` (`L` odd). -/
theorem anm0_complex (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) :
    ∃ bbar Ca : ℝ, 0 < bbar ∧ bbar ≤ lbar / 2 ∧ bbar ≤ 1 ∧ 0 ≤ Ca ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0) ∧
      (∀ b, 0 < b → b ≤ bbar → ‖LamA d L V₀c lbar 0 b - 1‖ ≤ 1 / 2) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ b, 0 < b → b ≤ bbar →
        0 < atR d L V₀c N b ∧ Fintype.card (Lam d L N) * atR d L V₀c N b ≤ 8 * b ∧
        ∃ E : ℂ, ‖E‖ ≤ Ca * b * (L : ℝ) ^ (-(min κ 1 * N)) ∧
          (1 : ℂ) = (c2F V₀c b 0 : ℂ) * (GamA d L V₀c lbar 0 b + LamA d L V₀c lbar 0 b /
            ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) * (1 + E)) := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hC := HF.C_nonneg
  have hl := HF.lbar_pos
  have hκ := HF.κ_pos
  have H := ObsLimHyp.ofW HW hLodd
  have hL3 := three_le_L H
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  obtain ⟨Cs, hCs, hSall⟩ := exists_stepBd d hd1
  have hS := hSall L A ℓ₀ V₀c lbar C κ H
  obtain ⟨hθ0, hθ1, hθp⟩ := th_facts H hd1 hCs hS
  have hρ0 := rho_nonneg d L
  have hρ1 := rho_lt_one hd (by omega : 2 ≤ L)
  have hρp : 0 < rho d L := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨bw, K, hbw0, hbw2, hbw1, hK0, hKb, h48, hall, hh0, -⟩ := cor_ward_i hd HW
  obtain ⟨bm, Cm, hbm0, hbm2, hCm, -, hmac⟩ := cor_macro_of hd HW
  obtain ⟨Ct, hCt, HB⟩ := thm_psi4_full_of hd HF
  set Kl := 2 * Cs * C / (th L κ ^ 2 * (1 - th L κ)) with hKl
  set KG := K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) with hKG
  set KL1 := Cs * C / (1 - th L κ) with hKL1
  have hKl0 : 0 ≤ Kl := by rw [hKl]; have := sub_pos.2 hθ1; positivity
  have hKG0 : 0 ≤ KG := by
    rw [hKG]; have := sub_pos.2 hρ1; unfold K1; have := sub_pos.2 hθ1; positivity
  have hKL10 : 0 ≤ KL1 := by rw [hKL1]; have := sub_pos.2 hθ1; positivity
  set Kγ := 2 * ℓ₀ ^ 2 + Ct with hKγ
  set bbar := min (min bw bm) (1 / (2 * KL1 + 8 * Kγ + 2 * (Kl + Ct) + 2)) with hbbar
  have hbb1 : bbar ≤ bw := (min_le_left _ _).trans (min_le_left _ _)
  have hbb2 : bbar ≤ bm := (min_le_left _ _).trans (min_le_right _ _)
  have hbb3 : bbar ≤ 1 / (2 * KL1 + 8 * Kγ + 2 * (Kl + Ct) + 2) := min_le_right _ _
  have hKγ0 : 0 ≤ Kγ := by positivity
  have hden : 0 < 2 * KL1 + 8 * Kγ + 2 * (Kl + Ct) + 2 := by positivity
  have hbpos : 0 < bbar := lt_min (lt_min hbw0 hbm0) (by positivity)
  have hsmall : (2 * KL1 + 8 * Kγ + 2 * (Kl + Ct) + 2) * bbar ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hbb3 hden.le
    rwa [mul_one_div_cancel hden.ne'] at this
  have hexp : (2 * KL1 + 8 * Kγ + 2 * (Kl + Ct) + 2) * bbar =
      2 * (KL1 * bbar) + 8 * (Kγ * bbar) + 2 * ((Kl + Ct) * bbar) + 2 * bbar := by ring
  have p1 := mul_nonneg hKL10 hbpos.le
  have p2 := mul_nonneg hKγ0 hbpos.le
  have p3 := mul_nonneg (add_nonneg hKl0 hCt) hbpos.le
  have hsm1 : KL1 * bbar ≤ 1 / 2 := by linarith
  have hsm2 : 4 * bbar * Kγ ≤ 1 := by
    have : 4 * bbar * Kγ = 4 * (Kγ * bbar) := by ring
    linarith
  have hsm3 : (Kl + Ct) * bbar ≤ 1 / 2 := by linarith
  have hsm4 : bbar ≤ 1 := hbb1.trans hbw1
  have hLam : ∀ b, 0 < b → b ≤ bbar → ‖LamA d L V₀c lbar 0 b - 1‖ ≤ 1 / 2 := by
    intro b hb hbb
    have hbn : ‖(b : ℂ)‖ ≤ lbar := by
      rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith
    have h := LamA_sub_one H hd1 hCs hS le_rfl hbn
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le] at h
    rw [← hKL1] at h
    calc _ ≤ KL1 * b := h
      _ ≤ KL1 * bbar := mul_le_mul_of_nonneg_left hbb hKL10
      _ ≤ 1 / 2 := hsm1
  refine ⟨bbar, 2 * (Kl + Ct + 8 * KG), hbpos, hbb1.trans hbw2, hsm4, by positivity,
    fun b hb hbb => hh0 b hb (hbb.trans hbb1), hLam, fun N hN b hb hbb => ?_⟩
  have hbw : b ≤ bw := hbb.trans hbb1
  have hbn : ‖(b : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith
  have hbnorm : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]
  have ha0 := (hmac N (by omega) b hb (hbb.trans hbb2)).1
  obtain ⟨x, hx⟩ := exists_ne_zero_lam hd1 (by omega : 2 ≤ L) (by omega : 1 ≤ N)
  obtain ⟨hγN, e, he, heq⟩ := anm0_scaleN hd HW hbw2 hbw1 hK0 hKb h48 hall hh0 hCt HB hb hbw
    (by omega) ha0 hx
  have hsb := (fv_model hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw).1 0 le_rfl
  have hc0 : 0 < c2F V₀c b 0 := c2F_pos hb (by linarith [hsb.1])
  have hc2 : c2F V₀c b 0 ≤ 2 * b := by
    unfold c2F; rw [div_le_iff₀ (by linarith [hsb.1])]; nlinarith [hsb.1]
  have hcard0 := Suscept.card_lam_pos (d := d) (L := L) N
  have hM : 0 < (Fintype.card (Lam d L N) : ℝ) * atR d L V₀c N b := mul_pos hcard0 ha0
  have hθN : (L : ℝ) ^ (-(κ * N)) ≤ 1 := rpow_neg_mul_le_one hL1 hκ.le N
  have hrl := lamA2_rate H hd1 hCs hS le_rfl hbn hN hx
  have hrg := gamA2_rate H hd1 hCs hS hd le_rfl hbn hN hx
  rw [hbnorm] at hrl
  have heq' : ((1 / c2F V₀c b 0 : ℝ) : ℂ) = gamA2 d L N 0 (V₀c 0 b) lbar x +
      (lamA2 d L N 0 (V₀c 0 b) lbar x + e) /
        (((Fintype.card (Lam d L N) : ℝ) * atR d L V₀c N b : ℝ) : ℂ) := by
    rw [heq]; push_cast; ring
  have hle : Kl * b * (L : ℝ) ^ (-(κ * N)) + Ct * b * (L : ℝ) ^ (-(κ * N)) ≤ 1 / 2 := by
    have h1 : (Kl + Ct) * b ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hbb (add_nonneg hKl0 hCt)).trans hsm3
    have h2 : (Kl + Ct) * b * (L : ℝ) ^ (-(κ * N)) ≤ (Kl + Ct) * b :=
      mul_le_of_le_one_right (by positivity) hθN
    nlinarith
  have hbK : 4 * b * Kγ ≤ 1 := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbb (by norm_num)) hKγ0).trans hsm2
  have hγN' : ‖gamA2 d L N 0 (V₀c 0 b) lbar x‖ ≤ Kγ := by
    refine hγN.trans ?_
    rw [hKγ]; nlinarith [mul_le_mul_of_nonneg_left (hbb.trans hsm4) hCt]
  obtain ⟨hM8, E, hE, hid⟩ := anm0_alg hc0 hc2 hM heq' hγN' hbK hrl he hle hrg (hLam b hb hbb)
  refine ⟨ha0, hM8, E, hE.trans ?_, hid⟩
  have hκ1 : min κ 1 ≤ κ := min_le_left _ _
  have hκ2 : min κ 1 ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have := min_le_right κ 1; linarith
  have r1 : (L : ℝ) ^ (-(κ * N)) ≤ (L : ℝ) ^ (-(min κ 1 * N)) := rpow_neg_mul_mono_one hL1 hκ1 N
  have r2 : (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ≤ (L : ℝ) ^ (-(min κ 1 * N)) :=
    rpow_neg_mul_mono_one hL1 hκ2 N
  rw [← hKG] at *
  nlinarith [mul_le_mul_of_nonneg_left r1 (mul_nonneg hKl0 hb.le),
    mul_le_mul_of_nonneg_left r1 (mul_nonneg hCt hb.le),
    mul_le_mul_of_nonneg_left r2 (mul_nonneg hKG0 hb.le)]

end

end Ward
