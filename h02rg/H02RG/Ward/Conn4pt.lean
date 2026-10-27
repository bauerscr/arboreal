import Ward.Anm0Real
import Ward.ConnAlg
import FRD.GreenLimit
import FRD.GreenBd

/-!
# Lemma `cor:conn4pt`

For real `b ∈ (0, b̄]`, `N ≥ 2`, `x ∈ Λ_N ∖ {0}` (`|x| = supNorm x`), with
`θ = 1 - c₀² γ`, `c₀² = c²(b, 0)`, `γ = gamInf`, `λ = lamInf` and `G(x) = (-Δ_{ℤ^d})^{-1}(0, r(x))`:
```
P_{β(b,0),0}^{Λ_N}[0 ↔ x] = θ² + 2 c₀² λ θ G(x)
    + O(b² |x|^{-(d-2+κ₁)}) + O(b L^{-(d-2)N}) + O(b² L^{-κ₁N}),
```
uniformly in `x` and `N` (`cor_conn4pt_of`), `κ₁ = min(κ, 1)`.

The `b`-slot couplings at `ctr_N + x` are replaced by the `a`-slot ones through
`LamA_eq_LamB`, `GamA_eq_GamB` (point independence of the limits) and the rates `lamB2_rate`,
`gamB2_rate` (uniform in the point). The error `O(b L^{-(d-2)N})` has no second factor `b` (the
`γ` rate has no factor `b`), and `κ₁ ≤ d - 2`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem avg_ξηξη_eq {N : ℕ} (hconj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj)
    {b m : ℝ} (hb : 0 < b) (hs : -1 < s0R V₀c b m) (hm : 0 < m) (a x : Lam d L N) :
    ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m)
        (H02.ξ a * H02.η a * (H02.ξ x * H02.η x)) : ℝ) : ℂ) =
      (c2F V₀c b m : ℂ) ^ 2 * avgM d L N V₀c m b (psibar a * psi a * (psibar x * psi x)) := by
  rw [bridge_avg_ξηξη (betaF_pos hb hs) hs hm, Vh_eq_V₀sp hconj hb hs, c2F_eq hb hs]
  rfl

/-- `P_{β,0}[a ↔ x] = 1 - ⟨ξ_aη_a ξ_xη_x⟩_{β,0}`. -/
theorem conn_eq_one_sub {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) (a x : Lam d L N) :
    H02.arborealProb (nnW d L N β) (nnW_symm β) (fun F => F.Reachable a x) =
      1 - H02.avg (nnW d L N β) (fun _ => 0) (H02.ξ a * H02.η a * (H02.ξ x * H02.η x)) := by
  obtain ⟨e1, e2, e3, e4⟩ := H02.cor_spin_conn (nnW_symm (d := d) (L := L) (N := N) β)
    (nnW_nonneg hβ) a x
  have hηξ : H02.η a * H02.ξ a * H02.η x * H02.ξ x =
      (H02.ξ a * H02.η a * (H02.ξ x * H02.η x) : H02.Grassmann (Lam d L N)) := by
    rw [mul_assoc, H02.η_anticomm_ξ x x, H02.η_anticomm_ξ a a]; noncomm_ring
  rw [e1, e2, e3, e4, hηξ]
  rfl

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

set_option maxHeartbeats 8000000 in
/-- **The scale-`N` form of `cor:conn4pt`** (at `m² = 0`, before the `N → ∞` replacement). -/
theorem conn4pt_scaleN {N : ℕ} (hN : 1 ≤ N) (ha0 : 0 < atR d L V₀c N b) {x : Lam d L N}
    (hx : x ≠ 0) {w : ℝ}
    (hw : Tendsto (fun m => WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N x) (𝓝[>] 0) (𝓝 w)) :
    ∃ et : ℂ, ‖et‖ ≤ Ct * b * (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) +
        Ct * b * ((L : ℝ) ^ (-(κ * N)) + (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) /
          (Fintype.card (Lam d L N) * atR d L V₀c N b) ∧
      ((1 - H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _)
          (fun F => F.Reachable 0 x) : ℝ) : ℂ) =
        (c2F V₀c b 0 : ℂ) ^ 2 * (-lamA2 d L N 0 (V₀c 0 b) lbar x * lamB2 d L N 0 (V₀c 0 b) lbar x *
          (w : ℂ) ^ 2 + gamA2 d L N 0 (V₀c 0 b) lbar x * gamB2 d L N 0 (V₀c 0 b) lbar x +
          (-2 * lamA2 d L N 0 (V₀c 0 b) lbar x * lamB2 d L N 0 (V₀c 0 b) lbar x * (w : ℂ) +
            lamA2 d L N 0 (V₀c 0 b) lbar x * gamB2 d L N 0 (V₀c 0 b) lbar x +
            lamB2 d L N 0 (V₀c 0 b) lbar x * gamA2 d L N 0 (V₀c 0 b) lbar x) /
            ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) + et) := by
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
  obtain ⟨card, hcard⟩ : ∃ c : ℝ, c = (Fintype.card (Lam d L N) : ℝ) := ⟨_, rfl⟩
  have hcard0 : 0 < card := hcard ▸ Suscept.card_lam_pos N
  obtain ⟨utr, hutr⟩ : ∃ f : ℝ → ℝ, f = fun m => (Suscept.utN d L N m (V₀c m b)).re := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ f : ℝ → ℝ, f = fun m => m * (1 + utr m) := ⟨_, rfl⟩
  obtain ⟨la, hla⟩ : ∃ f : ℝ → ℂ, f = fun m => lamA2 d L N m (V₀c m b) lbar x := ⟨_, rfl⟩
  obtain ⟨lb, hlb⟩ : ∃ f : ℝ → ℂ, f = fun m => lamB2 d L N m (V₀c m b) lbar x := ⟨_, rfl⟩
  obtain ⟨ga, hga⟩ : ∃ f : ℝ → ℂ, f = fun m => gamA2 d L N m (V₀c m b) lbar x := ⟨_, rfl⟩
  obtain ⟨gb, hgb⟩ : ∃ f : ℝ → ℂ, f = fun m => gamB2 d L N m (V₀c m b) lbar x := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ f : ℝ → ℝ, f = fun m => WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N x :=
    ⟨_, rfl⟩
  obtain ⟨F, hF'⟩ : ∃ f : ℝ → ℝ, f = fun m => H02.avg (nnW d L N (betaF V₀c b m))
      (fun _ => hF V₀c b m) (H02.ξ 0 * H02.η 0 * (H02.ξ x * H02.η x)) := ⟨_, rfl⟩
  obtain ⟨mt, hmt⟩ : ∃ f : ℝ → ℝ, f = fun m => m * Suscept.tNN d L N m := ⟨_, rfl⟩
  have hut : ∀ m, 0 < m → Suscept.utN d L N m (V₀c m b) = (utr m : ℂ) ∧ 0 < 1 + utr m :=
    fun m hm => by
      rw [hutr]; exact fv_one_add_utN hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw hN hm
  have hDpos : ∀ m, 0 < m → 0 < D m := fun m hm => by rw [hD]; exact mul_pos hm (hut m hm).2
  have tendsC : ∀ {f : ℝ → ℂ}, ContinuousOn f (Set.Ici 0) → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    fun hf => ((hf 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto
  have tendsR : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Ici 0) → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    fun hf => ((hf 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto
  have hlaT : Tendsto la (𝓝[>] 0) (𝓝 (la 0)) :=
    tendsC (by rw [hla]; exact HF.lamA2_cont hd1 hbn _ x)
  have hlbT : Tendsto lb (𝓝[>] 0) (𝓝 (lb 0)) :=
    tendsC (by rw [hlb]; exact HF.lamB2_cont hd1 hbn _ x)
  have hgaT : Tendsto ga (𝓝[>] 0) (𝓝 (ga 0)) :=
    tendsC (by rw [hga]; exact HF.gamA2_cont hd1 hbn _ x)
  have hgbT : Tendsto gb (𝓝[>] 0) (𝓝 (gb 0)) :=
    tendsC (by rw [hgb]; exact HF.gamB2_cont hd1 hbn _ x)
  have hWT : Tendsto (fun m => (W m : ℂ)) (𝓝[>] 0) (𝓝 (w : ℂ)) := by
    rw [hW]; exact (Complex.continuous_ofReal.tendsto _).comp hw
  obtain ⟨P, hP⟩ : ∃ p : ℝ, p = H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _)
      (fun F => F.Reachable 0 x) := ⟨_, rfl⟩
  have hFT : Tendsto F (𝓝[>] 0) (𝓝 (1 - P)) := by
    have hc : ContinuousOn F (Set.Ici 0) := by
      rw [hF']; exact contOn_avg_comp cβ ch (fun m hm => ⟨(hβpos m hm).le, hhnn m hm⟩) _
    have h0 : F 0 = 1 - P := by
      rw [hF', hP, conn_eq_one_sub (hβpos 0 le_rfl).le]; simp only [hh0 b hb hbw]; ring
    rw [← h0]; exact tendsR hc
  have hcT : Tendsto (fun m => c2F V₀c b m) (𝓝[>] 0) (𝓝 (c2F V₀c b 0)) := tendsR cc2
  have hc0 : 0 < c2F V₀c b 0 := c2F_pos hb (hs1 0 le_rfl)
  have hDT : Tendsto D (𝓝[>] 0) (𝓝 (atR d L V₀c N b)) := by
    rw [hD, hutr]; exact fv_D_tendsto hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw N
  have hmtT : Tendsto mt (𝓝[>] 0) (𝓝 1) := by rw [hmt]; exact fv_mt_tendsto hd1 N
  set θN : ℝ := (L : ℝ) ^ (-(κ * N))
  set σN : ℝ := (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N))
  set s₁ : ℝ := (supNorm x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ))
  set s₂ : ℝ := (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))
  have hs₁ : 0 ≤ s₁ := by positivity
  have hs₂ : 0 ≤ s₂ := by positivity
  -- the main term and the remainder at `m² > 0`
  obtain ⟨Xf, hXf⟩ : ∃ f : ℝ → ℂ, f = fun m => -2 * la m * lb m * (W m : ℂ) + la m * gb m +
      lb m * ga m := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ f : ℝ → ℂ, f = fun m => ((F m / c2F V₀c b m ^ 2 : ℝ) : ℂ) -
      (-la m * lb m * (W m : ℂ) ^ 2 + ga m * gb m) - Xf m * ((mt m / card : ℝ) : ℂ) / (D m : ℂ) :=
    ⟨_, rfl⟩
  have key : ∀ m, 0 < m → ‖Y m‖ ≤ Ct * b * s₁ + Ct * b * (m * σN + (θN + s₂) / card) / D m := by
    intro m hm
    obtain ⟨hu, hu1⟩ := hut m hm
    have hu0 : 1 + Suscept.utN d L N m (V₀c m b) ≠ 0 := by
      rw [hu]; exact_mod_cast hu1.ne'
    obtain ⟨-, -, E₁, E₂, hE₁, hE₂, hEq⟩ := ((hZcorr N m b hN hm hbn).2 hu0).2 x hx
    have hc2m := c2F_pos hb (hs1 m hm.le)
    have hFc : ((F m : ℝ) : ℂ) = (c2F V₀c b m : ℂ) ^ 2 *
        avgM d L N V₀c m b (psibar 0 * psi 0 * (psibar x * psi x)) := by
      rw [hF']; exact avg_ξηξη_eq HW.conj hb (hs1 m hm.le) hm 0 x
    rw [hbnorm] at hE₁ hE₂
    have hD0 : (D m : ℂ) ≠ 0 := by exact_mod_cast (hDpos m hm).ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hcd0 : (card : ℂ) ≠ 0 := by exact_mod_cast hcard0.ne'
    have hc20 : (c2F V₀c b m : ℂ) ≠ 0 := by exact_mod_cast hc2m.ne'
    have e1 : Y m = E₁ + (m : ℂ) * E₂ / (D m : ℂ) := by
      have hDc : (D m : ℂ) = (m : ℂ) * (1 + Suscept.utN d L N m (V₀c m b)) := by
        rw [hu, hD]; push_cast; ring
      have hmtc : ((mt m / card : ℝ) : ℂ) = (m : ℂ) * PtCorr.tau d L N m := by
        rw [hmt, hcard]; simp only [PtCorr.tau]; push_cast; ring
      rw [hY]
      simp only
      rw [Complex.ofReal_div, hFc, hmtc, hDc, hXf, hla, hlb, hga, hgb, hW]
      simp only
      rw [Complex.ofReal_pow, hEq]
      field_simp
      ring
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add hE₁ ?_)
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hm.le,
      Real.norm_of_nonneg (hDpos m hm).le]
    refine div_le_div_of_nonneg_right ?_ (hDpos m hm).le
    calc m * ‖E₂‖ ≤ m * (Ct * b * (σN + (θN + s₂) / (m * Fintype.card (Lam d L N)))) :=
          mul_le_mul_of_nonneg_left hE₂ hm.le
      _ = Ct * b * (m * σN + (θN + s₂) / card) := by rw [hcard]; field_simp
  -- limits
  set X₀ := -2 * la 0 * lb 0 * (w : ℂ) + la 0 * gb 0 + lb 0 * ga 0 with hX₀
  have hXT : Tendsto Xf (𝓝[>] 0) (𝓝 X₀) := by
    rw [hXf]
    exact (((tendsto_const_nhds.mul hlaT).mul hlbT).mul hWT).add (hlaT.mul hgbT) |>.add
      (hlbT.mul hgaT)
  have hYT : Tendsto Y (𝓝[>] 0) (𝓝 ((((1 - P) / c2F V₀c b 0 ^ 2 : ℝ) : ℂ) -
      (-la 0 * lb 0 * (w : ℂ) ^ 2 + ga 0 * gb 0) -
      X₀ * ((1 / card : ℝ) : ℂ) / (atR d L V₀c N b : ℂ))) := by
    rw [hY]
    have h1 : Tendsto (fun m => ((F m / c2F V₀c b m ^ 2 : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 (((1 - P) / c2F V₀c b 0 ^ 2 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (hFT.div (hcT.pow 2) (by positivity))
    have h2 : Tendsto (fun m => ((mt m / card : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((1 / card : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (hmtT.div_const card)
    have h3 : Tendsto (fun m => (D m : ℂ)) (𝓝[>] 0) (𝓝 (atR d L V₀c N b : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hDT
    exact (h1.sub (((hlaT.neg.mul hlbT).mul (hWT.pow 2)).add (hgaT.mul hgbT))).sub
      ((hXT.mul h2).div h3 (by exact_mod_cast ha0.ne'))
  have hBT : Tendsto (fun m => Ct * b * s₁ + Ct * b * (m * σN + (θN + s₂) / card) / D m)
      (𝓝[>] 0) (𝓝 (Ct * b * s₁ + Ct * b * (0 * σN + (θN + s₂) / card) / atR d L V₀c N b)) := by
    have hid : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
    exact tendsto_const_nhds.add
      ((tendsto_const_nhds.mul ((hid.mul_const σN).add tendsto_const_nhds)).div hDT ha0.ne')
  have hY0 := le_of_tendsto_of_tendsto hYT.norm hBT
    (by filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m) using key m hm)
  rw [zero_mul, zero_add] at hY0
  set Y₀ := (((1 - P) / c2F V₀c b 0 ^ 2 : ℝ) : ℂ) - (-la 0 * lb 0 * (w : ℂ) ^ 2 + ga 0 * gb 0) -
      X₀ * ((1 / card : ℝ) : ℂ) / (atR d L V₀c N b : ℂ)
  rw [← hP]
  refine ⟨Y₀, ?_, ?_⟩
  · refine hY0.trans (le_of_eq ?_)
    rw [hcard]; field_simp
  · have hcd0 : (card : ℂ) ≠ 0 := by exact_mod_cast hcard0.ne'
    have ha00 : (atR d L V₀c N b : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hc00 : (c2F V₀c b 0 : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    simp only [Y₀, hX₀]
    rw [hla, hlb, hga, hgb]
    simp only
    rw [hcard]
    push_cast
    field_simp
    ring

end ScaleN


/-! ### `cor:conn4pt` -/

theorem rpow_le_rpow_neg_of_one_le {s a a' : ℝ} (hs : 1 ≤ s) (h : a ≤ a') :
    s ^ (-a') ≤ s ^ (-a) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)

set_option maxHeartbeats 16000000 in
/-- **`cor:conn4pt`** for a given `V₀c` with `FlowDataW` (`L` odd), uniformly in `x ≠ 0` and
`N ≥ 2`. -/
theorem cor_conn4pt_of (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) :
    ∃ bbar Cc KΓ : ℝ, 0 < bbar ∧ bbar ≤ lbar / 2 ∧ bbar ≤ 1 ∧ 0 ≤ Cc ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0 ∧ (GamA d L V₀c lbar 0 b).im = 0 ∧
        (LamA d L V₀c lbar 0 b).im = 0 ∧ |lamInf d L V₀c lbar b - 1| ≤ 1 / 2) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ b, 0 < b → b ≤ bbar → ∀ x : Lam d L N, x ≠ 0 →
        |gamInf d L V₀c lbar b| ≤ KΓ ∧
        |H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _) (fun F => F.Reachable 0 x) -
          ((1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) ^ 2 + 2 * c2F V₀c b 0 *
            lamInf d L V₀c lbar b * (1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) *
              greenZd d (rep x))| ≤
          Cc * (b ^ 2 * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + min κ 1)) +
            b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N))) := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hC := HF.C_nonneg
  have hl := HF.lbar_pos
  have hκ := HF.κ_pos
  have H := ObsLimHyp.ofW HW hLodd
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cs, hCs, hSall⟩ := exists_stepBd d hd1
  have hS := hSall L A ℓ₀ V₀c lbar C κ H
  obtain ⟨hθ0, hθ1, hθp⟩ := th_facts H hd1 hCs hS
  have hρ1 := rho_lt_one hd hL2
  have hρp : 0 < rho d L := Real.rpow_pos_of_pos hL0 _
  obtain ⟨bw, K, hbw0, hbw2, hbw1, hK0, hKb, h48, hall, hh0, -⟩ := cor_ward_i hd HW
  obtain ⟨Ct, hCt, HB⟩ := thm_psi4_full_of hd HF
  obtain ⟨ba, Ca, hba, hba2, hba1, hCa, -, hLam, hmain⟩ := anm0_complex hd HW hLodd
  obtain ⟨bR, -, hbR, -, -, -, hreal, -⟩ := cor_anm0_of hd HW hLodd
  obtain ⟨Kf, hKf⟩ := FRD.greenf stdPt hd
  obtain ⟨Cg, hCg0, hCg⟩ := FRD.greenZd_bound_supNorm hd
  set Kl := 2 * Cs * C / (th L κ ^ 2 * (1 - th L κ)) with hKl
  set KG := K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) with hKG
  have hKl0 : 0 ≤ Kl := by rw [hKl]; have := sub_pos.2 hθ1; positivity
  have hKG0 : 0 ≤ KG := by
    rw [hKG]; have := sub_pos.2 hρ1; unfold K1; have := sub_pos.2 hθ1; positivity
  have hKf0 : 0 ≤ Kf := by
    obtain ⟨w, -, hw⟩ := hKf L hL2 1 le_rfl 0
    by_contra hneg
    push_neg at hneg
    have h1 : Kf * (L : ℝ) ^ (-(((d : ℝ) - 2) * ((1 - 1 : ℕ) : ℝ))) < 0 :=
      mul_neg_of_neg_of_pos hneg (by positivity)
    linarith [abs_nonneg (w - greenZd d (rep (0 : Torus d (L ^ 1))))]
  set bbar := min (min bw (min ba bR)) (min (1 / (Kl + 1)) (1 / (2 * Ca + 2))) with hbbar
  have hb1 : bbar ≤ bw := (min_le_left _ _).trans (min_le_left _ _)
  have hb2 : bbar ≤ ba := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb3 : bbar ≤ bR := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb4 : bbar ≤ 1 / (Kl + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hb5 : bbar ≤ 1 / (2 * Ca + 2) := (min_le_right _ _).trans (min_le_right _ _)
  have hbpos : 0 < bbar := lt_min (lt_min hbw0 (lt_min hba hbR)) (lt_min (by positivity)
    (by positivity))
  have hKlb : Kl * bbar ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hb4 (by positivity : (0 : ℝ) ≤ Kl + 1)
    rw [mul_one_div_cancel (by positivity)] at this; nlinarith
  have hCab : Ca * bbar ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hb5 (by positivity : (0 : ℝ) ≤ 2 * Ca + 2)
    rw [mul_one_div_cancel (by positivity)] at this; nlinarith
  set KΓ := 2 * ℓ₀ ^ 2 + Ct + KG with hKΓ
  set Sb := 1 + KΓ + Cg + KG + Kf * (L : ℝ) ^ ((d : ℝ) - 2) with hSb
  set K' := Cg ^ 2 + Kl + KG + Kf * (L : ℝ) ^ ((d : ℝ) - 2) + Ca + 3 * Ct with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨bbar, 200 * Sb ^ 2 * K', KΓ, hbpos, hb1.trans hbw2, hb1.trans hbw1, by positivity,
    fun b hb hbb => hreal b hb (hbb.trans hb3), fun N hN b hb hbb x hx => ?_⟩
  have hbw : b ≤ bw := hbb.trans hb1
  have hb1' : b ≤ 1 := hbw.trans hbw1
  have hbn : ‖(b : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith
  have hbnorm : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]
  obtain ⟨ha0, -, E, hE, hid⟩ := hmain N hN b hb (hbb.trans hb2)
  obtain ⟨-, hGim, hΛim, hΛ1⟩ := hreal b hb (hbb.trans hb3)
  obtain ⟨w, hwT, hwG⟩ := hKf L hL2 N (by omega) x
  obtain ⟨et, het, heq⟩ := conn4pt_scaleN hd HW hbw2 hbw1 hK0 hKb h48 hall hh0 hCt HB hb hbw
    (by omega) ha0 hx hwT
  obtain ⟨hγN, -⟩ := anm0_scaleN hd HW hbw2 hbw1 hK0 hKb h48 hall hh0 hCt HB hb hbw
    (by omega) ha0 hx
  -- rates
  have hz0 : ∀ i, 0 ≤ redZ N (ctr d L N + x) i := redZ_nonneg N _
  have hla := lamA2_rate H hd1 hCs hS le_rfl hbn hN hx
  have hlb := lamB2_rate H hd1 hCs hS le_rfl hbn hN hx
  rw [← LamA_eq_LamB H hd1 hCs hS hd hbn hz0] at hlb
  have hga := gamA2_rate H hd1 hCs hS hd le_rfl hbn hN hx
  have hgb := gamB2_rate H hd1 hCs hS hd le_rfl hbn hN hx
  rw [← GamA_eq_GamB H hd1 hCs hS hd le_rfl hbn hz0] at hgb
  rw [hbnorm, ← hKl] at hla hlb
  rw [← hKG] at hga hgb
  -- the model parameters at `m² = 0`
  have hsb := (fv_model hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw).1 0 le_rfl
  have hc0 : 0 < c2F V₀c b 0 := c2F_pos hb (by linarith [hsb.1])
  have hc2 : c2F V₀c b 0 ≤ 2 * b := by
    unfold c2F; rw [div_le_iff₀ (by linarith [hsb.1])]; nlinarith [hsb.1]
  have hcard0 := Suscept.card_lam_pos (d := d) (L := L) N
  have hM : 0 < (Fintype.card (Lam d L N) : ℝ) * atR d L V₀c N b := mul_pos hcard0 ha0
  -- the Green's function
  have hrep : rep x ≠ 0 := fun h => hx (by rw [← prj_rep x, h]; exact Loc.prj_zero)
  set s : ℝ := (supNorm x : ℝ) with hs
  have hs1 : 1 ≤ s := by
    have : supNorm x ≠ 0 := fun h => hx ((supNorm_eq_zero_iff x).1 h)
    rw [hs]; exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hG := hCg (rep x) hrep
  rw [supNormZ_rep_eq_supNorm, ← hs] at hG
  set g := Cg * s ^ (-((d : ℝ) - 2)) with hg
  have hg0 : 0 ≤ g := by positivity
  have hgC : g ≤ Cg := by
    rw [hg]; exact mul_le_of_le_one_right hCg0 (Real.rpow_le_one_of_one_le_of_nonpos hs1
      (by linarith))
  -- the bounds of `conn_alg`
  have hθN1 : (L : ℝ) ^ (-(κ * N)) ≤ 1 := rpow_neg_mul_le_one hL1 hκ.le N
  have hρN1 : (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ≤ 1 :=
    rpow_neg_mul_le_one hL1 (by linarith) N
  have hδ1 : Kl * b * (L : ℝ) ^ (-(κ * N)) ≤ 1 := by
    have h1 : Kl * b ≤ 1 := (mul_le_mul_of_nonneg_left hbb hKl0).trans hKlb
    nlinarith [mul_le_mul_of_nonneg_left hθN1 (mul_nonneg hKl0 hb.le)]
  have he1 : Ca * b * (L : ℝ) ^ (-(min κ 1 * N)) ≤ 1 / 2 := by
    have h1 : Ca * b ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hbb hCa).trans hCab
    have h2 : (L : ℝ) ^ (-(min κ 1 * N)) ≤ 1 :=
      rpow_neg_mul_le_one hL1 (le_min hκ.le zero_le_one) N
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hCa hb.le)]
  have hΓ : ‖GamA d L V₀c lbar 0 b‖ ≤ KΓ := by
    have h2 : KG * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ≤ KG := mul_le_of_le_one_right hKG0 hρN1
    have h3 := norm_sub_norm_le (GamA d L V₀c lbar 0 b) (gamA2 d L N 0 (V₀c 0 b) lbar x)
    rw [norm_sub_rev] at h3
    have h4 : Ct * b ≤ Ct := mul_le_of_le_one_right hCt hb1'
    rw [hKΓ]
    linarith
  have hwG' : ‖(w : ℂ) - (greenZd d (rep x) : ℂ)‖ ≤
      Kf * (L : ℝ) ^ ((d : ℝ) - 2) * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine hwG.trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.rpow_add hL0]
    congr 2
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; push_cast; ring
  have hΛ1' := hLam b hb (hbb.trans hb2)
  have hmain' := conn_alg (b := b) (KΓ := KΓ) (g := g) (hc0) hc2 hb1' hΛ1' hΓ hE he1
    (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hG) hM hid hla hlb hδ1 hga hgb hwG'
    (by positivity) (by positivity) het (by have h := heq; rw [Complex.ofReal_sub, Complex.ofReal_one] at h; exact h)
  -- conversion to the real statement
  have eG : GamA d L V₀c lbar 0 b = (gamInf d L V₀c lbar b : ℂ) := Complex.ext rfl (by simp [hGim])
  have eΛ : LamA d L V₀c lbar 0 b = (lamInf d L V₀c lbar b : ℂ) := Complex.ext rfl (by simp [hΛim])
  rw [eG, eΛ] at hmain'
  have hLHS : ‖(H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _)
      (fun F => F.Reachable 0 x) : ℂ) - ((1 - (c2F V₀c b 0 : ℂ) * (gamInf d L V₀c lbar b : ℂ)) ^ 2 +
        2 * (c2F V₀c b 0 : ℂ) * (lamInf d L V₀c lbar b : ℂ) *
          (1 - (c2F V₀c b 0 : ℂ) * (gamInf d L V₀c lbar b : ℂ)) * (greenZd d (rep x) : ℂ))‖ =
      |H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _) (fun F => F.Reachable 0 x) -
          ((1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) ^ 2 + 2 * c2F V₀c b 0 *
            lamInf d L V₀c lbar b * (1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) *
              greenZd d (rep x))| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]; push_cast; rfl
  rw [hLHS] at hmain'
  refine ⟨?_, hmain'.trans ?_⟩
  · have := hΓ; rw [eG, Complex.norm_real, Real.norm_eq_abs] at this; exact this
  -- bounding the right-hand side
  set κ₁ := min κ 1 with hκ₁
  have hκ₁κ : κ₁ ≤ κ := min_le_left _ _
  have hκ₁1 : κ₁ ≤ 1 := min_le_right _ _
  have hκ₁0 : 0 ≤ κ₁ := le_min hκ.le zero_le_one
  set θN := (L : ℝ) ^ (-(κ * N))
  set ρN := (L : ℝ) ^ (-(((d : ℝ) - 2) * N))
  set θ₁ := (L : ℝ) ^ (-(κ₁ * N))
  set sN := s ^ (-((d : ℝ) - 2 + κ₁))
  have hθθ : θN ≤ θ₁ := rpow_neg_mul_mono_one hL1 hκ₁κ N
  have hs₁ : s ^ (-(2 * ((d : ℝ) - 2) + κ)) ≤ sN :=
    rpow_le_rpow_neg_of_one_le hs1 (by linarith)
  have hs₂ : s ^ (-((d : ℝ) - 2 + κ)) ≤ sN := rpow_le_rpow_neg_of_one_le hs1 (by linarith)
  have hgg : g ^ 2 ≤ Cg ^ 2 * sN := by
    have e : (s ^ (-((d : ℝ) - 2))) ^ 2 = s ^ (-(2 * ((d : ℝ) - 2))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; push_cast; ring_nf
    have h2 : s ^ (-(2 * ((d : ℝ) - 2))) ≤ sN := rpow_le_rpow_neg_of_one_le hs1 (by linarith)
    rw [hg, mul_pow, e]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hS : 1 + KΓ + g + KG * ρN + Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN ≤ Sb := by
    rw [hSb]
    have h1 : KG * ρN ≤ KG := mul_le_of_le_one_right hKG0 hρN1
    have h2 : Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN ≤ Kf * (L : ℝ) ^ ((d : ℝ) - 2) :=
      mul_le_of_le_one_right (by positivity) hρN1
    linarith
  have hS0 : 0 ≤ 1 + KΓ + g + KG * ρN + Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN := by positivity
  have hSS : (1 + KΓ + g + KG * ρN + Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN) ^ 2 ≤ Sb ^ 2 :=
    pow_le_pow_left₀ hS0 hS 2
  have hA1 : 0 ≤ b ^ 2 * sN := by positivity
  have hA2 : 0 ≤ b * ρN := by positivity
  have hA3 : 0 ≤ b ^ 2 * θ₁ := by positivity
  have hsum : b ^ 2 * g ^ 2 + b * (Kl * b * θN) + b * (KG * ρN) +
      b * (Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN) + b * (Ca * b * θ₁) +
      b ^ 2 * (Ct * b * s ^ (-(2 * ((d : ℝ) - 2) + κ))) +
      b * (Ct * b * (θN + s ^ (-((d : ℝ) - 2 + κ)))) ≤
      K' * (b ^ 2 * sN + b * ρN + b ^ 2 * θ₁) := by
    have i1 : b ^ 2 * g ^ 2 ≤ Cg ^ 2 * (b ^ 2 * sN) := by
      calc b ^ 2 * g ^ 2 ≤ b ^ 2 * (Cg ^ 2 * sN) := mul_le_mul_of_nonneg_left hgg (sq_nonneg b)
        _ = Cg ^ 2 * (b ^ 2 * sN) := by ring
    have i2 : b * (Kl * b * θN) ≤ Kl * (b ^ 2 * θ₁) := by
      calc b * (Kl * b * θN) = Kl * b ^ 2 * θN := by ring
        _ ≤ Kl * b ^ 2 * θ₁ := mul_le_mul_of_nonneg_left hθθ (mul_nonneg hKl0 (sq_nonneg b))
        _ = Kl * (b ^ 2 * θ₁) := by ring
    have i6 : b ^ 2 * (Ct * b * s ^ (-(2 * ((d : ℝ) - 2) + κ))) ≤ Ct * (b ^ 2 * sN) := by
      have h1 : b * s ^ (-(2 * ((d : ℝ) - 2) + κ)) ≤ sN := by
        calc b * s ^ (-(2 * ((d : ℝ) - 2) + κ)) ≤ 1 * sN :=
              mul_le_mul hb1' hs₁ (by positivity) zero_le_one
          _ = sN := one_mul _
      calc b ^ 2 * (Ct * b * s ^ (-(2 * ((d : ℝ) - 2) + κ))) =
            Ct * b ^ 2 * (b * s ^ (-(2 * ((d : ℝ) - 2) + κ))) := by ring
        _ ≤ Ct * b ^ 2 * sN := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCt (sq_nonneg b))
        _ = Ct * (b ^ 2 * sN) := by ring
    have i7 : b * (Ct * b * (θN + s ^ (-((d : ℝ) - 2 + κ)))) ≤
        Ct * (b ^ 2 * θ₁) + Ct * (b ^ 2 * sN) := by
      calc b * (Ct * b * (θN + s ^ (-((d : ℝ) - 2 + κ)))) =
            Ct * b ^ 2 * (θN + s ^ (-((d : ℝ) - 2 + κ))) := by ring
        _ ≤ Ct * b ^ 2 * (θ₁ + sN) :=
            mul_le_mul_of_nonneg_left (add_le_add hθθ hs₂) (mul_nonneg hCt (sq_nonneg b))
        _ = Ct * (b ^ 2 * θ₁) + Ct * (b ^ 2 * sN) := by ring
    have e3 : b * (KG * ρN) = KG * (b * ρN) := by ring
    have e4 : b * (Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN) = Kf * (L : ℝ) ^ ((d : ℝ) - 2) * (b * ρN) := by
      ring
    have e5 : b * (Ca * b * θ₁) = Ca * (b ^ 2 * θ₁) := by ring
    have hKfL : 0 ≤ Kf * (L : ℝ) ^ ((d : ℝ) - 2) :=
      mul_nonneg hKf0 (Real.rpow_nonneg hL0.le ((d : ℝ) - 2))
    have hCg2 : 0 ≤ Cg ^ 2 := sq_nonneg Cg
    have c1 : Cg ^ 2 + 2 * Ct ≤ K' := by rw [hK']; linarith
    have c2 : KG + Kf * (L : ℝ) ^ ((d : ℝ) - 2) ≤ K' := by rw [hK']; linarith
    have c3 : Kl + Ca + Ct ≤ K' := by rw [hK']; linarith
    have m1 := mul_le_mul_of_nonneg_right c1 hA1
    have m2 := mul_le_mul_of_nonneg_right c2 hA2
    have m3 := mul_le_mul_of_nonneg_right c3 hA3
    rw [e3, e4, e5]
    have eK : K' * (b ^ 2 * sN + b * ρN + b ^ 2 * θ₁) =
        K' * (b ^ 2 * sN) + K' * (b * ρN) + K' * (b ^ 2 * θ₁) := by ring
    rw [eK]
    have ea : (Cg ^ 2 + 2 * Ct) * (b ^ 2 * sN) = Cg ^ 2 * (b ^ 2 * sN) + 2 * (Ct * (b ^ 2 * sN)) := by
      ring
    have eb : (KG + Kf * (L : ℝ) ^ ((d : ℝ) - 2)) * (b * ρN) =
        KG * (b * ρN) + Kf * (L : ℝ) ^ ((d : ℝ) - 2) * (b * ρN) := by ring
    have ec : (Kl + Ca + Ct) * (b ^ 2 * θ₁) =
        Kl * (b ^ 2 * θ₁) + Ca * (b ^ 2 * θ₁) + Ct * (b ^ 2 * θ₁) := by ring
    rw [ea] at m1; rw [eb] at m2; rw [ec] at m3
    linarith
  have hsum0 : 0 ≤ b ^ 2 * g ^ 2 + b * (Kl * b * θN) + b * (KG * ρN) +
      b * (Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN) + b * (Ca * b * θ₁) +
      b ^ 2 * (Ct * b * s ^ (-(2 * ((d : ℝ) - 2) + κ))) +
      b * (Ct * b * (θN + s ^ (-((d : ℝ) - 2 + κ)))) := by positivity
  calc 200 * (1 + KΓ + g + KG * ρN + Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN) ^ 2 *
        (b ^ 2 * g ^ 2 + b * (Kl * b * θN) + b * (KG * ρN) +
          b * (Kf * (L : ℝ) ^ ((d : ℝ) - 2) * ρN) + b * (Ca * b * θ₁) +
          b ^ 2 * (Ct * b * s ^ (-(2 * ((d : ℝ) - 2) + κ))) +
          b * (Ct * b * (θN + s ^ (-((d : ℝ) - 2 + κ)))))
      ≤ 200 * Sb ^ 2 * (K' * (b ^ 2 * sN + b * ρN + b ^ 2 * θ₁)) := by
        gcongr
    _ = 200 * Sb ^ 2 * K' * (b ^ 2 * sN + b * ρN + b ^ 2 * θ₁) := by ring


end

end Ward
