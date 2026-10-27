import Spin2.Master.MasterL
import Obs2.Flow.Tau2Bd

/-!
# `GamLastRel`: the two `γ` steps above `N_h`

Pair history `obsInit .two (zV b) (ptsX x)`, `N = N_h + 2`. `GamLastRel c_L` asks
`‖β_{N_h}Γ_{N_h} - ρ_{N_h}‖ + ‖β_{N_h+1}C_N(0,0) - ρ_N‖ ≤ c_Lϑ_{N_h}ǧ_{N_h}`.

**Covariances (proved).** At the step `N_h` (`ValidAtL`) the step covariance satisfies `GoodCov2`
at the field scale `fscale(Z_{N_h+1})ℓ/4` (`RawInv.covL`), and at the last step (`ValidLast`) so
does `stCovN` at `fscale(Z_N)ℓ/4` (`LastN.covN`). Entries of a `GoodCov2` covariance are bounded by
the square of the field scale (`Obs2.good_entry`), so
`‖Γ_{N_h}‖ ≤ ℓ²/(16|Z_{N_h+1}|)` (`norm_gamT_top_le`) and `‖C_N(0,0)‖ ≤ ℓ²/(16|Z_N|)`
(`norm_zCovN_le`), with `|Z_N| ≥ (7/8)|Z_{N_h+1}|` (`|ζ| ≤ ρ ≤ 1/8`). `SpinConcl` at `n = N_h`
gives `1/|Z_{N_h+1}| ≤ e^{K_Z}θ_{N_h}` (`inv_normZ_le`). Hence both are `≤ K_Cθ_{N_h}`,
`K_C = ℓ²e^{K_Z}/14`.

**Arithmetic.** `bθ_k² = ϑ_kǧ_k` (`b_thJ_sq`).

**Named inputs (exactly).**
* **`BetaLast K_β`**: `‖β_{N_h}‖, ‖β_{N_h+1}‖ ≤ K_βbθ_{N_h}` — (H_λ)-type size of the pair vertex at
  the two top scales (`β_k = btX = bλ̂_k`, `λ̂_k ≈ θ_k`); (H_λ) itself (`HLam`) only covers `k < N_h`
  and is stated with `ǧ_k` of the bulk trajectory.
* **`GamLastRem c_r`**: `‖ρ_{N_h}‖ ≤ c_r‖β_{N_h}‖‖Γ_{N_h}‖`, `‖ρ_N‖ ≤ c_r‖β_{N_h+1}‖‖C_N(0,0)‖` —
  the `GamRemRel` shape at the two top steps, without the smallness factor `ǧ_k + a_k`
  (only the size is needed). The split `GamBulkRel`/`GamWKRel` is not used here: at `k = N_h` only
  `ValidAtL` is available (`gamRem2_split_hist` needs `ValidAt` at `k`), and the last step is
  `gamRemG` with `stCovN`.

**Results.** `gamLast_pure`; **`gamLastRel_of`** (trajectory level); **`gamLastRel_flow`**
(admissible trajectories under `FlowC2Concl`, `SpinConcl`, `LastValidConcl`):
`GamLastRel` with `c_L = 2(1 + c_r)K_β·ℓ²e^{K_Z}/14`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-! ### Arithmetic -/

/-- `bθ² = ϑǧ` with `θ = (ǧ/b)^{1/3}`, `ϑ = (b/ǧ)^{1/3}`. -/
theorem b_thJ_sq {g b : ℝ} (hg : 0 < g) (hb : 0 < b) :
    b * ((g / b) ^ (1 / 3 : ℝ)) ^ 2 = (b / g) ^ (1 / 3 : ℝ) * g := by
  have hu : 0 < g / b := div_pos hg hb
  set s := (g / b) ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hu _
  have h3 : s ^ 3 = g / b := by
    rw [hs, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hu.le (by norm_num)
  have hinv : (b / g) ^ (1 / 3 : ℝ) = s⁻¹ := by
    rw [hs, ← Real.inv_rpow hu.le, inv_div]
  rw [hinv]
  have hg' : g = b * s ^ 3 := by rw [h3]; field_simp
  rw [hg']
  field_simp

/-- `1/|Z| ≤ e^{K_Z}θ` from `|log|Z| + (1/3)log(ǧ/b)| ≤ K_Zǧ`, `ǧ ≤ 1`. -/
theorem inv_normZ_le {Z g b KZ : ℝ} (hZ : 0 < Z) (hg : 0 < g) (hg1 : g ≤ 1) (hb : 0 < b)
    (hKZ : 0 ≤ KZ) (h : |Real.log Z + 1 / 3 * Real.log (g / b)| ≤ KZ * g) :
    Z⁻¹ ≤ Real.exp KZ * (g / b) ^ (1 / 3 : ℝ) := by
  rw [Real.rpow_def_of_pos (div_pos hg hb), ← Real.exp_add, ← Real.exp_log hZ, ← Real.exp_neg]
  refine Real.exp_le_exp.2 ?_
  have h1 := (abs_le.1 h).1
  have h2 : KZ * g ≤ KZ := mul_le_of_le_one_right hKZ hg1
  linarith

/-- Pure assembly of `GamLastRel`. -/
theorem gamLast_pure {β0 β1 Γ C ρ0 ρ1 : ℂ} {Kβ KC cr bθ θ : ℝ} (hKβ : 0 ≤ Kβ) (hKC : 0 ≤ KC)
    (hcr : 0 ≤ cr) (hbθ : 0 ≤ bθ) (hθ : 0 ≤ θ) (h0 : ‖β0‖ ≤ Kβ * bθ) (h1 : ‖β1‖ ≤ Kβ * bθ)
    (hΓ : ‖Γ‖ ≤ KC * θ) (hC : ‖C‖ ≤ KC * θ) (hr0 : ‖ρ0‖ ≤ cr * ‖β0‖ * ‖Γ‖)
    (hr1 : ‖ρ1‖ ≤ cr * ‖β1‖ * ‖C‖) :
    ‖β0 * Γ - ρ0‖ + ‖β1 * C - ρ1‖ ≤ 2 * (1 + cr) * Kβ * KC * (bθ * θ) := by
  have key : ∀ {β G ρ : ℂ}, ‖β‖ ≤ Kβ * bθ → ‖G‖ ≤ KC * θ → ‖ρ‖ ≤ cr * ‖β‖ * ‖G‖ →
      ‖β * G - ρ‖ ≤ (1 + cr) * Kβ * KC * (bθ * θ) := by
    intro β G ρ hβ hG hρ
    have hp : ‖β‖ * ‖G‖ ≤ (Kβ * bθ) * (KC * θ) :=
      mul_le_mul hβ hG (norm_nonneg _) (mul_nonneg hKβ hbθ)
    calc ‖β * G - ρ‖ ≤ ‖β * G‖ + ‖ρ‖ := norm_sub_le _ _
      _ ≤ (1 + cr) * (‖β‖ * ‖G‖) := by rw [norm_mul]; linarith
      _ ≤ (1 + cr) * ((Kβ * bθ) * (KC * θ)) :=
          mul_le_mul_of_nonneg_left hp (by linarith)
      _ = (1 + cr) * Kβ * KC * (bθ * θ) := by ring
  have e : 2 * (1 + cr) * Kβ * KC * (bθ * θ) =
      (1 + cr) * Kβ * KC * (bθ * θ) + (1 + cr) * Kβ * KC * (bθ * θ) := by ring
  rw [e]
  exact add_le_add (key h0 hΓ hr0) (key h1 hC hr1)

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-! ### The covariances of the two top steps -/

theorem fscale_sq (Z : ℂ) (ℓ : ℝ) : (fscale Z * ℓ / 4) ^ 2 = ℓ ^ 2 / 16 * ‖Z‖⁻¹ := by
  unfold fscale
  rw [div_pow, mul_pow, Real.sq_sqrt (inv_nonneg.2 (norm_nonneg _))]
  ring

/-- `‖Γ_{N_h}‖ ≤ ℓ²/(16|Z_{N_h+1}|)` (`GoodCov2` of the step covariance under `ValidAtL`). -/
theorem norm_gamT_top_le (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh) :
    ‖gamT R m b μ₀ Nh‖ ≤ R.ℓ ^ 2 / 16 *
      ‖(rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖⁻¹ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  have H := rawInv_histU (R.withMsq m) hV hVL t Nh (by omega)
  have hC := (RawInv.covL hVL.2 H).1
  have e : gamT R m b μ₀ Nh = rawCov (R.withMsq m) Nh
      (RawInv.zeta' (R.withMsq m) Nh (rawHist (R.withMsq m) Nh t)) 0 0 := by
    unfold gamT; rw [← histCov_gamInt R hP]; rfl
  rw [e]
  refine (Obs2.good_entry hC 0 0).trans (le_of_eq ?_)
  rw [fscale_sq]
  rfl

/-- `‖C_N(0,0)‖ ≤ ℓ²/(16|Z_N|)` (`GoodCov2` of `stCovN` under `ValidLast`). -/
theorem norm_zCovN_le {Nh : ℕ} {m b μ₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) :
    ‖zCovN R Nh m b μ₀‖ ≤ R.ℓ ^ 2 / 16 * ‖stZ' (R.withMsq m)
      (rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))‖⁻¹ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  have H := rawInv_histU (R.withMsq m) hV hVL t (Nh + 1) le_rfl
  have hC := (LastN.covN hVN H).1
  refine (Obs2.good_entry hC 0 0).trans (le_of_eq ?_)
  rw [fscale_sq]
  rfl

/-- `|Z_N| ≥ (7/8)|Z_{N_h+1}|`. -/
theorem norm_stZ'_ge {j : ℕ} (st : RawSt 2 L N) (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) :
    7 / 8 * ‖st.Z‖ ≤ ‖stZ' R st‖ := by
  unfold stZ'
  rw [norm_mul]
  have hz : ‖stZeta R st‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ8
  have h1 : 7 / 8 ≤ ‖1 + stZeta R st‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-stZeta R st)
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have := mul_le_mul_of_nonneg_left h1 (norm_nonneg st.Z)
  linarith

/-! ### The named inputs -/

/-- **Named input (pair vertex at the two top scales)**:
`‖β_{N_h}‖, ‖β_{N_h+1}‖ ≤ K_βbθ_{N_h}`. -/
def BetaLast (Nh : ℕ) (m b μ₀ Kβ : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖btX R m b μ₀ x Nh‖ ≤ Kβ * b * thJ R m b μ₀ Nh ∧
      ‖btX R m b μ₀ x (Nh + 1)‖ ≤ Kβ * b * thJ R m b μ₀ Nh

/-- **Named input (the remainders of the two top steps)**, in the `GamRemRel` shape:
`‖ρ_{N_h}‖ ≤ c_r‖β_{N_h}‖‖Γ_{N_h}‖`, `‖ρ_N‖ ≤ c_r‖β_{N_h+1}‖‖C_N(0,0)‖`. -/
def GamLastRem (Nh : ℕ) (m b μ₀ cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖gamRemX R m b μ₀ x Nh‖ ≤ cr * ‖btX R m b μ₀ x Nh‖ * ‖gamT R m b μ₀ Nh‖ ∧
      ‖gamRemN R Nh m b μ₀ x‖ ≤ cr * ‖btX R m b μ₀ x (Nh + 1)‖ * ‖zCovN R Nh m b μ₀‖

/-- The covariance sizes `‖Γ_{N_h}‖, ‖C_N(0,0)‖ ≤ (ℓ²e^{K_Z}/14)θ_{N_h}`. -/
theorem gamT_zCovN_le (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ KZ : ℝ} (hb : 0 < b) (hKZ : 0 ≤ KZ)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hg : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hZ0 : (rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0)
    (hZ : |Real.log ‖(rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
      1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 / b)| ≤
      KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) :
    ‖gamT R m b μ₀ Nh‖ ≤ R.ℓ ^ 2 * Real.exp KZ / 14 * thJ R m b μ₀ Nh ∧
      ‖zCovN R Nh m b μ₀‖ ≤ R.ℓ ^ 2 * Real.exp KZ / 14 * thJ R m b μ₀ Nh := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  set Z := (rawHist (R.withMsq m) (Nh + 1) t).Z with hZd
  have hZp : 0 < ‖Z‖ := norm_pos_iff.2 hZ0
  have hinv := inv_normZ_le hZp hg hg1 hb hKZ hZ
  have hθ : 0 ≤ thJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hg hb).le _
  have hℓ : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  have hE : 0 ≤ Real.exp KZ * thJ R m b μ₀ Nh := mul_nonneg (Real.exp_pos _).le hθ
  have hinv' : ‖Z‖⁻¹ ≤ Real.exp KZ * thJ R m b μ₀ Nh := hinv
  constructor
  · refine (norm_gamT_top_le R hP hV hVL).trans ?_
    have := mul_le_mul_of_nonneg_left hinv' (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 / 16)
    have h2 : R.ℓ ^ 2 / 16 * (Real.exp KZ * thJ R m b μ₀ Nh) ≤
        R.ℓ ^ 2 * Real.exp KZ / 14 * thJ R m b μ₀ Nh := by
      have := mul_nonneg hℓ hE
      nlinarith
    exact this.trans h2
  · refine (norm_zCovN_le R hV hVL hVN).trans ?_
    have hρ0 : 0 ≤ (R.withMsq m).ρ := hVN.2.2.2.1
    have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVN.2.2.2.2.1
    have hZ' := norm_stZ'_ge (R.withMsq m) (j := Nh) (rawHist (R.withMsq m) (Nh + 1) t) hρ0 hρ8
    have hZ'p : 0 < 7 / 8 * ‖Z‖ := by positivity
    have hi : ‖stZ' (R.withMsq m) (rawHist (R.withMsq m) (Nh + 1) t)‖⁻¹ ≤ 8 / 7 * ‖Z‖⁻¹ := by
      have := inv_anti₀ hZ'p hZ'
      rw [mul_inv, inv_div] at this
      exact this
    have h1 := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 / 16)
    have h2 : R.ℓ ^ 2 / 16 * (8 / 7 * ‖Z‖⁻¹) ≤ R.ℓ ^ 2 * Real.exp KZ / 14 * thJ R m b μ₀ Nh := by
      have := mul_le_mul_of_nonneg_left hinv' hℓ
      have e1 : R.ℓ ^ 2 / 16 * (8 / 7 * ‖Z‖⁻¹) = R.ℓ ^ 2 * ‖Z‖⁻¹ / 14 := by ring
      have e2 : R.ℓ ^ 2 * Real.exp KZ / 14 * thJ R m b μ₀ Nh =
          R.ℓ ^ 2 * (Real.exp KZ * thJ R m b μ₀ Nh) / 14 := by ring
      rw [e1, e2]
      linarith
    exact h1.trans h2

/-- **`GamLastRel` along one trajectory**, `c_L = 2(1 + c_r)K_β·ℓ²e^{K_Z}/14`. -/
theorem gamLastRel_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ KZ Kβ cr : ℝ} (hb : 0 < b) (hKZ : 0 ≤ KZ)
    (hKβ : 0 ≤ Kβ) (hcr : 0 ≤ cr)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hg : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hZ0 : (rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0)
    (hZ : |Real.log ‖(rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
      1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 / b)| ≤
      KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hβ : BetaLast R Nh m b μ₀ Kβ) (hr : GamLastRem R Nh m b μ₀ cr) :
    GamLastRel R Nh m b μ₀ (2 * (1 + cr) * Kβ * (R.ℓ ^ 2 * Real.exp KZ / 14)) := by
  intro x hx h1 hj
  obtain ⟨hΓ, hC⟩ := gamT_zCovN_le R hP hb hKZ hV hVL hVN hg hg1 hZ0 hZ
  obtain ⟨hβ0, hβ1⟩ := hβ x hx h1 hj
  obtain ⟨hr0, hr1⟩ := hr x hx h1 hj
  have hθ : 0 ≤ thJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hg hb).le _
  have hKC : 0 ≤ R.ℓ ^ 2 * Real.exp KZ / 14 := by positivity
  have h := gamLast_pure hKβ hKC hcr (mul_nonneg hb.le hθ) hθ
    (by rw [← mul_assoc]; exact hβ0) (by rw [← mul_assoc]; exact hβ1) hΓ hC hr0 hr1
  have e : b * thJ R m b μ₀ Nh * thJ R m b μ₀ Nh =
      varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    rw [mul_assoc, ← sq]; exact b_thJ_sq hg hb
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  ring

end Traj

/-- **`GamLastRel` along the admissible trajectories** (`FlowC2Concl`, `ε ≤ 1`, `SpinConcl`,
`LastValidConcl`): `BetaLast K_β` and `GamLastRem c_r` give `GamLastRel` with
`c_L = 2(1 + c_r)K_β·ℓ²e^{K_Z}/14`. -/
theorem gamLastRel_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ)
    (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) (hLV : LastValidConcl L ℓ ρ) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ Kβ cr : ℝ, 0 ≤ Kβ → 0 ≤ cr → BetaLast R Nh m b μ₀ Kβ → GamLastRem R Nh m b μ₀ cr →
      GamLastRel R Nh m b μ₀ (2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm Kβ cr hKβ hcr hβ hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
  obtain ⟨hV, hVL⟩ := (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hZ0, hZ⟩ :=
    (hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.2.2.1 m hm b μ₀ hadm Nh le_rfl
  have h := gamLastRel_of R hP hb hKZ hKβ hcr hV hVL hVN (hadm.1 Nh le_rfl).1
    (((hadm.1 Nh le_rfl).2.1).trans hε1) hZ0 hZ hβ hr
  rwa [hRℓ] at h

end

end Spin2
