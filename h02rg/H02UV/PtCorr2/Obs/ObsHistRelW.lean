import PtCorr2.Obs.ObsHistRel
import Obs2.Flow.BlockFlow3

/-!
# The relative coupled recursion along the history, with uniform constants

`obs_hist_rel` asks for `|τ(C_k, C_j)(a)| ≤ B_τ (L^{-2})^{j-k}` with `B_τ ≥ 18 ℓ_M⁴`, where
`ℓ_M = ellM R n t = ∑_{i ≤ n} fscale(Z_{i+1})ℓ/4` is a *sum* over the scales (so `B_τ` grows like
`n⁴`), and for the absolute couplings `|g'_i| ≤ c_g r_i`, `|g'_{i+1} − g'_i| ≤ c_g r_i²` with
`g'_i = ǧ_iZ_{i+1}²/(1 + n_i)`. Since `C_k` lives at the scale `ℓ_k = |Z_{k+1}|^{-1/2}ℓ/4` and
`|Z_j| → 0` along the flow, neither is uniform. Here the weighted recursion
(`Obs2.MuChain.rel_flow_w`) is used with `w_i = |Z_{i+1}|²`:

* `norm_tauC_le2`: the tadpole between two scales with two Gram constants,
  `|τ(C, Γ)| ≤ 18 ℓ_C² ℓ_Γ² (L^{-2})^{j-k}`;
* `norm_Z_succ`, `zH_ratio_up`, `zH_ratio_down`: `|Z_{i+1}| = |Z_i||1+ζ_i|`, `|ζ_i| ≤ 1/8`, hence
  `|Z_m|/|Z_l|, |Z_l|/|Z_m| ≤ (8/7)^{m-l}`;
* **`hist_tau_w`**: `|τ(C_k, C_j)(a)| |Z_{i+1}|² ≤ (9ℓ⁴/128)(2L^{-2})^{j-k}` for `k ≤ i < j`;
* `kapH`, **`muChain_obsHist_kap`**: the `MuChain` of the history with the explicit couplings
  `κ'_k = (z♭, y♭, ν♭, ǧ_kZ_{k+1}²/(1+n_k)).shift 2 c₀ δ`;
* the rescaled bulk bounds **`hist_G_w`** (`|g'_i|/|Z_{i+1}|² ≤ (8/7)ǧ_i`), **`hist_frakN_le`**
  (`|𝔫_i| ≤ c_n ǧ_i`), **`hist_dg_w`** (`|g'_{i+1} − g'_i|/|Z_{i+1}|² ≤ c_d ǧ_i²`), and the band
  increment `ǧ_{i+1} ≥ ǧ_i + (β/4)ǧ_i²` (`hist_inc`) from the regularity of the history;
* **`obs_hist_rel_w`**: the relative coupled recursion along a regular history with these
  discharged; the remaining named inputs are the `ℓ¹` product bound `ProdBd` (with ratio
  `q ∈ [2L^{-2}, 1/4]`), the initial state (`D_0 = 0`, `β_0 ≠ 0`), and the choice of `c_δ`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-! ### The tadpole between two scales -/

/-- **The tadpole between scales, two Gram constants**:
`|τ(C_k, Γ_j)(a)| ≤ 18 ℓ_C² ℓ_Γ² (L^{-2})^{j-k}`. -/
theorem norm_tauC_le2 {j k : ℕ} (hk : k ≤ j) (hkN : k + 1 < N) {ℓC ℓΓ : ℝ}
    {C Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : GoodCov2 k ℓC C) (hT : TInv C)
    (hs : ∀ x y, C x y = C y x) (hΓ : GoodCov2 j ℓΓ Γ) {c₀ δ : ℂ} (hc : ∀ x, Γ x x = c₀)
    (hδ : ∀ x e, Γ (x + dirVec e) x = c₀ + δ) (hδ' : ∀ x e, Γ x (x + dirVec e) = c₀ + δ)
    (a : Lam 2 L N) :
    ‖tauC C Γ a‖ ≤ 18 * ℓC ^ 2 * ℓΓ ^ 2 * (((L : ℝ) ^ 2)⁻¹) ^ (j - k) := by
  rw [tauC_TI C Γ a c₀ δ hc hδ hδ', sum_row_eq_zero_mode hT hs]
  have hz := zero_mode_le hkN hC
  have hd := (cov_c0_delta_le hΓ hc hδ hδ').2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  have e4 : ‖(2 : ℂ) * ((2 : ℕ) : ℂ) * δ * ∑ x, C x 0‖ = 4 * ‖δ‖ * ‖∑ x, C x 0‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    norm_num
  rw [e4]
  have hpow : ((L : ℝ) ^ (k + m + 1)) ^ 2 = ((L : ℝ) ^ (k + 1)) ^ 2 * ((L : ℝ) ^ 2) ^ m := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  have hq : (((L : ℝ) ^ 2)⁻¹) ^ m = ((L : ℝ) ^ (k + 1)) ^ 2 / ((L : ℝ) ^ (k + m + 1)) ^ 2 := by
    rw [hpow, inv_pow]
    field_simp
  rw [hq]
  calc 4 * ‖δ‖ * ‖∑ x, C x 0‖
      ≤ 4 * (ℓΓ ^ 2 / (2 * ((L : ℝ) ^ (k + m + 1)) ^ 2)) *
          (9 * ((L : ℝ) ^ (k + 1)) ^ 2 * ℓC ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hz (norm_nonneg _)
          (by positivity)
    _ = 18 * ℓC ^ 2 * ℓΓ ^ 2 * (((L : ℝ) ^ (k + 1)) ^ 2 / ((L : ℝ) ^ (k + m + 1)) ^ 2) := by
        field_simp; ring

/-! ### Ratios of a sequence with bounded steps -/

theorem ratio_up {u : ℕ → ℝ} (h : ∀ i, u (i + 1) ≤ 8 / 7 * u i) {l : ℕ} :
    ∀ m, l ≤ m → u m ≤ (8 / 7 : ℝ) ^ (m - l) * u l := by
  intro m hlm
  induction m, hlm using Nat.le_induction with
  | base => simp
  | succ m hlm ih =>
    rw [show m + 1 - l = (m - l) + 1 by omega, pow_succ]
    calc u (m + 1) ≤ 8 / 7 * u m := h m
      _ ≤ 8 / 7 * ((8 / 7 : ℝ) ^ (m - l) * u l) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by ring

theorem ratio_down {u : ℕ → ℝ} (h : ∀ i, u i ≤ 8 / 7 * u (i + 1)) {l : ℕ} :
    ∀ m, l ≤ m → u l ≤ (8 / 7 : ℝ) ^ (m - l) * u m := by
  intro m hlm
  exact le_pow_mul_of_step (by norm_num) (fun i _ => h i) l hlm

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `|Z_i|` along the history. -/
abbrev zH (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) : ℝ := ‖(rawHist R i t).Z‖

theorem norm_Z_succ (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) :
    zH R t (i + 1) = zH R t i * ‖1 + zetaH R i t‖ := by
  simp only [zH, rawHist_succ_Z, norm_mul]

theorem one_add_zeta_bds (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) :
    7 / 8 ≤ ‖1 + zetaH R i t‖ ∧ ‖1 + zetaH R i t‖ ≤ 9 / 8 := by
  have hz : ‖zetaH R i t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
  have h2 := norm_sub_norm_le (1 : ℂ) (-zetaH R i t)
  have h3 := norm_add_le (1 : ℂ) (zetaH R i t)
  rw [norm_one, norm_neg, sub_neg_eq_add] at h2
  rw [norm_one] at h3
  constructor <;> linarith

theorem zH_pos (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ i, 0 < zH R t i
  | 0 => by simp [zH, rawHist]
  | i + 1 => by
    rw [norm_Z_succ]
    exact mul_pos (zH_pos hρ0 hρ t i) (by linarith [(one_add_zeta_bds R hρ0 hρ t i).1])

theorem zH_ratio_up (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) {l m : ℕ}
    (hlm : l ≤ m) : zH R t m ≤ (8 / 7 : ℝ) ^ (m - l) * zH R t l := by
  refine ratio_up (fun i => ?_) m hlm
  rw [norm_Z_succ]
  have := (one_add_zeta_bds R hρ0 hρ t i).2
  have := zH_pos R hρ0 hρ t i
  nlinarith

theorem zH_ratio_down (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) {l m : ℕ}
    (hlm : l ≤ m) : zH R t l ≤ (8 / 7 : ℝ) ^ (m - l) * zH R t m := by
  refine ratio_down (fun i => ?_) m hlm
  rw [norm_Z_succ]
  have := (one_add_zeta_bds R hρ0 hρ t i).1
  have := zH_pos R hρ0 hρ t i
  nlinarith

/-- The Gram constant of step `i`: `ℓ_i² = ℓ²/(16|Z_{i+1}|)`. -/
theorem ellI_sq (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) :
    (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) ^ 2 = R.ℓ ^ 2 / (16 * zH R t (i + 1)) := by
  have e : stZ' R (rawHist R i t) = (rawHist R (i + 1) t).Z := rfl
  rw [div_pow, mul_pow, fscale_sq, e]
  field_simp
  ring

/-- The covariance of step `i ≤ n` at its own Gram scale. -/
theorem histCovO_props_i {n : ℕ} (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n)
    (t : Flow2.Hist.Seq (Xs R)) {i : ℕ} (hi : i ≤ n) :
    GoodCov2 i (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) (histCovO R t i) ∧
      TInv (histCovO R t i) ∧ CSym (histCovO R t i) ∧
      ∀ x y, histCovO R t i x y = histCovO R t i y x := by
  have H := rawInv_histU R hV hVL t i (by omega)
  exact covU R hV hVL hi H

/-- **The rescaled tadpole decay**: for `k ≤ i < j ≤ n < N`,
`|τ(C_k, C_j)(a)| |Z_{i+1}|² ≤ (9ℓ⁴/128)(2L^{-2})^{j-k}`. -/
theorem hist_tau_w (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hN : n < N)
    (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (a : Lam 2 L N) {k i j : ℕ} (hki : k ≤ i) (hij : i ≤ j) (hj : j ≤ n) (hkj : k < j) :
    ‖tauC (histCovO R t k) (histCovO R t j) a‖ * zH R t (i + 1) ^ 2 ≤
      9 * R.ℓ ^ 4 / 128 * (2 * ((L : ℝ) ^ 2)⁻¹) ^ (j - k) := by
  obtain ⟨hCk, hTk, -, hsk⟩ := histCovO_props_i R hV hVL t (i := k) (by omega)
  obtain ⟨hCj, -, hCsj, hsj⟩ := histCovO_props_i R hV hVL t hj
  obtain ⟨c₀, δ, hc, hδ, hδ'⟩ := covProps (by norm_num) hCsj hsj
  have hτ := norm_tauC_le2 (by omega : k ≤ j) (by omega) hCk hTk hsk hCj hc hδ hδ' a
  rw [ellI_sq, ellI_sq] at hτ
  have hzk := zH_pos R hρ0 hρ t (k + 1)
  have hzj := zH_pos R hρ0 hρ t (j + 1)
  have hzi := zH_pos R hρ0 hρ t (i + 1)
  have h1 := zH_ratio_up R hρ0 hρ t (show k + 1 ≤ i + 1 by omega)
  have h2 := zH_ratio_down R hρ0 hρ t (show i + 1 ≤ j + 1 by omega)
  have hℓ : 0 < R.ℓ := Fact.out
  set q := ((L : ℝ) ^ 2)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  -- `|Z_{i+1}|² ≤ (8/7)^{j-k} |Z_{k+1}| |Z_{j+1}|`
  have hZ : zH R t (i + 1) ^ 2 ≤ (8 / 7 : ℝ) ^ (j - k) * (zH R t (k + 1) * zH R t (j + 1)) := by
    have e : (8 / 7 : ℝ) ^ (j - k) = (8 / 7 : ℝ) ^ (i + 1 - (k + 1)) * (8 / 7 : ℝ) ^ (j + 1 - (i + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [e, sq]
    have := mul_le_mul h1 h2 hzi.le (by positivity)
    nlinarith
  have hp : (8 / 7 : ℝ) ^ (j - k) * q ^ (j - k) ≤ (2 * q) ^ (j - k) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  calc ‖tauC (histCovO R t k) (histCovO R t j) a‖ * zH R t (i + 1) ^ 2
      ≤ 18 * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) * (R.ℓ ^ 2 / (16 * zH R t (j + 1))) * q ^ (j - k) *
          ((8 / 7 : ℝ) ^ (j - k) * (zH R t (k + 1) * zH R t (j + 1))) :=
        mul_le_mul hτ hZ (sq_nonneg _) (by positivity)
    _ = 9 * R.ℓ ^ 4 / 128 * ((8 / 7 : ℝ) ^ (j - k) * q ^ (j - k)) := by
        field_simp; ring
    _ ≤ 9 * R.ℓ ^ 4 / 128 * (2 * q) ^ (j - k) := mul_le_mul_of_nonneg_left hp (by positivity)

/-! ### The `MuChain` of the history with explicit couplings -/

/-- The coupling vector of `V♭_k`. -/
def vH (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) : Fin 4 → ℂ :=
  ![(rawHist R k t).z + stYc R (rawHist R k t) - stA R (rawHist R k t),
    (rawHist R k t).y - stYc R (rawHist R k t),
    stNu R k (rawHist R k t) (t k).2.1 - stA R (rawHist R k t) * R.msq,
    stGr R k (rawHist R k t) (t k).1 (t k).2.1 * stZ' R (rawHist R k t) ^ 2]

/-- `c₀ = C_k(0,0)`. -/
def c0H (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) : ℂ := histCovO R t k 0 0

/-- `δ = C_k(e,0) − C_k(0,0)`. -/
def dH (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) : ℂ :=
  histCovO R t k (0 + dirVec (Sum.inl (0 : Fin 2))) 0 - c0H R t k

/-- **The couplings of the chain**: `κ'_k = κ♭_k.shift 2 c₀ δ`. -/
def kapH (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) : Step2.Coup :=
  (Coup.ofVec (vH R t k)).shift 2 (c0H R t k) (dH R t k)

theorem kapH_g (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) :
    (kapH R t k).g = stGr R k (rawHist R k t) (t k).1 (t k).2.1 * stZ' R (rawHist R k t) ^ 2 := rfl

theorem kapH_nu (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) :
    (kapH R t k).nu = (stNu R k (rawHist R k t) (t k).2.1 - stA R (rawHist R k t) * R.msq) +
      2 * ((2 : ℕ) : ℂ) * (stGr R k (rawHist R k t) (t k).1 (t k).2.1 * stZ' R (rawHist R k t) ^ 2) *
        dH R t k := rfl

/-- The covariance constants of step `k ≤ n` are `c0H`, `dH`. -/
theorem covH_consts {n : ℕ} (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n)
    (t : Flow2.Hist.Seq (Xs R)) {k : ℕ} (hk : k ≤ n) :
    (∀ x, histCovO R t k x x = c0H R t k) ∧
      (∀ x e, histCovO R t k (x + dirVec e) x = c0H R t k + dH R t k) ∧
      (∀ x e, histCovO R t k x (x + dirVec e) = c0H R t k + dH R t k) := by
  obtain ⟨-, -, hCs, hCsym⟩ := histCovO_props_i R hV hVL t hk
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num : 1 ≤ 2) hCs hCsym
  have e1 : c0H R t k = c₀ := hc₀ 0
  have e2 : dH R t k = δ := by
    unfold dH; rw [hδ 0 (Sum.inl 0), e1]; ring
  rw [e1, e2]
  exact ⟨hc₀, hδ, hδ'⟩

/-- **`MuChain` along the history with the explicit couplings `kapH`.** -/
theorem muChain_obsHist_kap (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Flow2.Hist.Seq (Xs R))
    {n : ℕ} (hN : n < N) (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n)
    (h₀ : o₀.IsObs) (hW0 : ∀ b, (o₀.W b : SA .one (Lam 2 L N)).a = 0)
    (hV0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) :
    ∃ r : ℕ → ℂ,
      MuChain P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t)
        (kapH R t) r n := by
  have hr : ∀ k, ∃ r : ℂ, k ≤ n →
      (VprLO k (histCovO R t k) (histVO R P o₀ t k) : SA .one (Lam 2 L N)).e =
        Vcoup (kapH R t k) univ + r • (1 : Alg 2 L N) := by
    intro k
    by_cases hk : k ≤ n
    · obtain ⟨hc₀, hδ, hδ'⟩ := covH_consts R hV hVL t hk
      obtain ⟨r, hr⟩ := histVprLO_e R P o₀ t (obsHist_isObs R P o₀ h₀ k t) hc₀ hδ hδ'
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose r hr using hr
  exact ⟨r,
    { hN := hN
      hW0 := fun b => by rw [histWO_a]; exact hW0 b
      hW := fun k _ c' => histWO_succ_a R P o₀ t k c'
      hV := fun k _ c' => histVO_succ_a R P o₀ t k c'
      hform := fun k _ b => eq_mass1_smul_of_span (obsHist_hform R P o₀ t hV0 k b)
      he := fun k hk => hr k hk }⟩

/-! ### Pure estimates -/

/-- `‖g/(1+n)‖ ≤ (8/7) g`. -/
theorem norm_gr_le {g : ℝ} (hg : 0 ≤ g) (n : ℂ) (hn : ‖n‖ ≤ 1 / 8) :
    ‖(g : ℂ) / (1 + n)‖ ≤ 8 / 7 * g := by
  have h1 : 7 / 8 ≤ ‖1 + n‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-n); rw [norm_one, norm_neg, sub_neg_eq_add] at this; linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg, div_le_iff₀ (by linarith)]
  nlinarith

/-- The increment of `ǧ(1+ζ)²/(1+n')` against `ǧ/(1+n)`. -/
theorem norm_gr_diff_le {g g' : ℝ} (hg : 0 ≤ g) (hg' : 0 ≤ g') {n n' ζ : ℂ} (hn : ‖n‖ ≤ 1 / 8)
    (hn' : ‖n'‖ ≤ 1 / 8) (hζ : ‖ζ‖ ≤ 1 / 8) :
    ‖(g' : ℂ) / (1 + n') * (1 + ζ) ^ 2 - (g : ℂ) / (1 + n)‖ ≤
      64 / 49 * (9 / 8 * |g' - g| + g * (‖n‖ + ‖n'‖)) + 8 / 7 * g' * (17 / 8 * ‖ζ‖) := by
  have h1 : 7 / 8 ≤ ‖1 + n‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-n); rw [norm_one, norm_neg, sub_neg_eq_add] at this; linarith
  have h1' : 7 / 8 ≤ ‖1 + n'‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-n'); rw [norm_one, norm_neg, sub_neg_eq_add] at this; linarith
  have hne : (1 + n) ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  have hne' : (1 + n') ≠ 0 := fun h => by rw [h, norm_zero] at h1'; linarith
  have e : (g' : ℂ) / (1 + n') * (1 + ζ) ^ 2 - (g : ℂ) / (1 + n) =
      ((g' - g : ℂ) * (1 + n) + g * (n - n')) / ((1 + n) * (1 + n')) +
        (g' : ℂ) / (1 + n') * (ζ * (2 + ζ)) := by
    field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, div_le_iff₀ (by positivity)]
    have hnum : ‖((g' - g : ℂ)) * (1 + n) + g * (n - n')‖ ≤ 9 / 8 * |g' - g| + g * (‖n‖ + ‖n'‖) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, show ((g' : ℂ) - g) = ((g' - g : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
        have := norm_add_le (1 : ℂ) n; rw [norm_one] at this
        calc |g' - g| * ‖1 + n‖ ≤ |g' - g| * (9 / 8) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = 9 / 8 * |g' - g| := by ring
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hg
    have hpos : 0 ≤ 9 / 8 * |g' - g| + g * (‖n‖ + ‖n'‖) := by positivity
    have h2 : 49 / 64 ≤ ‖1 + n‖ * ‖1 + n'‖ := by nlinarith
    nlinarith
  · rw [norm_mul]
    refine mul_le_mul (norm_gr_le hg' n' hn') ?_ (norm_nonneg _) (by positivity)
    rw [norm_mul]
    have := norm_add_le (2 : ℂ) ζ
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at this
    nlinarith [norm_nonneg ζ]

/-! ### The bulk bounds along the history -/

section Bulk

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- `|n_i| ≤ 4|μ_i|ℓ²` from `|Z_{i+1}w^{(1)}_i| ≤ ℓ²L^{2i}`. -/
theorem norm_nCor_hist_le (st : RawSt 2 L N) (i : ℕ) (μ : ℝ)
    (hZw : ‖stZ' R st * st.w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ i) ^ 2) :
    ‖nCor (stNu R i st μ) st.w1‖ ≤ 4 * |μ| * R.ℓ ^ 2 := by
  refine (norm_clampDisk_le_self (by norm_num) _).trans ?_
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e : 4 * stNu R i st μ * st.w1 = 4 * (μ : ℂ) * (stZ' R st * st.w1) / (L : ℂ) ^ (2 * i) := by
    unfold stNu; ring
  rw [e, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
    Complex.norm_natCast, div_le_iff₀ (by positivity)]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4, show ((L : ℝ) ^ (2 * i)) = ((L : ℝ) ^ i) ^ 2 by ring]
  have := abs_nonneg μ
  nlinarith

/-- `|ζ_i| ≤ 2 c_Z ǧ_i` (the a priori bounds). -/
theorem norm_zetaH_le (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (t : Flow2.Hist.Seq (Xs R)) {j : ℕ} (hj : j ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) :
    ‖zetaH R j t‖ ≤ 2 * cZ R * (t j).1 := by
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H j hj t ht
  refine (norm_clampDisk_le_self hρ0 _).trans ?_
  rw [add_div]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **The rescaled quartic coupling**: `|g'_i|/|Z_{i+1}|² = |ǧ_i/(1+n_i)| ≤ (8/7)ǧ_i`. -/
theorem hist_G_w (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) (i : ℕ)
    (hg : 0 ≤ (t i).1) : ‖(kapH R t i).g‖ / zH R t (i + 1) ^ 2 ≤ 8 / 7 * (t i).1 := by
  have hz := zH_pos R hρ0 hρ t (i + 1)
  have e : zH R t (i + 1) = ‖stZ' R (rawHist R i t)‖ := rfl
  rw [kapH_g, norm_mul, norm_pow, ← e, mul_div_assoc, div_self (by positivity), mul_one]
  exact norm_gr_le hg _ (norm_nCor_le _ _)

/-- **The bound on `𝔫_i`**: `|𝔫_i| ≤ (ℓ²L²(c_μ + 3c_z) + ℓ⁴) ǧ_i`. -/
theorem hist_frakN_le (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) {n : ℕ} (hN : n < N)
    (hV : ∀ i < n, ValidAt R i) (hVL : ValidAtL R n) (t : Flow2.Hist.Seq (Xs R))
    (a : Lam 2 L N) (hL6 : (6 : ℝ) ≤ (L : ℝ) ^ 2) {i : ℕ} (hi : i < n) {cmu' cz' : ℝ}
    (hcmu : 0 ≤ cmu') (hcz : 0 ≤ cz') (hg : 0 ≤ (t i).1) (hμ : |(t i).2.1| ≤ cmu' * (t i).1)
    (hζ : ‖zetaH R i t‖ ≤ 2 * cz' * (t i).1) (hmsq : |R.msq| * ((L : ℝ) ^ i) ^ 2 ≤ 1) :
    ‖frakN (histCovO R t) (kapH R t) a i‖ ≤
      (R.ℓ ^ 2 * (L : ℝ) ^ 2 * (cmu' + 3 * cz') + R.ℓ ^ 4) * (t i).1 := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set g := (t i).1
  set μ := (t i).2.1
  set st := rawHist R i t
  set C := histCovO R t i
  have hzp := zH_pos R hρ0 hρ t (i + 1)
  set zp := zH R t (i + 1) with hzpdef
  have ezp : zp = ‖stZ' R st‖ := rfl
  obtain ⟨hC, hT, -, hs⟩ := histCovO_props_i R hV hVL t hi.le
  obtain ⟨hc₀, hδ, hδ'⟩ := covH_consts R hV hVL t hi.le
  have hiN : i + 1 < N := by have := (hV i hi).1; omega
  have hA := zero_mode_le hiN hC
  have hD := (cov_c0_delta_le hC hc₀ hδ hδ').2
  rw [ellI_sq] at hA hD
  rw [← hzpdef] at hA hD
  have hrow : ∑ x, C a x = ∑ x, C x 0 := sum_row_eq_zero_mode hT hs a
  set A := ‖∑ x, C x 0‖
  set D := ‖dH R t i‖
  set Lp := (L : ℝ) ^ (i + 1)
  have hLp : Lp = (L : ℝ) ^ i * L := pow_succ _ _
  have hLi : 0 < (L : ℝ) ^ i := by positivity
  set ℓ2 := R.ℓ ^ 2 / (16 * zp) with hℓ2
  have hℓ20 : 0 ≤ ℓ2 := by positivity
  -- the pieces
  have hGr : ‖stGr R i st g μ‖ ≤ 8 / 7 * g := norm_gr_le hg _ (norm_nCor_le _ _)
  have hNu : ‖stNu R i st μ‖ = |μ| * zp / ((L : ℝ) ^ i) ^ 2 := by
    unfold stNu
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_natCast,
      ← ezp, show (L : ℝ) ^ (2 * i) = ((L : ℝ) ^ i) ^ 2 by ring]
  have hZr : zH R t i ≤ 8 / 7 * zp := by
    have := zH_ratio_down R hρ0 hρ t (show i ≤ i + 1 by omega)
    rwa [show i + 1 - i = 1 by omega, pow_one] at this
  have hA' : ‖stA R st * (R.msq : ℂ)‖ ≤ 8 / 7 * zp * ‖zetaH R i t‖ * |R.msq| := by
    unfold stA
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e : stZeta R st = zetaH R i t := rfl
    rw [e]
    have := norm_nonneg (zetaH R i t)
    have := abs_nonneg R.msq
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZr (norm_nonneg _))
      (abs_nonneg _)
  have hnu : ‖(kapH R t i).nu‖ ≤ |μ| * zp / ((L : ℝ) ^ i) ^ 2 +
      8 / 7 * zp * ‖zetaH R i t‖ * |R.msq| + 4 * (8 / 7 * g) * zp ^ 2 * D := by
    rw [kapH_nu]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add hNu.le hA')) ?_)
    have e : ‖(2 : ℂ) * ((2 : ℕ) : ℂ) * (stGr R i st g μ * stZ' R st ^ 2) * dH R t i‖ =
        4 * (‖stGr R i st g μ‖ * zp ^ 2) * D := by
      simp only [norm_mul, norm_pow, ← ezp]; norm_num; exact Or.inl rfl
    rw [e]
    have := norm_nonneg (dH R t i)
    have : ‖stGr R i st g μ‖ * zp ^ 2 ≤ 8 / 7 * g * zp ^ 2 :=
      mul_le_mul_of_nonneg_right hGr (sq_nonneg _)
    nlinarith
  -- the tadpole of the past scales
  have htau : ‖(kapH R t i).g * tauC (wCum (histCovO R t) i) C a‖ ≤ 8 / 7 * g *
      (9 * R.ℓ ^ 4 / 128 * (1 / 2)) := by
    rw [kapH_g, norm_mul, norm_mul, norm_pow, ← ezp, wCum, tauC_sum_left]
    have hq0 : 0 ≤ 2 * ((L : ℝ) ^ 2)⁻¹ := by positivity
    have hq1 : 2 * ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 3 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
    have hsum : ‖∑ k ∈ range i, tauC (histCovO R t k) C a‖ * zp ^ 2 ≤
        9 * R.ℓ ^ 4 / 128 * (1 / 2) := by
      refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (sq_nonneg _)).trans ?_
      rw [sum_mul]
      refine (sum_le_sum fun k hk => hist_tau_w R hρ0 hρ hN hV hVL t a
        (mem_range.1 hk).le le_rfl hi.le (mem_range.1 hk)).trans ?_
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (geom_tail_le hq0 hq1 i) (by positivity)
    have := norm_nonneg (stGr R i st g μ)
    have := norm_nonneg (∑ k ∈ range i, tauC (histCovO R t k) C a)
    calc ‖stGr R i st g μ‖ * zp ^ 2 * ‖∑ k ∈ range i, tauC (histCovO R t k) C a‖
        = ‖stGr R i st g μ‖ * (‖∑ k ∈ range i, tauC (histCovO R t k) C a‖ * zp ^ 2) := by ring
      _ ≤ 8 / 7 * g * (9 * R.ℓ ^ 4 / 128 * (1 / 2)) := mul_le_mul hGr hsum (by positivity)
          (by positivity)
  -- assemble
  rw [frakN, hrow]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hA0 : 0 ≤ A := norm_nonneg _
  have hD0 : 0 ≤ D := norm_nonneg _
  have h1 := mul_le_mul hnu hA (norm_nonneg _) (by positivity)
  -- the three terms of `ν'_i ∑C`
  have t1 : |μ| * zp / ((L : ℝ) ^ i) ^ 2 * (9 * Lp ^ 2 * ℓ2) = 9 / 16 * |μ| * (L : ℝ) ^ 2 * R.ℓ ^ 2 := by
    rw [hLp, hℓ2]; field_simp
  have t2 : 8 / 7 * zp * ‖zetaH R i t‖ * |R.msq| * (9 * Lp ^ 2 * ℓ2) =
      9 / 14 * ‖zetaH R i t‖ * (|R.msq| * ((L : ℝ) ^ i) ^ 2) * (L : ℝ) ^ 2 * R.ℓ ^ 2 := by
    rw [hLp, hℓ2]; field_simp; ring
  have t3 : 4 * (8 / 7 * g) * zp ^ 2 * D * (9 * Lp ^ 2 * ℓ2) ≤ 9 / 112 * R.ℓ ^ 4 * g := by
    have hDl : D * (9 * Lp ^ 2) ≤ 9 / 2 * ℓ2 := by
      have hLp0 : 0 < Lp := by positivity
      calc D * (9 * Lp ^ 2) ≤ ℓ2 / (2 * Lp ^ 2) * (9 * Lp ^ 2) :=
            mul_le_mul_of_nonneg_right hD (by positivity)
        _ = 9 / 2 * ℓ2 := by field_simp
    calc 4 * (8 / 7 * g) * zp ^ 2 * D * (9 * Lp ^ 2 * ℓ2)
        = 4 * (8 / 7 * g) * zp ^ 2 * ℓ2 * (D * (9 * Lp ^ 2)) := by ring
      _ ≤ 4 * (8 / 7 * g) * zp ^ 2 * ℓ2 * (9 / 2 * ℓ2) :=
          mul_le_mul_of_nonneg_left hDl (by positivity)
      _ = 9 / 112 * R.ℓ ^ 4 * g := by rw [hℓ2]; field_simp; ring
  have hμ' : 9 / 16 * |μ| * (L : ℝ) ^ 2 * R.ℓ ^ 2 ≤ 9 / 16 * (cmu' * g) * (L : ℝ) ^ 2 * R.ℓ ^ 2 := by
    gcongr
  have hζ' : 9 / 14 * ‖zetaH R i t‖ * (|R.msq| * ((L : ℝ) ^ i) ^ 2) * (L : ℝ) ^ 2 * R.ℓ ^ 2 ≤
      9 / 14 * (2 * cz' * g) * 1 * (L : ℝ) ^ 2 * R.ℓ ^ 2 := by
    gcongr
  have hfin : 9 / 16 * (cmu' * g) * (L : ℝ) ^ 2 * R.ℓ ^ 2 +
      9 / 14 * (2 * cz' * g) * 1 * (L : ℝ) ^ 2 * R.ℓ ^ 2 + 9 / 112 * R.ℓ ^ 4 * g +
      8 / 7 * g * (9 * R.ℓ ^ 4 / 128 * (1 / 2)) ≤
      (R.ℓ ^ 2 * (L : ℝ) ^ 2 * (cmu' + 3 * cz') + R.ℓ ^ 4) * g := by
    have e : (R.ℓ ^ 2 * (L : ℝ) ^ 2 * (cmu' + 3 * cz') + R.ℓ ^ 4) * g -
        (9 / 16 * (cmu' * g) * (L : ℝ) ^ 2 * R.ℓ ^ 2 +
          9 / 14 * (2 * cz' * g) * 1 * (L : ℝ) ^ 2 * R.ℓ ^ 2 + 9 / 112 * R.ℓ ^ 4 * g +
          8 / 7 * g * (9 * R.ℓ ^ 4 / 128 * (1 / 2))) =
        R.ℓ ^ 2 * (L : ℝ) ^ 2 * g * (7 / 16 * cmu' + 12 / 7 * cz') + R.ℓ ^ 4 * g * (197 / 224) := by
      ring
    have : 0 ≤ R.ℓ ^ 2 * (L : ℝ) ^ 2 * g * (7 / 16 * cmu' + 12 / 7 * cz') + R.ℓ ^ 4 * g * (197 / 224) := by
      positivity
    linarith
  have e1 : (|μ| * zp / ((L : ℝ) ^ i) ^ 2 + 8 / 7 * zp * ‖zetaH R i t‖ * |R.msq| +
      4 * (8 / 7 * g) * zp ^ 2 * D) * (9 * Lp ^ 2 * ℓ2) =
      |μ| * zp / ((L : ℝ) ^ i) ^ 2 * (9 * Lp ^ 2 * ℓ2) +
      8 / 7 * zp * ‖zetaH R i t‖ * |R.msq| * (9 * Lp ^ 2 * ℓ2) +
      4 * (8 / 7 * g) * zp ^ 2 * D * (9 * Lp ^ 2 * ℓ2) := by ring
  rw [e1, t1, t2] at h1
  linarith only [h1, t3, hμ', hζ', hfin, htau]

/-- **The rescaled increment of the quartic coupling**:
`|g'_{i+1} − g'_i|/|Z_{i+1}|² ≤ (3β + 16c_μℓ² + 20c_z) ǧ_i²`. -/
theorem hist_dg_w (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) (i : ℕ)
    {cmu' cz' β : ℝ} (hcmu : 0 ≤ cmu') (hcz : 0 ≤ cz') (hβ : 0 ≤ β)
    (hg : 0 ≤ (t i).1) (hg1 : 0 ≤ (t (i + 1)).1) (hgg : (t (i + 1)).1 ≤ 2 * (t i).1)
    (hΔ : |(t (i + 1)).1 - (t i).1| ≤ 7 / 4 * β * (t i).1 ^ 2)
    (hμ : |(t i).2.1| ≤ cmu' * (t i).1) (hμ1 : |(t (i + 1)).2.1| ≤ cmu' * (t (i + 1)).1)
    (hζ1 : ‖zetaH R (i + 1) t‖ ≤ 2 * cz' * (t (i + 1)).1)
    (hZw : ‖stZ' R (rawHist R i t) * (rawHist R i t).w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ i) ^ 2)
    (hZw1 : ‖stZ' R (rawHist R (i + 1) t) * (rawHist R (i + 1) t).w1‖ ≤
      R.ℓ ^ 2 * ((L : ℝ) ^ (i + 1)) ^ 2) :
    ‖(kapH R t (i + 1)).g - (kapH R t i).g‖ / zH R t (i + 1) ^ 2 ≤
      (3 * β + 16 * cmu' * R.ℓ ^ 2 + 20 * cz') * (t i).1 ^ 2 := by
  set g := (t i).1
  set g' := (t (i + 1)).1
  set st := rawHist R i t
  set st' := rawHist R (i + 1) t
  set n := nCor (stNu R i st (t i).2.1) st.w1
  set n' := nCor (stNu R (i + 1) st' (t (i + 1)).2.1) st'.w1
  set ζ := zetaH R (i + 1) t
  have hz := zH_pos R hρ0 hρ t (i + 1)
  have ezp : zH R t (i + 1) = ‖stZ' R st‖ := rfl
  have eZ : stZ' R st' = stZ' R st * (1 + ζ) := rfl
  have e : (kapH R t (i + 1)).g - (kapH R t i).g =
      stZ' R st ^ 2 * ((g' : ℂ) / (1 + n') * (1 + ζ) ^ 2 - (g : ℂ) / (1 + n)) := by
    rw [kapH_g, kapH_g, eZ]
    show (g' : ℂ) / (1 + n') * (stZ' R st * (1 + ζ)) ^ 2 - (g : ℂ) / (1 + n) * stZ' R st ^ 2 = _
    ring
  have hz0 : ‖stZ' R st‖ ≠ 0 := by rw [← ezp]; exact hz.ne'
  rw [e, norm_mul, norm_pow, show ∀ x : ℝ, ‖stZ' R st‖ ^ 2 * x / zH R t (i + 1) ^ 2 = x from
    fun x => by rw [ezp]; field_simp]
  have hn : ‖n‖ ≤ 4 * |(t i).2.1| * R.ℓ ^ 2 := norm_nCor_hist_le R st i _ hZw
  have hn' : ‖n'‖ ≤ 4 * |(t (i + 1)).2.1| * R.ℓ ^ 2 := norm_nCor_hist_le R st' (i + 1) _ hZw1
  have hζ8 : ‖ζ‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
  refine (norm_gr_diff_le hg hg1 (norm_nCor_le _ _) (norm_nCor_le _ _) hζ8).trans ?_
  have hℓ2 : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  have hn2 : ‖n‖ + ‖n'‖ ≤ 12 * cmu' * R.ℓ ^ 2 * g := by
    have a1 : 4 * |(t i).2.1| * R.ℓ ^ 2 ≤ 4 * (cmu' * g) * R.ℓ ^ 2 := by gcongr
    have a2 : 4 * |(t (i + 1)).2.1| * R.ℓ ^ 2 ≤ 4 * (cmu' * (2 * g)) * R.ℓ ^ 2 := by
      gcongr; exact hμ1.trans (mul_le_mul_of_nonneg_left hgg hcmu)
    linarith
  have b1 : 64 / 49 * (9 / 8 * |g' - g| + g * (‖n‖ + ‖n'‖)) ≤
      64 / 49 * (9 / 8 * (7 / 4 * β * g ^ 2) + g * (12 * cmu' * R.ℓ ^ 2 * g)) := by
    gcongr
  have b2 : 8 / 7 * g' * (17 / 8 * ‖ζ‖) ≤ 8 / 7 * (2 * g) * (17 / 8 * (2 * cz' * (2 * g))) := by
    have : ‖ζ‖ ≤ 2 * cz' * (2 * g) := hζ1.trans (mul_le_mul_of_nonneg_left hgg (by positivity))
    gcongr
  have b3 : 64 / 49 * (9 / 8 * (7 / 4 * β * g ^ 2) + g * (12 * cmu' * R.ℓ ^ 2 * g)) +
      8 / 7 * (2 * g) * (17 / 8 * (2 * cz' * (2 * g))) ≤
      (3 * β + 16 * cmu' * R.ℓ ^ 2 + 20 * cz') * g ^ 2 := by
    have e : (3 * β + 16 * cmu' * R.ℓ ^ 2 + 20 * cz') * g ^ 2 -
        (64 / 49 * (9 / 8 * (7 / 4 * β * g ^ 2) + g * (12 * cmu' * R.ℓ ^ 2 * g)) +
          8 / 7 * (2 * g) * (17 / 8 * (2 * cz' * (2 * g)))) =
        g ^ 2 * (3 / 7 * β + 16 / 49 * (cmu' * R.ℓ ^ 2) + 4 / 7 * cz') := by ring
    have : 0 ≤ g ^ 2 * (3 / 7 * β + 16 / 49 * (cmu' * R.ℓ ^ 2) + 4 / 7 * cz') := by positivity
    linarith
  linarith only [b1, b2, b3]

end Bulk

end Hist

/-! ### The initial state -/

/-- **Point initial state**: if the shares at scale `k` are `c_k(B) = β₀ 1_{a∈B}`, then
`β_k = β₀` and `D_k = 0` (e.g. `V_0(B)_a = β₀1_{a∈B}ψ̄_a`). -/
theorem betaTot_shareDev_point {d : ℕ} (a : Lam d L N) (k : ℕ) (V : OFam .one d L N) (β₀ : ℂ)
    (h : ∀ b ∈ blockIdx (L := L) (N := N) k, mass1 (-1) (V b : SA .one (Lam d L N)).a =
      if a ∈ blockSet (L := L) (N := N) k b then β₀ else 0) :
    betaTot (L := L) (N := N) k V = β₀ ∧ shareDev a k V = 0 := by
  classical
  have hs : betaTot (L := L) (N := N) k V = β₀ := by
    rw [betaTot, sum_congr rfl h]
    simp only [mem_blockSet]
    rw [sum_ite_eq]
    exact if_pos (mem_blocks.2 ⟨a, mem_univ _, rfl⟩)
  refine ⟨hs, ?_⟩
  unfold shareDev
  refine sum_eq_zero fun b hb => ?_
  rw [h b hb, hs, sub_self, norm_zero]

section Main

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The relative coupled observable recursion along the history, uniform constants**
(Case (1), `σ_a`; weights `w_i = |Z_{i+1}|²`). -/
theorem obs_hist_rel_w {C₀ η ε₀ C₁k : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁k) (hC₁k : 0 ≤ C₁k)
    {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀)
    (hs0 : ObsSymInv 0 o₀) (hf0 : ∀ b, (o₀.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a))
    (hW0a : ∀ b, (o₀.W b : SA .one (Lam 2 L N)).a = 0)
    (t : Flow2.Hist.Seq (Xs R)) (hW0 : ∀ b, oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) = 0)
    (hK0 : ∀ X, oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) = 0)
    (n : ℕ) (hn : n ≤ Nh) (hNh : 0 < Nh) (hnN : n < N) (hVL : ValidAtL R n)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁k * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + 64 * kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hLw : Kw / L ≤ 1 / 12) (hC₁ε : C₁ * (cR R Λ cm C₂ * ε) ≤ 1 / 12)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁)
    (hβp : 0 < β) (hδ2 : δ ≤ 1 / 2) (hcgε : cg * ε ≤ β / 4) (hβε : β * ε ≤ 1 / 2) :
    let B := kB (kθ0 L R.A C₀ η) C₁k (8 * cx κ cT)
    let rr := fun j => cR R Λ cm C₂ * (t j).1
    let cWo := 3 * C₁ + 1
    let bt := fun j => ‖betaTot (L := L) (N := N) j (histVO R P o₀ t j)‖
    let κ' := kapH R t
    let Bτ := 9 * R.ℓ ^ 4 / 128
    ∃ r' : ℕ → ℂ,
      MuChain P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t) (histKO R P o₀ t) κ' r' n ∧
      ∀ {cgb cP cδ qq : ℝ}, 0 ≤ cgb → 0 ≤ cP → 0 ≤ cδ →
        2 * ((L : ℝ) ^ 2)⁻¹ ≤ qq → qq ≤ 1 / 4 →
        8 / 7 ≤ cgb * cR R Λ cm C₂ →
        R.ℓ ^ 2 * (L : ℝ) ^ 2 * (cmu Λ cm + 3 * cZ R) + R.ℓ ^ 4 ≤ cgb * cR R Λ cm C₂ →
        3 * β + 16 * cmu Λ cm * R.ℓ ^ 2 + 20 * cZ R ≤ cgb * cR R Λ cm C₂ ^ 2 →
        cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 7 →
        16 * (8 * (csN 2 : ℝ)) * cWo * B + 3 * cP * cWo + 4 * Bτ * cgb * (1 + cgb) +
          4 * Bτ * cgb * cδ * (cR R Λ cm C₂ * ε) ≤ 6 / 7 * cδ →
        cδ * (cR R Λ cm C₂ ^ 2 * (ε / (β / 4))) ≤ 1 / 8 →
        ProdBd R P o₀ t n rr cP qq →
        shareDev P.a 0 (histVO R P o₀ t 0) = 0 → 0 < bt 0 →
        cδ * ∑ k ∈ range n, rr k ^ 2 ≤ 1 / 8 ∧ ∀ j ≤ n, 0 < bt j ∧
          shareDev P.a j (histVO R P o₀ t j) ≤ 6 * (cδ * ∑ k ∈ range j, rr k ^ 2) * bt j ∧
          WbH R P o₀ t j (cWo * rr j * (2 * histS R j t * bt j)) ∧
          KbH R P o₀ t j (16 * cWo * B * rr j ^ 2 * (histS R j t * bt j)) ∧
          (j < n → ‖betaTot (L := L) (N := N) (j + 1) (histVO R P o₀ t (j + 1)) -
              betaTot (L := L) (N := N) j (histVO R P o₀ t j) *
                (1 - frakN (histCovO R t) κ' P.a j)‖ ≤
            cδ * rr j ^ 2 * ‖betaTot (L := L) (N := N) j (histVO R P o₀ t j) *
              (1 - frakN (histCovO R t) κ' P.a j)‖) ∧
          ‖betaTot (L := L) (N := N) j (histVO R P o₀ t j) -
              betaTot (L := L) (N := N) 0 (histVO R P o₀ t 0) *
                ∏ k ∈ range j, (1 - frakN (histCovO R t) κ' P.a k)‖ ≤
            (Real.exp (cδ * ∑ k ∈ range j, rr k ^ 2) - 1) *
              ‖betaTot (L := L) (N := N) 0 (histVO R P o₀ t 0) *
                ∏ k ∈ range j, (1 - frakN (histCovO R t) κ' P.a k)‖ := by
  intro B rr cWo bt κ' Bτ
  have hVn : ∀ i < n, ValidAt R i := fun i hi => hV i (by omega)
  obtain ⟨r', HC⟩ := muChain_obsHist_kap R P o₀ t hnN hVn hVL h0 hW0a hf0
  refine ⟨r', HC, ?_⟩
  intro cgb cP cδ qq hcg hcP hcδ0 hqq hqq4 hcg1 hcg2 hcg3 hcgε' hcδ hsumε hPr hD0 hb0
  have hβ' : 0 < β / 4 := by linarith
  -- the band along the history
  have hcg0 : 0 ≤ cg := H.hcg
  have hband : ∀ k < n, (t k).1 + β / 4 * (t k).1 ^ 2 ≤ (t (k + 1)).1 ∧
      |(t (k + 1)).1 - (t k).1| ≤ 7 / 4 * β * (t k).1 ^ 2 ∧ (t (k + 1)).1 ≤ 2 * (t k).1 := by
    intro k hk
    have hr := ht.2 k hk
    obtain ⟨hg, hgε, -, -⟩ := ht.1 k hk.le
    have h3 : cg * (t k).1 ^ 3 ≤ β / 4 * (t k).1 ^ 2 := by
      have : cg * (t k).1 ≤ cg * ε := mul_le_mul_of_nonneg_left hgε hcg0
      have e : cg * (t k).1 ^ 3 = (cg * (t k).1) * (t k).1 ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right (this.trans hcgε) (sq_nonneg _)
    have hδβ : δ * β * (t k).1 ^ 2 ≤ 1 / 2 * β * (t k).1 ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ2 hβ) (sq_nonneg _)
    rw [abs_le] at hr
    have hg2 : 0 ≤ β * (t k).1 ^ 2 := by positivity
    refine ⟨by linarith [hr.1], ?_, ?_⟩
    · rw [abs_le]; constructor <;> nlinarith [hr.1, hr.2]
    · have h4 : 7 / 4 * β * (t k).1 ^ 2 ≤ 7 / 8 * (t k).1 := by
        have : β * (t k).1 ≤ β * ε := mul_le_mul_of_nonneg_left hgε hβ
        have e : 7 / 4 * β * (t k).1 ^ 2 = 7 / 4 * (β * (t k).1) * (t k).1 := by ring
        rw [e]; nlinarith
      nlinarith [hr.2]
  have hinc : ∀ k < n, (t k).1 + β / 4 * (t k).1 ^ 2 ≤ (t (k + 1)).1 := fun k hk => (hband k hk).1
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  have hwa : Obs2.wA.a ≠ ⊤ := by simp [Obs2.wA]
  have hwb : Obs2.wA.b ≠ ⊤ := by simp [Obs2.wA]
  have hcx := H.hcx
  have hcb : 0 ≤ 8 * cx κ cT := by positivity
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 hcb
    have h2 := mul_nonneg hC₁k (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L R.A C₀ η * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hC1 : 0 ≤ C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) := by positivity
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hr0 : ∀ j ≤ n, 0 ≤ rr j := fun j hj => mul_nonneg hcR (ht.1 j hj).1.le
  have hrε : ∀ j ≤ n, rr j ≤ cR R Λ cm C₂ * ε := fun j hj =>
    mul_le_mul_of_nonneg_left (ht.1 j hj).2.1 hcR
  have hform : ∀ k b, ((obsHist R P o₀ k t).V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a) :=
    fun k b => by rw [← histVO_a]; exact obsHist_hform R P o₀ t hf0 k b
  -- positivity of the field scales
  have hsj : ∀ j ≤ n, 0 < histS R j t := by
    intro j hj
    rcases Nat.lt_or_ge j Nh with h | h
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩ :=
        hist_raw R hSB hV hm hβ hδ1 H t j h (hDh j hj)
      exact hs
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs'⟩ :=
        hist_raw R hSB hV hm hβ hδ1 H t i (by omega) (hDh i (by omega))
      exact hs'
  have hL2 : (2 : ℝ) ≤ L := by
    have := hVL.1; norm_num at this; exact_mod_cast (by omega : 2 ≤ L)
  -- the block bound of `V^{obs}_j` from the `ℓ¹` size
  have hVo : ∀ j ≤ n, ∀ m, histS R j t * MuChain.shA (histVO R P o₀ t) j ≤ m →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m := by
    intro j hj m hsm b hb'
    have hs := hsj j hj
    rw [Obs2.oTo_wA, eq_mass1_smul_of_span (hform j b), Tj_smul_psibar j hs]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hsm)
    have h1 : ‖mass1 (-1) ((obsHist R P o₀ j t).V b : SA .one (Lam 2 L N)).a‖ ≤
        MuChain.shA (histVO R P o₀ t) j := by
      rw [← histVO_a_mass R P o₀ t j b]
      exact single_le_sum (f := fun b => ‖mass1 (-1)
        (histVO R P o₀ t j b : SA .one (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h1 hs.le
  have hgm : ∀ k < n, (t k).1 ≤ (t (k + 1)).1 := fun k hk => by
    have := hinc k hk; have : 0 ≤ β / 4 * (t k).1 ^ 2 := by positivity
    linarith
  -- the weights and the rescaled bulk bounds
  let w : ℕ → ℝ := fun i => zH R t (i + 1) ^ 2
  let Tt : ℕ → ℕ → ℝ := fun k j => Bτ * qq ^ (j - k)
  have hw : ∀ i < n, 0 < w i := fun i _ => pow_pos (zH_pos R hρ0 hρ t (i + 1)) 2
  have hL6 : (6 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have h49 : (3 : ℝ) ≤ L := by
      have := hVL.1; norm_num at this; exact_mod_cast (by omega : 3 ≤ L)
    nlinarith
  have hTt : ∀ k j, k < j → j < n → ∀ i ∈ Ico k j,
      ‖tauC (histCovO R t k) (histCovO R t j) P.a‖ * w i ≤ Tt k j := by
    intro k j hkj hj i hi
    have hi' := mem_Ico.1 hi
    refine (hist_tau_w R hρ0 hρ hnN hVn hVL t P.a hi'.1 hi'.2.le hj.le hkj).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hqq _) (by positivity)
  have hcZ : 0 ≤ cZ R := by unfold cZ; positivity
  have hcmu := H.hcmu
  have hGb : ∀ i < n, ‖(κ' i).g‖ / w i ≤ cgb * rr i := by
    intro i hi
    refine (hist_G_w R hρ0 hρ t i (ht.1 i hi.le).1.le).trans ?_
    have := (ht.1 i hi.le).1.le
    show 8 / 7 * (t i).1 ≤ cgb * (cR R Λ cm C₂ * (t i).1)
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcg1 this
  have hnnb : ∀ i < n, ‖frakN (histCovO R t) κ' P.a i‖ ≤ cgb * rr i := by
    intro i hi
    obtain ⟨hg, -, hμ, -⟩ := ht.1 i hi.le
    have h := hist_frakN_le R hρ0 hρ hnN hVn hVL t P.a hL6 hi hcmu hcZ hg.le hμ
      (norm_zetaH_le R hSB hV hm hβ hδ1 H hρ0 t (by omega) (hDh i hi.le)) (hm i (by omega))
    refine h.trans ?_
    show _ ≤ cgb * (cR R Λ cm C₂ * (t i).1)
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcg2 hg.le
  have hdgb : ∀ i < n, ‖(κ' (i + 1)).g - (κ' i).g‖ / w i ≤ cgb * rr i ^ 2 := by
    intro i hi
    obtain ⟨hg, -, hμ, -⟩ := ht.1 i hi.le
    obtain ⟨hg1, -, hμ1, -⟩ := ht.1 (i + 1) hi
    obtain ⟨-, hΔ, hgg⟩ := hband i hi
    have h := hist_dg_w R hρ0 hρ t i hcmu hcZ hβ hg.le hg1.le hgg hΔ hμ hμ1
      (norm_zetaH_le R hSB hV hm hβ hδ1 H hρ0 t (by omega) (hDh (i + 1) hi))
      (norm_Zw1_le R hρ0 i (fun i' hi' => hV i' (by omega)) t)
      (norm_Zw1_succ_le R hρ0 i (fun i' hi' => hV i' (by omega)) t)
    refine h.trans ?_
    show _ ≤ cgb * (cR R Λ cm C₂ * (t i).1) ^ 2
    rw [mul_pow, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hcg3 (sq_nonneg _)
  have I : RelIn n bt (MuChain.shA (histVO R P o₀ t))
      (fun j => shareDev P.a j (histVO R P o₀ t j))
      (fun j => shareErrL1 P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t)
        (histKO R P o₀ t) κ' j)
      (fun j => ‖1 - frakN (histCovO R t) κ' P.a j‖) (fun j => histS R j t) rr
      (MuChain.shKt (histKO R P o₀ t))
      (MuChain.shPr P (histCovO R t) (histVO R P o₀ t) (histWO R P o₀ t))
      (fun i => ‖(κ' (i + 1)).g - (κ' i).g‖ / w i) (fun i => ‖(κ' i).g‖ / w i)
      (fun i => ‖frakN (histCovO R t) κ' P.a i‖)
      (fun j => Kw / L + C₁ * rr j)
      (fun j => kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * rr j)
      Tt (WbH R P o₀ t) (KbH R P o₀ t)
      C₁ cWo B (8 * (csN 2 : ℝ)) cP cgb Bτ qq (cR R Λ cm C₂ * ε) cδ := {
    hC₁ := hC₁
    hcW1 := by show (1 : ℝ) ≤ 3 * C₁ + 1; linarith
    hcWC := by show 3 * C₁ ≤ 3 * C₁ + 1; linarith
    hBk := hB
    hcK := by positivity
    hcP := hcP
    hcg := hcg
    hBτ := by positivity
    hq0 := le_trans (by positivity) hqq
    hq := hqq4
    hcδ0 := hcδ0
    hcδ := hcδ
    hsum := by
      have h1 := Step2.sum_sq_le hβ' n hinc
      have h2 : ∑ k ∈ range n, rr k ^ 2 = cR R Λ cm C₂ ^ 2 * ∑ k ∈ range n, (t k).1 ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      have h3 : ((t n).1 - (t 0).1) / (β / 4) ≤ ε / (β / 4) := by
        have := (ht.1 n le_rfl).2.1; have := (ht.1 0 (Nat.zero_le _)).1
        exact div_le_div_of_nonneg_right (by linarith) hβ'.le
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg (cR R Λ cm C₂))
      have h5 := mul_le_mul_of_nonneg_left h4 hcδ0
      linarith
    hr0 := hr0
    hrb := hrε
    hrm := fun j hj => mul_le_mul_of_nonneg_left (hgm j hj) hcR
    hs := hsj
    hss := by
      intro j hj
      have e : histS R (j + 1) t = histS R j t * fscale (1 + zetaH R j t) := by
        unfold histS
        rw [rawHist_succ_Z, fscale_mul]; ring
      have hz : ‖zetaH R j t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
      have h1 := fscale_one_add_ge hz
      have h2 := hsj j hj.le
      rw [e]
      nlinarith
    ha := by
      intro j hj
      have h1 := (hnnb j hj).trans ((mul_le_mul_of_nonneg_left (hrε j hj.le) hcg).trans
        (by linarith [hcgε'] : cgb * (cR R Λ cm C₂ * ε) ≤ 1 / 7))
      have h2 := norm_sub_norm_le (1 : ℂ) (frakN (histCovO R t) κ' P.a j)
      have h3 := norm_sub_le (1 : ℂ) (frakN (histCovO R t) κ' P.a j)
      rw [norm_one] at h2 h3
      constructor <;> linarith
    hb0 := hb0
    hD0 := hD0
    hWm := fun j x y hx hxy b hb' => (hx b hb').trans (ENNReal.ofReal_le_ofReal hxy)
    hKm := fun j x y hx hxy X hX => (hx X hX).trans (ENNReal.ofReal_le_ofReal hxy)
    hW0 := fun b _ => by
      show oTo Obs2.wA 0 (histS R 0 t) (o₀.W b) ≤ _
      rw [hW0 b]; exact zero_le
    hK0 := fun X _ => by
      show _ * oTo Obs2.wA 0 (histS R 0 t) (o₀.K X) ≤ _
      rw [hK0 X, mul_zero]; exact zero_le
    hθW := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC₁
      show Kw / L + C₁ * rr j ≤ 1 / 6
      linarith
    hθK := fun j hj => by
      have := mul_le_mul_of_nonneg_left (hrε j hj.le) hC1
      show kθ0 L R.A C₀ η + C₁k * (2 + 2 * (8 * cx κ cT) + 64 * B) * rr j ≤ 1 / 16
      linarith
    hW := fun j hj m w hm0 hw0' hsA hWj =>
      wobs_hist_step R hWB hSB hV hm hβ hδ1 H P Obs2.wA hw0 o₀ h0 hl0 hs0 t j (by omega)
        (hDh j hj.le) hε₁ m w hm0 hw0' (hVo j hj.le m hsA) hWj
    hK := fun j hj m k hm0 hk0 hsA hWj hKj hk8 =>
      kobs_hist_step R hKB hSB hV hm hβ hδ1 H P Obs2.wA hw0 hwa hwb o₀ h0 hl0 hs0 t j (by omega)
        (hDh j hj.le) (64 * B) m k (by positivity) hm0 hk0 hε1 hεε hεk hk8
        (hVo j hj.le m hsA) hWj hKj
    hKt := fun j hj k hk0 hKj => by
      have h := kobs_EK1 R hSB hV hm hβ hδ1 H P o₀ hl0 t j (by omega) (hDh j hj.le) Obs2.wA hw0
        1 one_pos (by simp [Obs2.wA]) k hk0 hKj
      refine h.trans (le_of_eq ?_)
      rw [div_one]; ring
    hPr := hPr
    hT := fun k j _ _ => ⟨by
      show 0 ≤ Bτ * qq ^ (j - k)
      exact mul_nonneg (by positivity) (pow_nonneg (le_trans (by positivity) hqq) _), le_rfl⟩
    hdg := fun i hi => ⟨div_nonneg (norm_nonneg _) (hw i hi).le, hdgb i hi⟩
    hG := fun i hi => ⟨div_nonneg (norm_nonneg _) (hw i hi).le, hGb i hi⟩
    hnn := fun i hi => ⟨norm_nonneg _, hnnb i hi⟩ }
  exact ⟨I.hsum, HC.rel_flow_w w Tt hw hTt I⟩

end Main

end

end PtCorr2
