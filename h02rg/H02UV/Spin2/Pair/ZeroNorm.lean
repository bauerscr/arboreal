import Spin2.Pair.PairPR6

/-!
# The pair zero mode without the bulk normaliser `s`

Pair observable `z̃_0z̃_x`, `j = j_x`, `M = M_j`, `ǧ = ǧ_j`, `F = F_N` (`zFin`), `F' = F'_N`
(`zFinR`), `c = t_raw/|Λ|` (`zCc`), `s = εF_∅ - c·c2F_∅ = sE Ω` (the bulk normaliser, `= 1 + ũ_{N,N}`
for the bulk final object, `PtCorr2.one_add_uFin_ward`).

**The `|s|` problem.** `PairZeroRelR`/`PairZeroRemR` bound the constants `εF'_{ab}`, `εF_a` relative
to `|s|`; only `s ≠ 0` is known, and a lower bound on `|s|/|P₀|` is equivalent to an upper bound on
the zero-mode ratio `|t_raw ã/(1 + ũ)|` (`PtCorr2.norm_one_add_uFin_ge`), not available.

**The way out: normalise by the one-point zero mode.** The Ω-part of `E` is
`(x - ρ̃x_a)/s + ρ̃·n_aΩ` (`PtCorr2.zm_red_elim`), and `n_aΩ = D/s` with
`D = εF_a - c·c2F_a = sA Ω`. So if `‖x - ρ̃x_a‖ ≤ K₂‖M‖ǧ‖D‖`, the Ω-part is
`≤ (K₂ + K₃)‖M‖ǧ‖n_aΩ‖` (`zm_rel_boundW`), and `n_aΩ = r - γ_{a,N}` is fixed by the one-point
closure (`pair_E_split`): **`s` cancels**. This is `PairZeroRelW` (`pairAboveW1_of_redW`:
`K_E = K₁ + (K₂ + K₃)K₄`, `K_R = (K₂ + K₃)M_b`).

**The remainders relative to the zero-mode vertex `|c||β_{a,N-1}||P₀|`** (`PairZeroRemW e₁ e₂`):
(a) `P₀ ≠ 0`; (b) `‖c2F_a - β_{a,N-1}P₀‖ ≤ ½‖β_{a,N-1}‖‖P₀‖`; (c) `‖c2F'_{ab} - r'_{N-1}P₀‖ ≤
e₁‖M‖ǧ‖β_{a,N-1}‖‖P₀‖` (unchanged); (d) `‖εF'_{ab}‖ ≤ e₂‖M‖ǧ·|c||β_{a,N-1}||P₀|`;
(e) `‖εF_a‖ ≤ ¼|c||β_{a,N-1}||P₀|`. Then `‖D‖ ≥ ¼|c||β||P₀|` and (**`pairZeroRelW_of`**)
`PairZeroRelW (4e₂ + 2(c_r + e₁)) (2(c_r + e₁))`. Heuristically `|c β P₀| ≈ ‖M‖|s|` (`n_aΩ ≈ -M`),
so (d), (e) are the old items `e₂‖M‖²ǧ|s|`, `e₃‖M‖|s|` with `e₃ = ¼`, without `s`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **Zero-mode relative bound without `s`** (pure). From `‖y_a - βP₀‖ ≤ ½‖β‖‖P₀‖`,
`‖y_{ab} - rP₀‖ ≤ e₁Mg‖β‖‖P₀‖`, `‖r‖ ≤ c_rMg‖β‖`, `‖x_{ab}‖ ≤ e₂Mg·Q`, `‖x_a‖ ≤ ¼Q`
(`Q = |c||β||P₀|`): `ρ = y_{ab}/y_a` has `y_{ab} = ρy_a`, `‖ρ‖ ≤ 2(c_r + e₁)Mg` and
`‖x_{ab} - ρx_a‖ ≤ (4e₂ + 2(c_r + e₁))Mg‖x_a - c·y_a‖`. -/
theorem zero_rel_pureW {ya yab xa xab β r P0 cc : ℂ} {cr e1 e2 M g : ℝ} (hβ : β ≠ 0)
    (hP : P0 ≠ 0) (hM : 0 ≤ M) (hg : 0 ≤ g) (hcr : 0 ≤ cr) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (h1 : ‖ya - β * P0‖ ≤ 1 / 2 * ‖β‖ * ‖P0‖) (h2 : ‖yab - r * P0‖ ≤ e1 * M * g * ‖β‖ * ‖P0‖)
    (hr : ‖r‖ ≤ cr * M * g * ‖β‖) (h3 : ‖xab‖ ≤ e2 * M * g * (‖cc‖ * ‖β‖ * ‖P0‖))
    (h4 : ‖xa‖ ≤ 1 / 4 * (‖cc‖ * ‖β‖ * ‖P0‖)) :
    ∃ ρ : ℂ, yab = ρ * ya ∧ ‖ρ‖ ≤ 2 * (cr + e1) * M * g ∧
      ‖xab - ρ * xa‖ ≤ (4 * e2 + 2 * (cr + e1)) * M * g * ‖xa - cc * ya‖ := by
  obtain ⟨ρ, e, hρ, -⟩ := zero_rel_pure (xab := 0) (xa := 0) (s := 0) (e2 := 0) (e3 := 0) hβ hP hM
    hg hcr he1 h1 h2 hr (by simp) (by simp)
  refine ⟨ρ, e, hρ, ?_⟩
  set Q := ‖cc‖ * ‖β‖ * ‖P0‖ with hQ
  have hya : 1 / 2 * (‖β‖ * ‖P0‖) ≤ ‖ya‖ := by
    have e' : β * P0 = ya - (ya - β * P0) := by ring
    have := norm_sub_le ya (ya - β * P0)
    rw [← e', norm_mul] at this
    linarith
  have hcya : 1 / 2 * Q ≤ ‖cc * ya‖ := by
    rw [norm_mul, hQ, mul_assoc ‖cc‖]
    have := mul_le_mul_of_nonneg_left hya (norm_nonneg cc)
    linarith
  have hD : 1 / 4 * Q ≤ ‖xa - cc * ya‖ := by
    have e' : cc * ya = xa - (xa - cc * ya) := by ring
    have := norm_sub_le xa (xa - cc * ya)
    rw [← e'] at this
    linarith
  have hK : 0 ≤ (cr + e1) * M * g := mul_nonneg (mul_nonneg (by linarith) hM) hg
  have hA : 0 ≤ e2 * M * g := mul_nonneg (mul_nonneg he2 hM) hg
  have h5 : ‖ρ * xa‖ ≤ 2 * (cr + e1) * M * g * (1 / 4 * Q) := by
    rw [norm_mul]; exact mul_le_mul hρ h4 (norm_nonneg _) (by nlinarith)
  have h6 : ‖xab - ρ * xa‖ ≤ (e2 * M * g + (cr + e1) * M * g / 2) * Q := by
    have := norm_sub_le xab (ρ * xa)
    have e' : (e2 * M * g + (cr + e1) * M * g / 2) * Q =
        e2 * M * g * Q + 2 * (cr + e1) * M * g * (1 / 4 * Q) := by ring
    rw [e']; linarith
  have h7 : (e2 * M * g + (cr + e1) * M * g / 2) * Q ≤
      (e2 * M * g + (cr + e1) * M * g / 2) * (4 * ‖xa - cc * ya‖) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  refine h6.trans (h7.trans (le_of_eq ?_))
  ring

/-- The Ω-part bound without `s` (pure): `‖X‖ ≤ K‖D‖`, `‖ρ‖ ≤ K₃` give
`‖X/s + ρ·(D/s)‖ ≤ (K + K₃)‖D/s‖`. -/
theorem zm_rel_boundW {X D s ρ : ℂ} {K K3 : ℝ} (hX : ‖X‖ ≤ K * ‖D‖) (hρ : ‖ρ‖ ≤ K3) :
    ‖X / s + ρ * (D / s)‖ ≤ (K + K3) * ‖D / s‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  refine add_le_add ?_ ?_
  · rw [norm_div, norm_div, mul_div_assoc']
    exact div_le_div_of_nonneg_right hX (norm_nonneg _)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right hρ (norm_nonneg _)

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Named input (PR6, reduced final object, without `s`).** As `PairZeroRelR`, but the constant
part is relative to the one-point zero-mode numerator `D = εF_a - c·c2F_a` (`= sA Ω`):
`‖εF'_{ab} - ρ̃εF_a‖ ≤ K₂‖M‖ǧ‖D‖`. -/
def PairZeroRelW (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (K2 K3 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ ρ : ℂ,
      Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab =
        ρ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a ∧
      ‖ρ‖ ≤ K3 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab -
          ρ * ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
        K2 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
            zCc R Nh m b μ₀ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖

/-- **Named input (PR6, the last-step remainders, without `s`).** Items (a)–(c) of
`PairZeroRemR`; the constants relative to the zero-mode vertex `|c||β_{a,N-1}||P₀|`:
`‖ε(F'_N)_{ab}‖ ≤ e₂‖M‖ǧ|c||β||P₀|`, `‖ε(F_N)_a‖ ≤ ¼|c||β||P₀|`. -/
def PairZeroRemW (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (e1 e2 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    zP0 R Nh m b μ₀ x ≠ 0 ∧
    ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) * zP0 R Nh m b μ₀ x‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ ∧
    ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab -
        rRN R Nh m b μ₀ oR x * zP0 R Nh m b μ₀ x‖ ≤
      e1 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ ∧
    ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      e2 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        (‖zCc R Nh m b μ₀‖ * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ *
          ‖zP0 R Nh m b μ₀ x‖) ∧
    ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      1 / 4 * (‖zCc R Nh m b μ₀‖ * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ *
        ‖zP0 R Nh m b μ₀ x‖)

/-- **`PairZeroRelW` from `PairRRelR` and the last-step remainders** (trajectory level). -/
theorem pairZeroRelW_of {Nh : ℕ} (m b μ₀ : ℝ) (lam : ℕ → ℂ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cr e1 e2 : ℝ} (hcr : 0 ≤ cr) (he1 : 0 ≤ e1)
    (he2 : 0 ≤ e2)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hβ : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) ≠ 0)
    (hR : PairRRelR R Nh m b μ₀ lam oR cr) (hZ : PairZeroRemW R Nh m b μ₀ lam oR e1 e2) :
    PairZeroRelW R Nh m b μ₀ lam oR (4 * e2 + 2 * (cr + e1)) (2 * (cr + e1)) := by
  intro x hx h1 hj
  obtain ⟨hP, k1, k2, k3, k4⟩ := hZ x hx h1 hj
  exact zero_rel_pureW (hβ x hx h1 hj) hP (norm_nonneg _) (hg _ hj) hcr he1 he2 k1 k2
    (hR x hx h1 hj).2 k3 k4

set_option maxHeartbeats 1000000 in
/-- **`PairAboveW1` from the reduced pair history, without `s`** (trajectory level; copy of
`pairAboveW1_of_red` with `PairZeroRelW`): `PairSectRed`, `PairCstRelR K₁`, `PairZeroRelW K₂ K₃`,
`GamTopBd K₄`, `‖M_k‖ ≤ M_b`, `0 ≤ ǧ ≤ 1` give `PairAboveW1` with `K_E = K₁ + (K₂ + K₃)K₄`,
`K_R = (K₂ + K₃)M_b`. -/
theorem pairAboveW1_of_redW {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    {K1 K2 K3 K4 Mb : ℝ} (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hMb : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb)
    (hR : PairSectRed R Nh m b μ₀ oR) (hC : PairCstRelR R Nh m b μ₀ lam oR K1)
    (hZ : PairZeroRelW R Nh m b μ₀ lam oR K2 K3) (hT : GamTopBd R Nh m b μ₀ lam K4) :
    PairAboveW1 R Nh m b μ₀ lam (K1 + (K2 + K3) * K4) ((K2 + K3) * Mb) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  obtain ⟨hX, hΩ, -, hω⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  rw [← hjd] at hX hω
  obtain ⟨ho', hl', hab', hS⟩ := hR x hx h1 hj
  rw [← hjd] at hl' hab' hS
  have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
  have e : zOm R m b μ₀ x j = zCst R Nh m b μ₀ x j * zZm R Nh m b μ₀ x :=
    hw.trans (zHi_eq R Nh m b μ₀ x)
  have hY0 : PtCorr2.sE (zOm R m b μ₀ x j) ≠ 0 := by
    rw [e, PtCorr2.sE_mul]; exact mul_ne_zero hX hΩ
  obtain ⟨hXX, hX0', hΩ0', hEs, hEn⟩ := PtCorr2.pair_red_ratio (R.withMsq m) (ptsX x) hN hρ1 hspl
    hm0 hm hV hVL b μ₀ (Obs2.obsInit .two (zV b) (ptsX x))
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) hj (oR x) ho' hl' hab' hS hY0
  set X' := zCstR R Nh m b μ₀ oR x
  set Ω' := zZmR R Nh m b μ₀ oR x
  set F := zFin R Nh m b μ₀ x
  set F' := zFinR R Nh m b μ₀ oR x
  set cc := zCc R Nh m b μ₀
  have hXX' : PtCorr2.sE X' = PtCorr2.sE (zCst R Nh m b μ₀ x j) := by
    rw [← cstOF_zero_eq_zCst]; exact hXX
  have hΩΩ : PtCorr2.sE Ω' = PtCorr2.sE (zZm R Nh m b μ₀ x) := by
    have h2 : PtCorr2.sE (zOm R m b μ₀ x j) =
        PtCorr2.sE (zCst R Nh m b μ₀ x j) * PtCorr2.sE (zZm R Nh m b μ₀ x) := by
      rw [e, PtCorr2.sE_mul]
    have h3 : PtCorr2.sE (zOm R m b μ₀ x j) = PtCorr2.sE X' * PtCorr2.sE Ω' := hEs
    rw [h3, hXX'] at h2
    exact mul_left_cancel₀ hX h2
  obtain ⟨ρ, hρ, hρn, hx'⟩ := hZ x hx h1 hj
  rw [← hjd] at hρn hx'
  obtain ⟨s1, s2, -, -⟩ := PtCorr2.sX_omegaCO_cstC cc F
  obtain ⟨-, -, -, s4'⟩ := PtCorr2.sX_omegaCO_cstC cc F'
  have hΩd : zZm R Nh m b μ₀ x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F := rfl
  have hΩd' : Ω' = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F' := rfl
  have hnA : PtCorr2.nA (zZm R Nh m b μ₀ x) =
      (ε (F : Obs.SA .two (Lam 2 L N)).a - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).a) /
      (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) := by
    unfold PtCorr2.nA; rw [hΩd, s1, s2]
  have hbr : PtCorr2.nAB Ω' =
      (ε (F' : Obs.SA .two (Lam 2 L N)).ab - ρ * ε (F : Obs.SA .two (Lam 2 L N)).a) /
        (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) +
      ρ * PtCorr2.nA (zZm R Nh m b μ₀ x) := by
    have h1' : PtCorr2.nAB Ω' =
        (ε (F' : Obs.SA .two (Lam 2 L N)).ab - cc * Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).ab) /
        (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) := by
      unfold PtCorr2.nAB
      rw [hΩΩ, hΩd, s1, hΩd', s4']
    rw [h1', hnA]
    exact PtCorr2.zm_red_elim hρ
  have hwa : ‖PtCorr2.nA (zZm R Nh m b μ₀ x)‖ ≤
      ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖ +
        K4 * ‖Mmag R m b μ₀ lam j‖ := by
    rw [hω, uA_add_nA_zCst R Nh m b μ₀ x (by omega) hX]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hT x hx h1 hj))
  have hZb := zm_rel_boundW
    (s := ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e)
    hx' hρn
  rw [← hnA] at hZb
  have hK23 : 0 ≤ K2 + K3 := add_nonneg hK2 hK3
  have key := pair_bound_pure (K2 := 0) hK23 (hg j hj).1 (hg j hj).2 (hMb j hj) (norm_nonneg _)
    (show PtCorr2.sAB (zOm R m b μ₀ x j) / PtCorr2.sE (zOm R m b μ₀ x j) =
      PtCorr2.nAB X' + PtCorr2.nAB Ω' from hEn)
    (hC x hx h1 hj) (by rw [hbr]; exact hZb.trans (le_of_eq (by ring))) hwa
  rwa [add_zero] at key

end Traj

end

end Spin2
