import Spin2.Pair.PairRed
import PtCorr2.Pair.PairReduce

/-!
# `PairAboveW1` from the Pauli-reduced pair history (PR1/PR2/PR6 along the trajectory)

Pair observable `z̃_0z̃_x` (`zV b`, `ptsX x`), trajectory at mass `m²`, `j = j_x`. A **reduced
state** `o'_x` (`oR x`) at scale `j_x` is an observable state without `σ_a`, `σ_b` parts whose input
`Z_j(o')` has the same `∅` and `σ_aσ_b` components as the input `Z_j` of the pair history
(`PairSectRed`, PR1). Along the history from `j_x` it keeps no one-point parts (PR2,
`PtCorr2.obsAbInv_histFrom`), and exactly (`PtCorr2.pair_red_ratio`)

  `E = n_{ab}(ω_{Γ_j}Z_j) = n_{ab}X' + n_{ab}Ω'`,

`X' = zCstR` the reduced constants above `j` (no `Δγ_aΔγ_b` cross terms), `Ω' = ω_{cQ}(F'_N)` the
reduced zero mode (`zZmR`, `F'_N = zFinR`), with the same bulk normalisation `sE Ω' = sE Ω`.

Named inputs in reduced form (for `x ≠ 0`, `1 ≤ j_x ≤ N_h`, `M = M_{j_x}`, `ǧ = ǧ_{j_x}`):
* **`PairSectRed oR`** (PR1): the reduced state exists in the above sense (the polymer regrouping
  of the cross products `σ_aV_a·σ_bV_b` of different factors into a `K'_{ab}` supported on
  connected polymers containing the coalescence region; open as formalisation);
* **`PairCstRelR K₁`**: `‖n_{ab}X'‖ ≤ K₁‖M‖²ǧ` (PR5: the reduced constants `q'_N - q'_j`);
* **`PairZeroRelR K₂ K₃`** (PR6): `∃ρ̃`, `c2F'_{N,ab} = ρ̃·c2F_{N,a}`, `‖ρ̃‖ ≤ K₃‖M‖ǧ`,
  `‖εF'_{N,ab} - ρ̃εF_{N,a}‖ ≤ K₂‖M‖²ǧ‖εF_{N,e} - c·c2F_{N,e}‖` (`ρ̃ ≈ r'_N/β_{a,N}`);
* `GamTopBd K₄` (unchanged).

**`pairAboveW1_of_red`** / **`pairAboveW1_of_red_flow`**: these give `PairAboveW1` with
`K_E = K₁ + K₂ + K₃K₄`, `K_R = K₃M_b` (same constants as `pairAboveW1_of_parts`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The reduced constants `X' = ∏_{j≤i≤N_h} chOF_i · det·e^{-u'_N}` at `j = j_x`. -/
def zCstR (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) :
    Obs.OE .two (Lam 2 L N) :=
  PtCorr2.cstOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) Nh
    (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- The reduced final object `F'_N`. -/
def zFinR (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) :
    Obs.OE .two (Lam 2 L N) :=
  PtCorr2.finOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) Nh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- The reduced zero-mode integral `Ω' = ω_{cQ}(F'_N)`. -/
def zZmR (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) :
    Obs.OE .two (Lam 2 L N) :=
  PtCorr2.zmOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) Nh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- **Named input (PR1): the reduced states.** `o'_x` is observable, local and without one-point
parts at scale `j_x`, and `Z_{j_x}(o'_x)` has the `∅` and `σ_aσ_b` components of `Z_{j_x}`. -/
def PairSectRed (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    (oR x).IsObs ∧ PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) ∧
      PtCorr2.ObsAbInv (Obs.coal L (0 : Lam 2 L N) x) (oR x) ∧
      PtCorr2.SectEq
        (PtCorr2.ZhO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
          (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (PtCorr2.ZhOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- **Named input (PR5): the reduced pair constants above coalescence.** -/
def PairCstRelR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (K1 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oR x)‖ ≤
      K1 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- **Named input (PR6): the reduced final object.** The pair coupling of `F'_N` is relative to the
`a`-vertex of the original `F_N`, `c2F'_{ab} = ρ̃·c2F_a`, `‖ρ̃‖ ≤ K₃‖M‖ǧ`, and the constant part
`‖εF'_{ab} - ρ̃εF_a‖ ≤ K₂‖M‖²ǧ‖εF_e - c·c2F_e‖`. -/
def PairZeroRelR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (K2 K3 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ ρ : ℂ,
      Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab =
        ρ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a ∧
      ‖ρ‖ ≤ K3 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab -
          ρ * ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
        K2 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e -
            zCc R Nh m b μ₀ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e‖

/-- The original constants are the history-from-`0` constants. -/
theorem cstOF_zero_eq_zCst (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) :
    PtCorr2.cstOF (R.withMsq m) (ptsX x) 0 (Obs2.obsInit .two (zV b) (ptsX x)) Nh k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) = zCst R Nh m b μ₀ x k := by
  unfold PtCorr2.cstOF PtCorr2.lastCstOF PtCorr2.chOF zCst zUo PtCorr2.chO
  simp only [PtCorr2.obsHistFrom_zero]

set_option maxHeartbeats 1000000 in
/-- **`PairAboveW1` from the reduced pair history** (trajectory level): `PairSectRed`,
`PairCstRelR K₁`, `PairZeroRelR K₂ K₃`, `GamTopBd K₄`, `‖M_k‖ ≤ M_b`, `0 ≤ ǧ ≤ 1` give
`PairAboveW1` with `K_E = K₁ + K₂ + K₃K₄`, `K_R = K₃M_b`. -/
theorem pairAboveW1_of_red {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    {K1 K2 K3 K4 Mb : ℝ} (hK3 : 0 ≤ K3)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hMb : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb)
    (hR : PairSectRed R Nh m b μ₀ oR) (hC : PairCstRelR R Nh m b μ₀ lam oR K1)
    (hZ : PairZeroRelR R Nh m b μ₀ lam oR K2 K3) (hT : GamTopBd R Nh m b μ₀ lam K4) :
    PairAboveW1 R Nh m b μ₀ lam (K1 + K2 + K3 * K4) (K3 * Mb) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  obtain ⟨hX, hΩ, -, hω⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  rw [← hjd] at hX hω
  obtain ⟨ho', hl', hab', hS⟩ := hR x hx h1 hj
  rw [← hjd] at hl' hab' hS
  -- the original `ω_{Γ_j}Z_j = XΩ`
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
  -- `sE Ω' = sE Ω`
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
  have hs : ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e ≠ 0 := by
    rw [← s1, ← hΩd]; exact hΩ
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
  have hZb := PtCorr2.zm_pauli_bound hs hx' hρn (le_refl ‖PtCorr2.nA (zZm R Nh m b μ₀ x)‖)
  exact pair_bound_pure hK3 (hg j hj).1 (hg j hj).2 (hMb j hj) (norm_nonneg _)
    (show PtCorr2.sAB (zOm R m b μ₀ x j) / PtCorr2.sE (zOm R m b μ₀ x j) =
      PtCorr2.nAB X' + PtCorr2.nAB Ω' from hEn)
    (hC x hx h1 hj) (by rw [hbr]; exact hZb.trans (le_of_eq (by ring))) hwa

end Traj

end

end Spin2
