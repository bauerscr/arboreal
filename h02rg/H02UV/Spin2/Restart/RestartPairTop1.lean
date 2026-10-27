import Spin2.Pair.PairTop3
import PtCorr2.Restart.RestartPairTop

/-!
# T5 (pair/top restart): the two-point output of a general state at `N - 1`, linear in the
`a`-side size

Pair `(0, x)` with `j_x ≥ N_h + 1` (top coalescence), the `h = 0` trajectory. For an **arbitrary**
observable state `o` at scale `N_h + 1` (local, e.g. the state reached by the restarted history of
a small `a`-side datum, `PtCorr2.obsHistFrom … m δ (N_h + 1)`):

* **`rpTopE`** `= n_{ab}(lastOF (N_h+1) o)` (the pair part of the last factor), **`rpTopU`**
  `= -ε(u^{obs}_a)` (the accumulated `a`-constant), **`rpTopOut`** `= rpTopU·γ_{x,N-1} − rpTopE`
  (the two-point output; bilinear in the `a`- and `b`-sides of the state, the `b`-side fixed to the
  reference `γ_{x,N-1}`).
* **`rpTopOut_ref`**: on the reference state (the history of the pair observable) the output is
  the two-point function, `b⟨ψ̄_0ψ_x⟩ = rpTopOut`.
* **`rp_zero_abs`** (pure): the zero mode with an **absolute** `a`-side, normalised by the
  reference one-point data (`|c| ≤ 4|γ_{a,N}||s₀|/|β|`).
* **`rp_topE_le`**: for the reduced state of `o` with the seed bound
  `A^{(|𝓑(X)|-4)_+}‖K'_{N_h+1}(X)‖_{wM(2s²σ, M_b)} ≤ c_K` (`s = s_{N_h}`, `σ > 0` the `a`-side size
  of `o` in coupling units):
  `|rpTopE o| ≤ (c_{Lab}c_Sc_u² + 8(½ + (81/32)c_{Jab}c_S)c_uK₄)·(σ/|β_{a,N_h}|)·‖M_{N_h}‖²ǧ_{N_h}`,
  linear in `σ` (`c_S = 8c_K + 1`); the reference one-point items are those of `pairTop_E_le`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

/-- **The zero mode with an absolute `a`-side** (pure). With the reference one-point data
`y_a ≈ β`, `|x_a| ≤ ¼|c||β|`, `x_a - c·y_a = -γs₀`: `|(x_{ab} - c·y_{ab})/s₀| ≤ 4|γ|(e_X + e_Y)/|β|`
whenever `|x_{ab}| ≤ |c|e_X`, `|y_{ab}| ≤ e_Y`. -/
theorem rp_zero_abs {xab yab xa ya β cc s γ : ℂ} {eX eY : ℝ} (hβ : β ≠ 0) (hs : s ≠ 0)
    (heX : 0 ≤ eX) (heY : 0 ≤ eY)
    (h1 : ‖ya - β‖ ≤ 1 / 2 * ‖β‖) (h4 : ‖xa‖ ≤ 1 / 4 * (‖cc‖ * ‖β‖))
    (hγ : xa - cc * ya = -(γ * s)) (hX : ‖xab‖ ≤ ‖cc‖ * eX) (hY : ‖yab‖ ≤ eY) :
    ‖(xab - cc * yab) / s‖ ≤ 4 * ‖γ‖ * (eX + eY) / ‖β‖ := by
  have hβn : 0 < ‖β‖ := norm_pos_iff.2 hβ
  have hsn : 0 < ‖s‖ := norm_pos_iff.2 hs
  -- `|c||β| ≤ 4|γ||s|`
  have hya : 1 / 2 * ‖β‖ ≤ ‖ya‖ := by
    have := norm_sub_norm_le β (β - ya)
    rw [show β - (β - ya) = ya by ring, norm_sub_rev] at this
    linarith
  have hcy : cc * ya = xa + γ * s := by linear_combination -hγ
  have hc1 : ‖cc‖ * ‖ya‖ ≤ ‖xa‖ + ‖γ‖ * ‖s‖ := by
    rw [← norm_mul, ← norm_mul, hcy]; exact norm_add_le _ _
  have hc2 : ‖cc‖ * (1 / 2 * ‖β‖) ≤ ‖cc‖ * ‖ya‖ :=
    mul_le_mul_of_nonneg_left hya (norm_nonneg _)
  have hcβ : ‖cc‖ * ‖β‖ ≤ 4 * (‖γ‖ * ‖s‖) := by linarith
  have hcs : ‖cc‖ / ‖s‖ ≤ 4 * ‖γ‖ / ‖β‖ := by
    rw [div_le_div_iff₀ hsn hβn]; linarith
  rw [norm_div]
  have hnum : ‖xab - cc * yab‖ ≤ ‖cc‖ * (eX + eY) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left hY (norm_nonneg cc)
    linarith
  calc ‖xab - cc * yab‖ / ‖s‖ ≤ ‖cc‖ * (eX + eY) / ‖s‖ :=
        div_le_div_of_nonneg_right hnum hsn.le
    _ = ‖cc‖ / ‖s‖ * (eX + eY) := by ring
    _ ≤ 4 * ‖γ‖ / ‖β‖ * (eX + eY) := mul_le_mul_of_nonneg_right hcs (by linarith)
    _ = 4 * ‖γ‖ * (eX + eY) / ‖β‖ := by ring

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The pair part of the last factor of a general state `o` at `N_h + 1`**:
`n_{ab}(lastOF (N_h+1) o)`. -/
def rpTopE (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) : ℂ :=
  PtCorr2.nAB (PtCorr2.lastOF (R.withMsq m) (ptsX x) (Nh + 1) o Nh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- **The accumulated `a`-constant of a state**: `-ε(u^{obs}_a)`. -/
def rpTopU (o : Obs2.ObsSt .two L N) : ℂ := -ε ((o.u : Obs.SA .two (Lam 2 L N)).a)

/-- **The two-point output of a state `o` at `N_h + 1`** (top coalescence, `h = 0`):
`rpTopU o·γ_{x,N-1} − rpTopE o`. -/
def rpTopOut (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) : ℂ :=
  rpTopU o * uB R m b μ₀ x (Nh + 1) - rpTopE R Nh m b μ₀ x o

/-- The reduced state of `o` at `N_h + 1` (covering polymer `dxTop`). -/
def rpRed (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) :
    Obs2.ObsSt .two L N :=
  PtCorr2.redSt (R.withMsq m) (ptsX x) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K o (dxTop Nh x)

/-- The reference state at `N_h + 1`: the history of the pair observable. -/
def rpRef (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs2.ObsSt .two L N :=
  Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

theorem rp_lastO_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    PtCorr2.lastO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) =
      PtCorr2.lastOF (R.withMsq m) (ptsX x) (Nh + 1) (rpRef R Nh m b μ₀ x) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := by
  unfold PtCorr2.lastO PtCorr2.lastOF PtCorr2.zmOF PtCorr2.finOF PtCorr2.zmC rpRef
  rw [PtCorr2.obsHistFrom_self]

set_option maxHeartbeats 1000000 in
/-- **The output on the reference state is the two-point function** (`j_x ≥ N_h + 1`, `h = 0`). -/
theorem rpTopOut_ref {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh0 : b = μ₀ + m) (x : Lam 2 L N) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x) :
    (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) =
      rpTopOut R Nh m b μ₀ x (rpRef R Nh m b μ₀ x) := by
  obtain ⟨p, r, hp0, hpr, -, hr, -, -, hP⟩ :=
    twopt_zz_eq_top R hN m hρ1 hspl hm0 hm hV hVL hL hb (le_of_eq hh0) x hj
  have hr0 : (r : ℂ) = 0 := by
    rw [← hr, PtCorr2.onept_avg0_h0 hb hm0 hh0, mul_one_div_cancel
      (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]
  have hr0' : r = 0 := by exact_mod_cast hr0
  have hp : (p : ℂ) = 0 := by
    have : p = 0 := le_antisymm (hr0' ▸ hpr) hp0
    rw [this, Complex.ofReal_zero]
  rw [hP, hr0, hp, rp_lastO_eq]
  unfold rpTopOut rpTopE rpTopU
  have : uA R m b μ₀ x (Nh + 1) = -ε (((rpRef R Nh m b μ₀ x).u : Obs.SA .two (Lam 2 L N)).a) := rfl
  rw [this]; ring

set_option maxHeartbeats 8000000 in
/-- **The pair output of a general state at `N_h + 1`, linear in the `a`-side size** (one
trajectory, one `x` with `j_x ≥ N_h + 1`, `h = 0`). -/
theorem rp_topE_le {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK0 r₀ : ℝ} (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hb : 0 < b) (hh0 : b = μ₀ + m)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) (hA2 : 2 ≤ R.A)
    (hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (R.A / 2) r₀)
    (hcW : 0 ≤ cW) (hcK0 : 0 ≤ cK0) (hCf : 0 ≤ Cf)
    (hg0 : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hs1 : 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ R.ρ)
    (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2)
    (hs3 : cRho L * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀)
    (lam : ℕ → ℂ) (x : Lam 2 L N) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs) (hlo : PtCorr2.ObsLocInv (ptsX x) (Nh + 1) o)
    {σ Mb cK cu K4 KA : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb) (hcK : 0 ≤ cK) (hcu : 0 ≤ cu)
    (hKo : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ)
          Mb) (Nh + 1)
        (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rpRed R Nh m b μ₀ x o).K X) ≤ ENNReal.ofReal cK)
    (hMa0 : 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖hBeta R m b μ₀ x Nh‖ ≤
      cu * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hMbM : Mb ≤ cu * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hβ0 : hBeta R m b μ₀ x Nh ≠ 0)
    (hone1 : ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖)
    (hone2 : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KA * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖)
    (hgam : ‖gamNa R Nh m b μ₀ x‖ ≤ K4 * ‖Mmag R m b μ₀ lam Nh‖)
    (hCN : lC R Nh m b μ₀ x x = lC R Nh m b μ₀ 0 0)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2) (hmA : 8 * KA * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * cK + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖rpTopE R Nh m b μ₀ x o‖ ≤
      (cLab L * (8 * cK + 1) * cu ^ 2 + 8 * (1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK + 1)) * cu * K4) *
        (σ / ‖hBeta R m b μ₀ x Nh‖) * ‖Mmag R m b μ₀ lam Nh‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set oG : Lam 2 L N → Obs2.ObsSt .two L N := fun _ => rpRed R Nh m b μ₀ x o with hoG
  set Mn := ‖Mmag R m b μ₀ lam Nh‖ with hMn
  set g := (t Nh).1 with hgd
  set sN := histS (R.withMsq m) Nh t with hsN
  set Ma := 2 * sN ^ 2 * σ with hMad
  set hb0 := ‖hBeta R m b μ₀ x Nh‖ with hb0d
  have hhb0 : 0 < hb0 := norm_pos_iff.2 hβ0
  have hMn0 : 0 ≤ Mn := norm_nonneg _
  have hsN : 0 < sN := histS_pos' (R.withMsq m) hρ0 hVL.2.2.2.2.2.1 t Nh
  have hMa : 0 < Ma := mul_pos (mul_pos two_pos (pow_pos hsN 2)) hσ
  -- the reference split
  obtain ⟨p, r, hp0, hpr, -, hr, hX0, hΩ0, -, -, hnA, -⟩ :=
    pairTop_E R hNh m hρ1 hspl hm0 hm hV hVL hL8 hb (le_of_eq hh0) (dxTop Nh) x
      (dCov_dxTop Nh x) hj
  have hr0 : (r : ℂ) = 0 := by
    rw [← hr, PtCorr2.onept_avg0_h0 hb hm0 hh0, mul_one_div_cancel
      (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]
  rw [hr0, zero_sub] at hnA
  -- the decomposition for `o`
  have hY0 : PtCorr2.sE (PtCorr2.lastOF (R.withMsq m) (ptsX x) (Nh + 1) o Nh t) ≠ 0 := by
    rw [← PtCorr2.rp_sE_lastO_eq (R.withMsq m) (ptsX x)
      (Obs2.obsInit_isObs .two (zV b) (ptsX x)) ho Nh t, lastO_eq_zCst, PtCorr2.sE_mul]
    exact mul_ne_zero hX0 hΩ0
  obtain ⟨-, hsplit⟩ := PtCorr2.rp_pair_red_gen (R.withMsq m) (ptsX x) hNh hρ1 hspl hm0 hm hV hVL
    t o ho hlo (dCov_dxTop Nh x) hj le_rfl
  obtain ⟨hX'0, hΩ'0, hEn⟩ := hsplit hY0
  have eX' : zCstR R Nh m b μ₀ oG x =
      PtCorr2.lastCstOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oG x) Nh t :=
    zCstR_top R Nh m b μ₀ oG x hj
  have eΩ' : zZmR R Nh m b μ₀ oG x =
      PtCorr2.zmOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oG x) Nh t := rfl
  have hE : rpTopE R Nh m b μ₀ x o =
      PtCorr2.nAB (zCstR R Nh m b μ₀ oG x) + PtCorr2.nAB (zZmR R Nh m b μ₀ oG x) := by
    rw [eX', eΩ']; exact hEn
  -- the reduced constants
  have hF : PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oG x)
      (Nh + 1) t = oG x := PtCorr2.obsHistFrom_le (oG x) t hj
  have habT : PtCorr2.ObsAbInv (Nh + 1) (oG x) := PtCorr2.obsAbInv_redSt _ _ _ _ _ _ _ _ _ _
  have hlocT : PtCorr2.ObsLocInv (ptsX x) (Nh + 1) (oG x) :=
    PtCorr2.obsLocInv_redSt_last hVN (rawInv_histU (R.withMsq m) hV hVL t (Nh + 1) le_rfl)
      (RawInv.stepL hVL (rawInv_hist (R.withMsq m) hρ0 Nh hV t) (t Nh).1 (t Nh).2.1
        (rawD_mem (R.withMsq m) _ _) (rawK_mem (R.withMsq m) _ _)).2.1
      (RawInv.stepL hVL (rawInv_hist (R.withMsq m) hρ0 Nh hV t) (t Nh).1 (t Nh).2.1
        (rawD_mem (R.withMsq m) _ _) (rawK_mem (R.withMsq m) _ _)).2.2 hlo
  obtain ⟨-, hXd⟩ := nAB_zCstR_top R Nh m b μ₀ oG x hj habT rfl (by rw [eX']; exact hX'0) hCN
  -- the last step of the reduced state
  obtain ⟨s', hs', hsc1, hsc2, hc2, hε, hLD⟩ := pairLastAB_xT R hNh hV hVL hVN hLp hL8 hA2 hmN hG
    hr₀ hr₀1 hJ hcW hcK0 hCf hg0 hg1 hs1 hs2 hs3 hs4 hs5 oG x
    (PtCorr2.redSt_isObs _ _ _ _ _ _ _ _ _ _) (by rw [hF]; exact hlocT)
    (by rw [hF]; exact habT) hMa hMb le_rfl le_rfl hcK
    (fun b' _ => by rw [hF]; show Obs2.oTo _ _ _ (0 : Obs.OE .two (Lam 2 L N)) ≤ _
                    rw [Obs2.oTo_zero']; exact zero_le)
    (fun b' _ => by rw [hF]; show Obs2.oTo _ _ _ (0 : Obs.OE .two (Lam 2 L N)) ≤ _
                    rw [Obs2.oTo_zero']; exact zero_le)
    (fun X hX => by rw [hF]; exact hKo X hX)
  simp only [zero_add] at hc2 hε hLD
  set cS := 8 * cK + 1 with hcSd
  have hcS : 1 ≤ cS := by rw [hcSd]; linarith
  -- the coupling `β_{a,N-1}` of the reference
  set β1 := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβ1d
  have hβx : hb0 ≤ 2 * β1 := by
    set P := ptsX (L := L) (N := N) x
    have hflow := bt2_flow R P (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
    have hBB : ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ 2 * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      rw [hflow]; exact beta_step_ge htop.1 htop.2
    have hβeq : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x)‖ =
        ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      have h : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x) =
          Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (Obs2.histVO2 (R.withMsq m) P
            (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) := by
        unfold Obs2.betaTot2
        refine sum_congr rfl fun b' _ => ?_
        rw [Obs2.histVO2_a]
        congr 1
        exact Obs2.emb_add_cmp true _ _
      rw [h]; rfl
    rw [hβ1d, hβeq]; exact hBB
  have hβ10 : 0 < β1 := by linarith
  have hβ1ne : Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) ≠ 0 := norm_pos_iff.1 hβ10
  -- the constants
  have hcJ0 : 0 ≤ cJab L r₀ := by
    unfold cJab
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcS', hQ1]
    have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
    positivity
  set cJ' := cJet L * (cRho L + 4 / r₀ ^ 2) with hcJ'd
  have hcJ'0 : 0 ≤ cJ' := by
    rw [hcJ'd]
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcS', hQ1]
    exact mul_nonneg h1 (add_nonneg h2 (by positivity))
  have hcL : 0 ≤ cLab L := by
    unfold cLab
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    positivity
  -- `M_a ≤ (81/32)·2σ s'²`-type bounds
  have hs'2 : 0 < s' ^ 2 := pow_pos hs' 2
  set eY := 81 / 32 * cJab L r₀ * cS * σ * Mb with heYd
  have heY : 0 ≤ eY := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcJ0)
    (by linarith)) hσ.le) hMb.le
  have hY : ‖Suscept.c2 (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖ ≤ eY := by
    have k1 : Ma * Mb ≤ s' ^ 2 * (81 / 32 * σ * Mb) := by
      have : Ma ≤ s' ^ 2 * (81 / 32 * σ) :=
        calc Ma = 2 * σ * sN ^ 2 := by rw [hMad]; ring
          _ ≤ 2 * σ * ((9 / 8) ^ 2 * s' ^ 2) :=
              mul_le_mul_of_nonneg_left hsc1 (by linarith)
          _ = s' ^ 2 * (81 / 32 * σ) := by ring
      have := mul_le_mul_of_nonneg_right this hMb.le
      linarith
    have k2 : s' ^ 2 * ‖Suscept.c2 (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
        s' ^ 2 * eY := by
      refine hc2.trans ?_
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ0 (by linarith : (0 : ℝ) ≤ cS))
      calc cJab L r₀ * cS * (Ma * Mb) ≤ cJab L r₀ * cS * (s' ^ 2 * (81 / 32 * σ * Mb)) := this
        _ = s' ^ 2 * eY := by rw [heYd]; ring
    exact le_of_mul_le_mul_left k2 hs'2
  -- `|εF'_{ab}| ≤ |c|·½σM_b`
  set Z := (lastOut (R.withMsq m) Nh t).Z with hZd
  have hZ : Z ≠ 0 := lastOut_Z_ne (R.withMsq m) hρ0 hρ1 Nh _
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have hc := zCc_ge R hNh hm0 b μ₀ hK hmT hZ
  set Λ := (L : ℝ) ^ (2 * N) with hΛd
  have hΛ : 0 < Λ := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hmid : 1 / (2 * m * Λ) / ‖Z‖ ≤ ‖zCc R Nh m b μ₀‖ := by
    refine le_trans (le_of_eq ?_) hc
    field_simp
    exact (div_self hZn.ne').symm
  set eX := 1 / 2 * σ * Mb with heXd
  have heX : 0 ≤ eX := mul_nonneg (mul_nonneg (by norm_num) hσ.le) hMb.le
  have hX : ‖ε (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      ‖zCc R Nh m b μ₀‖ * eX := by
    have k1 : Ma * Mb ≤ 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * (σ * Mb) := by
      have : Ma ≤ 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * σ :=
        calc Ma = 2 * σ * sN ^ 2 := by rw [hMad]; ring
          _ ≤ 2 * σ * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) :=
              mul_le_mul_of_nonneg_left hsc2 (by linarith)
          _ = 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * σ := by ring
      have := mul_le_mul_of_nonneg_right this hMb.le
      linarith
    calc ‖ε (zFinR R Nh m b μ₀ oG x : Obs.SA .two (Lam 2 L N)).ab‖
        ≤ cJ' * cS * (Ma * Mb) := hε
      _ ≤ cJ' * cS * (81 / 32 * R.ℓ ^ 2 / ‖Z‖ * (σ * Mb)) :=
          mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ'0 (by linarith))
      _ = (81 / 16 * cJ' * cS * R.ℓ ^ 2) / ‖Z‖ * eX := by rw [heXd]; ring
      _ ≤ (1 / (2 * m * Λ)) / ‖Z‖ * eX := by
          have h2mΛ : 0 < 2 * m * Λ := mul_pos (mul_pos two_pos hm0) hΛ
          have hq : 81 / 16 * cJ' * cS * R.ℓ ^ 2 ≤ 1 / (2 * m * Λ) := by
            rw [le_div_iff₀ h2mΛ]
            have e : 81 / 16 * cJ' * cS * R.ℓ ^ 2 * (2 * m * Λ) =
                2 * (81 / 16 * cJ' * cS * R.ℓ ^ 2) * m * Λ := by ring
            rw [e]; exact hmAB
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hq hZn.le) heX
      _ ≤ ‖zCc R Nh m b μ₀‖ * eX := mul_le_mul_of_nonneg_right hmid heX
  -- `|εF_a| ≤ ¼|c||β|` (reference)
  have he' : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by
    have hKA : KA * (β1 / ‖Z‖) ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := by
      have hKA0 : KA ≤ 1 / (8 * m * Λ) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hq : 0 ≤ β1 / ‖Z‖ := div_nonneg hβ10.le hZn.le
      have e : 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 = 1 / (8 * m * Λ) * (β1 / ‖Z‖) := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hKA0 hq
    have hc' : 1 / (2 * m * ‖Z‖ * Λ) ≤ ‖zCc R Nh m b μ₀‖ := by
      refine le_trans (le_of_eq ?_) hmid
      field_simp
    calc ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤ KA * β1 / ‖Z‖ := hone2
      _ = KA * (β1 / ‖Z‖) := by ring
      _ ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := hKA
      _ ≤ 1 / 4 * ‖zCc R Nh m b μ₀‖ * β1 := by gcongr
      _ = 1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by ring
  -- the zero mode of the reduced state, with the reference normaliser
  set F := zFin R Nh m b μ₀ x with hFd
  set F' := zFinR R Nh m b μ₀ oG x with hF'd
  set cc := zCc R Nh m b μ₀ with hccd
  obtain ⟨s1, s2, -, -⟩ := PtCorr2.sX_omegaCO_cstC cc F
  obtain ⟨s1', -, -, s4'⟩ := PtCorr2.sX_omegaCO_cstC cc F'
  have hoGo : (oG x).IsObs := PtCorr2.redSt_isObs _ _ _ _ _ _ _ _ _ _
  have hFe : (F' : Obs.SA .two (Lam 2 L N)).e = (F : Obs.SA .two (Lam 2 L N)).e := by
    have h := congrArg (fun y : Step.EvR (Lam 2 L N) => (y : Grassmann.N (Lam 2 L N)))
      (PtCorr2.rp_bulk_finO (R.withMsq m) (ptsX x) (Nh + 1) (histOut (R.withMsq m) Nh t).st
        (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
        (histOut (R.withMsq m) Nh t).D (histOut (R.withMsq m) Nh t).K
        (PtCorr2.obsHistFrom_isObs (P := ptsX x) (j := Obs.coal L (0 : Lam 2 L N) x)
          hoGo t (Nh + 1))
        (Obs2.obsHist_isObs (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
          (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (Nh + 1) t))
    simp only [coe_bulk] at h
    exact h
  have hΩd : zZm R Nh m b μ₀ x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F := rfl
  have hΩd' : zZmR R Nh m b μ₀ oG x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F' := rfl
  set s0 := ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e
    with hs0d
  have hs0 : s0 ≠ 0 := by
    have : PtCorr2.sE (zZm R Nh m b μ₀ x) = s0 := by rw [hΩd, s1]
    rw [← this]; exact hΩ0
  have hnABΩ : PtCorr2.nAB (zZmR R Nh m b μ₀ oG x) =
      (ε (F' : Obs.SA .two (Lam 2 L N)).ab - cc * Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).ab) /
        s0 := by
    unfold PtCorr2.nAB
    rw [hΩd', s4', s1', hFe]
  have hγ : ε (F : Obs.SA .two (Lam 2 L N)).a - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).a =
      -(gamNa R Nh m b μ₀ x * s0) := by
    have h := hnA
    unfold PtCorr2.nA at h
    rw [hΩd, s1, s2] at h
    rw [div_eq_iff hs0] at h
    rw [h]; ring
  have hZm := rp_zero_abs hβ1ne hs0 heX heY hone1 he' hγ hX hY
  rw [← hnABΩ] at hZm
  -- assembly
  have hD1 : ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oG x)‖ ≤
      cLab L * cS * cu ^ 2 * (σ / hb0) * Mn ^ 2 * g := by
    rw [hXd]
    refine hLD.trans ?_
    have hMa' : Ma ≤ cu * Mn * g * (σ / hb0) := by
      have e : Ma = 2 * sN ^ 2 * hb0 * (σ / hb0) := by
        rw [hMad]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hMa0 (div_nonneg hσ.le hhb0.le)
    have hMg : 0 ≤ cu * Mn * g := mul_nonneg (mul_nonneg hcu hMn0) hg0.le
    have h1 : Ma * Mb ≤ (cu * Mn * g * (σ / hb0)) * (cu * Mn * g) :=
      mul_le_mul hMa' hMbM hMb.le (mul_nonneg hMg (div_nonneg hσ.le hhb0.le))
    have h2 : (cu * Mn * g * (σ / hb0)) * (cu * Mn * g) ≤ cu ^ 2 * (σ / hb0) * Mn ^ 2 * g := by
      have : g * g ≤ g := mul_le_of_le_one_left hg0.le hg1
      have h0 : 0 ≤ cu ^ 2 * (σ / hb0) * Mn ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg hσ.le hhb0.le)) (sq_nonneg _)
      have e : (cu * Mn * g * (σ / hb0)) * (cu * Mn * g) = cu ^ 2 * (σ / hb0) * Mn ^ 2 * (g * g) := by
        ring
      rw [e]; exact mul_le_mul_of_nonneg_left this h0
    have := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hcL (by linarith : (0:ℝ) ≤ cS))
    calc cLab L * cS * (Ma * Mb) ≤ cLab L * cS * (cu ^ 2 * (σ / hb0) * Mn ^ 2 * g) := this
      _ = cLab L * cS * cu ^ 2 * (σ / hb0) * Mn ^ 2 * g := by ring
  have hD2 : ‖PtCorr2.nAB (zZmR R Nh m b μ₀ oG x)‖ ≤
      8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * cu * K4 * (σ / hb0) * Mn ^ 2 * g := by
    refine hZm.trans ?_
    set c1 := 1 / 2 + 81 / 32 * cJab L r₀ * cS with hc1d
    have hc10 : 0 ≤ c1 := by
      rw [hc1d]
      have : 0 ≤ 81 / 32 * cJab L r₀ * cS := mul_nonneg (mul_nonneg (by norm_num) hcJ0) (by linarith)
      linarith
    have hsum : eX + eY ≤ c1 * σ * (cu * Mn * g) := by
      have e : eX + eY = c1 * σ * Mb := by rw [heXd, heYd, hc1d]; ring
      rw [e]; exact mul_le_mul_of_nonneg_left hMbM (mul_nonneg hc10 hσ.le)
    have hγ' : ‖gamNa R Nh m b μ₀ x‖ ≤ K4 * Mn := hgam
    have hinv : 1 / β1 ≤ 2 / hb0 := by
      rw [div_le_div_iff₀ hβ10 hhb0]; linarith
    have hXY0 : 0 ≤ eX + eY := add_nonneg heX heY
    calc 4 * ‖gamNa R Nh m b μ₀ x‖ * (eX + eY) / β1
        = 4 * ‖gamNa R Nh m b μ₀ x‖ * (eX + eY) * (1 / β1) := by ring
      _ ≤ 4 * (K4 * Mn) * (c1 * σ * (cu * Mn * g)) * (2 / hb0) := by
          have hK4M : 0 ≤ K4 * Mn := (norm_nonneg _).trans hγ'
          have a1 : 4 * ‖gamNa R Nh m b μ₀ x‖ * (eX + eY) ≤
              4 * (K4 * Mn) * (c1 * σ * (cu * Mn * g)) := by
            have := mul_le_mul hγ' hsum hXY0 hK4M
            linarith
          have hMg0 : 0 ≤ cu * Mn * g := mul_nonneg (mul_nonneg hcu hMn0) hg0.le
          exact mul_le_mul a1 hinv (div_nonneg zero_le_one hβ10.le)
            (mul_nonneg (mul_nonneg (by norm_num) hK4M)
              (mul_nonneg (mul_nonneg hc10 hσ.le) hMg0))
      _ = 8 * c1 * cu * K4 * (σ / hb0) * Mn ^ 2 * g := by ring
  rw [hE]
  have hfin : ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oG x) + PtCorr2.nAB (zZmR R Nh m b μ₀ oG x)‖ ≤
      (cLab L * cS * cu ^ 2 + 8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * cu * K4) *
        (σ / hb0) * Mn ^ 2 * g :=
    calc ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oG x) + PtCorr2.nAB (zZmR R Nh m b μ₀ oG x)‖
        ≤ ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oG x)‖ + ‖PtCorr2.nAB (zZmR R Nh m b μ₀ oG x)‖ :=
          norm_add_le _ _
      _ ≤ cLab L * cS * cu ^ 2 * (σ / hb0) * Mn ^ 2 * g +
          8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * cu * K4 * (σ / hb0) * Mn ^ 2 * g :=
          add_le_add hD1 hD2
      _ = _ := by ring
  exact hfin

end Traj

end

end Spin2
