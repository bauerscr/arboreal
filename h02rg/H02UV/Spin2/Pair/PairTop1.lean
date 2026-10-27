import Spin2.Pair.PairRed3
import Spin2.Pair.PairSect
import PtCorr2.Last.TopCoal1

/-!
# Top coalescence `j_x ≥ N_h + 1`: the exact split at `k = N_h + 1` along the trajectory

Pair observable `z̃_0z̃_x` (`zV b`, `ptsX x`), `j_x = coal 0 x ≥ N_h + 1` (`j_x ∈ {N - 1, N}`), split
at `k* = N_h + 1` (`T1–T4` of the A3 paper check):

* **`twopt_zz_eq_top`**: `b⟨ψ̄_0ψ_x⟩ = AB - r(A + B) - E + p`, `A = γ_{0,N-1}`, `B = γ_{x,N-1}`
  (`uA`, `uB` at `N_h + 1`), `E = sAB(lastO)/sE(lastO)` (`Π^{≥N_h+1} = lastO`);
* **`dxTop`**, **`oTop`**: the covering polymer at scale `N_h + 1` and the reduced state there
  (`PtCorr2.redTop`, a pair chain of length zero);
* **`pairTop_E`**: `E = n_{ab}X' + n_{ab}Ω'` with `X' = zCstR … oTop`, `Ω' = zZmR … oTop`,
  `sE Ω' = sE Ω` and the one-point closure `n_aΩ = r - γ_{a,N}`;
* **`nAB_zCstR_top`**: `n_{ab}X' = lastDefR` (`r'_{N-1} = 0`, no steps above `N_h + 1`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `coal L (ptsX x).a (ptsX x).b = coal L 0 x`. -/
theorem coal_ptsX (x : Lam 2 L N) :
    Obs.coal L (ptsX x).a (ptsX x).b = Obs.coal L (0 : Lam 2 L N) x := rfl

set_option maxHeartbeats 1000000 in
/-- **The two-point function at the split `N_h + 1`** (`j_x ≥ N_h + 1`; copy of `twopt_zz_eq`). -/
theorem twopt_zz_eq_top {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x) :
    ∃ p r : ℝ, 0 ≤ p ∧ p ≤ r ∧ r ≤ 1 ∧
      1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) = r ∧
      PtCorr2.sE (PtCorr2.lastO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ≠ 0 ∧
      PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) =
        uA R m b μ₀ x (Nh + 1) +
          PtCorr2.nA (PtCorr2.lastO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) Nh
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) =
        uA R m b μ₀ x (Nh + 1) * uB R m b μ₀ x (Nh + 1) -
          (r : ℂ) * uA R m b μ₀ x (Nh + 1) - (r : ℂ) * uB R m b μ₀ x (Nh + 1) -
          PtCorr2.nAB (PtCorr2.lastO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) Nh
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) + (p : ℂ) := by
  obtain ⟨p, r, hp0, hpr, hr1, hr, hP⟩ := PtCorr2.twopt_eq_neg_zz (L := L) (N := N) hb hm0 hh x
  refine ⟨p, r, hp0, hpr, hr1, hr, ?_⟩
  have hk : Nh + 1 ≤ min (Obs.coal L (ptsX x).a (ptsX x).b) (Nh + 1) := by
    rw [coal_ptsX]; exact le_min hj le_rfl
  obtain ⟨hX0, hY0, hza, -, hzz⟩ := PtCorr2.zz_square_split_at (R.withMsq m) (ptsX x) hN hρ1 hspl
    hm0 hm hV hVL hL hk hb hh (zV b) (zV_abFree b)
  rw [PtCorr2.prodHi_top] at hY0 hza hzz
  obtain ⟨ea, eb⟩ := PtCorr2.prodLo_sA_sB (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) rfl (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
  set X := PtCorr2.prodLo (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) with hXd
  have ha : PtCorr2.sA X / PtCorr2.sE X = uA R m b μ₀ x (Nh + 1) := by
    rw [ea, mul_div_cancel_left₀ _ hX0]; rfl
  have hb' : PtCorr2.sB X / PtCorr2.sE X = uB R m b μ₀ x (Nh + 1) := by
    rw [eb, mul_div_cancel_left₀ _ hX0]; rfl
  have hra : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) = r := by
    rw [zObsA_zV, ← hr]
    exact Ward.avg_one_sub_smul _ _ (PtCorr2.onept_Zb_ne hb hm0 hh) _ _
  have hrb : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsB (zV b) (ptsX x)) = r := by
    rw [zObsB_zV, ← hr, ← PtCorr2.avg0_diag_transl hm0 (by omega) x]
    exact Ward.avg_one_sub_smul _ _ (PtCorr2.onept_Zb_ne hb hm0 hh) _ _
  refine ⟨hY0, ?_, ?_⟩
  · refine hza.trans ?_; rw [ha]; rfl
  · have hzz' := hzz
    rw [show (R.withMsq m).msq = m from rfl, hra, hrb, zObsA_zV, zObsB_zV, ha, hb'] at hzz'
    rw [hP, hzz']
    unfold PtCorr2.nAB
    ring

/-! ### The reduced state at scale `N_h + 1` -/

/-- **The covering polymer at scale `N_h + 1`**: the `(N_h+1)`-blocks meeting the sup-ball of
radius `8L^{N_h+1} + |x|_∞` around `0`. -/
def dxTop (Nh : ℕ) (x : Lam 2 L N) : Finset (Lam 2 L N) :=
  PtCorr2.ballPoly (Nh + 1) (0 : Lam 2 L N) (2 ^ (2 + 1) * L ^ (Nh + 1) + supNorm (x - 0))

theorem dCov_dxTop (Nh : ℕ) (x : Lam 2 L N) : PtCorr2.DCov (ptsX x) (Nh + 1) (dxTop Nh x) :=
  ⟨PtCorr2.isConn_ballPoly _ _ _, fun c hc => PtCorr2.ballPoly_cover _ (0 : Lam 2 L N) x c hc⟩

/-- **The reduced state at scale `N_h + 1`** for the pair observable at `x`. -/
def oTop (Nh : ℕ) (m b μ₀ : ℝ) (D : Lam 2 L N → Finset (Lam 2 L N)) (x : Lam 2 L N) :
    Obs2.ObsSt .two L N :=
  PtCorr2.redTop (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (D x) Nh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- For `j_x ≥ N_h + 1` the reduced constants `zCstR` are those of the last step. -/
theorem zCstR_top (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x) :
    zCstR R Nh m b μ₀ oR x = PtCorr2.lastCstOF (R.withMsq m) (ptsX x)
      (Obs.coal L (0 : Lam 2 L N) x) (oR x) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := by
  unfold zCstR PtCorr2.cstOF
  rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty, one_mul]

/-- `lastO` is the product of the original constants `X = zCst (N_h+1)` and `Ω = zZm`. -/
theorem lastO_eq_zCst (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    PtCorr2.lastO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) =
      zCst R Nh m b μ₀ x (Nh + 1) * zZm R Nh m b μ₀ x := by
  unfold PtCorr2.lastO zCst zUo zZm zFin zCc
  rw [Finset.Ico_self, Finset.prod_empty, one_mul, smul_mul_assoc]

theorem lastCstOF_zero_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    PtCorr2.lastCstOF (R.withMsq m) (ptsX x) 0 (Obs2.obsInit .two (zV b) (ptsX x)) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) = zCst R Nh m b μ₀ x (Nh + 1) := by
  unfold PtCorr2.lastCstOF zCst zUo
  rw [Finset.Ico_self, Finset.prod_empty, one_mul, PtCorr2.obsHistFrom_zero]

set_option maxHeartbeats 1000000 in
/-- **The pair part at `N_h + 1` from the reduced state** (exact): for `j_x ≥ N_h + 1` and a
covering polymer `D x` at scale `N_h + 1`, `E = n_{ab}(lastO) = n_{ab}X' + n_{ab}Ω'`
(`X' = zCstR`, `Ω' = zZmR` for `oTop`), `sE Ω' = sE Ω`, and the one-point closure
`n_aΩ = r - γ_{a,N}`. -/
theorem pairTop_E {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (D : Lam 2 L N → Finset (Lam 2 L N)) (x : Lam 2 L N)
    (hD : PtCorr2.DCov (ptsX x) (Nh + 1) (D x)) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x) :
    ∃ p r : ℝ, 0 ≤ p ∧ p ≤ r ∧ r ≤ 1 ∧
      1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) = r ∧
      PtCorr2.sE (zCst R Nh m b μ₀ x (Nh + 1)) ≠ 0 ∧ PtCorr2.sE (zZm R Nh m b μ₀ x) ≠ 0 ∧
      PtCorr2.sE (zZmR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x) = PtCorr2.sE (zZm R Nh m b μ₀ x) ∧
      PtCorr2.sE (zCstR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x) ≠ 0 ∧
      PtCorr2.nA (zZm R Nh m b μ₀ x) = (r : ℂ) - gamNa R Nh m b μ₀ x ∧
      (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) =
        uA R m b μ₀ x (Nh + 1) * uB R m b μ₀ x (Nh + 1) -
          (r : ℂ) * uA R m b μ₀ x (Nh + 1) - (r : ℂ) * uB R m b μ₀ x (Nh + 1) -
          (PtCorr2.nAB (zCstR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x) +
            PtCorr2.nAB (zZmR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x)) + (p : ℂ) := by
  obtain ⟨p, r, hp0, hpr, hr1, hr, hY0, hza, hP⟩ :=
    twopt_zz_eq_top R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨hI, hE, hR⟩ := PtCorr2.pair_red_top (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm hV hVL
    (Obs2.obsInit .two (zV b) (ptsX x)) (Obs2.obsInit_isObs .two (zV b) (ptsX x))
    (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) t hD hj
  obtain ⟨hX'0, hΩ'0, hEn⟩ := hR hY0
  have eX' : zCstR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x =
      PtCorr2.lastCstOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (PtCorr2.redTop (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (D x) Nh t)
          Nh t := zCstR_top R Nh m b μ₀ _ x hj
  have eΩ' : zZmR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x =
      PtCorr2.zmOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (PtCorr2.redTop (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (D x) Nh t)
          Nh t := rfl
  have hL0 := lastO_eq_zCst R Nh m b μ₀ x
  have hX0 : PtCorr2.sE (zCst R Nh m b μ₀ x (Nh + 1)) ≠ 0 := by
    intro h; apply hY0; rw [hL0, PtCorr2.sE_mul, h, zero_mul]
  have hΩ0 : PtCorr2.sE (zZm R Nh m b μ₀ x) ≠ 0 := by
    intro h; apply hY0; rw [hL0, PtCorr2.sE_mul, h, mul_zero]
  have hI' : PtCorr2.sE (zCstR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x) =
      PtCorr2.sE (zCst R Nh m b μ₀ x (Nh + 1)) := by
    rw [eX', ← lastCstOF_zero_eq]; exact hI
  have hΩΩ : PtCorr2.sE (zZmR R Nh m b μ₀ (oTop R Nh m b μ₀ D) x) =
      PtCorr2.sE (zZm R Nh m b μ₀ x) := by
    have h2 := hE
    rw [hL0, PtCorr2.sE_mul, ← eX', ← eΩ', hI'] at h2
    exact (mul_left_cancel₀ hX0 h2).symm
  refine ⟨p, r, hp0, hpr, hr1, hr, hX0, hΩ0, hΩΩ, by rw [eX']; exact hX'0, ?_, ?_⟩
  · have hn : PtCorr2.nA (PtCorr2.lastO (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        Nh t) = PtCorr2.nA (zCst R Nh m b μ₀ x (Nh + 1)) + PtCorr2.nA (zZm R Nh m b μ₀ x) := by
      rw [hL0]; exact PtCorr2.nA_mul hX0 hΩ0
    have hra : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) = r := by
      rw [zObsA_zV, ← hr]
      exact Ward.avg_one_sub_smul _ _ (PtCorr2.onept_Zb_ne hb hm0 hh) _ _
    have hg := uA_add_nA_zCst R Nh m b μ₀ x le_rfl hX0
    rw [hra, hn] at hza
    rw [← hg, hza]; ring
  · rw [hP, hEn, ← eX', ← eΩ']

/-! ### The reduced constants at `N_h + 1` -/

set_option maxHeartbeats 1000000 in
/-- **The reduced constants for `j_x ≥ N_h + 1`** (exact): for a reduced state without one-point
parts and `V' = 0` at `N_h + 1`: `n_{ab}X' = -C_N(0,0)r'_{N-1} + lastDefR`, and
`r'_{N-1} = 0`. -/
theorem nAB_zCstR_top (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (x : Lam 2 L N) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hab : PtCorr2.ObsAbInv (Nh + 1) (oR x)) (hV0 : (oR x).V = 0)
    (hX : PtCorr2.sE (zCstR R Nh m b μ₀ oR x) ≠ 0)
    (hCN : lC R Nh m b μ₀ x x = lC R Nh m b μ₀ 0 0) :
    rRN R Nh m b μ₀ oR x = 0 ∧
      PtCorr2.nAB (zCstR R Nh m b μ₀ oR x) = lastDefR R Nh m b μ₀ oR x := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hF1 : PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) j (oR x) (Nh + 1) t = oR x :=
    PtCorr2.obsHistFrom_le (oR x) t hj
  have hF2 : PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Nh + 1) (oR x) (Nh + 1) t = oR x :=
    PtCorr2.obsHistFrom_self _ _ _
  have e1 : zCstR R Nh m b μ₀ oR x =
      PtCorr2.lastCstOF (R.withMsq m) (ptsX x) (Nh + 1) (oR x) Nh t := by
    rw [zCstR_top R Nh m b μ₀ oR x hj]
    unfold PtCorr2.lastCstOF
    rw [hF1, hF2]
  have hVab : ∀ B, (lVR R Nh m b μ₀ oR x B : Obs.SA .two (Lam 2 L N)).ab = 0 := by
    intro B
    show (((Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
      (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
      (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) j (oR x) (Nh + 1) t)) B : Obs.OE .two _) :
        Obs.SA .two (Lam 2 L N)).ab = 0
    rw [hF1]
    show (0 : Grassmann.N (Lam 2 L N)) + ((oR x).V B : Obs.SA .two (Lam 2 L N)).ab = 0
    rw [hV0]; simp
  have hrR : rRN R Nh m b μ₀ oR x = 0 := by
    unfold rRN Obs2.rAB2
    exact sum_eq_zero fun B _ => by rw [hVab B, Obs.mass2_zero]
  refine ⟨hrR, ?_⟩
  have hab' : PtCorr2.ObsAbInv (Nh + 1)
      (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) j (oR x) (Nh + 1) t) := by rw [hF1]; exact hab
  have H := PtCorr2.oabS_full (R.withMsq m) (histOut (R.withMsq m) Nh t).g.re
    (histOut (R.withMsq m) Nh t).nu.re (st := (histOut (R.withMsq m) Nh t).st)
    (D := (histOut (R.withMsq m) Nh t).D) (K := (histOut (R.withMsq m) Nh t).K) hab'
  have hU := H.uXO_ab (P := ptsX x) (C := lC R Nh m b μ₀) univ
  have hVa : ∀ B, (lVR R Nh m b μ₀ oR x B : Obs.SA .two (Lam 2 L N)).a = 0 := fun B =>
    (H.hV B).1
  have hVb : ∀ B, (lVR R Nh m b μ₀ oR x B : Obs.SA .two (Lam 2 L N)).b = 0 := fun B =>
    (H.hV B).2
  have hβa : Obs2.betaTot2 (Nh + 1) (lVR R Nh m b μ₀ oR x) = 0 := by
    unfold Obs2.betaTot2; exact sum_eq_zero fun B _ => by rw [hVa B, Obs.mass2_zero]
  have hβb : Obs2.betaB2 (Nh + 1) (lVR R Nh m b μ₀ oR x) = 0 := by
    unfold Obs2.betaB2; exact sum_eq_zero fun B _ => by rw [hVb B, Obs.mass2_zero]
  have hl := Obs2.pair_step_red (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
    (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x)
    (fun B => by rw [hVa B]; exact Obs2.Loc2Form.zero _)
    (fun B => by rw [hVb B]; exact Obs2.Loc2Form.zero _)
    (sum_eq_zero fun B _ => by rw [hVab B, map_zero])
    (sum_eq_zero fun B _ => by rw [hVa B, map_zero])
    (sum_eq_zero fun B _ => by rw [hVb B, map_zero]) hCN hβa hβb
  have hUa : (Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
      (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) : Obs.SA .two (Lam 2 L N)).a = 0 := hU.1
  rw [hUa, map_zero, neg_zero, zero_mul, add_zero] at hl
  have hab2 : PtCorr2.ObsAbInv (Nh + 1) (oR x) := hab
  have h0' : PtCorr2.sE (PtCorr2.lastCstOF (R.withMsq m) (ptsX x) (Nh + 1) (oR x) Nh t) ≠ 0 := by
    rw [← e1]; exact hX
  rw [e1, PtCorr2.nAB_lastCstOF (R := R.withMsq m) (P := ptsX x) (t := t) hab2 le_rfl h0']
  have hUe : PtCorr2.lastUR (R.withMsq m) (ptsX x) (Nh + 1) (oR x) t Nh =
      Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
        (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) := by
    unfold PtCorr2.lastUR lVR lWR lKR lC
    rw [hF1, hF2]; rfl
  rw [hUe, hl, show Obs2.rAB2 (Nh + 1) (lVR R Nh m b μ₀ oR x) = 0 from hrR, mul_zero, neg_zero,
    zero_sub]
  unfold lastDefR
  dsimp only [ptsX]

end Traj

end

end Spin2
