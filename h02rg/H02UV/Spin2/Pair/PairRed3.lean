import Spin2.Pair.PairRed2
import PtCorr2.Pair.PairReduceChain

/-!
# `PairCstRelR` reduced: the reduced pair chain, the `r'` flow, discrete Gronwall (PR3/PR5 along
the trajectory)

Pair observable, reduced states `o'_x = oR x` at `j = j_x` (`PairSectRed`). Along the reduced
history (`PtCorr2.obsHistFrom`):

* **`nAB_zCstR_sum`** (exact): `n_{ab}X' = ∑_{j≤k≤N_h}(-C_k(0,0)r'_k + d'_k) + (-C_N(0,0)r'_N + d'_N)`,
  `d'_k = -𝔡_k + X_k + ρ_aρ_b` (`hDefR`, `lastDefR`): **no vertex term `β_aβ_b`, no `γ`-cross terms**
  (compare `nAB_zCst_sum`).
* **`pairCstRelR_of_parts`**: `PairRRelR c_r` (`‖r'_k‖ ≤ c_r‖M_j‖ǧ_j‖β_{a,k}‖`, `β_{a,k}` the
  vertex of the original history), `PairVertSum c_s` (unchanged), `PairDefSumR c_d` give
  `PairCstRelR (c_rc_s + c_d)`.
* **`pairRRelR_of_src`**: the reduced `r'` flow `r'_{k+1} = (1 - n_{a,k})r'_k + σ'_k`,
  `σ'_k = -d_r + 𝔡₂ - e_{ab} + f` (`srcR`), has the **same** `n_{a,k}` as the original `β_a` flow
  (`PtCorr2.nA2_fullV_indep`); with the seed `r'_j = 0` (`PairRedSeed`) and `PairSrcRelR c_σ c_ε`
  (relative sources, no vertex term), discrete Gronwall gives `PairRRelR (c_σe^{c_ε})`.

Remaining analytic inputs (PR5): `PairSrcRelR`, `PairDefSumR`, `PairVertSum`; exact input (PR1):
`PairSectRed`, `PairRedSeed`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `r'_k` along the reduced history from `j_x`. -/
def hRR (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  PtCorr2.rR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- The defect and remainder of step `k` of the reduced history: `-𝔡_k + X_k + ρ_aρ_b`. -/
def hDefR (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  PtCorr2.incR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k +
    hC00 R m b μ₀ k * hRR R m b μ₀ oR x k

/-- The full `V` of the last step of the reduced history. -/
def lVR (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) :
    Obs2.OFam .two 2 L N :=
  Obs2.fullV (R.withMsq m) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
    (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- The full `𝒲` of the last step of the reduced history. -/
def lWR (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) :
    Obs2.OFam .two 2 L N :=
  Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
    (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- The full `K` of the last step of the reduced history. -/
def lKR (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) :
    Obs2.OAct .two 2 L N :=
  Obs2.fullK (R.withMsq m) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
    (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- `r'_N` (the last step). -/
def rRN (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) : ℂ :=
  Obs2.rAB2 (Nh + 1) (lVR R Nh m b μ₀ oR x)

/-- The defect and remainder of the last step of the reduced history. -/
def lastDefR (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) : ℂ :=
  -Obs2.pdefAB2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x) +
    (Obs2.xAB2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x) (lWR R Nh m b μ₀ oR x)
        (lKR R Nh m b μ₀ oR x) +
      Obs2.rhoA2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
          (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) *
        Obs2.rhoB2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
          (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x))

/-- The source `σ'_k = -d_r + 𝔡₂ - e_{ab} + f` of the reduced `r'` flow. -/
def srcR (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  let C := Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  let K := PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  (Obs2.pdefM2 k C V - Obs2.dR2 (ptsX x) k C V) - Obs2.eAB2 (ptsX x) k C W K +
    Obs2.farABm (ptsX x) k C V W

/-- **Named input (PR1, seed): the reduced state has no `σ_aσ_b` constants and no marginal pair
coupling at `j_x`**: `∑_Bε(V'_j(B)_{ab}) = 0`, `r'_j = 0` (the quartic seed has no `m₂`). -/
def PairRedSeed (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∑ B ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
        ε (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs.coal L (0 : Lam 2 L N) x) B :
            Obs.SA .two (Lam 2 L N)).ab = 0 ∧
      hRR R m b μ₀ oR x (Obs.coal L (0 : Lam 2 L N) x) = 0

theorem lVR_ab (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (B : Fin 2 → ℕ) :
    (lVR R Nh m b μ₀ oR x B : Obs.SA .two (Lam 2 L N)).ab =
      (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) B : Obs.SA .two (Lam 2 L N)).ab :=
  (zero_add _).trans (zero_add _).symm

set_option maxHeartbeats 1000000 in
/-- **The reduced constants as a sum over the steps above coalescence** (exact; `R.P = Pc`). -/
theorem nAB_zCstR_sum (hP : R.P = Pc) (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    (hab : PtCorr2.ObsAbInv (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (hseed : ∑ B ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
        ε (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs.coal L (0 : Lam 2 L N) x) B :
            Obs.SA .two (Lam 2 L N)).ab = 0)
    (hX : PtCorr2.sE (zCstR R Nh m b μ₀ oR x) ≠ 0)
    (hCN : lC R Nh m b μ₀ x x = lC R Nh m b μ₀ 0 0) :
    PtCorr2.nAB (zCstR R Nh m b μ₀ oR x) =
      ∑ k ∈ Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (-(hC00 R m b μ₀ k * hRR R m b μ₀ oR x k) + hDefR R m b μ₀ oR x k) +
        (-(lC R Nh m b μ₀ 0 0 * rRN R Nh m b μ₀ oR x) + lastDefR R Nh m b μ₀ oR x) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hC : ∀ k, Obs2.histCovO (R.withMsq m) t k (ptsX x).b (ptsX x).b =
      Obs2.histCovO (R.withMsq m) t k (ptsX x).a (ptsX x).a := fun k => by
    rw [histCov_gamInt_at R hP, histCov_gamInt_at R hP]
  have h1 := PtCorr2.nAB_cstOF_eq (R := R.withMsq m) (P := ptsX x) (t := t) hab le_rfl (by omega) hX
  have h2 := PtCorr2.qR_eq_sum (R := R.withMsq m) (P := ptsX x) (t := t) hab hC hseed (Nh + 1)
    (by omega)
  -- the last step
  have hab' := PtCorr2.hab_at (R := R.withMsq m) (P := ptsX x) (t := t) hab
    (show j ≤ Nh + 1 by omega)
  have H := PtCorr2.oabS_full (R.withMsq m) (histOut (R.withMsq m) Nh t).g.re
    (histOut (R.withMsq m) Nh t).nu.re (st := (histOut (R.withMsq m) Nh t).st)
    (D := (histOut (R.withMsq m) Nh t).D) (K := (histOut (R.withMsq m) Nh t).K) hab'
  have hU := H.uXO_ab (P := ptsX x) (C := lC R Nh m b μ₀) univ
  have hVa : ∀ B, (lVR R Nh m b μ₀ oR x B : Obs.SA .two (Lam 2 L N)).a = 0 := fun B =>
    (H.hV B).1
  have hVb : ∀ B, (lVR R Nh m b μ₀ oR x B : Obs.SA .two (Lam 2 L N)).b = 0 := fun B =>
    (H.hV B).2
  have h0ab : ∑ B ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ε (lVR R Nh m b μ₀ oR x B : Obs.SA .two (Lam 2 L N)).ab = 0 := by
    simp only [lVR_ab]
    exact PtCorr2.epsAB_histR_succ (R := R.withMsq m) (P := ptsX x) (o' := oR x) (t := t)
      (show j ≤ Nh by omega)
  have hβa : Obs2.betaTot2 (Nh + 1) (lVR R Nh m b μ₀ oR x) = 0 := by
    unfold Obs2.betaTot2; exact sum_eq_zero fun B _ => by rw [hVa B, Obs.mass2_zero]
  have hβb : Obs2.betaB2 (Nh + 1) (lVR R Nh m b μ₀ oR x) = 0 := by
    unfold Obs2.betaB2; exact sum_eq_zero fun B _ => by rw [hVb B, Obs.mass2_zero]
  have hl := Obs2.pair_step_red (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
    (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x)
    (fun B => by rw [hVa B]; exact Obs2.Loc2Form.zero _)
    (fun B => by rw [hVb B]; exact Obs2.Loc2Form.zero _) h0ab
    (sum_eq_zero fun B _ => by rw [hVa B, map_zero])
    (sum_eq_zero fun B _ => by rw [hVb B, map_zero]) hCN hβa hβb
  have hUe : PtCorr2.lastUR (R.withMsq m) (ptsX x) j (oR x) t Nh =
      Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
        (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) := rfl
  have hUa : (Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
      (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) : Obs.SA .two (Lam 2 L N)).a = 0 := hU.1
  have hUb : (Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
      (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) : Obs.SA .two (Lam 2 L N)).b = 0 := hU.2
  rw [hUa, map_zero, neg_zero, zero_mul, add_zero] at hl
  have e1 : zCstR R Nh m b μ₀ oR x = PtCorr2.cstOF (R.withMsq m) (ptsX x) j (oR x) Nh j t := rfl
  rw [e1, h1]
  unfold PtCorr2.qRN
  rw [hUe]
  have e2 : PtCorr2.qR (R.withMsq m) (ptsX x) j (oR x) t (Nh + 1) -
      ε (Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
        (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) : Obs.SA .two (Lam 2 L N)).ab -
      PtCorr2.qR (R.withMsq m) (ptsX x) j (oR x) t j =
      (PtCorr2.qR (R.withMsq m) (ptsX x) j (oR x) t (Nh + 1) -
        PtCorr2.qR (R.withMsq m) (ptsX x) j (oR x) t j) +
      -ε (Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
        (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) : Obs.SA .two (Lam 2 L N)).ab := by ring
  rw [e2, h2, hl]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    unfold hDefR hRR hC00
    ring
  · unfold rRN lastDefR
    dsimp only [ptsX]
    ring

/-! ### Named inputs and the reduction -/

/-- **Named input: `r'` is relatively small** (`c_r‖M_j‖ǧ_j` against the vertex `β_{a,k}` of the
original history), above coalescence and at the last step. -/
def PairRRelR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
      ‖hRR R m b μ₀ oR x k‖ ≤
        cr * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖hBeta R m b μ₀ x k‖) ∧
    ‖rRN R Nh m b μ₀ oR x‖ ≤
      cr * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖

/-- **Named input (PR5): the defects and remainders of the reduced history** are `O(M_j²ǧ_j)`. -/
def PairDefSumR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cd : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ‖hDefR R m b μ₀ oR x k‖ +
        ‖lastDefR R Nh m b μ₀ oR x‖ ≤
      cd * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

set_option maxHeartbeats 1000000 in
/-- **`PairCstRelR` from the reduced step decomposition** (trajectory level). -/
theorem pairCstRelR_of_parts (hP : R.P = Pc) {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cr cs cd : ℝ} (hcr : 0 ≤ cr)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hRd : PairSectRed R Nh m b μ₀ oR) (hSeed : PairRedSeed R Nh m b μ₀ oR)
    (hR : PairRRelR R Nh m b μ₀ lam oR cr) (hS : PairVertSum R Nh m b μ₀ lam cs)
    (hD : PairDefSumR R Nh m b μ₀ lam oR cd) :
    PairCstRelR R Nh m b μ₀ lam oR (cr * cs + cd) := by
  intro x hx h1 hj
  obtain ⟨hX, hΩ, -, -⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  obtain ⟨ho', hl', hab', hS'⟩ := hRd x hx h1 hj
  have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
  have hY0 : PtCorr2.sE (zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) ≠ 0 := by
    rw [show zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) = _ from hw.trans (zHi_eq R Nh m b μ₀ x),
      PtCorr2.sE_mul]
    exact mul_ne_zero hX hΩ
  obtain ⟨-, hX0', -, -, -⟩ := PtCorr2.pair_red_ratio (R.withMsq m) (ptsX x) hN hρ1 hspl
    hm0 hm hV hVL b μ₀ (Obs2.obsInit .two (zV b) (ptsX x))
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) hj (oR x) ho' hl' hab' hS' hY0
  rw [nAB_zCstR_sum R hP Nh m b μ₀ oR x hj hab' (hSeed x hx h1 hj).1 hX0'
    (lC_diag R hV hVL hVN b μ₀ x)]
  obtain ⟨hr, hrN⟩ := hR x hx h1 hj
  exact pairCst_pure _ _ _ _ _ _ _ _ _ hcr (norm_nonneg _) (hg _ hj) hr hrN (hS x hx h1 hj)
    (hD x hx h1 hj)

/-! ### `PairRRelR` from the sources of the reduced `r'` flow -/

/-- **Named input (PR5): the sources of the reduced `r'` flow** (`σ'_k = srcR`, no vertex term)
and the `K`, `𝒲` parts `e_{a,k}` of the original `β_a` flow are small relative to `β_{a,k+1}`:
`‖σ'_k‖ ≤ s_k‖β_{a,k+1}‖`, `‖e_{a,k}‖ ≤ ε_k‖β_{a,k+1}‖`, `∑s_k ≤ c_σ‖M_j‖ǧ_j`, `∑ε_k ≤ c_ε`. -/
def PairSrcRelR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cσ cε : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ s ε : ℕ → ℝ, (∀ k, 0 ≤ s k) ∧ (∀ k, 0 ≤ ε k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        hBeta R m b μ₀ x (k + 1) ≠ 0 ∧
        ‖srcR R m b μ₀ oR x k‖ ≤ s k * ‖hBeta R m b μ₀ x (k + 1)‖ ∧
        ‖Obs2.eA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k‖ ≤ ε k * ‖hBeta R m b μ₀ x (k + 1)‖) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), s k ≤
        cσ * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ε k ≤ cε

theorem rRN_eq (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) :
    rRN R Nh m b μ₀ oR x = hRR R m b μ₀ oR x (Nh + 1) := by
  unfold rRN hRR PtCorr2.rR Obs2.rAB2
  simp only [lVR_ab]

set_option maxHeartbeats 1000000 in
/-- **`PairRRelR` from the reduced sources** (discrete Gronwall, `Obs2.rel_gronwall`):
`PairSectRed`, `PairRedSeed`, `PairSrcRelR c_σ c_ε` give `PairRRelR (c_σe^{c_ε})`. -/
theorem pairRRelR_of_src {Nh : ℕ} (m : ℝ) (b μ₀ : ℝ) (lam : ℕ → ℂ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cσ cε : ℝ} (hcσ : 0 ≤ cσ)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hRd : PairSectRed R Nh m b μ₀ oR) (hSeed : PairRedSeed R Nh m b μ₀ oR)
    (hS : PairSrcRelR R Nh m b μ₀ lam oR cσ cε) :
    PairRRelR R Nh m b μ₀ lam oR (cσ * Real.exp cε) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨s, ε, hs0, hε0, hk, hsum, hεsum⟩ := hS x hx h1 hj
  rw [← hjd] at hk hsum hεsum
  obtain ⟨ho', -, hab', -⟩ := hRd x hx h1 hj
  rw [← hjd] at hab'
  obtain ⟨-, hr0⟩ := hSeed x hx h1 hj
  rw [← hjd] at hr0
  have hn : ∀ k, j ≤ k → Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) t k)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t k) =
      Obs2.nA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t k := fun k _ =>
    PtCorr2.nA2_fullV_indep (R.withMsq m) (ptsX x) k _ _ _ _
      (PtCorr2.obsHistFrom_isObs (R := R.withMsq m) (P := ptsX x) (j := j) ho' t k)
      (Obs2.obsHist_isObs (R.withMsq m) (ptsX x) _ (Obs2.obsInit_isObs .two (zV b) (ptsX x)) k t)
  have hG := Obs2.rel_gronwall (fun k => hRR R m b μ₀ oR x k) (fun k => hBeta R m b μ₀ x k)
    (Obs2.nA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t)
    (fun k => srcR R m b μ₀ oR x k)
    (Obs2.eA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t) s ε j (Nh + 1)
    hr0 hs0 hε0
    (fun k hk1 _ => by
      have h := PtCorr2.rR_succ (R := R.withMsq m) (P := ptsX x) (o' := oR x) (t := t) hab' hk1
      rw [hn k hk1] at h
      show hRR R m b μ₀ oR x (k + 1) = _
      unfold hRR srcR
      dsimp only
      rw [h]; ring)
    (fun k _ _ => Obs2.betaA_hist_succ (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      t (Obs2.obsInit_two_form _ _) k)
    (fun k hk1 hk2 => (hk k (mem_Ico.2 ⟨hk1, hk2⟩)).1)
    (fun k hk1 hk2 => (hk k (mem_Ico.2 ⟨hk1, hk2⟩)).2.1)
    (fun k hk1 hk2 => (hk k (mem_Ico.2 ⟨hk1, hk2⟩)).2.2)
  have bnd : ∀ k, j ≤ k → k ≤ Nh + 1 → ‖hRR R m b μ₀ oR x k‖ ≤
      cσ * Real.exp cε * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 *
        ‖hBeta R m b μ₀ x k‖ := by
    intro k hk1 hk2
    refine (hG k hk1 hk2).trans ?_
    have hsub : Finset.Ico j k ⊆ Finset.Ico j (Nh + 1) := Ico_subset_Ico_right hk2
    have hS1 : ∑ i ∈ Finset.Ico j k, s i ≤ cσ * ‖Mmag R m b μ₀ lam j‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 :=
      (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hs0 i).trans hsum
    have hP1 : ∏ i ∈ Finset.Ico j k, (1 + ε i) ≤ Real.exp cε :=
      (prod_one_add_le_exp _ _ fun i _ => hε0 i).trans (Real.exp_le_exp.2
        ((sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hε0 i).trans hεsum))
    have hP0 : 0 ≤ ∏ i ∈ Finset.Ico j k, (1 + ε i) := prod_nonneg fun i _ => by linarith [hε0 i]
    have := mul_le_mul hS1 hP1 hP0 (mul_nonneg (mul_nonneg hcσ (norm_nonneg _)) (hg j hj))
    have := mul_le_mul_of_nonneg_right this (norm_nonneg (hBeta R m b μ₀ x k))
    calc (∑ i ∈ Finset.Ico j k, s i) * (∏ i ∈ Finset.Ico j k, (1 + ε i)) *
          ‖hBeta R m b μ₀ x k‖
        ≤ cσ * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 *
            Real.exp cε * ‖hBeta R m b μ₀ x k‖ := this
      _ = _ := by ring
  refine ⟨fun k hk => bnd k (mem_Ico.1 hk).1 (mem_Ico.1 hk).2.le, ?_⟩
  rw [rRN_eq, (rTilN_eq R Nh m b μ₀ x j).2]
  exact bnd (Nh + 1) (by omega) le_rfl

set_option maxHeartbeats 1000000 in
/-- **`PairAboveW1` from the reduced pair history, all parts** (trajectory level):
`PairSectRed`, `PairRedSeed`, `PairSrcRelR c_σ c_ε`, `PairVertSum c_s`, `PairDefSumR c_d`,
`PairZeroRelR K₂ K₃`, `GamTopBd K₄` give `PairAboveW1` with
`K_E = c_σe^{c_ε}c_s + c_d + K₂ + K₃K₄`, `K_R = K₃M_b`. -/
theorem pairAboveW1_of_red_parts (hP : R.P = Pc) {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ)
    (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cσ cε cs cd K2 K3 K4 Mb : ℝ} (hcσ : 0 ≤ cσ)
    (hK3 : 0 ≤ K3)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hMb : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb)
    (hRd : PairSectRed R Nh m b μ₀ oR) (hSeed : PairRedSeed R Nh m b μ₀ oR)
    (hSrc : PairSrcRelR R Nh m b μ₀ lam oR cσ cε) (hS : PairVertSum R Nh m b μ₀ lam cs)
    (hD : PairDefSumR R Nh m b μ₀ lam oR cd) (hZ : PairZeroRelR R Nh m b μ₀ lam oR K2 K3)
    (hT : GamTopBd R Nh m b μ₀ lam K4) :
    PairAboveW1 R Nh m b μ₀ lam (cσ * Real.exp cε * cs + cd + K2 + K3 * K4) (K3 * Mb) := by
  have hg0 : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := fun k hk => (hg k hk).1
  have hRR' := pairRRelR_of_src R m b μ₀ lam oR hcσ hg0 hRd hSeed hSrc
  have hC := pairCstRelR_of_parts R hP hN m hρ1 hspl hm0 hm hV hVL hVN hL hb hh lam oR
    (mul_nonneg hcσ (Real.exp_pos _).le) hg0 hRd hSeed hRR' hS hD
  exact pairAboveW1_of_red R hN m hρ1 hspl hm0 hm hV hVL hL hb hh lam oR hK3 hg hMb hRd hC hZ hT

end Traj

end

end Spin2
