import Spin2.Pair.PairAbove
import Spin2.Gam.GamFormB
import Obs2.Pair.PairChain
import Step2.Last.FlowLastF1a

/-!
# `PairCstRel`: the Pauli-adjusted pair constant above coalescence, step by step

Pair observable `z̃_0z̃_x` (`zV b`, `ptsX x`), trajectory at mass `m²`, `j = j_x ≥ 1`.
`n_{ab}X = (q_N - q_j) + (γ_{a,N} - γ_{a,j})(γ_{b,N} - γ_{b,j})` (`zCst_coup`) is the
Pauli-adjusted accumulated pair constant `D_{j,N}` of `Obs2/Pair/PairChain`, telescoped over the
steps `j ≤ k ≤ N_h` of the history and the last step (`lC`, `lV`, `lW`, `lK`, with `zUN` its
constant):

* **`nAB_zCst_split`**: `n_{ab}X = D_{j,N_h+1} + inc_N` (`lastInc`);
* **`nAB_zCst_sum`** (`R.P = Pc`, `ValidLast`): `n_{ab}X = ∑_{j≤k≤N_h}(-C_k(0,0)r̃_{j,k} + det_k - 𝔡_k
  + Rem_k) + (-C_N(0,0)r̃_N + det_N - 𝔡_N + Rem_N)` (`Obs2.pairD2_eq_sum`, `pair_step_id`; the
  covariances are translation invariant, `histCov_gamInt_at`, `LastN.covN`);
* named inputs, exactly (`x ≠ 0`, `1 ≤ j_x ≤ N_h`, `M = M_{j_x}`, `ǧ = ǧ_{j_x}`):
  - **`PairRTilRel c_r`**: `‖r̃_{j,k}‖ ≤ c_r‖M‖ǧ‖β_{a,k}‖` for `j ≤ k ≤ N_h` and at the last step
    (the marginal Pauli-adjusted coupling is relatively small; it is reduced to its sources
    by `Obs2.rTil2_rel_bound`, see `pairRTilRel_of_src`);
  - **`PairVertSum c_s`**: `∑_k‖C_k(0,0)‖‖β_{a,k}‖ + ‖C_N(0,0)‖‖β_{a,N}‖ ≤ c_s‖M‖` (the absolute
    one-point vertex sum above coalescence, cf. `GamTopBd`);
  - **`PairDefSum c_d`**: `∑_k‖det_k - 𝔡_k + Rem_k‖ + ‖det_N - 𝔡_N + Rem_N‖ ≤ c_d‖M‖²ǧ` (the
    determinant and Pauli defects and the remainders);
* **`pairCstRel_of_parts`**: these give `PairCstRel (c_rc_s + c_d)`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The covariance of the last step. -/
def lC (Nh : ℕ) (m b μ₀ : ℝ) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ :=
  LastN.stCovN (R.withMsq m) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st

/-- The full `V` of the last step. -/
def lV (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs2.OFam .two 2 L N :=
  Obs2.fullV (R.withMsq m) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
    (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- The full `𝒲` of the last step. -/
def lW (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs2.OFam .two 2 L N :=
  Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
    (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- The full `K` of the last step. -/
def lK (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs2.OAct .two 2 L N :=
  Obs2.fullK (R.withMsq m) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
    (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

theorem zUN_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    zUN R Nh m b μ₀ x = Obs2.uObsTot (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x)
      (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x) := rfl

/-- The Pauli-adjusted increment of the last step,
`Δq_N + Δγ_{a,N}A_b + A_aΔγ_{b,N} + Δγ_{a,N}Δγ_{b,N}`, `A_• = γ_{•,N_h+1} - γ_{•,j}`. -/
def lastInc (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (j : ℕ) : ℂ :=
  -ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).ab +
    (-ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a) *
      (uB R m b μ₀ x (Nh + 1) - uB R m b μ₀ x j) +
    (uA R m b μ₀ x (Nh + 1) - uA R m b μ₀ x j) *
      (-ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).b) +
    (-ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a) *
      (-ε (zUN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).b)

/-- `D_{j,k}` along the pair history. -/
def pD (m b μ₀ : ℝ) (x : Lam 2 L N) (j k : ℕ) : ℂ :=
  Obs2.pairD2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j k

/-- **`n_{ab}X = D_{j,N_h+1} + inc_N`** (exact). -/
theorem nAB_zCst_split (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) {j : ℕ} (hj : j ≤ Nh + 1)
    (hX : PtCorr2.sE (zCst R Nh m b μ₀ x j) ≠ 0) :
    PtCorr2.nAB (zCst R Nh m b μ₀ x j) = pD R m b μ₀ x j (Nh + 1) + lastInc R Nh m b μ₀ x j := by
  obtain ⟨-, -, h3⟩ := zCst_coup R Nh m b μ₀ x hj
  unfold PtCorr2.nAB
  rw [h3, mul_div_cancel_left₀ _ hX]
  unfold pD Obs2.pairD2 lastInc qN gamNa gamNb
  unfold Obs2.qAB2 Obs2.gamA Obs2.gamB2 zq uA uB
  ring

/-- The `r̃` of the last step. -/
def rTilN (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (j : ℕ) : ℂ :=
  Obs2.rAB2 (Nh + 1) (lV R Nh m b μ₀ x) +
    Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) * (uB R m b μ₀ x (Nh + 1) - uB R m b μ₀ x j) +
    Obs2.betaB2 (Nh + 1) (lV R Nh m b μ₀ x) * (uA R m b μ₀ x (Nh + 1) - uA R m b μ₀ x j)

/-- The defect and remainder part of the last step: `det_N - 𝔡_N + Rem_N`. -/
def lastDef (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (j : ℕ) : ℂ :=
  Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) * Obs2.betaB2 (Nh + 1) (lV R Nh m b μ₀ x) *
      (lC R Nh m b μ₀ 0 0 * lC R Nh m b μ₀ 0 0 - lC R Nh m b μ₀ 0 x * lC R Nh m b μ₀ x 0) -
    Obs2.pdefAB2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) +
    (Obs2.xAB2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
        (lK R Nh m b μ₀ x) +
      Obs2.rhoA2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
          (lK R Nh m b μ₀ x) *
        ((uB R m b μ₀ x (Nh + 1) - uB R m b μ₀ x j) -
          Obs2.betaB2 (Nh + 1) (lV R Nh m b μ₀ x) * lC R Nh m b μ₀ 0 0) +
      Obs2.rhoB2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
          (lK R Nh m b μ₀ x) *
        ((uA R m b μ₀ x (Nh + 1) - uA R m b μ₀ x j) -
          Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) * lC R Nh m b μ₀ 0 0) +
      Obs2.rhoA2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
          (lK R Nh m b μ₀ x) *
        Obs2.rhoB2 (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
          (lK R Nh m b μ₀ x))

theorem lV_a (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (B : Fin 2 → ℕ) :
    (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).a =
      (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) B : Obs.SA .two (Lam 2 L N)).a :=
  (Obs2.emb_add_cmp true _ _).trans (Obs2.emb_add_cmp true _ _).symm

theorem lV_b (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (B : Fin 2 → ℕ) :
    (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).b =
      (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) B : Obs.SA .two (Lam 2 L N)).b :=
  (Obs2.emb_add_cmp false _ _).trans (Obs2.emb_add_cmp false _ _).symm

theorem lV_ab (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (B : Fin 2 → ℕ) :
    (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).ab =
      (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) B : Obs.SA .two (Lam 2 L N)).ab :=
  (zero_add _).trans (zero_add _).symm

/-- **The last step**: `inc_N = -C_N(0,0)r̃_N + (det_N - 𝔡_N + Rem_N)` if `C_N(x,x) = C_N(0,0)`. -/
theorem lastInc_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (j : ℕ)
    (hC : lC R Nh m b μ₀ x x = lC R Nh m b μ₀ 0 0) :
    lastInc R Nh m b μ₀ x j =
      -(lC R Nh m b μ₀ 0 0 * rTilN R Nh m b μ₀ x j) + lastDef R Nh m b μ₀ x j := by
  have hVa : ∀ B, Obs2.Loc2Form (ptsX x).a (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).a := fun B => by
    rw [lV_a]; exact Obs2.obsHist_hform2 _ _ _ _ (Obs2.obsInit_two_form _ _) _ B
  have hVb : ∀ B, Obs2.Loc2Form (ptsX x).b (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).b := fun B => by
    rw [lV_b]; exact Obs2.obsHist_hform2_b _ _ _ _ (Obs2.obsInit_two_form_b _ _) _ B
  have h0ab : ∑ B ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ε (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).ab = 0 := by
    simp only [lV_ab]; exact Obs2.epsAB_hist_succ _ _ _ _ Nh
  have h0a : ∑ B ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ε (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).a = 0 := by
    simp only [lV_a]; exact Obs2.epsTot2_succ _ _ _ _ Nh
  have h0b : ∑ B ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ε (lV R Nh m b μ₀ x B : Obs.SA .two (Lam 2 L N)).b = 0 := by
    simp only [lV_b]; exact Obs2.epsB_hist_succ _ _ _ _ Nh
  have h := Obs2.pair_step_id (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
    (lK R Nh m b μ₀ x) hVa hVb h0ab h0a h0b hC (uA R m b μ₀ x (Nh + 1) - uA R m b μ₀ x j)
    (uB R m b μ₀ x (Nh + 1) - uB R m b μ₀ x j)
  unfold lastInc rTilN lastDef
  rw [zUN_eq]
  dsimp only [ptsX] at h ⊢
  linear_combination h

/-- `C_N(x,x) = C_N(0,0)` (translation invariance of the last covariance, `LastN.covN`). -/
theorem lC_diag {Nh : ℕ} {m : ℝ} (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hVL : ValidAtL (R.withMsq m) Nh) (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (b μ₀ : ℝ)
    (x : Lam 2 L N) : lC R Nh m b μ₀ x x = lC R Nh m b μ₀ 0 0 := by
  have H := rawInv_histU (R.withMsq m) hV hVL (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
    le_rfl
  have hT := (LastN.covN hVN H).2.1
  have := hT x 0 0
  simp only [zero_add] at this
  exact this

/-- The defect and remainder part of step `k` of the pair history. -/
def hDef (m b μ₀ : ℝ) (x : Lam 2 L N) (j k : ℕ) : ℂ :=
  Obs2.detDef2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k -
    Obs2.pdef2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k +
    Obs2.pairRem2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j k

/-- `r̃_{j,k}` along the pair history. -/
def hRTil (m b μ₀ : ℝ) (x : Lam 2 L N) (j k : ℕ) : ℂ :=
  Obs2.rTil2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j k

/-- `C_k(0,0)` along the pair history. -/
def hC00 (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 0

/-- `β_{a,k}` along the pair history. -/
def hBeta (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.betaTot2 k (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)

/-- **`n_{ab}X` as a sum over the steps above coalescence** (exact; `R.P = Pc`):
`n_{ab}X = ∑_{j≤k≤N_h}(-C_k(0,0)r̃_{j,k} + def_k) + (-C_N(0,0)r̃_N + def_N)`. -/
theorem nAB_zCst_sum (hP : R.P = Pc) (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ Nh + 1) (hX : PtCorr2.sE (zCst R Nh m b μ₀ x j) ≠ 0)
    (hCN : lC R Nh m b μ₀ x x = lC R Nh m b μ₀ 0 0) :
    PtCorr2.nAB (zCst R Nh m b μ₀ x j) =
      ∑ k ∈ Ico j (Nh + 1), (-(hC00 R m b μ₀ k * hRTil R m b μ₀ x j k) + hDef R m b μ₀ x j k) +
        (-(lC R Nh m b μ₀ 0 0 * rTilN R Nh m b μ₀ x j) + lastDef R Nh m b μ₀ x j) := by
  rw [nAB_zCst_split R Nh m b μ₀ x hj hX, lastInc_eq R Nh m b μ₀ x j hCN]
  congr 1
  have hC : ∀ k, Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
      (ptsX x).b (ptsX x).b = Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
        k (ptsX x).a (ptsX x).a := fun k => by
    rw [histCov_gamInt_at R hP, histCov_gamInt_at R hP]
  rw [pD, Obs2.pairD2_eq_sum _ _ _ _ (Obs2.obsInit_two_form _ _) (Obs2.obsInit_two_form_b _ _)
    hj1 hC _ hj]
  refine sum_congr rfl fun k _ => ?_
  unfold Obs2.pairInc2 hDef hRTil hC00
  dsimp only [ptsX]
  ring

/-! ### Named inputs and the reduction -/

/-- **Named input: `r̃` is relatively small** (`c_r‖M_j‖ǧ_j` against the vertex `β_{a,k}`), above
coalescence and at the last step. -/
def PairRTilRel (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
      ‖hRTil R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) k‖ ≤
        cr * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
          ‖hBeta R m b μ₀ x k‖) ∧
    ‖rTilN R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      cr * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖

/-- **Named input: the absolute vertex sum above coalescence** is `O(M_j)`. -/
def PairVertSum (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (cs : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ‖hC00 R m b μ₀ k‖ * ‖hBeta R m b μ₀ x k‖ +
        ‖lC R Nh m b μ₀ 0 0‖ * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ≤
      cs * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖

/-- **Named input: the defects and remainders above coalescence** are `O(M_j²ǧ_j)` in total. -/
def PairDefSum (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (cd : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ‖hDef R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) k‖ +
        ‖lastDef R Nh m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      cd * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- Pure assembly of the `PairCstRel` bound. -/
theorem pairCst_pure {ι : Type*} (s : Finset ι) (c r d β : ι → ℂ) (cN rN dN βN : ℂ)
    {cr cs cd M g : ℝ} (hcr : 0 ≤ cr) (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hr : ∀ k ∈ s, ‖r k‖ ≤ cr * M * g * ‖β k‖) (hrN : ‖rN‖ ≤ cr * M * g * ‖βN‖)
    (hs : ∑ k ∈ s, ‖c k‖ * ‖β k‖ + ‖cN‖ * ‖βN‖ ≤ cs * M)
    (hd : ∑ k ∈ s, ‖d k‖ + ‖dN‖ ≤ cd * M ^ 2 * g) :
    ‖∑ k ∈ s, (-(c k * r k) + d k) + (-(cN * rN) + dN)‖ ≤ (cr * cs + cd) * M ^ 2 * g := by
  have hA : 0 ≤ cr * M * g := mul_nonneg (mul_nonneg hcr hM) hg
  have h1 : ∀ k ∈ s, ‖-(c k * r k) + d k‖ ≤ cr * M * g * (‖c k‖ * ‖β k‖) + ‖d k‖ := by
    intro k hk
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_neg, norm_mul]
    calc ‖c k‖ * ‖r k‖ ≤ ‖c k‖ * (cr * M * g * ‖β k‖) :=
          mul_le_mul_of_nonneg_left (hr k hk) (norm_nonneg _)
      _ = cr * M * g * (‖c k‖ * ‖β k‖) := by ring
  have h2 : ‖-(cN * rN) + dN‖ ≤ cr * M * g * (‖cN‖ * ‖βN‖) + ‖dN‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_neg, norm_mul]
    calc ‖cN‖ * ‖rN‖ ≤ ‖cN‖ * (cr * M * g * ‖βN‖) :=
          mul_le_mul_of_nonneg_left hrN (norm_nonneg _)
      _ = cr * M * g * (‖cN‖ * ‖βN‖) := by ring
  have h3 := (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (sum_le_sum h1)) h2)
  have e3 : ∑ i ∈ s, (cr * M * g * (‖c i‖ * ‖β i‖) + ‖d i‖) =
      cr * M * g * ∑ k ∈ s, ‖c k‖ * ‖β k‖ + ∑ k ∈ s, ‖d k‖ := by
    rw [sum_add_distrib, mul_sum]
  rw [e3] at h3
  have h4 : cr * M * g * (∑ k ∈ s, ‖c k‖ * ‖β k‖ + ‖cN‖ * ‖βN‖) ≤ cr * M * g * (cs * M) :=
    mul_le_mul_of_nonneg_left hs hA
  have e : (cr * cs + cd) * M ^ 2 * g = cr * M * g * (cs * M) + cd * M ^ 2 * g := by ring
  rw [e]
  have e2 : cr * M * g * ∑ k ∈ s, ‖c k‖ * ‖β k‖ + ∑ k ∈ s, ‖d k‖ +
      (cr * M * g * (‖cN‖ * ‖βN‖) + ‖dN‖) =
      cr * M * g * (∑ k ∈ s, ‖c k‖ * ‖β k‖ + ‖cN‖ * ‖βN‖) + (∑ k ∈ s, ‖d k‖ + ‖dN‖) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **`PairCstRel` from the step decomposition** (trajectory level): `PairRTilRel c_r`,
`PairVertSum c_s`, `PairDefSum c_d` give `PairCstRel (c_rc_s + c_d)`. -/
theorem pairCstRel_of_parts (hP : R.P = Pc) {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ)
    {cr cs cd : ℝ} (hcr : 0 ≤ cr)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hR : PairRTilRel R Nh m b μ₀ lam cr) (hS : PairVertSum R Nh m b μ₀ lam cs)
    (hD : PairDefSum R Nh m b μ₀ lam cd) :
    PairCstRel R Nh m b μ₀ lam (cr * cs + cd) := by
  intro x hx h1 hj
  obtain ⟨hX, -, -, -⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  rw [nAB_zCst_sum R hP Nh m b μ₀ x h1 (by omega) hX (lC_diag R hV hVL hVN b μ₀ x)]
  obtain ⟨hr, hrN⟩ := hR x hx h1 hj
  exact pairCst_pure _ _ _ _ _ _ _ _ _ hcr (norm_nonneg _) (hg _ hj) hr hrN (hS x hx h1 hj)
    (hD x hx h1 hj)

/-! ### `PairRTilRel` from the sources of the `r̃` flow -/

theorem prod_one_add_le_exp {ι : Type*} (s : Finset ι) (ε : ι → ℝ) (h : ∀ i ∈ s, 0 ≤ ε i) :
    ∏ i ∈ s, (1 + ε i) ≤ Real.exp (∑ i ∈ s, ε i) := by
  rw [Real.exp_sum]
  refine prod_le_prod (fun i hi => by linarith [h i hi]) fun i _ => ?_
  have := Real.add_one_le_exp (ε i); linarith

/-- The last-step `r̃` is the history `r̃` at `N_h + 1` (only the observable components enter). -/
theorem rTilN_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (j : ℕ) :
    rTilN R Nh m b μ₀ x j = hRTil R m b μ₀ x j (Nh + 1) ∧
      Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) = hBeta R m b μ₀ x (Nh + 1) := by
  have e1 : Obs2.rAB2 (Nh + 1) (lV R Nh m b μ₀ x) = Obs2.rAB2 (Nh + 1)
      (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) := by
    unfold Obs2.rAB2; simp only [lV_ab]
  have e2 : Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) = hBeta R m b μ₀ x (Nh + 1) := by
    unfold hBeta Obs2.betaTot2; simp only [lV_a]
  have e3 : Obs2.betaB2 (Nh + 1) (lV R Nh m b μ₀ x) = Obs2.betaB2 (Nh + 1)
      (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) := by
    unfold Obs2.betaB2; simp only [lV_b]
  refine ⟨?_, e2⟩
  unfold rTilN hRTil Obs2.rTil2
  rw [e1, e2, e3]
  rfl

/-- **Named input: the sources of the `r̃` flow** (`σ_{j,k}`, `rSrc2`) and the `K`, `𝒲` parts
`e_{a,k}` of the `β_a` flow are small relative to the vertex `β_{a,k+1}`, for `j ≤ k ≤ N_h`:
`‖σ_k‖ ≤ s_k‖β_{a,k+1}‖`, `‖e_{a,k}‖ ≤ ε_k‖β_{a,k+1}‖`, `∑s_k ≤ c_σ‖M_j‖ǧ_j`, `∑ε_k ≤ c_ε`. -/
def PairSrcRel (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (cσ cε : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ s ε : ℕ → ℝ, (∀ k, 0 ≤ s k) ∧ (∀ k, 0 ≤ ε k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        hBeta R m b μ₀ x (k + 1) ≠ 0 ∧
        ‖Obs2.rSrc2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs.coal L (0 : Lam 2 L N) x) k‖ ≤
          s k * ‖hBeta R m b μ₀ x (k + 1)‖ ∧
        ‖Obs2.eA2h (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k‖ ≤ ε k * ‖hBeta R m b μ₀ x (k + 1)‖) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), s k ≤
        cσ * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ε k ≤ cε

/-- **`PairRTilRel` from the sources** (discrete Gronwall, `Obs2.rTil2_rel_bound`):
`PairSrcRel c_σ c_ε` gives `PairRTilRel (c_σe^{c_ε})`. -/
theorem pairRTilRel_of_src (hP : R.P = Pc) {Nh : ℕ} (m : ℝ)
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ) (lam : ℕ → ℂ) {cσ cε : ℝ} (hcσ : 0 ≤ cσ)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hS : PairSrcRel R Nh m b μ₀ lam cσ cε) :
    PairRTilRel R Nh m b μ₀ lam (cσ * Real.exp cε) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  obtain ⟨s, ε, hs0, hε0, hk, hsum, hεsum⟩ := hS x hx h1 hj
  rw [← hjd] at hk hsum hεsum
  have hcoal := Obs2.obsHist_coal_valid (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (Obs2.coalInv_init .two (zV_abFree b) (ptsX x)) hL
    hVL.2.2.2.2.1 (fun k hk => hV k (by
      have : Obs.coal L (ptsX x).a (ptsX x).b = Obs.coal L (0 : Lam 2 L N) x := rfl
      omega)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have hC : ∀ k, Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
      (ptsX x).b (ptsX x).b = Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
        k (ptsX x).a (ptsX x).a := fun k => by
    rw [histCov_gamInt_at R hP, histCov_gamInt_at R hP]
  have hG := Obs2.rTil2_rel_bound (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs2.obsInit_two_form _ _)
    (Obs2.obsInit_two_form_b _ _) (j := j) (m := Nh + 1) h1 hC ((hcoal j le_rfl).1) s ε hs0 hε0
    (fun k hk1 hk2 => (hk k (mem_Ico.2 ⟨hk1, hk2⟩)).1)
    (fun k hk1 hk2 => (hk k (mem_Ico.2 ⟨hk1, hk2⟩)).2.1)
    (fun k hk1 hk2 => (hk k (mem_Ico.2 ⟨hk1, hk2⟩)).2.2)
  have hMg : 0 ≤ ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 :=
    mul_nonneg (norm_nonneg _) (hg j hj)
  have bnd : ∀ k, j ≤ k → k ≤ Nh + 1 → ‖hRTil R m b μ₀ x j k‖ ≤
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
    have hS0 : 0 ≤ ∑ i ∈ Finset.Ico j k, s i := sum_nonneg fun i _ => hs0 i
    have := mul_le_mul hS1 hP1 hP0 (mul_nonneg (mul_nonneg hcσ (norm_nonneg _)) (hg j hj))
    have := mul_le_mul_of_nonneg_right this (norm_nonneg (hBeta R m b μ₀ x k))
    calc (∑ i ∈ Finset.Ico j k, s i) * (∏ i ∈ Finset.Ico j k, (1 + ε i)) *
          ‖Obs2.betaTot2 k (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖
        ≤ cσ * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 *
            Real.exp cε * ‖hBeta R m b μ₀ x k‖ := this
      _ = _ := by ring
  refine ⟨fun k hk => bnd k (mem_Ico.1 hk).1 (mem_Ico.1 hk).2.le, ?_⟩
  obtain ⟨e1, e2⟩ := rTilN_eq R Nh m b μ₀ x j
  rw [e1, e2]
  exact bnd (Nh + 1) (by omega) le_rfl

end Traj

end

end Spin2
