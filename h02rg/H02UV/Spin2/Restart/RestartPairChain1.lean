import Spin2.Restart.RestartPairTop1
import PtCorr2.Restart.RestartPairChain1

/-!
# T5, item (5): the two-point output of a general state at the coalescence scale `j_x ≤ N_h`

Pair `(0, x)` with `1 ≤ j_x ≤ N_h`, the `h = 0` trajectory. For an **arbitrary** observable state
`o` at scale `j_x` (local at `j_x`; e.g. the restarted history of a small `a`-side datum,
`PtCorr2.obsHistFrom … m δ j_x`):

* **`rpcZ`** `= ω_{Γ_{j_x}}Z_{j_x}(o)`, **`rpcE`** `= n_{ab}(rpcZ)`, **`rpcOut`**
  `= rpTopU o·γ_{x,j_x} − rpcE o` (the two-point output at the coalescence scale; the `b`-side is the
  reference `γ_{x,j_x} = uB j_x`).
* **`rpcOut_ref`**: on the reference state (the history of the pair observable at `j_x`) the output
  is the two-point function `b⟨ψ̄_0ψ_x⟩` (`h = 0`).
* **`rpc_out_split`** (exact, any observable local `o`): with `o' = rpcRed o` (the reduced state at
  `j_x`, covering polymer `dxStd x`), `o'' = rpcTail o` (the reduced chain at `N_h + 1`) and
  `rpcQ o = n_{ab}(∏_{j_x ≤ i ≤ N_h} chOF_i)` (the accumulated pair constants of the reduced chain),
  `rpcOut o = rpTopU o·γ_{x,j_x} − rpcQ o + rpTopOut o''`
  (`rpTopU o'' = 0`: the reduced chain has no one-point parts). So the coalescence case
  `j_x ≤ N_h` is the top output (`Spin2/Restart/RestartPairTop2`, `rp_top_traj`) of the reduced chain
  at `N_h + 1` plus the accumulated pair constants above `j_x`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `ω_{Γ_{j_x}}Z_{j_x}(o)` for a general state `o` at the coalescence scale. -/
def rpcZ (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) : Obs.OE .two (Lam 2 L N) :=
  PtCorr2.omegaCO (PtCorr2.Γh (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (PtCorr2.ZhOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o
      (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- **The pair part at the coalescence scale of a general state**: `n_{ab}(ω_{Γ_{j_x}}Z_{j_x}(o))`. -/
def rpcE (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) : ℂ :=
  PtCorr2.nAB (rpcZ R m b μ₀ x o)

/-- **The two-point output of a state `o` at the coalescence scale `j_x`** (`h = 0`):
`rpTopU o·γ_{x,j_x} − rpcE o`. -/
def rpcOut (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) : ℂ :=
  rpTopU o * uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) - rpcE R m b μ₀ x o

/-- The reference state at `j_x`: the history of the pair observable. -/
def rpcRef (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs2.ObsSt .two L N :=
  Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- The reduced state of `o` at `j_x` (covering polymer `dxStd x`). -/
def rpcRed (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) : Obs2.ObsSt .two L N :=
  PtCorr2.rpcRedSt (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o (dxStd x)

/-- The reduced chain of `o` at `N_h + 1`. -/
def rpcTail (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) :
    Obs2.ObsSt .two L N :=
  PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
    (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- The accumulated pair constants of the reduced chain, `n_{ab}(∏_{j_x ≤ i ≤ N_h} chOF_i)`. -/
def rpcQ (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (o : Obs2.ObsSt .two L N) : ℂ :=
  PtCorr2.nAB (∏ i ∈ Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
    PtCorr2.chOF (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o) i
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

theorem rpcZ_ref (m b μ₀ : ℝ) (x : Lam 2 L N) :
    rpcZ R m b μ₀ x (rpcRef R m b μ₀ x) = zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := by
  unfold rpcZ zOm rpcRef
  rw [← PtCorr2.rpc_ZhO_eq]

/-- The reduced chain has no accumulated `a`-constant: `rpTopU o'' = 0`. -/
theorem rpcTail_U (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh + 1)
    (o : Obs2.ObsSt .two L N) : rpTopU (rpcTail R Nh m b μ₀ x o) = 0 := by
  have h := PtCorr2.rpc_tail_ua (R.withMsq m) (ptsX x)
    (PtCorr2.rpcRedSt_abInv (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o (dxStd x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hj
  unfold rpTopU rpcTail rpcRed
  rw [h, map_zero, neg_zero]

set_option maxHeartbeats 1000000 in
/-- **The output on the reference state is the two-point function** (`j_x ≤ N_h`, `h = 0`). -/
theorem rpcOut_ref {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh0 : b = μ₀ + m) (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) =
      rpcOut R m b μ₀ x (rpcRef R m b μ₀ x) := by
  obtain ⟨p, r, hp0, hpr, -, hr, hP⟩ :=
    twopt_zz_eq R hN m hρ1 hspl hm0 hm hV hVL hL hb (le_of_eq hh0) x hj
  have hr0 : (r : ℂ) = 0 := by
    rw [← hr, PtCorr2.onept_avg0_h0 hb hm0 hh0, mul_one_div_cancel
      (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]
  have hr0' : r = 0 := by exact_mod_cast hr0
  have hp : (p : ℂ) = 0 := by
    have : p = 0 := le_antisymm (hr0' ▸ hpr) hp0
    rw [this, Complex.ofReal_zero]
  obtain ⟨hX0, -⟩ := PtCorr2.zz_square_split (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm
    hV hVL hL hj hb (le_of_eq hh0) (zV b) (zV_abFree b)
  obtain ⟨ea, eb⟩ := PtCorr2.prodLo_sA_sB (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) rfl (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
    (Obs.coal L (0 : Lam 2 L N) x)
  have hX0' : PtCorr2.sE (zLo R m b μ₀ x) ≠ 0 := hX0
  have ha : PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) =
      uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := by
    have ea' : PtCorr2.sA (zLo R m b μ₀ x) =
        PtCorr2.sE (zLo R m b μ₀ x) * uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := ea
    rw [ea', mul_div_cancel_left₀ _ hX0']
  have hb' : PtCorr2.sB (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) =
      uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := by
    have eb' : PtCorr2.sB (zLo R m b μ₀ x) =
        PtCorr2.sE (zLo R m b μ₀ x) * uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := eb
    rw [eb', mul_div_cancel_left₀ _ hX0']
  have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
  have e : zHi R Nh m b μ₀ x = zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) := hw.symm
  rw [hP, hr0, hp, ha, hb', e]
  unfold rpcOut rpcE
  rw [rpcZ_ref]
  have hu : uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) = rpTopU (rpcRef R m b μ₀ x) := rfl
  rw [hu]
  unfold PtCorr2.nAB
  ring

set_option maxHeartbeats 2000000 in
/-- **The output of a general state at `j_x ≤ N_h` through the reduced chain** (exact): for an
observable state `o` at `j_x`, local at `j_x`,
`rpcOut o = rpTopU o·γ_{x,j_x} − rpcQ o + rpTopOut (rpcTail o)`. -/
theorem rpc_out_split {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hl : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o) :
    rpcOut R m b μ₀ x o = rpTopU o * uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) -
      rpcQ R Nh m b μ₀ x o + rpTopOut R Nh m b μ₀ x (rpcTail R Nh m b μ₀ x o) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  -- the reference normalisation is nonzero
  obtain ⟨hX, hΩ, -, -⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
  have e : zOm R m b μ₀ x j = zCst R Nh m b μ₀ x j * zZm R Nh m b μ₀ x :=
    hw.trans (zHi_eq R Nh m b μ₀ x)
  have hY0 : PtCorr2.sE (zOm R m b μ₀ x j) ≠ 0 := by
    rw [e, PtCorr2.sE_mul]; exact mul_ne_zero hX hΩ
  -- the reference state is observable and local at `j`
  have hcore : ∀ i ≤ Nh, ValidCore (R.withMsq m) i := fun i hi => by
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · rw [show i = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU (R.withMsq m) hV hVL t
  have hoR : (rpcRef R m b μ₀ x).IsObs :=
    Obs2.obsHist_isObs (R.withMsq m) (ptsX x) _ (Obs2.obsInit_isObs .two (zV b) (ptsX x)) j t
  have hlR : PtCorr2.ObsLocInv (ptsX x) j (rpcRef R m b μ₀ x) :=
    PtCorr2.obsLocInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsLocInv_init .two (zV b) (ptsX x))
      t j fun i hi => ⟨hcore i (by omega), hRI i (by omega)⟩
  have hYo : PtCorr2.sE (rpcZ R m b μ₀ x o) ≠ 0 := by
    have hi := PtCorr2.rpc_sE_indep (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm hV hVL b μ₀ hj
      ho hl hoR hlR
    have hi' : PtCorr2.sE (rpcZ R m b μ₀ x o) = PtCorr2.sE (rpcZ R m b μ₀ x (rpcRef R m b μ₀ x)) :=
      hi
    rw [hi', rpcZ_ref]; exact hY0
  -- the split through the reduced chain
  obtain ⟨-, hsplit⟩ := PtCorr2.rpc_pair_red_tail (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm hV hVL
    b μ₀ hj o ho hl (pairDCov_std Nh x hx h1 hj)
  have hE := hsplit hYo
  have hU := rpcTail_U R Nh m b μ₀ x (by omega) o
  unfold rpcOut rpcE rpcQ rpTopOut rpTopE
  rw [hU]
  have hE' : PtCorr2.nAB (rpcZ R m b μ₀ x o) =
      PtCorr2.nAB (∏ i ∈ Ico j (Nh + 1),
        PtCorr2.chOF (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) i t) +
      PtCorr2.nAB (PtCorr2.lastOF (R.withMsq m) (ptsX x) (Nh + 1) (rpcTail R Nh m b μ₀ x o) Nh t) :=
    hE
  rw [hE']
  ring

end Traj

end

end Spin2
