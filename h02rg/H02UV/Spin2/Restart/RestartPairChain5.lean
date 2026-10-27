import Spin2.Restart.RestartPairChain4

/-!
# T5, item (5)(iii)(b) and wiring: the reduced pair constants and the `b`-side coupling at `j_x`

Pair `(0, x)`, `1 ≤ j_x ≤ N_h`, a general observable local state `o` at `j_x`,
`oG = fun _ => rpcRed o`.

* **`rpc_cst_le`** (exact decomposition, `nAB_zCstR_sum` for the reduced state of a general `o`):
  `|n_{ab}X'| ≤ ∑_{j_x≤k≤N_h}(|C_k(0,0)||r'_k| + |d'_k|) + |C_N(0,0)||r'_N| + |d'_N|`,
  `r'_k = ∑_Bm₂(V_k(B)_{ab})` (`hRR`), `d'_k = -𝔡_k + X_k` (`hDefR`, `hDefR_eq`), `d'_N = lastDefR`
  — no vertex term, no `γ`-cross terms (the reduced chain has no one-point parts). Every term is
  linear in the reduced chain, hence in the seed.
* **`rpc_uB_le`**: `|γ_{x,j_x}| = |uB j_x| ≤ (1 + K_Mǧ_{j_x})‖M_{j_x}‖` from `ZBelowU1 K_M`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 2000000 in
/-- **The reduced pair constants of a general state** (exact decomposition and triangle bound). -/
theorem rpc_cst_le (hP : R.P = Pc) {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hl : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o) :
    PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x) =
        ∑ k ∈ Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (-(hC00 R m b μ₀ k * hRR R m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x k) +
            hDefR R m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x k) +
        (-(lC R Nh m b μ₀ 0 0 * rRN R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x) +
          lastDefR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x) ∧
    ‖PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ ≤
      ∑ k ∈ Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (‖hC00 R m b μ₀ k‖ * ‖hRR R m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x k‖ +
            ‖hDefR R m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x k‖) +
        (‖lC R Nh m b μ₀ 0 0‖ * ‖rRN R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x‖ +
          ‖lastDefR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x‖) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  -- `sE ≠ 0` from the reference
  obtain ⟨hX, hΩ, -, -⟩ := pair_E_split R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
  have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
    (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
  have e : zOm R m b μ₀ x j = zCst R Nh m b μ₀ x j * zZm R Nh m b μ₀ x :=
    hw.trans (zHi_eq R Nh m b μ₀ x)
  have hY0 : PtCorr2.sE (zOm R m b μ₀ x j) ≠ 0 := by
    rw [e, PtCorr2.sE_mul]; exact mul_ne_zero hX hΩ
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
  obtain ⟨-, hsplit⟩ := PtCorr2.rpc_pair_red_gen (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm hV hVL
    b μ₀ hj o ho hl (pairDCov_std Nh x hx h1 hj)
  obtain ⟨hX', -, -⟩ := hsplit hYo
  -- the exact decomposition
  have hab : PtCorr2.ObsAbInv j (rpcRed R m b μ₀ x o) := PtCorr2.rpcRedSt_abInv _ _ _ _ _ _
  have hseed : ∑ B ∈ blockIdx (L := L) (N := N) j,
      ε (PtCorr2.hVR (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) t j B :
        Obs.SA .two (Lam 2 L N)).ab = 0 := by
    refine sum_eq_zero fun B _ => ?_
    rw [PtCorr2.hVR_ab, PtCorr2.obsHistFrom_self]
    show ε ((0 : Obs2.OFam .two 2 L N) B : Obs.SA .two (Lam 2 L N)).ab = 0
    simp
  have hEq := nAB_zCstR_sum R hP Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x hj hab hseed hX'
    (lC_diag R hV hVL hVN b μ₀ x)
  refine ⟨hEq, ?_⟩
  rw [hEq]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)) ?_)
  · refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) le_rfl)
    rw [norm_neg, norm_mul]
  · refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) le_rfl)
    rw [norm_neg, norm_mul]

/-- **The `b`-side coupling at the coalescence scale** from `ZBelowU1`:
`|γ_{x,j_x}| ≤ (1 + K_Mǧ_{j_x})‖M_{j_x}‖`. -/
theorem rpc_uB_le {Nh : ℕ} {m b μ₀ : ℝ} {lam : ℕ → ℂ} {KM : ℝ}
    (hZ : ZBelowU1 R Nh m b μ₀ lam KM) (x : Lam 2 L N) (hx : x ≠ 0)
    (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    ‖uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      (1 + KM * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1) *
        ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ := by
  have h := (hZ x hx h1 hj).2
  have h2 := norm_le_norm_sub_add (uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x))
    (Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x))
  nlinarith

end Traj

end

end Spin2
