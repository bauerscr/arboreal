import Spin2.Restart.RestartPairChain9
import Spin2.Pair.PairErrAB

set_option autoImplicit false

/-!
# T5, item (5)(iii), task 2: the reduced pair constants `n_{ab}X'` from the sizes

**`rpc10_cst_bd`** (trajectory level): for the reduced chain of a general state `o` at
`1 ≤ j_x ≤ N_h`, from

* `GoodCov2 k s_k C_k` (`k ≤ N_h`) and `GoodCov2 (N_h+1) s_{N_h+1} C_N` (so `|C_k(0,0)| ≤ s_k²`),
* the per-block masses `|m₂(V_n(B)_{ab})|·s_n² ≤ A` (`j_x < n ≤ N_h + 1`),
* the per-step defects `|−𝔡_k + X_k| ≤ D` (`j_x ≤ k ≤ N_h`), and `|lastDefR| ≤ E`,

`|n_{ab}X'| ≤ (N_h + 1 − j_x)(2A + D) + L²A + E` (`rpc_cst_le`; `r'_k` has at most two
non-zero blocks by anchoring, `r'_{j_x} = 0`, `r'_N` at most `L²` blocks; `hDefR_eq`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 4000000 in
/-- **`|n_{ab}X'|` of the reduced chain from its per-block masses and per-step defects.** -/
theorem rpc10_cst_bd (hP : R.P = Pc) {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hl : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o)
    (hs : ∀ n, 0 < histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hGC : ∀ k ≤ Nh, GoodCov2 k (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k))
    (hGCN : GoodCov2 (Nh + 1)
      (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (lC R Nh m b μ₀))
    {A D E : ℝ} (hA : 0 ≤ A)
    (hmass : ∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 → ∀ c : Fin 2 → ℕ,
      ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (rpcRed R m b μ₀ x o) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c :
          SA .two (Lam 2 L N)).ab‖ *
        (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) *
          histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ≤ A)
    (hdef : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k ≤ Nh →
      ‖-pdefAB2 (ptsX x) k (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) +
        xAB2 (ptsX x) k (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (rpcRed R m b μ₀ x o)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ D)
    (hlast : ‖lastDefR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x‖ ≤ E) :
    ‖PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ ≤
      ((Nh + 1 - Obs.coal L (0 : Lam 2 L N) x : ℕ) : ℝ) * (2 * A + D) +
        ((L : ℝ) ^ 2 * A + E) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set o' := rpcRed R m b μ₀ x o with ho'd
  have hanc : ObsAnchInv (ptsX x) j o' :=
    PtCorr2.obsAnchInv_redSt (R.withMsq m) (ptsX x) _ _ (pairDCov_std Nh x hx h1 hj)
  have hT := (rpc_cst_le R hP hN m hρ1 hspl hm0 hm hV hVL hVN hL hb hh x hx h1 hj o ho hl).2
  refine hT.trans (add_le_add ?_ ?_)
  · -- the steps `j_x ≤ k ≤ N_h`
    have hk : ∀ k ∈ Finset.Ico j (Nh + 1), ‖hC00 R m b μ₀ k‖ *
        ‖hRR R m b μ₀ (fun _ => o') x k‖ + ‖hDefR R m b μ₀ (fun _ => o') x k‖ ≤ 2 * A + D := by
      intro k hk'
      have hjk := (Finset.mem_Ico.1 hk').1
      have hkN : k ≤ Nh := by have := (Finset.mem_Ico.1 hk').2; omega
      have hsk := hs k
      -- the defect
      have hD : ‖hDefR R m b μ₀ (fun _ => o') x k‖ ≤ D := by
        rw [hDefR_eq R m b μ₀ (fun _ => o') x (oanchS_hR (R.withMsq m) (ptsX x) hanc t hjk).toAb]
        exact hdef k hjk hkN
      -- `r'_k`
      have hC : ‖hC00 R m b μ₀ k‖ ≤ histS (R.withMsq m) k t ^ 2 := Obs2.good_entry (hGC k hkN) 0 0
      have hR : ‖hRR R m b μ₀ (fun _ => o') x k‖ * (histS (R.withMsq m) k t *
          histS (R.withMsq m) k t) ≤ 2 * A := by
        have e : hRR R m b μ₀ (fun _ => o') x k = ∑ c ∈ blockIdx (L := L) (N := N) k,
            LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) j o' k t).V c :
              SA .two (Lam 2 L N)).ab := by
          show rAB2 k (hVR (R.withMsq m) (ptsX x) j o' t k) = _
          unfold rAB2
          exact sum_congr rfl fun c _ => by rw [hVR_ab]
        rcases eq_or_lt_of_le hjk with hkj | hkj
        · subst hkj
          have : hRR R m b μ₀ (fun _ => o') x j = 0 := by
            rw [e]
            refine sum_eq_zero fun c _ => ?_
            rw [obsHistFrom_self]
            show LocObs.mass2 ((0 : Obs2.OFam .two 2 L N) c : SA .two (Lam 2 L N)).ab = 0
            simp only [Pi.zero_apply, ZeroMemClass.coe_zero]
            exact Obs.mass2_zero
          rw [this, norm_zero, zero_mul]; linarith
        · have hss : 0 < histS (R.withMsq m) k t * histS (R.withMsq m) k t := mul_pos hsk hsk
          have hb2 : ‖hRR R m b μ₀ (fun _ => o') x k‖ ≤
              2 * (A / (histS (R.withMsq m) k t * histS (R.withMsq m) k t)) := by
            rw [e]
            refine norm_sum_two_le _ _ (blk k (ptsX x).a) (blk k (ptsX x).b) (by positivity)
              (fun c _ h1 h2 => by
                rw [← hVR_ab, hVR_ab_anch (R.withMsq m) (ptsX x) j o' t hanc hjk c h1 h2]
                exact Obs.mass2_zero) fun c _ => ?_
            rw [le_div_iff₀ hss]; exact hmass k hkj (by omega) c
          calc ‖hRR R m b μ₀ (fun _ => o') x k‖ * (histS (R.withMsq m) k t *
                histS (R.withMsq m) k t)
              ≤ 2 * (A / (histS (R.withMsq m) k t * histS (R.withMsq m) k t)) *
                (histS (R.withMsq m) k t * histS (R.withMsq m) k t) :=
                mul_le_mul_of_nonneg_right hb2 hss.le
            _ = 2 * A := by field_simp
      have hCR : ‖hC00 R m b μ₀ k‖ * ‖hRR R m b μ₀ (fun _ => o') x k‖ ≤ 2 * A := by
        calc ‖hC00 R m b μ₀ k‖ * ‖hRR R m b μ₀ (fun _ => o') x k‖
            ≤ histS (R.withMsq m) k t ^ 2 * ‖hRR R m b μ₀ (fun _ => o') x k‖ :=
              mul_le_mul_of_nonneg_right hC (norm_nonneg _)
          _ = ‖hRR R m b μ₀ (fun _ => o') x k‖ * (histS (R.withMsq m) k t *
              histS (R.withMsq m) k t) := by ring
          _ ≤ 2 * A := hR
      linarith
    refine (sum_le_sum hk).trans (le_of_eq ?_)
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
  · -- the last step
    have hsN := hs (Nh + 1)
    have hssN : 0 < histS (R.withMsq m) (Nh + 1) t * histS (R.withMsq m) (Nh + 1) t :=
      mul_pos hsN hsN
    have hC : ‖lC R Nh m b μ₀ 0 0‖ ≤ histS (R.withMsq m) (Nh + 1) t ^ 2 := Obs2.good_entry hGCN 0 0
    have hR : ‖rRN R Nh m b μ₀ (fun _ => o') x‖ ≤
        (L : ℝ) ^ 2 * (A / (histS (R.withMsq m) (Nh + 1) t * histS (R.withMsq m) (Nh + 1) t)) := by
      unfold rRN rAB2
      have hn : ((blockIdx (d := 2) (L := L) (N := N) (Nh + 1)).card : ℝ) ≤ (L : ℝ) ^ 2 := by
        exact_mod_cast Step2.LastN.card_blockIdx_last (d := 2) (L := L) (N := N)
          (show Nh + 1 + 1 = N by omega)
      have hb1 : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
          ‖LocObs.mass2 (lVR R Nh m b μ₀ (fun _ => o') x c : SA .two (Lam 2 L N)).ab‖ ≤
            A / (histS (R.withMsq m) (Nh + 1) t * histS (R.withMsq m) (Nh + 1) t) := by
        intro c _
        have e : (lVR R Nh m b μ₀ (fun _ => o') x c : SA .two (Lam 2 L N)).ab =
            ((obsHistFrom (R.withMsq m) (ptsX x) j o' (Nh + 1) t).V c : SA .two (Lam 2 L N)).ab :=
          emb_add_ab _ _
        rw [e, le_div_iff₀ hssN]; exact hmass (Nh + 1) (by omega) le_rfl c
      refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ hb1).trans ?_)
      rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn (by positivity)
    have hCR : ‖lC R Nh m b μ₀ 0 0‖ * ‖rRN R Nh m b μ₀ (fun _ => o') x‖ ≤ (L : ℝ) ^ 2 * A := by
      calc ‖lC R Nh m b μ₀ 0 0‖ * ‖rRN R Nh m b μ₀ (fun _ => o') x‖
          ≤ histS (R.withMsq m) (Nh + 1) t ^ 2 *
            ((L : ℝ) ^ 2 * (A / (histS (R.withMsq m) (Nh + 1) t *
              histS (R.withMsq m) (Nh + 1) t))) :=
            mul_le_mul hC hR (norm_nonneg _) (by positivity)
        _ = (L : ℝ) ^ 2 * A := by field_simp
    exact add_le_add hCR hlast

end Traj

end

end Spin2
