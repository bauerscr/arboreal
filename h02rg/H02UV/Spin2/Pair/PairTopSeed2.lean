import Spin2.Pair.PairTopSeed1

/-!
# Top coalescence: the one-point sizes at `N - 1` in the weights `wM(M_a, M_b)` of the seed

`M_a = pM (0,x) N_h = 2s_{N_h}²|β_{a,N_h}|`, `M_b = pM (x,0) N_h`. From the master conclusions at
`N_h + 1` (`LastL1Concl`: `∑_B|m₂V_{N_h+1}(B)_a| ≤ 3|β_{N_h+1}|`; `LastObsConclK`:
`‖K^{obs}_{N_h+1}‖_{w_a} ≤ c_Kǧs_{N_h}²|β_{N_h}|`), `Case2TopStep` (`|β_{N_h+1}| ≤ (81/64)|β_{N_h}|`),
`s_{N_h+1} ≤ (9/8)s_{N_h}`, the mirror and `V^{obs}_{N_h+1,ab} = 0` (`obsHist_coal_validL`):

* **`topOne_conv`**: `‖V^{obs}_{N_h+1}(B)‖_{wM} ≤ 3(81/64)²`,
  `A^{(|𝓑(X)|-4)_+}‖K^{obs}_{N_h+1}(X)‖_{wM1} ≤ c_Kǧ_{N_h}` (the inputs `v_T`, `k_{xT}` of
  `topSeed_traj`).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `pM = 2s_k²|β_k|` for the `zV b` vertex (`k ≥ 1`; generic history). -/
theorem pM_eq_bt2G (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R))
    (ht0 : (t 0).2.2 = 0) (b : ℝ) (P : ObsPts 2 L N) {k : ℕ} (hk : 1 ≤ k) :
    pM R P (zV0 b) t k = 2 * histS R k t ^ 2 *
      ‖betaTot2 (L := L) (N := N) k (histVO2 R P (obsInit .two (zV b) P) t k)‖ := by
  unfold pM histVO2 fullV
  rw [(obsHist_zV0 R P t b ht0 k hk).1]

/-- The `σ_b` parts at `(0, x)` are the `σ_a` parts at `(x, 0)` (`zV b`, `j ≥ 1`; generic). -/
theorem mirror_zV_cmpG (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R))
    (ht0 : (t 0).2.2 = 0) (b : ℝ) (x : Lam 2 L N) {j : ℕ} (hj : 1 ≤ j) :
    (∀ q, ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) j t).V q : SA .two (Lam 2 L N)).b =
      ((obsHist R (ptsS x) (obsInit .two (zV b) (ptsS x)) j t).V q : SA .two (Lam 2 L N)).a) ∧
    (∀ X, ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) j t).K X : SA .two (Lam 2 L N)).b =
      ((obsHist R (ptsS x) (obsInit .two (zV b) (ptsS x)) j t).K X : SA .two (Lam 2 L N)).a) := by
  have hX := obsHist_zV0 R (ptsX x) t b ht0 j hj
  have hS := obsHist_zV0 R (ptsS x) t b ht0 j hj
  have hc := prjSt_eq_cmp (mirror_b_eq R t b x j)
  refine ⟨fun q => ?_, fun X => ?_⟩
  · rw [hX.1, hS.1]; exact hc.1 q
  · rw [hX.2.2, hS.2.2]; exact hc.2.2 X

set_option maxHeartbeats 4000000 in
/-- **The one-point sizes at `N_h + 1` in the seed weights** (generic history). -/
theorem topOne_conv (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R))
    (ht0 : (t 0).2.2 = 0) {Nh : ℕ} (hNh1 : 1 ≤ Nh) (b : ℝ)
    (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (x : Lam 2 L N) {cK : ℝ}
    (hcK : 0 ≤ cK) (hg0 : 0 ≤ (t Nh).1)
    (hβX : ‖betaTot2 (L := L) (N := N) (Nh + 1)
        (histVO2 R (ptsX x) (obsInit .two (zV b) (ptsX x)) t (Nh + 1))‖ ≤
      81 / 64 * ‖betaTot2 (L := L) (N := N) Nh
        (histVO2 R (ptsX x) (obsInit .two (zV b) (ptsX x)) t Nh)‖)
    (hβS : ‖betaTot2 (L := L) (N := N) (Nh + 1)
        (histVO2 R (ptsS x) (obsInit .two (zV b) (ptsS x)) t (Nh + 1))‖ ≤
      81 / 64 * ‖betaTot2 (L := L) (N := N) Nh
        (histVO2 R (ptsS x) (obsInit .two (zV b) (ptsS x)) t Nh)‖)
    (hl1X : shA2 (histVO2 R (ptsX x) (obsInit .two (zV b) (ptsX x)) t) (Nh + 1) ≤
      3 * ‖betaTot2 (L := L) (N := N) (Nh + 1)
        (histVO2 R (ptsX x) (obsInit .two (zV b) (ptsX x)) t (Nh + 1))‖)
    (hl1S : shA2 (histVO2 R (ptsS x) (obsInit .two (zV b) (ptsS x)) t) (Nh + 1) ≤
      3 * ‖betaTot2 (L := L) (N := N) (Nh + 1)
        (histVO2 R (ptsS x) (obsInit .two (zV b) (ptsS x)) t (Nh + 1))‖)
    (hKX : KbHc R (ptsX x) (obsInit .two (zV b) (ptsX x)) t (Nh + 1)
      (cK * (t Nh).1 * histS R Nh t ^ 2 * ‖betaTot2 (L := L) (N := N) Nh
        (histVO2 R (ptsX x) (obsInit .two (zV b) (ptsX x)) t Nh)‖))
    (hKS : KbHc R (ptsS x) (obsInit .two (zV b) (ptsS x)) t (Nh + 1)
      (cK * (t Nh).1 * histS R Nh t ^ 2 * ‖betaTot2 (L := L) (N := N) Nh
        (histVO2 R (ptsS x) (obsInit .two (zV b) (ptsS x)) t Nh)‖))
    (hVab : ∀ q, ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).V q :
      SA .two (Lam 2 L N)).ab = 0)
    (hMa : 0 < pM R (ptsX x) (zV0 b) t Nh) (hMb : 0 < pM R (ptsS x) (zV0 b) t Nh) :
    (∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      oTo (wM (pM R (ptsX x) (zV0 b) t Nh) (pM R (ptsS x) (zV0 b) t Nh)) (Nh + 1)
        (histS R (Nh + 1) t)
        ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).V q) ≤
          ENNReal.ofReal (3 * (81 / 64) ^ 2)) ∧
    (∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      oTo (wM1 (pM R (ptsX x) (zV0 b) t Nh) (pM R (ptsS x) (zV0 b) t Nh)) (Nh + 1)
        (histS R (Nh + 1) t)
        ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X) ≤
      ENNReal.ofReal (cK * (t Nh).1)) := by
  have hs : 0 < histS R Nh t := histS_pos' R hρ0 hρ8 t Nh
  have hs1 : 0 < histS R (Nh + 1) t := histS_pos' R hρ0 hρ8 t (Nh + 1)
  have hss : histS R (Nh + 1) t ^ 2 ≤ 81 / 64 * histS R Nh t ^ 2 := by
    have h := histS_succ_le_q R hρ0 hρ8 t Nh
    have := pow_le_pow_left₀ hs1.le h 2
    nlinarith
  have hMaE := pM_eq_bt2G R t ht0 b (ptsX x) hNh1
  have hMbE := pM_eq_bt2G R t ht0 b (ptsS x) hNh1
  -- the `V` one-point bound for a point configuration `P`
  have hVP : ∀ P : ObsPts 2 L N,
      ‖betaTot2 (L := L) (N := N) (Nh + 1) (histVO2 R P (obsInit .two (zV b) P) t (Nh + 1))‖ ≤
        81 / 64 * ‖betaTot2 (L := L) (N := N) Nh (histVO2 R P (obsInit .two (zV b) P) t Nh)‖ →
      shA2 (histVO2 R P (obsInit .two (zV b) P) t) (Nh + 1) ≤
        3 * ‖betaTot2 (L := L) (N := N) (Nh + 1) (histVO2 R P (obsInit .two (zV b) P) t (Nh + 1))‖ →
      ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
        Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((obsHist R P (obsInit .two (zV b) P) (Nh + 1) t).V q : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (3 / 2 * (81 / 64) ^ 2 * (2 * histS R Nh t ^ 2 *
          ‖betaTot2 (L := L) (N := N) Nh (histVO2 R P (obsInit .two (zV b) P) t Nh)‖)) := by
    intro P hb1 hl q hq
    rw [← oTo_wA]
    refine (vobs2_block_le' R P (zV b) t ht0 (by omega) hs1 q hq).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ ‖betaTot2 (L := L) (N := N) Nh (histVO2 R P (obsInit .two (zV b) P) t Nh)‖ :=
      norm_nonneg _
    calc histS R (Nh + 1) t ^ 2 * shA2 (histVO2 R P (obsInit .two (zV b) P) t) (Nh + 1)
        ≤ (81 / 64 * histS R Nh t ^ 2) * (3 * (81 / 64 *
            ‖betaTot2 (L := L) (N := N) Nh (histVO2 R P (obsInit .two (zV b) P) t Nh)‖)) := by
          refine mul_le_mul hss (hl.trans ?_) (by unfold shA2; positivity) (by positivity)
          linarith
      _ = 3 / 2 * (81 / 64) ^ 2 * (2 * histS R Nh t ^ 2 *
          ‖betaTot2 (L := L) (N := N) Nh (histVO2 R P (obsInit .two (zV b) P) t Nh)‖) := by ring
  have hmir := mirror_zV_cmpG R t ht0 b x (j := Nh + 1) (by omega)
  refine ⟨fun q hq => ?_, fun X hX => ?_⟩
  · have ha := hVP (ptsX x) hβX hl1X q hq
    have hb := hVP (ptsS x) hβS hl1S q hq
    rw [← hmir.1 q] at hb
    rw [← hMaE] at ha
    rw [← hMbE] at hb
    refine (oTo_wM_le_of_ab hMa hMb (Nh + 1) _ _ (hVab q) (by positivity) (by positivity) ha
      hb).trans (le_of_eq (congrArg _ ?_))
    field_simp
    ring
  · have ha : ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
        Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X :
            SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal (cK * (t Nh).1 / 2 * pM R (ptsX x) (zV0 b) t Nh) := by
      have := hKX X hX
      rw [oTo_wA] at this
      refine this.trans (le_of_eq (congrArg _ ?_))
      rw [hMaE]; ring
    have hb : ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
        Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X :
            SA .two (Lam 2 L N)).b ≤ ENNReal.ofReal (cK * (t Nh).1 / 2 * pM R (ptsS x) (zV0 b) t Nh) := by
      have := hKS X hX
      rw [oTo_wA] at this
      rw [hmir.2 X]
      refine this.trans (le_of_eq (congrArg _ ?_))
      rw [hMbE]; ring
    refine (reg_oTo_wM1_le hMa hMb (Nh + 1) _ _ _ (by positivity) (by positivity) ha hb).trans
      (le_of_eq (congrArg _ ?_))
    field_simp
    ring

end Traj

end

end Spin2
