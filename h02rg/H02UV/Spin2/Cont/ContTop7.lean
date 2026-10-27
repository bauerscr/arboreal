import Spin2.Pair.PairLin3
import PtCorr2.Restart.RestartPairAB

set_option autoImplicit false

/-!
# Top coalescence: the `σ_aσ_b` size `k₂` at `N_h + 1` for the pair-difference datum

**`ct_k2_top`**: `PtCorr2.rpab_top` for `δ = pl2Delta R m b μ₀ x y ms` restarted at `ms`, with the
small-set input `hKs` (`K^δ_j(X)_{ab} = 0` for small `X`, `ms ≤ j ≤ N_h`) discharged by the relaxed
coalescence invariant (`pl3_delta_inv`, `N_h < j_y`). The remaining inputs are those of `rpab_top`:
the per-scale sizes `m_j`, `k₁_j` (`ms ≤ j ≤ N_h`) of the restarted history in one fixed weight
`w`, the `KObsBoundsU` constants with their smallness, and `hK20`, the `ab` part of `K^δ_{ms}`
(the datum's own `σ_aσ_b` activity). Conclusion:
`A^{(|𝓑(X)|−4)_+}w_{ab}T_{N_h+1}(K_{N_h+1}(X)_{ab}) ≤ (c_{ab}/5)(cǧ_{N_h})m_{N_h}²`, i.e.
`k₂ = (c_{ab}/5)·r_{N_h}m_{N_h}²` in `ct_T5top`/`ct_conn_diff_top` (`w = wM(2s_{N_h}²σ, M_b)`).
-/

namespace Spin2

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist PtCorr2

noncomputable section

variable {L N : ℕ} [NeZero L]

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 1000000 in
/-- **`k₂` at `N_h + 1` for the pair-difference datum** (`rpab_top`, `hKs` discharged). -/
theorem ct_k2_top (m : ℝ) {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L (R.withMsq m).A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L (R.withMsq m).A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hN : Nh + 2 = N)
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh)
    (hm : ∀ j < Nh, |(R.withMsq m).msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |(R.withMsq m).msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp (R.withMsq m) Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ) (x y : Lam 2 L N)
    (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤) {ms : ℕ} (hmsN : ms ≤ Nh) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hjy : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    (h0 : (pl2Delta R m b μ₀ x y ms).IsObs) (hl0 : ObsLocInv (ptsX y) ms (pl2Delta R m b μ₀ x y ms))
    (hs0 : ObsSymInv ms (pl2Delta R m b μ₀ x y ms))
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (mm k₁ : ℕ → ℝ) (c₁ cab : ℝ) (hc₁ : 0 ≤ c₁) (hm0 : ∀ j, 0 < mm j)
    (hmm : ∀ j, ms ≤ j → j < Nh → mm j ≤ 2 * mm (j + 1)) (hk₁0 : ∀ j, 0 ≤ k₁ j)
    (hk₁ : ∀ j, ms ≤ j → j ≤ Nh → k₁ j ≤ c₁ * (cR (R.withMsq m) Λ cm C₂ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ 2 * mm j)
    (hrm : ∀ j, ms ≤ j → j ≤ Nh → cR (R.withMsq m) Λ cm C₂ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ mm j)
    (hcab : 10 * kB2 (kθ0 L (R.withMsq m).A C₀ η) C₁ (cx κ cT) c₁ ≤ cab)
    (hε1 : cR (R.withMsq m) Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR (R.withMsq m) Λ cm C₂ * ε) ≤ ε₀)
    (hkt1 : 8 * (cx κ cT + c₁ + cab) * (cR (R.withMsq m) Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + c₁ + cab) * (cR (R.withMsq m) Λ cm C₂ * ε) ^ 3 ≤ ε₀)
    (hθ' : 8 * kθ0 L (R.withMsq m).A C₀ η + 16 * C₁ * (cR (R.withMsq m) Λ cm C₂ * ε) +
      8 * C₁ * (8 * (cx κ cT + c₁ + cab) * (cR (R.withMsq m) Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hVo : ∀ j, ms ≤ j → j ≤ Nh → ∀ q ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q) ≤ ENNReal.ofReal (mm j))
    (hWo : ∀ j, ms ≤ j → j ≤ Nh → ∀ q ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q) ≤
        ENNReal.ofReal (cR (R.withMsq m) Λ cm C₂ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 * mm j))
    (hK1 : ∀ j, ms ≤ j → j ≤ Nh → ∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤ ENNReal.ofReal (k₁ j))
    (hK20 : ∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ((pl2Delta R m b μ₀ x y ms).K X : SA .two (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab * (cR (R.withMsq m) Λ cm C₂ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) * mm ms ^ 2)) :
    ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal ((R.withMsq m).A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X : SA .two (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab / 5 * ((cR (R.withMsq m) Λ cm C₂ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) * mm Nh ^ 2)) := by
  have hmy : ms < Obs.coal L (0 : Lam 2 L N) y := by omega
  exact rpab_top (R.withMsq m) hKB hC₀ hC₁ hSB hV hVL hm hmNh hβ hδ1 H (ptsX y) w hw hwa hwb hwab
    hmsN _ h0 hl0 hs0 _ ht
    (fun j hmj hjN X hX => (pl3_delta_inv R hN m hV hVL hL b μ₀ x y hmsN hblk hmx hmy (k := j) hmj
      (by omega) (by omega)).Kab X hX)
    mm k₁ c₁ cab hc₁ hm0 hmm hk₁0 hk₁ hrm hcab hε1 hεε hkt1 hktε hθ' hVo hWo hK1 hK20

end

end Spin2
