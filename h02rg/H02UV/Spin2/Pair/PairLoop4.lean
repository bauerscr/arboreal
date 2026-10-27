import Spin2.Pair.PairLoop3

/-!
# The `E`-step size data after the cancellation; the master route

* **`PairESizesAt3`** / **`PairESizes3`**: the size data of `PairESizesAt`/`PairESizes` with
  the item `|M₄_k(X)| ≤ μ_k|β_{k+1}|` replaced by the per-step sources
  `|M₄(Q_i)(X)| ≤ μ^Q_i|β_{i+1}|`, `|M₄(Loc S_i)(X)| ≤ μ^S_i|β_{i+1}|` (`i < k`) and the vertex
  bound `|n_k| ≤ c_{ν,k}`, and **without** the `Loc S_i` size `Λ_i`;
* **`pairEStep3_of_sizes`** (the `E`-step), **`pairJointSizesP3_MF`** (`PairJointSizesP3` for
  `oRed … dxStd` under `MasterFacts`), **`pairRRelR_of_jointSizesP3_MF`** (⇒ `PairRRelR`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The reorganised size data of the `E`-step at scale `k`** (for every region `X`). -/
def PairESizesAt3 (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ)
    (κQ se so sw ηw μQ μS cn cν δ e Pd F Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) : Prop :=
  (∀ Y, IsSmall k Y → Tj 2 (L : ℝ) k
        (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k Y : Obs.SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (κQ k * ‖hBeta R m b μ₀ x (k + 1)‖)) ∧
  (∀ X : Finset (Lam 2 L N), let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
        let C := Obs2.histCovO (R.withMsq m) t
        let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let ℓs := fun k => PtCorr2.histS (R.withMsq m) k t
        Obs.coal L (0 : Lam 2 L N) x < k →
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
          (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (se k)) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
          (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (so k)) ∧
        2 * ((L : ℝ) ^ 2 * so k * ((1 + se k) ^ (L ^ 2) - 1) * (ℓs k)⁻¹ ^ 2) ≤
          sw k * ‖hBeta R m b μ₀ x (k + 1)‖ + ηw k * ‖hRRX R m b μ₀ oR x X (k - 1)‖) ∧
  (∀ X : Finset (Lam 2 L N), ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
      ‖Obs2.m4QX (ptsX x) i (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (oR x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X‖ ≤ μQ i * ‖hBeta R m b μ₀ x (i + 1)‖) ∧
  (∀ X : Finset (Lam 2 L N), ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
      ‖Obs2.m4LSX (ptsX x) i
        (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
        (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X‖ ≤ μS i * ‖hBeta R m b μ₀ x (i + 1)‖) ∧
  (‖1 - Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ cn k) ∧
  (‖Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ cν k) ∧
  (∀ X : Finset (Lam 2 L N), Tj 2 (L : ℝ) (k + 1)
          (2 * (2 * PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (Obs2.dABX (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) X) ≤
          ENNReal.ofReal (δ k * ‖hBeta R m b μ₀ x (k + 1)‖)) ∧
  (Tj 2 (L : ℝ) (k + 1)
          (2 * (2 * PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (PtCorr2.gNear (0 : Lam 2 L N) x k (blockIdx (L := L) (N := N) k) fun c =>
            (Obs2.VprO (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
              (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) c : Obs.SA .two (Lam 2 L N)).e) ≤
          ENNReal.ofReal (e k)) ∧
  (∀ X : Finset (Lam 2 L N), ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
        ‖Obs2.pdefM2X i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X‖ ≤ Pd i * ‖hBeta R m b μ₀ x (i + 1)‖) ∧
  (∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
        ‖Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) i k‖ ≤ τ i k) ∧
  (∀ X : Finset (Lam 2 L N), ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
        Tj 2 (L : ℝ) (i + 1) (PtCorr2.histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (FC (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
            (Obs2.dABX (ptsX x) i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
              (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X)
            (PtCorr2.gNear (0 : Lam 2 L N) x i (blockIdx (L := L) (N := N) i) fun c =>
              (Obs2.VprO (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
                (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) c : Obs.SA .two (Lam 2 L N)).e)) ≤
          ENNReal.ofReal (F i * ‖hBeta R m b μ₀ x (i + 1)‖)) ∧
  (∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k → ∀ c',
        (c' = blk (i + 1) (0 : Lam 2 L N) ∨ c' = blk (i + 1) x) →
        Tj 2 (L : ℝ) (i + 1) (PtCorr2.histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((Obs2.Wnext2O (ptsX x) i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
              (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
              (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) c' -
            ∑ B ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c'),
              Obs2.WpO (ptsX x) i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
                (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
                (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) B : Obs.OE .two (Lam 2 L N)) :
              Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (Wp i * ‖hBeta R m b μ₀ x (i + 1)‖))

/-- **The reorganised size data of the `E`-step**: at every scale `k < n`, from `VB n` and the
region masses below `n`. -/
def PairESizes3 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cr : ℝ) (x : Lam 2 L N) (VB : ℕ → Prop)
    (κQ se so sw ηw μQ μS cn cν δ e Pd F Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) : Prop :=
  ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
    (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
    ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < n →
      PairESizesAt3 R m b μ₀ oR x k κQ se so sw ηw μQ μS cn cν δ e Pd F Wp τ

/-- **The `E`-step with the reorganised items.** -/
theorem pairEStep3_of_sizes {Nh : ℕ} (hN : Nh + 2 = N) (hL49 : 49 ≤ L)
    (hLb : PtCorr2.prodLb ≤ (L : ℝ)) (hLp : pauliL0 2 ≤ L) (m b μ₀ : ℝ) (lam : ℕ → ℂ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) (cr : ℝ) (x : Lam 2 L N)
    (hVab : PtCorr2.ObsVabInv (ptsX x) (oR x))
    (hloc0 : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (hanc : PtCorr2.ObsAnchInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hG : ∀ k ≤ Nh, GoodCov2 k (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k))
    (hRI : ∀ i ≤ Nh, ValidCore (R.withMsq m) i ∧
      RawInv (R.withMsq m) i (rawHist (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hβr : ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ 64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖)
    (w : List (Dir 2)) (hw : Obs2.pathEnd (0 : Lam 2 L N) w = x)
    (VB : ℕ → Prop) (κQ se so sw ηw μQ μS cn cν δ e Pd F Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
    (h0 : ∀ k, 0 ≤ κQ k ∧ 0 ≤ μQ k ∧ 0 ≤ μS k ∧ 0 ≤ cn k ∧ 0 ≤ cν k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧
      0 ≤ Pd k ∧ 0 ≤ F k ∧ 0 ≤ Wp k)
    (hτ0 : ∀ i k, 0 ≤ τ i k)
    (hS : PairESizes3 R Nh m b μ₀ lam oR cr x VB κQ se so sw ηw μQ μS cn cν δ e Pd F Wp τ) :
    ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
      (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
      ∀ M, Obs.coal L (0 : Lam 2 L N) x ≤ M → M ≤ n → ∀ X : Finset (Lam 2 L N),
        IsPolymer M X → ∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
          PairErrItemsXP3 R m b μ₀ oR x X k
            (fun k => PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (fun k => cQab * κQ k) se so sw
            (spE3 (Obs.coal L (0 : Lam 2 L N) x) μQ μS cn cν (fun k => (w.length *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
                (L : ℝ) ^ (k + 1))) ^ 2))
            (fun k => 2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2)
            (smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Wp τ) ηw (fun _ _ => 0) := by
  intro n hn1 hn2 hVB hMs M hM1 hM2 X hX k hk
  have hkM := Finset.mem_Ico.1 hk
  obtain ⟨hKs, hWk, hμQ, hμS, hnA, hnν, hδ, he, hPd, hτ, hF, hWp⟩ :=
    hS n hn1 hn2 hVB hMs k hkM.1 (by omega)
  exact pairErrItemsXP3_of_sizes R hN hL49 hLb hLp m b μ₀ oR x hVab hloc0 hanc hV hVL hG hRI
    hβr w hw κQ se so sw ηw μQ μS cn cν δ e Pd F Wp τ h0 hτ0 hkM.1 (by omega) X hKs (hWk X)
    (hμQ X) (hμS X) hnA hnν (hδ X) he (hPd X) hτ (hF X) hWp

end Traj

set_option maxHeartbeats 4000000 in
/-- **`PairJointSizesP3` for the reduced states** from the `V`-step data and the reorganised
`E`-step sizes, along every admissible trajectory of `MasterFacts` (copy of
`pairJointSizesP_MF`). -/
theorem pairJointSizesP3_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) (ce ca cr : ℝ)
    (hX : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ (VB : ℕ → Prop) (κQ se so sw ηw μQ μS cn cν δ e Pd F Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
        (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
        (∀ k, 0 ≤ κQ k ∧ 0 ≤ μQ k ∧ 0 ≤ μS k ∧ 0 ≤ cn k ∧ 0 ≤ cν k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧
          0 ≤ Pd k ∧ 0 ≤ F k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
        (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * κQ k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              sw k + spE3 (Obs.coal L (0 : Lam 2 L N) x) μQ μS cn cν (fun k => (w.length *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
                  (L : ℝ) ^ (k + 1))) ^ 2) k +
              2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Wp τ k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
        VB (Obs.coal L (0 : Lam 2 L N) x) ∧
        (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
          PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ dxStd) cr x n → VB (n + 1)) ∧
        PairESizes3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x VB κQ se so sw ηw μQ μS cn cν δ e
          Pd F Wp τ) :
    PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hLb : PtCorr2.prodLb ≤ (L : ℝ) := M.core.hLb.trans (by exact_mod_cast M.core.hLo)
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  intro x hx h1 hj
  obtain ⟨VB, κQ, se, so, sw, ηw, μQ, μS, cn, cν, δ, e, Pd, F, Wp, τ, w, hw, h0, hτ0, h0', hsum,
    hηsum, hVB0, hVs, hS⟩ := hX x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hVab : PtCorr2.ObsVabInv (ptsX x) (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  have hloc0 := (hRd x hx h1 hj).2.1
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hβr := pairBetaRatio_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  refine ⟨VB, fun k => PtCorr2.histS (R.withMsq m) k t, fun k => cQab * κQ k, se, so, sw,
    spE3 j μQ μS cn cν (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k t /
      (L : ℝ) ^ (k + 1))) ^ 2),
    fun k => 2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k t)⁻¹ ^ 2,
    smE3 R m b μ₀ j Pd F Wp τ, ηw, fun _ _ => 0, fun k => ?_, fun _ _ => le_rfl, hsum, ?_,
    hVB0, hVs, pairEStep3_of_sizes R hNh hL49 hLb hLp m b μ₀ lam _ cr x hVab hloc0 hanc hV hVL hG
      hRI hβr w hw VB κQ se so sw ηw μQ μS cn cν δ e Pd F Wp τ h0 hτ0 hS⟩
  · obtain ⟨hκ0, -, -, -, -, hδ0, he0, -, -, -⟩ := h0 k
    obtain ⟨hse, hso, hsw, hηw⟩ := h0' k
    exact ⟨PtCorr2.histS_pos' (R.withMsq m) hρ0 hρ8 t k, mul_nonneg cQab_nonneg hκ0, hse, hso,
      hsw, spE3_nonneg j (fun i => (h0 i).2.1) (fun i => (h0 i).2.2.1) (fun i => (h0 i).2.2.2.1)
        (fun i => (h0 i).2.2.2.2.1) (fun i => sq_nonneg _) k,
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hδ0) he0) (sq_nonneg _),
      smE3_nonneg R m b μ₀ hρ0 hρ8 j (fun i => (h0 i).2.2.2.2.2.2.2.1)
        (fun i => (h0 i).2.2.2.2.2.2.2.2.1) (fun i => (h0 i).2.2.2.2.2.2.2.2.2) hτ0 k, hηw⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hηsum
    simp

set_option maxHeartbeats 4000000 in
/-- **The joint route from `MasterFacts` with the reorganised items** (copy of
`pairRRelR_of_jointSizesP_MF`). -/
theorem pairRRelR_of_jointSizesP3_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) {ce ca cr : ℝ} (hce : 0 ≤ ce)
    (hcr : crErr2 ce M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) ca ≤ cr)
    (hJ : PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr) :
    PairRRelR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr ∧
      PairRRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr ∧
      PairErrRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg' : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1.le, ((hadm.1 k hk).2.1).trans M.eps_le⟩
  have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
  have hG2 : ∑ k ∈ Finset.range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤
      4 / betaL L :=
    sum_gsq_le_of_inc hβL (M.ginc N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm)
      (hg' 0 (Nat.zero_le _)).1 (hg' Nh le_rfl).2
  have hmono := M.gmono N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1 := by
    intro i l hil hl
    have key : ∀ n, i + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (i + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (i + n) (by omega))
    have := key (l - i) (by omega)
    rwa [show i + (l - i) = l by omega] at this
  obtain ⟨hct, htad, hcg⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hF := M.flow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j :=
    ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL := ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hRd := pairSectRed_of R m hval hvalL b μ₀ (pairDCov_std Nh)
  have hloop := fun x : Lam 2 L N =>
    (M.loop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  refine pairRRelR_of_jointSizesP3 R hNh hLp m hb lam (oRed R m b μ₀ dxStd) hce M.cRel_nonneg hct
    (le_max_right _ _) hL49 (fun k hk => (hg' k hk).1) hG2 hgm hcg hRd
    (fun x B => oRed_V_ab_zero R m b μ₀ dxStd x B) (fun x B => oRed_W_ab_zero R m b μ₀ dxStd x B)
    (fun x _ => M.relG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)
      (zV_mua_ne hb))
    (fun x _ k hk => by
      obtain ⟨q, -, -, hl⟩ := hloop x
      exact (hl k hk).1)
    (fun x _ k hk => by
      obtain ⟨q, -, -, hl⟩ := hloop x
      exact (hl k hk).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hg' k hk.le).1))
    (fun x _ _ _ => (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1)
    (fun x _ i k hik hk => htad (ptsX x) (zV b) i k hik hk)
    (pairAnchR_oRed R Nh m b μ₀)
    (pairRedInv_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm) hcr hJ

end

end Spin2
