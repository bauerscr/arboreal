import Spin2.Pair.PairEStep3

/-!
# The `E`-step of the joint induction

* **`PairESizesAt`**: the per-scale size data of the `E`-step at scale `k` (all regions `X`):
  the `ab` sizes of `K_k` on small sets, the `𝒲'_{k-1}` block (passed through), `|M₄_k(X)|`,
  `|1 − n_{a,k}|`, the `T_{k+1}(4s_k)` sizes of the region gradient part and of the near part of
  `V'_∅`, and, for `j_x ≤ i < k`, `|𝔡₂_i(X)|`, `|tadInc₂(i,k)|` and the `T_{i+1}(s_{i+1})` sizes of
  the three memory arguments (all but `𝒲'`, `n_a`, `V'_∅`, `tadInc₂` proportional to
  `|β_{a,i+1}|`).
* **`PairESizes`**: these data at every `k < n` from the `V`-block sizes `VB n` and the region
  masses below `n` (the form of the `E`-step of `PairJointSizes`).
* **`pairEStep_of_sizes`** (task (6) of the `E`-step): `VB n` + masses below `n` ⇒ the pair-local
  items `PairErrItemsXP` of every region at every scale `k < M ≤ n`, with the sequences fixed in
  advance (`ℓ_k = s_k`, `s^q = c_Qκ^Q`, `s^p = μ(nℓ/L^{k+1})²c_n`, `s^g = 2δe s_k^{-2}`,
  `s^m = smE`, `η^m = 0`).
* **`pairJointSizesP_of_ESizes`**: the `V`-step data (`VB j_x`, the `V`-step) + `PairESizes` +
  the two summability conditions ⇒ `PairJointSizesP`.
* **`pairEStep_MF`**: the same for the reduced states `oRed … dxStd` along every admissible
  trajectory of `MasterFacts`: all trajectory facts (validity up to `N_h`, `GoodCov2`, `OLocS`,
  `OAnchS`, `U(1)` invariance, the `β_a` ratio) are discharged.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The size data of the `E`-step at scale `k`** (for every region `X`). -/
def PairESizesAt (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ)
    (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) : Prop :=
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
  (∀ X : Finset (Lam 2 L N), ‖Obs2.m4X (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
          (oR x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) X‖ ≤ μ k * ‖hBeta R m b μ₀ x (k + 1)‖) ∧
  (‖1 - Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ cn k) ∧
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
  (∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k → ∀ B,
        (B = blk i (0 : Lam 2 L N) ∨ B = blk i x) →
        Tj 2 (L : ℝ) (i + 1) (PtCorr2.histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs2.LSO (ptsX x) i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
            (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
            (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (Λ i * ‖hBeta R m b μ₀ x (i + 1)‖)) ∧
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

/-- **The size data of the `E`-step**: at every scale `k < n`, from `VB n` and the region masses
below `n`. -/
def PairESizes (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cr : ℝ) (x : Lam 2 L N) (VB : ℕ → Prop)
    (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) : Prop :=
  ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
    (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
    ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < n →
      PairESizesAt R m b μ₀ oR x k κQ se so sw ηw μ cn δ e Pd F Λ Wp τ

/-- **The `E`-step**: from `VB n` and the masses below `n`, the pair-local items of every region
at every scale `k < M ≤ n`. -/
theorem pairEStep_of_sizes {Nh : ℕ} (hN : Nh + 2 = N) (hL49 : 49 ≤ L)
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
    (hsym : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k ≤ Nh →
      PtCorr2.ObsSymInv k (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (oR x) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hβr : ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ 64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖)
    (w : List (Dir 2)) (hw : Obs2.pathEnd (0 : Lam 2 L N) w = x)
    (VB : ℕ → Prop) (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
    (h0 : ∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
      0 ≤ Λ k ∧ 0 ≤ Wp k)
    (hτ0 : ∀ i k, 0 ≤ τ i k)
    (hS : PairESizes R Nh m b μ₀ lam oR cr x VB κQ se so sw ηw μ cn δ e Pd F Λ Wp τ) :
    ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
      (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
      ∀ M, Obs.coal L (0 : Lam 2 L N) x ≤ M → M ≤ n → ∀ X : Finset (Lam 2 L N),
        IsPolymer M X → ∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
          PairErrItemsXP R m b μ₀ oR x X k
            (fun k => PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (fun k => cQab * κQ k) se so sw
            (fun k => μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k)
            (fun k => 2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2)
            (smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ) ηw (fun _ _ => 0) := by
  intro n hn1 hn2 hVB hMs M hM1 hM2 X hX k hk
  have hkM := Finset.mem_Ico.1 hk
  obtain ⟨hKs, hWk, hμ, hnA, hδ, he, hPd, hτ, hF, hΛ, hWp⟩ :=
    hS n hn1 hn2 hVB hMs k hkM.1 (by omega)
  exact pairErrItemsXP_of_sizes R hN hL49 hLb hLp m b μ₀ oR x hVab hloc0 hanc hV hVL hG hRI hsym
    hβr w hw κQ se so sw ηw μ cn δ e Pd F Λ Wp τ h0 hτ0 hkM.1 (by omega) X hKs (hWk X) (hμ X) hnA
    (hδ X) he (hPd X) hτ (hF X) hΛ hWp

end Traj

set_option maxHeartbeats 4000000 in
/-- **`PairJointSizesP` for the reduced states from the `V`-step data and the `E`-step sizes**,
along every admissible trajectory of `MasterFacts`. For every `x`: a predicate `VB` with `VB j_x`
and the `V`-step (the output of the `V`-step), the size data `PairESizes`, a lattice path `w` from
`0` to `x`, and the two summability conditions for the sequences of `pairEStep_of_sizes`. All
trajectory facts are discharged (`MasterCore.pairTraj`, `pairBetaRatio_MF`, the invariants of
`oRed`). -/
theorem pairJointSizesP_MFD {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (lam : ℕ → ℂ) (ce ca cr : ℝ)
    (hX : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ (VB : ℕ → Prop) (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
        (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
        (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
          0 ≤ Λ k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
        (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * κQ k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k +
              2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
        VB (Obs.coal L (0 : Lam 2 L N) x) ∧
        (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
          PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ dxStd) cr x n → VB (n + 1)) ∧
        PairESizes R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x VB κQ se so sw ηw μ cn δ e Pd F Λ
          Wp τ) :
    PairJointSizesP R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hLb : PtCorr2.prodLb ≤ (L : ℝ) := M.core.hLb.trans (by exact_mod_cast M.core.hLo)
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  intro x hx h1 hj
  obtain ⟨VB, κQ, se, so, sw, ηw, μ, cn, δ, e, Pd, F, Λ, Wp, τ, w, hw, h0, hτ0, h0', hsum, hηsum,
    hVB0, hVs, hS⟩ := hX x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hVab : PtCorr2.ObsVabInv (ptsX x) (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  have hloc0 := (hRd x hx h1 hj).2.1
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  have hsym : ∀ k, j ≤ k → k ≤ Nh → PtCorr2.ObsSymInv k (PtCorr2.obsHistFrom (R.withMsq m)
      (ptsX x) j (oRed R m b μ₀ dxStd x) k t) := fun k hk hkN =>
    PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk fun i _ hi => hRI i (by omega)
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD x
  refine ⟨VB, fun k => PtCorr2.histS (R.withMsq m) k t, fun k => cQab * κQ k, se, so, sw,
    fun k => μ k * (w.length * (PtCorr2.histS (R.withMsq m) k t / (L : ℝ) ^ (k + 1))) ^ 2 * cn k,
    fun k => 2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k t)⁻¹ ^ 2,
    smE R m b μ₀ j Pd F Λ Wp τ, ηw, fun _ _ => 0, fun k => ?_, fun _ _ => le_rfl, hsum, ?_,
    hVB0, hVs, pairEStep_of_sizes R hNh hL49 hLb hLp m b μ₀ lam _ cr x hVab hloc0 hanc hV hVL hG
      hRI hsym hβr w hw VB κQ se so sw ηw μ cn δ e Pd F Λ Wp τ h0 hτ0 hS⟩
  · obtain ⟨hκ0, hμ0, hcn0, hδ0, he0, -, -, -, -⟩ := h0 k
    obtain ⟨hse, hso, hsw, hηw⟩ := h0' k
    have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
    have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
    have hsm : 0 ≤ smE R m b μ₀ j Pd F Λ Wp τ k := by
      unfold smE
      refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (pow_nonneg (by norm_num) _)
      obtain ⟨-, -, -, -, -, hP0, hF0, hΛ0, hW0⟩ := h0 i
      exact add_nonneg (mul_nonneg hP0 (hτ0 i k)) (mul_nonneg
        (PtCorr2.memKer_nonneg (R.withMsq m) hρ0 hρ8 _ i k)
        (add_nonneg (add_nonneg hF0 (mul_nonneg zero_le_two hΛ0)) (mul_nonneg zero_le_two hW0)))
    exact ⟨PtCorr2.histS_pos' (R.withMsq m) hρ0 hρ8 t k, mul_nonneg cQab_nonneg hκ0, hse, hso,
      hsw, mul_nonneg (mul_nonneg hμ0 (sq_nonneg _)) hcn0,
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hδ0) he0) (sq_nonneg _), hsm, hηw⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hηsum
    simp

/-- Corollary of `pairJointSizesP_MFD` (`Admissible` ⟹ the domain condition). -/
theorem pairJointSizesP_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) (ce ca cr : ℝ)
    (hX : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ (VB : ℕ → Prop) (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
        (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
        (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
          0 ≤ Λ k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
        (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * κQ k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k +
              2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
        VB (Obs.coal L (0 : Lam 2 L N) x) ∧
        (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
          PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ dxStd) cr x n → VB (n + 1)) ∧
        PairESizes R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x VB κQ se so sw ηw μ cn δ e Pd F Λ
          Wp τ) :
    PairJointSizesP R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr  :=
  pairJointSizesP_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm.1 lam ce ca cr hX

end

end Spin2
