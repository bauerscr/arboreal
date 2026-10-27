import Spin2.Pair.PairEStep2
import Obs2.Flow.GradAB1

/-!
# The `E`-step: the pair-local items from per-scale sizes

**`pairErrItemsXP_of_sizes`** derives `PairErrItemsXP` at one scale `k ≤ N_h` for every region from
per-scale **size data** (all proportional to `|β_{a,i+1}|`), with every structural part proved:

* `GoodCov2 k (s_k) (C_k)`, validity (`ValidAt` below `N_h`, `ValidAtL` at `N_h`), `OLocS` and
  `OAnchS` of the reduced history (inputs here; from `MasterCore.pairTraj`, `PtCorr2.olocS_hR`,
  `PtCorr2.oanchS_hR`);
* `Q'`: `‖Q'_k(B)_{ab}‖ ≤ c_Q κ^Q_k|β_{k+1}|` from the `ab` sizes `κ^Q_k|β_{k+1}|` of `K_k` on
  small sets (`PtCorr2.Tj_Q2O_ab_le`; the locality item is not needed, `PairErrItemsXP`);
* `𝔡₂`: `|𝔡₂_k(X)||1 − n_a| ≤ μ_k(nℓ_k/L^{k+1})²c_n|β_{k+1}|` from `|M₄_k(X)| ≤ μ_k|β_{k+1}|`
  (`PtCorr2.pdefM2X_hVR_le`, `b = a + w`, `|w| = n`);
* the gradient tadpole: the range of `F_C` (`PtCorr2.FC_pair_eq_near`) reduces `V'(Λ)_∅` to the
  near blocks, then `Obs2.norm_mass2_FC_le` with the `T_{k+1}(4s_k)` sizes `δ_k|β_{k+1}|` of the
  region gradient part and `e_k` of the near part of `V'_∅`;
* the memory terms: `PtCorr2.memABX_hist_leL` (validity up to `N_h` only), the three localities
  (`PtCorr2.memSz_of_sizes`), the sizes `P_i`, `F_i`, `Λ_i`, `W_i` (times `|β_{i+1}|`), the kernel
  `τ_{ik}` of `tadInc₂`, and the ratio `|β_{i+1}| ≤ (64/49)^{k-i}|β_{k+1}|` (`hBeta_ratio_pow`):
  `s^m_k = ∑_{j≤i<k}(P_iτ_{ik} + ker_{ik}(F_i + 2Λ_i + 2W_i))(64/49)^{k-i}`, `η^m = 0`;
* the `𝒲'` item is passed through (its sizes at scale `k` in `T_k(s_k)` are not exported by the
  `𝒲` chain).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

theorem cQab_nonneg : 0 ≤ cQab := (Classical.choose_spec (PtCorr2.Tj_Q2O_ab_le (d := 2) one_le_two)).1

theorem cQab_spec : ∀ (L : ℕ) [NeZero L],
    2 ^ (2 + 3) + 8 * 2 < L → ∀ (N : ℕ) (P : Obs2.ObsPts 2 L N) (k : ℕ), k < N → ∀ ℓ : ℝ, 0 < ℓ →
    ∀ (V W : Obs2.OFam .two 2 L N) (K : Obs2.OAct .two 2 L N), Obs2.OAnchS P k V W K →
    ∀ κ : ℝ, 0 ≤ κ →
      (∀ X, IsSmall k X → (K X : Obs.SA .two (Lam 2 L N)).ab ∈ NX (nbhd k X : Set (Lam 2 L N))) →
      (∀ X, IsSmall k X → Tj 2 (L : ℝ) k ℓ (K X : Obs.SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal κ) →
      ∀ b, Tj 2 (L : ℝ) k ℓ (Obs2.Q2O P k K b : Obs.SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (cQab * κ) :=
  (Classical.choose_spec (PtCorr2.Tj_Q2O_ab_le (d := 2) one_le_two)).2

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The memory size `s^m_k` of the `E`-step. -/
def smE (m b μ₀ : ℝ) (j : ℕ) (Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico j k, (Pd i * τ i k + PtCorr2.memKer (R.withMsq m)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i k * (F i + 2 * Λ i + 2 * Wp i)) *
      (64 / 49 : ℝ) ^ (k - i)

set_option maxHeartbeats 4000000 in
/-- **The pair-local items at one scale from the per-scale sizes.** -/
theorem pairErrItemsXP_of_sizes {Nh : ℕ} (hN : Nh + 2 = N) (hL49 : 49 ≤ L)
    (hLb : PtCorr2.prodLb ≤ (L : ℝ)) (hLp : pauliL0 2 ≤ L) (m b μ₀ : ℝ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
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
    -- the size sequences
    (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
    (h0 : ∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
      0 ≤ Λ k ∧ 0 ≤ Wp k)
    (hτ0 : ∀ i k, 0 ≤ τ i k)
    {k : ℕ} (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hkN : k ≤ Nh) (X : Finset (Lam 2 L N))
    -- the sizes at scale `k`
    (hKs : ∀ Y, IsSmall k Y → Tj 2 (L : ℝ) k
      (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k Y : Obs.SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal (κQ k * ‖hBeta R m b μ₀ x (k + 1)‖))
    (hWk : let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
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
        sw k * ‖hBeta R m b μ₀ x (k + 1)‖ + ηw k * ‖hRRX R m b μ₀ oR x X (k - 1)‖)
    (hμ : ‖Obs2.m4X (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (oR x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) X‖ ≤ μ k * ‖hBeta R m b μ₀ x (k + 1)‖)
    (hnA : ‖1 - Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ cn k)
    (hδ : Tj 2 (L : ℝ) (k + 1)
        (2 * (2 * PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
        (Obs2.dABX (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) X) ≤
        ENNReal.ofReal (δ k * ‖hBeta R m b μ₀ x (k + 1)‖))
    (he : Tj 2 (L : ℝ) (k + 1)
        (2 * (2 * PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
        (PtCorr2.gNear (0 : Lam 2 L N) x k (blockIdx (L := L) (N := N) k) fun c =>
          (Obs2.VprO (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) c : Obs.SA .two (Lam 2 L N)).e) ≤
        ENNReal.ofReal (e k))
    -- the sizes at the scales `i < k` (memory)
    (hPd : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
      ‖Obs2.pdefM2X i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X‖ ≤ Pd i * ‖hBeta R m b μ₀ x (i + 1)‖)
    (hτ : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
      ‖Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) i k‖ ≤ τ i k)
    (hF : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
      Tj 2 (L : ℝ) (i + 1) (PtCorr2.histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (FC (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
          (Obs2.dABX (ptsX x) i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
            (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X)
          (PtCorr2.gNear (0 : Lam 2 L N) x i (blockIdx (L := L) (N := N) i) fun c =>
            (Obs2.VprO (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
              (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) c : Obs.SA .two (Lam 2 L N)).e)) ≤
        ENNReal.ofReal (F i * ‖hBeta R m b μ₀ x (i + 1)‖))
    (hΛ : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k → ∀ B,
      (B = blk i (0 : Lam 2 L N) ∨ B = blk i x) →
      Tj 2 (L : ℝ) (i + 1) (PtCorr2.histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Obs2.LSO (ptsX x) i (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
          (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) B : Obs.SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Λ i * ‖hBeta R m b μ₀ x (i + 1)‖))
    (hWp : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k → ∀ c',
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
        ENNReal.ofReal (Wp i * ‖hBeta R m b μ₀ x (i + 1)‖)) :
    PairErrItemsXP R m b μ₀ oR x X k
      (fun k => PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (fun k => cQab * κQ k) se so sw
      (fun k => μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k)
      (fun k => 2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2)
      (smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ) ηw (fun _ _ => 0) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  set P := ptsX x with hPdef
  set C := Obs2.histCovO (R.withMsq m) t with hCd
  set V := PtCorr2.hVR (R.withMsq m) P j (oR x) t with hVd
  set W := PtCorr2.hWR (R.withMsq m) P j (oR x) t with hWd
  set K := PtCorr2.hKR (R.withMsq m) P j (oR x) t with hKd
  set s := fun k => PtCorr2.histS (R.withMsq m) k t with hsd
  set β := fun k => ‖hBeta R m b μ₀ x k‖ with hβd
  have hβ0 : ∀ k, 0 ≤ β k := fun k => norm_nonneg _
  have hNk : k < N := by omega
  have hk1N : k + 1 < N := by omega
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ i, 0 < s i := fun i => PtCorr2.histS_pos' (R.withMsq m) hρ0 hρ8 t i
  have hL5 : 2 ^ (2 + 3) ≤ L := by norm_num; omega
  have hL5' : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hPa : P.a = 0 := rfl
  have hPb : P.b = x := rfl
  -- `|x|_∞ ≤ L^{i+1}` for `i ≥ j`
  have hab : ∀ i, j ≤ i → (supNorm (P.b - P.a) : ℝ) ≤ (L : ℝ) ^ (i + 1) := by
    intro i hi
    have h1 := two_supNorm_lt_coal (by omega : 2 ≤ L) x
    have h2 : ((2 * supNorm (x - 0) : ℕ) : ℝ) ≤ ((L ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1.le
    push_cast at h2
    have h3 : (L : ℝ) ^ (j + 1) ≤ (L : ℝ) ^ (i + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) (by omega)
    have h4 : (0 : ℝ) ≤ (supNorm (x - 0) : ℝ) := by positivity
    show (supNorm (x - 0) : ℝ) ≤ _
    linarith
  have hVabk : ∀ i (c : Fin 2 → ℕ), (V i c : Obs.SA .two (Lam 2 L N)).ab ∈
      NX ({P.a, P.b} : Set (Lam 2 L N)) := fun i c => PtCorr2.hVR_ab_mem (R.withMsq m) P j (oR x) t hVab i c
  have hanc' : ∀ i, j ≤ i → Obs2.OAnchS P i (V i) (W i) (K i) := fun i hi =>
    PtCorr2.oanchS_hR (R.withMsq m) P hanc t hi
  have hloc' : ∀ i, j ≤ i → i ≤ Nh → Obs2.OLocS P i (V i) (W i) (K i) := fun i hi hiN =>
    PtCorr2.olocS_hR (R.withMsq m) P t hloc0 hi fun i' _ hi' => hRI i' (by omega)
  have hCR : ∀ i, i ≤ Nh → Obs2.CovRange i (C i) := fun i hi u v h =>
    (hG i hi).range (by omega) u v h
  obtain ⟨hκ0, hμ0, hcn0, hδ0, he0, -, -, -, -⟩ := h0 k
  -- the `Q'` item
  have hQ : ∀ B, Tj 2 (L : ℝ) k (s k) (Obs2.Q2O P k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal (cQab * κQ k * β (k + 1)) := by
    intro B
    have h := cQab_spec L hL5' N P k hNk (s k) (hs k) (V k) (W k) (K k) (hanc' k hjk)
      (κQ k * β (k + 1)) (mul_nonneg hκ0 (hβ0 _))
      (fun Y hY => ((hloc' k hjk hkN).hK Y ⟨hY.1, hY.2.1⟩).2.2.2.1) hKs B
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring
  -- the Pauli defect
  have hP : ‖Obs2.pdefM2X k (C k) (V k) X‖ * ‖1 - Obs2.nA2 P k (C k) (V k)‖ ≤
      μ k * (w.length * (s k / (L : ℝ) ^ (k + 1))) ^ 2 * cn k * β (k + 1) := by
    have h1 := PtCorr2.pdefM2X_hVR_le (R.withMsq m) P t hVab (hsym k hjk hkN) (hG k hkN) w hw X
    have h2 := norm_nonneg (1 - Obs2.nA2 P k (C k) (V k))
    have h3 : ‖Obs2.pdefM2X k (C k) (V k) X‖ ≤
        μ k * β (k + 1) * (w.length * (s k / (L : ℝ) ^ (k + 1))) ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_right hμ (sq_nonneg _))
    calc ‖Obs2.pdefM2X k (C k) (V k) X‖ * ‖1 - Obs2.nA2 P k (C k) (V k)‖
        ≤ (μ k * β (k + 1) * (w.length * (s k / (L : ℝ) ^ (k + 1))) ^ 2) * cn k :=
          mul_le_mul h3 hnA h2 (by have := hβ0 (k + 1); positivity)
      _ = _ := by ring
  -- the gradient tadpole
  have hGr : ‖Obs.LocObs.mass2 (FC (C k) (Obs2.dABX P k (C k) (V k) X)
      (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤
      2 * δ k * e k * (s k)⁻¹ ^ 2 * β (k + 1) := by
    have hD := PtCorr2.dABX_mem_pair P k (C k) (V k) X (hVabk k)
    rw [PtCorr2.VprLO_e_eq, PtCorr2.FC_pair_eq_near (hCR k hkN) hD _
      (fun c => ((hloc' k hjk hkN).Vpr_mem c).1)]
    have h := Obs2.norm_mass2_FC_le (hs k) (hG k hkN) (mul_nonneg hδ0 (hβ0 _)) he0 hδ he
    refine h.trans (le_of_eq ?_)
    ring
  -- the memory terms
  have hM : ∑ i ∈ Finset.Ico j k, ‖Obs2.memABX P C V W X i k‖ ≤
      smE R m b μ₀ j Pd F Λ Wp τ k * β (k + 1) +
        ∑ i ∈ Finset.Icc j k, (fun _ _ => (0 : ℝ)) i k * ‖hRRX R m b μ₀ oR x X i‖ := by
    have hM := PtCorr2.memABX_hist_leL (R.withMsq m) hρ0 hρ8 (n := Nh) (by omega) hV hVL t P hLb
      V W K X hkN (by omega) (fun i h1 h2 => hanc' i h1) (fun i => Pd i * β (i + 1))
      (fun i => F i * β (i + 1)) (fun i => Λ i * β (i + 1)) (fun i => Wp i * β (i + 1))
      τ (fun i => mul_nonneg (h0 i).2.2.2.2.2.2.1 (hβ0 _))
      (fun i => mul_nonneg (h0 i).2.2.2.2.2.2.2.1 (hβ0 _))
      (fun i => mul_nonneg (h0 i).2.2.2.2.2.2.2.2 (hβ0 _)) (fun i h1 h2 => hPd i h1 h2)
      (fun i h1 h2 => hτ i h1 h2) fun i h1 h2 => by
        have hD := PtCorr2.dABX_mem_pair P i (C i) (V i) X (hVabk i)
        exact PtCorr2.memSz_of_sizes (R.withMsq m) t P (hloc' i h1 (by omega)) hL5 (by omega)
          (hCR i (by omega)) (hab i h1) hD (hF i h1 h2) (hΛ i h1 h2) (hWp i h1 h2)
    have hsum0 : ∑ i ∈ Finset.Icc j k, (fun _ _ => (0 : ℝ)) i k * ‖hRRX R m b μ₀ oR x X i‖ = 0 := by
      simp
    rw [hsum0, add_zero]
    refine hM.trans ?_
    unfold smE
    refine PtCorr2.mem_conv_le _ (fun i => Pd i * τ i k + PtCorr2.memKer (R.withMsq m) t i k *
      (F i + 2 * Λ i + 2 * Wp i)) β (64 / 49) (fun i => ?_)
      (fun i _ => le_of_eq (by ring)) (fun i hi => ?_)
    · have hk0 := PtCorr2.memKer_nonneg (R.withMsq m) hρ0 hρ8 t i k
      obtain ⟨-, -, -, -, -, hP0, hF0, hΛ0, hW0⟩ := h0 i
      exact add_nonneg (mul_nonneg hP0 (hτ0 i k)) (mul_nonneg hk0
        (add_nonneg (add_nonneg hF0 (mul_nonneg zero_le_two hΛ0)) (mul_nonneg zero_le_two hW0)))
    · have hik := Finset.mem_Ico.1 hi
      have := hBeta_ratio_pow R x hβr (i + 1) (k + 1) (by omega) (by omega)
      rwa [show k + 1 - (i + 1) = k - i by omega] at this
  exact ⟨hG k hkN, hQ, hWk, hP, hGr, hM⟩

end Traj

end

end Spin2
