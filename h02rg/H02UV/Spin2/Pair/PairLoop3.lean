import Spin2.Pair.PairLoop2

/-!
# The `E`-step after the cancellation: items from per-scale sizes, the master route

Copies of `pairErrItemsXP_of_sizes`, `PairESizesAt`/`PairESizes`, `pairEStep_of_sizes`,
`pairJointSizesP_MF`, `pairRRelR_of_jointSizesP_MF` for the reorganised items
`PairErrItemsXP3`:

* the Pauli item: from `|M₄(Q_i)(X)| ≤ μ^Q_i|β_{i+1}|`, `|M₄(Loc S_i)(X)| ≤ μ^S_i|β_{i+1}|`
  (`i < k`), `|1 − n_k| ≤ c_n`, `|n_k| ≤ c_ν`, `|m2D(C_k)| ≤ (|w|s_k/L^{k+1})²`:
  `s^p_k = (∑_iμ^Q_i(64/49)^{k-i})D_kc_{n,k} + c_{ν,k}(∑_iμ^S_i(64/49)^{k-i})D_k`
  (`spE3`; the `Loc S` part carries the vertex factor `c_ν = O(ǧ_k)`);
* the memory item without `Λ_i` (the size of `Loc S_i`):
  `s^m_k = ∑_i(P_iτ_{ik} + ker_{ik}(F_i + 2W_i))(64/49)^{k-i}` (`smE3`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The memory size without the `Loc S` tadpole. -/
def smE3 (m b μ₀ : ℝ) (j : ℕ) (Pd F Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico j k, (Pd i * τ i k + PtCorr2.memKer (R.withMsq m)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i k * (F i + 2 * Wp i)) * (64 / 49 : ℝ) ^ (k - i)

/-- The reorganised Pauli size: the `Q`-part with `1 − n_k`, the `Loc S`-part with `n_k`. -/
def spE3 (j : ℕ) (μQ μS cn cν D : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.Ico j k, μQ i * (64 / 49 : ℝ) ^ (k - i)) * D k * cn k +
    cν k * (∑ i ∈ Finset.Ico j k, μS i * (64 / 49 : ℝ) ^ (k - i)) * D k

theorem smE3_nonneg (m b μ₀ : ℝ) (hρ0 : 0 ≤ (R.withMsq m).ρ) (hρ8 : (R.withMsq m).ρ ≤ 1 / 8)
    (j : ℕ) {Pd F Wp : ℕ → ℝ} {τ : ℕ → ℕ → ℝ} (hP : ∀ i, 0 ≤ Pd i) (hF : ∀ i, 0 ≤ F i)
    (hW : ∀ i, 0 ≤ Wp i) (hτ : ∀ i k, 0 ≤ τ i k) (k : ℕ) : 0 ≤ smE3 R m b μ₀ j Pd F Wp τ k := by
  unfold smE3
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (pow_nonneg (by norm_num) _)
  exact add_nonneg (mul_nonneg (hP i) (hτ i k)) (mul_nonneg
    (PtCorr2.memKer_nonneg (R.withMsq m) hρ0 hρ8 _ i k)
    (add_nonneg (hF i) (mul_nonneg zero_le_two (hW i))))

theorem spE3_nonneg (j : ℕ) {μQ μS cn cν D : ℕ → ℝ} (hQ : ∀ i, 0 ≤ μQ i) (hS : ∀ i, 0 ≤ μS i)
    (hcn : ∀ i, 0 ≤ cn i) (hcν : ∀ i, 0 ≤ cν i) (hD : ∀ i, 0 ≤ D i) (k : ℕ) :
    0 ≤ spE3 j μQ μS cn cν D k := by
  unfold spE3
  have h1 : 0 ≤ ∑ i ∈ Finset.Ico j k, μQ i * (64 / 49 : ℝ) ^ (k - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hQ i) (pow_nonneg (by norm_num) _)
  have h2 : 0 ≤ ∑ i ∈ Finset.Ico j k, μS i * (64 / 49 : ℝ) ^ (k - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hS i) (pow_nonneg (by norm_num) _)
  exact add_nonneg (mul_nonneg (mul_nonneg h1 (hD k)) (hcn k))
    (mul_nonneg (mul_nonneg (hcν k) h2) (hD k))

set_option maxHeartbeats 4000000 in
/-- **The reorganised items at one scale from the per-scale sizes** (copy of
`pairErrItemsXP_of_sizes`). -/
theorem pairErrItemsXP3_of_sizes {Nh : ℕ} (hN : Nh + 2 = N) (hL49 : 49 ≤ L)
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
    (hβr : ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ 64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖)
    (w : List (Dir 2)) (hw : Obs2.pathEnd (0 : Lam 2 L N) w = x)
    (κQ se so sw ηw μQ μS cn cν δ e Pd F Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
    (h0 : ∀ k, 0 ≤ κQ k ∧ 0 ≤ μQ k ∧ 0 ≤ μS k ∧ 0 ≤ cn k ∧ 0 ≤ cν k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧
      0 ≤ Pd k ∧ 0 ≤ F k ∧ 0 ≤ Wp k)
    (hτ0 : ∀ i k, 0 ≤ τ i k)
    {k : ℕ} (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hkN : k ≤ Nh) (X : Finset (Lam 2 L N))
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
    (hμQ : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
      ‖Obs2.m4QX (ptsX x) i (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (oR x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X‖ ≤ μQ i * ‖hBeta R m b μ₀ x (i + 1)‖)
    (hμS : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i < k →
      ‖Obs2.m4LSX (ptsX x) i
        (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i)
        (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i) X‖ ≤ μS i * ‖hBeta R m b μ₀ x (i + 1)‖)
    (hnA : ‖1 - Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ cn k)
    (hnν : ‖Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ ≤ cν k)
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
    PairErrItemsXP3 R m b μ₀ oR x X k
      (fun k => PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (fun k => cQab * κQ k) se so sw
      (spE3 (Obs.coal L (0 : Lam 2 L N) x) μQ μS cn cν (fun k => (w.length *
        (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
          (L : ℝ) ^ (k + 1))) ^ 2))
      (fun k => 2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2)
      (smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Wp τ) ηw (fun _ _ => 0) := by
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
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ i, 0 < s i := fun i => PtCorr2.histS_pos' (R.withMsq m) hρ0 hρ8 t i
  have hL5 : 2 ^ (2 + 3) ≤ L := by norm_num; omega
  have hL5' : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL9 : 9 ≤ L := by omega
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
  obtain ⟨hκ0, -, -, hcn0, hcν0, hδ0, he0, -, -, -⟩ := h0 k
  have hratio : ∀ i ∈ Finset.Ico j k, β (i + 1) ≤ (64 / 49 : ℝ) ^ (k - i) * β (k + 1) := by
    intro i hi
    have hik := Finset.mem_Ico.1 hi
    have := hBeta_ratio_pow R x hβr (i + 1) (k + 1) (by omega) (by omega)
    rwa [show k + 1 - (i + 1) = k - i by omega] at this
  -- the `Q'` item
  have hQ : ∀ B, Tj 2 (L : ℝ) k (s k) (Obs2.Q2O P k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal (cQab * κQ k * β (k + 1)) := by
    intro B
    have h := cQab_spec L hL5' N P k hNk (s k) (hs k) (V k) (W k) (K k) (hanc' k hjk)
      (κQ k * β (k + 1)) (mul_nonneg hκ0 (hβ0 _))
      (fun Y hY => ((hloc' k hjk hkN).hK Y ⟨hY.1, hY.2.1⟩).2.2.2.1) hKs B
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring
  -- the reorganised Pauli item
  set Dk := (w.length * (s k / (L : ℝ) ^ (k + 1))) ^ 2 with hDk
  have hD : ‖Obs2.m2D P (C k)‖ ≤ Dk := by
    have h := Obs2.norm_m2Def_le2 (hG k hkN) (0 : Lam 2 L N) w
    rw [hw] at h
    exact h
  have hD0 : 0 ≤ Dk := sq_nonneg _
  have hSQ : ‖∑ i ∈ Finset.Ico j k, Obs2.m4QX P i (K i) X‖ ≤
      (∑ i ∈ Finset.Ico j k, μQ i * (64 / 49 : ℝ) ^ (k - i)) * β (k + 1) :=
    (norm_sum_le _ _).trans (PtCorr2.mem_conv_le _ μQ β (64 / 49) (fun i => (h0 i).2.1)
      (fun i hi => hμQ i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2) hratio)
  have hSS : ‖∑ i ∈ Finset.Ico j k, Obs2.m4LSX P i (C i) (V i) (W i) X‖ ≤
      (∑ i ∈ Finset.Ico j k, μS i * (64 / 49 : ℝ) ^ (k - i)) * β (k + 1) :=
    (norm_sum_le _ _).trans (PtCorr2.mem_conv_le _ μS β (64 / 49) (fun i => (h0 i).2.2.1)
      (fun i hi => hμS i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2) hratio)
  have hP : ‖∑ i ∈ Finset.Ico j k, Obs2.m4QX P i (K i) X‖ * ‖Obs2.m2D P (C k)‖ *
        ‖1 - Obs2.nA2 P k (C k) (V k)‖ +
      ‖Obs2.nA2 P k (C k) (V k)‖ * ‖∑ i ∈ Finset.Ico j k, Obs2.m4LSX P i (C i) (V i) (W i) X‖ *
        ‖Obs2.m2D P (C k)‖ ≤
      spE3 j μQ μS cn cν (fun k => (w.length * (s k / (L : ℝ) ^ (k + 1))) ^ 2) k * β (k + 1) := by
    have hq0 : 0 ≤ (∑ i ∈ Finset.Ico j k, μQ i * (64 / 49 : ℝ) ^ (k - i)) * β (k + 1) :=
      (norm_nonneg _).trans hSQ
    have hl0 : 0 ≤ (∑ i ∈ Finset.Ico j k, μS i * (64 / 49 : ℝ) ^ (k - i)) * β (k + 1) :=
      (norm_nonneg _).trans hSS
    have a1 := mul_le_mul (mul_le_mul hSQ hD (norm_nonneg _) hq0) hnA (norm_nonneg _)
      (mul_nonneg hq0 hD0)
    have a2 := mul_le_mul (mul_le_mul hnν hSS (norm_nonneg _) hcν0) hD (norm_nonneg _)
      (mul_nonneg hcν0 hl0)
    unfold spE3
    calc _ ≤ (∑ i ∈ Finset.Ico j k, μQ i * (64 / 49 : ℝ) ^ (k - i)) * β (k + 1) * Dk * cn k +
          cν k * ((∑ i ∈ Finset.Ico j k, μS i * (64 / 49 : ℝ) ^ (k - i)) * β (k + 1)) * Dk :=
          add_le_add a1 a2
      _ = _ := by ring
  -- the gradient tadpole
  have hGr : ‖Obs.LocObs.mass2 (FC (C k) (Obs2.dABX P k (C k) (V k) X)
      (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤
      2 * δ k * e k * (s k)⁻¹ ^ 2 * β (k + 1) := by
    have hDm := PtCorr2.dABX_mem_pair P k (C k) (V k) X (hVabk k)
    rw [PtCorr2.VprLO_e_eq, PtCorr2.FC_pair_eq_near (hCR k hkN) hDm _
      (fun c => ((hloc' k hjk hkN).Vpr_mem c).1)]
    have h := Obs2.norm_mass2_FC_le (hs k) (hG k hkN) (mul_nonneg hδ0 (hβ0 _)) he0 hδ he
    refine h.trans (le_of_eq ?_)
    ring
  -- the memory terms without `Loc S`
  have hM : ∑ i ∈ Finset.Ico j k, ‖Obs2.memABX3 P C V W X i k‖ ≤
      smE3 R m b μ₀ j Pd F Wp τ k * β (k + 1) +
        ∑ i ∈ Finset.Icc j k, (fun _ _ => (0 : ℝ)) i k * ‖hRRX R m b μ₀ oR x X i‖ := by
    have hM := PtCorr2.memABX3_hist_leL (R.withMsq m) hρ0 hρ8 (n := Nh) (by omega) hV hVL t P hLb
      V W K X hkN (by omega) (fun i h1 h2 => hanc' i h1) (fun i => Pd i * β (i + 1))
      (fun i => F i * β (i + 1)) (fun i => Wp i * β (i + 1))
      τ (fun i => mul_nonneg (h0 i).2.2.2.2.2.2.2.2.1 (hβ0 _))
      (fun i => mul_nonneg (h0 i).2.2.2.2.2.2.2.2.2 (hβ0 _)) (fun i h1 h2 => hPd i h1 h2)
      (fun i h1 h2 => hτ i h1 h2)
      (fun i h1 h2 => by
        have hDm := PtCorr2.dABX_mem_pair P i (C i) (V i) X (hVabk i)
        rw [PtCorr2.VprLO_e_eq]
        exact PtCorr2.locSz_FC_near (R.withMsq m) t (hCR i (by omega)) hL9 (hab i h1) hDm _
          (fun c => ((hloc' i h1 (by omega)).Vpr_mem c).1) _ (hF i h1 h2))
      (fun i h1 h2 c' hc => PtCorr2.locSz_prodPart (R.withMsq m) t (hloc' i h1 (by omega)) hL5
        (by omega) (hCR i (by omega)) (hab i h1) hc (hWp i h1 h2 c' hc))
    have hsum0 : ∑ i ∈ Finset.Icc j k, (fun _ _ => (0 : ℝ)) i k * ‖hRRX R m b μ₀ oR x X i‖ = 0 := by
      simp
    rw [hsum0, add_zero]
    refine hM.trans ?_
    unfold smE3
    refine PtCorr2.mem_conv_le _ (fun i => Pd i * τ i k + PtCorr2.memKer (R.withMsq m) t i k *
      (F i + 2 * Wp i)) β (64 / 49) (fun i => ?_)
      (fun i _ => le_of_eq (by ring)) hratio
    obtain ⟨-, -, -, -, -, -, -, hP0, hF0, hW0⟩ := h0 i
    exact add_nonneg (mul_nonneg hP0 (hτ0 i k)) (mul_nonneg
      (PtCorr2.memKer_nonneg (R.withMsq m) hρ0 hρ8 t i k)
      (add_nonneg hF0 (mul_nonneg zero_le_two hW0)))
  exact ⟨hG k hkN, hQ, hWk, hP, hGr, hM⟩

end Traj

end

end Spin2
