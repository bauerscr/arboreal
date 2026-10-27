import Spin2.Pair.PairEStep4
import PtCorr2.Pair.PairEStep2
import PtCorr2.Obs.ObsFlow

/-!
# The `M₄` seed term of `PairDefSizesR3`

The seed term of `PairDefSizesR3` is
`∑_{j_x≤k≤N_h}|M₄_k|·2ℓ_k²(L^{j_x+1}ℓ_k/L^{k+1})²` with `M₄_k = m4Tot(V'_k)` and `ℓ_k` the scale of
the `GoodCov2` item, i.e. the field scale `s_k = histS` of the history (not monotone).

* **`histS_le_pow`**: `s_k ≤ (9/8)^{k-i}s_i` (`histS_ratio_le`, `ρ ≤ 1/8`);
* **`pairDefSeed_le`**: along the reduced history, the seed term is
  `≤ 16∑_kK_{M4}((9/8)⁴κ^Q_k + κ^S_k)` (`PtCorr2.m4_hist_weighted_sizes_q` with `q = 9/8`,
  `q⁴L^{-2} ≤ 1/4` for `L ≥ 3`), where `κ^Q_k ≥ ∑_B∑_{X⊇B}‖K_k(X)_{ab}‖_{T_k(s_k)}` and
  `κ^S_k ≥ ∑_B‖S_k(B_+)_{ab}‖_{T_{k+1}(s_{k+1})}` (the `ab` sizes of the activity and of `S`);
* **`pairDefSeed_MF`**: the same for the reduced states `oRed … dxStd` along every admissible
  trajectory of `MasterFacts` (validity, `U(1)` invariance, `ρ ≤ 1/8` discharged).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **The field scale grows at most by `9/8` per step**: `s_k ≤ (9/8)^{k-i}s_i`. -/
theorem histS_le_pow (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hρ0 : 0 ≤ R.ρ)
    (hρ8 : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ i k, i ≤ k → PtCorr2.histS R k t ≤ (9 / 8 : ℝ) ^ (k - i) * PtCorr2.histS R i t := by
  have hstep : ∀ l, PtCorr2.histS R (l + 1) t ≤ 9 / 8 * PtCorr2.histS R l t := by
    intro l
    have h1 := PtCorr2.histS_ratio_le R hρ0 (by linarith) l t
    have hz : ‖zetaH R l t‖ ≤ R.ρ := absorb_le R hρ0 _ _
    have hs := PtCorr2.histS_pos' R hρ0 hρ8 t l
    have h2 : PtCorr2.histS R (l + 1) t / PtCorr2.histS R l t ≤ 9 / 8 :=
      (le_max_right _ _).trans (h1.trans (by linarith))
    rwa [div_le_iff₀ hs] at h2
  intro i k hik
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
    calc PtCorr2.histS R (k + 1) t ≤ 9 / 8 * PtCorr2.histS R k t := hstep k
      _ ≤ 9 / 8 * ((9 / 8 : ℝ) ^ (k - i) * PtCorr2.histS R i t) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by ring

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The `M₄` seed term of `PairDefSizesR3` along the reduced history.** -/
theorem pairDefSeed_le {Nh : ℕ} (hN : Nh + 2 = N) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (m b μ₀ : ℝ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (hx : x ≠ 0)
    (hVab : PtCorr2.ObsVabInv (ptsX x) (oR x))
    (hz : ∀ B, ((oR x).V B : Obs.SA .two (Lam 2 L N)).ab = 0)
    (hsym : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      PtCorr2.ObsSymInv k (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (oR x) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hρ0 : 0 ≤ (R.withMsq m).ρ) (hρ8 : (R.withMsq m).ρ ≤ 1 / 8)
    {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hKl : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 → ∀ X, IsSmall k X →
      (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k X : Obs.SA .two (Lam 2 L N)).ab ∈
        NX (nbhd k X : Set (Lam 2 L N)))
    (hSl : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      ∀ c ∈ blockIdx (L := L) (N := N) k,
      (Obs2.SXO k (Obs2.histCovO (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
        (Step2.Bp (L := L) (N := N) k c) : Obs.SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (k + 1) (Step2.Bp (L := L) (N := N) k c) : Set (Lam 2 L N)))
    (κQ κS : ℕ → ℝ) (hκQ0 : ∀ k, 0 ≤ κQ k) (hκS0 : ∀ k, 0 ≤ κS k)
    (hκQ : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      (open Classical in ∑ c ∈ blockIdx (L := L) (N := N) k,
        ∑ X ∈ (smallSets k).filter (fun X => blockSet k c ⊆ X),
          (Tj 2 (L : ℝ) k (PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k X : Obs.SA .two (Lam 2 L N)).ab).toReal) ≤
        κQ k)
    (hκS : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      ∑ c ∈ blockIdx (L := L) (N := N) k,
        (Tj 2 (L : ℝ) (k + 1)
          (PtCorr2.histS (R.withMsq m) (k + 1) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs2.SXO k (Obs2.histCovO (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
              (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (Step2.Bp (L := L) (N := N) k c) : Obs.SA .two (Lam 2 L N)).ab).toReal ≤ κS k) :
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ‖Obs2.m4Tot (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
          (oR x) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ *
          (2 * PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ((L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x + 1) *
              (PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
                (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        Obs2.KM4 2 Cc * ((9 / 8 : ℝ) ^ 4 * κQ k + κS k) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by norm_num at hL; omega)
  have hab : (ptsX x).a ≠ (ptsX x).b := fun h => hx h.symm
  have hqL : (9 / 8 : ℝ) ^ 4 * ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast (show 3 ≤ L by norm_num at hL; omega)
    have hL9 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    norm_num
    nlinarith
  exact PtCorr2.m4_hist_weighted_sizes_q (R.withMsq m) (ptsX x) _ (oR x)
    (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hL2 hCc0 hCc hL hab hVab hz (by omega) hsym
    (PtCorr2.pow_coal_le_two_supNorm hab) _ (fun k => PtCorr2.histS_pos' (R.withMsq m) hρ0 hρ8 _ k)
    (by norm_num) hqL (histS_le_pow (R.withMsq m) hρ0 hρ8 _) hKl hSl κQ κS hκQ0 hκS0 hκQ hκS

end Traj

/-- The cutoff derivative constant (`d = 2`, `|α| ≤ p_Φ`, `m_i ≤ 1`). -/
def CcutE : ℝ := Classical.choose (exists_D1_cutP_bound 2 (pPhi 2) 1)

theorem CcutE_spec : 0 ≤ CcutE ∧ ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → ∀ a : Dir 2 → ℕ, Grassmann.mabs a ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) a (cutP m R) u| ≤ CcutE * R ^ (∑ i, m i) / R ^ Grassmann.mabs a :=
  Classical.choose_spec (exists_D1_cutP_bound 2 (pPhi 2) 1)

set_option maxHeartbeats 4000000 in
/-- **The `M₄` seed term of `PairDefSizesR3` for the reduced states under `MasterFacts`**: only
the `ab` sizes `κ^Q`, `κ^S` of the activity and of `S` remain. -/
theorem pairDefSeed_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    (κQ κS : ℕ → ℝ) (hκQ0 : ∀ k, 0 ≤ κQ k) (hκS0 : ∀ k, 0 ≤ κS k)
    (hκQ : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      (open Classical in ∑ c ∈ blockIdx (L := L) (N := N) k,
        ∑ X ∈ (smallSets k).filter (fun X => blockSet k c ⊆ X),
          (Tj 2 (L : ℝ) k
            (PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
              (oRed R m b μ₀ dxStd x)
              (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k X : Obs.SA .two (Lam 2 L N)).ab).toReal) ≤
        κQ k)
    (hκS : ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < Nh + 1 →
      ∑ c ∈ blockIdx (L := L) (N := N) k,
        (Tj 2 (L : ℝ) (k + 1)
          (PtCorr2.histS (R.withMsq m) (k + 1) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs2.SXO k (Obs2.histCovO (R.withMsq m) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
              (oRed R m b μ₀ dxStd x) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
              (oRed R m b μ₀ dxStd x) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
            (Step2.Bp (L := L) (N := N) k c) : Obs.SA .two (Lam 2 L N)).ab).toReal ≤ κS k) :
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        ‖Obs2.m4Tot (ptsX x) k (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
          (oRed R m b μ₀ dxStd x) (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ *
          (2 * PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ((L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x + 1) *
              (PtCorr2.histS (R.withMsq m) k (Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
                (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        Obs2.KM4 2 CcutE * ((9 / 8 : ℝ) ^ 4 * κQ k + κS k) := by
  have hL49 : 49 ≤ L := M.core.hL49
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := Hist.traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    with ht
  have hloc0 := (hRd x hx h1 hj).2.1
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  have hloc' : ∀ k, j ≤ k → k ≤ Nh → Obs2.OLocS (ptsX x) k
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) := fun k hk hkN =>
    PtCorr2.olocS_hR (R.withMsq m) (ptsX x) t hloc0 hk fun i' _ hi' => hRI i' (by omega)
  exact pairDefSeed_le R hNh (by omega) m b μ₀ (oRed R m b μ₀ dxStd) x hx
    (PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)) (fun B => oRed_V_ab_zero R m b μ₀ dxStd x B)
    (fun k hk hkN => PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk
      fun i _ hi => hRI i (by omega))
    hVL.2.2.2.2.1 hVL.2.2.2.2.2.1 CcutE_spec.1 CcutE_spec.2
    (fun k hk hkN X hX => ((hloc' k hk (by omega)).hK X ⟨hX.1, hX.2.1⟩).2.2.2.1)
    (fun k hk hkN c _ => ((hloc' k hk (by omega)).SX_mem one_le_two (by norm_num; omega)
      (by omega) (fun u v h => (hG k (by omega)).range (by omega) u v h) c).2.2.2.1)
    κQ κS hκQ0 hκS0 hκQ hκS

end

end Spin2
