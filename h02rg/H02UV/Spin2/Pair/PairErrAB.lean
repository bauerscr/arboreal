import Spin2.Pair.PairPR5d
import Spin2.Pair.PairSect
import PtCorr2.Pair.ObsHistAnch
import Obs2.Est.ErrAB

/-!
# `PairErrRelR` reduced to the `ab` sizes of the reduced history

Along the reduced history `obsHistFrom j_x (oR x)` from an anchored state (`ObsAnchInv`):

* `PtCorr2.oanchS_hR`: the inputs `hVR k`, `hWR k`, `hKR k` of every step `k ≥ j` are anchored;
  **`PtCorr2.farABm_hR_eq_zero`**: the far-block term of `errAB` vanishes;
* `PairAnchR` (anchoring of the reduced states at `j_x`) and **`pairAnchR_oRed`**: it holds for the
  reduced states built from the standard covering polymers `dxStd` (`obsAnchInv_redSt`);
* **`PairErrSizesR c_e`** (named input, the remainder of `PairErrRelR` once the `ab` step chain
  lands): at every `k ∈ [j_x, N_h]`, with a field scale `ℓ_k` and `GoodCov2 k ℓ_k C_k`,
  - `‖Q'_k(B)_{ab}‖_{T_k(ℓ_k)} ≤ ŝ^q_k‖β_{a,k+1}‖` (`Q' = ∑_{X ⊇ B}Loc_{X,B}K'_k(X)`, the `ab`
    size of `K'_k`; `Q'_k(B)_{ab}` local in `B^□`),
  - `‖𝒲'_k(B)_{ab}‖_{T_k(ℓ_k)} ≤ ŝ^w_k‖β_{a,k+1}‖` (the `ab` size of `𝒲'_k`),
  - `|𝔡₂_k||1 - n_{a,k}| ≤ s^p_k‖β_{a,k+1}‖`, `|m₂F_{C_k}(D_k, V'_∅)| ≤ s^g_k‖β_{a,k+1}‖`,
    `∑_{j≤i<k}|memAB(i,k)| ≤ s^m_k‖β_{a,k+1}‖`,
  - `∑_k(2Q₁ℓ_k^{-2}ŝ^q_k + 2ℓ_k^{-2}ŝ^w_k + s^p_k + s^g_k + s^m_k) ≤ c_e‖M_j‖ǧ_j`;
* **`pairErrRelR_of_sizes`**: `PairAnchR` and `PairErrSizesR c_e` give `PairErrRelR c_e`
  (`norm_qAB_le`, `norm_wTadAB0_le`: only the blocks of `a`, `b` carry `ab` parts; `farABm = 0`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) {j : ℕ} {o' : ObsSt .two L N}

/-- The inputs of every step of the reduced history are anchored. -/
theorem oanchS_hR (h0 : ObsAnchInv P j o') (t : Hist.Seq (Xs R)) {k : ℕ} (hk : j ≤ k) :
    OAnchS P k (hVR R P j o' t k) (hWR R P j o' t k) (hKR R P j o' t k) := by
  have h := obsAnchInv_histFrom R P h0 t (k - j)
  rw [Nat.add_sub_cancel' hk] at h
  exact oanchS_full R P _ _ h

/-- **The far-block term vanishes along the reduced history.** -/
theorem farABm_hR_eq_zero (h0 : ObsAnchInv P j o') (t : Hist.Seq (Xs R)) {k : ℕ} (hk : j ≤ k) :
    farABm P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) = 0 :=
  farABm_eq_zero_of_anch (oanchS_hR R P h0 t hk)

end

end PtCorr2

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The reduced states are anchored at coalescence.** -/
def PairAnchR (Nh : ℕ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    PtCorr2.ObsAnchInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)

/-- `PairAnchR` for the reduced states of the standard covering polymers. -/
theorem pairAnchR_oRed (Nh : ℕ) (m b μ₀ : ℝ) :
    PairAnchR (L := L) (N := N) Nh (oRed R m b μ₀ (dxStd (L := L) (N := N))) :=
  fun x hx h1 hj => PtCorr2.obsAnchInv_redSt (R.withMsq m) (ptsX x) _ _
    (pairDCov_std (L := L) (N := N) Nh x hx h1 hj)

/-- **Named input: the `ab` sizes of the reduced history** (what remains of `PairErrRelR` once
the `ab` step chain bounds `K'`, `𝒲'`, the Pauli and gradient defects and the memory terms). -/
def PairErrSizesR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (ce : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ ℓs sq sw sp sg sm : ℕ → ℝ,
      (∀ k, 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sg k ∧ 0 ≤ sm k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
        let C := Obs2.histCovO (R.withMsq m) t
        let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let K := PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let β := ‖hBeta R m b μ₀ x (k + 1)‖
        GoodCov2 k (ℓs k) (C k) ∧
        (∀ B, (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ∈
          NX (nbhd k (blockSet (L := L) (N := N) k B) : Set (Lam 2 L N))) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sq k * β)) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (W k B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sw k * β)) ∧
        ‖Obs2.pdefM2 k (C k) (V k)‖ * ‖1 - Obs2.nA2 (ptsX x) k (C k) (V k)‖ ≤ sp k * β ∧
        ‖Obs.LocObs.mass2 (Grassmann.FC (C k) (Obs2.dAB (ptsX x) k (C k) (V k))
          (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sg k * β ∧
        ∑ i ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) k,
          ‖Obs2.memAB (ptsX x) C V W i k‖ ≤ sm k * β) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + 2 * (sw k * (ℓs k)⁻¹ ^ 2) + sp k + sg k + sm k) ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- **`PairErrRelR` from the `ab` sizes** of the reduced history. -/
theorem pairErrRelR_of_sizes {Nh : ℕ} (hN : Nh + 2 = N) (hL : pauliL0 2 ≤ L) (m b μ₀ : ℝ)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce : ℝ}
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hS : PairErrSizesR R Nh m b μ₀ lam oR ce) :
    PairErrRelR R Nh m b μ₀ lam oR ce := by
  intro x hx h1 hj
  obtain ⟨ℓs, sq, sw, sp, sg, sm, h0, hk, hsum⟩ := hS x hx h1 hj
  have hanc := hA x hx h1 hj
  refine ⟨fun k => 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + 2 * (sw k * (ℓs k)⁻¹ ^ 2) + sp k + sg k +
    sm k, fun k => ?_, fun k hk' => ?_, hsum⟩
  · obtain ⟨hl, hq, hw, hp, hg, hm⟩ := h0 k
    have hQ := one_le_Q1 (d := 2) one_le_two
    have a1 : 0 ≤ Q1 2 * sq k * (ℓs k)⁻¹ ^ 2 := mul_nonneg (mul_nonneg (by linarith) hq) (sq_nonneg _)
    have a2 : 0 ≤ sw k * (ℓs k)⁻¹ ^ 2 := mul_nonneg hw (sq_nonneg _)
    linarith
  obtain ⟨hl, hq, hw, hp, hg, hm⟩ := h0 k
  obtain ⟨hC, hloc, hQ, hW, hP, hG, hM⟩ := hk k hk'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  set β := ‖hBeta R m b μ₀ x (k + 1)‖
  have hβ : 0 ≤ β := norm_nonneg _
  have hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k := (Finset.mem_Ico.1 hk').1
  have hkN : k < N := by have := (Finset.mem_Ico.1 hk').2; omega
  have H := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hjk
  have hf := PtCorr2.farABm_hR_eq_zero (R.withMsq m) (ptsX x) hanc t hjk
  have hq' := Obs2.norm_qAB_le one_le_two hL (ptsX x) hkN hl (mul_nonneg hq hβ) hC H hloc hQ
  have hw' := Obs2.norm_wTadAB0_le (ptsX x) H.hW hl (mul_nonneg hw hβ) hW
  have he := Obs2.norm_errAB_le (ptsX x) (Obs2.histCovO (R.withMsq m) t)
    (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t)
    (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t)
    (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t)
    (Obs.coal L (0 : Lam 2 L N) x) k hf
  show ‖hErrR R m b μ₀ oR x k‖ ≤ _
  refine he.trans ?_
  have e1 : 2 * (Q1 2 * (sq k * β) * (ℓs k)⁻¹ ^ 2) = 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) * β := by
    ring
  have e2 : 2 * (sw k * β * (ℓs k)⁻¹ ^ 2) = 2 * (sw k * (ℓs k)⁻¹ ^ 2) * β := by ring
  rw [e1] at hq'
  rw [e2] at hw'
  calc _ ≤ 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) * β + 2 * (sw k * (ℓs k)⁻¹ ^ 2) * β +
        sp k * β + sg k * β + sm k * β := by
        gcongr
    _ = _ := by ring

end Traj

end

end Spin2
