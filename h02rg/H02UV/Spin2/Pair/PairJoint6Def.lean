import Spin2.Pair.PairJoint4
import PtCorr2.Pair.PairEStep1

/-!
# `PairDefSizesR3` without the false `Q'` locality item

`PairDefSizesR3` asks `Q'_k(B)_{ab} ∈ 𝒩(B^□)`; at `k = j_x` this can fail (the point `b` may lie
outside `B_a^□`, see `PtCorr2.Pair.PairEStep1`). It is used only in the expectation bound of the
`ε`-part of `wkAB2`, which holds for `F ∈ 𝒩({a,b})` as well (`|𝓑({a,b})| ≤ 2`), and
`Q'_k(B)_{ab} ∈ 𝒩({a,b})` always (`Obs2.Q2O_ab_mem_pair`). The `𝒲'_k(B)_{ab} ∈ 𝒩(B^□)` item is
true (`OLocS.hW`, `PtCorr2.olocS_hR`) and is kept.

* **`norm_eps_expLC_le_pair`**: `|ε(e^{ℒ_C}F)| ≤ Q₁‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩({a,b})`;
* **`norm_wkAB2_leP`**: `norm_wkAB2_le` without the `Q'` locality hypothesis;
* **`PairDefSizesR3P`** (`PairDefSizesR3` without the `Q'` locality item; `pairDefSizesR3P_of_R3`),
  **`pairDefSumR_of_sizes3P`**, **`pairDefSumR_of_sizes3P_MF`**.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {d L N : ℕ} [NeZero L]

/-- `|ε(e^{ℒ_C}F)| ≤ Q₁‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩({a,b})`. -/
theorem norm_eps_expLC_le_pair (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C)
    (a b : Lam d L N) {F : Alg d L N} (hF : F ∈ NX ({a, b} : Set (Lam d L N))) :
    ‖ε (expLC C F)‖ ≤ Q1 d * (Tj d (L : ℝ) j ℓ F).toReal := by
  have hF' : F ∈ NX (↑({a, b} : Finset (Lam d L N)) : Set (Lam d L N)) := by
    rw [Finset.coe_pair]; exact hF
  have h1 := norm_eps_le hℓ (j + 1) (expLC C F)
  have h2 := EthE_succ_le hd hL hj hℓ hC hF'
  rw [ECC_theta] at h2
  have hnb : nb j ({a, b} : Finset (Lam d L N)) ≤ (2 ^ (d + 1) + 3) ^ d := by
    unfold nb blocks
    refine (card_image_le).trans ((card_le_two).trans ?_)
    calc 2 ≤ 2 ^ (d + 1) + 3 := by have := Nat.one_le_two_pow (n := d + 1); omega
      _ ≤ (2 ^ (d + 1) + 3) ^ d := Nat.le_self_pow (by omega) _
  have h3 : ENNReal.ofReal (pq d ^ nb j ({a, b} : Finset (Lam d L N))) *
      Tj d (L : ℝ) j ℓ F ≤ ENNReal.ofReal (Q1 d) * Tj d (L : ℝ) j ℓ F :=
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (one_le_pq hd) hnb)) _
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tNorm_ne_top (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) j) hℓ F))
    (h2.trans h3)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := one_le_Q1 hd; linarith)] at h4
  exact h1.trans h4

/-- **`|wkAB2| ≤ 2Q₁q̄ + 2Q₁w̄`** on anchored inputs, without the `Q'` locality hypothesis. -/
theorem norm_wkAB2_leP (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) (P : ObsPts d L N) {k : ℕ} (hk : k < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ q w : ℝ} (hℓ : 0 < ℓ) (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hC : GoodCov2 k ℓ C) {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P k V W K)
    (hQ : ∀ b, Tj d (L : ℝ) k ℓ (Q2O P k K b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal q)
    (hlocW : ∀ b, (W b : SA .two (Lam d L N)).ab ∈
      NX (nbhd k (blockSet (L := L) (N := N) k b) : Set (Lam d L N)))
    (hW : ∀ b, Tj d (L : ℝ) k ℓ (W b : SA .two (Lam d L N)).ab ≤ ENNReal.ofReal w) :
    ‖wkAB2 P k C W K‖ ≤ 2 * (Q1 d * q) + 2 * (Q1 d * w) := by
  unfold wkAB2
  have hQ1 := one_le_Q1 hd
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine norm_sum_two_le _ _ (blk k P.a) (blk k P.b) (by positivity)
      (fun b _ h1 h2 => by rw [ab_eq_zero_of_anch P (H.Q2O_anch b) h1 h2, map_zero, map_zero])
      fun b _ => ?_
    refine (norm_eps_expLC_le_pair hd hL hk hℓ hC P.a P.b (Q2O_ab_mem_pair P k K b)).trans ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQ b)
    rw [ENNReal.toReal_ofReal hq] at this
    gcongr
  · refine norm_sum_two_le _ _ (blk k P.a) (blk k P.b) (by positivity)
      (fun b _ h1 h2 => by
        rw [(EthO_comp C (W b)).2.2, ab_eq_zero_of_anch P (H.hW b) h1 h2, map_zero, map_zero])
      fun b _ => ?_
    rw [(EthO_comp C (W b)).2.2]
    refine (norm_eps_expLC_le hd hL hk hℓ hC (hlocW b)).trans ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hW b)
    rw [ENNReal.toReal_ofReal hw] at this
    gcongr

end

end PtCorr2

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Named input (`P`-variant of `PairDefSizesR3`)**: without the item `Q'_k(B)_{ab} ∈ 𝒩(B^□)`. -/
def PairDefSizesR3P (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cd : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (ℓs sq sw sp sf : ℕ → ℝ) (M4 : ℕ → ℂ) (sL : ℝ),
      (∀ k, 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sf k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
        let C := Obs2.histCovO (R.withMsq m) t
        let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let K := PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        GoodCov2 k (ℓs k) (C k) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sq k)) ∧
        (∀ B, (W k B : Obs.SA .two (Lam 2 L N)).ab ∈
          NX (nbhd k (blockSet (L := L) (N := N) k B) : Set (Lam 2 L N))) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (W k B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sw k)) ∧
        ‖Obs2.pdefAB2 (ptsX x) k (C k) (V k) -
            M4 k * (C k 0 0 * C k x x - C k 0 x * C k x 0)‖ ≤ sp k ∧
        ‖ε (FC (C k) (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).ab
          (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sf k) ∧
      ‖lastDefR R Nh m b μ₀ oR x‖ ≤ sL ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k +
            ‖M4 k‖ * (2 * ℓs k ^ 2 *
              ((L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2)) +
          sL ≤
        cd * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

set_option maxHeartbeats 1000000 in
/-- **`PairDefSumR` from `PairDefSizesR3P`** (copy of `pairDefSumR_of_sizes3` with
`norm_wkAB2_leP`). -/
theorem pairDefSumR_of_sizes3P {Nh : ℕ} (hN : Nh + 2 = N) (hL : pauliL0 2 ≤ L) (hL2 : 2 ≤ L)
    (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cd : ℝ}
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hS : PairDefSizesR3P R Nh m b μ₀ lam oR cd) :
    PairDefSumR R Nh m b μ₀ lam oR cd := by
  intro x hx h1 hj
  obtain ⟨ℓs, sq, sw, sp, sf, M4, sL, h0, hk, hlast, hsum⟩ := hS x hx h1 hj
  have hanc := hA x hx h1 hj
  set jx := Obs.coal L (0 : Lam 2 L N) x with hjx
  set C := Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) with hCdef
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (0 : Lam 2 L N) w = x := by rw [Obs2.pathEnd, zero_add, hwx]
  have hlen : (w.length : ℝ) ≤ (L : ℝ) ^ (jx + 1) := by
    have h2 := two_supNorm_lt_coal hL2 x
    rw [sub_zero] at h2
    have : w.length ≤ L ^ (jx + 1) := hwl.trans h2.le
    exact_mod_cast this
  have hstep : ∀ k ∈ Finset.Ico jx (Nh + 1), ‖hDefR R m b μ₀ oR x k‖ ≤
      2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k +
        ‖M4 k‖ * (2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2) := by
    intro k hk'
    obtain ⟨hl, hq, hw, hp, hf⟩ := h0 k
    obtain ⟨hC, hQ, hlocW, hW, hP, hF⟩ := hk k hk'
    have hjk : jx ≤ k := (Finset.mem_Ico.1 hk').1
    have hkN : k < N := by have := (Finset.mem_Ico.1 hk').2; omega
    have H := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hjk
    have hfar := Obs2.farAB_eq_zero_of_anch (C := C k) H
    have hwk := PtCorr2.norm_wkAB2_leP one_le_two hL (ptsX x) hkN hl hq hw hC H hQ hlocW hW
    rw [hDefR_eq R m b μ₀ oR x H.toAb]
    unfold Obs2.xAB2
    rw [hfar, sub_zero]
    have hdet := Obs2.norm_detDef_le2 hC 0 w
    rw [hpe] at hdet
    have hdet' : ‖C k 0 0 * C k x x - C k 0 x * C k x 0‖ ≤
        2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2 := by
      refine hdet.trans ?_
      have h3 : 0 ≤ ℓs k / (L : ℝ) ^ (k + 1) := by have := hl.le; positivity
      have h4 : (w.length : ℝ) * (ℓs k / (L : ℝ) ^ (k + 1)) ≤
          (L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1)) := mul_le_mul_of_nonneg_right hlen h3
      have h5 : 0 ≤ (w.length : ℝ) * (ℓs k / (L : ℝ) ^ (k + 1)) := by positivity
      have h6 := pow_le_pow_left₀ h5 h4 2
      have h7 : 0 ≤ 2 * ℓs k ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left h6 h7
    have hMd : ‖M4 k * (C k 0 0 * C k x x - C k 0 x * C k x 0)‖ ≤
        ‖M4 k‖ * (2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2) := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hdet' (norm_nonneg _)
    have key : ∀ A B Cw D : ℂ, ‖-A + (Cw + D)‖ ≤ ‖A - B‖ + ‖B‖ + ‖Cw‖ + ‖D‖ := by
      intro A B Cw D
      have e : -A + (Cw + D) = -(A - B) - B + Cw + D := by ring
      rw [e]
      have n1 := norm_add_le (-(A - B) - B + Cw) D
      have n2 := norm_add_le (-(A - B) - B) Cw
      have n3 := norm_sub_le (-(A - B)) B
      rw [norm_neg] at n3
      linarith
    refine (key _ (M4 k * (C k 0 0 * C k x x - C k 0 x * C k x 0)) _ _).trans ?_
    refine (add_le_add (add_le_add (add_le_add hP hMd) hwk) hF).trans (le_of_eq ?_)
    ring
  calc ∑ k ∈ Finset.Ico jx (Nh + 1), ‖hDefR R m b μ₀ oR x k‖ + ‖lastDefR R Nh m b μ₀ oR x‖
      ≤ ∑ k ∈ Finset.Ico jx (Nh + 1), (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k +
        ‖M4 k‖ * (2 * ℓs k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓs k / (L : ℝ) ^ (k + 1))) ^ 2)) + sL :=
        add_le_add (Finset.sum_le_sum hstep) hlast
    _ ≤ _ := hsum

end Traj

/-- **`PairDefSumR` for `oRed … dxStd` from `PairDefSizesR3P`** (`L` from `MasterFacts`). -/
theorem pairDefSumR_of_sizes3P_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} (hNh : Nh + 2 = N)
    (m b μ₀ : ℝ) (lam : ℕ → ℂ) {cd : ℝ}
    (hS : PairDefSizesR3P R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd) :
    PairDefSumR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd :=
  pairDefSumR_of_sizes3P R hNh M.core.hLpl (by have := M.core.hL49; omega) m b μ₀ lam _
    (pairAnchR_oRed R Nh m b μ₀) hS

end

end Spin2
