import Spin2.Pair.PairErrAB
import Spin2.Pair.PairDefAB
import PtCorr2.Obs.GamWKBd
import PtCorr2.Pair.PairDGeom2

/-!
# `PairDefSumR` reduced to the `ab` sizes of the reduced history (copy of `pairErrRelR_of_sizes`)

On the reduced history (`ρ_a = ρ_b = 0`) the defect of step `k` is (exactly)
`hDefR_k = -𝔡_k + X_k`, `𝔡_k = pdefAB2 = ∑_B𝔡^a_{C_k}(V_k(B)_{ab})`,
`X_k = wkAB2 + εF_{C_k}(V'_{k,ab}, V'_{k,∅}) - farAB`.

* `farAB_eq_zero_of_anch`: `farAB = 0` on anchored inputs (`ε`-copy of `farABm_eq_zero_of_anch`);
* `rhoA2_eq_zero_of_ab`: `ρ_a = 0` without one-point parts;
* **`norm_wkAB2_le`**: `|wkAB2| ≤ 2Q₁q̄ + 2Q₁w̄` on anchored inputs with `‖Q(B)_{ab}‖ ≤ q̄`,
  `‖𝒲(B)_{ab}‖ ≤ w̄` (local in `B^□`; `ε`-copies of `norm_qAB_le`, `norm_wTadAB0_le` via
  `PtCorr2.norm_eps_expLC_le`);
* **`hDefR_eq`**: `hDefR_k = -pdefAB2 + xAB2` along the reduced history;
* `two_supNorm_lt_coal`, **`nb_dxStd_le`**: `|𝓑_{j_x}(D_x)| ≤ (L + 18)²` for the standard covering
  polymers (task: `|𝓑(dxStd x)| = O(L²)`);
* **`PairDefSizesR c_d`** (named input): at `k ∈ [j_x, N_h]`, `GoodCov2 k ℓ_k C_k` with `ℓ_k ≤ ℓ̄`,
  the `ab` sizes `ŝ^q_k`, `ŝ^w_k` of `Q'_k`, `𝒲'_k` (local in `B^□`), a split of the Pauli
  defect `‖𝔡_k - M_{4,k}(C_k(0,0)C_k(x,x) - C_k(0,x)C_k(x,0))‖ ≤ s^p_k` with `|M_{4,k}| ≤ M̄`
  (the seed part: coefficient of `ψ̄_0ψ_0ψ̄_xψ_x`), `|εF_{C_k}(V'_{ab}, V'_∅)| ≤ s^f_k`, the last
  step `|lastDefR| ≤ s^L`, and
  `∑_k(2Q₁ŝ^q_k + 2Q₁ŝ^w_k + s^p_k + s^f_k) + M̄·2Lℓ̄⁴/(L-1) + s^L ≤ c_d‖M_j‖²ǧ_j`;
* **`pairDefSumR_of_sizes`**: `PairAnchR` + `PairDefSizesR c_d` ⇒ `PairDefSumR c_d`. The seed sum
  `∑_k|detDef_k| ≤ 2Lℓ̄⁴/(L-1)` is `seed_detDef_sum_le` along a lattice path `0 → x` with
  `≤ 2|x|_∞ < L^{j_x+1}` steps (`PtCorr2.exists_path_sum`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD ENNReal

variable {d L N : ℕ} [NeZero L]

/-- **`farAB = 0` on anchored inputs.** -/
theorem farAB_eq_zero_of_anch {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P j V W K) :
    farAB P j C V W = 0 := by
  unfold farAB
  refine sum_eq_zero fun c' _ => ?_
  split_ifs with h
  · rfl
  · rw [SXO, AddSubmonoidClass.coe_finsetSum, SA.sum_ab, map_sum]
    refine sum_eq_zero fun b hb => ?_
    have hsub : blockSet (L := L) (N := N) j b ⊆ blockSet (L := L) (N := N) (j + 1) c' :=
      blockSet_subset_of_mem_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb
    rw [(H.Sb_anch (C := C) b).2.2 fun hne => h (hne.mono (inter_subset_inter_right hsub)),
      map_zero]

/-- `ρ_a = 0` without one-point parts. -/
theorem rhoA2_eq_zero_of_ab (P : ObsPts d L N) {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
    {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAbS j V W K) :
    rhoA2 P j C V W K = 0 := by
  unfold rhoA2 wkA2
  have h1 : ∀ b, (Q2O P j K b : SA .two (Lam d L N)).a = 0 := fun b => (H.Q2O_ab (P := P) b).1
  have h2 : ∀ b, (EthO C (W b) : SA .two (Lam d L N)).a = 0 := fun b => (EthO_mem_ab C (H.hW b)).1
  have h3 : (VprLO j C V : SA .two (Lam d L N)).a = 0 := (H.VprL_ab (C := C)).1
  simp only [h1, h2, h3, map_zero, sum_const_zero, zero_add]
  simp [FC]

/-- **`|wkAB2| ≤ 2Q₁q̄ + 2Q₁w̄`** on anchored inputs. -/
theorem norm_wkAB2_le (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) (P : ObsPts d L N) {k : ℕ} (hk : k < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} {ℓ q w : ℝ} (hℓ : 0 < ℓ) (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hC : GoodCov2 k ℓ C) {V W : OFam .two d L N} {K : OAct .two d L N} (H : OAnchS P k V W K)
    (hlocQ : ∀ b, (Q2O P k K b : SA .two (Lam d L N)).ab ∈
      NX (nbhd k (blockSet (L := L) (N := N) k b) : Set (Lam d L N)))
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
    refine (PtCorr2.norm_eps_expLC_le hd hL hk hℓ hC (hlocQ b)).trans ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQ b)
    rw [ENNReal.toReal_ofReal hq] at this
    gcongr
  · refine norm_sum_two_le _ _ (blk k P.a) (blk k P.b) (by positivity)
      (fun b _ h1 h2 => by
        rw [(EthO_comp C (W b)).2.2, ab_eq_zero_of_anch P (H.hW b) h1 h2, map_zero, map_zero])
      fun b _ => ?_
    rw [(EthO_comp C (W b)).2.2]
    refine (PtCorr2.norm_eps_expLC_le hd hL hk hℓ hC (hlocW b)).trans ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hW b)
    rw [ENNReal.toReal_ofReal hw] at this
    gcongr

end

end Obs2

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- `2|x|_∞ < L^{j_x+1}`. -/
theorem two_supNorm_lt_coal (hL : 2 ≤ L) (x : Lam 2 L N) :
    2 * supNorm (x - 0) < L ^ (Obs.coal L (0 : Lam 2 L N) x + 1) := by
  unfold Obs.coal
  rw [supNorm_sub_comm (0 : Lam 2 L N) x]
  exact Nat.lt_pow_succ_log_self (by omega) _

/-- **`|𝓑_{j_x}(D_x)| ≤ (L + 18)²`** for the standard covering polymers. -/
theorem nb_dxStd_le (hL : 2 ≤ L) (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ N) :
    nb (Obs.coal L (0 : Lam 2 L N) x) (dxStd (L := L) (N := N) x) ≤ (L + 18) ^ 2 :=
  PtCorr2.nb_ballPoly_coal_le hj 0 x (two_supNorm_lt_coal hL x)

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The defect of step `k` of the reduced history** is `-𝔡_k + X_k` (`ρ_a = 0`). -/
theorem hDefR_eq (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    {k : ℕ} (H : Obs2.OAbS k
      (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)) :
    hDefR R m b μ₀ oR x k =
      -Obs2.pdefAB2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) +
        Obs2.xAB2 (ptsX x) k (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)
          (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) := by
  unfold hDefR PtCorr2.incR hRR hC00
  rw [Obs2.rhoA2_eq_zero_of_ab (ptsX x) H, zero_mul, add_zero]
  have ha : (ptsX x : Obs2.ObsPts 2 L N).a = 0 := rfl
  rw [ha]
  ring

/-- **Named input: the `ab` sizes of the reduced history for the defects** (what remains of
`PairDefSumR` once the `ab` step chain lands). -/
def PairDefSizesR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cd : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (ℓs sq sw sp sf : ℕ → ℝ) (M4 : ℕ → ℂ) (ℓb Mb sL : ℝ),
      0 ≤ ℓb ∧ 0 ≤ Mb ∧
      (∀ k, 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sf k) ∧
      (∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
        let C := Obs2.histCovO (R.withMsq m) t
        let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        let K := PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
        GoodCov2 k (ℓs k) (C k) ∧ ℓs k ≤ ℓb ∧
        (∀ B, (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ∈
          NX (nbhd k (blockSet (L := L) (N := N) k B) : Set (Lam 2 L N))) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sq k)) ∧
        (∀ B, (W k B : Obs.SA .two (Lam 2 L N)).ab ∈
          NX (nbhd k (blockSet (L := L) (N := N) k B) : Set (Lam 2 L N))) ∧
        (∀ B, Tj 2 (L : ℝ) k (ℓs k) (W k B : Obs.SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (sw k)) ∧
        ‖M4 k‖ ≤ Mb ∧
        ‖Obs2.pdefAB2 (ptsX x) k (C k) (V k) -
            M4 k * (C k 0 0 * C k x x - C k 0 x * C k x 0)‖ ≤ sp k ∧
        ‖ε (FC (C k) (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).ab
          (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sf k) ∧
      ‖lastDefR R Nh m b μ₀ oR x‖ ≤ sL ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k) +
        Mb * (2 * (L : ℝ) * ℓb ^ (2 + 2) / ((L : ℝ) - 1)) + sL ≤
        cd * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

set_option maxHeartbeats 1000000 in
/-- **`PairDefSumR` from the `ab` sizes** of the reduced history. -/
theorem pairDefSumR_of_sizes {Nh : ℕ} (hN : Nh + 2 = N) (hL : pauliL0 2 ≤ L) (hL2 : 2 ≤ L)
    (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cd : ℝ}
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hS : PairDefSizesR R Nh m b μ₀ lam oR cd) :
    PairDefSumR R Nh m b μ₀ lam oR cd := by
  intro x hx h1 hj
  obtain ⟨ℓs, sq, sw, sp, sf, M4, ℓb, Mb, sL, hℓb, hMb, h0, hk, hlast, hsum⟩ := hS x hx h1 hj
  have hanc := hA x hx h1 hj
  -- the per-step bound
  have hstep : ∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ‖hDefR R m b μ₀ oR x k‖ ≤
      (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k) +
        Mb * ‖Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 0 * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x x - Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 x * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x 0‖ := by
    intro k hk'
    obtain ⟨hl, hq, hw, hp, hf⟩ := h0 k
    obtain ⟨hC, -, hlocQ, hQ, hlocW, hW, hM, hP, hF⟩ := hk k hk'
    have hjk : (Obs.coal L (0 : Lam 2 L N) x) ≤ k := (Finset.mem_Ico.1 hk').1
    have hkN : k < N := by have := (Finset.mem_Ico.1 hk').2; omega
    have H := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hjk
    have hfar := Obs2.farAB_eq_zero_of_anch (C := Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) H
    have hwk := Obs2.norm_wkAB2_le one_le_two hL (ptsX x) hkN hl hq hw hC H hlocQ hQ hlocW hW
    rw [hDefR_eq R m b μ₀ oR x H.toAb]
    unfold Obs2.xAB2
    rw [hfar, sub_zero]
    have hMd : ‖M4 k * (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 0 * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x x - Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 x * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x 0)‖ ≤ Mb * ‖(Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 0 * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x x - Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 x * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x 0)‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hM (norm_nonneg _)
    have key : ∀ A B Cw D : ℂ, ‖-A + (Cw + D)‖ ≤ ‖A - B‖ + ‖B‖ + ‖Cw‖ + ‖D‖ := by
      intro A B Cw D
      have e : -A + (Cw + D) = -(A - B) - B + Cw + D := by ring
      rw [e]
      have n1 := norm_add_le (-(A - B) - B + Cw) D
      have n2 := norm_add_le (-(A - B) - B) Cw
      have n3 := norm_sub_le (-(A - B)) B
      rw [norm_neg] at n3
      linarith
    refine (key _ (M4 k * (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 0 * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x x - Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 x * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x 0)) _ _).trans ?_
    refine (add_le_add (add_le_add (add_le_add hP hMd) hwk) hF).trans (le_of_eq ?_)
    ring
  -- the seed sum along a path `0 → x`
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (0 : Lam 2 L N) w = x := by rw [Obs2.pathEnd, zero_add, hwx]
  have hlen : (w.length : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x) := by
    have h2 := two_supNorm_lt_coal hL2 x
    rw [sub_zero] at h2
    have : w.length ≤ L * L ^ (Obs.coal L (0 : Lam 2 L N) x) := by
      rw [← pow_succ']
      exact hwl.trans h2.le
    exact_mod_cast this
  have hseed := seed_detDef_sum_le (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (by exact_mod_cast hL2) 0 w (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1)
    (c₀ := (L : ℝ)) (ℓb := ℓb) (Nat.cast_nonneg _) hℓb hlen ℓs (fun k => (h0 k).1.le)
    (fun k hk' => (hk k hk').2.1) (fun k hk' => (hk k hk').1)
  rw [hpe] at hseed
  calc ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ‖hDefR R m b μ₀ oR x k‖ + ‖lastDefR R Nh m b μ₀ oR x‖
      ≤ ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ((2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k) +
          Mb * ‖Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 0 * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x x - Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 x * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x 0‖) + sL :=
        add_le_add (Finset.sum_le_sum hstep) hlast
    _ = ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k) +
          Mb * ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), ‖Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 0 * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x x - Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k 0 x * Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k x 0‖ + sL := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (2 * (Q1 2 * sq k) + 2 * (Q1 2 * sw k) + sp k + sf k) +
          Mb * (2 * (L : ℝ) * ℓb ^ (2 + 2) / ((L : ℝ) - 1)) + sL := by
        gcongr
    _ ≤ _ := hsum

end Traj

end

end Spin2
