import Spin2.Pair.PairEStep4
import Spin2.Pair.PairVStep1

/-!
# The `E`-step sizes (2): `|1 − n_a|`, `tadInc₂` and `𝔡₂` discharged; `PairJointSizesP` from the
reduced size data

Of the per-scale size data `PairESizesAt` of the `E`-step three items are discharged here along
every admissible trajectory of `MasterFacts` (for the reduced states `oRed … dxStd`):

* item (iv), `|1 − n_{a,k}| ≤ 3` (`k ≤ N_h`): `n_{a,k} = ν̄_k = 𝔫_k − ∑_{i<k}tadInc₂(i,k)` (`nA2` is
  `nuBar2` by definition), `𝔫_k` and `tadInc₂` only see the bulk (`frakN2_hR_eq`,
  `tadInc2_hR_eq`), `‖𝔫_k‖ ≤ 1/8` (`loop`, `top`), `‖tadInc₂(i,k)‖ ≤ c_t(2/L)^{k−i}ǧ_i` with
  `c_tǧ_i ≤ 1` (`tad`), `∑_{i<k}(2/L)^{k−i} ≤ 1` (**`geom_tail_two_le`**);
* item (v), `τ_{ik} = c_t(2/L)^{k−i}ǧ_i` (`tad` + `tadInc2_hR_eq`);
* the Pauli-defect sizes `P_i = μ_i(|w|s_i/L^{i+1})²` from the `M₄` sizes `μ_i` of the same data
  (`pdefM2X_hVR_le`).

**`PairESizesAtR`/`PairESizesR`**: `PairESizesAt`/`PairESizes` without these three items;
**`pairESizes_of_R_MF`**: `PairESizesR ⇒ PairESizes` (with `c_n = 3`, `P_i`, `τ` as above);
**`pairJointSizesP_of_R_MF`**: `pairJointSizesP_MF` with `PairESizesR`;
**`pairJointSizesP_of_VR_MF`**: in addition the `V`-step discharged (`VB := PairVB … m̄`,
`pairVStep_MF`; inputs `PairUnitSeed c_u` and the seed condition).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- `∑_{i<k} x^{k−i} ≤ 1` for `0 ≤ x ≤ 1/2`. -/
theorem geom_tail_two_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (k : ℕ) :
    ∑ i ∈ Finset.range k, x ^ (k - i) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega, pow_one]
    have e : ∑ i ∈ Finset.range k, x ^ (k + 1 - i) = x * ∑ i ∈ Finset.range k, x ^ (k - i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        have := Finset.mem_range.1 hi
        rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ, mul_comm]
    rw [e]
    nlinarith

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The size data of the `E`-step at scale `k` without `|1 − n_a|`, `𝔡₂`, `tadInc₂`**
(`PairESizesAt` without its items 4, 7, 8). -/
def PairESizesAtR (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ)
    (κQ se so sw ηw μ δ e F Λ Wp : ℕ → ℝ) : Prop :=
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

/-- **The reduced size data of the `E`-step** (`PairESizes` with `PairESizesAtR`). -/
def PairESizesR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cr : ℝ) (x : Lam 2 L N) (VB : ℕ → Prop) (κQ se so sw ηw μ δ e F Λ Wp : ℕ → ℝ) : Prop :=
  ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
    (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
    ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < n →
      PairESizesAtR R m b μ₀ oR x k κQ se so sw ηw μ δ e F Λ Wp

end Traj

/-- The Pauli-defect sizes `P_i = μ_i(|w|s_i/L^{i+1})²`. -/
def pdSz {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (w : List (Dir 2)) (μ : ℕ → ℝ) (i : ℕ) : ℝ :=
  μ i * (w.length * (PtCorr2.histS (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) /
    (L : ℝ) ^ (i + 1))) ^ 2

/-- The tadpole kernel `τ_{ik} = c_t(2/L)^{k−i}max(ǧ_i, 0)`. -/
def tauSz {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ ct : ℝ)
    (i k : ℕ) : ℝ :=
  ct * (2 / (L : ℝ)) ^ (k - i) * max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 0

set_option maxHeartbeats 1000000 in
/-- **`PairESizesR ⇒ PairESizes`** under `MasterFacts` (`c_n = 3`, `P = pdSz`, `τ = tauSz`). -/
theorem pairESizes_of_R_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) (cr : ℝ) (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (w : List (Dir 2))
    (hw : Obs2.pathEnd (0 : Lam 2 L N) w = x) (VB : ℕ → Prop)
    (κQ se so sw ηw μ δ e F Λ Wp : ℕ → ℝ)
    (hS : PairESizesR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x VB κQ se so sw ηw μ δ e F Λ Wp) :
    PairESizes R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x VB κQ se so sw ηw μ (fun _ => 3) δ e
      (pdSz R m b μ₀ w μ) F Λ Wp (tauSz R m b μ₀ M.core.ce) := by
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL49 : 49 ≤ L := M.core.hL49
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, -, -, -⟩ := hRd x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hVab : PtCorr2.ObsVabInv (ptsX x) (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  have hsym : ∀ k, j ≤ k → k ≤ Nh → PtCorr2.ObsSymInv k (PtCorr2.obsHistFrom (R.withMsq m)
      (ptsX x) j (oRed R m b μ₀ dxStd x) k t) := fun k hk hkN =>
    PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk fun i _ hi => hRI i (by omega)
  obtain ⟨hct, htad, hcg⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨q, -, -, hl⟩ :=
    (M.loop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  have hnn : ∀ k ≤ Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8 := fun k hk => by
    rcases Nat.lt_or_ge k Nh with h | h
    · exact (hl k h).1
    · rw [show k = Nh by omega]
      exact (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1.1
  have htadR : ∀ i k, Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t) i k = tadO R m b μ₀ x i k :=
    fun i k => PtCorr2.tadInc2_hR_eq hobs (Obs2.obsInit_isObs .two (zV b) (ptsX x)) i k
  have hτ : ∀ i k, i < k → k ≤ Nh → ‖tadO R m b μ₀ x i k‖ ≤ tauSz R m b μ₀ M.core.ce i k := by
    intro i k hik hk
    have h := htad (ptsX x) (zV b) i k hik hk
    unfold tauSz
    rw [max_eq_left (hadm.1 i (by omega)).1.le]
    exact h
  have hL2' : (2 : ℝ) / L ≤ 1 / 2 := by
    have hL4 : (4 : ℝ) ≤ L := by exact_mod_cast (show 4 ≤ L by omega)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  intro n hn1 hn2 hVB hMs k hk1 hk2
  have hAt := fun k' (hk1' : j ≤ k') (hk2' : k' < n) => hS n hn1 hn2 hVB hMs k' hk1' hk2'
  obtain ⟨a1, a2, a3, a5, a6, a9, a10, a11⟩ := hAt k hk1 hk2
  refine ⟨a1, a2, a3, ?_, a5, a6, ?_, fun i hi1 hi2 => ?_, a9, a10, a11⟩
  · -- `|1 − n_a| ≤ 3`
    have e1 : Obs2.nA2 (ptsX x) k (Obs2.histCovO (R.withMsq m) t k)
        (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k) =
        nn2 R (ptsX x) (zV b) m b μ₀ k - ∑ i ∈ Finset.range k, tadO R m b μ₀ x i k := by
      have e2 := PtCorr2.frakN2_hR_eq (R := R.withMsq m) (P := ptsX x) (j := j) (t := t) hobs
        (Obs2.obsInit_isObs .two (zV b) (ptsX x)) k
      have e3 : nn2 R (ptsX x) (zV b) m b μ₀ k = Obs2.frakN2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
          (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t) k := by
        rw [e2]; rfl
      rw [e3]
      unfold Obs2.frakN2
      simp only [htadR]
      show Obs2.nuBar2 _ _ _ k = _
      ring
    rw [e1]
    have hs : ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ ≤ 1 := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => ?_).trans
        (geom_tail_two_le (by positivity) hL2' k))
      have hik := Finset.mem_range.1 hi
      have hkN : k ≤ Nh := by omega
      refine (htad (ptsX x) (zV b) i k hik hkN).trans ?_
      have hc := hcg i (by omega)
      have hp : 0 ≤ (2 / (L : ℝ)) ^ (k - i) := by positivity
      calc M.core.ce * (2 / (L : ℝ)) ^ (k - i) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1
          = (2 / (L : ℝ)) ^ (k - i) * (M.core.ce * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1) := by
            ring
        _ ≤ (2 / (L : ℝ)) ^ (k - i) * 1 := mul_le_mul_of_nonneg_left hc hp
        _ = _ := mul_one _
    have hn := hnn k (by omega)
    calc ‖1 - (nn2 R (ptsX x) (zV b) m b μ₀ k - ∑ i ∈ Finset.range k, tadO R m b μ₀ x i k)‖
        ≤ ‖(1 : ℂ)‖ + ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ +
            ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ := by
          refine (norm_sub_le _ _).trans ?_
          have := norm_sub_le (nn2 R (ptsX x) (zV b) m b μ₀ k)
            (∑ i ∈ Finset.range k, tadO R m b μ₀ x i k)
          linarith
      _ ≤ 3 := by rw [norm_one]; linarith
  · -- `𝔡₂_i` from `μ_i`
    intro X i hi1 hi2
    obtain ⟨-, -, hμi, -⟩ := hAt i hi1 (by omega)
    have h := PtCorr2.pdefM2X_hVR_le (R.withMsq m) (ptsX x) t hVab (hsym i hi1 (by omega))
      (hG i (by omega)) w hw X
    refine h.trans ?_
    unfold pdSz
    have hsq := sq_nonneg ((w.length : ℝ) *
      (PtCorr2.histS (R.withMsq m) i t / (L : ℝ) ^ (i + 1)))
    calc _ ≤ μ i * ‖hBeta R m b μ₀ x (i + 1)‖ * ((w.length : ℝ) *
          (PtCorr2.histS (R.withMsq m) i t / (L : ℝ) ^ (i + 1))) ^ 2 :=
          mul_le_mul_of_nonneg_right (hμi X) hsq
      _ = _ := by ring
  · -- `tadInc₂`
    rw [htadR]
    exact hτ i k hi2 (by omega)

set_option maxHeartbeats 4000000 in
/-- **`PairJointSizesP` from the `V`-step data and the reduced `E`-step sizes** (`pairJointSizesP_MF`
with `PairESizesR`; `c_n = 3`, `P = pdSz`, `τ = tauSz` with `c_t = core.ce`). -/
theorem pairJointSizesP_of_R_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) (ce ca cr : ℝ)
    (hX : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ (VB : ℕ → Prop) (κQ se so sw ηw μ δ e F Λ Wp : ℕ → ℝ) (w : List (Dir 2)),
        Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
        (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ F k ∧ 0 ≤ Λ k ∧ 0 ≤ Wp k) ∧
        (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * κQ k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * 3 +
              2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) (pdSz R m b μ₀ w μ) F Λ Wp
                (tauSz R m b μ₀ M.core.ce) k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
        VB (Obs.coal L (0 : Lam 2 L N) x) ∧
        (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
          PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ dxStd) cr x n → VB (n + 1)) ∧
        PairESizesR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x VB κQ se so sw ηw μ δ e F Λ Wp) :
    PairJointSizesP R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  obtain ⟨hct, -, -⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  refine pairJointSizesP_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam ce ca cr
    fun x hx h1 hj => ?_
  obtain ⟨VB, κQ, se, so, sw, ηw, μ, δ, e, F, Λ, Wp, w, hw, h0, h0', hsum, hηsum, hVB0, hVs, hS⟩ :=
    hX x hx h1 hj
  refine ⟨VB, κQ, se, so, sw, ηw, μ, fun _ => 3, δ, e, pdSz R m b μ₀ w μ, F, Λ, Wp,
    tauSz R m b μ₀ M.core.ce, w, hw, fun k => ?_, fun i k => ?_, h0', hsum, hηsum, hVB0, hVs,
    pairESizes_of_R_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cr x hx h1 hj w hw VB
      κQ se so sw ηw μ δ e F Λ Wp hS⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h0 k
    exact ⟨a1, a2, by norm_num, a3, a4, mul_nonneg a2 (sq_nonneg _), a5, a6, a7⟩
  · unfold tauSz
    exact mul_nonneg (mul_nonneg hct (pow_nonneg (by positivity) _)) (le_max_right _ _)

set_option maxHeartbeats 4000000 in
/-- **`PairJointSizesP` with the `V`-step discharged**: `VB := PairVB … m̄`, the `V`-step from
`pairVStep_MF` (inputs `PairUnitSeed c_u`, `c_r ≤ m̄` and the seed condition); what remains per `x`
is the reduced size data `PairESizesR` under `PairVB`, a path, and the two sums. -/
theorem pairJointSizesP_of_VR_MF {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁w : ℝ, 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu ce ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      cr ≤ mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁w * ((4 * C₁w + 1) * mbar) →
    (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ (κQ se so sw ηw μ δ e F Λ Wp : ℕ → ℝ) (w : List (Dir 2)),
        Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
        (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ F k ∧ 0 ≤ Λ k ∧ 0 ≤ Wp k) ∧
        (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * κQ k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * 3 +
              2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) (pdSz R m b μ₀ w μ) F Λ Wp
                (tauSz R m b μ₀ M.core.ce) k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
        PairESizesR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x (PairVB R m b μ₀ lam x mbar)
          κQ se so sw ηw μ δ e F Λ Wp) →
    PairJointSizesP R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  obtain ⟨C₁w, hC₁w, hVS⟩ := pairVStep_MF M
  refine ⟨C₁w, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ce ca cr mbar hU hmbar hcr h8
    hX
  refine pairJointSizesP_of_R_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam ce ca cr
    fun x hx h1 hj => ?_
  obtain ⟨κQ, se, so, sw, ηw, μ, δ, e, F, Λ, Wp, w, hw, h0, h0', hsum, hηsum, hS⟩ := hX x hx h1 hj
  obtain ⟨hVB0, hVs⟩ := hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU
    hmbar hcr h8 x hx h1 hj
  exact ⟨PairVB R m b μ₀ lam x mbar, κQ, se, so, sw, ηw, μ, δ, e, F, Λ, Wp, w, hw, h0, h0', hsum,
    hηsum, hVB0, hVs, hS⟩

end

end Spin2
