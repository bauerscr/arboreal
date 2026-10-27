import Spin2.Pair.PairJoint2

/-!
# The `E`-step of the joint induction from per-scale size items

`PairJointStep` asks, in its `E`-step, for the region error bounds themselves. Here the `E`-step is
reduced to the per-scale **size items** of `PairErrSizesRX` (activity `Q'`, the `𝒲'` product
term, the Pauli defect, the gradient tadpole, the memory terms), now only **up to the current
scale** (the items at `k < M ≤ n` from `VB n` and the region masses below `n`), with sequences
fixed in advance:

* `PairErrItemsX` (the items of one region at one scale), **`hErrRX_le_of_items`** (the region
  error at that scale; the per-scale part of `pairErrRelRX_of_sizesX`);
* **`PairJointSizes c_e c_a c_r`** (named input: `VB`, the `V`-step, and the truncated item
  bounds) and **`pairJointStep_of_sizes`**: `PairJointSizes ⇒ PairJointStep`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The size items of the region `X` at scale `k`** (as in `PairErrSizesRX`). -/
def PairErrItemsX (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (X : Finset (Lam 2 L N)) (k : ℕ) (ℓs sq se so sw sp sg sm ηw : ℕ → ℝ) (ηm : ℕ → ℕ → ℝ) :
    Prop :=
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
  (Obs.coal L (0 : Lam 2 L N) x < k →
    (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
      (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (se k)) ∧
    (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
      (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (so k)) ∧
    2 * ((L : ℝ) ^ 2 * so k * ((1 + se k) ^ (L ^ 2) - 1) * (ℓs k)⁻¹ ^ 2) ≤
      sw k * β + ηw k * ‖hRRX R m b μ₀ oR x X (k - 1)‖) ∧
  ‖Obs2.pdefM2X k (C k) (V k) X‖ * ‖1 - Obs2.nA2 (ptsX x) k (C k) (V k)‖ ≤ sp k * β ∧
  ‖Obs.LocObs.mass2 (Grassmann.FC (C k) (Obs2.dABX (ptsX x) k (C k) (V k) X)
    (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sg k * β ∧
  ∑ i ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) k, ‖Obs2.memABX (ptsX x) C V W X i k‖ ≤
    sm k * β + ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k,
      ηm i k * ‖hRRX R m b μ₀ oR x X i‖

set_option maxHeartbeats 1000000 in
/-- **The region error at one scale from the size items.** -/
theorem hErrRX_le_of_items (hL : pauliL0 2 ≤ L) {Nh : ℕ} (hN : Nh + 2 = N) (m b μ₀ : ℝ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (hanc : PtCorr2.ObsAnchInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (X : Finset (Lam 2 L N)) {k : ℕ} (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hkN : k ≤ Nh)
    {ℓs sq se so sw sp sg sm ηw : ℕ → ℝ} {ηm : ℕ → ℕ → ℝ}
    (h0 : 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sg k ∧
        0 ≤ sm k ∧ 0 ≤ ηw k)
    (hI : PairErrItemsX R m b μ₀ oR x X k ℓs sq se so sw sp sg sm ηw ηm) :
    ‖hErrRX R m b μ₀ oR x X k‖ ≤
      (2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + sw k + sp k + sg k + sm k) *
          ‖hBeta R m b μ₀ x (k + 1)‖ +
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k,
          (ηm i k + if i = k - 1 then ηw k else 0) * ‖hRRX R m b μ₀ oR x X i‖ := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  obtain ⟨hl, hq, he0, ho0, hw, hp, hg, hm, hηw⟩ := h0
  obtain ⟨hC, hloc, hQ, hWk, hP, hG, hM⟩ := hI
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  set β := ‖hBeta R m b μ₀ x (k + 1)‖
  have hβ : 0 ≤ β := norm_nonneg _
  have hkN' : k < N := by omega
  have H := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hjk
  have hf := Obs2.farABmX_eq_zero_of_anch (C := Obs2.histCovO (R.withMsq m) t k) H X
  have hq' := Obs2.norm_qABX_le one_le_two hL (ptsX x) hkN' hl (mul_nonneg hq hβ) hC H hloc hQ X
  have he := Obs2.norm_errABX2_le (ptsX x) (Obs2.histCovO (R.withMsq m) t)
    (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t)
    (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oR x) t)
    (PtCorr2.hKR (R.withMsq m) (ptsX x) j (oR x) t) X j k hf
  set rs : ℕ → ℝ := fun i => ‖hRRX R m b μ₀ oR x X i‖ with hrs
  have hrs0 : ∀ i, 0 ≤ rs i := fun i => norm_nonneg _
  have hWm : ‖Obs2.wMassABX (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oR x) t) X j k‖ ≤
      sw k * β + ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i := by
    have hsum0 : 0 ≤ ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i :=
      sum_nonneg fun i _ => mul_nonneg (by split_ifs <;> linarith) (hrs0 i)
    unfold Obs2.wMassABX
    split_ifs with hlt
    · obtain ⟨hWe, hWo, hWs⟩ := hWk hlt
      have hj1 : j ≤ k - 1 := by omega
      have H1 := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hj1
      rw [Obs2.farABmX_eq_zero_of_anch H1 X, zero_add]
      refine (Obs2.norm_wProdABX0_le H1 k hl he0 ho0 hWe hWo X).trans (hWs.trans ?_)
      have hmem : k - 1 ∈ Finset.Icc j k := Finset.mem_Icc.2 ⟨hj1, by omega⟩
      have := Finset.single_le_sum (f := fun i => (if i = k - 1 then ηw k else 0) * rs i)
        (fun i _ => mul_nonneg (by split_ifs <;> linarith) (hrs0 i)) hmem
      simp only [if_true] at this
      have e : rs (k - 1) = ‖hRRX R m b μ₀ oR x X (k - 1)‖ := rfl
      rw [e] at this
      linarith
    · rw [norm_zero]
      have := mul_nonneg hw hβ
      linarith
  show ‖hErrRX R m b μ₀ oR x X k‖ ≤ _
  refine he.trans ?_
  have e1 : 2 * (Q1 2 * (sq k * β) * (ℓs k)⁻¹ ^ 2) = 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) * β := by
    ring
  rw [e1] at hq'
  have hsplit : ∑ i ∈ Finset.Icc j k, (ηm i k + if i = k - 1 then ηw k else 0) * rs i =
      ∑ i ∈ Finset.Icc j k, ηm i k * rs i +
        ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  show _ ≤ _ + ∑ i ∈ Finset.Icc j k, (ηm i k + if i = k - 1 then ηw k else 0) * rs i
  rw [hsplit]
  have hM' : ∑ i ∈ Finset.Ico j k, ‖Obs2.memABX (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oR x) t) X i k‖ ≤
      sm k * β + ∑ i ∈ Finset.Icc j k, ηm i k * rs i := hM
  have hP' := hP
  have hG' := hG
  calc _ ≤ 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) * β +
        (sw k * β + ∑ i ∈ Finset.Icc j k, (if i = k - 1 then ηw k else 0) * rs i) +
        sp k * β + sg k * β + (sm k * β + ∑ i ∈ Finset.Icc j k, ηm i k * rs i) := by
        gcongr
    _ = _ := by ring

/-- **Named input: the joint induction with the `E`-step as truncated size items.** For every
`x`: a predicate `VB` (the `V'` block sizes on `[j_x, n)`), fixed size sequences, `VB j_x`, the
`V`-step, and the items of every region `X` (`M`-polymer, `M ≤ n`) at every scale `k < M`, from
`VB n` and the region masses below `n`; the sums as in `PairErrSizesRX`. -/
def PairJointSizes (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (ce ca cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ (VB : ℕ → Prop) (ℓs sq se so sw sp sg sm ηw : ℕ → ℝ) (ηm : ℕ → ℕ → ℝ),
      (∀ k, 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sg k ∧
        0 ≤ sm k ∧ 0 ≤ ηw k) ∧ (∀ i k, 0 ≤ ηm i k) ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + sw k + sp k + sg k + sm k) ≤
        ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
      ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
          (∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k,
            (64 / 49 : ℝ) ^ (k + 1 - i) * ηm i k + (64 / 49 : ℝ) ^ 2 * ηw k) ≤ ca ∧
      VB (Obs.coal L (0 : Lam 2 L N) x) ∧
      (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → VB n →
        PairMassUpTo R m b μ₀ lam oR cr x n → VB (n + 1)) ∧
      (∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
        (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
        ∀ M, Obs.coal L (0 : Lam 2 L N) x ≤ M → M ≤ n → ∀ X : Finset (Lam 2 L N),
          IsPolymer M X → ∀ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) M,
            PairErrItemsX R m b μ₀ oR x X k ℓs sq se so sw sp sg sm ηw ηm)

/-- **`PairJointSizes ⇒ PairJointStep`.** -/
theorem pairJointStep_of_sizes {Nh : ℕ} (hN : Nh + 2 = N) (hL : pauliL0 2 ≤ L) (m b μ₀ : ℝ)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce ca cr : ℝ}
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hS : PairJointSizes R Nh m b μ₀ lam oR ce ca cr) :
    PairJointStep R Nh m b μ₀ lam oR ce ca cr := by
  intro x hx h1 hj
  obtain ⟨VB, ℓs, sq, se, so, sw, sp, sg, sm, ηw, ηm, h0, hηm0, hsum, hηsum, hVB0, hVs, hEs⟩ :=
    hS x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  refine ⟨VB, fun k => 2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + sw k + sp k + sg k + sm k,
    fun i k => ηm i k + if i = k - 1 then ηw k else 0, fun k => ?_, fun i k => ?_, hsum, ?_,
    hVB0, hVs, fun n hn1 hn2 hVB hMs M hM1 hM2 X hX k hk => ?_⟩
  · obtain ⟨hl, hq, -, -, hw, hp, hg, hm, -⟩ := h0 k
    have hQ := one_le_Q1 (d := 2) one_le_two
    have a1 : 0 ≤ Q1 2 * sq k * (ℓs k)⁻¹ ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith) hq) (sq_nonneg _)
    linarith
  · show 0 ≤ ηm i k + (if i = k - 1 then ηw k else 0)
    have := hηm0 i k
    have := (h0 k).2.2.2.2.2.2.2.2
    split_ifs <;> linarith
  · refine le_trans (sum_le_sum fun k hk' => ?_) hηsum
    rw [show ∑ i ∈ Finset.Icc j k, (64 / 49 : ℝ) ^ (k + 1 - i) *
        (ηm i k + if i = k - 1 then ηw k else 0) =
        ∑ i ∈ Finset.Icc j k, (64 / 49 : ℝ) ^ (k + 1 - i) * ηm i k +
          ∑ i ∈ Finset.Icc j k, (if i = k - 1 then (64 / 49 : ℝ) ^ (k + 1 - i) * ηw k else 0) by
      rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by split_ifs <;> ring]
    gcongr
    rw [Finset.sum_ite_eq']
    have hηw := (h0 k).2.2.2.2.2.2.2.2
    split_ifs with hmem
    · have hk1 : 1 ≤ k := by have := (Finset.mem_Ico.1 hk').1; omega
      rw [show k + 1 - (k - 1) = 2 by omega]
    · positivity
  · have hkM := Finset.mem_Ico.1 hk
    exact hErrRX_le_of_items R hL hN m b μ₀ oR x (hA x hx h1 hj) X hkM.1 (by omega) (h0 k)
      (hEs n hn1 hn2 hVB hMs M hM1 hM2 X hX k hk)

/-- **`PairRRelR` and the region masses from `PairJointSizes`** (for combination with the master
exports): the trajectory-level inputs are those of `pairRRelRX_of_err2` (tadpole kernel `c_t`,
`‖𝔫‖ ≤ B'ǧ`, `Case2Rel`, `Case2TopStep`, `∑ǧ² ≤ G₂`), plus `PairAnchR` and
`crErr2 c_e c_δ G₂ c_t B' c_a ≤ c_r`. -/
theorem pairRRelR_of_jointSizes {Nh : ℕ} (hN : Nh + 2 = N) (hLp : pauliL0 2 ≤ L) (m : ℝ)
    {b μ₀ : ℝ} (hb : 0 < b) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    {ce cδ G2 ct B' ca cr : ℝ}
    (hce : 0 ≤ ce) (hcδ : 0 ≤ cδ) (hct : 0 ≤ ct) (hB' : 0 ≤ B') (hL : 49 ≤ L)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hG2 : ∑ k ∈ range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ G2)
    (hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1)
    (hcg : ∀ i ≤ Nh, ct * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤ 1)
    (hRd : PairSectRed R Nh m b μ₀ oR)
    (hV0 : ∀ x : Lam 2 L N, ∀ B, ((oR x).V B : Obs.SA .two (Lam 2 L N)).ab = 0)
    (hW0 : ∀ x : Lam 2 L N, ∀ B, ((oR x).W B : Obs.SA .two (Lam 2 L N)).ab = 0)
    (hrel : ∀ x : Lam 2 L N, x ≠ 0 → Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (hnB : ∀ x : Lam 2 L N, x ≠ 0 → ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
      B' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (ht : ∀ x : Lam 2 L N, x ≠ 0 → ∀ i k, i < k → k ≤ Nh →
      ‖tadO R m b μ₀ x i k‖ ≤ ct * (2 / (L : ℝ)) ^ (k - i) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1)
    (hA : PairAnchR (L := L) (N := N) Nh oR)
    (hcr : crErr2 ce cδ G2 ct B' ca ≤ cr) (hJ : PairJointSizes R Nh m b μ₀ lam oR ce ca cr) :
    PairRRelR R Nh m b μ₀ lam oR cr ∧ PairRRelRX R Nh m b μ₀ lam oR cr ∧
      PairErrRelRX R Nh m b μ₀ lam oR ce ca := by
  have H := pairRelRX_of_joint R hN m hb lam oR hce hcδ hct hB' hL hg hG2 hgm hcg hRd hV0 hW0 hrel
    hn hnB htop ht hcr (pairJointStep_of_sizes R hN hLp m b μ₀ lam oR hA hJ)
  exact ⟨pairRRelR_of_relRX R H.2, H.2, H.1⟩

end Traj

end

end Spin2
