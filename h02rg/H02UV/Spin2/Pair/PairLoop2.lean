import Spin2.Pair.PairEStep4
import PtCorr2.Pair.SFirst1

/-!
# The `E`-step items after the cancellation of the first-order `S`-contribution

`PairErrItemsXP` bounds the Pauli defect `|𝔡₂_k(X)||1 − n_k|` (item `s^p`) and the memory sum
`∑_i|mem(i,k)|` (item `s^m`) separately. Both contain the first-order `Loc S` contribution
(`M₄(Loc S_i)·m2D(C_k)`), which is `≍ C(L)cǧ_k m̄` and makes the constant loop fail
(`Spin2/Pair/PairLoop`). By `Obs2.errABX2_eq3` / `PtCorr2.errABX2_eq3_hR` the two cancel exactly. Here:

* **`PairErrItemsXP3`**: `PairErrItemsXP` with the two items replaced by
  `|∑_iM₄(Q_i)(X)||m2D(C_k)||1 − n_k| + |n_k||∑_iM₄(Loc S_i)(X)||m2D(C_k)| ≤ s^p_kβ` and
  `∑_i|mem₃(i,k)| ≤ s^m_kβ + ∑_iη^m_{ik}|r'_i(X)|` (memory without the `Loc S` tadpole);
* **`hErrRX_le_of_itemsP3`** (same bound as `hErrRX_le_of_itemsP`; needs the invariants of the
  reduced history: `ObsVabInv`, `V'_{j,ab} = 0`, `ObsSymInv` up to `k`, `X` a `k`-polymer);
* **`PairJointSizesP3`**, **`pairJointStep_of_sizesP3`**, **`pairRRelR_of_jointSizesP3`**,
  **`pairRRelR_of_jointSizesP3_MF`** (copies of the `P` versions).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The size items of the region `X` at scale `k` after the cancellation.** -/
def PairErrItemsXP3 (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (X : Finset (Lam 2 L N)) (k : ℕ) (ℓs sq se so sw sp sg sm ηw : ℕ → ℝ) (ηm : ℕ → ℕ → ℝ) :
    Prop :=
  let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  let C := Obs2.histCovO (R.withMsq m) t
  let V := PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
  let W := PtCorr2.hWR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
  let K := PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) t
  let j := Obs.coal L (0 : Lam 2 L N) x
  let β := ‖hBeta R m b μ₀ x (k + 1)‖
  GoodCov2 k (ℓs k) (C k) ∧
  (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.Q2O (ptsX x) k (K k) B : Obs.SA .two (Lam 2 L N)).ab ≤
    ENNReal.ofReal (sq k * β)) ∧
  (j < k →
    (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
      (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (se k)) ∧
    (∀ B, Tj 2 (L : ℝ) k (ℓs k) (Obs2.WpO (ptsX x) (k - 1) (C (k - 1)) (V (k - 1))
      (W (k - 1)) B : Obs.SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (so k)) ∧
    2 * ((L : ℝ) ^ 2 * so k * ((1 + se k) ^ (L ^ 2) - 1) * (ℓs k)⁻¹ ^ 2) ≤
      sw k * β + ηw k * ‖hRRX R m b μ₀ oR x X (k - 1)‖) ∧
  ‖∑ i ∈ Finset.Ico j k, Obs2.m4QX (ptsX x) i (K i) X‖ * ‖Obs2.m2D (ptsX x) (C k)‖ *
      ‖1 - Obs2.nA2 (ptsX x) k (C k) (V k)‖ +
    ‖Obs2.nA2 (ptsX x) k (C k) (V k)‖ *
      ‖∑ i ∈ Finset.Ico j k, Obs2.m4LSX (ptsX x) i (C i) (V i) (W i) X‖ *
      ‖Obs2.m2D (ptsX x) (C k)‖ ≤ sp k * β ∧
  ‖Obs.LocObs.mass2 (Grassmann.FC (C k) (Obs2.dABX (ptsX x) k (C k) (V k) X)
    (Obs2.VprLO k (C k) (V k) : Obs.SA .two (Lam 2 L N)).e)‖ ≤ sg k * β ∧
  ∑ i ∈ Finset.Ico j k, ‖Obs2.memABX3 (ptsX x) C V W X i k‖ ≤
    sm k * β + ∑ i ∈ Finset.Icc j k, ηm i k * ‖hRRX R m b μ₀ oR x X i‖

set_option maxHeartbeats 1000000 in
/-- **The region error at one scale from the reorganised items** (copy of
`hErrRX_le_of_itemsP`, through `PtCorr2.errABX2_eq3_hR` and `Obs2.norm_errABX3_le`). -/
theorem hErrRX_le_of_itemsP3 (hL : pauliL0 2 ≤ L) {Nh : ℕ} (hN : Nh + 2 = N) (m b μ₀ : ℝ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (hanc : PtCorr2.ObsAnchInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (hVab : PtCorr2.ObsVabInv (ptsX x) (oR x))
    (hz : ∀ B, ((oR x).V B : Obs.SA .two (Lam 2 L N)).ab = 0)
    (X : Finset (Lam 2 L N)) {k : ℕ} (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hkN : k ≤ Nh)
    (hsym : ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i ≤ k →
      PtCorr2.ObsSymInv i (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (oR x) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hX : IsPolymer k X)
    {ℓs sq se so sw sp sg sm ηw : ℕ → ℝ} {ηm : ℕ → ℕ → ℝ}
    (h0 : 0 < ℓs k ∧ 0 ≤ sq k ∧ 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ sp k ∧ 0 ≤ sg k ∧
        0 ≤ sm k ∧ 0 ≤ ηw k)
    (hI : PairErrItemsXP3 R m b μ₀ oR x X k ℓs sq se so sw sp sg sm ηw ηm) :
    ‖hErrRX R m b μ₀ oR x X k‖ ≤
      (2 * (Q1 2 * sq k * (ℓs k)⁻¹ ^ 2) + sw k + sp k + sg k + sm k) *
          ‖hBeta R m b μ₀ x (k + 1)‖ +
        ∑ i ∈ Finset.Icc (Obs.coal L (0 : Lam 2 L N) x) k,
          (ηm i k + if i = k - 1 then ηw k else 0) * ‖hRRX R m b μ₀ oR x X i‖ := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  obtain ⟨hl, hq, he0, ho0, hw, hp, hg, hm, hηw⟩ := h0
  obtain ⟨hC, hQ, hWk, hP, hG, hM⟩ := hI
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  set β := ‖hBeta R m b μ₀ x (k + 1)‖
  have hβ : 0 ≤ β := norm_nonneg _
  have hkN' : k < N := by omega
  have H := PtCorr2.oanchS_hR (R.withMsq m) (ptsX x) hanc t hjk
  have hf := Obs2.farABmX_eq_zero_of_anch (C := Obs2.histCovO (R.withMsq m) t k) H X
  have hq' := PtCorr2.norm_qABX_leP one_le_two hL (ptsX x) hkN' hl (mul_nonneg hq hβ) hC H hQ X
  have hE3 := PtCorr2.errABX2_eq3_hR (R.withMsq m) (ptsX x) j (oR x) t hVab hz hsym hX hjk
  have he := Obs2.norm_errABX3_le (ptsX x) (Obs2.histCovO (R.withMsq m) t)
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
  have hEq : ‖hErrRX R m b μ₀ oR x X k‖ = ‖Obs2.errABX3 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oR x) t)
      (PtCorr2.hWR (R.withMsq m) (ptsX x) j (oR x) t)
      (PtCorr2.hKR (R.withMsq m) (ptsX x) j (oR x) t) X j k‖ := by
    unfold hErrRX; exact congrArg _ hE3
  rw [hEq]
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
  have hM' : ∑ i ∈ Finset.Ico j k, ‖Obs2.memABX3 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
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

/-- **The joint induction with the reorganised items** (`PairJointSizesP` with
`PairErrItemsXP3`). -/
def PairJointSizesP3 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
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
            PairErrItemsXP3 R m b μ₀ oR x X k ℓs sq se so sw sp sg sm ηw ηm)

/-- The invariants of the reduced states used by the cancellation. -/
def PairRedInv (Nh : ℕ) (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    PtCorr2.ObsVabInv (ptsX x) (oR x) ∧
    (∀ B, ((oR x).V B : Obs.SA .two (Lam 2 L N)).ab = 0) ∧
    ∀ i, Obs.coal L (0 : Lam 2 L N) x ≤ i → i ≤ Nh →
      PtCorr2.ObsSymInv i (PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (oR x) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))

/-- **`PairJointSizesP3 ⇒ PairJointStep`.** -/
theorem pairJointStep_of_sizesP3 {Nh : ℕ} (hN : Nh + 2 = N) (hL : pauliL0 2 ≤ L) (m b μ₀ : ℝ)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) {ce ca cr : ℝ}
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hI : PairRedInv R Nh m b μ₀ oR)
    (hS : PairJointSizesP3 R Nh m b μ₀ lam oR ce ca cr) :
    PairJointStep R Nh m b μ₀ lam oR ce ca cr := by
  intro x hx h1 hj
  obtain ⟨VB, ℓs, sq, se, so, sw, sp, sg, sm, ηw, ηm, h0, hηm0, hsum, hηsum, hVB0, hVs, hEs⟩ :=
    hS x hx h1 hj
  obtain ⟨hVab, hz, hsym⟩ := hI x hx h1 hj
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
    exact hErrRX_le_of_itemsP3 R hL hN m b μ₀ oR x (hA x hx h1 hj) hVab hz X hkM.1 (by omega)
      (fun i hi hik => hsym i hi (by omega)) (Step2.isPolymer_of_le hX k (by omega)) (h0 k)
      (hEs n hn1 hn2 hVB hMs M hM1 hM2 X hX k hk)

/-- **`PairRRelR` from `PairJointSizesP3`** (copy of `pairRRelR_of_jointSizesP`). -/
theorem pairRRelR_of_jointSizesP3 {Nh : ℕ} (hN : Nh + 2 = N) (hLp : pauliL0 2 ≤ L) (m : ℝ)
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
    (hA : PairAnchR (L := L) (N := N) Nh oR) (hI : PairRedInv R Nh m b μ₀ oR)
    (hcr : crErr2 ce cδ G2 ct B' ca ≤ cr) (hJ : PairJointSizesP3 R Nh m b μ₀ lam oR ce ca cr) :
    PairRRelR R Nh m b μ₀ lam oR cr ∧ PairRRelRX R Nh m b μ₀ lam oR cr ∧
      PairErrRelRX R Nh m b μ₀ lam oR ce ca := by
  have H := pairRelRX_of_joint R hN m hb lam oR hce hcδ hct hB' hL hg hG2 hgm hcg hRd hV0 hW0 hrel
    hn hnB htop ht hcr (pairJointStep_of_sizesP3 R hN hLp m b μ₀ lam oR hA hI hJ)
  exact ⟨pairRRelR_of_relRX R H.2, H.2, H.1⟩

end Traj

set_option maxHeartbeats 4000000 in
/-- **The invariants of the reduced states `oRed … dxStd` under `MasterFacts`.** -/
theorem pairRedInv_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀) :
    PairRedInv R Nh m b μ₀ (oRed R m b μ₀ dxStd) := by
  obtain ⟨-, -, -, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        t j fun i hi => (hRI i (by omega)))
  exact ⟨PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x), fun B => oRed_V_ab_zero R m b μ₀ dxStd x B,
    fun k hk hkN =>
      PtCorr2.obsSymInv_histFrom' (R.withMsq m) (ptsX x) hsymj t hk fun i _ hi => hRI i (by omega)⟩

end

end Spin2
