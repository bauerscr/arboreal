import Flow.FlowDefs
import Step.Reg

/-!
# Regularity of the bulk flow in a parameter

The flow `(V_j, K_j) = flowN N m² V₀ j` is regular in a parameter `t` (coefficient-wise) when
`V₀(t)` and the covariances `C_{j+1}(μ(t))` are, in the sense of a class `Reg` of regular scalar
functions (`Step/Reg.lean`): `flowN_reg`, `uflow_reg`.  The parameter enters through a map
`μ : T → ℝ` (`μ = id` for continuity in `m²`, `μ` constant for holomorphy in `b₀`).

For continuity in `m²` (`Reg.cont S`): `flowN_cont`, `uflow_cont` (the continuous families `CV`,
`CK`), together with `covAt_continuousOn` (the covariances are continuous in `m² ≥ 0`) and
`goodCov_covAt` (the hypotheses `GoodCov` hold for `ℓ₀` large).
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Coup

variable {d L : ℕ} [NeZero L] {N : ℕ}

section Reg

variable {T : Type*} {R : Reg T}

theorem _root_.Step.RegK.restr {K : T → Act d L N} (hK : RegK R K) (j : ℕ) :
    RegK R (fun t => Flow.restr j (K t)) := by
  classical
  intro X
  by_cases hX : IsConn j X
  · simpa [Flow.restr_of_conn _ hX] using hK X
  · simpa [Flow.restr_of_not_conn _ hX] using RegE.const (R := R) (0 : EvR (Lam d L N))

/-- **Regularity along the bulk flow**: if `V₀(t)` and the covariances `C_{j+1}(μ(t))` are
regular, then so are `V_j`, `K_j` (coefficient-wise), `j ≤ N`. -/
theorem flowN_reg (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ : ℝ} {μ : T → ℝ} {V₀ : T → Vcoup}
    (hV₀ : RegV R V₀)
    (hC : ∀ j < N, ∀ x y, R.P (fun t => ((covAt d L N (μ t) j x y : ℝ) : ℂ)))
    (hgood : ∀ t ∈ R.D, ∀ j < N,
      GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N (μ t) j)) :
    ∀ j ≤ N, RegV R (fun t => (flowN d L N (μ t) (V₀ t) j).1) ∧
      RegK R (fun t => (flowN d L N (μ t) (V₀ t) j).2) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨hV₀, fun X => by simpa [flowN_zero] using RegE.const (R := R) (0 : EvR (Lam d L N))⟩
  | succ j ih =>
    intro hj
    obtain ⟨ihV, ihK⟩ := ih (by omega)
    have hKj : ∀ t ∈ R.D, InK j (flowN d L N (μ t) (V₀ t) j).2 := fun t ht =>
      InK_flowN hd hL (hgood t ht) (V₀ t) j (by omega)
    have hinv : ∀ t ∈ R.D, CovInv (covAt d L N (μ t) j) := fun t ht =>
      (hgood t ht j (by omega)).covInv
    have hsym : ∀ t ∈ R.D, ∀ x y, covAt d L N (μ t) j x y = covAt d L N (μ t) j y x :=
      fun t ht => (hgood t ht j (by omega)).symm'
    simp only [flowN_succ]
    refine ⟨(uVnext_reg hd hL (by omega) (hC j (by omega)) hinv hsym ihV ihK hKj).2, ?_⟩
    refine RegK.restr (fun U => ?_) (j + 1)
    exact Knext_reg hd hL (by omega) (hC j (by omega)) hinv hsym ihV ihK hKj U

theorem uflow_reg (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ : ℝ} {μ : T → ℝ} {V₀ : T → Vcoup}
    (hV₀ : RegV R V₀)
    (hC : ∀ j < N, ∀ x y, R.P (fun t => ((covAt d L N (μ t) j x y : ℝ) : ℂ)))
    (hgood : ∀ t ∈ R.D, ∀ j < N,
      GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N (μ t) j))
    {j : ℕ} (hj : j < N) : R.P (fun t => uflow d L N (μ t) (V₀ t) j) := by
  obtain ⟨hV, hK⟩ := flowN_reg hd hL hV₀ hC hgood j hj.le
  exact (uVnext_reg hd hL hj (hC j hj) (fun t ht => (hgood t ht j hj).covInv)
    (fun t ht => (hgood t ht j hj).symm') hV hK
    (fun t ht => InK_flowN hd hL (hgood t ht) (V₀ t) j hj)).1

end Reg

/-! ### Continuity in `m²` -/

section Cont

variable {S : Set ℝ}

/-- **Continuity along the flow**: if `V₀(m)` and the covariances are continuous on `S`, then
so are `V_j`, `K_j` (coefficient-wise) and `u_{j+1}`. -/
theorem flowN_cont (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ : ℝ} {V₀ : ℝ → Vcoup}
    (hV₀ : CV S V₀) (hC : ∀ j < N, ∀ x y, ContinuousOn (fun m => covAt d L N m j x y) S)
    (hgood : ∀ m ∈ S, ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N m j)) :
    ∀ j ≤ N, CV S (fun m => (flowN d L N m (V₀ m) j).1) ∧
      CK S (fun m => (flowN d L N m (V₀ m) j).2) := fun j hj =>
  let h := flowN_reg (R := Reg.cont S) (μ := id) hd hL (RegV.of_CV hV₀)
    (fun j hj x y => Reg.cont_ofReal (hC j hj x y)) hgood j hj
  ⟨h.1.toCV, regK_cont_iff.1 h.2⟩

theorem uflow_cont (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {ℓ₀ : ℝ} {V₀ : ℝ → Vcoup}
    (hV₀ : CV S V₀) (hC : ∀ j < N, ∀ x y, ContinuousOn (fun m => covAt d L N m j x y) S)
    (hgood : ∀ m ∈ S, ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N m j))
    {j : ℕ} (hj : j < N) : ContinuousOn (fun m => uflow d L N m (V₀ m) j) S :=
  uflow_reg (R := Reg.cont S) (μ := id) hd hL (RegV.of_CV hV₀)
    (fun j hj x y => Reg.cont_ofReal (hC j hj x y)) hgood hj

/-- The covariances of the flow are continuous in `m² ≥ 0`. -/
theorem covAt_continuousOn (hd : 1 ≤ d) {j : ℕ} (hj : j < N) (x y : Lam d L N) :
    ContinuousOn (fun m => covAt d L N m j x y) (Set.Ici 0) := by
  rcases Nat.lt_or_ge (j + 1) N with h | h
  · simp only [covAt_lt h]
    exact Cj_continuousOn stdPt hd (Nat.cast_nonneg L) (j + 1) x y
  · obtain rfl : N = j + 1 := by omega
    simp only [covAt_last]
    exact CN_continuousOn stdPt hd (Nat.cast_nonneg L) (j + 1) x y

end Cont

/-- The hypotheses `GoodCov` hold for the covariances of the flow once `ℓ₀` is large
(`e:Cleq1`), for all `m² ≥ 0`. -/
theorem goodCov_covAt (hd : 3 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L : ℕ) [NeZero L], ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
      K * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
      ∀ (N : ℕ) (msq : ℝ), 0 ≤ msq → ∀ j < N,
        GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j) := by
  obtain ⟨K₁, hK₁, h₁⟩ := goodCov_Cfrd hd
  obtain ⟨K₂, hK₂, h₂⟩ := goodCov_CfrdN hd
  refine ⟨max K₁ K₂, le_trans hK₁ (le_max_left _ _), fun L _ ℓ₀ hℓ₀ hK N msq hmsq j hj => ?_⟩
  have hLpos : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.lt_or_ge (j + 1) N with h | h
  · rw [covAt_lt h]
    exact h₁ L NeZero.one_le ℓ₀ hℓ₀
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos).trans hK) N j h msq hmsq
  · obtain rfl : N = j + 1 := by omega
    rw [covAt_last]
    exact h₂ L NeZero.one_le ℓ₀ hℓ₀
      ((mul_le_mul_of_nonneg_right (le_max_right _ _) hLpos).trans hK) j msq hmsq

end

end Flow
