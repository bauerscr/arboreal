import Spin2.Pair.PairESz3

/-!
# The `E`-step sizes (4): items (i), (vi) inserted; `PairJointSizesP` from the remaining items

With the `𝒲`-chain sizes of `pairWSizes_MF` (weights `vwA`, `vwB`; target `m̄`; `C₁w` of
`MasterCore.abwHist`) and the off-lattice vanishing (`MasterCore.wpoOff`), the items 2, 10, 11 of
`PairESizesAt` (the `𝒲'_{k-1}` block, `Loc S_i(B)_{ab}`, the product parts) are discharged with
the explicit sequences (`r_i = max(cǧ_i, 0)`, `s_{O,i} = s_O(r_i, m̄, c_Wr_im̄)`,
`o_i = s_{O,i} + C_{lo}L²s_{O,i}`):

* `se_k = c_W(L)r_{k-1}`, `so_k = M_{a,k-1}M_bo_{k-1}`,
  `sw_k = 2L²so_k((1+se_k)^{L²} - 1)s_k^{-2}/|β_{a,k+1}|`, `ηw = 0`;
* `Λ_i = M_{a,i}M_bC_{lo}L²s_{O,i}/|β_{a,i+1}|`,
  `Wp_i = M_{a,i}M_bL²o_i((1+c_W(L)r_i)^{L²} - 1)/|β_{a,i+1}|`.

* **`PairESizesAtK`/`PairESizesK`**: the items still open — `κ^Q` (item 1), `|M₄_k(X)|` (3), the
  `T_{k+1}(4s_k)` sizes `δ` of `dABX` (5) and `e` of `V'^{near}_∅` (6), and `F` of
  `F_C(dABX_i, V'^{near}_∅)` (9);
* **`pairESizesR_of_K_MF`**: `PairESizesK ⇒ PairESizesR` (under `PairVB`, `PairUnitSeed`, the seed
  condition of the `𝒲` chain);
* **`pairJointSizesP_of_VRK`**: `PairJointSizesP` from `PairUnitSeed`, `c_r ≤ m̄`, the two seed
  conditions, and per `x` the data `κ^Q, μ, δ, e, F`, a path, the first summability condition and
  `PairESizesK` (`L ≥ L₀` for the constants of `wpo_bounds_AB`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The items of `PairESizesAt` still open** (1, 3, 5, 6, 9). -/
def PairESizesAtK (m b μ₀ : ℝ) (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N) (k : ℕ)
    (κQ μ δ e F : ℕ → ℝ) : Prop :=
  (∀ Y, IsSmall k Y → Tj 2 (L : ℝ) k
        (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (PtCorr2.hKR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k Y : Obs.SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (κQ k * ‖hBeta R m b μ₀ x (k + 1)‖)) ∧
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
          ENNReal.ofReal (F i * ‖hBeta R m b μ₀ x (i + 1)‖))

/-- `PairESizesAtK` at every `k < n` under `VB n` and the masses below `n`. -/
def PairESizesK (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cr : ℝ) (x : Lam 2 L N) (VB : ℕ → Prop) (κQ μ δ e F : ℕ → ℝ) : Prop :=
  ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh + 1 → VB n →
    (∀ n', n' < n → PairMassUpTo R m b μ₀ lam oR cr x n') →
    ∀ k, Obs.coal L (0 : Lam 2 L N) x ≤ k → k < n →
      PairESizesAtK R m b μ₀ oR x k κQ μ δ e F

/-- `r_i = max(cǧ_i, 0)`. -/
def eszR (c m b μ₀ : ℝ) (i : ℕ) : ℝ := max (c * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i).1) 0

/-- `s_{O,i} = s_O(r_i, m̄, c_Wr_im̄)`. -/
def eszSO (c C₁w mbar m b μ₀ : ℝ) (i : ℕ) : ℝ :=
  sO 2 L (eszR R c m b μ₀ i) mbar ((4 * C₁w + 1) * eszR R c m b μ₀ i * mbar)

/-- `o_i = s_{O,i} + C_{lo}L²s_{O,i}`. -/
def eszO (c C₁w mbar Clo m b μ₀ : ℝ) (i : ℕ) : ℝ :=
  eszSO R c C₁w mbar m b μ₀ i + Clo * ((L : ℝ) ^ 2 * eszSO R c C₁w mbar m b μ₀ i)

/-- `se_k = c_W(L)r_{k-1}`. -/
def eszSe (c Clb m b μ₀ : ℝ) (k : ℕ) : ℝ := cWblk 2 L Clb * eszR R c m b μ₀ (k - 1)

/-- `so_k = M_{a,k-1}M_bo_{k-1}`. -/
def eszSo (c C₁w mbar Clo m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (k : ℕ) : ℝ :=
  vwA R m b μ₀ x (k - 1) * vwB R m b μ₀ lam x * eszO R c C₁w mbar Clo m b μ₀ (k - 1)

/-- `sw_k = 2L²so_k((1+se_k)^{L²} - 1)s_k^{-2}/|β_{a,k+1}|`. -/
def eszSw (c C₁w mbar Clo Clb m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (k : ℕ) : ℝ :=
  2 * ((L : ℝ) ^ 2 * eszSo R c C₁w mbar Clo m b μ₀ lam x k *
    ((1 + eszSe R c Clb m b μ₀ k) ^ (L ^ 2) - 1) * (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) /
    ‖hBeta R m b μ₀ x (k + 1)‖

/-- `Λ_i = M_{a,i}M_bC_{lo}L²s_{O,i}/|β_{a,i+1}|`. -/
def eszLam (c C₁w mbar Clo m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (i : ℕ) : ℝ :=
  vwA R m b μ₀ x i * vwB R m b μ₀ lam x * (Clo * ((L : ℝ) ^ 2 * eszSO R c C₁w mbar m b μ₀ i)) /
    ‖hBeta R m b μ₀ x (i + 1)‖

/-- `Wp_i = M_{a,i}M_bL²o_i((1+c_W(L)r_i)^{L²} - 1)/|β_{a,i+1}|`. -/
def eszWp (c C₁w mbar Clo Clb m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (i : ℕ) : ℝ :=
  vwA R m b μ₀ x i * vwB R m b μ₀ lam x * ((L : ℝ) ^ 2 * eszO R c C₁w mbar Clo m b μ₀ i *
    ((1 + cWblk 2 L Clb * eszR R c m b μ₀ i) ^ (L ^ 2) - 1)) / ‖hBeta R m b μ₀ x (i + 1)‖

end Traj

set_option maxHeartbeats 4000000 in
/-- **`PairESizesK ⇒ PairESizesR`**: the items 2, 10, 11 from the `𝒲` chain (see the module
docstring). -/
theorem pairESizesR_of_K_MF {L : ℕ} [NeZero L] (M : MasterFacts L) {Clo Clb : ℝ}
    (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb) :
    ∃ C₁w : ℝ, 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → ∀ κQ μ δ e F : ℕ → ℝ,
      PairESizesK R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x (PairVB R m b μ₀ lam x mbar)
        κQ μ δ e F →
      PairESizesR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x (PairVB R m b μ₀ lam x mbar) κQ
        (eszSe R M.core.c Clb m b μ₀) (eszSo R M.core.c C₁w mbar Clo m b μ₀ lam x)
        (eszSw R M.core.c C₁w mbar Clo Clb m b μ₀ lam x) (fun _ => 0) μ δ e F
        (eszLam R M.core.c C₁w mbar Clo m b μ₀ lam x)
        (eszWp R M.core.c C₁w mbar Clo Clb m b μ₀ lam x) := by
  obtain ⟨C₁w, hC₁w, hW⟩ := pairWSizes_MF M hWB hClo hClb
  refine ⟨C₁w, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar h8 x hx h1 hj
    κQ μ δ e F hK
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x (k + 1) ≠ 0 := by
    obtain ⟨q, -, -, hl⟩ :=
      (M.loop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
    intro k hk
    exact (hBeta_rel_of R hNh hb x
      (M.relG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1)
      (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1 k hk).2.1
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  have hrE : ∀ i ≤ Nh, eszR R M.core.c m b μ₀ i = M.core.c * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) i).1 := fun i hi =>
    max_eq_left (mul_nonneg hc0 (hadm.1 i hi).1.le)
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, -, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  intro n hn1 hn2 hVB hMs k hk1 hk2
  obtain ⟨a1, a3, a5, a6, a9⟩ := hK n hn1 hn2 hVB hMs k hk1 hk2
  have hWi := fun i (hi1 : Obs.coal L (0 : Lam 2 L N) x ≤ i) (hin : i < n) (hiN : i < Nh) =>
    hW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj n hn2
      hVB i hi1 hin hiN
  refine ⟨a1, ?_, a3, a5, a6, a9, ?_, ?_⟩
  · -- item 2: the `𝒲'_{k-1}` block
    intro X
    dsimp only
    intro hjk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hiN : i < Nh := by omega
    obtain ⟨hblk, -⟩ := hWi i (by omega) (by omega) hiN
    simp only [Nat.add_sub_cancel]
    refine ⟨fun B => ?_, fun B => ?_, ?_⟩
    · by_cases hB : B ∈ blockIdx (L := L) (N := N) i
      · refine (hblk B hB).1.trans (le_of_eq ?_)
        unfold eszSe; rw [Nat.add_sub_cancel, hrE i hiN.le]
      · refine le_trans (le_of_eq (congrArg (Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (M.core.wpoOff N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) _ hobs hanc i
            (by omega) hiN hB).1)) ?_
        rw [Step.Tj_zero]; exact zero_le
    · by_cases hB : B ∈ blockIdx (L := L) (N := N) i
      · refine (hblk B hB).2.1.trans (le_of_eq ?_)
        unfold eszSo eszO eszSO; rw [Nat.add_sub_cancel, hrE i hiN.le]
      · refine le_trans (le_of_eq (congrArg (Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (M.core.wpoOff N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) _ hobs hanc i
            (by omega) hiN hB).2)) ?_
        rw [Step.Tj_zero]; exact zero_le
    · have hβ : 0 < ‖hBeta R m b μ₀ x (i + 1 + 1)‖ := norm_pos_iff.2 (hβne (i + 1) (by omega))
      unfold eszSw
      rw [div_mul_cancel₀ _ hβ.ne', zero_mul, add_zero]
      exact le_rfl
  · -- item 10: `Loc S_i(B)_{ab}`
    intro i hi1 hi2 B hB
    have hBI : B ∈ blockIdx (L := L) (N := N) i := by
      rcases hB with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
    obtain ⟨hblk, -⟩ := hWi i hi1 (by omega) (by omega)
    have hβ : 0 < ‖hBeta R m b μ₀ x (i + 1)‖ := norm_pos_iff.2 (hβne i (by omega))
    refine (hblk B hBI).2.2.trans (le_of_eq ?_)
    unfold eszLam eszSO
    rw [div_mul_cancel₀ _ hβ.ne', hrE i (by omega)]
  · -- item 11: the product parts
    intro i hi1 hi2 c' hc'
    have hcI : c' ∈ blockIdx (L := L) (N := N) (i + 1) := by
      rcases hc' with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
    obtain ⟨-, hprod⟩ := hWi i hi1 (by omega) (by omega)
    have hβ : 0 < ‖hBeta R m b μ₀ x (i + 1)‖ := norm_pos_iff.2 (hβne i (by omega))
    refine (hprod c' hcI).trans (le_of_eq ?_)
    unfold eszWp eszO eszSO
    rw [div_mul_cancel₀ _ hβ.ne', hrE i (by omega)]

theorem sO_nonneg' {L : ℕ} {r mV mW : ℝ} (hr : 0 ≤ r) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW) :
    0 ≤ sO 2 L r mV mW := by
  unfold sO
  have hQ := Step2.one_le_Q1 (d := 2) one_le_two
  have hn : (0 : ℝ) ≤ Step2.cNear 2 L := Nat.cast_nonneg _
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn) (by positivity))
    (mul_nonneg hr hmV)) (mul_nonneg (by linarith) hmW)

theorem cWblk_nonneg' {L : ℕ} {Cl : ℝ} (hCl : 0 ≤ Cl) : 0 ≤ cWblk 2 L Cl := by
  have hQ := one_le_Q1 (d := 2) one_le_two
  have hn : (0 : ℝ) ≤ cNear 2 L := Nat.cast_nonneg _
  unfold cWblk cSblk
  generalize Q1 2 = q at *
  generalize cNear 2 L = cn at *
  have : 0 ≤ cn * q ^ 2 + q := by positivity
  positivity

theorem vwA_nonneg (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (x : Lam 2 L N) (i : ℕ) : 0 ≤ vwA R m b μ₀ x i := by
  unfold vwA; split_ifs
  · norm_num
  · positivity

/-- The sequences of items 2, 10, 11 are nonnegative. -/
theorem esz_nonneg (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {c C₁w mbar Clo Clb m b μ₀ : ℝ}
    {lam : ℕ → ℂ} {x : Lam 2 L N} (hc : 0 ≤ c) (hC₁w : 0 ≤ C₁w) (hmbar : 0 ≤ mbar) (hClo : 0 ≤ Clo)
    (hClb : 0 ≤ Clb) (hB : 0 ≤ vwB R m b μ₀ lam x) (k : ℕ) :
    0 ≤ eszSe R c Clb m b μ₀ k ∧ 0 ≤ eszSo R c C₁w mbar Clo m b μ₀ lam x k ∧
      0 ≤ eszSw R c C₁w mbar Clo Clb m b μ₀ lam x k ∧ 0 ≤ eszLam R c C₁w mbar Clo m b μ₀ lam x k ∧
      0 ≤ eszWp R c C₁w mbar Clo Clb m b μ₀ lam x k := by
  have hr : ∀ i, 0 ≤ eszR R c m b μ₀ i := fun i => le_max_right _ _
  have hsO : ∀ i, 0 ≤ eszSO R c C₁w mbar m b μ₀ i := fun i =>
    sO_nonneg' (hr i) hmbar (mul_nonneg (mul_nonneg (by linarith) (hr i)) hmbar)
  have hO : ∀ i, 0 ≤ eszO R c C₁w mbar Clo m b μ₀ i := fun i =>
    add_nonneg (hsO i) (mul_nonneg hClo (mul_nonneg (by positivity) (hsO i)))
  have hW := cWblk_nonneg' (L := L) hClb
  have hSe : 0 ≤ eszSe R c Clb m b μ₀ k := mul_nonneg hW (hr _)
  have hSo : 0 ≤ eszSo R c C₁w mbar Clo m b μ₀ lam x k :=
    mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hB) (hO _)
  have hp : ∀ y : ℝ, 0 ≤ y → 0 ≤ (1 + y) ^ (L ^ 2) - 1 := fun y hy => by
    have := one_le_pow₀ (n := L ^ 2) (show (1 : ℝ) ≤ 1 + y by linarith); linarith
  refine ⟨hSe, hSo, ?_, ?_, ?_⟩
  · unfold eszSw
    exact div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      hSo) (hp _ hSe)) (sq_nonneg _))) (norm_nonneg _)
  · unfold eszLam
    exact div_nonneg (mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hB)
      (mul_nonneg hClo (mul_nonneg (by positivity) (hsO _)))) (norm_nonneg _)
  · unfold eszWp
    exact div_nonneg (mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hB)
      (mul_nonneg (mul_nonneg (by positivity) (hO _)) (hp _ (mul_nonneg hW (hr _)))))
      (norm_nonneg _)

set_option maxHeartbeats 4000000 in
/-- **`PairJointSizesP` from the remaining items** (see the module docstring). -/
theorem pairJointSizesP_of_VRK : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ M : MasterFacts L,
    ∃ C₁w C₁w' Clo Clb : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁w' ∧ 0 ≤ Clo ∧ 0 ≤ Clb ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu ce ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      cr ≤ mbar → 0 ≤ ca →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁w * ((4 * C₁w + 1) * mbar) →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ (κQ μ δ e F : ℕ → ℝ) (w : List (Dir 2)),
        Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
        (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ F k) ∧
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * κQ k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              (eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * 3 +
              2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) (pdSz R m b μ₀ w μ) F
                (eszLam R M.core.c C₁w' mbar Clo m b μ₀ lam x) (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x)
                (tauSz R m b μ₀ M.core.ce) k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
        PairESizesK R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x (PairVB R m b μ₀ lam x mbar)
          κQ μ δ e F) →
    PairJointSizesP R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  obtain ⟨Clo, Clb, hClo, hClb, L₀, hWBL⟩ := wpo_bounds_AB
  refine ⟨L₀, fun L _ hL M => ?_⟩
  have hWB := hWBL L hL
  obtain ⟨C₁w, hC₁w, hVR⟩ := pairJointSizesP_of_VR_MF M
  obtain ⟨C₁w', hC₁w', hRK⟩ := pairESizesR_of_K_MF M hWB hClo hClb
  refine ⟨C₁w, C₁w', Clo, Clb, hC₁w, hC₁w', hClo, hClb, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ce ca cr mbar hU hmbar hcr hca
    h8 h8' hX
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  refine hVR N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ce ca cr mbar hU hmbar hcr h8
    fun x hx h1 hj => ?_
  obtain ⟨κQ, μ, δ, e, F, w, hw, h0, hsum, hK⟩ := hX x hx h1 hj
  have hB : 0 ≤ vwB R m b μ₀ lam x :=
    mul_nonneg (norm_nonneg _) (hadm.1 _ hj).1.le
  have hE := fun k => esz_nonneg R (c := M.core.c) (C₁w := C₁w') (mbar := mbar) (Clo := Clo)
    (Clb := Clb) (m := m) (b := b) (μ₀ := μ₀) (lam := lam) (x := x) hc0 hC₁w' hmbar.le hClo hClb hB k
  refine ⟨κQ, eszSe R M.core.c Clb m b μ₀, eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x,
    eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x, fun _ => 0, μ, δ, e, F,
    eszLam R M.core.c C₁w' mbar Clo m b μ₀ lam x, eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x,
    w, hw, fun k => ?_, fun k => ?_, hsum, ?_,
    hRK N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar h8' x hx h1 hj
      κQ μ δ e F hK⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := h0 k
    obtain ⟨-, -, -, b4, b5⟩ := hE k
    exact ⟨a1, a2, a3, a4, a5, b4, b5⟩
  · obtain ⟨b1, b2, b3, -, -⟩ := hE k
    exact ⟨b1, b2, b3, le_rfl⟩
  · simp only [mul_zero, Finset.sum_const_zero]
    exact hca

end

end Spin2
