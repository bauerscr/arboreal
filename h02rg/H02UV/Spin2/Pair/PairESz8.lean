import Spin2.Pair.PairESz7

/-!
# The `E`-step sizes (8): `PairJointSizesP3` with only the first summability condition open

**`pairJointSizesP3_of_VS`**: `∃ L₀, ∀ L ≥ L₀, ∀ M : MasterFacts L, ∃` constants
(`C₁v` of `pairVStep_MF`, `C₁k, C₁w` of `pairKSSizes_MF`, `C₁w'` of `pairWSizes_MF`, `C_lo, C_lb`
of `wpo_bounds_AB`), along every admissible trajectory, for `PairUnitSeed c_u` (a theorem,
`Spin2/Pair/PairUnit`), `0 < m̄`, `c_r ≤ m̄`, `0 ≤ c_a`, the three seed conditions
`8c_u(2ι_WA)^{(L+18)²} ≤ vck(C₁v)(4C₁v+1)m̄`, `≤ (4C₁w+1)m̄`, `≤ (4C₁w'+1)m̄`, and, for every
`x` and every lattice path `w` from `0` to `x` with `|w| ≤ 2|x|_∞`, **the first summability
condition** on the explicit sequences (`Spin2/Pair/PairESz4`, `Spin2/Pair/PairESz6`) — `PairJointSizesP3`
holds for the reduced states. `PairESizes3` is discharged (`pairESizes3_MF`), the `V`-step by
`pairVStep_MF`; the second sum is `0 ≤ c_a` (`ηw = 0`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

set_option maxHeartbeats 8000000 in
/-- **`pairJointSizesP3_of_VS` at given constants** (`hAH`, `hAH'`: `MasterCore.abwHist` at `(C₁k, C₁w)`, `(C₁k', C₁w')`; `C_lo`, `C_lb` with `WpOBoundsAB`). -/
theorem pairJointSizesP3_of_VSat {L : ℕ} [NeZero L] (M : MasterFacts L)
    {Clo Clb C₁k C₁w C₁k' C₁w' : ℝ} (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hAH : M.core.AbwHistP C₁k C₁w)
    (hAH' : M.core.AbwHistP C₁k' C₁w') :
    ∃ C₁v : ℝ, 0 ≤ C₁v ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu ce ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      cr ≤ mbar → 0 ≤ ca →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁v * ((4 * C₁v + 1) * mbar) →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∀ w : List (Dir 2), Obs2.pathEnd (0 : Lam 2 L N) w = x → (w.length : ℝ) ≤ 2 * sXp x →
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k +
              spE3 (Obs.coal L (0 : Lam 2 L N) x) (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
                (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
                (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2) k +
              2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x)
                (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
                (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
                (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1) →
    PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  obtain ⟨C₁v, hC₁v, hVS⟩ := pairVStep_MF M
  have hES := pairESizes3_MFat M hWB hClo hClb hC₁k hC₁w hC₁w' hAH hAH'
  refine ⟨C₁v, hC₁v, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ce ca cr mbar hU hmbar hcr hca
    h8v h8 h8' hX
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  obtain ⟨hct, -, -⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨-, hVL, -, -⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := fun k =>
    histS_pos' (R.withMsq m) hρ0 hρ8 _ k
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by have := M.core.hL49; omega)
  refine pairJointSizesP3_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam ce ca cr
    fun x hx h1 hj => ?_
  obtain ⟨hVB0, hVs⟩ := hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU
    hmbar hcr h8v x hx h1 hj
  -- the path from `0` to `x`
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (0 : Lam 2 L N) w = x := by
    rw [Obs2.pathEnd, zero_add, hwx]
  have hwl' : (w.length : ℝ) ≤ 2 * sXp x := by
    unfold sXp
    have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm x := by
      show supNorm ((0 : Lam 2 L N) - x) = supNorm x
      rw [zero_sub, supNorm_neg]
    rw [hsn]; exact_mod_cast hwl
  have hg0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 :=
    (hadm.1 _ hj).1.le
  have hvwB : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) hg0
  have hE := fun k => esz_nonneg R (c := M.core.c) (C₁w := C₁w') (mbar := mbar) (Clo := Clo)
    (Clb := Clb) (m := m) (b := b) (μ₀ := μ₀) (lam := lam) (x := x) hc0 hC₁w' hmbar.le hClo hClb
    hvwB k
  -- nonnegativity of the explicit sequences
  have hQ0 : ∀ i, 0 ≤ kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i := fun i => by
    unfold kszQ
    exact mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hvwB)
      (mul_nonneg (by norm_num) (le_max_right _ _))
  have hS0 : ∀ i, 0 ≤ kszS R M C₁w mbar m b μ₀ lam x i := fun i => by
    unfold kszS; exact le_max_right _ _
  have hsX0 : 0 ≤ sXp x := Nat.cast_nonneg _
  have hGr0 : ∀ k, 0 ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    gradRHS_nonneg hL0 (Obs2.KG_nonneg 2 (Cc := Ccut2) (by norm_num)) (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hM40 : ∀ k, 0 ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    m4RHS_nonneg hL0 (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hLop0 : ∀ k ℓ', 0 ≤ ℓ' → 0 ≤ e6Lop R m b μ₀ x w.length k ℓ' := fun k ℓ' hℓ' => by
    unfold e6Lop; positivity
  have hK4 := KM4_nonneg 2 (Cc := Ccut2)
  refine ⟨PairVB R m b μ₀ lam x mbar, e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x,
    eszSe R M.core.c Clb m b μ₀, eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x,
    eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x, fun _ => 0,
    e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x, e6MS R M C₁w mbar m b μ₀ lam x, fun _ => 3,
    e6Nu R M Nh m b μ₀, e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length, e6E R M m b μ₀,
    pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x),
    e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length,
    eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x, tauSz R m b μ₀ M.core.ce, w, hpe,
    fun k => ⟨?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_, (hE k).2.2.2.2⟩, fun i k => ?_,
    fun k => ⟨(hE k).1, (hE k).2.1, (hE k).2.2.1, le_rfl⟩,
    hX x hx h1 hj w hpe hwl', ?_, hVB0, hVs,
    hES N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar h8 h8' x hx h1 hj
      w hpe hwl'⟩
  · unfold e6KQ; exact div_nonneg (hQ0 k) (norm_nonneg _)
  · unfold e6MQ
    exact div_nonneg (mul_nonneg hK4 (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (hQ0 k)))) (norm_nonneg _)
  · unfold e6MS
    exact div_nonneg (mul_nonneg hK4 (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (hS0 k)))) (norm_nonneg _)
  · unfold e6Nu
    have h1' : 0 ≤ (if k < Nh then max M.core.B' 0 *
        max (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 0 else 1 / 8) := by
      split_ifs
      · exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
      · norm_num
    exact add_nonneg h1' (mul_nonneg hct (le_max_right _ _))
  · unfold e6Del
    exact div_nonneg (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 k))
      (mul_nonneg (hM40 k) (hLop0 k _ (by have := hs k; positivity))))) (norm_nonneg _)
  · unfold e6E
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (mul_nonneg hc0 (le_max_right _ _)))
  · unfold pdSz e6M4X
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hM40 k)) (norm_nonneg _)) (sq_nonneg _)
  · unfold e6F e6DelF e6EF
    refine div_nonneg (mul_nonneg (by norm_num) (mul_nonneg ?_ ?_)) (norm_nonneg _)
    · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 k))
        (mul_nonneg (hM40 k) (hLop0 k _ (by have := hs (k + 1); positivity))))
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (mul_nonneg hc0 (le_max_right _ _)))
  · unfold tauSz
    exact mul_nonneg (mul_nonneg hct (pow_nonneg (by positivity) _)) (le_max_right _ _)
  · simp only [mul_zero, Finset.sum_const_zero]
    exact hca

set_option maxHeartbeats 8000000 in
/-- **`PairJointSizesP3` from the first summability condition** (see the module docstring). -/
theorem pairJointSizesP3_of_VS : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ M : MasterFacts L,
    ∃ C₁v C₁k C₁w C₁w' Clo Clb : ℝ, 0 ≤ C₁v ∧ 0 ≤ C₁k ∧ 0 ≤ C₁w ∧ 0 ≤ C₁w' ∧ 0 ≤ Clo ∧ 0 ≤ Clb ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu ce ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      cr ≤ mbar → 0 ≤ ca →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁v * ((4 * C₁v + 1) * mbar) →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∀ w : List (Dir 2), Obs2.pathEnd (0 : Lam 2 L N) w = x → (w.length : ℝ) ≤ 2 * sXp x →
        ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
            (2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
              (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
              eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k +
              spE3 (Obs.coal L (0 : Lam 2 L N) x) (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
                (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
                (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2) k +
              2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
              smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x)
                (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
                (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
                (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k) ≤
          ce * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1) →
    PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr := by
  obtain ⟨Clo, Clb, hClo, hClb, L₀, hWBL⟩ := wpo_bounds_AB
  refine ⟨L₀, fun L _ hL M => ?_⟩
  obtain ⟨C₁k, C₁w, hC₁k, hC₁w, hAH⟩ := M.core.abwHist
  obtain ⟨C₁v, hC₁v, H⟩ :=
    pairJointSizesP3_of_VSat M (hWBL L hL) hClo hClb hC₁k hC₁w hC₁w hAH hAH
  exact ⟨C₁v, C₁k, C₁w, C₁w, Clo, Clb, hC₁v, hC₁k, hC₁w, hC₁w, hClo, hClb, H⟩

end

end Spin2
