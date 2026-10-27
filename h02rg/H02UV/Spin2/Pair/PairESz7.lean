import Spin2.Pair.PairESz6

/-!
# The `E`-step sizes (7): `PairESizes3` discharged for the reduced states

**`pairESizes3_MF`**: under `MasterFacts` (and `L ≥ L₀` through `WpOBoundsAB`), along every
admissible trajectory, for `PairUnitSeed c_u`, `0 < m̄` and the two seed conditions of the `ab`
chain (`C₁w` of `pairKSSizes_MF`, `C₁w'` of `pairWSizes_MF`), for every `x` and every lattice path
`w` from `0` to `x` with `|w| ≤ 2|x|_∞`: `PairESizes3 … (PairVB … m̄)` holds with the explicit
sequences of `Spin2/Pair/PairESz6` (items 1, 3 (`μ^Q`, `μ^S`), 5, 6, 9, `c_ν`, `P`), of
`Spin2/Pair/PairESz4` (the `𝒲` items, `ηw = 0`), `c_n = 3` and `τ = tauSz`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

set_option maxHeartbeats 8000000 in
/-- **`pairESizes3_MF` at given constants** (`hAH`, `hAH'`: `MasterCore.abwHist` at `(C₁k, C₁w)`, `(C₁k', C₁w')`). -/
theorem pairESizes3_MFat {L : ℕ} [NeZero L] (M : MasterFacts L) {Clo Clb : ℝ}
    (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb) {C₁k C₁w C₁k' C₁w' : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hAH : M.core.AbwHistP C₁k C₁w)
    (hAH' : M.core.AbwHistP C₁k' C₁w') :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ w : List (Dir 2), Obs2.pathEnd (0 : Lam 2 L N) w = x → (w.length : ℝ) ≤ 2 * sXp x →
      PairESizes3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x (PairVB R m b μ₀ lam x mbar)
        (e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x)
        (eszSe R M.core.c Clb m b μ₀) (eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x)
        (eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (fun _ => 0)
        (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x) (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3)
        (e6Nu R M Nh m b μ₀) (e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
        (e6E R M m b μ₀) (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
        (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
        (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) := by
  have hKS := pairKSSizes_MFat M hC₁k hC₁w hAH
  have hW := pairWSizes_MFat M hWB hClo hClb hC₁w' hAH'
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu cr mbar hU hmbar h8 h8' x hx
    h1 hj w hw hwl
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL49 : 49 ≤ L := M.core.hL49
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hL0 : (0 : ℝ) < L := by linarith
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by omega
  obtain ⟨hV, hVL, hG, hRI⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
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
  have htop := (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1
  have hnn : ∀ k ≤ Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8 := fun k hk => by
    rcases Nat.lt_or_ge k Nh with h | h
    · exact (hl k h).1
    · rw [show k = Nh by omega]; exact htop.1
  have htadR : ∀ i k, Obs2.tadInc2 (ptsX x) (Obs2.histCovO (R.withMsq m) t)
      (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t) i k = tadO R m b μ₀ x i k :=
    fun i k => PtCorr2.tadInc2_hR_eq hobs (Obs2.obsInit_isObs .two (zV b) (ptsX x)) i k
  have hL2' : (2 : ℝ) / L ≤ 1 / 2 := by
    have hL4 : (4 : ℝ) ≤ L := by exact_mod_cast (show 4 ≤ L by omega)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x (k + 1) ≠ 0 := fun k hk =>
    (hBeta_rel_of R hNh hb x
      (M.relG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1) htop k hk).2.1
  have hβp : ∀ k ≤ Nh, 0 < ‖hBeta R m b μ₀ x (k + 1)‖ := fun k hk => norm_pos_iff.2 (hβne k hk)
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k t := fun k => histS_pos' (R.withMsq m) hρ0 hρ8 t k
  have hsq : ∀ k, histS (R.withMsq m) (k + 1) t ≤ 9 / 8 * histS (R.withMsq m) k t :=
    fun k => histS_succ_le_q (R.withMsq m) hρ0 hρ8 t k
  have hz0 : ∀ b', ((oRed R m b μ₀ dxStd x).V b' : SA .two (Lam 2 L N)).ab = 0 :=
    fun b' => oRed_V_ab_zero R m b μ₀ dxStd x b'
  have hab : (ptsX x).a ≠ (ptsX x).b := fun h => hx h.symm
  have hpe : Obs2.pathEnd (ptsX x).a w = (ptsX x).b := hw
  have hsX0 : 0 ≤ sXp x := Nat.cast_nonneg _
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  have hg0 : ∀ i ≤ Nh, 0 ≤ (t i).1 := fun i hi => (hadm.1 i hi).1.le
  have hmono := M.gmono N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hgm : ∀ i l, i ≤ l → l ≤ Nh → (t i).1 ≤ (t l).1 := by
    intro i l hil hl'
    have key : ∀ n, i + n ≤ Nh → (t i).1 ≤ (t (i + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (i + n) (by omega))
    have := key (l - i) (by omega)
    rwa [show i + (l - i) = l by omega] at this
  -- the sizes of the history
  set QK := kszQ R M C₁k C₁w mbar cu m b μ₀ lam x with hQKd
  set SS := kszS R M C₁w mbar m b μ₀ lam x with hSSd
  have hvwA := vwA_nonneg R m b μ₀ x
  have hvwB : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) (hg0 j hj)
  have hQ0 : ∀ i, 0 ≤ QK i := fun i => by
    rw [hQKd]; unfold kszQ
    exact mul_nonneg (mul_nonneg (hvwA _) hvwB) (mul_nonneg (by norm_num) (le_max_right _ _))
  have hS0 : ∀ i, 0 ≤ SS i := fun i => by rw [hSSd]; unfold kszS; exact le_max_right _ _
  have hcS : ∀ i, ∀ b' ∈ blockIdx (L := L) (N := N) i,
      (open Classical in ((smallSets (d := 2) (L := L) (N := N) i).filter
        (fun X => blockSet i b' ⊆ X)).card : ℝ) ≤ (cSm2 : ℝ) :=
    fun i b' hb' => by exact_mod_cast cSm2_spec L N i b' hb'
  have hcN : ∀ i (y : Lam 2 L N) (s : Finset (Fin 2 → ℕ)), s ⊆ blockIdx (L := L) (N := N) i →
      ((s.filter (fun b' => y ∈ nbhd i (blockSet (L := L) (N := N) i b'))).card : ℝ) ≤ (cNb2 : ℝ) :=
    fun i y s hs' => by exact_mod_cast cNb2_spec L N i y s hs'
  -- the sequences are nonnegative
  have hGr0 : ∀ k, 0 ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    gradRHS_nonneg hL0 (Obs2.KG_nonneg 2 (Cc := Ccut2) (by norm_num)) (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hM40 : ∀ k, 0 ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    m4RHS_nonneg hL0 (KM4_nonneg 2 (Cc := Ccut2)) hsX0
      hs (fun i => by have := hQ0 i; positivity) (fun i => by have := hS0 i; positivity) _ _
  have hLop0 : ∀ k ℓ', 0 ≤ ℓ' → 0 ≤ e6Lop R m b μ₀ x w.length k ℓ' := fun k ℓ' hℓ' => by
    unfold e6Lop; positivity
  intro n hn1 hn2 hVB hMs k hk1 hk2
  have hkN : k ≤ Nh := by omega
  have hKSi := fun i (hi1 : j ≤ i) (hin : i < n) =>
    hKS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar h8 x hx h1 hj n hn2
      hVB i hi1 hin (by omega)
  have hFi := fun i (hi1 : j ≤ i) (hiN : i < Nh) =>
    M.core.vhistF N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
      (oRed R m b μ₀ dxStd x) hloc0 hsymj hanc i hi1 hiN
  -- the per-scale gradient and `M₄` sizes of the blocks at `k' < n`
  have hGr : ∀ k', j ≤ k' → k' < n → ∀ c ∈ blockIdx (L := L) (N := N) k',
      gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ k') (histS (R.withMsq m) k' t)
          (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
            SA .two (Lam 2 L N)).ab ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k' ∧
      ‖cfAB4 (ptsX x).a (ptsX x).b (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
          SA .two (Lam 2 L N)).ab‖ ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k' := by
    intro k' hk1' hk' c hc
    exact M.core.vhistG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) hab w hpe hwl
      (oRed R m b μ₀ dxStd x) hloc0 hsymj hanc hVab hz0 hk1' (by omega) QK SS hQ0 hS0
      (fun i hi hik Y hY => (hKSi i hi (by omega)).1 Y hY)
      (fun i hi hik b' hb' => ((hKSi i hi (by omega)).2 (by omega) b' hb').1) c hc
  -- the per-block bounds for every block (off the lattice blocks the `ab` part vanishes)
  have hGrA : ∀ k', j ≤ k' → k' < n → ∀ c,
      gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ k') (histS (R.withMsq m) k' t)
          (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
            SA .two (Lam 2 L N)).ab ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k' ∧
      ‖cfAB4 (ptsX x).a (ptsX x).b (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k' c :
          SA .two (Lam 2 L N)).ab‖ ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k' := by
    intro k' hk1' hk' c
    by_cases hc : c = blk k' (ptsX x).a ∨ c = blk k' (ptsX x).b
    · have hcI : c ∈ blockIdx (L := L) (N := N) k' := by
        rcases hc with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
      exact hGr k' hk1' hk' c hcI
    · push Not at hc
      rw [hVR_ab_anch (R.withMsq m) (ptsX x) j _ t hanc hk1' c hc.1 hc.2]
      refine ⟨?_, ?_⟩
      · have : gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ k')
            (histS (R.withMsq m) k' t) (0 : Alg 2 L N) = 0 := by
          unfold gradM4Sz; simp [cfAB2, cfAB4, coeff_zero]
        rw [this]; exact hGr0 k'
      · rw [show cfAB4 (ptsX x).a (ptsX x).b (0 : Alg 2 L N) = 0 from coeff_zero _, norm_zero]
        exact hM40 k'
  -- the `LopM4` term
  have hLop : ∀ k', k' ≤ Nh → ∀ ℓ', 0 ≤ ℓ' →
      gradM4Sz {(ptsX x).a} (ptsX x).a (ptsX x).b ((L : ℝ) ^ (k' + 1)) ℓ'
          (LopM4 (histCovO (R.withMsq m) t k') (ptsX x).a (ptsX x).b) ≤
        e6Lop R m b μ₀ x w.length k' ℓ' := by
    intro k' hk' ℓ' hℓ'
    obtain ⟨hc1, hc2, hc3⟩ := covDiff_le_path (hG k' hk') (ptsX x).a w
    rw [hpe] at hc2 hc3
    refine (gradM4Sz_LopM4_le (by positivity) hℓ' _ hab hc1 hc2 hc3).trans ?_
    have hE : eN1 {(ptsX x).a} (ptsX x).a (ptsX x).b ≤ 2 * sXp x := by
      have := eN1_single_le (d := 2) (ptsX x).a (ptsX x).b
      unfold sXp; push_cast at this ⊢; linarith
    have hE0 := eN1_nonneg {(ptsX x).a} (ptsX x).a (ptsX x).b
    have hg : eN1 {(ptsX x).a} (ptsX x).a (ptsX x).b * ℓ' * ((L : ℝ) ^ (k' + 1))⁻¹ ≤
        2 * sXp x * ℓ' * ((L : ℝ) ^ (k' + 1))⁻¹ := by gcongr
    have hg0 : 0 ≤ eN1 {(ptsX x).a} (ptsX x).a (ptsX x).b * ℓ' * ((L : ℝ) ^ (k' + 1))⁻¹ := by
      positivity
    unfold e6Lop
    have hd0 : 0 ≤ (w.length : ℝ) * (histS (R.withMsq m) k' t ^ 2 / (L : ℝ) ^ (k' + 1)) := by
      positivity
    gcongr
  -- the near bulk `V'` at the field scale `4ℓ`, `ℓ ≥ s_{k'}/…`
  have hNear : ∀ k', k' ≤ Nh → ∀ (ℓ₀ ℓ' cc : ℝ), 0 < ℓ' → ℓ₀ ≤ ℓ' → 1 ≤ cc →
      GoodCov2 k' ℓ₀ (histCovO (R.withMsq m) t k') →
      2 * ℓ' ≤ cc * histS (R.withMsq m) k' t →
      Tj 2 (L : ℝ) (k' + 1) ℓ'
          (PtCorr2.gNear (0 : Lam 2 L N) x k' (blockIdx (L := L) (N := N) k') fun c =>
            (Obs2.VprO (Obs2.histCovO (R.withMsq m) t k')
              (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k') c :
                Obs.SA .two (Lam 2 L N)).e) ≤
        ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2 * (cc ^ 4 * (M.core.c * (t k').1))) := by
    classical
    intro k' hk' ℓ₀ ℓ' cc hℓ' hℓ₀ hcc hC hcs
    unfold PtCorr2.gNear
    have hcard := card_near_le (0 : Lam 2 L N) x (j := k') (by omega)
      (blockIdx (L := L) (N := N) k') subset_rfl
    have hu0 : 0 ≤ cc ^ 4 * (M.core.c * (t k').1) :=
      mul_nonneg (by positivity) (mul_nonneg hc0 (hg0 k' hk'))
    have hterm : ∀ c ∈ (blockIdx (L := L) (N := N) k').filter (PtCorr2.NearAB (0 : Lam 2 L N) x k'),
        Tj 2 (L : ℝ) (k' + 1) ℓ' (Obs2.VprO (Obs2.histCovO (R.withMsq m) t k')
          (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k') c :
            Obs.SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (cc ^ 4 * (M.core.c * (t k').1)) := by
      intro c hc
      have hcI := (mem_filter.1 hc).1
      refine (Tj_VprO_e_le hℓ' hℓ₀ hC _ c).trans ?_
      refine (tNorm_mono (pow_pos hL0 k').le le_rfl (by linarith) hcs _).trans ?_
      exact M.core.vhistE N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
        (oRed R m b μ₀ dxStd x) hobs k' hk' hcc c hcI
    refine (tNorm_sum_le _ _).trans ?_
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have h2 : (((blockIdx (L := L) (N := N) k').filter
        (PtCorr2.NearAB (0 : Lam 2 L N) x k')).card : ENNReal) ≤
        ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hcard
    calc _ ≤ ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2) *
          ENNReal.ofReal (cc ^ 4 * (M.core.c * (t k').1)) := mul_le_mul_right' h2 _
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  -- the gradient part of a region at `T_{k'+1}(ℓ')`
  have hDel : ∀ k', j ≤ k' → k' < n → ∀ (ℓ' qq : ℝ), 0 < ℓ' → 1 ≤ qq →
      ℓ' ≤ qq * histS (R.withMsq m) k' t → ∀ X : Finset (Lam 2 L N),
      Tj 2 (L : ℝ) (k' + 1) ℓ'
          (Obs2.dABX (ptsX x) k' (Obs2.histCovO (R.withMsq m) t k')
            (PtCorr2.hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t k') X) ≤
        ENNReal.ofReal (2 * (qq ^ 4 * (L : ℝ)⁻¹ * e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k' +
          e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k' * e6Lop R m b μ₀ x w.length k' ℓ')) := by
    intro k' hk1' hk' ℓ' qq hℓ' hqq hlq X
    refine Tj_dABX_le (ptsX x) hab k' _ _ X (hVR_ab_mem (R.withMsq m) (ptsX x) j _ t hVab k')
      (hVR_ab_sym (R.withMsq m) (ptsX x) j _ t (hsym k' hk1' (by omega)))
      (fun c h1' h2' => hVR_ab_anch (R.withMsq m) (ptsX x) j _ t hanc hk1' c h1' h2') hℓ'
      (mul_nonneg (by positivity) (hGr0 k')) (hM40 k') (hLop0 k' ℓ' hℓ'.le)
      (fun c => (gradM4Sz_scale_le hℓ'.le hqq hlq _ _ _).trans
        (mul_le_mul_of_nonneg_left (hGrA k' hk1' hk' c).1 (by positivity)))
      (fun c => (hGrA k' hk1' hk' c).2) (hLop k' (by omega) ℓ' hℓ'.le)
  refine ⟨fun Y hY => ?_, fun X => ?_, fun X i hi1 hi2 => ?_, fun X i hi1 hi2 => ?_, ?_, ?_,
    fun X => ?_, ?_, fun X i hi1 hi2 => ?_, fun i hi1 hi2 => ?_, fun X i hi1 hi2 => ?_,
    fun i hi1 hi2 c' hc' => ?_⟩
  · -- item 1: `κ^Q`
    refine ((hKSi k hk1 hk2).1 Y hY).trans (le_of_eq ?_)
    unfold e6KQ; rw [div_mul_cancel₀ _ (hβp k hkN).ne']
  · -- item 2: the `𝒲'_{k-1}` block
    dsimp only
    intro hjk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hiN : i < Nh := by omega
    obtain ⟨hblk, -⟩ := hW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar
      h8' x hx h1 hj n hn2 hVB i (by omega) (by omega) hiN
    have hrE : eszR R M.core.c m b μ₀ i = M.core.c * (t i).1 :=
      max_eq_left (mul_nonneg hc0 (hg0 i hiN.le))
    simp only [Nat.add_sub_cancel]
    refine ⟨fun B => ?_, fun B => ?_, ?_⟩
    · by_cases hB : B ∈ blockIdx (L := L) (N := N) i
      · refine (hblk B hB).1.trans (le_of_eq ?_)
        unfold eszSe; rw [Nat.add_sub_cancel, hrE]; rfl
      · refine le_trans (le_of_eq (congrArg (Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t))
          (M.core.wpoOff N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) _ hobs hanc i
            (by omega) hiN hB).1)) ?_
        rw [Step.Tj_zero]; exact zero_le
    · by_cases hB : B ∈ blockIdx (L := L) (N := N) i
      · refine (hblk B hB).2.1.trans (le_of_eq ?_)
        unfold eszSo eszO eszSO; rw [Nat.add_sub_cancel, hrE]; rfl
      · refine le_trans (le_of_eq (congrArg (Tj 2 (L : ℝ) (i + 1) (histS (R.withMsq m) (i + 1) t))
          (M.core.wpoOff N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) _ hobs hanc i
            (by omega) hiN hB).2)) ?_
        rw [Step.Tj_zero]; exact zero_le
    · have hβ := hβp (i + 1) (by omega)
      unfold eszSw
      rw [div_mul_cancel₀ _ hβ.ne', zero_mul, add_zero]
      exact le_rfl
  · -- item 3a: `μ^Q`
    have hiN : i < Nh := by omega
    have hF := hFi i hi1 hiN
    have hκ := kappaQ_le_count (ptsX x) (hKR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i) X
      hF.2.2.2.2.1.hK (hQ0 i) ((hKSi i hi1 (by omega)).1) (hcS i) (hcN i)
    refine (norm_m4QX_le (R.withMsq m) (ptsX x) j _ t Ccut2_spec.1 Ccut2_spec.2 hL8 hab X (hs i)
      hF.2.2.2.2.2.1 hκ).trans (le_of_eq ?_)
    unfold e6MQ sXp
    rw [div_mul_cancel₀ _ (hβp i hiN.le).ne']
  · -- item 3b: `μ^S`
    have hiN : i < Nh := by omega
    have hF := hFi i hi1 hiN
    have hκ := kappaS_le_count (ptsX x) (i := i)
      (fun U => (SXO i (histCovO (R.withMsq m) t i)
        (hVR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i)
        (hWR (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) t i) U : SA .two (Lam 2 L N)).ab) X
      (fun b' hb' hn' => ((hKSi i hi1 (by omega)).2 hiN b' hb').2 hn') (hS0 i)
      (fun b' hb' => ((hKSi i hi1 (by omega)).2 hiN b' hb').1)
    refine (norm_m4LSX_le (R.withMsq m) (ptsX x) j _ t Ccut2_spec.1 Ccut2_spec.2 hL8 hab
      (by omega) X (hs (i + 1)) hF.2.2.2.2.2.2 hκ).trans (le_of_eq ?_)
    unfold e6MS sXp
    rw [div_mul_cancel₀ _ (hβp i hiN.le).ne']
  · -- item 4: `|1 − n_a| ≤ 3`
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
    have hs' : ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ ≤ 1 := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => ?_).trans
        (geom_tail_two_le (by positivity) hL2' k))
      have hik := Finset.mem_range.1 hi
      refine (htad (ptsX x) (zV b) i k hik hkN).trans ?_
      have hc := hcg i (by omega)
      have hp : 0 ≤ (2 / (L : ℝ)) ^ (k - i) := by positivity
      calc M.core.ce * (2 / (L : ℝ)) ^ (k - i) * (t i).1
          = (2 / (L : ℝ)) ^ (k - i) * (M.core.ce * (t i).1) := by ring
        _ ≤ (2 / (L : ℝ)) ^ (k - i) * 1 := mul_le_mul_of_nonneg_left hc hp
        _ = _ := mul_one _
    have hn := hnn k hkN
    calc ‖1 - (nn2 R (ptsX x) (zV b) m b μ₀ k - ∑ i ∈ Finset.range k, tadO R m b μ₀ x i k)‖
        ≤ ‖(1 : ℂ)‖ + ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ +
            ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ := by
          refine (norm_sub_le _ _).trans ?_
          have := norm_sub_le (nn2 R (ptsX x) (zV b) m b μ₀ k)
            (∑ i ∈ Finset.range k, tadO R m b μ₀ x i k)
          linarith
      _ ≤ 3 := by rw [norm_one]; linarith
  · -- the vertex factor `|n_k| ≤ c_{ν,k}`
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
    have hgk := hg0 k hkN
    have hmk : max (t k).1 0 = (t k).1 := max_eq_left hgk
    have hs' : ‖∑ i ∈ Finset.range k, tadO R m b μ₀ x i k‖ ≤ M.core.ce * (t k).1 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ Finset.range k, ‖tadO R m b μ₀ x i k‖
          ≤ ∑ i ∈ Finset.range k, (M.core.ce * (t k).1) * (2 / (L : ℝ)) ^ (k - i) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hik := Finset.mem_range.1 hi
            refine (htad (ptsX x) (zV b) i k hik hkN).trans ?_
            have hgi := hgm i k hik.le hkN
            have hp : 0 ≤ (2 / (L : ℝ)) ^ (k - i) := by positivity
            calc M.core.ce * (2 / (L : ℝ)) ^ (k - i) * (t i).1
                = (M.core.ce * (2 / (L : ℝ)) ^ (k - i)) * (t i).1 := rfl
              _ ≤ (M.core.ce * (2 / (L : ℝ)) ^ (k - i)) * (t k).1 :=
                  mul_le_mul_of_nonneg_left hgi (mul_nonneg hct hp)
              _ = _ := by ring
        _ = (M.core.ce * (t k).1) * ∑ i ∈ Finset.range k, (2 / (L : ℝ)) ^ (k - i) := by
            rw [Finset.mul_sum]
        _ ≤ (M.core.ce * (t k).1) * 1 :=
            mul_le_mul_of_nonneg_left (geom_tail_two_le (by positivity) hL2' k)
              (mul_nonneg hct hgk)
        _ = _ := mul_one _
    have hn : ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤
        (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) := by
      split_ifs with hkl
      · rw [hmk]
        exact (hl k hkl).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgk)
      · exact hnn k hkN
    show _ ≤ (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) +
      M.core.ce * max (t k).1 0
    rw [hmk]
    rw [hmk] at hn
    refine (norm_sub_le _ _).trans ?_
    linarith
  · -- item 5: `δ_k`
    refine (hDel k hk1 hk2 (2 * (2 * histS (R.withMsq m) k t)) 4 (by have := hs k; positivity)
      (by norm_num) (by linarith [hs k]) X).trans (le_of_eq ?_)
    unfold e6Del
    rw [div_mul_cancel₀ _ (hβp k hkN).ne']
  · -- item 6: `e_k`
    have h := hNear k hkN (histS (R.withMsq m) k t) (2 * (2 * histS (R.withMsq m) k t)) 8
      (by have := hs k; positivity) (by linarith [hs k]) (by norm_num) (hG k hkN) (by linarith)
    refine h.trans (le_of_eq ?_)
    show _ = ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2 * ((8 : ℝ) ^ 4 * (M.core.c * max (t k).1 0)))
    rw [max_eq_left (hg0 k hkN)]
  · -- item 7: the Pauli defects
    have hiN : i ≤ Nh := by omega
    have h := PtCorr2.pdefM2X_hVR_le (R.withMsq m) (ptsX x) t hVab (hsym i hi1 hiN) (hG i hiN) w hpe X
    have hm4 := norm_m4X_le_two (R.withMsq m) (ptsX x) j _ t hanc hi1 X (hM40 i)
      (fun c => (hGrA i hi1 (by omega) c).2)
    refine h.trans ?_
    unfold pdSz e6M4X
    have hsq' := sq_nonneg ((w.length : ℝ) * (histS (R.withMsq m) i t / (L : ℝ) ^ (i + 1)))
    set D := ((w.length : ℝ) * (histS (R.withMsq m) i t / (L : ℝ) ^ (i + 1))) ^ 2 with hD
    set μi := e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x i with hμi
    have hβi := (hβp i hiN).ne'
    have e : 2 * μi / ‖hBeta R m b μ₀ x (i + 1)‖ * D * ‖hBeta R m b μ₀ x (i + 1)‖ = 2 * μi * D := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hm4 hsq'
  · -- item 8: `tadInc₂`
    rw [htadR]
    have h := htad (ptsX x) (zV b) i k hi2 hkN
    show _ ≤ M.core.ce * (2 / (L : ℝ)) ^ (k - i) * max (t i).1 0
    rw [max_eq_left (hg0 i (by omega))]
    exact h
  · -- item 9: `F_C(dABX_i, V'^{near}_∅)`
    have hiN : i < Nh := by omega
    have hF := hFi i hi1 hiN
    have hC1 : GoodCov2 i (histS (R.withMsq m) (i + 1) t) (histCovO (R.withMsq m) t i) :=
      hF.1.mono (by
        show histS (R.withMsq m) (i + 1) t / 4 ≤ histS (R.withMsq m) (i + 1) t
        linarith [hs (i + 1)])
    have hA := hDel i hi1 (by omega) (2 * (2 * histS (R.withMsq m) (i + 1) t)) (9 / 2)
      (by have := hs (i + 1); positivity) (by norm_num) (by linarith [hsq i]) X
    have hB := hNear i hiN.le (histS (R.withMsq m) (i + 1) t / 4)
      (2 * (2 * histS (R.withMsq m) (i + 1) t)) 9 (by have := hs (i + 1); positivity)
      (by linarith [hs (i + 1)]) (by norm_num) hF.1 (by linarith [hsq i, hs (i + 1)])
    refine (tNorm_FC_gen_le (hs (i + 1)) hC1 _ _).trans ?_
    have hd0 : 0 ≤ e6DelF R M C₁k C₁w mbar cu m b μ₀ lam x w.length i := by
      unfold e6DelF
      exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 i))
        (mul_nonneg (hM40 i) (hLop0 i _ (by have := hs (i + 1); positivity))))
    have he0 : 0 ≤ 2 * ((L : ℝ) + 39) ^ 2 * ((9 : ℝ) ^ 4 * (M.core.c * (t i).1)) :=
      mul_nonneg (by positivity) (mul_nonneg (by positivity) (mul_nonneg hc0 (hg0 i hiN.le)))
    calc 2 * (Tj 2 (L : ℝ) (i + 1) (2 * (2 * histS (R.withMsq m) (i + 1) t)) _ *
          Tj 2 (L : ℝ) (i + 1) (2 * (2 * histS (R.withMsq m) (i + 1) t)) _)
        ≤ 2 * (ENNReal.ofReal (e6DelF R M C₁k C₁w mbar cu m b μ₀ lam x w.length i) *
          ENNReal.ofReal (2 * ((L : ℝ) + 39) ^ 2 * ((9 : ℝ) ^ 4 * (M.core.c * (t i).1)))) := by
          gcongr
          exact hA
      _ = ENNReal.ofReal (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length i *
          ‖hBeta R m b μ₀ x (i + 1)‖) := by
          show _ = ENNReal.ofReal (2 * (e6DelF R M C₁k C₁w mbar cu m b μ₀ lam x w.length i *
            (2 * ((L : ℝ) + 39) ^ 2 * ((9 : ℝ) ^ 4 * (M.core.c * max (t i).1 0)))) /
            ‖hBeta R m b μ₀ x (i + 1)‖ * ‖hBeta R m b μ₀ x (i + 1)‖)
          rw [max_eq_left (hg0 i hiN.le), div_mul_cancel₀ _ (hβp i hiN.le).ne',
            ← ENNReal.ofReal_mul hd0, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_ofNat]
  · -- item 10: the product parts
    have hiN : i < Nh := by omega
    have hcI : c' ∈ blockIdx (L := L) (N := N) (i + 1) := by
      rcases hc' with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
    obtain ⟨-, hprod⟩ := hW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu mbar hU hmbar
      h8' x hx h1 hj n hn2 hVB i hi1 (by omega) hiN
    have hrE : eszR R M.core.c m b μ₀ i = M.core.c * (t i).1 :=
      max_eq_left (mul_nonneg hc0 (hg0 i hiN.le))
    refine (hprod c' hcI).trans (le_of_eq ?_)
    unfold eszWp eszO eszSO
    rw [div_mul_cancel₀ _ (hβp i hiN.le).ne', hrE]
    rfl

set_option maxHeartbeats 8000000 in
/-- **`PairESizes3` for the reduced states** (see the module docstring). -/
theorem pairESizes3_MF {L : ℕ} [NeZero L] (M : MasterFacts L) {Clo Clb : ℝ}
    (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb) :
    ∃ C₁k C₁w C₁w' : ℝ, 0 ≤ C₁k ∧ 0 ≤ C₁w ∧ 0 ≤ C₁w' ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ w : List (Dir 2), Obs2.pathEnd (0 : Lam 2 L N) w = x → (w.length : ℝ) ≤ 2 * sXp x →
      PairESizes3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr x (PairVB R m b μ₀ lam x mbar)
        (e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x)
        (eszSe R M.core.c Clb m b μ₀) (eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x)
        (eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (fun _ => 0)
        (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x) (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3)
        (e6Nu R M Nh m b μ₀) (e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
        (e6E R M m b μ₀) (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
        (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
        (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) := by
  obtain ⟨C₁k, C₁w, hC₁k, hC₁w, hAH⟩ := M.core.abwHist
  exact ⟨C₁k, C₁w, C₁w, hC₁k, hC₁w, hC₁w,
    pairESizes3_MFat M hWB hClo hClb hC₁k hC₁w hC₁w hAH hAH⟩

end

end Spin2
