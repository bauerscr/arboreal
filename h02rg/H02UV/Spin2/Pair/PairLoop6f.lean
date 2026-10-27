import Spin2.Pair.PairLoop6e

/-!
# The constant loop, per scale (6): **`pl6_item_le`** (task 1)

See `Spin2/Pair/PairLoop6e` for the statement and the constants.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

set_option maxHeartbeats 16000000 in
/-- **The per-scale bound for the explicit sequences** (see `Spin2/Pair/PairLoop6e`). -/
theorem pl6_item_le {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w C₁w' Clo Clb : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (hθ : C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) * (M.core.c * M.core.ε) ≤ 1 / 72)
    (hpow : (1 + cWblk 2 L Clb * (M.core.c * M.core.ε)) ^ (L ^ 2) ≤ 2)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) {cu mbar : ℝ} (hcu : 0 ≤ cu) (hmbar : 0 ≤ mbar)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (w : List (Dir 2)) (hwl : (w.length : ℝ) ≤ 2 * sXp x)
    (k : ℕ) (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hk : k ≤ Nh) :
    2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
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
        (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k ≤
      vwB R m b μ₀ lam x * (pl6CEM M C₁k C₁w C₁w' Clo Clb *
        pl6NF (Obs.coal L (0 : Lam 2 L N) x) (pl6k0 M cu) mbar (pl6r R m b μ₀ M.core.c) k) +
      (if k < Nh then 0 else
        vwB R m b μ₀ lam x * (pl6CNM L C₁w * (mbar * (M.core.c * M.core.ε)))) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL49 : 49 ≤ L := M.core.hL49
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨-, hVL, -, -⟩ := M.core.pairTraj N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k t := fun k => histS_pos' (R.withMsq m) hρ0 hρ8 t k
  obtain ⟨hct, -, hcg⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨q, -, -, hl⟩ :=
    (M.loop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  have htop := (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := fun k hk => by
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1) htop k hk
    exact ⟨a1, a2⟩
  have hβr := pairBetaRatio_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm x
  obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    exact (hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm).1
  have hc1 : 1 ≤ M.core.c := by
    rw [← hcR]
    have hcV : 0 ≤ cV (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm := by
      unfold cV cZ; have := Hap.hcmu; positivity
    have hcW : 0 ≤ cW (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x := by
      unfold cW; have := Hap.hC₂; positivity
    unfold cR; linarith
  have hc0 : 0 ≤ M.core.c := by linarith
  have hcx : 0 ≤ cx M.core.κ M.core.cT := Hap.hcx
  have hg : ∀ i ≤ Nh, 0 < (t i).1 ∧ (t i).1 ≤ M.core.ε := fun i hi =>
    ⟨(hadm.1 i hi).1, (hadm.1 i hi).2.1⟩
  have hε0 : 0 ≤ M.core.ε := ((hg 0 (Nat.zero_le _)).1.trans_le (hg 0 (Nat.zero_le _)).2).le
  have hcε : M.core.c * M.core.ε ≤ 1 := M.core.hcε
  have hmono := M.gmono N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  -- the sequence `r`
  have hrE : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i = M.core.c * (t i).1 := fun i hi => by
    show M.core.c * max (t i).1 0 = _; rw [max_eq_left (hg i hi).1.le]
  have hrε : ∀ i ≤ Nh, pl6r R m b μ₀ M.core.c i ≤ M.core.c * M.core.ε := fun i hi => by
    rw [hrE i hi]; exact mul_le_mul_of_nonneg_left (hg i hi).2 hc0
  have hr0 : ∀ i, 0 ≤ pl6r R m b μ₀ M.core.c i := fun i => mul_nonneg hc0 (le_max_right _ _)
  have hgr : ∀ i ≤ Nh, max (t i).1 0 ≤ pl6r R m b μ₀ M.core.c i := fun i hi => by
    show max (t i).1 0 ≤ M.core.c * max (t i).1 0
    have := le_max_right (t i).1 0; nlinarith
  have heszR : ∀ i ≤ Nh, eszR R M.core.c m b μ₀ i = pl6r R m b μ₀ M.core.c i := fun i hi => by
    show max (M.core.c * (t i).1) 0 = _
    rw [hrE i hi]; exact max_eq_left (mul_nonneg hc0 (hg i hi).1.le)
  -- the ratio facts
  have H : PL6H j Nh (L : ℝ) (sXp x) (fun i => histS (R.withMsq m) i t)
      (fun i => ‖hBeta R m b μ₀ x i‖) (pl6r R m b μ₀ M.core.c) :=
    { hL := by exact_mod_cast hL49
      hs0 := hs
      hs1 := fun i => histS_succ_le_q (R.withMsq m) hρ0 hρ8 t i
      hs2 := fun i => histS_sq_ratio (R.withMsq m) hρ0 hρ8 t i
      hβ0 := fun i => norm_nonneg _
      hβp := fun i hi => by
        rcases Nat.lt_or_ge i (Nh + 1) with h | h
        · exact norm_pos_iff.2 (hβne i (by omega)).1
        · rw [show i = Nh + 1 by omega]; exact norm_pos_iff.2 (hβne Nh le_rfl).2
      hβr := hβr
      hr0 := hr0
      hr1 := fun i hi => (hrε i hi).trans hcε
      hsx := Nat.cast_nonneg _
      hsxL := by
        have h2 := two_supNorm_lt_coal (by omega : 2 ≤ L) x
        have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm (x - 0) := by
          show supNorm ((0 : Lam 2 L N) - x) = supNorm (x - 0)
          rw [supNorm_sub_comm]
        unfold sXp; rw [hsn]
        have : ((2 * supNorm (x - 0) : ℕ) : ℝ) ≤ ((L ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast h2.le
        push_cast at this; exact this }
  have hβj : 0 < ‖hBeta R m b μ₀ x j‖ := H.hβp j (by omega)
  -- the master constants
  have hK4 : 0 ≤ KM4 2 Ccut2 := KM4_nonneg 2
  have hKG : 0 ≤ Obs2.KG 2 Ccut2 4 := Obs2.KG_nonneg 2 (by norm_num)
  have hcNS : 0 ≤ 2 * (cNb2 : ℝ) * (cSm2 : ℝ) := by positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (d := 2) one_le_two
  have hcN : 0 ≤ Step2.cNear 2 L := by unfold Step2.cNear; exact Nat.cast_nonneg _
  have hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa := by
    unfold kθ0
    have := M.core.hA2
    exact mul_nonneg M.core.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hθa : kθ0 L M.core.A M.core.C₀a M.core.ηa ≤ 1 / 72 := (M.core.hAa M.core.hLa).2
  set Bk := kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT) with hBkd
  have hBk : 0 ≤ Bk := by rw [hBkd]; unfold kB; positivity
  have hcWc : 0 ≤ 4 * C₁w + 1 := by linarith
  have hcWc' : 0 ≤ 4 * C₁w' + 1 := by linarith
  have hcW : 0 ≤ cWblk 2 L Clb := cWblk_nonneg' hClb
  have hcB : 0 ≤ max M.core.B' 0 + M.core.ce := add_nonneg (le_max_right _ _) hct
  have hAs : ∀ c', 0 ≤ c' → 0 ≤ pl6As L c' := fun c' hc' => pl6As_nonneg hc'
  have haQ : 0 ≤ pl6aQ Bk (4 * C₁w + 1) := by unfold pl6aQ pl6ρ; positivity
  have hcQ : 0 ≤ pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) := by
    unfold pl6cQ; exact mul_nonneg hcNS haQ
  have hcS : 0 ≤ pl6cS L (4 * C₁w + 1) := by unfold pl6cS; have := hAs _ hcWc; positivity
  have hcM : 0 ≤ pl6cM L (KM4 2 Ccut2) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) := by
    unfold pl6cM; positivity
  have hcG : 0 ≤ pl6cG L (KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk
      (4 * C₁w + 1) := by unfold pl6cG; positivity
  have hcO : 0 ≤ pl6cO L Clo (4 * C₁w' + 1) := by unfold pl6cO; have := hAs _ hcWc'; positivity
  set V := vwB R m b μ₀ lam x with hVd
  have hV : 0 ≤ V := mul_nonneg (norm_nonneg _) (hg j hj).1.le
  set k₀ := pl6k0 M cu with hk₀d
  have hk₀ : 0 ≤ k₀ := by
    rw [hk₀d]; unfold pl6k0
    have := M.ιW_ge; have := M.core.hA2
    exact mul_nonneg hcu (pow_nonneg (by positivity) _)
  -- `vwA = 2s²β` below `N_h + 1`
  have hvwA : ∀ i ≤ Nh, vwA R m b μ₀ x i = 2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖ :=
    fun i hi => by unfold vwA; rw [if_neg (hβne i hi).1]
  -- the small-set sizes in profile form
  set θ := 8 * (kθ0 L M.core.A M.core.C₀a M.core.ηa + C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) *
      (M.core.c * M.core.ε)) with hθd
  have hθ0 : 0 ≤ θ := by rw [hθd]; positivity
  have hθρ : θ * pl6ρ ≤ 1 / 2 := by
    have h29 : θ ≤ 2 / 9 := by rw [hθd]; linarith
    unfold pl6ρ; nlinarith
  have hK : ∀ i, j ≤ i → i ≤ Nh →
      2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        kszK R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ *
        (128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
          (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i)) := fun i hji hi =>
    pl6_kseq H (r' := fun i => M.core.c * (t i).1)
      (m' := fun i => (4 * C₁w + 1) * (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar))
      hθ0 hθρ hBk hcWc hk₀ hmbar (fun i hi => (hrE i hi).symm)
      (fun i hji hi => by
        show 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * ((4 * C₁w + 1) *
          (vwA R m b μ₀ x i * V / (vwA R m b μ₀ x j * V) * mbar)) ≤
          (4 * C₁w + 1) * (2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖) * mbar
        rw [hvwA i hi, hvwA j hj]
        rcases hV.eq_or_lt with h0 | hpos
        · rw [← h0]; simp only [mul_zero, div_zero, zero_mul]
          have := hs i; positivity
        · have hA : 0 < 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ := by
            have := hs j; positivity
          rw [mul_div_mul_right _ _ hpos.ne']
          apply le_of_eq
          have := (hs j).ne'
          have := (H.hβp j (by omega)).ne'
          field_simp)
      hji hi
  have hkszQ : ∀ i, j ≤ i → i ≤ Nh → kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i) := by
    intro i hji hi
    have hA : 0 < 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ := by
      have := hs j; positivity
    have hKi := hK i hji hi
    set X := 128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) *
      (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) with hXd
    have hP0 := pl6P_nonneg (j := j) hk₀ i
    have hQ0 := pl6Q_nonneg (j := j) (r := pl6r R m b μ₀ M.core.c) i
    have hc₁ : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) := by unfold pl6ρ; positivity
    have hX0 : 0 ≤ X := by rw [hXd]; positivity
    have hT0 : 0 ≤ histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ := by positivity
    have hmax : 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
        max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0 ≤
        histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X := by
      rw [mul_max_of_nonneg _ _ hA.le, mul_zero]
      exact max_le hKi (mul_nonneg hT0 hX0)
    have h8 : 8 * X ≤ pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i := by
      have e : pl6aQ Bk (4 * C₁w + 1) * pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i =
          8 * X + 8 * (128 / 49 * (mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i) +
            4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i) := by
        rw [hXd]; unfold pl6aQ pl6G0; ring
      rw [e]; have : 0 ≤ mbar * pl6Q j (pl6r R m b μ₀ M.core.c) i := mul_nonneg hmbar hQ0
      have : 0 ≤ 4 * pl6ρ * (64 / 49) * Bk * (4 * C₁w + 1) * pl6P j k₀ i := mul_nonneg hc₁ hP0
      linarith
    unfold kszQ
    rw [hvwA j hj]
    calc 2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ * V *
          (8 * max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) =
        8 * V * (2 * histS (R.withMsq m) j t ^ 2 * ‖hBeta R m b μ₀ x j‖ *
          max (kszK R M C₁k C₁w mbar cu m b μ₀ lam x i) 0) := by ring
      _ ≤ 8 * V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * X) := by gcongr
      _ = V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) * (8 * X) := by ring
      _ ≤ _ := by gcongr
  have hkszS : ∀ i, j ≤ i → i ≤ Nh → kszS R M C₁w mbar m b μ₀ lam x i ≤
      V * (histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖) *
        (128 / 49 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * (mbar * pl6r R m b μ₀ M.core.c i)) := by
    intro i hji hi
    have e : vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar)) =
        2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * ‖hBeta R m b μ₀ x i‖ := by
      rw [hvwA i hi, hrE i hi]; unfold sO pl6As; ring
    have hB := H.hβr i hi
    have hX0 : 0 ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
        (mbar * pl6r R m b μ₀ M.core.c i) := by
      have := hAs _ hcWc; have := hr0 i; positivity
    show max (vwA R m b μ₀ x i * V * ((L : ℝ) ^ 2 * sO 2 L (M.core.c * (t i).1) mbar
        ((4 * C₁w + 1) * (M.core.c * (t i).1) * mbar))) 0 ≤ _
    rw [e]
    have := hAs _ hcWc; have := hr0 i
    refine max_le ?_ (by positivity)
    calc _ ≤ 2 * (L : ℝ) ^ 2 * pl6As L (4 * C₁w + 1) * V * histS (R.withMsq m) i t ^ 2 *
          (mbar * pl6r R m b μ₀ M.core.c i) * (64 / 49 * ‖hBeta R m b μ₀ x (i + 1)‖) :=
          mul_le_mul_of_nonneg_left hB hX0
      _ = _ := by ring
  -- the abstract sizes
  set κQ : ℕ → ℝ := fun i => 2 * (cNb2 : ℝ) * (cSm2 : ℝ) * kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i
    with hκQd
  set κS : ℕ → ℝ := fun i => 2 * (L : ℝ) ^ 2 * kszS R M C₁w mbar m b μ₀ lam x i with hκSd
  have hQK0 : ∀ i, 0 ≤ kszQ R M C₁k C₁w mbar cu m b μ₀ lam x i := fun i => by
    unfold kszQ
    exact mul_nonneg (mul_nonneg (vwA_nonneg R m b μ₀ x _) hV)
      (mul_nonneg (by norm_num) (le_max_right _ _))
  have hSK0 : ∀ i, 0 ≤ kszS R M C₁w mbar m b μ₀ lam x i := fun i => by
    unfold kszS; exact le_max_right _ _
  have hκQ0 : ∀ i, 0 ≤ κQ i := fun i => mul_nonneg hcNS (hQK0 i)
  have hκS0 : ∀ i, 0 ≤ κS i := fun i => mul_nonneg (by positivity) (hSK0 i)
  have hκQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (histS (R.withMsq m) i t ^ 2 *
      ‖hBeta R m b μ₀ x (i + 1)‖) * (pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) *
        pl6G0 j k₀ mbar (pl6r R m b μ₀ M.core.c) i) := fun i hji hi => by
    have := mul_le_mul_of_nonneg_left (hkszQ i hji hi) hcNS
    calc κQ i ≤ _ := this
      _ = _ := by unfold pl6cQ; ring
  have hκS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (histS (R.withMsq m) i t ^ 2 *
      ‖hBeta R m b μ₀ x (i + 1)‖) * (pl6cS L (4 * C₁w + 1) *
        (mbar * pl6r R m b μ₀ M.core.c i)) := fun i hji hi => by
    have := mul_le_mul_of_nonneg_left (hkszS i hji hi) (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) ^ 2)
    calc κS i ≤ _ := this
      _ = _ := by unfold pl6cS; ring
  have hwl0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  -- the profile constants
  set cQ := pl6cQ (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) with hcQd
  set cS := pl6cS L (4 * C₁w + 1) with hcSd
  set cM := pl6cM L (KM4 2 Ccut2) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk (4 * C₁w + 1) with hcMd
  set cG := pl6cG L (KM4 2 Ccut2) (Obs2.KG 2 Ccut2 4) (2 * (cNb2 : ℝ) * (cSm2 : ℝ)) Bk
    (4 * C₁w + 1) with hcGd
  set r := pl6r R m b μ₀ M.core.c with hrd
  have hcMe : cM = KM4 2 Ccut2 * (cQ / (L : ℝ) ^ 2 + 6 / 5 * cS) := by rw [hcMd]; rfl
  have hcGe : cG = (L : ℝ) * (3 / 4 * (L : ℝ) ^ 2 * (KM4 2 Ccut2 * (cQ / (L : ℝ) ^ 2 + 6 / 5 * cS)) +
      (2 * Obs2.KG 2 Ccut2 4 / (L : ℝ) + 243 / 64) * cQ + (2 * Obs2.KG 2 Ccut2 4 + 3) * cS) := by
    rw [hcGd]; rfl
  -- the gradient and `M₄` sizes
  have hγ : ∀ i, i ≤ Nh → e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x i ≤
      histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x (i + 1)‖ * V *
        (cG * pl6FO j k₀ mbar r i) := fun i hi => by
    rw [hcGe]
    exact pl6_grad H hK4 hKG hV hk₀ hmbar hcQ hcS hκQ0 hκS0 hκQ hκS hi
  have hml : ∀ i, i ≤ Nh → ∀ ℓ', 0 ≤ ℓ' →
      e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x i * e6Lop R m b μ₀ x w.length i ℓ' ≤
      12 * ℓ' ^ 2 * (‖hBeta R m b μ₀ x (i + 1)‖ * V * (cM * pl6FO j k₀ mbar r i)) :=
    fun i hi ℓ' hℓ' => by
      rw [hcMe]
      exact pl6_m4lop H hK4 hV hk₀ hmbar hcQ hcS hκQ0 hκS0 hκQ hκS hwl0 hwl hℓ' hi
  have hGr0 : ∀ k, 0 ≤ e6Gr R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    gradRHS_nonneg hL0 hKG hK4 (Nat.cast_nonneg _) hs hκQ0 hκS0 _ _
  have hM40 : ∀ k, 0 ≤ e6M4 R M C₁k C₁w mbar cu m b μ₀ lam x k := fun k =>
    m4RHS_nonneg hL0 hK4 (Nat.cast_nonneg _) hs hκQ0 hκS0 _ _
  have hLop0 : ∀ k ℓ', 0 ≤ ℓ' → 0 ≤ e6Lop R m b μ₀ x w.length k ℓ' := fun k ℓ' hℓ' => by
    unfold e6Lop; have : (0 : ℝ) ≤ sXp x := Nat.cast_nonneg _; positivity
  -- group 1
  have g1 : 2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
      (histS (R.withMsq m) k t)⁻¹ ^ 2) ≤
      V * (2 * Q1 2 * cQab * pl6aQ Bk (4 * C₁w + 1) * pl6NF j k₀ mbar r k) :=
    pl6_g1 H hk (by linarith) cQab_nonneg haQ hV hk₀ hmbar (hkszQ k hjk hk)
  -- group 2
  have g2 : eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k ≤
      V * (4 * (L : ℝ) ^ 4 * cWblk 2 L Clb * pl6cO L Clo (4 * C₁w' + 1) * (6 / 5) * (64 / 49) ^ 2 *
        pl6NF j k₀ mbar r k) := by
    have hk1 : 1 ≤ k := le_trans h1 hjk
    have hso : eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x k =
        V * (histS (R.withMsq m) (k - 1) t ^ 2 * ‖hBeta R m b μ₀ x (k - 1)‖) *
          (pl6cO L Clo (4 * C₁w' + 1) * (mbar * r (k - 1))) := by
      unfold eszSo eszO eszSO
      rw [hvwA (k - 1) (by omega), heszR (k - 1) (by omega)]
      unfold sO pl6cO pl6As; ring
    have hso0 : 0 ≤ eszSo R M.core.c C₁w' mbar Clo m b μ₀ lam x k := by
      rw [hso]; have := hr0 (k - 1); positivity
    have hse : eszSe R M.core.c Clb m b μ₀ k = cWblk 2 L Clb * r (k - 1) := by
      unfold eszSe; rw [heszR (k - 1) (by omega)]
    have hp : (1 + cWblk 2 L Clb * r (k - 1)) ^ (L ^ 2) ≤ 2 := by
      refine le_trans (pow_le_pow_left₀ (by have := hr0 (k - 1); positivity) ?_ _) hpow
      have := hrε (k - 1) (by omega)
      have := mul_le_mul_of_nonneg_left this hcW
      linarith
    have hmo : r (k - 1) ≤ r k := by
      rw [hrE (k - 1) (by omega), hrE k hk]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      have := hmono (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
    exact pl6_g2 H hjk hk1 hk hV hk₀ hmbar hcW hcO (by push_cast; ring) hso0 hso.le hse hp hmo
  -- group 3
  have g3 : spE3 j (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
        (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
        (fun k => (w.length * (histS (R.withMsq m) k t / (L : ℝ) ^ (k + 1))) ^ 2) k ≤
      V * ((12 * KM4 2 Ccut2 * cQ / (L : ℝ) ^ 2 + 24 / 5 * (max M.core.B' 0 + M.core.ce) *
        KM4 2 Ccut2 * cS) * pl6NF j k₀ mbar r k) +
      (if k < Nh then 0 else V * (27 / 5 * KM4 2 Ccut2 * cS * (mbar * (M.core.c * M.core.ε)))) :=
    pl6_g3 H (K₄ := KM4 2 Ccut2) (cQ := cQ) (cS := cS) (V := V) (k₀ := k₀) (mb := mbar)
    (wl := w.length) (cB := max M.core.B' 0 + M.core.ce) (cε := M.core.c * M.core.ε)
    (κQ := κQ) (κS := κS) (cν := e6Nu R M Nh m b μ₀) hK4 hV hk₀ hmbar hcQ hcS hcB hwl0 hwl
    hκQ0 hκS0 hκQ hκS hrε hk
    (by
      unfold e6Nu
      have h1' : 0 ≤ (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) := by
        split_ifs
        · exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
        · norm_num
      exact add_nonneg h1' (mul_nonneg hct (le_max_right _ _)))
    (fun hkN => by
      unfold e6Nu; rw [if_pos hkN]
      have := hgr k hk
      have : 0 ≤ max (t k).1 0 := le_max_right _ _
      calc max M.core.B' 0 * max (t k).1 0 + M.core.ce * max (t k).1 0 =
          (max M.core.B' 0 + M.core.ce) * max (t k).1 0 := by ring
        _ ≤ (max M.core.B' 0 + M.core.ce) * r k := by gcongr)
    (fun hkN => by
      change (if k < Nh then max M.core.B' 0 * max (t k).1 0 else 1 / 8) +
        M.core.ce * max (t k).1 0 ≤ 9 / 8
      rw [if_neg hkN, max_eq_left (hg k hk).1.le]
      have h' : M.core.ce * (t k).1 ≤ 1 := hcg k hk
      linarith)
  -- group 4
  have g4 : 2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
      (histS (R.withMsq m) k t)⁻¹ ^ 2 ≤
      V * (8 * (2 * ((L : ℝ) + 39) ^ 2 * 8 ^ 4) * (256 * cG / (L : ℝ) + 192 * cM) *
        pl6NF j k₀ mbar r k) :=
    pl6_g4 H hk (hGr0 k) (mul_nonneg (hM40 k) (hLop0 k _ (by have := hs k; positivity)))
      (by unfold e6E; have := le_max_right (t k).1 0; positivity) (by positivity) hcG hcM hV
      hk₀ hmbar (hγ k hk) (hml k hk _ (by have := hs k; positivity))
      (by unfold e6E; rw [hrd]; unfold pl6r; apply le_of_eq; ring)
  -- group 5
  have g5 : smE3 R m b μ₀ j (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
      (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
      (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k ≤
      V * ((16 * M.core.ce * cM + 2560 * locK 2 ^ 2 * (4 * (2 * ((L : ℝ) + 39) ^ 2 * 9 ^ 4) *
        ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cG / (L : ℝ) + 192 * cM)) +
        2560 * locK 2 ^ 2 * (2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb *
          (64 / 49) * (6 / 5))) * pl6NF j k₀ mbar r k) := by
    have hE := fun i => esz_nonneg R (c := M.core.c) (C₁w := C₁w') (mbar := mbar) (Clo := Clo)
      (Clb := Clb) (m := m) (b := b) (μ₀ := μ₀) (lam := lam) (x := x) hc0 hC₁w' hmbar hClo hClb
      hV i
    refine pl6_g5 H hk hct hcM (by positivity) (by positivity) hV hk₀ hmbar
      (fun i => by
        unfold pdSz e6M4X
        exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hM40 i)) (norm_nonneg _))
          (sq_nonneg _))
      (fun i => by
        show 0 ≤ M.core.ce * (2 / (L : ℝ)) ^ (k - i) * max (t i).1 0
        exact mul_nonneg (mul_nonneg hct (by positivity)) (le_max_right _ _))
      (fun i => by
        unfold e6F e6DelF e6EF
        refine div_nonneg (mul_nonneg (by norm_num) (mul_nonneg ?_ ?_)) (norm_nonneg _)
        · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by positivity) (hGr0 i))
            (mul_nonneg (hM40 i) (hLop0 i _ (by have := hs (i + 1); positivity))))
        · exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
            (mul_nonneg hc0 (le_max_right _ _))))
      (fun i => (hE i).2.2.2.2)
      (fun i hji hik => by
        rw [hcMe]
        exact pl6_Pd_le H hK4 hV hk₀ hmbar hcQ hcS hκQ0 hκS0 hκQ hκS hwl0 hwl (by omega))
      (fun i hji hik => by
        show M.core.ce * (2 / (L : ℝ)) ^ (k - i) * max (t i).1 0 ≤ _
        exact mul_le_mul_of_nonneg_left (hgr i (by omega)) (by positivity))
      (fun i hji hik =>
        pl6_F_le H (by omega) (hGr0 i)
          (mul_nonneg (hM40 i) (hLop0 i _ (by have := hs (i + 1); positivity)))
          (by unfold e6EF; have := le_max_right (t i).1 0; positivity) (by positivity) hcG hcM hV
          hk₀ hmbar (hγ i (by omega)) (hml i (by omega) _ (by have := hs (i + 1); positivity))
          (by unfold e6EF; rw [hrd]; unfold pl6r; apply le_of_eq; ring))
      (fun i hji hik => by
        have hiN : i ≤ Nh := by omega
        have hx0 : 0 ≤ cWblk 2 L Clb * r i := mul_nonneg hcW (hr0 i)
        have hpw : (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1 ≤ 2 * (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i) := by
          have h := pl6_pow_sub_one_le hx0 (L ^ 2)
          have hp2 : (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) ≤ 2 := by
            refine le_trans (pow_le_pow_left₀ (by positivity) ?_ _) hpow
            have := mul_le_mul_of_nonneg_left (hrε i hiN) hcW; linarith
          push_cast at h
          have : (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i) * (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) ≤
              (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i) * 2 :=
            mul_le_mul_of_nonneg_left hp2 (by positivity)
          nlinarith
        have hpw0 : 0 ≤ (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1 := by
          have : 1 ≤ (1 + cWblk 2 L Clb * r i) ^ (L ^ 2) := one_le_pow₀ (by linarith)
          linarith
        have hβi := H.hβp (i + 1) (by omega)
        have hβr' := H.hβr i hiN
        have hs2 := H.hs2 i
        have hO : eszO R M.core.c C₁w' mbar Clo m b μ₀ i =
            pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i) := by
          unfold eszO eszSO; rw [heszR i hiN]; unfold sO pl6cO pl6As; ring
        unfold eszWp
        rw [hvwA i hiN, hO, heszR i hiN, div_le_iff₀ hβi]
        have hA0 : 0 ≤ 2 * histS (R.withMsq m) i t ^ 2 * V *
            ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i))) := by
          have := hr0 i; positivity
        calc 2 * histS (R.withMsq m) i t ^ 2 * ‖hBeta R m b μ₀ x i‖ * V *
              ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i)) *
                ((1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1)) =
            (2 * histS (R.withMsq m) i t ^ 2 * V *
              ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i)))) *
              ((1 + cWblk 2 L Clb * r i) ^ (L ^ 2) - 1) * ‖hBeta R m b μ₀ x i‖ := by ring
          _ ≤ (2 * histS (R.withMsq m) i t ^ 2 * V *
              ((L : ℝ) ^ 2 * (pl6cO L Clo (4 * C₁w' + 1) / 2 * (mbar * r i)))) *
              (2 * (L : ℝ) ^ 2 * (cWblk 2 L Clb * r i)) *
                (64 / 49 * ‖hBeta R m b μ₀ x (i + 1)‖) := by gcongr
          _ = 2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb * (64 / 49) *
                (histS (R.withMsq m) i t ^ 2) * V * (mbar * r i ^ 2) *
                ‖hBeta R m b μ₀ x (i + 1)‖ := by ring
          _ ≤ 2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb * (64 / 49) *
                (6 / 5 * histS (R.withMsq m) (i + 1) t ^ 2) * V * (mbar * r i ^ 2) *
                ‖hBeta R m b μ₀ x (i + 1)‖ := by
              have : 0 ≤ 2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb *
                (64 / 49) := by positivity
              have : 0 ≤ mbar * r i ^ 2 := by positivity
              gcongr
          _ = _ := by ring)
  -- assemble
  have hsplit : V * (pl6CEM M C₁k C₁w C₁w' Clo Clb * pl6NF j k₀ mbar r k) =
      V * (2 * Q1 2 * cQab * pl6aQ Bk (4 * C₁w + 1) * pl6NF j k₀ mbar r k) +
      V * (4 * (L : ℝ) ^ 4 * cWblk 2 L Clb * pl6cO L Clo (4 * C₁w' + 1) * (6 / 5) * (64 / 49) ^ 2 *
        pl6NF j k₀ mbar r k) +
      V * ((12 * KM4 2 Ccut2 * cQ / (L : ℝ) ^ 2 + 24 / 5 * (max M.core.B' 0 + M.core.ce) *
        KM4 2 Ccut2 * cS) * pl6NF j k₀ mbar r k) +
      V * (8 * (2 * ((L : ℝ) + 39) ^ 2 * 8 ^ 4) * (256 * cG / (L : ℝ) + 192 * cM) *
        pl6NF j k₀ mbar r k) +
      V * ((16 * M.core.ce * cM + 2560 * locK 2 ^ 2 * (4 * (2 * ((L : ℝ) + 39) ^ 2 * 9 ^ 4) *
        ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cG / (L : ℝ) + 192 * cM)) +
        2560 * locK 2 ^ 2 * (2 * (L : ℝ) ^ 4 * pl6cO L Clo (4 * C₁w' + 1) * cWblk 2 L Clb *
          (64 / 49) * (6 / 5))) * pl6NF j k₀ mbar r k) := by
    rw [hcQd, hcSd, hcMd, hcGd]
    unfold pl6CEM pl6CE
    ring
  have hN : (if k < Nh then (0 : ℝ) else V * (27 / 5 * KM4 2 Ccut2 * cS *
      (mbar * (M.core.c * M.core.ε)))) =
      (if k < Nh then 0 else V * (pl6CNM L C₁w * (mbar * (M.core.c * M.core.ε)))) := by
    rw [hcSd]; unfold pl6CNM pl6CN; split_ifs <;> ring
  rw [hsplit, ← hN]
  linarith

end

end Spin2
