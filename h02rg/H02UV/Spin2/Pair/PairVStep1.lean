import Spin2.Master.MasterAllVStep
import Spin2.Pair.PairEStep1
import Spin2.Pair.PairSeedW

/-!
# The `V`-step of the joint induction for the reduced pair histories (`PairJointSizes`, `V`-part)

With the weights of the joint-induction analysis (Log, `thm_pairAbove_red_joint` section)

`M_{a,j} = 2s_j²|β_{a,j}|` (**`vwA`**), `M_b = ‖M_{j_x}‖ǧ_{j_x}` (**`vwB`**),

the `V`-predicate of the joint induction is **`PairVB … m̄ n`**: `‖V'_j(B)‖_{wM(M_{a,j}, M_b)} ≤ m̄`
for `j_x ≤ j < n` along the reduced history of `oRed … dxStd x`. The mass part of the `V`-bound is
then exact: `ρ_ns_n²/(M_{a,n}M_b) = c_r/2` with `ρ_n = c_r‖M_{j_x}‖ǧ_{j_x}|β_{a,n}|` from
`PairMassUpTo n` (region `X = B`, `k = M = n`).

The only unit relation is at the seed: `pairSeed_hK0` bounds `K'_{j_x}` in the weights
`wM(pM(ptsX), pM(ptsS))` of the two one-point magnetisations; since `pM(ptsX)_{j_x} = M_{a,j_x}`
(`hBeta_eq_zV0`), the conversion needs only

**`PairUnitSeed c_u`** (named input): `pM(ptsS)_{j_x} = 2s_{j_x}²|β^{mir}_{a,j_x}| ≤
c_u‖M_{j_x}‖ǧ_{j_x}` for every `x` (one inequality at one scale; expected from
`|β| ≍ bθ`, `s² ≍ ℓ²/|Z|`, `M ≍ ϑ`, not available from the exported spin facts).

* **`pairVStep_MF`**: under `MasterFacts`, with `C₁w` of the `V`-step requirement `abwEReqV`:
  for every admissible trajectory, `PairUnitSeed c_u`, `c_r ≤ m̄` and the seed condition
  `8c_u(2ι_WA)^{(L+18)²} ≤ vck(C₁w)(4C₁w + 1)m̄`: `PairVB j_x` holds and
  `PairVB n ∧ PairMassUpTo n ⇒ PairVB (n + 1)` for `j_x ≤ n ≤ N_h` — the `V`-part of
  `PairJointSizes` (`VB := PairVB … m̄`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The weight `M_{a,j} = 2s_j²|β_{a,j}|` (`1` where `β_{a,j} = 0`). -/
def vwA (m b μ₀ : ℝ) (x : Lam 2 L N) (j : ℕ) : ℝ :=
  if hBeta R m b μ₀ x j = 0 then 1 else
    2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ‖hBeta R m b μ₀ x j‖

/-- The weight `M_b = ‖M_{j_x}‖ǧ_{j_x}` (constant in the scale). -/
def vwB (m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) : ℝ :=
  ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- **Named input: the unit relation at the seed** — the mirrored one-point weight at coalescence
is bounded by `c_u‖M_{j_x}‖ǧ_{j_x}`. -/
def PairUnitSeed (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (cu : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
        (Obs.coal L (0 : Lam 2 L N) x) ≤ cu * vwB R m b μ₀ lam x

/-- **The `V`-predicate of the joint induction**: `‖V'_j(B)‖_{wM(M_{a,j}, M_b)} ≤ m̄` for
`j_x ≤ j < n`. -/
def PairVB (m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (mbar : ℝ) (n : ℕ) : Prop :=
  ∀ j, Obs.coal L (0 : Lam 2 L N) x ≤ j → j < n → ∀ c ∈ blockIdx (L := L) (N := N) j,
    oTo (wM (vwA R m b μ₀ x j) (vwB R m b μ₀ lam x)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
          (oRed R m b μ₀ (dxStd (L := L) (N := N)) x) j
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c) ≤ ENNReal.ofReal mbar

theorem pairVB_start (m b μ₀ : ℝ) (lam : ℕ → ℂ) (x : Lam 2 L N) (mbar : ℝ) :
    PairVB R m b μ₀ lam x mbar (Obs.coal L (0 : Lam 2 L N) x) :=
  fun j hj hjn => absurd hj (by omega)

/-- `β_{a,j}` of `zV b` is that of `zV0 b` from scale `1` on. -/
theorem hBeta_eq_zV0 (m b μ₀ : ℝ) (x : Lam 2 L N) {j : ℕ} (hj : 1 ≤ j) :
    hBeta R m b μ₀ x j = Obs2.betaTot2 (L := L) (N := N) j
      (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV0 b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j) := by
  unfold hBeta Obs2.histVO2 Obs2.fullV
  rw [(obsHist_zV0 (R.withMsq m) (ptsX x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) b
    (traj_zero_X R m b μ₀) j hj).1]

end Traj

set_option maxHeartbeats 4000000 in
/-- **The `V`-step of the joint induction under `MasterFacts`.** -/
theorem pairVStep_MFD {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁w : ℝ, 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar → cr ≤ mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁w * ((4 * C₁w + 1) * mbar) →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      PairVB R m b μ₀ lam x mbar (Obs.coal L (0 : Lam 2 L N) x) ∧
      ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → PairVB R m b μ₀ lam x mbar n →
        PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ (dxStd (L := L) (N := N))) cr x n →
        PairVB R m b μ₀ lam x mbar (n + 1) := by
  obtain ⟨C₁w, hC₁w, hVS⟩ := M.core.vstepD
  refine ⟨C₁w, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam cu cr mbar hU hmbar hcr h8 x hx
    h1 hj
  refine ⟨pairVB_start R m b μ₀ lam x mbar, ?_⟩
  intro n hjn hn hVB hMs
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hβr := pairBetaRatio_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD x
  -- `β_{a,k} ≠ 0`
  have hβne : ∀ k ≤ Nh, hBeta R m b μ₀ x k ≠ 0 ∧ hBeta R m b μ₀ x (k + 1) ≠ 0 := by
    obtain ⟨q, -, -, hl⟩ :=
      (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b)).2.2
    intro k hk
    obtain ⟨a1, a2, -, -⟩ := hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hl k hk).1)
      (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)).1 k hk
    exact ⟨a1, a2⟩
  have hρ0 : 0 ≤ (R.withMsq m).ρ := (hV 0 (by omega) |>.toValidCore).2.2.2.1
  -- the value of the weights
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := ((hRI 0 (by omega)).1).2.2.2.2.1
  have hs : ∀ k, 0 < histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := fun k => histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  have hvwA : ∀ k ≤ Nh + 1, vwA R m b μ₀ x k = 2 * histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ‖hBeta R m b μ₀ x k‖ := by
    intro k hk
    have hne : hBeta R m b μ₀ x k ≠ 0 := by
      rcases Nat.lt_or_ge k (Nh + 1) with h | h
      · exact (hβne k (by omega)).1
      · obtain rfl : k = Nh + 1 := by omega
        exact (hβne Nh le_rfl).2
    unfold vwA; rw [if_neg hne]
  have hMa : ∀ k, 0 < vwA R m b μ₀ x k := fun k => by
    unfold vwA
    split_ifs with h
    · norm_num
    · have := hs k; have := norm_pos_iff.2 h; positivity
  -- the seed
  obtain ⟨hpa, hpb, hK⟩ := pairSeed_hK0D M.pairInitWD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD x h1 hj
  have hU' := hU x hx h1 hj
  have hg0 : 0 ≤ ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 := (hD j hj).1.le
  have hwB0 : 0 ≤ vwB R m b μ₀ lam x := mul_nonneg (norm_nonneg _) hg0
  have hwB : 0 < vwB R m b μ₀ lam x := by
    rcases hwB0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hU'; linarith
  have hcu : 0 < cu := by
    by_contra hc
    push Not at hc
    have : cu * vwB R m b μ₀ lam x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hwB0
    linarith
  have hpaE : pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j = vwA R m b μ₀ x j := by
    rw [hvwA j (by omega), hBeta_eq_zV0 R m b μ₀ x h1]; rfl
  set k₀ := cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) with hk₀d
  have hιA : 0 ≤ (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2) := by
    have := M.ιW_ge; have := M.core.hA2; positivity
  have hk₀ : 0 ≤ k₀ := mul_nonneg hcu.le hιA
  have hK0 : ∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      oTo (wM (vwA R m b μ₀ x j) (vwB R m b μ₀ lam x)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X) ≤ ENNReal.ofReal k₀ := by
    intro X hX
    have hab : (oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X ∈
        (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) :=
      (PtCorr2.obsAbInv_redSt _ _ _ _ _ _ _ _ _ _).K X hX
    rw [oTo_wM_rescale (hMa j) hwB hpa hpb j _ hab, hpaE, mul_left_comm]
    have hr : vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
        (vwA R m b μ₀ x j * vwB R m b μ₀ lam x) ≤ cu := by
      rw [mul_div_mul_left _ _ (hMa j).ne', div_le_iff₀ hwB]; linarith
    calc ENNReal.ofReal (vwA R m b μ₀ x j * pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j /
          (vwA R m b μ₀ x j * vwB R m b μ₀ lam x)) *
          (ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
            oTo (wM (vwA R m b μ₀ x j) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X))
        ≤ ENNReal.ofReal cu * ENNReal.ofReal ((2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) := by
          gcongr
          rw [← hpaE]; exact hK X hX
      _ = ENNReal.ofReal k₀ := by rw [← ENNReal.ofReal_mul hcu.le]
  -- the path from `0` to `x`
  obtain ⟨w, hwx, hwl⟩ := PtCorr2.exists_path_sum (n := L ^ N) (x : Lam 2 L N)
  have hpe : Obs2.pathEnd (ptsX x).a w = (ptsX x).b := by
    show Obs2.pathEnd (0 : Lam 2 L N) w = x
    rw [Obs2.pathEnd, zero_add, hwx]
  have hsn : supNorm ((ptsX x).a - (ptsX x).b) = supNorm x := by
    show supNorm ((0 : Lam 2 L N) - x) = supNorm x
    rw [zero_sub, supNorm_neg]
  have hwl' : (w.length : ℝ) ≤ 2 * ((supNorm ((ptsX x).a - (ptsX x).b) : ℕ) : ℝ) := by
    rw [hsn]; exact_mod_cast hwl
  have hsL : 2 * ((supNorm ((ptsX x).a - (ptsX x).b) : ℕ) : ℝ) ≤ (L : ℝ) ^ (j + 1) := by
    have h2 := two_supNorm_lt_coal (by have := M.core.hL49; omega : 2 ≤ L) x
    rw [sub_zero] at h2
    rw [hsn]; exact_mod_cast h2.le
  have hab : (ptsX x).a ≠ (ptsX x).b := fun h => hx (h.symm)
  -- the initial state
  have hRd := pairSectRed_of R m hV hVL b μ₀ (pairDCov_std (L := L) (N := N) Nh)
  obtain ⟨hobs, hloc0, -, -⟩ := hRd x hx h1 hj
  have hanc := pairAnchR_oRed R Nh m b μ₀ x hx h1 hj
  have hsymj : PtCorr2.ObsSymInv j (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsSymInv_redSt (hRI j hj).1 (hRI j hj).2 (rawD_mem (R.withMsq m) _ _)
      (rawK_mem (R.withMsq m) _ _)
      (PtCorr2.obsSymInv_hist (R.withMsq m) (ptsX x) _ (PtCorr2.obsSymInv_init .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j fun i hi => (hRI i (by omega)))
  have hVab : PtCorr2.ObsVabInv (ptsX x) (oRed R m b μ₀ dxStd x) :=
    PtCorr2.obsVabInv_redSt (R.withMsq m) (ptsX x)
  -- the doubling of the weights
  have hdbl : ∀ k, j ≤ k → k < n → vwA R m b μ₀ x k ≤ 2 * vwA R m b μ₀ x (k + 1) := by
    intro k hk hkn
    rw [hvwA k (by omega), hvwA (k + 1) (by omega)]
    have h1' := histS_sq_ratio (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
    have h2' := hβr k (by omega)
    have h3 := sq_nonneg (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    have h4 := norm_nonneg (hBeta R m b μ₀ x (k + 1))
    have h5 : histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ‖hBeta R m b μ₀ x k‖ ≤
        (6 / 5 * histS (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2) * (64 / 49 * ‖hBeta R m b μ₀ x (k + 1)‖) :=
      mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg (histS (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) h4]
  -- the mass at scale `n`
  have hρ : ∀ c ∈ blockIdx (L := L) (N := N) n,
      ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c :
        SA .two (Lam 2 L N)).ab‖ ≤
        cr * ‖Mmag R m b μ₀ lam j‖ * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 * ‖hBeta R m b μ₀ x n‖ := by
    intro c hc
    have hne : (blockSet (L := L) (N := N) n c).Nonempty := by
      obtain ⟨y, -, hy⟩ := mem_image.1 hc
      exact ⟨y, mem_blockSet.2 hy⟩
    have h := hMs n hjn le_rfl (blockSet (L := L) (N := N) n c) (isPolymer_blockSet n c) n hjn le_rfl
    have e : hRRX R m b μ₀ (oRed R m b μ₀ dxStd) x (blockSet (L := L) (N := N) n c) n =
        LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) j (oRed R m b μ₀ dxStd x) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V c :
          SA .two (Lam 2 L N)).ab := by
      unfold hRRX
      rw [rRX_blockSet n c hne, hVR_ab]
    rw [← e]; exact h
  have hρm : (vwA R m b μ₀ x n * vwB R m b μ₀ lam x)⁻¹ *
      (cr * ‖Mmag R m b μ₀ lam j‖ * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 * ‖hBeta R m b μ₀ x n‖ *
        (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) * histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) ≤ mbar / 2 := by
    rw [hvwA n (by omega)]
    have hβn : 0 < ‖hBeta R m b μ₀ x n‖ := norm_pos_iff.2 (hβne n hn).1
    have hsn' := hs n
    have e : (2 * histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ‖hBeta R m b μ₀ x n‖ * vwB R m b μ₀ lam x)⁻¹ *
        (cr * ‖Mmag R m b μ₀ lam j‖ * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 * ‖hBeta R m b μ₀ x n‖ *
          (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) * histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))) = cr / 2 := by
      unfold vwB
      unfold vwB at hwB
      rw [← hjd] at hwB ⊢
      have hM0 : ‖Mmag R m b μ₀ lam j‖ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hwB; exact lt_irrefl _ hwB
      have hg0' : ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j).1 ≠ 0 := fun h0 => by
        rw [h0, mul_zero] at hwB; exact lt_irrefl _ hwB
      field_simp
    rw [e]; linarith
  -- the step
  intro k hk hkn
  rcases Nat.lt_or_ge k n with hkn' | hkn'
  · exact hVB k hk hkn'
  · obtain rfl : k = n := by omega
    exact hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) hab w hpe hwl'
      (vwA R m b μ₀ x) (vwB R m b μ₀ lam x) hMa hwB j (oRed R m b μ₀ dxStd x) hobs hloc0 hsymj
      hanc hVab (oRed_V_ab_zero R m b μ₀ dxStd x) hsL k hjn hn hdbl mbar hmbar hVB
      (fun b' _ => by
        show oTo _ _ _ (0 : OE .two (Lam 2 L N)) ≤ _
        rw [oTo_zero']; exact bot_le)
      k₀ hk₀ hK0 h8 _ hρ hρm


/-- **The `V`-step of the joint induction under `MasterFacts`.** -/
theorem pairVStep_MF {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁w : ℝ, 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 < mbar → cr ≤ mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁w * ((4 * C₁w + 1) * mbar) →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      PairVB R m b μ₀ lam x mbar (Obs.coal L (0 : Lam 2 L N) x) ∧
      ∀ n, Obs.coal L (0 : Lam 2 L N) x ≤ n → n ≤ Nh → PairVB R m b μ₀ lam x mbar n →
        PairMassUpTo R m b μ₀ lam (oRed R m b μ₀ (dxStd (L := L) (N := N))) cr x n →
        PairVB R m b μ₀ lam x mbar (n + 1) := by
  obtain ⟨C₁w, hC₁w, h⟩ := pairVStep_MFD M
  refine ⟨C₁w, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

end

end Spin2
