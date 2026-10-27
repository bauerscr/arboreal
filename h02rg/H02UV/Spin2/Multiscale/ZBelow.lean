import Spin2.Multiscale.TwoPtSq
import Spin2.Case2.Case2
import Spin2.Multiscale.BetaThm
import Obs2.Flow.GamChain2

/-!
# `ZBelowU`: the Case-(2) `γ` flow below coalescence

**Defect of `ZBelowU` at `j_x = 0`** (`uA_zero`, `zBelowU_coal_zero`). `γ_{0,0} = uA 0 = 0`
(`obsInit` has `u = 0`) while `M_0 = 1`, so `ZBelowU` at a point with `j_x = 0` (e.g. `x = e_1`:
`j_x = ⌊log_L 2⌋ = 0` for `L > 2`) forces `1 ≤ K_M b`: `ZBelowU` (and `PairAboveW`, for the same
reason `E ≈ -1`) cannot hold with a uniform `K_M`. At `j_x = 0`, `Π^{<0} = 1` and the whole
two-point function sits in `Π^{≥0}`. Corrected split (`twoPtSq_of_zz1`, `twoPtSq_of_zz1_flow`):
`ZBelowU1`, `PairAboveW1` (only `1 ≤ j_x ≤ N_h`) and `TwoPtNear` (the `j_x = 0` case of
`TwoPtSq`, `|b⟨ψ̄_0ψ_x⟩ - 1| ≤ K_N b + K_{RN} r`) give `TwoPtSq`.

**The `γ` flow** (`Obs2.gamA_succ` along the pair history from `obsInit .two (zV b) (ptsX x)`,
`uA_succ`): `γ_{k+1} = γ_k - ∑_Bε(V_k(B)_0) - β_kΓ^{int}_{k+1}(0,0) + ρ_k`, with
`β_k = bt2 = -μ_{0,k}` (`β_0 = b`), `ε`-part `-1` at `k = 0` and `0` afterwards, and the
explicit remainder `ρ_k = gamRemX` (activity and second order). The covariance is the dressed
`Γ^{int}_{k+1}` (`histCov_gamInt`). Hence (`uA_eq_mmag`), for `j ≥ 1`, `γ_{0,j} = M_j(λ^γ)` with
`λ^γ_k = β_k/b - ρ_k/(bΓ^{int}_{k+1}(0,0))`: the second-order terms are exactly those of `e:PM`
up to the relative corrections `ρ_k`.

**Reduction to `MagConcl`** (`zBelowU1_of_forms`): if `λ` satisfies (H_λ), `γ_{0,j} = M_j(λ^a)`,
`γ_{x,j} = M_j(λ^b)` with `λ^a, λ^b` close to `(ǧ_k/b)^{1/3}` (relative `O(ǧ_k + a_k)`) below
`j_x`, then both `γ`'s and `M_j(λ)` are `ϑ_j(1 + O(ǧ_j))` by `MagConcl`, so `ZBelowU1` holds with
`K_M = 2(K(λ^γ) + K(λ))` (smallness `K(λ)ǧ_j ≤ 1/2`). No identification of the pair `λ^a` with
the one-point `λ̂` (nor with the given `λ`) is needed: both are compared with `ϑ_j`.
For the `0`-part, `λ^a` is controlled (`gamFormA_of`) by (H_λ) for the pair's `lamHat2` (from
`Case2Rel`, `Case2Loop` of the pair history via `hLam_case2`) and the named relative remainder bound
**`GamRemRel`**: `‖ρ_k‖ ≤ c_γ(ǧ_k/b)^{1/3}(ǧ_k + a_k)·b‖Γ^{int}_{k+1}(0,0)‖`.
The `x`-part is the named input **`GamFormB`** (the mirror image; the `σ_b` analogues of
`MuChain2`/`Case2` are not formalised).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-! ### The defect at `j_x = 0` -/

theorem uA_zero (m b μ₀ : ℝ) (x : Lam 2 L N) : uA R m b μ₀ x 0 = 0 :=
  Obs2.gamA_obsInit_zero (R.withMsq m) (ptsX x) _ (zV b)

theorem Mmag_zero (m b μ₀ : ℝ) (lam : ℕ → ℂ) : Mmag R m b μ₀ lam 0 = 1 := by
  simp [Mmag]

/-- **`ZBelowU` is unsatisfiable at `j_x = 0`** with `K_M < 1/b`. -/
theorem zBelowU_coal_zero {Nh : ℕ} {m b μ₀ : ℝ} {lam : ℕ → ℂ} {KM : ℝ}
    (h : ZBelowU R Nh m b μ₀ lam KM) {x : Lam 2 L N} (hx : x ≠ 0)
    (h0 : Obs.coal L (0 : Lam 2 L N) x = 0) : 1 ≤ KM * b := by
  have := (h x hx (by rw [h0]; exact Nat.zero_le _)).1
  rw [h0, uA_zero, Mmag_zero, Hist.traj_zero] at this
  simpa using this

/-! ### The corrected split -/

/-- `ZBelowU` for `1 ≤ j_x ≤ N_h`. -/
def ZBelowU1 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KM : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) -
        Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      KM * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
    ‖uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) -
        Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      KM * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

/-- `PairAboveW` for `1 ≤ j_x ≤ N_h`. -/
def PairAboveW1 (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KE KR : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖PtCorr2.sAB (zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x)) /
        PtCorr2.sE (zOm R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x))‖ ≤
      KE * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 +
        KR * ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖

/-- **Named input: the two-point function at `j_x = 0`** (`|x|_∞ < L/2`, `M_0 = 1`, `ǧ_0 = b`). -/
def TwoPtNear (m b μ₀ : ℝ) (KN KRN : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x = 0 →
    ‖(b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) - 1‖ ≤
      KN * b + KRN * ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from `ZBelowU1`, `PairAboveW1`, `TwoPtNear`** (trajectory level). -/
theorem twoPtSq_of_zz1 {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh : b ≤ μ₀ + m) (lam : ℕ → ℂ) {KM Mb KE KR KN KRN : ℝ} (hKM : 0 ≤ KM)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hMb : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb)
    (hZ : ZBelowU1 R Nh m b μ₀ lam KM) (hE : PairAboveW1 R Nh m b μ₀ lam KE KR)
    (hNear : TwoPtNear (L := L) (N := N) m b μ₀ KN KRN) :
    TwoPtSq R Nh m b μ₀ lam (max (KM * (2 + KM) + KE) KN)
      (max (1 + 2 * (1 + KM) * Mb + KR) KRN) := by
  intro x hx hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hr0 : 0 ≤ ‖1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0)‖ := norm_nonneg _
  have hMg : 0 ≤ ‖Mmag R m b μ₀ lam j‖ ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 :=
    mul_nonneg (sq_nonneg _) (hg j hj).1
  rcases Nat.eq_zero_or_pos j with h0 | h1
  · -- `j_x = 0`
    have hn := hNear x hx h0
    rw [h0, Mmag_zero, Hist.traj_zero, norm_one]
    simp only [one_pow, mul_one]
    refine hn.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) hb.le)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr0))
  · obtain ⟨p, r, hp0, hpr, -, hr, hP⟩ :=
      twopt_zz_eq R hN m hρ1 hspl hm0 hm hV hVL hL hb hh x hj
    obtain ⟨hX0, -⟩ := PtCorr2.zz_square_split (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm
      hV hVL hL hj hb hh (zV b) (zV_abFree b)
    obtain ⟨ea, eb⟩ := PtCorr2.prodLo_sA_sB (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) rfl (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j
    have hX0' : PtCorr2.sE (zLo R m b μ₀ x) ≠ 0 := hX0
    have ha : PtCorr2.sA (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) = uA R m b μ₀ x j := by
      have ea' : PtCorr2.sA (zLo R m b μ₀ x) = PtCorr2.sE (zLo R m b μ₀ x) * uA R m b μ₀ x j := ea
      rw [ea', mul_div_cancel_left₀ _ hX0']
    have hb' : PtCorr2.sB (zLo R m b μ₀ x) / PtCorr2.sE (zLo R m b μ₀ x) = uB R m b μ₀ x j := by
      have eb' : PtCorr2.sB (zLo R m b μ₀ x) = PtCorr2.sE (zLo R m b μ₀ x) * uB R m b μ₀ x j := eb
      rw [eb', mul_div_cancel_left₀ _ hX0']
    have hw := PtCorr2.hist_omegaO_from (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) hN hρ1 hspl hm0 hm hV hVL b μ₀
      (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) hj
    have e : zHi R Nh m b μ₀ x = zOm R m b μ₀ x j := hw.symm
    obtain ⟨hA, hB⟩ := hZ x hx h1 hj
    have hE' := hE x hx h1 hj
    rw [← e, hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0.trans hpr)] at hE'
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0.trans hpr)] at hr0 ⊢
    rw [hP, ha, hb']
    rw [ha, hb'] at hP
    have key := twoPt_sq_pure (hg _ hj).1 (hg _ hj).2 hKM (hp0.trans hpr) hp0 hpr hA hB
      (hMb _ hj) hE'
    refine key.trans ?_
    have e2 : ∀ K : ℝ, K * ‖Mmag R m b μ₀ lam j‖ ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1
        = K * (‖Mmag R m b μ₀ lam j‖ ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) :=
      fun K => by ring
    rw [e2, e2]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hMg)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0)

end Traj

/-- **`TwoPtSq` along the admissible trajectories** from `ZBelowU1`, `PairAboveW1`, `TwoPtNear`. -/
theorem twoPtSq_of_zz1_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (KM Mb KE KR KN KRN : ℝ), 0 ≤ KM →
      (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
      ZBelowU1 R Nh m b μ₀ lam KM → PairAboveW1 R Nh m b μ₀ lam KE KR →
      TwoPtNear (L := L) (N := N) m b μ₀ KN KRN →
      TwoPtSq R Nh m b μ₀ lam (max (KM * (2 + KM) + KE) KN)
        (max (1 + 2 * (1 + KM) * Mb + KR) KRN) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam KM Mb KE KR KN KRN hKM hMb
    hZ hE hNear
  obtain ⟨-, -, hρ0, -, -, -, -, -, -, -, -, -, -, hρ8, hspl, hrest⟩ := hF
  have hval := (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1.le, ((hadm.1 k hk).2.1).trans hε1⟩
  exact twoPtSq_of_zz1 R hNh m (by rw [hRρ]; linarith) (by rw [hP, hRρ]; exact hspl)
    hm.1 hm.2 hval.1 hval.2 hL hb hh lam hKM hg hMb hZ hE hNear

end

end Spin2
