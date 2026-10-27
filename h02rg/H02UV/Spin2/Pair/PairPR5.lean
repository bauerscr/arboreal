import Spin2.Pair.PairSect

/-!
# PR5 (part): `PairVertSum` discharged along the admissible trajectories

The absolute vertex sum above coalescence,
`∑_{j≤k≤N_h}‖C_k(0,0)‖‖β_{a,k}‖ + ‖C_N(0,0)‖‖β_{a,N_h+1}‖ ≤ c_s‖M_j‖`, follows from three facts
that are available under the master construction:

* the covariance sizes `‖C_k(0,0)‖ ≤ (ℓ²/16)|Z_{k+1}|^{-1} ≤ (ℓ²e^{K_Z}/14)θ_k` (`GoodCov2` of the
  step covariance, `norm_gamT_le_k`; the `log|Z|` band of `SpinConcl`);
* the vertex sizes `‖β_{a,k}‖ ≤ (1 + 3K_p)bθ_k` for `k < N_h` ((H_λ) for the pair vertex,
  `norm_bt2_le_hLam`) and `≤ K_βbθ_{N_h}` at `N_h`, `N_h + 1` (`BetaLast`);
* the Riemann sum `∑_{j≤k<N_h} bθ_k² ≤ (6/β)(1 + K_S)ϑ_j` (**`sum_bthSq_le`**): `SpinSum` of
  `SpinConcl` applied to the exact sequence `T_k = (β/3)bθ_k²` gives
  `1 - ∑_{k<i}T_k = ϑ_i(1 + O(ǧ_i))` at `i = j` and `i = N_h`; subtract. No rpow calculus.

With `bθ_k² = ϑ_kǧ_k`, `ϑ_{N_h} ≤ ϑ_j` and `ϑ_j ≤ 2‖M_j‖` (`MagConcl` and the smallness
`K(K_λ)ǧ_j ≤ 1/2`): **`pairVertSum_of`**,
`c_s = 2·(ℓ²e^{K_Z}/14)·max(1 + 3K_p, K_β)·((6/β)(1 + max(K_S, 0)) + 2)`.

**`thm_pairAbove_red'`**: `thm_pairAbove_red` without the `PairVertSum` hypothesis.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- Product of two sizes. -/
theorem norm_mul_thsq_le {c β : ℂ} {A B b θ : ℝ} (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hc : ‖c‖ ≤ A * θ) (hβ : ‖β‖ ≤ B * b * θ) :
    ‖c‖ * ‖β‖ ≤ A * B * (b * θ ^ 2) := by
  have := mul_le_mul hc hβ (norm_nonneg _) (mul_nonneg hA hθ)
  calc ‖c‖ * ‖β‖ ≤ A * θ * (B * b * θ) := this
    _ = A * B * (b * θ ^ 2) := by ring

/-- `ϑ ≤ 2‖M‖` from `‖M - ϑ‖ ≤ Fϑǧ`, `Fǧ ≤ 1/2`. -/
theorem varth_le_two_norm {M : ℂ} {v F g : ℝ} (hv : 0 ≤ v) (hg : 0 ≤ g)
    (hM : ‖M - (v : ℂ)‖ ≤ F * v * g) (hsm : max F 0 * g ≤ 1 / 2) : v ≤ 2 * ‖M‖ := by
  have hvn : ‖(v : ℂ)‖ = v := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  have t := norm_le_norm_add_norm_sub' (v : ℂ) M
  rw [hvn, norm_sub_rev] at t
  have h1 : F * v * g ≤ max F 0 * g * v := by
    have : F * g ≤ max F 0 * g := mul_le_mul_of_nonneg_right (le_max_left _ _) hg
    nlinarith
  have h2 : max F 0 * g * v ≤ 1 / 2 * v := mul_le_mul_of_nonneg_right hsm hv
  linarith

/-- The `SpinSum` conclusion at one trajectory `(b, μ₀)` (no domain hypothesis). -/
def SpinSumAt {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] (F : HData X) (Λ β cg : ℝ) (N : ℕ)
    (eR b μ₀ : ℝ) : Prop :=
  ∀ (T : ℕ → ℂ) (a : ℕ → ℝ) (B aS : ℝ), 0 ≤ B →
    (∀ k, 0 ≤ a k) → ∑ k ∈ range N, a k ≤ aS →
    (∀ k < N, ‖T k - ((β / 3 * b * (((traj F Λ b μ₀ k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 : ℝ) : ℂ)‖ ≤
      B * b * (((traj F Λ b μ₀ k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 * ((traj F Λ b μ₀ k).1 + a k)) →
    ∀ j ≤ N, ‖(1 - ∑ k ∈ range j, T k) - (((b / (traj F Λ b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinTrajK β cg B eR aS * (b / (traj F Λ b μ₀ j).1) ^ (1 / 3 : ℝ) * (traj F Λ b μ₀ j).1

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `‖Γ_k‖ ≤ ℓ²/(16|Z_{k+1}|)` for `k ≤ N_h` (`GoodCov2` of the step covariance). -/
theorem norm_gamT_le_k (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh) {k : ℕ}
    (hk : k ≤ Nh) :
    ‖gamT R m b μ₀ k‖ ≤ R.ℓ ^ 2 / 16 *
      ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖⁻¹ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  have H := rawInv_histU (R.withMsq m) hV hVL t k (by omega)
  have hVC : ValidCore (R.withMsq m) k := by
    rcases Nat.lt_or_ge k Nh with h | h
    · exact (hV k h).toValidCore
    · obtain rfl : k = Nh := le_antisymm hk h
      exact hVL.2
  have hC := (RawInv.covL hVC H).1
  have e : gamT R m b μ₀ k = rawCov (R.withMsq m) k
      (RawInv.zeta' (R.withMsq m) k (rawHist (R.withMsq m) k t)) 0 0 := by
    unfold gamT; rw [← histCov_gamInt R hP]; rfl
  rw [e]
  refine (Obs2.good_entry hC 0 0).trans (le_of_eq ?_)
  rw [fscale_sq]
  rfl

/-- **The pair vertex below `N_h`** from (H_λ): `‖β_k‖ ≤ (1 + 3K_p)bθ_k`. -/
theorem norm_bt2_le_hLam {P : Obs2.ObsPts 2 L N} {Nh : ℕ} {m b μ₀ Kp : ℝ} (hb : 0 < b)
    (hKp : 0 ≤ Kp) (hl : HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp) {k : ℕ} (hk : k < Nh)
    (hg : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hga3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k ≤ 3) :
    ‖bt2 R P (zV b) m b μ₀ k‖ ≤ (1 + 3 * Kp) * b * thJ R m b μ₀ k := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  have hθk : 0 ≤ thJ R m b μ₀ k := Real.rpow_nonneg (div_nonneg hg hb.le) _
  have hlk := hl k hk
  have hlh : lamHat2 R P (zV b) m b μ₀ k = bt2 R P (zV b) m b μ₀ k / b := by
    unfold lamHat2; rw [bt2_zV_zero]
  rw [hlh] at hlk
  have hβb : ‖bt2 R P (zV b) m b μ₀ k‖ = b * ‖bt2 R P (zV b) m b μ₀ k / b‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]; field_simp
  have h2 := norm_le_insert' (bt2 R P (zV b) m b μ₀ k / b) ((thJ R m b μ₀ k : ℝ) : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθk] at h2
  have hlk' : ‖bt2 R P (zV b) m b μ₀ k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
      Kp * thJ R m b μ₀ k * ((t k).1 + zA L m k) := hlk
  have h3 : Kp * thJ R m b μ₀ k * ((t k).1 + zA L m k) ≤ Kp * thJ R m b μ₀ k * 3 :=
    mul_le_mul_of_nonneg_left hga3 (mul_nonneg hKp hθk)
  have h4 : ‖bt2 R P (zV b) m b μ₀ k / b‖ ≤ (1 + 3 * Kp) * thJ R m b μ₀ k := by linarith
  rw [hβb]
  have := mul_le_mul_of_nonneg_left h4 hb.le
  linarith

/-- **The Riemann sum above coalescence**: `∑_{j≤k<N_h} bθ_k² ≤ (6/β)(1 + max(K_S,0))ϑ_j`, from
`SpinSum` applied to the exact sequence `T_k = (β/3)bθ_k²`. -/
theorem sum_bthSq_leD {Nh : ℕ} {m b μ₀ κ cg cm cT ε eR : ℝ}
    (hSS : SpinSumAt (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) cg Nh eR b μ₀)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) (hβ : 0 < betaL L)
    (hb : 0 < b)
    (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    {j : ℕ} (hj : j ≤ Nh)
    (hjN : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) :
    ∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2 ≤
      6 / betaL L * (1 + max (spinTrajK (betaL L) cg 0 eR 0) 0) * varthJ R m b μ₀ j := by
  set K := spinTrajK (betaL L) cg 0 eR 0
  set K' := max K 0 with hK'd
  have hK' : 0 ≤ K' := le_max_right _ _
  set β := betaL L
  set s : ℕ → ℝ := fun i => 1 - ∑ k ∈ range i, β / 3 * b * thJ R m b μ₀ k ^ 2 with hsd
  have key := hSS (fun k => ((β / 3 * b * thJ R m b μ₀ k ^ 2 : ℝ) : ℂ)) (fun _ => 0)
    0 0 le_rfl (fun _ => le_rfl) (by simp) (fun k _ => by unfold thJ; simp)
  have hS : ∀ i ≤ Nh, |s i| ≤ (1 + K') * varthJ R m b μ₀ i := by
    intro i hi
    have h := key i hi
    have e : (1 - ∑ k ∈ range i, ((β / 3 * b * thJ R m b μ₀ k ^ 2 : ℝ) : ℂ)) -
        (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ) =
        ((s i - varthJ R m b μ₀ i : ℝ) : ℂ) := by
      simp only [hsd, varthJ]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at h
    have hv : 0 ≤ varthJ R m b μ₀ i := Real.rpow_nonneg (div_pos hb (hg i hi).1).le _
    have h1 : K * varthJ R m b μ₀ i * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
        K' * varthJ R m b μ₀ i := by
      have := mul_le_mul_of_nonneg_right (le_max_left K 0) hv
      have h2 : K' * varthJ R m b μ₀ i * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
          K' * varthJ R m b μ₀ i :=
        mul_le_of_le_one_right (mul_nonneg hK' hv) (hg i hi).2
      have h3 := mul_le_mul_of_nonneg_right this (hg i hi).1.le
      linarith
    have h' : |s i - varthJ R m b μ₀ i| ≤
        K * varthJ R m b μ₀ i * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 := h
    have h4 := abs_sub_abs_le_abs_sub (s i) (varthJ R m b μ₀ i)
    rw [abs_of_nonneg hv] at h4
    linarith
  have hvv := varthJ_anti R hb.le (hg j hj).1 hjN
  have hsum : β / 3 * ∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2 = s j - s Nh := by
    rw [mul_sum, sum_Ico_eq_sub _ hj]
    simp only [hsd]
    rw [show ∑ k ∈ range Nh, β / 3 * (b * thJ R m b μ₀ k ^ 2) =
        ∑ k ∈ range Nh, β / 3 * b * thJ R m b μ₀ k ^ 2 from
          sum_congr rfl fun _ _ => by ring,
      show ∑ k ∈ range j, β / 3 * (b * thJ R m b μ₀ k ^ 2) =
        ∑ k ∈ range j, β / 3 * b * thJ R m b μ₀ k ^ 2 from
          sum_congr rfl fun _ _ => by ring]
    ring
  have hb3 : β / 3 * ∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2 ≤
      2 * (1 + K') * varthJ R m b μ₀ j := by
    rw [hsum]
    have h1 := hS j hj
    have h2 := hS Nh le_rfl
    have h3 : s j - s Nh ≤ |s j| + |s Nh| := by
      have := le_abs_self (s j); have := neg_abs_le (s Nh); linarith
    have h4 := mul_le_mul_of_nonneg_left hvv (by linarith : (0 : ℝ) ≤ 1 + K')
    linarith
  have e1 : ∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2 =
      (β / 3 * ∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2) * (3 / β) := by
    field_simp
  have e2 : 6 / β * (1 + K') * varthJ R m b μ₀ j = (2 * (1 + K') * varthJ R m b μ₀ j) * (3 / β) := by
    field_simp; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hb3 (by positivity)

set_option maxHeartbeats 1000000 in
/-- **`PairVertSum` along one trajectory.** -/
theorem pairVertSum_ofD (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ KZ Kp Kβ κ cg cm cT ε eR : ℝ}
    (hb : 0 < b) (hKZ : 0 ≤ KZ) (hKp : 0 ≤ Kp)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hjN : ∀ j ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hZ : ∀ n ≤ Nh,
        (rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0 ∧
        |Real.log ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
            1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 / b)| ≤
          KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1)
    (hpair : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hβL : BetaLast R Nh m b μ₀ Kβ)
    (hSS : SpinSumAt (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) cg Nh eR b μ₀)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) (hβ : 0 < betaL L)
    {f : ℝ → ℝ} (hMag : MagAt R Nh m b μ₀ f) {lam : ℕ → ℂ} {Kl : ℝ} (hKl : 0 ≤ Kl)
    (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (f Kl) 0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) :
    PairVertSum R Nh m b μ₀ lam
      (2 * (R.ℓ ^ 2 * Real.exp KZ / 14 * max (1 + 3 * Kp) Kβ) *
        (6 / betaL L * (1 + max (spinTrajK (betaL L) cg 0 eR 0) 0) + 2)) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set cC := R.ℓ ^ 2 * Real.exp KZ / 14 with hcCd
  set cB := max (1 + 3 * Kp) Kβ with hcBd
  set K' := max (spinTrajK (betaL L) cg 0 eR 0) 0
  have hcC : 0 ≤ cC := by positivity
  have hcB : 0 ≤ cB := le_trans (by linarith) (le_max_left _ _)
  have hθ : ∀ k ≤ Nh, 0 ≤ thJ R m b μ₀ k := fun k hk =>
    Real.rpow_nonneg (div_pos (hg k hk).1 hb).le _
  -- covariance sizes
  have hZθ : ∀ k ≤ Nh, ‖(rawHist (R.withMsq m) (k + 1) t).Z‖⁻¹ ≤ Real.exp KZ * thJ R m b μ₀ k :=
    fun k hk => inv_normZ_le (norm_pos_iff.2 (hZ k hk).1) (hg k hk).1 (hg k hk).2 hb hKZ (hZ k hk).2
  have hCk : ∀ k ≤ Nh, ‖hC00 R m b μ₀ k‖ ≤ cC * thJ R m b μ₀ k := by
    intro k hk
    have e : hC00 R m b μ₀ k = gamT R m b μ₀ k := histCov_gamInt R hP m t k
    rw [e]
    refine (norm_gamT_le_k R hP hV hVL hk).trans ?_
    have h1 := mul_le_mul_of_nonneg_left (hZθ k hk) (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 / 16)
    have h2 : R.ℓ ^ 2 / 16 * (Real.exp KZ * thJ R m b μ₀ k) ≤ cC * thJ R m b μ₀ k := by
      have := mul_nonneg (mul_nonneg (sq_nonneg R.ℓ) (Real.exp_pos KZ).le) (hθ k hk)
      rw [hcCd]; nlinarith
    exact h1.trans h2
  -- vertex sizes
  obtain ⟨hβN, hβN1⟩ := hβL x hx h1 hj
  have hβk : ∀ k ≤ Nh, ‖hBeta R m b μ₀ x k‖ ≤ cB * b * thJ R m b μ₀ k := by
    intro k hk
    rcases Nat.lt_or_ge k Nh with h | h
    · have := norm_bt2_le_hLam R hb hKp (hpair x hx) h (hg k hk).1.le
        (by linarith [(hg k hk).2, (ha k h).2])
      refine this.trans ?_
      have := mul_nonneg hb.le (hθ k hk)
      have h' : (1 + 3 * Kp) * b * thJ R m b μ₀ k ≤ cB * b * thJ R m b μ₀ k := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
      exact h'
    · obtain rfl : k = Nh := le_antisymm hk h
      have h' : Kβ * b * thJ R m b μ₀ k ≤ cB * b * thJ R m b μ₀ k := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hb.le (hθ k hk))
      exact hβN.trans h'
  -- the per-step terms
  have hterm : ∀ k ≤ Nh, ‖hC00 R m b μ₀ k‖ * ‖hBeta R m b μ₀ x k‖ ≤
      cC * cB * (b * thJ R m b μ₀ k ^ 2) := fun k hk =>
    norm_mul_thsq_le hcC (hθ k hk) (hCk k hk) (hβk k hk)
  -- the last step
  obtain ⟨-, hCN⟩ := gamT_zCovN_le R hP hb hKZ hV hVL hVN (hg Nh le_rfl).1 (hg Nh le_rfl).2
    (hZ Nh le_rfl).1 (hZ Nh le_rfl).2
  have hlast : ‖lC R Nh m b μ₀ 0 0‖ * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ≤
      cC * cB * (b * thJ R m b μ₀ Nh ^ 2) := by
    rw [(rTilN_eq R Nh m b μ₀ x j).2]
    have hβ1 : ‖hBeta R m b μ₀ x (Nh + 1)‖ ≤ cB * b * thJ R m b μ₀ Nh := by
      refine hβN1.trans ?_
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hb.le (hθ Nh le_rfl))
    exact norm_mul_thsq_le hcC (hθ Nh le_rfl) hCN hβ1
  -- `bθ² = ϑǧ ≤ ϑ_j`
  have hvv := varthJ_anti R hb.le (hg j hj).1 (hjN j hj)
  have hNθ : b * thJ R m b μ₀ Nh ^ 2 ≤ varthJ R m b μ₀ j := by
    have e : b * thJ R m b μ₀ Nh ^ 2 = varthJ R m b μ₀ Nh * (t Nh).1 := b_thJ_sq (hg Nh le_rfl).1 hb
    rw [e]
    have hv : 0 ≤ varthJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hb (hg Nh le_rfl).1).le _
    exact (mul_le_of_le_one_right hv (hg Nh le_rfl).2).trans hvv
  have hS := sum_bthSq_leD R hSS hD hβ hb hg hj (hjN j hj)
  -- `ϑ_j ≤ 2‖M_j‖`
  have hvj : 0 ≤ varthJ R m b μ₀ j := Real.rpow_nonneg (div_pos hb (hg j hj).1).le _
  have hM := varth_le_two_norm hvj (hg j hj).1.le (hMag lam Kl hKl hl j hj) (hsmall j hj)
  -- assembly
  have hsplit : ∑ k ∈ Ico j (Nh + 1), ‖hC00 R m b μ₀ k‖ * ‖hBeta R m b μ₀ x k‖ ≤
      cC * cB * (∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2) + cC * cB * (b * thJ R m b μ₀ Nh ^ 2) := by
    rw [sum_Ico_succ_top hj, mul_sum]
    exact add_le_add (sum_le_sum fun k hk => hterm k (mem_Ico.1 hk).2.le) (hterm Nh le_rfl)
  have hcCB : 0 ≤ cC * cB := mul_nonneg hcC hcB
  have hK' : 0 ≤ K' := le_max_right _ _
  have hA : ∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2 + 2 * (b * thJ R m b μ₀ Nh ^ 2) ≤
      (6 / betaL L * (1 + K') + 2) * varthJ R m b μ₀ j := by
    have := hS
    nlinarith
  have hB : (6 / betaL L * (1 + K') + 2) * varthJ R m b μ₀ j ≤
      (6 / betaL L * (1 + K') + 2) * (2 * ‖Mmag R m b μ₀ lam j‖) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have hC := mul_le_mul_of_nonneg_left (hA.trans hB) hcCB
  calc ∑ k ∈ Ico j (Nh + 1), ‖hC00 R m b μ₀ k‖ * ‖hBeta R m b μ₀ x k‖ +
        ‖lC R Nh m b μ₀ 0 0‖ * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖
      ≤ cC * cB * (∑ k ∈ Ico j Nh, b * thJ R m b μ₀ k ^ 2 + 2 * (b * thJ R m b μ₀ Nh ^ 2)) := by
        nlinarith [hsplit, hlast]
    _ ≤ cC * cB * ((6 / betaL L * (1 + K') + 2) * (2 * ‖Mmag R m b μ₀ lam j‖)) := hC
    _ = 2 * (cC * cB) * (6 / betaL L * (1 + K') + 2) * ‖Mmag R m b μ₀ lam j‖ := by ring

/-- Corollary of `pairVertSum_ofD` (`Admissible` ⟹ the domain condition). -/
theorem pairVertSum_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ KZ Kp Kβ κ cg cm cT ε eR : ℝ}
    (hb : 0 < b) (hKZ : 0 ≤ KZ) (hKp : 0 ≤ Kp)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hjN : ∀ j ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hZ : ∀ n ≤ Nh,
        (rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0 ∧
        |Real.log ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
            1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 / b)| ≤
          KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1)
    (hpair : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hβL : BetaLast R Nh m b μ₀ Kβ)
    (hSS : SpinSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε eR)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) (hβ : 0 < betaL L)
    {f : ℝ → ℝ} (hMag : MagAt R Nh m b μ₀ f) {lam : ℕ → ℂ} {Kl : ℝ} (hKl : 0 ≤ Kl)
    (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (f Kl) 0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) :
    PairVertSum R Nh m b μ₀ lam
      (2 * (R.ℓ ^ 2 * Real.exp KZ / 14 * max (1 + 3 * Kp) Kβ) *
        (6 / betaL L * (1 + max (spinTrajK (betaL L) cg 0 eR 0) 0) + 2))  :=
  pairVertSum_ofD R hP hb hKZ hKp hV hVL hVN hg ha hjN hZ hpair hβL (hSS b μ₀ hadm) hadm.1 hβ hMag hKl hl hsmall

end Traj

set_option maxHeartbeats 4000000 in
/-- **`thm_pairAbove_red` without `PairVertSum`** (copy of its body; `PairVertSum` is discharged by
`pairVertSum_of` with `c_s = 2(ℓ²e^{K_Z}/14)·2(1 + 3K_p)·((6/β)(1 + max(K_S, 0)) + 2)`, `K_S` the
`SpinSum` constant). Remaining PR5/PR6 inputs: `PairSrcRelR`, `PairDefSumR`, `PairZeroRelR`. -/
theorem thm_pairAbove_red' : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG ce cw Kp : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧ 0 ≤ KZ ∧
      SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      0 ≤ ce ∧ 0 ≤ cw ∧ 0 ≤ Kp ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl cr : ℝ), 0 ≤ Kl → 0 ≤ cr →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
        Case2TopStep R (ptsX x) (zV b) Nh m b μ₀ ∧ Case2TopStep R (ptsS x) (zV b) Nh m b μ₀) →
      GamLastRem R Nh m b μ₀ cr → GamLastRemS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ (cσ cε cd K2 K3 Mb : ℝ), 0 ≤ cσ → 0 ≤ K3 →
      (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
      PairSrcRelR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cσ cε →
      PairDefSumR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      PairZeroRelR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) K2 K3 →
      PairAboveW1 R Nh m b μ₀ lam
        (cσ * Real.exp cε * (2 * (ℓ ^ 2 * Real.exp KZ / 14 * max (1 + 3 * Kp) (2 * (1 + 3 * Kp))) *
          (6 / betaL L * (1 + max (spinTrajK (betaL L) cg 0 (eRange (betaL L) Ke 1) 0) 0) + 2)) + cd + K2 + K3 * (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 +
            2 * (1 + cr) * (2 * (1 + 3 * Kp)) * (ℓ ^ 2 * Real.exp KZ / 14)))) (K3 * Mb) := by
  obtain ⟨L₀, hL₀⟩ := thm_case2_pairL
  refine ⟨max L₀ 49, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, B₁, B₂, B₃, cq, B', cδ, cw, ce, hF, hε1,
    hSp, hMC, hLoop, hcδ, hRelG, hcw, hWK, hce, hGB, hKZ, hGM, hLV⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL49 : 49 ≤ L := le_trans (le_max_right _ _) hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  set Kp := max (lamRelK (betaL L) cg (B₁ + B₂ + B₃) B' cq cδ (eRange (betaL L) Ke 1) 4) 0
    with hKpd
  have hKp : 0 ≤ Kp := le_max_right _ _
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, ce, cw, Kp, hF, hε1, hKZ, hSp, hMC, hce,
    hcw, hKp, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam Kl cr hKl hcr hl htop hr hrS
    hsmall cσ cε cd K2 K3 Mb hcσ hK3 hMb hSrc hDf hZ
  have hB := hGB N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk.le).1.le, ((hadm.1 k hk.le).2.1).trans hε1⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  -- (H_λ) for the pair vertices
  have hLC := lamConcl_of hL2 hε1 hSp
  have hpairP : ∀ P : Obs2.ObsPts 2 L N,
      HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp := by
    intro P
    obtain ⟨hB0, -, hloop⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    have h := hLam_case2 hLC hP hi0 hRℓ hRA hRρ (by omega) hm hadm hB0 hcδ (zV_mua_ne hb)
      (hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)) hloop
    exact hLam_mono hb hm.1.le (fun k hk => (hadm.1 k hk.le).1) h (le_max_left _ _)
  have hrel : ∀ P : Obs2.ObsPts 2 L N, Case2Rel R P (zV b) Nh m b μ₀ cδ := fun P =>
    hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)
  have hn : ∀ P : Obs2.ObsPts 2 L N, ∀ k < Nh, ‖nn2 R P (zV b) m b μ₀ k‖ ≤ 1 / 8 := by
    intro P k hk
    obtain ⟨-, -, q, -, -, hl'⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    exact (hl' k hk).1
  have hmono := hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, hWT, hWM⟩ := wk_inputs hWK N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβ := betaLast_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).1)
  have hβS := betaLastS_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).2)
  have hRS := gamRemTopS_of R hb hKp hce hcw hval hg ha (fun x _ => hpairP _) hB hWM
  have hcγ : 0 ≤ (ce + cw) * (1 + 3 * Kp) := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hKβ : 0 ≤ 2 * (1 + 3 * Kp) := by linarith
  have hGT := gamTopBd_both_flow hF hε1 hKZ hL8 hSp hMC hGM hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    b μ₀ hadm lam Kl Kp ce cw _ _ cr hKl hKp hce hcw hcγ hKβ hcr hl (fun x _ => hpairP _)
    (fun x _ => hpairP _) (gamBulkRel_of_A R hB) hWT hRS hβ hr hβS hrS hsmall
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hρ8, hspl, hrest⟩ := hF
  have hvalL := ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hg' : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1.le, ((hadm.1 k hk).2.1).trans hε1⟩
  -- `PairVertSum` (new)
  have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
  have hSpN := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hSS := hSpN.2.2.2.1 m hm
  have hZb := hSpN.2.2.2.2.2.2.1 m hm b μ₀ hadm
  have hMag := magAt_of R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hadm
  have hg0 : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1, ((hadm.1 k hk).2.1).trans hε1⟩
  have hjN : ∀ j ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    intro j hj
    have key : ∀ n, j + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (j + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (j + n) (by omega))
    have := key (Nh - j) (by omega)
    rwa [show j + (Nh - j) = Nh by omega] at this
  have hS := pairVertSum_of R hP hb hKZ hKp hval hvalL (hLV N R hP hRℓ hRρ hN2 Nh hNh m hm) hg0 ha
    hjN hZb (fun x _ => hpairP _) hβ hSS hadm hβL hMag hKl hl hsmall
  rw [hRℓ] at hS
  exact pairAboveW1_of_red_parts R hP hNh m (by rw [hRρ]; linarith) (by rw [hP, hRρ]; exact hspl)
    hm.1 hm.2 hval hvalL (hLV N R hP hRℓ hRρ hN2 Nh hNh m hm) hL8 hb hh lam (oRed R m b μ₀ dxStd) hcσ
    hK3 hg' hMb (pairSectRed_of R m hval hvalL b μ₀ (pairDCov_std Nh)) (pairRedSeed_of R Nh m b μ₀ dxStd) hSrc hS
    hDf hZ hGT.1

end

end Spin2
