import Spin2.Multiscale.ZBelow3
import Spin2.Multiscale.TwoPtNear
import Obs2.Map.SwapHist

/-!
# `GamFormB` from the mirrored `0`-part; `TwoPtSq` without `GamFormB` and `TwoPtNear`

**`GamFormB` (the `σ_x` part of the pair `γ` flow).** By the `a ↔ b` mirror of the map
(`Obs2.prj_obsHist`, `Obs2.neg_eps_u_b_eq_gamA`: the projection `F ↦ F_∅ + σ_aF_b` commutes with the
whole observable step, with the points changed from `(0, x)` to `(x, 0)`, and `zV b` is symmetric),

  `γ_{x,k} = uB(x)_k = γ_{a,k}` along the pair history with points **`ptsS x = (x, 0)`**  (`uB_eq_uMir`).

The chain of `Spin2/Multiscale/ZBelow2.lean` (`uA_succ`, `uA_eq_mmag`, `gamFormA_of`) then applies verbatim at
`a = x` (`uMir_succ`, `uMir_eq_mmag`, **`gamFormB_of`**); the only geometric input is the translation
invariance of the diagonal of the step covariance, `C_k(x,x) = Γ^{int}_{k+1}(0,0)`
(`histCov_gamInt_at`). The inputs are the mirror instances of those of `gamFormA_of`: (H_λ) for the
pair vertex `μ_{x,k}/μ_{x,0}` (`lamHat2` at `ptsS x`, e.g. from `Case2Rel`/`Case2Loop` at `ptsS x`
via `hLam_case2`, `pairHLamS_of`) and **`GamRemRelS`** (`GamRemRel` at `ptsS x`).

**`twoPtSq_of_gam_flowB`**: `twoPtSq_of_gam_flow` with `GamFormB` replaced by these mirror inputs and
`TwoPtNear` discharged by the model (`twoPtNear_of`, `K_N = L`, `K_{RN} = 1`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- The mirrored points `a = x`, `b = 0`. -/
def ptsS (x : Lam 2 L N) : Obs2.ObsPts 2 L N := ⟨x, 0, ∅⟩

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `γ_{a,k}` along the mirrored pair history (points `(x, 0)`). -/
def uMir (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.gamA (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- **`γ_{x,k} = uB = uMir`**: the `σ_x` part of the pair flow is the `σ_a` part of the mirrored one. -/
theorem uB_eq_uMir (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : uB R m b μ₀ x k = uMir R m b μ₀ x k :=
  Obs2.neg_eps_u_b_eq_gamA (R.withMsq m) (P := ptsX x) (P' := ptsS x) rfl _ _
    (Obs2.prjSt_obsInit_swap (zV b) rfl rfl rfl) _ k

/-- The remainder `ρ_k` of the mirrored `γ` flow. -/
def gamRemMir (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.gamRem2 (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- `β_k = -μ_{x,k}` along the mirrored history. -/
def btMir (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ := bt2 R (ptsS x) (zV b) m b μ₀ k

/-- `λ^γ_k = β_k/b - ρ_k/(bΓ_k)` for the mirrored flow. -/
def lamGMir (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  btMir R m b μ₀ x k / b - gamRemMir R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k)

/-- **Translation invariance of the diagonal**: `C_k(x,x) = Γ^{int}_{k+1}(0,0)`. -/
theorem histCov_gamInt_at (hP : R.P = Pc) (m : ℝ) (t : Hist.Seq (Xs (R.withMsq m))) (k : ℕ)
    (x : Lam 2 L N) : Obs2.histCovO (R.withMsq m) t k x x = GamInt (R.withMsq m) k t := by
  unfold Obs2.histCovO GamInt
  rw [stCov_eq_dData (R.withMsq m) hP t le_rfl]
  simp [DressedFRD.kmat]

theorem uMir_succ (hP : R.P = Pc) (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) :
    uMir R m b μ₀ x (k + 1) = uMir R m b μ₀ x k -
      Obs2.epsTot2 (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k -
      btMir R m b μ₀ x k * gamT R m b μ₀ k + gamRemMir R m b μ₀ x k := by
  have := Obs2.gamA_succ (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (fun b' => Obs2.obsInit_two_form _ _ b') k
  rw [show (ptsS x).a = x from rfl, histCov_gamInt_at R hP] at this
  exact this

theorem uMir_zero (m b μ₀ : ℝ) (x : Lam 2 L N) : uMir R m b μ₀ x 0 = 0 :=
  Obs2.gamA_obsInit_zero (R.withMsq m) (ptsS x) _ (zV b)

theorem btMir_zero (m b μ₀ : ℝ) (x : Lam 2 L N) : btMir R m b μ₀ x 0 = b := by
  unfold btMir; rw [bt2_zero]; simp [zV]

theorem b_mul_lamGMir {m b μ₀ : ℝ} (hb : b ≠ 0) {x : Lam 2 L N} {k : ℕ}
    (h0 : gamT R m b μ₀ k = 0 → gamRemMir R m b μ₀ x k = 0) :
    (b : ℂ) * (lamGMir R m b μ₀ x k * gamT R m b μ₀ k) =
      btMir R m b μ₀ x k * gamT R m b μ₀ k - gamRemMir R m b μ₀ x k := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb
  by_cases hΓ : gamT R m b μ₀ k = 0
  · rw [hΓ, h0 hΓ]; ring
  · unfold lamGMir; field_simp

/-- **`γ_{x,j} = M_j(λ^γ)`** for `j ≥ 1` (exact, mirrored flow). -/
theorem uMir_eq_mmag (hP : R.P = Pc) {m b μ₀ : ℝ} (hb : b ≠ 0) (x : Lam 2 L N) {j : ℕ}
    (hj : 1 ≤ j) (h0 : ∀ k < j, gamT R m b μ₀ k = 0 → gamRemMir R m b μ₀ x k = 0) :
    uMir R m b μ₀ x j = Mmag R m b μ₀ (lamGMir R m b μ₀ x) j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [uMir_succ R hP, uMir_zero, Obs2.epsTot2_obsInit, btMir_zero]
    have := b_mul_lamGMir R hb (x := x) (k := 0) (h0 0 one_pos)
    rw [btMir_zero] at this
    have hM : Mmag R m b μ₀ (lamGMir R m b μ₀ x) 1 =
        1 - (b : ℂ) * (lamGMir R m b μ₀ x 0 * gamT R m b μ₀ 0) := by
      unfold Mmag gamT; rw [sum_range_one]
    rw [hM, this]; simp [zV]; ring
  | succ n hn ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [uMir_succ R hP, ih (fun k hk => h0 k (by omega)), Obs2.epsTot2_succ]
    have := b_mul_lamGMir R hb (x := x) (k := n' + 1) (h0 _ (by omega))
    have hM : Mmag R m b μ₀ (lamGMir R m b μ₀ x) (n' + 1 + 1) =
        Mmag R m b μ₀ (lamGMir R m b μ₀ x) (n' + 1) -
          (b : ℂ) * (lamGMir R m b μ₀ x (n' + 1) * gamT R m b μ₀ (n' + 1)) := by
      unfold Mmag gamT; rw [sum_range_succ _ (n' + 1)]; ring
    rw [hM, this]; ring

/-- **Named input (mirror of `GamRemRel`)**: the remainder of the mirrored `γ` flow (points
`(x, 0)`) is relatively small below `j_x`. -/
def GamRemRelS (Nh : ℕ) (m b μ₀ cγ : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ k < Obs.coal L (0 : Lam 2 L N) x, ‖gamRemMir R m b μ₀ x k‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) *
        (b * ‖gamT R m b μ₀ k‖)

/-- **`GamFormB` from (H_λ) for the mirrored pair vertex `μ_{x,k}/μ_{x,0}` and `GamRemRelS`.** -/
theorem gamFormB_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ Kl cγ : ℝ} (hb : 0 < b) (hm : 0 ≤ m)
    (hcγ : 0 ≤ cγ) (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kl)
    (hrem : GamRemRelS R Nh m b μ₀ cγ) : GamFormB R Nh m b μ₀ (Kl + cγ) := by
  intro x hx hj1 hj
  have hpos : ∀ k ≤ Nh, 0 ≤ thJ R m b μ₀ k *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := fun k hk =>
    mul_nonneg (Real.rpow_nonneg (div_pos (hg k hk) hb).le _)
      (add_nonneg (hg k hk).le (zA_nonneg L hm k))
  have h0 : ∀ k < Obs.coal L (0 : Lam 2 L N) x,
      gamT R m b μ₀ k = 0 → gamRemMir R m b μ₀ x k = 0 := by
    intro k hk hΓ
    have := hrem x hx hj k hk
    rw [hΓ, norm_zero, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  refine ⟨lamGMir R m b μ₀ x, fun k hk => ?_, ?_⟩
  · have hkN : k < Nh := lt_of_lt_of_le hk hj
    have hlh : lamHat2 R (ptsS x) (zV b) m b μ₀ k = btMir R m b μ₀ x k / b := by
      unfold lamHat2
      rw [show bt2 R (ptsS x) (zV b) m b μ₀ 0 = btMir R m b μ₀ x 0 from rfl, btMir_zero]
      rfl
    have h1 := hl x hx k hkN
    rw [hlh] at h1
    have e : lamGMir R m b μ₀ x k - ((thJ R m b μ₀ k : ℝ) : ℂ) =
        (btMir R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)) -
          gamRemMir R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k) := by unfold lamGMir; ring
    have h2 : ‖gamRemMir R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k)‖ ≤
        cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by
      by_cases hΓ : gamT R m b μ₀ k = 0
      · rw [hΓ, mul_zero, div_zero, norm_zero, mul_assoc]
        exact mul_nonneg hcγ (hpos k hkN.le)
      · have hd : 0 < b * ‖gamT R m b μ₀ k‖ := mul_pos hb (norm_pos_iff.2 hΓ)
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb,
          div_le_iff₀ hd]
        exact hrem x hx hj k hk
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1' : ‖btMir R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
        Kl * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := h1
    linarith
  · rw [uB_eq_uMir]
    exact uMir_eq_mmag R hP hb.ne' x hj1 h0

end Traj

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from the `γ` flow, without `GamFormB` and `TwoPtNear`** (master constants):
`GamFormB` from the mirrored `0`-part (`gamFormB_of`: (H_λ) for `lamHat2` at `ptsS x` and
`GamRemRelS`), `TwoPtNear` from the model (`twoPtNear_of`, `K_N = L`, `K_{RN} = 1`). -/
theorem twoPtSq_of_gam_flowB {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMC : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl Kp cγ KE KR : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ cγ →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp) →
      GamRemRel R Nh m b μ₀ cγ → GamRemRelS R Nh m b μ₀ cγ →
      PairAboveW1 R Nh m b μ₀ lam KE KR →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      TwoPtSq R Nh m b μ₀ lam
        (max (zbKM L cg Ke KZ KG Kp cγ (Kp + cγ) Kl * (2 + zbKM L cg Ke KZ KG Kp cγ (Kp + cγ) Kl)
          + KE) (L : ℝ))
        (max (1 + 2 * (1 + zbKM L cg Ke KZ KG Kp cγ (Kp + cγ) Kl) * zbMb L cg Ke KZ KG Kl + KR)
          1) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam Kl Kp cγ KE KR
    hKl hKp hcγ hl hpair hpairS hrem hremS hE hsmall
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := fun k hk =>
    (hadm.1 k hk).1
  have hB := gamFormB_of R hP hb hm.1.le hcγ hg hpairS hremS
  have hNear := twoPtNear_of (L := L) (N := N) (by omega) hb hm.1 hh
  exact twoPtSq_of_gam_flow hF hε1 hL hSp hMC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh
    lam Kl Kp cγ (Kp + cγ) KE KR (L : ℝ) 1 hKl hKp hcγ (add_nonneg hKp hcγ) hl hpair hrem hB hE
    hNear hsmall

end

end Spin2
