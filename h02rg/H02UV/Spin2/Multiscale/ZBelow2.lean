import Spin2.Multiscale.ZBelow

/-!
# `ZBelowU1` from the exact `γ` flow and `MagConcl`

See the module docstring of `Spin2/Multiscale/ZBelow.lean`.
* `histCov_gamInt`: `C_k(0,0) = Γ^{int}_{k+1}(0,0)` (`GamInt`), the dressed covariance;
* **`uA_succ`**: `γ_{0,k+1} = γ_{0,k} - ∑_Bε(V_k(B)_0) - β_kΓ^{int}_{k+1}(0,0) + ρ_k` along the pair
  history (`β_k = bt2`, `ρ_k = gamRemX`);
* **`uA_eq_mmag`**: `γ_{0,j} = M_j(λ^γ)` for `j ≥ 1`, `λ^γ_k = β_k/b - ρ_k/(bΓ_k)` (`lamG`);
* `GamRemRel` (named), `GamFormA`, `GamFormB` (named), **`gamFormA_of`**;
* `MagAt` (`MagConcl` at one trajectory, `magAt_of`), **`mmag_near_of`**, **`zBelowU1_of_forms`**;
* `mmag_bound_of`: `‖M_k‖ ≤ Θ(1 + K)` from `ϑ_k ≤ Θ`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `θ_k = (ǧ_k/b)^{1/3}`, the expected size of `λ̂_k`. -/
def thJ (m b μ₀ : ℝ) (k : ℕ) : ℝ := ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ)

/-- `ϑ_k = (b/ǧ_k)^{1/3}`. -/
def varthJ (m b μ₀ : ℝ) (k : ℕ) : ℝ := (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) ^ (1 / 3 : ℝ)

/-- The remainder `ρ_k` of the `γ_0` flow along the pair history. -/
def gamRemX (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.gamRem2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- `β_k = -μ_{0,k}` along the pair history. -/
def btX (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ := bt2 R (ptsX x) (zV b) m b μ₀ k

/-- `Γ_k = Γ^{int}_{k+1}(0,0)` along the trajectory. -/
def gamT (m b μ₀ : ℝ) (k : ℕ) : ℂ := GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- `λ^γ_k = β_k/b - ρ_k/(bΓ_k)`. -/
def lamG (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  btX R m b μ₀ x k / b - gamRemX R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k)

/-- **The covariance of the observable step is the dressed `Γ^{int}_{k+1}`**: `C_k(0,0) = GamInt`. -/
theorem histCov_gamInt (hP : R.P = Pc) (m : ℝ) (t : Hist.Seq (Xs (R.withMsq m))) (k : ℕ) :
    Obs2.histCovO (R.withMsq m) t k 0 0 = GamInt (R.withMsq m) k t := by
  unfold Obs2.histCovO GamInt
  rw [stCov_eq_dData (R.withMsq m) hP t le_rfl]
  simp [DressedFRD.kmat]

/-- **The exact `γ_0` flow along the pair history.** -/
theorem uA_succ (hP : R.P = Pc) (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) :
    uA R m b μ₀ x (k + 1) = uA R m b μ₀ x k -
      Obs2.epsTot2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k -
      btX R m b μ₀ x k * gamT R m b μ₀ k + gamRemX R m b μ₀ x k := by
  have := Obs2.gamA_succ (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (fun b' => Obs2.obsInit_two_form _ _ b') k
  rw [show (ptsX x).a = (0 : Lam 2 L N) from rfl, histCov_gamInt R hP] at this
  exact this

theorem btX_zero (m b μ₀ : ℝ) (x : Lam 2 L N) : btX R m b μ₀ x 0 = b := by
  unfold btX; rw [bt2_zero]; simp [zV]

theorem b_mul_lamG {m b μ₀ : ℝ} (hb : b ≠ 0) {x : Lam 2 L N} {k : ℕ}
    (h0 : gamT R m b μ₀ k = 0 → gamRemX R m b μ₀ x k = 0) :
    (b : ℂ) * (lamG R m b μ₀ x k * gamT R m b μ₀ k) =
      btX R m b μ₀ x k * gamT R m b μ₀ k - gamRemX R m b μ₀ x k := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb
  by_cases hΓ : gamT R m b μ₀ k = 0
  · rw [hΓ, h0 hΓ]; ring
  · unfold lamG; field_simp

/-- **`γ_{0,j} = M_j(λ^γ)`** for `j ≥ 1` (exact). -/
theorem uA_eq_mmag (hP : R.P = Pc) {m b μ₀ : ℝ} (hb : b ≠ 0) (x : Lam 2 L N) {j : ℕ}
    (hj : 1 ≤ j) (h0 : ∀ k < j, gamT R m b μ₀ k = 0 → gamRemX R m b μ₀ x k = 0) :
    uA R m b μ₀ x j = Mmag R m b μ₀ (lamG R m b μ₀ x) j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [uA_succ R hP, uA_zero, Obs2.epsTot2_obsInit, btX_zero]
    have := b_mul_lamG R hb (x := x) (k := 0) (h0 0 one_pos)
    rw [btX_zero] at this
    have hM : Mmag R m b μ₀ (lamG R m b μ₀ x) 1 =
        1 - (b : ℂ) * (lamG R m b μ₀ x 0 * gamT R m b μ₀ 0) := by
      unfold Mmag gamT; rw [sum_range_one]
    rw [hM, this]; simp [zV]; ring
  | succ n hn ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [uA_succ R hP, ih (fun k hk => h0 k (by omega)), Obs2.epsTot2_succ]
    have := b_mul_lamG R hb (x := x) (k := n' + 1) (h0 _ (by omega))
    have hM : Mmag R m b μ₀ (lamG R m b μ₀ x) (n' + 1 + 1) =
        Mmag R m b μ₀ (lamG R m b μ₀ x) (n' + 1) -
          (b : ℂ) * (lamG R m b μ₀ x (n' + 1) * gamT R m b μ₀ (n' + 1)) := by
      unfold Mmag gamT; rw [sum_range_succ _ (n' + 1)]; ring
    rw [hM, this]; ring

/-- **Named input: the remainder of the `γ_0` flow is relatively small**:
`‖ρ_k‖ ≤ c_γθ_k(ǧ_k + a_k)·b‖Γ^{int}_{k+1}(0,0)‖` below `j_x`. -/
def GamRemRel (Nh : ℕ) (m b μ₀ cγ : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ k < Obs.coal L (0 : Lam 2 L N) x, ‖gamRemX R m b μ₀ x k‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) *
        (b * ‖gamT R m b μ₀ k‖)

/-- `γ_{0,j_x} = M_{j_x}(λ^a)` with `λ^a` relatively close to `θ` below `j_x`. -/
def GamFormA (Nh : ℕ) (m b μ₀ Ka : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ lamA : ℕ → ℂ, (∀ k < Obs.coal L (0 : Lam 2 L N) x,
      ‖lamA k - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
        Ka * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) ∧
      uA R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) =
        Mmag R m b μ₀ lamA (Obs.coal L (0 : Lam 2 L N) x)

/-- **Named input (mirror of `GamFormA` for the `σ_x` part)**. -/
def GamFormB (Nh : ℕ) (m b μ₀ Kb : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ lamB : ℕ → ℂ, (∀ k < Obs.coal L (0 : Lam 2 L N) x,
      ‖lamB k - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
        Kb * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) ∧
      uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x) =
        Mmag R m b μ₀ lamB (Obs.coal L (0 : Lam 2 L N) x)

/-- **`GamFormA` from (H_λ) for the pair `λ̂ = μ_{0,k}/μ_{0,0}` and `GamRemRel`.** -/
theorem gamFormA_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ Kl cγ : ℝ} (hb : 0 < b) (hm : 0 ≤ m)
    (hcγ : 0 ≤ cγ) (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kl)
    (hrem : GamRemRel R Nh m b μ₀ cγ) : GamFormA R Nh m b μ₀ (Kl + cγ) := by
  intro x hx hj1 hj
  have hpos : ∀ k ≤ Nh, 0 ≤ thJ R m b μ₀ k *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := fun k hk =>
    mul_nonneg (Real.rpow_nonneg (div_pos (hg k hk) hb).le _)
      (add_nonneg (hg k hk).le (zA_nonneg L hm k))
  have hgb : ∀ k ≤ Nh, 0 ≤ b * ‖gamT R m b μ₀ k‖ := fun _ _ => mul_nonneg hb.le (norm_nonneg _)
  have h0 : ∀ k < Obs.coal L (0 : Lam 2 L N) x,
      gamT R m b μ₀ k = 0 → gamRemX R m b μ₀ x k = 0 := by
    intro k hk hΓ
    have := hrem x hx hj k hk
    rw [hΓ, norm_zero, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  refine ⟨lamG R m b μ₀ x, fun k hk => ?_, uA_eq_mmag R hP hb.ne' x hj1 h0⟩
  have hkN : k < Nh := lt_of_lt_of_le hk hj
  have hlh : lamHat2 R (ptsX x) (zV b) m b μ₀ k = btX R m b μ₀ x k / b := by
    unfold lamHat2; rw [show bt2 R (ptsX x) (zV b) m b μ₀ 0 = btX R m b μ₀ x 0 from rfl, btX_zero]
    rfl
  have h1 := hl x hx k hkN
  rw [hlh] at h1
  have e : lamG R m b μ₀ x k - ((thJ R m b μ₀ k : ℝ) : ℂ) =
      (btX R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)) -
        gamRemX R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k) := by unfold lamG; ring
  have h2 : ‖gamRemX R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k)‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by
    by_cases hΓ : gamT R m b μ₀ k = 0
    · rw [hΓ, mul_zero, div_zero, norm_zero]
      exact mul_nonneg hcγ (by simpa [mul_assoc] using hpos k hkN.le) |>.trans_eq' rfl
        |> fun h => by simpa [mul_assoc] using h
    · have hd : 0 < b * ‖gamT R m b μ₀ k‖ := mul_pos hb (norm_pos_iff.2 hΓ)
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb,
        div_le_iff₀ hd]
      exact hrem x hx hj k hk
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1' : ‖btX R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
      Kl * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := h1
  linarith

/-! ### Comparison through `ϑ_j` (`MagConcl`) -/

/-- `MagConcl` at one trajectory, with constant `f(K_λ)`. -/
def MagAt (Nh : ℕ) (m b μ₀ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl → HLam R Nh m b μ₀ lam Kl → ∀ j ≤ Nh,
    ‖Mmag R m b μ₀ lam j - ((varthJ R m b μ₀ j : ℝ) : ℂ)‖ ≤
      f Kl * varthJ R m b μ₀ j * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1

theorem magAt_of {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hMC : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = ℓ) (hRA : R.A = A) (hRρ : R.ρ = ρ) (hN : 1 ≤ N)
    {Nh : ℕ} (hNh : Nh + 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) :
    MagAt R Nh m b μ₀ (fun Kl => spinMK L cg Ke KZ Kl KG 0) :=
  fun lam Kl hKl hl j hj => hMC N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm lam Kl hKl hl j hj

/-- **Two vertex sequences close to `θ` give magnetisations close to each other, relative to
`‖M_j‖`.** -/
theorem mmag_near_of {Nh : ℕ} {m b μ₀ : ℝ} {f : ℝ → ℝ} (hMag : MagAt R Nh m b μ₀ f)
    (hm : 0 ≤ m) (hb : 0 < b) (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    {lam : ℕ → ℂ} {Kl : ℝ} (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl) {j : ℕ} (hj : j ≤ Nh)
    (hsmall : max (f Kl) 0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2)
    {lam' : ℕ → ℂ} {K' : ℝ} (hK' : 0 ≤ K')
    (hl' : ∀ k < j, ‖lam' k - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
      K' * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) :
    ‖Mmag R m b μ₀ lam' j - Mmag R m b μ₀ lam j‖ ≤
      2 * (max (f K') 0 + max (f Kl) 0) * ‖Mmag R m b μ₀ lam j‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 := by
  classical
  set lam'' : ℕ → ℂ := fun k => if k < j then lam' k else ((thJ R m b μ₀ k : ℝ) : ℂ) with hl''d
  have hl'' : HLam R Nh m b μ₀ lam'' K' := by
    intro k hk
    show ‖lam'' k - _‖ ≤ _
    by_cases hkj : k < j
    · simp only [hl''d, if_pos hkj]; exact hl' k hkj
    · simp only [hl''d, if_neg hkj, thJ, sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg hK' (Real.rpow_nonneg (div_pos (hg k hk.le) hb).le _))
        (add_nonneg (hg k hk.le).le (zA_nonneg L hm k))
  have heq : Mmag R m b μ₀ lam'' j = Mmag R m b μ₀ lam' j := by
    unfold Mmag
    congr 2
    exact sum_congr rfl fun k hk => by simp only [hl''d, if_pos (mem_range.1 hk)]
  have h1 := hMag lam'' K' hK' hl'' j hj
  have h2 := hMag lam Kl hKl hl j hj
  rw [heq] at h1
  set M := Mmag R m b μ₀ lam j
  set M' := Mmag R m b μ₀ lam' j
  set v : ℝ := varthJ R m b μ₀ j
  set g : ℝ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1
  have hv : 0 ≤ v := Real.rpow_nonneg (div_pos hb (hg j hj)).le _
  have hg0 : 0 < g := hg j hj
  set F := max (f Kl) 0
  set F' := max (f K') 0
  have hF : 0 ≤ F := le_max_right _ _
  have hF' : 0 ≤ F' := le_max_right _ _
  have h1' : ‖M' - (v : ℂ)‖ ≤ F' * v * g :=
    h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
      hg0.le)
  have h2' : ‖M - (v : ℂ)‖ ≤ F * v * g :=
    h2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
      hg0.le)
  have hvM : v ≤ 2 * ‖M‖ := by
    have hvn : ‖(v : ℂ)‖ = v := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    have t := norm_le_norm_add_norm_sub' (v : ℂ) M
    rw [hvn, norm_sub_rev] at t
    have : F * v * g ≤ v / 2 := by
      have := mul_le_mul_of_nonneg_right hsmall hv
      nlinarith
    linarith
  have tri : ‖M' - M‖ ≤ ‖M' - (v : ℂ)‖ + ‖M - (v : ℂ)‖ := by
    have := norm_sub_le (M' - (v : ℂ)) (M - (v : ℂ))
    rwa [sub_sub_sub_cancel_right] at this
  have hfin : (F' * v * g) + (F * v * g) ≤ 2 * (F' + F) * ‖M‖ * g := by
    have := mul_le_mul_of_nonneg_left hvM (mul_nonneg (add_nonneg hF' hF) hg0.le)
    nlinarith
  linarith

/-- **`ZBelowU1` from `GamFormA`, `GamFormB`, (H_λ) and `MagConcl`.** -/
theorem zBelowU1_of_forms {Nh : ℕ} {m b μ₀ : ℝ} {f : ℝ → ℝ} (hMag : MagAt R Nh m b μ₀ f)
    (hm : 0 ≤ m) (hb : 0 < b) (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    {lam : ℕ → ℂ} {Kl : ℝ} (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (f Kl) 0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2)
    {Ka Kb : ℝ} (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hA : GamFormA R Nh m b μ₀ Ka)
    (hB : GamFormB R Nh m b μ₀ Kb) :
    ZBelowU1 R Nh m b μ₀ lam (2 * (max (f Ka) 0 + max (f Kb) 0 + max (f Kl) 0)) := by
  intro x hx hj1 hj
  obtain ⟨lA, hlA, eA⟩ := hA x hx hj1 hj
  obtain ⟨lB, hlB, eB⟩ := hB x hx hj1 hj
  have hMg : 0 ≤ ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 :=
    mul_nonneg (norm_nonneg _) (hg _ hj).le
  have ha := mmag_near_of R hMag hm hb hg hKl hl hj (hsmall _ hj) hKa hlA
  have hb' := mmag_near_of R hMag hm hb hg hKl hl hj (hsmall _ hj) hKb hlB
  rw [← eA] at ha
  rw [← eB] at hb'
  have hFa := le_max_right (f Ka) 0
  have hFb := le_max_right (f Kb) 0
  have hFl := le_max_right (f Kl) 0
  constructor
  · refine ha.trans ?_
    rw [mul_assoc, mul_assoc (2 * _)]
    exact mul_le_mul_of_nonneg_right (by linarith) hMg
  · refine hb'.trans ?_
    rw [mul_assoc, mul_assoc (2 * _)]
    exact mul_le_mul_of_nonneg_right (by linarith) hMg

/-- `‖M_k‖ ≤ Θ(1 + K)` from `ϑ_k ≤ Θ`, `K ǧ_k ≤ K` (bookkeeping for `twoPtSq_of_zz1`). -/
theorem mmag_bound_of {Nh : ℕ} {m b μ₀ : ℝ} {f : ℝ → ℝ} (hMag : MagAt R Nh m b μ₀ f)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    {lam : ℕ → ℂ} {Kl : ℝ} (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl) {Θ : ℝ}
    (hΘ : ∀ k ≤ Nh, varthJ R m b μ₀ k ≤ Θ) (hb : 0 ≤ b) :
    ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Θ * (1 + max (f Kl) 0) := by
  intro k hk
  have h := hMag lam Kl hKl hl k hk
  have hv : 0 ≤ varthJ R m b μ₀ k := Real.rpow_nonneg (div_nonneg hb (hg k hk).1) _
  have hvn : ‖((varthJ R m b μ₀ k : ℝ) : ℂ)‖ = varthJ R m b μ₀ k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  have t := norm_le_norm_add_norm_sub' (Mmag R m b μ₀ lam k) ((varthJ R m b μ₀ k : ℝ) : ℂ)
  rw [hvn] at t
  have hF := le_max_left (f Kl) 0
  have hF0 := le_max_right (f Kl) 0
  have e1 : f Kl * varthJ R m b μ₀ k * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      max (f Kl) 0 * varthJ R m b μ₀ k := by
    have := mul_le_mul_of_nonneg_left (hg k hk).2 (mul_nonneg hF0 hv)
    have h2 := mul_le_mul_of_nonneg_right hF (mul_nonneg hv (hg k hk).1)
    nlinarith
  have hΘ0 : 0 ≤ Θ := hv.trans (hΘ k hk)
  have := mul_le_mul_of_nonneg_left (hΘ k hk) (add_nonneg zero_le_one hF0)
  nlinarith

end Traj

end

end Spin2
