import Step2.Flow.FlowMasterHypLZ
import Spin2.Pair.PairAbove
import Spin2.Gam.GamRem
import Spin2.Multiscale.ObsRel
import Obs2.Flow.GamTop

/-!
# `GamTopBd`: the one-point `γ` coupling at the top scale `N`

Pair history `obsInit .two (zV b) (ptsX x)`, trajectory `t` at mass `m²`, `N = N_h + 2`. The `σ_a`
part of the flow does not depend on `x` (`Obs2/Map/SwapHist`), and `uA_succ` is exact at every scale.
So `γ_{a,N}` (`gamNa`) is followed through all scales, the last step included:

* `uA_succ_pos`: `γ_{a,k+1} = γ_{a,k} - (β_kΓ_k - ρ_k)` for `k ≥ 1`;
* **`gamNa_eq`** (last step, `Obs2.eps_uXO_univ_a` with `C = stCovN`):
  `γ_{a,N} = γ_{a,N-1} - β_{N-1}C_N(0,0) + ρ_N`, `ρ_N = gamRemN`;
* **`gamNa_sub_uA`**: `γ_{a,N} - γ_{a,N_h} = -(β_{N_h}Γ_{N_h} - ρ_{N_h}) - (β_{N_h+1}C_N(0,0) - ρ_N)`.

Below `N_h`, `γ_{a,N_h} = M_{N_h}(λ^γ)` (`uA_eq_mmag`), with `λ^γ` within `(K_p + c_γ)θ_k(ǧ_k + a_k)`
of `θ_k` once `ρ_k` is relatively small for **all** `k < N_h` (not only `k < j_x`). Then
`MagConcl` gives `‖M_{N_h}(λ^γ)‖ ≤ ϑ_{N_h}(1 + K)`, and `ϑ_{N_h} ≤ ϑ_{j_x} ≤ 2‖M_{j_x}‖`
(`ǧ` nondecreasing along admissible trajectories: `GMonoConcl`, from (F1) of the master
construction, `gMonoConcl_of`).

Named inputs:
* **`GamWKTop c_w`**: `GamWKRel` for all `k < N_h`
  (`‖gamWKX_k‖ ≤ c_w(ǧ_k + a_k)‖β_k‖‖Γ_k‖`); with `GamBulkRel` (already for `k < N_h`) it
  gives `GamRemRel` for all `k < N_h` (`gamRemX_top_le`);
* **`GamLastRel c_L`**: the two steps above `N_h`,
  `‖β_{N_h}Γ_{N_h} - ρ_{N_h}‖ + ‖β_{N_h+1}C_N(0,0) - ρ_N‖ ≤ c_Lϑ_{N_h}ǧ_{N_h}`
  (the natural size: `bθ_k/|Z_{k+1}| = b^{1/3}ǧ_k^{2/3} = ϑ_kǧ_k`).

**`gamTopBd_of`** (trajectory), **`gamTopBd_flow`** (admissible trajectories, `FlowC2Concl`,
`MagConcl`, `GMonoConcl`): `GamTopBd` with `K₄ = 2(1 + K(K_p + c_γ) + c_L)`,
`c_γ = (c_e + c_w)(1 + 3K_p)`, `K(·) = max(spinMK ·, 0)`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `C_N(0,0)`: the diagonal of the last-step covariance `stCovN`. -/
def zCovN (Nh : ℕ) (m b μ₀ : ℝ) : ℂ :=
  LastN.stCovN (R.withMsq m) (Nh + 1)
    (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st 0 0

/-- `ρ_N`: the remainder of the last `γ` step (pair history). -/
def gamRemN (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : ℂ :=
  Obs2.gamRemG (ptsX x) (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullK (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))

/-- **The last `γ` step** (exact): `γ_{a,N} = γ_{a,N-1} - β_{N-1}C_N(0,0) + ρ_N`. -/
theorem gamNa_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    gamNa R Nh m b μ₀ x = uA R m b μ₀ x (Nh + 1) -
      btX R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ + gamRemN R Nh m b μ₀ x := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  set o₀ := Obs2.obsInit .two (zV b) (ptsX x)
  have hVa : ∀ c, (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
      (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsX x) o₀ (Nh + 1) t) c : SA .two (Lam 2 L N)).a =
      (Obs2.histVO2 (R.withMsq m) (ptsX x) o₀ t (Nh + 1) c : SA .two (Lam 2 L N)).a := by
    intro c
    rw [Obs2.histVO2_a]
    exact Obs2.emb_add_cmp true _ _
  have hform := Obs2.obsHist_hform2 (R.withMsq m) (ptsX x) o₀ t
    (fun b' => Obs2.obsInit_two_form _ _ b') (Nh + 1)
  have h := Obs2.eps_uXO_univ_a (ptsX x) (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
      (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsX x) o₀ (Nh + 1) t))
    (Obs2.fullW (histOut (R.withMsq m) Nh t).st (histOut (R.withMsq m) Nh t).D
      (Obs2.obsHist (R.withMsq m) (ptsX x) o₀ (Nh + 1) t))
    (Obs2.fullK (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
      (histOut (R.withMsq m) Nh t).K (Obs2.obsHist (R.withMsq m) (ptsX x) o₀ (Nh + 1) t))
    (fun c => by rw [hVa]; exact hform c)
  have hε : ∑ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ε (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
        (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
        (Obs2.obsHist (R.withMsq m) (ptsX x) o₀ (Nh + 1) t) c : SA .two (Lam 2 L N)).a = 0 := by
    have := Obs2.epsTot2_succ (R.withMsq m) (ptsX x) o₀ t Nh
    unfold Obs2.epsTot2 at this
    rw [← this]
    exact sum_congr rfl fun c _ => by rw [hVa]
  have hβ : Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
      (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
        (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
        (Obs2.obsHist (R.withMsq m) (ptsX x) o₀ (Nh + 1) t)) = btX R m b μ₀ x (Nh + 1) := by
    unfold btX bt2 Obs2.betaTot2
    exact sum_congr rfl fun c _ => by rw [hVa]; rfl
  rw [hε, hβ, zero_add] at h
  have h' : ε (zUN R Nh m b μ₀ x : SA .two (Lam 2 L N)).a =
      btX R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ - gamRemN R Nh m b μ₀ x := h
  unfold gamNa
  rw [h']
  ring

/-- The `γ` step above scale `0`: `γ_{a,k+1} = γ_{a,k} - (β_kΓ_k - ρ_k)`. -/
theorem uA_succ_pos (hP : R.P = Pc) (m b μ₀ : ℝ) (x : Lam 2 L N) {k : ℕ} (hk : 1 ≤ k) :
    uA R m b μ₀ x (k + 1) = uA R m b μ₀ x k -
      (btX R m b μ₀ x k * gamT R m b μ₀ k - gamRemX R m b μ₀ x k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [uA_succ R hP, Obs2.epsTot2_succ]; ring

/-- **The two steps above `N_h`**: `γ_{a,N} - γ_{a,N_h} =
-(β_{N_h}Γ_{N_h} - ρ_{N_h}) - (β_{N_h+1}C_N(0,0) - ρ_N)`. -/
theorem gamNa_sub_uA (hP : R.P = Pc) {Nh : ℕ} (hNh : 1 ≤ Nh) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    gamNa R Nh m b μ₀ x - uA R m b μ₀ x Nh =
      -(btX R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemX R m b μ₀ x Nh) -
        (btX R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ - gamRemN R Nh m b μ₀ x) := by
  rw [gamNa_eq, uA_succ_pos R hP m b μ₀ x hNh]; ring

/-! ### Named inputs -/

/-- **Named input (observable, all scales below `N_h`)**: `GamWKRel` for every `k < N_h`. -/
def GamWKTop (Nh : ℕ) (m b μ₀ cw : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ k < Nh, ‖gamWKX R m b μ₀ x k‖ ≤
      cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖btX R m b μ₀ x k‖ *
        ‖gamT R m b μ₀ k‖

/-- **Named input (the two steps above `N_h`)**:
`‖β_{N_h}Γ_{N_h} - ρ_{N_h}‖ + ‖β_{N_h+1}C_N(0,0) - ρ_N‖ ≤ c_Lϑ_{N_h}ǧ_{N_h}`. -/
def GamLastRel (Nh : ℕ) (m b μ₀ cL : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖btX R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemX R m b μ₀ x Nh‖ +
        ‖btX R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ - gamRemN R Nh m b μ₀ x‖ ≤
      cL * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1

/-! ### The bound -/

/-- `‖ρ_k‖ ≤ c_γθ_k(ǧ_k + a_k)b‖Γ_k‖` for every `k < N_h`, `c_γ = (c_e + c_w)(1 + 3K_p)`. -/
theorem gamRemX_top_le {Nh : ℕ} {m b μ₀ Kp ce cw : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hce : 0 ≤ ce) (hcw : 0 ≤ cw) (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    {x : Lam 2 L N} (hl : HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hB : GamBulkRel R Nh m b μ₀ ce)
    (hW : ∀ k < Nh, ‖gamWKX R m b μ₀ x k‖ ≤
      cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖btX R m b μ₀ x k‖ *
        ‖gamT R m b μ₀ k‖) :
    ∀ k < Nh, ‖gamRemX R m b μ₀ x k‖ ≤
      (ce + cw) * (1 + 3 * Kp) * thJ R m b μ₀ k *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * (b * ‖gamT R m b μ₀ k‖) := by
  intro k hkN
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 with hgd
  set a := zA L m k with had
  set θ := thJ R m b μ₀ k with hθd
  set β := btX R m b μ₀ x k with hβd
  set Γ := ‖gamT R m b μ₀ k‖ with hΓd
  have hθ : 0 ≤ θ := Real.rpow_nonneg (div_nonneg (hg k hkN).1 hb.le) _
  have hga0 : 0 ≤ g + a := add_nonneg (hg k hkN).1 (ha k hkN).1
  have hga3 : g + a ≤ 3 := by linarith only [(hg k hkN).2, (ha k hkN).2]
  have hΓ : 0 ≤ Γ := norm_nonneg _
  have hlh : lamHat2 R (ptsX x) (zV b) m b μ₀ k = β / b := by
    unfold lamHat2; rw [show bt2 R (ptsX x) (zV b) m b μ₀ 0 = btX R m b μ₀ x 0 from rfl, btX_zero]
    rfl
  have h1 := hl k hkN
  rw [hlh] at h1
  have h1' : ‖β / b - ((θ : ℝ) : ℂ)‖ ≤ Kp * θ * (g + a) := h1
  have hβb : ‖β‖ = b * ‖β / b‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]; field_simp
  have hβ1 : ‖β / b‖ ≤ θ * (1 + 3 * Kp) := by
    have := norm_le_insert' (β / b) ((θ : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ] at this
    have h2 : Kp * θ * (g + a) ≤ Kp * θ * 3 :=
      mul_le_mul_of_nonneg_left hga3 (mul_nonneg hKp hθ)
    nlinarith
  have hβ : ‖β‖ ≤ b * θ * (1 + 3 * Kp) := by
    rw [hβb, mul_assoc]; exact mul_le_mul_of_nonneg_left hβ1 hb.le
  rw [gamRemX_split R hV x hkN]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hW' := hW k hkN
  have hB' := hB k hkN
  have e1 : ‖gamWKX R m b μ₀ x k‖ + ‖β‖ * ‖gamBulkT R m b μ₀ k‖ ≤
      (ce + cw) * (g + a) * ‖β‖ * Γ := by
    have := mul_le_mul_of_nonneg_left hB' (norm_nonneg β)
    have e : ‖β‖ * (ce * (g + a) * Γ) = ce * (g + a) * ‖β‖ * Γ := by ring
    have e' : (ce + cw) * (g + a) * ‖β‖ * Γ =
        cw * (g + a) * ‖β‖ * Γ + ce * (g + a) * ‖β‖ * Γ := by ring
    rw [e'] at *
    linarith only [hW', this, e]
  refine e1.trans ?_
  have hc : 0 ≤ (ce + cw) * (g + a) := mul_nonneg (add_nonneg hce hcw) hga0
  calc (ce + cw) * (g + a) * ‖β‖ * Γ ≤ (ce + cw) * (g + a) * (b * θ * (1 + 3 * Kp)) * Γ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hc) hΓ
    _ = (ce + cw) * (1 + 3 * Kp) * θ * (g + a) * (b * Γ) := by ring

/-- (H_λ) for `λ^γ` on all of `k < N_h`, from (H_λ) for the pair vertex and the `ρ` bound. -/
theorem hLam_lamG {Nh : ℕ} {m b μ₀ Kp cγ : ℝ} (hb : 0 < b) (hcγ : 0 ≤ cγ) {x : Lam 2 L N}
    (hl : HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hθa : ∀ k < Nh, 0 ≤ thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hrem : ∀ k < Nh, ‖gamRemX R m b μ₀ x k‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) *
        (b * ‖gamT R m b μ₀ k‖)) :
    HLam R Nh m b μ₀ (lamG R m b μ₀ x) (Kp + cγ) := by
  intro k hkN
  have hlh : lamHat2 R (ptsX x) (zV b) m b μ₀ k = btX R m b μ₀ x k / b := by
    unfold lamHat2; rw [show bt2 R (ptsX x) (zV b) m b μ₀ 0 = btX R m b μ₀ x 0 from rfl, btX_zero]
    rfl
  have h1 := hl k hkN
  rw [hlh] at h1
  have e : lamG R m b μ₀ x k - ((thJ R m b μ₀ k : ℝ) : ℂ) =
      (btX R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)) -
        gamRemX R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k) := by unfold lamG; ring
  have h2 : ‖gamRemX R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k)‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by
    by_cases hΓ : gamT R m b μ₀ k = 0
    · rw [hΓ, mul_zero, div_zero, norm_zero, mul_assoc]
      exact mul_nonneg hcγ (hθa k hkN)
    · have hd : 0 < b * ‖gamT R m b μ₀ k‖ := mul_pos hb (norm_pos_iff.2 hΓ)
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb,
        div_le_iff₀ hd]
      exact hrem k hkN
  show ‖lamG R m b μ₀ x k - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
    (Kp + cγ) * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1' : ‖btX R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
      Kp * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := h1
  have : (Kp + cγ) * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) =
      Kp * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) +
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by ring
  rw [this]
  exact add_le_add h1' h2

/-- Pure assembly: `‖G‖ ≤ 2(1 + F' + c_L)‖M‖`. -/
theorem gamTop_pure {G U Mp M : ℂ} {v' v g' g F F' cL : ℝ} (hv' : 0 ≤ v') (hvv : v' ≤ v)
    (_hg'0 : 0 ≤ g') (hg'1 : g' ≤ 1) (_hg0 : 0 ≤ g) (hF' : 0 ≤ F') (_hF : 0 ≤ F) (hcL : 0 ≤ cL)
    (hU : U = Mp) (hMp : ‖Mp - (v' : ℂ)‖ ≤ F' * v' * g') (hGU : ‖G - U‖ ≤ cL * v' * g')
    (hM : ‖M - (v : ℂ)‖ ≤ F * v * g) (hsm : F * g ≤ 1 / 2) :
    ‖G‖ ≤ 2 * (1 + F' + cL) * ‖M‖ := by
  have hv : 0 ≤ v := hv'.trans hvv
  have hvM : v ≤ 2 * ‖M‖ := by
    have hvn : ‖(v : ℂ)‖ = v := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    have t := norm_le_norm_add_norm_sub' (v : ℂ) M
    rw [hvn, norm_sub_rev] at t
    have : F * v * g ≤ v / 2 := by
      have := mul_le_mul_of_nonneg_right hsm hv
      nlinarith
    linarith
  have hMpn : ‖Mp‖ ≤ v' + F' * v' * g' := by
    have hvn : ‖(v' : ℂ)‖ = v' := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv']
    have t := norm_le_insert' Mp (v' : ℂ)
    rw [hvn] at t; linarith
  have hG : ‖G‖ ≤ ‖U‖ + ‖G - U‖ := norm_le_insert' G U
  have hUn : ‖U‖ = ‖Mp‖ := by rw [hU]
  have h1 : F' * v' * g' ≤ F' * v' := mul_le_of_le_one_right (mul_nonneg hF' hv') hg'1
  have h2 : cL * v' * g' ≤ cL * v' := mul_le_of_le_one_right (mul_nonneg hcL hv') hg'1
  have h3 : (1 + F' + cL) * v' ≤ (1 + F' + cL) * v :=
    mul_le_mul_of_nonneg_left hvv (by linarith)
  have h4 : (1 + F' + cL) * v ≤ (1 + F' + cL) * (2 * ‖M‖) :=
    mul_le_mul_of_nonneg_left hvM (by linarith)
  have e1 : (1 + F' + cL) * v' = v' + F' * v' + cL * v' := by ring
  have e2 : (1 + F' + cL) * (2 * ‖M‖) = 2 * (1 + F' + cL) * ‖M‖ := by ring
  linarith

/-- `ϑ_n ≤ ϑ_j` for `ǧ_j ≤ ǧ_n`. -/
theorem varthJ_anti {m b μ₀ : ℝ} (hb : 0 ≤ b) {j n : ℕ}
    (hj : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1)
    (hjn : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) :
    varthJ R m b μ₀ n ≤ varthJ R m b μ₀ j := by
  unfold varthJ
  exact Real.rpow_le_rpow (div_nonneg hb (hj.trans_le hjn).le)
    (div_le_div_of_nonneg_left hb hj hjn) (by norm_num)

set_option maxHeartbeats 1000000 in
/-- **`GamTopBd` along one trajectory.** -/
theorem gamTopBd_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ : ℝ} {f : ℝ → ℝ}
    (hMag : MagAt R Nh m b μ₀ f) (hm : 0 ≤ m) (hb : 0 < b)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hgm : ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1)
    (ha : ∀ k < Nh, zA L m k ≤ 2)
    {lam : ℕ → ℂ} {Kl Kp ce cw cL : ℝ} (hKl : 0 ≤ Kl) (hKp : 0 ≤ Kp) (hce : 0 ≤ ce)
    (hcw : 0 ≤ cw) (hcL : 0 ≤ cL) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (f Kl) 0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2)
    (hpair : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hB : GamBulkRel R Nh m b μ₀ ce) (hW : GamWKTop R Nh m b μ₀ cw)
    (hLast : GamLastRel R Nh m b μ₀ cL) :
    GamTopBd R Nh m b μ₀ lam
      (2 * (1 + max (f (Kp + (ce + cw) * (1 + 3 * Kp))) 0 + cL)) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set cγ := (ce + cw) * (1 + 3 * Kp) with hcγd
  have hcγ : 0 ≤ cγ := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hNh : 1 ≤ Nh := h1.trans hj
  have hrem := gamRemX_top_le R hb hKp hce hcw hV
    (fun k hk => ⟨(hg k hk.le).1.le, (hg k hk.le).2⟩)
    (fun k hk => ⟨zA_nonneg L hm k, ha k hk⟩) (hpair x hx) hB (hW x hx h1 hj)
  have hθa : ∀ k < Nh, 0 ≤ thJ R m b μ₀ k *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := fun k hk =>
    mul_nonneg (Real.rpow_nonneg (div_pos (hg k hk.le).1 hb).le _)
      (add_nonneg (hg k hk.le).1.le (zA_nonneg L hm k))
  have hlG := hLam_lamG R hb hcγ (hpair x hx) hθa hrem
  have h0 : ∀ k < Nh, gamT R m b μ₀ k = 0 → gamRemX R m b μ₀ x k = 0 := by
    intro k hk hΓ
    have := hrem k hk
    rw [hΓ, norm_zero, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hU := uA_eq_mmag R hP hb.ne' x hNh h0
  have hKp' : 0 ≤ Kp + cγ := add_nonneg hKp hcγ
  have hM' := hMag (lamG R m b μ₀ x) (Kp + cγ) hKp' hlG Nh le_rfl
  have hM := hMag lam Kl hKl hl j hj
  have hlast := hLast x hx h1 hj
  have hGU : ‖gamNa R Nh m b μ₀ x - uA R m b μ₀ x Nh‖ ≤
      cL * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    rw [gamNa_sub_uA R hP hNh]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]; exact hlast
  have hmono : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    have key : ∀ n, j + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (j + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hgm (j + n) (by omega))
    have := key (Nh - j) (by omega)
    rwa [show j + (Nh - j) = Nh by omega] at this
  have hvv := varthJ_anti R hb.le (hg j hj).1 hmono
  have hv' : 0 ≤ varthJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hb (hg Nh le_rfl).1).le _
  set F' := max (f (Kp + cγ)) 0
  set F := max (f Kl) 0
  have hM'' : ‖Mmag R m b μ₀ (lamG R m b μ₀ x) Nh - ((varthJ R m b μ₀ Nh : ℝ) : ℂ)‖ ≤
      F' * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 :=
    hM'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv')
      (hg Nh le_rfl).1.le)
  have hvj : 0 ≤ varthJ R m b μ₀ j := hv'.trans hvv
  have hMj : ‖Mmag R m b μ₀ lam j - ((varthJ R m b μ₀ j : ℝ) : ℂ)‖ ≤
      F * varthJ R m b μ₀ j * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 :=
    hM.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hvj)
      (hg j hj).1.le)
  exact gamTop_pure hv' hvv (hg Nh le_rfl).1.le (hg Nh le_rfl).2 (hg j hj).1.le
    (le_max_right _ _) (le_max_right _ _) hcL hU hM'' hGU hMj (hsmall j hj)

end Traj

/-! ### Along the admissible trajectories -/

/-- **`ǧ` is nondecreasing along every admissible trajectory** (below `N_h`). -/
def GMonoConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1

/-- `GMonoConcl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def GMonoConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1

theorem GMonoConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε : ℝ}
    (h : GMonoConclD L ℓ A ρ κ cm cT ε) : GMonoConcl L ℓ A ρ κ cm cT ε := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1


/-- `GMonoConcl` from the band (F1) of the master construction (`BandF1`, `cg·ε ≤ 1/6`). -/
theorem gMonoConcl_ofD {L : ℕ} [NeZero L] (hL8 : 8 ≤ L) {ℓ A ρ κ cg cm cT ε : ℝ} (hcg : 0 ≤ cg)
    (hF1 : ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
      cg * ε ≤ 1 / 6 ∧ BandF1 (R.withMsq m) Nh κ cg cm cT ε) :
    GMonoConclD L ℓ A ρ κ cm cT ε := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD k hk
  obtain ⟨h6, hB⟩ := hF1 N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have ht := inDh_rg_of_D (R.withMsq m) hB hD Nh le_rfl
  have hr := ht.2 k hk
  obtain ⟨hg, hgε, -, -⟩ := ht.1 k hk.le
  have hβ2 := betaL_ge hL8
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1
  set g' := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1
  have hr' : |g' - g - betaL L * g ^ 2| ≤ 1 / 2 * betaL L * g ^ 2 + cg * g ^ 3 := hr
  have h3 : cg * g ^ 3 ≤ 1 / 6 * g ^ 2 := by
    have : cg * g ≤ cg * ε := mul_le_mul_of_nonneg_left hgε hcg
    have e : cg * g ^ 3 = (cg * g) * g ^ 2 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right (this.trans h6) (sq_nonneg _)
  have h4 : 1 / 6 * g ^ 2 ≤ 1 / 4 * betaL L * g ^ 2 := by
    have := sq_nonneg g
    nlinarith
  have h5 := neg_abs_le (g' - g - betaL L * g ^ 2)
  have h6' : 0 ≤ betaL L * g ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- Corollary of `gMonoConcl_ofD`. -/
theorem gMonoConcl_of {L : ℕ} [NeZero L] (hL8 : 8 ≤ L) {ℓ A ρ κ cg cm cT ε : ℝ} (hcg : 0 ≤ cg)
    (hF1 : ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
      cg * ε ≤ 1 / 6 ∧ BandF1 (R.withMsq m) Nh κ cg cm cT ε) :
    GMonoConcl L ℓ A ρ κ cm cT ε :=
  (gMonoConcl_ofD hL8 hcg hF1).adm


set_option maxHeartbeats 1000000 in
/-- **`GamTopBd` along the admissible trajectories** (`FlowC2Concl`, `ε ≤ 1`, `MagConcl`,
`GMonoConcl`): (H_λ) for `λ` and for the pair vertex, `GamBulkRel`, `GamWKTop`, `GamLastRel` and
the smallness `K(K_λ)ǧ_j ≤ 1/2` give `GamTopBd` with `K₄ = 2(1 + K(K_p + c_γ) + c_L)`,
`c_γ = (c_e + c_w)(1 + 3K_p)`. -/
theorem gamTopBd_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hMC : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hGM : GMonoConcl L ℓ A ρ κ cm cT ε) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl Kp ce cw cL : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ ce → 0 ≤ cw → 0 ≤ cL →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      GamBulkRel R Nh m b μ₀ ce → GamWKTop R Nh m b μ₀ cw → GamLastRel R Nh m b μ₀ cL →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      GamTopBd R Nh m b μ₀ lam
        (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 + cL)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl Kp ce cw cL hKl hKp hce hcw
    hcL hl hpair hB hW hLast hsmall
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1, ((hadm.1 k hk).2.1).trans hε1⟩
  have ha : ∀ k < Nh, zA L m k ≤ 2 := fun k hk =>
    zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)
  have hMag := magAt_of R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hadm
  exact gamTopBd_of R hP hMag hm.1.le hb hval hg
    (hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm) ha hKl hKp hce hcw hcL hl hsmall
    hpair hB hW hLast

end

end Spin2
