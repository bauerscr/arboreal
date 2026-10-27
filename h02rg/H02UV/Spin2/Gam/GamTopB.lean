import Spin2.Gam.GamLast
import Spin2.Gam.GamFormB

/-!
# `GamTopBd` at the second point: `‖γ_{b,N}‖ ≤ K‖M_{j_x}‖`, and both points together

**The mirror of the last step.** `zUNS`, `gamRemNS`: the last-step increment and remainder of the
mirrored pair history (points `ptsS x = (x, 0)`). The projection `prjO` commutes with the last step
exactly as with the bulk steps (`Obs2.prj_uXO`, `prj_fullV/W/K`, `prj_obsHist`), so
`prjO false (zUN) = prjO true (zUNS)` (**`prjO_zUN`**), hence `ε(zUN)_b = ε(zUNS)_a`
(**`eps_zUN_b`**) and, with `uB_eq_uMir`, `γ_{b,N} = γ^{mir}_{a,N}` (**`gamNb_eq_mir`**). The proof of
`gamNa_eq` then applies at `a = x` (`stCovN(x,x) = stCovN(0,0)`, `stCovN_diag`): **`gamNb_eq`**,
**`gamNb_sub_uMir`**.

**Named inputs (mirror).**
* **`GamRemTopS c_γ`**: `‖ρ^{mir}_k‖ ≤ c_γθ_k(ǧ_k + a_k)b‖Γ_k‖` for all `k < N_h` — the conclusion of
  `gamRemX_top_le` for the mirrored flow (`GamRemRelS` extended from `k < j_x` to `k < N_h`).
  It is not split into `GamBulkRel`/`GamWKTop` here: the mirrored bulk factor is
  `ε(F_C(ψ̄_xψ_x, V_{κ'}(Λ)))`, equal to `gamBulkT` by translation invariance, which is not
  formalised.
* **`BetaLastS`**, **`GamLastRemS`**: `BetaLast`, `GamLastRem` for the mirrored flow; they give
  **`GamLastRelS`** (`gamLastRelS_of`, `gamLastRelS_flow`) as in `Spin2/Gam/GamLast.lean`.

**Results.** **`gamTopBdB_of`**, **`gamTopBdB_flow`**: `GamTopBdB` (`‖γ_{b,N}‖ ≤ K₄‖M_{j_x}‖`) with
`K₄ = 2(1 + K(K_p + c_γ) + c_L)`. **`gamTopBd_both_flow`**: `GamTopBd ∧ GamTopBdB` along the
admissible trajectories from (H_λ) for `λ` and both pair vertices, `GamBulkRel`, `GamWKTop`,
`GamRemTopS`, `BetaLast(S)`, `GamLastRem(S)` and the smallness, with
`c_L = 2(1 + c_r)K_β·ℓ²e^{K_Z}/14`. **`thm_gamTopBd_master`**: the same with the master constants
(`thm_gamTop_master`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The last-step increment `u_N - u_{N-1}` of the mirrored pair history (points `(x, 0)`). -/
def zUNS (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : Obs.OE .two (Lam 2 L N) :=
  Obs2.uXO (ptsS x) (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
      (Obs2.obsHist (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullK (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
      (Obs2.obsHist (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    univ

/-- `ρ^{mir}_N`: the remainder of the last step of the mirrored `γ` flow. -/
def gamRemNS (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : ℂ :=
  Obs2.gamRemG (ptsS x) (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
      (Obs2.obsHist (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullK (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
      (Obs2.obsHist (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))

/-- **The mirror of the last step**: `prjO false (zUN) = prjO true (zUNS)`. -/
theorem prjO_zUN (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    Obs2.prjO false (zUN R Nh m b μ₀ x) = Obs2.prjO true (zUNS R Nh m b μ₀ x) := by
  unfold zUN zUNS
  rw [Obs2.prj_uXO false (P := ptsX x) (P' := ptsS x) rfl,
    Obs2.prj_uXO true (P := ptsS x) (P' := ptsS x) rfl,
    Obs2.prj_fullV, Obs2.prj_fullW, Obs2.prj_fullK, Obs2.prj_fullV, Obs2.prj_fullW,
    Obs2.prj_fullK, Obs2.prj_obsHist _ false (P := ptsX x) (P' := ptsS x) rfl,
    Obs2.prj_obsHist _ true (P := ptsS x) (P' := ptsS x) rfl,
    Obs2.prjSt_obsInit_swap (zV b) rfl rfl (P := ptsX x) (P' := ptsS x) rfl]

/-- `ε(zUN)_b = ε(zUNS)_a`. -/
theorem eps_zUN_b (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    ε (zUN R Nh m b μ₀ x : SA .two (Lam 2 L N)).b = ε (zUNS R Nh m b μ₀ x : SA .two (Lam 2 L N)).a := by
  have h := congrArg (fun F : Obs.OE .two (Lam 2 L N) => ε (F : SA .two (Lam 2 L N)).a)
    (prjO_zUN R Nh m b μ₀ x)
  simp only [Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_true, Obs2.cmp_false] at h
  exact h

/-- **`γ_{b,N} = γ^{mir}_{a,N}`**. -/
theorem gamNb_eq_mir (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    gamNb R Nh m b μ₀ x =
      uMir R m b μ₀ x (Nh + 1) - ε (zUNS R Nh m b μ₀ x : SA .two (Lam 2 L N)).a := by
  unfold gamNb; rw [uB_eq_uMir, eps_zUN_b]

/-- Translation invariance of the last covariance on the diagonal. -/
theorem stCovN_diag (R' : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (x : Lam 2 L N) :
    LastN.stCovN R' j st x x = LastN.stCovN R' j st 0 0 := by
  unfold LastN.stCovN LastN.lastCov
  simp [DressedFRD.kmat]

/-- **The last mirrored `γ` step** (exact): `γ_{b,N} = γ^{mir}_{N-1} - β^{mir}_{N-1}C_N(0,0) + ρ^{mir}_N`. -/
theorem gamNb_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    gamNb R Nh m b μ₀ x = uMir R m b μ₀ x (Nh + 1) -
      btMir R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ + gamRemNS R Nh m b μ₀ x := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  set o₀ := Obs2.obsInit .two (zV b) (ptsS x)
  have hVa : ∀ c, (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
      (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsS x) o₀ (Nh + 1) t) c : SA .two (Lam 2 L N)).a =
      (Obs2.histVO2 (R.withMsq m) (ptsS x) o₀ t (Nh + 1) c : SA .two (Lam 2 L N)).a := by
    intro c
    rw [Obs2.histVO2_a]
    exact Obs2.emb_add_cmp true _ _
  have hform := Obs2.obsHist_hform2 (R.withMsq m) (ptsS x) o₀ t
    (fun b' => Obs2.obsInit_two_form _ _ b') (Nh + 1)
  have h := Obs2.eps_uXO_univ_a (ptsS x) (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
      (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsS x) o₀ (Nh + 1) t))
    (Obs2.fullW (histOut (R.withMsq m) Nh t).st (histOut (R.withMsq m) Nh t).D
      (Obs2.obsHist (R.withMsq m) (ptsS x) o₀ (Nh + 1) t))
    (Obs2.fullK (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
      (histOut (R.withMsq m) Nh t).K (Obs2.obsHist (R.withMsq m) (ptsS x) o₀ (Nh + 1) t))
    (fun c => by rw [hVa]; exact hform c)
  have hε : ∑ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ε (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
        (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
        (Obs2.obsHist (R.withMsq m) (ptsS x) o₀ (Nh + 1) t) c : SA .two (Lam 2 L N)).a = 0 := by
    have := Obs2.epsTot2_succ (R.withMsq m) (ptsS x) o₀ t Nh
    unfold Obs2.epsTot2 at this
    rw [← this]
    exact sum_congr rfl fun c _ => by rw [hVa]
  have hβ : Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
      (Obs2.fullV (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st
        (histOut (R.withMsq m) Nh t).g.re (histOut (R.withMsq m) Nh t).nu.re
        (Obs2.obsHist (R.withMsq m) (ptsS x) o₀ (Nh + 1) t)) = btMir R m b μ₀ x (Nh + 1) := by
    unfold btMir bt2 Obs2.betaTot2
    exact sum_congr rfl fun c _ => by rw [hVa]; rfl
  rw [hε, hβ, zero_add, show (ptsS x).a = x from rfl, stCovN_diag] at h
  have h' : ε (zUNS R Nh m b μ₀ x : SA .two (Lam 2 L N)).a =
      btMir R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ - gamRemNS R Nh m b μ₀ x := h
  rw [gamNb_eq_mir, h']
  ring

/-- The mirrored `γ` step above scale `0`: `γ^{mir}_{k+1} = γ^{mir}_k - (β^{mir}_kΓ_k - ρ^{mir}_k)`. -/
theorem uMir_succ_pos (hP : R.P = Pc) (m b μ₀ : ℝ) (x : Lam 2 L N) {k : ℕ} (hk : 1 ≤ k) :
    uMir R m b μ₀ x (k + 1) = uMir R m b μ₀ x k -
      (btMir R m b μ₀ x k * gamT R m b μ₀ k - gamRemMir R m b μ₀ x k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [uMir_succ R hP, Obs2.epsTot2_succ]; ring

/-- **The two mirrored steps above `N_h`.** -/
theorem gamNb_sub_uMir (hP : R.P = Pc) {Nh : ℕ} (hNh : 1 ≤ Nh) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    gamNb R Nh m b μ₀ x - uMir R m b μ₀ x Nh =
      -(btMir R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemMir R m b μ₀ x Nh) -
        (btMir R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ - gamRemNS R Nh m b μ₀ x) := by
  rw [gamNb_eq, uMir_succ_pos R hP m b μ₀ x hNh]; ring

/-! ### Named inputs (mirror) -/

/-- **Named input (mirror, all scales below `N_h`)**: the conclusion of `gamRemX_top_le` for the
mirrored flow, `‖ρ^{mir}_k‖ ≤ c_γθ_k(ǧ_k + a_k)b‖Γ_k‖` for every `k < N_h`. -/
def GamRemTopS (Nh : ℕ) (m b μ₀ cγ : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ k < Nh, ‖gamRemMir R m b μ₀ x k‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) *
        (b * ‖gamT R m b μ₀ k‖)

/-- **`GamLastRel` for the mirrored flow.** -/
def GamLastRelS (Nh : ℕ) (m b μ₀ cL : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖btMir R m b μ₀ x Nh * gamT R m b μ₀ Nh - gamRemMir R m b μ₀ x Nh‖ +
        ‖btMir R m b μ₀ x (Nh + 1) * zCovN R Nh m b μ₀ - gamRemNS R Nh m b μ₀ x‖ ≤
      cL * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1

/-- **Named input (mirror of `BetaLast`).** -/
def BetaLastS (Nh : ℕ) (m b μ₀ Kβ : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖btMir R m b μ₀ x Nh‖ ≤ Kβ * b * thJ R m b μ₀ Nh ∧
      ‖btMir R m b μ₀ x (Nh + 1)‖ ≤ Kβ * b * thJ R m b μ₀ Nh

/-- **Named input (mirror of `GamLastRem`).** -/
def GamLastRemS (Nh : ℕ) (m b μ₀ cr : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖gamRemMir R m b μ₀ x Nh‖ ≤ cr * ‖btMir R m b μ₀ x Nh‖ * ‖gamT R m b μ₀ Nh‖ ∧
      ‖gamRemNS R Nh m b μ₀ x‖ ≤ cr * ‖btMir R m b μ₀ x (Nh + 1)‖ * ‖zCovN R Nh m b μ₀‖

/-- **`GamLastRelS` along one trajectory** (as `gamLastRel_of`). -/
theorem gamLastRelS_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ KZ Kβ cr : ℝ} (hb : 0 < b)
    (hKZ : 0 ≤ KZ) (hKβ : 0 ≤ Kβ) (hcr : 0 ≤ cr)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1))
    (hg : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hZ0 : (rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0)
    (hZ : |Real.log ‖(rawHist (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
      1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 / b)| ≤
      KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hβ : BetaLastS R Nh m b μ₀ Kβ) (hr : GamLastRemS R Nh m b μ₀ cr) :
    GamLastRelS R Nh m b μ₀ (2 * (1 + cr) * Kβ * (R.ℓ ^ 2 * Real.exp KZ / 14)) := by
  intro x hx h1 hj
  obtain ⟨hΓ, hC⟩ := gamT_zCovN_le R hP hb hKZ hV hVL hVN hg hg1 hZ0 hZ
  obtain ⟨hβ0, hβ1⟩ := hβ x hx h1 hj
  obtain ⟨hr0, hr1⟩ := hr x hx h1 hj
  have hθ : 0 ≤ thJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hg hb).le _
  have hKC : 0 ≤ R.ℓ ^ 2 * Real.exp KZ / 14 := by positivity
  have h := gamLast_pure hKβ hKC hcr (mul_nonneg hb.le hθ) hθ
    (by rw [← mul_assoc]; exact hβ0) (by rw [← mul_assoc]; exact hβ1) hΓ hC hr0 hr1
  have e : b * thJ R m b μ₀ Nh * thJ R m b μ₀ Nh =
      varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    rw [mul_assoc, ← sq]; exact b_thJ_sq hg hb
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- (H_λ) for `λ^{γ,mir}` on all of `k < N_h`. -/
theorem hLam_lamGMir {Nh : ℕ} {m b μ₀ Kp cγ : ℝ} (hb : 0 < b) (hcγ : 0 ≤ cγ) {x : Lam 2 L N}
    (hl : HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp)
    (hθa : ∀ k < Nh, 0 ≤ thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hrem : ∀ k < Nh, ‖gamRemMir R m b μ₀ x k‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) *
        (b * ‖gamT R m b μ₀ k‖)) :
    HLam R Nh m b μ₀ (lamGMir R m b μ₀ x) (Kp + cγ) := by
  intro k hkN
  have hlh : lamHat2 R (ptsS x) (zV b) m b μ₀ k = btMir R m b μ₀ x k / b := by
    unfold lamHat2
    rw [show bt2 R (ptsS x) (zV b) m b μ₀ 0 = btMir R m b μ₀ x 0 from rfl, btMir_zero]
    rfl
  have h1 := hl k hkN
  rw [hlh] at h1
  have e : lamGMir R m b μ₀ x k - ((thJ R m b μ₀ k : ℝ) : ℂ) =
      (btMir R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)) -
        gamRemMir R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k) := by unfold lamGMir; ring
  have h2 : ‖gamRemMir R m b μ₀ x k / ((b : ℂ) * gamT R m b μ₀ k)‖ ≤
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by
    by_cases hΓ : gamT R m b μ₀ k = 0
    · rw [hΓ, mul_zero, div_zero, norm_zero, mul_assoc]
      exact mul_nonneg hcγ (hθa k hkN)
    · have hd : 0 < b * ‖gamT R m b μ₀ k‖ := mul_pos hb (norm_pos_iff.2 hΓ)
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb,
        div_le_iff₀ hd]
      exact hrem k hkN
  show ‖lamGMir R m b μ₀ x k - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
    (Kp + cγ) * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1' : ‖btMir R m b μ₀ x k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
      Kp * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := h1
  have : (Kp + cγ) * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) =
      Kp * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) +
      cγ * thJ R m b μ₀ k * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by ring
  rw [this]
  exact add_le_add h1' h2

/-- **`GamTopBd` at the second point**: `‖γ_{b,N}‖ ≤ K₄‖M_{j_x}‖`. -/
def GamTopBdB (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (K4 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖gamNb R Nh m b μ₀ x‖ ≤ K4 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖

set_option maxHeartbeats 1000000 in
/-- **`GamTopBdB` along one trajectory** (mirror of `gamTopBd_of`). -/
theorem gamTopBdB_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ : ℝ} {f : ℝ → ℝ}
    (hMag : MagAt R Nh m b μ₀ f) (hm : 0 ≤ m) (hb : 0 < b)
    (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (hgm : ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1)
    {lam : ℕ → ℂ} {Kl Kp cγ cL : ℝ} (hKl : 0 ≤ Kl) (hKp : 0 ≤ Kp) (hcγ : 0 ≤ cγ)
    (hcL : 0 ≤ cL) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (f Kl) 0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2)
    (hpair : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp)
    (hrem : GamRemTopS R Nh m b μ₀ cγ) (hLast : GamLastRelS R Nh m b μ₀ cL) :
    GamTopBdB R Nh m b μ₀ lam (2 * (1 + max (f (Kp + cγ)) 0 + cL)) := by
  intro x hx h1 hj
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hNh : 1 ≤ Nh := h1.trans hj
  have hrem' := hrem x hx h1 hj
  have hθa : ∀ k < Nh, 0 ≤ thJ R m b μ₀ k *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := fun k hk =>
    mul_nonneg (Real.rpow_nonneg (div_pos (hg k hk.le).1 hb).le _)
      (add_nonneg (hg k hk.le).1.le (zA_nonneg L hm k))
  have hlG := hLam_lamGMir R hb hcγ (hpair x hx) hθa hrem'
  have h0 : ∀ k < Nh, gamT R m b μ₀ k = 0 → gamRemMir R m b μ₀ x k = 0 := by
    intro k hk hΓ
    have := hrem' k hk
    rw [hΓ, norm_zero, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hU := uMir_eq_mmag R hP hb.ne' x hNh h0
  have hKp' : 0 ≤ Kp + cγ := add_nonneg hKp hcγ
  have hM' := hMag (lamGMir R m b μ₀ x) (Kp + cγ) hKp' hlG Nh le_rfl
  have hM := hMag lam Kl hKl hl j hj
  have hlast := hLast x hx h1 hj
  have hGU : ‖gamNb R Nh m b μ₀ x - uMir R m b μ₀ x Nh‖ ≤
      cL * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    rw [gamNb_sub_uMir R hP hNh]
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
  have hM'' : ‖Mmag R m b μ₀ (lamGMir R m b μ₀ x) Nh - ((varthJ R m b μ₀ Nh : ℝ) : ℂ)‖ ≤
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

/-- **`GamLastRelS` along the admissible trajectories** (as `gamLastRel_flow`). -/
theorem gamLastRelS_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ)
    (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) (hLV : LastValidConcl L ℓ ρ) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ Kβ cr : ℝ, 0 ≤ Kβ → 0 ≤ cr → BetaLastS R Nh m b μ₀ Kβ → GamLastRemS R Nh m b μ₀ cr →
      GamLastRelS R Nh m b μ₀ (2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm Kβ cr hKβ hcr hβ hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
  obtain ⟨hV, hVL⟩ := (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hZ0, hZ⟩ :=
    (hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.2.2.1 m hm b μ₀ hadm Nh le_rfl
  have h := gamLastRelS_of R hP hb hKZ hKβ hcr hV hVL hVN (hadm.1 Nh le_rfl).1
    (((hadm.1 Nh le_rfl).2.1).trans hε1) hZ0 hZ hβ hr
  rwa [hRℓ] at h

set_option maxHeartbeats 1000000 in
/-- **`GamTopBdB` along the admissible trajectories** (`FlowC2Concl`, `ε ≤ 1`, `MagConcl`,
`GMonoConcl`): (H_λ) for `λ` and for the mirrored pair vertex, `GamRemTopS`, `GamLastRelS` and the
smallness give `GamTopBdB` with `K₄ = 2(1 + K(K_p + c_γ) + c_L)`. -/
theorem gamTopBdB_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ}
    (hε1 : ε ≤ 1) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hMC : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hGM : GMonoConcl L ℓ A ρ κ cm cT ε) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl Kp cγ cL : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ cγ → 0 ≤ cL →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp) →
      GamRemTopS R Nh m b μ₀ cγ → GamLastRelS R Nh m b μ₀ cL →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      GamTopBdB R Nh m b μ₀ lam (2 * (1 + max (spinMK L cg Ke KZ (Kp + cγ) KG 0) 0 + cL)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl Kp cγ cL hKl hKp hcγ hcL
    hl hpair hrem hLast hsmall
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1, ((hadm.1 k hk).2.1).trans hε1⟩
  have hMag := magAt_of R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hadm
  exact gamTopBdB_of R hP hMag hm.1.le hb hg
    (hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm) hKl hKp hcγ hcL hl hsmall
    hpair hrem hLast

set_option maxHeartbeats 1000000 in
/-- **`GamTopBd` at both points** along the admissible trajectories (`FlowC2Concl`, `ε ≤ 1`,
`SpinConcl`, `MagConcl`, `GMonoConcl`, `LastValidConcl`). Inputs: (H_λ) for `λ` and for both pair
vertices (`ptsX x`, `ptsS x`, constant `K_p`), `GamBulkRel c_e`, `GamWKTop c_w`, `GamRemTopS c_γ'`,
`BetaLast(S) K_β`, `GamLastRem(S) c_r`, and the smallness. Constants:
`c_L = 2(1 + c_r)K_β·ℓ²e^{K_Z}/14`, `K₄ = 2(1 + K(K_p + (c_e + c_w)(1 + 3K_p)) + c_L)`,
`K₄' = 2(1 + K(K_p + c_γ') + c_L)`. -/
theorem gamTopBd_both_flow {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMC : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) (hGM : GMonoConcl L ℓ A ρ κ cm cT ε)
    (hLV : LastValidConcl L ℓ ρ) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl Kp ce cw cγ Kβ cr : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ ce → 0 ≤ cw → 0 ≤ cγ →
      0 ≤ Kβ → 0 ≤ cr →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp) →
      GamBulkRel R Nh m b μ₀ ce → GamWKTop R Nh m b μ₀ cw → GamRemTopS R Nh m b μ₀ cγ →
      BetaLast R Nh m b μ₀ Kβ → GamLastRem R Nh m b μ₀ cr →
      BetaLastS R Nh m b μ₀ Kβ → GamLastRemS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      GamTopBd R Nh m b μ₀ lam
          (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 +
            2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14))) ∧
        GamTopBdB R Nh m b μ₀ lam
          (2 * (1 + max (spinMK L cg Ke KZ (Kp + cγ) KG 0) 0 +
            2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14))) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl Kp ce cw cγ Kβ cr hKl hKp
    hce hcw hcγ hKβ hcr hl hpX hpS hB hW hRS hβ hr hβS hrS hsmall
  have hcL : 0 ≤ 2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14) := by positivity
  exact ⟨gamTopBd_flow hF hε1 hL hMC hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam
      Kl Kp ce cw _ hKl hKp hce hcw hcL hl hpX hB hW
      (gamLastRel_flow hF hε1 hKZ hSp hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
        Kβ cr hKβ hcr hβ hr) hsmall,
    gamTopBdB_flow hε1 hL hMC hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam
      Kl Kp cγ _ hKl hKp hcγ hcL hl hpS hRS
      (gamLastRelS_flow hF hε1 hKZ hSp hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
        Kβ cr hKβ hcr hβS hrS) hsmall⟩

end

end Spin2
