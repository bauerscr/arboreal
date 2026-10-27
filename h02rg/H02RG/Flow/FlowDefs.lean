import Flow.RGSystem

/-!
# The finite volume renormalisation group flow and its identification with the dynamical system

* `covAt N msq j`: the covariance of the `(j+1)`-st renormalisation group step on `Λ_N`:
  `C_{j+1}` (`Cfrd`) for `j + 1 < N` and `C_N` (`CfrdN`) for the last step `j + 1 = N`.
* `flowN N msq V₀ j = (V_j, K_j)`: the flow on the torus `Λ_N` started at `(V₀, K₀ = 0)`,
  `(V_{j+1}, K_{j+1}) = ((u, V)_{j+1}(V_j, K_j).2, K_{j+1}(V_j, K_j))` (the activity restricted to
  connected `(j+1)`-polymers, the normalised form of an element of `𝒦_{j+1}`), and `uflow N msq V₀ j
  = u_{j+1}`.
* `InK_flowN`: the activities `K_j` of the flow are in `𝒦_j` for `j < N` (given `GoodCov`).
* `flowN_orbit`: along an orbit of `RGsys` staying in the ball of radius `r`, the torus flows are
  given by the orbit: `V_j = V(v_j, b̂_j)` and `K_j = K_j^N` for `j + 3 ≤ N`.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Metric Filter Topology Coup

variable {d L : ℕ} [NeZero L]

variable (d L) in
/-- The covariance of the `(j+1)`-st step on `Λ_N`. -/
def covAt : (N : ℕ) → ℝ → ℕ → Matrix (Lam d L N) (Lam d L N) ℝ
  | 0, _, _ => 0
  | M + 1, msq, j => if j + 1 < M + 1 then Cfrd d L (M + 1) msq j else CfrdN d L M msq

theorem covAt_lt {N j : ℕ} (hj : j + 1 < N) (msq : ℝ) : covAt d L N msq j = Cfrd d L N msq j := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp [covAt, hj]

theorem covAt_last (M : ℕ) (msq : ℝ) : covAt d L (M + 1) msq M = CfrdN d L M msq := by
  simp [covAt]

variable (d L) in
/-- **The finite volume flow** `(V_j, K_j)` on `Λ_N` started at `(V₀, 0)`. -/
def flowN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : ℕ → Vcoup × Act d L N
  | 0 => (V₀, 0)
  | j + 1 => ((uVnext j (covAt d L N msq j) (flowN N msq V₀ j).1 (flowN N msq V₀ j).2).2,
      restr (j + 1) (Knext j (covAt d L N msq j) (flowN N msq V₀ j).1 (flowN N msq V₀ j).2))

variable (d L) in
/-- The constant `u_{j+1}` produced by the `(j+1)`-st step of the flow on `Λ_N`. -/
def uflow (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (j : ℕ) : ℂ :=
  (uVnext j (covAt d L N msq j) (flowN d L N msq V₀ j).1 (flowN d L N msq V₀ j).2).1

theorem flowN_zero (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : flowN d L N msq V₀ 0 = (V₀, 0) := rfl

theorem flowN_succ (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (j : ℕ) :
    flowN d L N msq V₀ (j + 1) =
      ((uVnext j (covAt d L N msq j) (flowN d L N msq V₀ j).1 (flowN d L N msq V₀ j).2).2,
        restr (j + 1) (Knext j (covAt d L N msq j) (flowN d L N msq V₀ j).1
          (flowN d L N msq V₀ j).2)) := rfl

/-- The activities of the flow are in `𝒦_j` for `j < N`. -/
theorem InK_flowN (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} {msq ℓ₀ : ℝ}
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    ∀ j < N, InK j (flowN d L N msq V₀ j).2 := by
  intro j
  induction j with
  | zero => intro _; exact InK.zero 0
  | succ j ih =>
    intro hj
    rw [flowN_succ]
    exact (restr_mem (by omega) (InK_Knext hd hL hj (hgood j (by omega)) _ (ih (by omega)))).1

/-! ### Identification with the dynamical system -/

variable {ℓ₀ A ε C₁ δK Kc Cw : ℝ} [Fact (0 < ℓ₀)] [Fact (0 < A)]

section
variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw)
include H

theorem RGsys_orbit_succ (m : ℝ) (v₀ : Vsp) (w₀ : WS d L ℓ₀ A 0) (j : ℕ)
    (_hr : ‖(RGsys H m).orbit v₀ w₀ j‖ ≤ rad d ℓ₀ ε) :
    (RGsys H m).orbit v₀ w₀ (j + 1) =
      (Emap L ((RGsys H m).orbit v₀ w₀ j).1 + BNf ℓ₀ A m j (j + 3)
          (((RGsys H m).orbit v₀ w₀ j).2.1, KFam.proj ⟨j + 3, le_rfl⟩ ((RGsys H m).orbit v₀ w₀ j).2.2),
        (bfac d L * ((RGsys H m).orbit v₀ w₀ j).2.1, FF H m j ((RGsys H m).orbit v₀ w₀ j))) := by
  rw [System.orbit_succ]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show bfac d L * _ + 0 = _
    rw [add_zero]; rfl
  · change DF H m j ((RGsys H m).orbit v₀ w₀ j).2.2 + (FF H m j ((RGsys H m).orbit v₀ w₀ j) -
      DF H m j ((RGsys H m).orbit v₀ w₀ j).2.2) = _
    abel

/-- **The torus flows are given by the orbit of the dynamical system** (as long as it stays in
the ball of radius `r`): for `j + 3 ≤ N`, `V_j = V(v_j, b̂_j)` and `K_j = K_j^N`. -/
theorem flowN_orbit {msq : ℝ} (hmsq : 0 ≤ msq) (v₀ : Vsp) (b₀ : ℂ)
    (hr : ∀ j, ‖(RGsys H msq).orbit v₀ (b₀, 0) j‖ ≤ rad d ℓ₀ ε) :
    ∀ j N (hN : j + 3 ≤ N),
      (flowN d L N msq (VresL d L 0 (v₀, b₀)) j).1 =
          VresL d L j (((RGsys H msq).orbit v₀ (b₀, 0) j).1,
            ((RGsys H msq).orbit v₀ (b₀, 0) j).2.1) ∧
        (flowN d L N msq (VresL d L 0 (v₀, b₀)) j).2 =
          ((RGsys H msq).orbit v₀ (b₀, 0) j).2.2.act ⟨N, hN⟩ := by
  set o := (RGsys H msq).orbit v₀ (b₀, 0) with ho
  have hC : ∀ N j, Cm d L N msq j = Cfrd d L N msq j := fun N j => by
    rw [Cm, max_eq_left hmsq]
  intro j
  induction j with
  | zero =>
    intro N hN
    refine ⟨rfl, ?_⟩
    rw [flowN_zero]
    show (0 : Act d L N) = (0 : KFam d L 0 3 (ellj d (L : ℝ) ℓ₀ 0) A).act ⟨N, hN⟩
    rw [KFam.act_zero]
  | succ j ih =>
    intro N hN
    obtain ⟨ihV, ihK⟩ := ih N (by omega)
    have hj : j + 1 < N := by omega
    set x := o j with hx
    have hxN : xN ⟨N, by omega⟩ x = ((x.1, x.2.1, KFam.proj ⟨N, by omega⟩ x.2.2) :
        XS d L j N ℓ₀ A) := rfl
    have hKN : (KFam.proj (⟨N, by omega⟩ : Idx j 3) x.2.2).toAct = x.2.2.act ⟨N, by omega⟩ := rfl
    rw [flowN_succ, covAt_lt hj, ihV, ihK, ho, RGsys_orbit_succ H msq v₀ (b₀, 0) j (hr j), ← ho]
    refine ⟨?_, ?_⟩
    · -- the coupling constants
      have hstep := uVnext_step H hj msq (xN ⟨N, by omega⟩ x)
      have hb := uVnext_step_b H hj msq (xN ⟨N, by omega⟩ x)
      rw [hxN, hC] at hstep hb
      simp only at hstep hb
      rw [hKN] at hstep hb
      have hcomp := BNf_compat H (le_refl (j + 3)) (by omega : j + 3 ≤ N) msq x.2.1
        (KFam.proj ⟨j + 3, le_rfl⟩ x.2.2) (KFam.proj ⟨N, by omega⟩ x.2.2)
        (KFam.compat x.2.2 (N := ⟨j + 3, le_rfl⟩) (M := ⟨N, by omega⟩) (by simp; omega))
      rw [hcomp, ← hstep, bfac]
      exact (VresL_vresL H (j + 1) _ _ hb).symm
    · -- the activities
      have hp := proj_FF H msq (hr j) ⟨N, hN⟩
      show restr (j + 1) (Knext j (Cfrd d L N msq j) (VresL d L j (x.1, x.2.1))
        (KFam.proj ⟨N, by omega⟩ x.2.2).toAct) = (FF H msq j x).act ⟨N, hN⟩
      rw [KFam.act_def, hp, FN_toAct H hj, hC]
      rfl

/-- The coupling constants `V_{j+1}` are given by the orbit for `j + 3 ≤ N` (i.e. up to
`j + 1 = N - 2`). -/
theorem flowN_orbit_V_succ {msq : ℝ} (hmsq : 0 ≤ msq) (v₀ : Vsp) (b₀ : ℂ)
    (hr : ∀ j, ‖(RGsys H msq).orbit v₀ (b₀, 0) j‖ ≤ rad d ℓ₀ ε) (j N : ℕ) (hN : j + 3 ≤ N) :
    (flowN d L N msq (VresL d L 0 (v₀, b₀)) (j + 1)).1 =
      VresL d L (j + 1) (((RGsys H msq).orbit v₀ (b₀, 0) (j + 1)).1,
        ((RGsys H msq).orbit v₀ (b₀, 0) (j + 1)).2.1) := by
  set o := (RGsys H msq).orbit v₀ (b₀, 0) with ho
  have hC : ∀ N j, Cm d L N msq j = Cfrd d L N msq j := fun N j => by
    rw [Cm, max_eq_left hmsq]
  obtain ⟨ihV, ihK⟩ := flowN_orbit H hmsq v₀ b₀ hr j N hN
  have hj : j + 1 < N := by omega
  set x := o j with hx
  have hxN : xN ⟨N, hN⟩ x = ((x.1, x.2.1, KFam.proj ⟨N, hN⟩ x.2.2) : XS d L j N ℓ₀ A) := rfl
  have hKN : (KFam.proj (⟨N, hN⟩ : Idx j 3) x.2.2).toAct = x.2.2.act ⟨N, hN⟩ := rfl
  rw [flowN_succ, covAt_lt hj, ihV, ihK, ho, RGsys_orbit_succ H msq v₀ (b₀, 0) j (hr j), ← ho]
  have hstep := uVnext_step H hj msq (xN ⟨N, hN⟩ x)
  have hb := uVnext_step_b H hj msq (xN ⟨N, hN⟩ x)
  rw [hxN, hC] at hstep hb
  simp only at hstep hb
  rw [hKN] at hstep hb
  have hcomp := BNf_compat H (le_refl (j + 3)) hN msq x.2.1
    (KFam.proj ⟨j + 3, le_rfl⟩ x.2.2) (KFam.proj ⟨N, hN⟩ x.2.2)
    (KFam.compat x.2.2 (N := ⟨j + 3, le_rfl⟩) (M := ⟨N, hN⟩) (by simp; omega))
  rw [hcomp, ← hstep, bfac]
  exact (VresL_vresL H (j + 1) _ _ hb).symm

/-- The constants `u_{j+1}` do not depend on the torus for `j + 3 ≤ N`. -/
theorem uflow_indep {msq : ℝ} (hmsq : 0 ≤ msq) (v₀ : Vsp) (b₀ : ℂ)
    (hr : ∀ j, ‖(RGsys H msq).orbit v₀ (b₀, 0) j‖ ≤ rad d ℓ₀ ε) {j N M : ℕ} (hN : j + 3 ≤ N)
    (hNM : N ≤ M) :
    uflow d L N msq (VresL d L 0 (v₀, b₀)) j = uflow d L M msq (VresL d L 0 (v₀, b₀)) j := by
  obtain ⟨hVN, hKN⟩ := flowN_orbit H hmsq v₀ b₀ hr j N hN
  obtain ⟨hVM, hKM⟩ := flowN_orbit H hmsq v₀ b₀ hr j M (by omega)
  unfold uflow
  rw [covAt_lt (by omega), covAt_lt (by omega), hVN, hKN, hVM, hKM,
    uVnext_compat H.hd H.hL8 hNM hN hmsq _ (KFam.inK _ _) (KFam.inK _ _)
      (KFam.compat _ (N := ⟨N, hN⟩) (M := ⟨M, by omega⟩) hNM)]

end

end

end Flow
