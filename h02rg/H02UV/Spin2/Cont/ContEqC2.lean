import Spin2.Cont.ContEqC1

set_option autoImplicit false

/-!
# B3, `r`-dependent form, item (c): `nbGB ≤ (N_h − j_y + 1)·eqcK·R_l·bθ_{N_h}²`

* **`MasterFacts.eqc_bulk_le`**: the bulk summand `2M_i(1 + c_{GB}(ǧ + a))‖Γ‖ ≤ eqcKA·R_l·bθ_{N_h}²`;
* **`MasterFacts.eqc_top_le`**: the top summand `2M(‖Γ_{N_h}‖ + K_bǧ_{N_h}/|Z_{N_h+1}|)
  ≤ eqcKT·R_l·bθ_{N_h}²`;
* **`MasterFacts.eqc_nbGB_le`**: `nbGB ≤ (N_h − j_y + 1)·eqcK·R_l·bθ_{N_h}²`;
* **`MasterFacts.eqc_ctSig_rel`**: `σ ≤ e^{c'}e^{c}R_l|β_{a,N_h}|` (`σ = M_{N_h − ms}`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **The bulk summand of `nbGB`** (`ms ≤ k < N_h`). -/
theorem eqc_bulk_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (o' : Obs2.ObsSt .two L N) (h0 : o'.IsObs)
    {ms : ℕ} (hms0 : 0 < ms) (hmsN : ms < Nh) {M₀ Rl : ℝ} (hM0 : 0 ≤ M₀) (hRl : 0 ≤ Rl)
    (hrel : M₀ ≤ Rl * ‖bt2 R P (zV0 b) m b μ₀ ms‖) {k : ℕ} (hmk : ms ≤ k) (hk : k < Nh) :
    2 * ctEnv R m b μ₀ P ms o' M₀ (k - ms) * ((1 + M.core.cGB *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) * ‖gamT R m b μ₀ k‖) ≤
      M.eqcKA * (Rl * (b * thJ R m b μ₀ Nh ^ 2)) := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hGB : 0 ≤ M.core.cGB := M.core.consts_nonneg.2.2.2.2.2.2.2.2.1
  have hG := M.eqcG_nonneg
  have hKe := M.eqcKe_nonneg
  set T := thJ R m b μ₀ Nh with hTd
  have hT0 : 0 ≤ T := Real.rpow_nonneg (div_pos (hD Nh le_rfl).1 hb).le _
  have hθ := M.eqc_thJ_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := k) (n := Nh) hk.le le_rfl
  have hE := M.eqc_env_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o' h0 hms0 hmsN hRl hrel
    (i := k - ms) (by omega)
  rw [show ms + (k - ms) = k by omega] at hE
  have hE' : ctEnv R m b μ₀ P ms o' M₀ (k - ms) ≤ M.eqcKe * Rl * b * T :=
    hE.trans (mul_le_mul_of_nonneg_left hθ (by positivity))
  have hE0 : 0 ≤ ctEnv R m b μ₀ P ms o' M₀ (k - ms) :=
    mul_nonneg hM0 (prod_nonneg fun _ _ => norm_nonneg _)
  have hΓ := (M.eqc_gamT_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hk.le).trans
    (mul_le_mul_of_nonneg_left hθ (by positivity))
  -- `ǧ + a ≤ 3`
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  have hmn : m * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hz := zA_le_two (by linarith only [hL2]) hmn
  have hz0 := zA_nonneg L hm.1.le k
  have hg0 := (hD k hk.le).1
  have hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := (hD k hk.le).2.1.trans M.eps_le
  have hf : 1 + M.core.cGB * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤
      1 + 3 * M.core.cGB := by nlinarith
  have hf0 : 0 ≤ 1 + M.core.cGB * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := by
    positivity
  have h1 := mul_le_mul hf hΓ (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul hE' h1 (by positivity) (by positivity)
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 by norm_num)
  refine (le_of_eq (by ring)).trans (h3.trans (le_of_eq ?_))
  unfold eqcKA; ring

set_option maxHeartbeats 4000000 in
/-- **The top summand of `nbGB`**. -/
theorem eqc_top_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (o' : Obs2.ObsSt .two L N) (h0 : o'.IsObs)
    {ms : ℕ} (hms0 : 0 < ms) (hmsN : ms < Nh) {M₀ Rl : ℝ} (hM0 : 0 ≤ M₀) (hRl : 0 ≤ Rl)
    (hrel : M₀ ≤ Rl * ‖bt2 R P (zV0 b) m b μ₀ ms‖) :
    2 * ctEnv R m b μ₀ P ms o' M₀ (Nh - ms) * (‖gamT R m b μ₀ Nh‖ +
      gbKb L (R.withMsq m).ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
      (cZ (R.withMsq m)) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
        zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) ≤
      M.eqcKT * (Rl * (b * thJ R m b μ₀ Nh ^ 2)) := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hG := M.eqcG_nonneg
  have hKe := M.eqcKe_nonneg
  set T := thJ R m b μ₀ Nh with hTd
  have hT0 : 0 ≤ T := Real.rpow_nonneg (div_pos (hD Nh le_rfl).1 hb).le _
  have hE := M.eqc_env_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o' h0 hms0 hmsN hRl hrel
    (i := Nh - ms) (by omega)
  rw [show ms + (Nh - ms) = Nh by omega] at hE
  have hE0 : 0 ≤ ctEnv R m b μ₀ P ms o' M₀ (Nh - ms) :=
    mul_nonneg hM0 (prod_nonneg fun _ _ => norm_nonneg _)
  have hΓ := M.eqc_gamT_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := Nh) le_rfl
  have hZ := M.eqc_zinv_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (n := Nh) le_rfl
  set K := max (gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm) (16 * M.core.ℓ ^ 2 / 49)) 0 with hKd
  have hK0 : 0 ≤ K := le_max_right _ _
  have eK : gbKb L (R.withMsq m).ℓ (cmu ((L : ℝ) ^ 2) M.core.cm) (cZ (R.withMsq m)) =
      gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm) (16 * M.core.ℓ ^ 2 / 49) := by
    show gbKb L R.ℓ _ (16 * R.ℓ ^ 2 / 49) = _
    rw [hRℓ]
  rw [eK]
  have hg0 := (hD Nh le_rfl).1
  have hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 := (hD Nh le_rfl).2.1.trans M.eps_le
  obtain ⟨hρ0, hρ8⟩ := M.eqc_rho R hRρ m
  have hzp := zH_pos (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
  have hq : gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm) (16 * M.core.ℓ ^ 2 / 49) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
        zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) ≤
      K * Real.exp M.core.KZ * T := by
    rw [div_eq_mul_inv]
    have a1 : gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm) (16 * M.core.ℓ ^ 2 / 49) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ K := by
      have := le_max_left (gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm) (16 * M.core.ℓ ^ 2 / 49)) 0
      nlinarith
    have a2 := mul_le_mul a1 hZ (inv_nonneg.2 hzp.le) hK0
    exact a2.trans (le_of_eq (by ring))
  have hs : ‖gamT R m b μ₀ Nh‖ + gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
      (16 * M.core.ℓ ^ 2 / 49) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
        zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1) ≤
      (M.eqcG / 16 + K * Real.exp M.core.KZ) * T := by
    have : (M.eqcG / 16 + K * Real.exp M.core.KZ) * T = M.eqcG / 16 * T + K * Real.exp M.core.KZ * T := by ring
    rw [this]; linarith
  have hs0 : 0 ≤ (M.eqcG / 16 + K * Real.exp M.core.KZ) * T := by positivity
  have h2 := (mul_le_mul_of_nonneg_left hs hE0).trans (mul_le_mul_of_nonneg_right hE hs0)
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 by norm_num)
  refine (le_of_eq (by ring)).trans (h3.trans (le_of_eq ?_))
  unfold eqcKT; rw [← hKd]; ring

theorem eqcKW_nonneg (hc0 : 0 ≤ M.core.c) : 0 ≤ M.eqcKW := by
  obtain ⟨-, -, -, -, -, hcWo, hBk, -, -, -⟩ := M.core.consts_nonneg
  have := M.eqcG_nonneg; have := M.eqcKe_nonneg; have := M.eqcS0_nonneg
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have : 0 ≤ M.core.cWo := by linarith
  have hc : 0 ≤ M.core.c ^ 2 := sq_nonneg _
  unfold eqcKW
  have h1 : 0 ≤ 135 / 8 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * M.eqcG * M.eqcKe := by
    positivity
  have h3 : 0 ≤ (PtCorr2.cBn : ℝ) * Q1 2 * (9 / 4 * M.core.cWo * M.core.c * M.eqcG * M.eqcKe) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by positivity)
  have : (0 : ℝ) ≤ PtCorr2.csN 2 := Nat.cast_nonneg _
  have : 0 ≤ Q1 2 * M.eqcS0 / 1344 :=
    div_nonneg (mul_nonneg (by linarith) M.eqcS0_nonneg) (by norm_num)
  have : 0 ≤ 15 / 14 * (M.eqcS0 / 1344 + 8 * (PtCorr2.csN 2 : ℝ) *
      (135 / 8 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * M.eqcG * M.eqcKe)) := by positivity
  linarith

theorem eqcK_nonneg (hc0 : 0 ≤ M.core.c) : 0 ≤ M.eqcK := by
  unfold eqcK; have := M.eqcKA_nonneg; have := M.eqcKW_nonneg hc0; have := M.eqcKT_nonneg; linarith

set_option maxHeartbeats 4000000 in
/-- **Item (c): the backward chain relative to `θ`**:
`nbGB ≤ (N_h − j_y + 1)·eqcK·R_l·bθ_{N_h}²` (`bθ_{N_h}² = ǧ_{N_h}ϑ_{N_h}`). -/
theorem eqc_nbGB_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (o' : Obs2.ObsSt .two L N) (h0 : o'.IsObs)
    {ms : ℕ} (hms0 : 0 < ms) (hmsN : ms < Nh) {M₀ Rl k w : ℝ} (hM0 : 0 ≤ M₀) (hRl : 0 ≤ Rl)
    (hrel : M₀ ≤ Rl * ‖bt2 R P (zV0 b) m b μ₀ ms‖) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)
    {jy : ℕ} (hmj : ms ≤ jy) (hjN : jy ≤ Nh) :
    M.nbGB R m b μ₀ Nh P ms o' M₀ k w jy ≤
      (((Nh - jy : ℕ) : ℝ) + 1) * M.eqcK * (Rl * (b * thJ R m b μ₀ Nh ^ 2)) := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set X := Rl * (b * thJ R m b μ₀ Nh ^ 2) with hXd
  have hX0 : 0 ≤ X := by
    have : 0 ≤ thJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos (hD Nh le_rfl).1 hb).le _
    positivity
  have hA := M.eqcKA_nonneg
  have hW := M.eqcKW_nonneg (by linarith [M.eqc_c_ge R hP hi0 hRℓ hRA hRρ hN2 hNh hm])
  have hT := M.eqcKT_nonneg
  have hsum : ∀ i ∈ range (Nh - jy),
      2 * ctEnv R m b μ₀ P ms o' M₀ (jy + i - ms) * ((1 + M.core.cGB *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (jy + i)).1 + zA L m (jy + i))) *
          ‖gamT R m b μ₀ (jy + i)‖) + M.ctGw R m b μ₀ P ms o' M₀ k w (jy + i - ms) ≤
        (M.eqcKA + M.eqcKW) * X := by
    intro i hi
    have hi' := mem_range.1 hi
    have h1 := M.eqc_bulk_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o' h0 hms0 hmsN hM0 hRl hrel
      (k := jy + i) (by omega) (by omega)
    have h2 := M.eqc_gw_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o' h0 hms0 hmsN hM0 hRl hrel hk
      hw hM (i := jy + i - ms) (by omega)
    linarith
  have hS := sum_le_sum hsum
  rw [sum_const, card_range, nsmul_eq_mul] at hS
  have htop := M.eqc_top_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o' h0 hms0 hmsN hM0 hRl hrel
  have hgw := M.eqc_gw_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o' h0 hms0 hmsN hM0 hRl hrel hk hw
    hM (i := Nh - ms) (by omega)
  unfold nbGB
  have hn0 : (0 : ℝ) ≤ ((Nh - jy : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : (((Nh - jy : ℕ) : ℝ) + 1) * M.eqcK * X =
      ((Nh - jy : ℕ) : ℝ) * ((M.eqcKA + M.eqcKW) * X) + (M.eqcKT + M.eqcKW) * X +
        ((Nh - jy : ℕ) : ℝ) * (M.eqcKT * X) + (M.eqcKA * X) := by unfold eqcK; ring
  rw [e]
  have : 0 ≤ ((Nh - jy : ℕ) : ℝ) * (M.eqcKT * X) := by positivity
  have : 0 ≤ M.eqcKA * X := by positivity
  linarith

set_option maxHeartbeats 4000000 in
/-- **The restart size at `N_h` relative to the vertex**: `σ ≤ e^{c'}e^{c}R_l|β_{a,N_h}|`. -/
theorem eqc_ctSig_rel {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (y : Lam 2 L N) (δ : Obs2.ObsSt .two L N) (h0 : δ.IsObs)
    {ms : ℕ} (hmsN : ms ≤ Nh) (hNh1 : 1 ≤ Nh) {M₀ Rl : ℝ} (hRl : 0 ≤ Rl)
    (hrel : M₀ ≤ Rl * ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖) :
    ctSig R m b Nh y ms δ M₀ ≤
      Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) *
        Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) * Rl * ‖hBeta R m b (b - m) y Nh‖ := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set c := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε) with hc
  have hhB : ‖hBeta R m b (b - m) y Nh‖ = ‖bt2 R (ptsX y) (zV0 b) m b (b - m) Nh‖ := by
    rw [hBeta_eq_zV0 R m b (b - m) y hNh1]; rfl
  rw [hhB]
  have hpc := M.cw4_prod_cmpD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsX y) (zV0 b)
    δ h0 (k := ms) (j := Nh - ms) (by omega)
  have hra := M.cw2_ratioD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsX y) (zV0 b)
    (zV0_mua_ne hb) (k := ms) (j := Nh - ms) (by omega)
  rw [show ms + (Nh - ms) = Nh by omega] at hra
  set Pf := ∏ i ∈ range (Nh - ms), ‖1 - Obs2.frakN2F (ptsX y) (Obs2.histCovO (R.withMsq m)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms (ms + i)‖
  set Pn := ∏ i ∈ range (Nh - ms), ‖1 - nn2 R (ptsX y) (zV0 b) m b (b - m) (ms + i)‖
  have hE : ctSig R m b Nh y ms δ M₀ = M₀ * Pf := rfl
  rw [hE]
  have hPf0 : 0 ≤ Pf := prod_nonneg fun _ _ => norm_nonneg _
  have hPn0 : 0 ≤ Pn := prod_nonneg fun _ _ => norm_nonneg _
  set βs := ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
  have hβs0 : 0 ≤ βs := norm_nonneg _
  have hec : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  have h1 : βs * Pn ≤ Real.exp c * ‖bt2 R (ptsX y) (zV0 b) m b (b - m) Nh‖ := by
    have := mul_le_mul_of_nonneg_left hra (Real.exp_pos c).le
    calc βs * Pn = Real.exp c * (Real.exp (-c) * βs * Pn) := by
          rw [← mul_assoc, ← mul_assoc, hec, one_mul]
      _ ≤ _ := this
  have h3 : M₀ * Pf ≤ Rl * βs * (Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) * Pn) :=
    mul_le_mul hrel hpc hPf0 (mul_nonneg hRl hβs0)
  have h4 := mul_le_mul_of_nonneg_left h1
    (mul_nonneg (Real.exp_pos (8 / 7 * (8 / 3 * (2 / (L : ℝ))))).le hRl)
  calc M₀ * Pf ≤ Rl * βs * (Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) * Pn) := h3
    _ = Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) * Rl * (βs * Pn) := by ring
    _ ≤ _ := h4
    _ = _ := by ring

end MasterFacts

end

end Spin2
