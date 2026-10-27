import Spin2.Pair.PairLin2
import PtCorr2.Restart.CoalRestartR

/-!
# Pair linearity, part 6: the coalescence invariant of the difference datum (relaxed radius)

Closes open item 1 of "B3, T6: `P(x) − P(y)` as the restarted output of the difference datum":
the difference datum `δ = pl2Delta R m b μ₀ x y ms` satisfies the **relaxed** coalescence invariant
`ObsCoalInvR (ptsX y) ms ρ δ` with `ρ = |y − x|_∞ < L^{ms}` (the `σ_a` parts of `𝒲`, `K` of the
relocated history of `(y − x, y)` live near `y − x`, i.e. within `L^{ms} + ρ` of the new point `0`).
The relaxed invariant propagates like the strict one (`Obs2/Pair/CoalR`, `Obs2/Pair/CoalHistR`), so:

* **`pl3_delta_coalR`**: `ObsCoalInvR (ptsX y) ms |y − x|_∞ δ` (for `ms < j_x`, `ms < j_y`);
* **`pl3_delta_ab`**: `V^δ_{k,ab} = 0`, `u^δ_{k,ab} = 0` for `ms ≤ k ≤ min(j_y, N_h + 1)`;
  **`pl3_delta_inv`**: the relaxed invariant (in particular `K^δ_{k}(X)_{ab} = 0` for small `X`,
  `𝒲^δ_{k,ab} = 0`) for `ms ≤ k < j_y`, `k ≤ N_h + 1`;
* **`pl3_conn_diff`**: `P(x) − P(y) = rpcOut_y(δ restarted from ms, at j_y)` exactly (no extra
  term), **`pl3_conn_diff_top`**: `= rpTopOut_y(δ at N_h + 1)` exactly for `N_h + 1 ≤ j_y`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Spin2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist PtCorr2

variable {L N : ℕ} [NeZero L]

section Delta

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem pl3_abFree (b : ℝ) : AbFree .two (zV b) := ⟨rfl, rfl, rfl, rfl⟩

/-- The strict coalescence invariant of the pair history of `Q` at `ms < j_Q`. -/
theorem pl3_o_coalInv {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ)
    (Q : ObsPts 2 L N) {ms : ℕ} (hmQ : ms < Obs.coal L Q.a Q.b) (hmN : ms ≤ Nh + 1) :
    ObsCoalInv Q ms (pl2O R m b μ₀ Q ms) := by
  have h := rpb_coalInv (R.withMsq m) Q (m := 0) (obsInit_isObs .two (zV b) Q)
    (coalInv_init .two (pl3_abFree b) Q) hL (n := min (Obs.coal L Q.a Q.b) (Nh + 1))
    ((min_le_right _ _).trans (by omega)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
    (fun k hk x y hxy => by
      have hkN : k ≤ Nh := by have := min_le_right (Obs.coal L Q.a Q.b) (Nh + 1); omega
      have H := rawInv_histU (R.withMsq m) hV hVL (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
        (by omega)
      exact (covU (R.withMsq m) hV hVL hkN H).1.range (by omega) x y hxy)
    ms (Nat.zero_le _) hmQ (le_min hmQ.le hmN)
  rw [obsHistFrom_zero] at h
  exact h

theorem pl3_rho_lt {x y : Lam 2 L N} {ms : ℕ} (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) :
    supNorm (y - x) < L ^ ms := by
  have := supNorm_lt_of_blk_eq hblk
  rwa [sub_zero] at this

/-- **The relaxed coalescence invariant of the difference datum** at `ms`, radius
`L^{ms} + |y − x|_∞` around `(0, y)` (`ms < j_x`, `ms < j_y`). -/
theorem pl3_delta_coalR {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ)
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ) (x y : Lam 2 L N) {ms : ℕ} (hmN : ms ≤ Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y) :
    ObsCoalInvR (ptsX y) ms (supNorm (y - x)) (pl2Delta R m b μ₀ x y ms) := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hval := pl2_valid R m hV hVL t hmN
  have hcx : Obs.coal L (pl2Pts x y).a (pl2Pts x y).b = Obs.coal L (0 : Lam 2 L N) x := by
    show Nat.log L (2 * supNorm (y - x - y)) = Nat.log L (2 * supNorm (0 - x))
    rw [show y - x - y = -x by abel, zero_sub]
  have H₁ := pl3_o_coalInv R hN m hV hVL hL b μ₀ (pl2Pts x y) (by rw [hcx]; exact hmx) (by omega)
  have H₂ := pl3_o_coalInv R hN m hV hVL hL b μ₀ (ptsX y) hmy (by omega)
  have hf : ∀ b', Loc2Form (pl2Pts x y).a
      (((pl2O R m b μ₀ (pl2Pts x y) ms).V b' : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a := by
    intro b'
    have := obsHist_hform2 (R.withMsq m) (pl2Pts x y) (obsInit .two (zV b) (pl2Pts x y)) t
      (fun b'' => obsInit_two_form (pl2Pts x y) (zV b) b'') ms b'
    rwa [histVO2_a] at this
  have hab : (L : ℝ) ^ (ms + 1) / 2 ≤ supNorm ((pl2Pts x y).a - (pl2Pts x y).b) :=
    pow_le_of_lt_coal (by rw [hcx]; exact hmx)
  have Hr := crr_rrSt_coalInvR (R.withMsq m) ms (rawHist (R.withMsq m) ms t) (t ms).1 (t ms).2.1
    (rawD (R.withMsq m) (rawHist (R.withMsq m) ms t).u (t ms).2.2)
    (rawK (R.withMsq m) (rawHist (R.withMsq m) ms t).u (t ms).2.2) (P' := ptsX y) H₁ hf rfl
    (ρ := supNorm (y - x)) (by show supNorm (y - x - 0) ≤ _; rw [sub_zero]) (by omega) hab
  exact crr_diff_coalInvR Hr (H₂.toR _)

/-- **`V^δ_{ab} = 0` and `u^δ_{ab} = 0`** along the restarted history up to `min(j_y, N_h + 1)`. -/
theorem pl3_delta_ab {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ)
    (x y : Lam 2 L N) {ms : ℕ} (hmN : ms ≤ Nh) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    {k : ℕ} (hmk : ms ≤ k) (hk : k ≤ min (Obs.coal L (0 : Lam 2 L N) y) (Nh + 1)) :
    (∀ B, ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V B : SA .two (Lam 2 L N)).ab = 0) ∧
    ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u : SA .two (Lam 2 L N)).ab = 0 := by
  obtain ⟨h₃, -⟩ := pl2_delta_inv R m hV hVL b μ₀ x y hmN hblk
  exact crr_coal_validL (R.withMsq m) (ptsX y) hN h₃
    (pl3_delta_coalR R hN m hV hVL hL b μ₀ x y hmN hmx hmy) (pl3_rho_lt hblk).le hL hV hVL
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k hmk hk

/-- **The relaxed invariant along the restarted history** (`ms ≤ k < j_y`, `k ≤ N_h + 1`): in
particular `𝒲^δ_{k,ab} = 0` and `K^δ_k(X)_{ab} = 0` for small `X` (`hKs` of `rpab_hist`). -/
theorem pl3_delta_inv {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ)
    (x y : Lam 2 L N) {ms : ℕ} (hmN : ms ≤ Nh) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    {k : ℕ} (hmk : ms ≤ k) (hk : k < Obs.coal L (0 : Lam 2 L N) y) (hkN : k ≤ Nh + 1) :
    ObsCoalInvR (ptsX y) k (supNorm (y - x)) (obsHistFrom (R.withMsq m) (ptsX y) ms
      (pl2Delta R m b μ₀ x y ms) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  obtain ⟨h₃, -⟩ := pl2_delta_inv R m hV hVL b μ₀ x y hmN hblk
  exact crr_coalInv_validL (R.withMsq m) (ptsX y) hN h₃
    (pl3_delta_coalR R hN m hV hVL hL b μ₀ x y hmN hmx hmy) (pl3_rho_lt hblk).le hL hV hVL
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k hmk hk hkN

theorem pl3_delta_uab {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ)
    (x y : Lam 2 L N) {ms : ℕ} (hmN : ms ≤ Nh) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    {k : ℕ} (hmk : ms ≤ k) (hk : k ≤ min (Obs.coal L (0 : Lam 2 L N) y) (Nh + 1)) :
    ε (plU (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab = 0 := by
  have := (pl3_delta_ab R hN m hV hVL hL b μ₀ x y hmN hblk hmx hmy hmk hk).2
  unfold plU
  rw [this, map_zero]

set_option maxHeartbeats 1000000 in
/-- **`P(x) − P(y)` is exactly the restarted output of the difference datum** at the coalescence
scale of `(0, y)` (`h = 0`, `y − x` and `0` in one `ms`-block, `ms < j_x`, `ms < j_y ≤ N_h`). -/
theorem pl3_conn_diff {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N)
    (ms : ℕ) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
      rpcOut R m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  rw [pl2_conn_diff R hN m hρ1 hspl hm0 hm hV hVL (by omega) hb hh0 x y ms hblk hmy.le hj,
    pl3_delta_uab R hN m hV hVL hL b μ₀ x y (by omega) hblk hmx hmy hmy.le
      (le_min le_rfl (by omega)), add_zero]

set_option maxHeartbeats 1000000 in
/-- **The exact pair difference at the top** (`N_h + 1 ≤ j_y`, `ms < j_x`, `ms ≤ N_h`):
`P(x) − P(y) = rpTopOut_y(δ restarted from ms, at N_h + 1)`. -/
theorem pl3_conn_diff_top {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N)
    (ms : ℕ) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) (hmN : ms ≤ Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hjy : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
      rpTopOut R Nh m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  rw [pl2_conn_diff_top R hN m hρ1 hspl hm0 hm hV hVL (by omega) hb hh0 x y ms hblk hmN,
    pl3_delta_uab R hN m hV hVL hL b μ₀ x y hmN hblk hmx (by omega) (by omega)
      (le_min hjy le_rfl), add_zero]

end Delta

end

end Spin2
