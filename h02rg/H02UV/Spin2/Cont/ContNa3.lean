import Spin2.Pair.PairLin2

set_option autoImplicit false

/-!
# The `h = 0` top identity `ε(u^δ_{N_h+1,a}) = n_a(lastOF_{N_h+1}(δ))`

Case (2), `h = 0`, the pair-difference datum `δ = pl2Delta R m b μ₀ x y ms` restarted at
`ms ≤ N_h` (any `y`, no coalescence condition). By `pl_W_rel` the generating elements
`W_top = e^{−u_{N_h+1}}·lastOF` of the three histories form a relative triple; `n_a` is additive on
triples (`pl_nA_sub`) and vanishes on the two reference entries (`pl2_WTop_facts`), so
`n_a(W_top(δ)) = 0`, i.e.

* **`na_eps_ua_top`**: `ε(u^δ_{N_h+1,a}) = n_a(lastOF_{ms}(δ))`;
* **`na_rpTopU_eq`**: `rpTopU(δ_{N_h+1}) = −n_a(lastOF_{N_h+1}(δ_{N_h+1}))`
  (`δ_{N_h+1} = obsHistFrom … ms δ (N_h+1)`; the last factor restarted at `N_h + 1`).

`na_nA_oexp_mul` (pure): `n_a(e^{−u}Y) = −ε(u_a) + n_aY` for an observable constant `u`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist PtCorr2

variable {L N : ℕ} [NeZero L]

section Pure

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `n_a(e^{−u}Y) = −ε(u_a) + n_aY` (`bulk u = 0`, `s_∅Y ≠ 0`). -/
theorem na_nA_oexp_mul {u Y : OE .two Λ} (hu : bulk u = 0) (hY : sE Y ≠ 0) :
    nA (oexp (-u) * Y) = -ε (u : SA .two Λ).a + nA Y := by
  have hb : bulk (-u) = 0 := by rw [map_neg, hu, neg_zero]
  obtain ⟨e1, a1, -, -⟩ := pl_sX_oexp_obs hb
  have h1 : sE (oexp (-u)) ≠ 0 := by rw [e1]; exact one_ne_zero
  rw [nA_mul h1 hY]
  unfold nA
  rw [e1, a1, div_one, NegMemClass.coe_neg, SA.neg_a, map_neg]

end Pure

section Delta

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 1000000 in
/-- **The `h = 0` top identity**: the accumulated `a`-constant of the restarted difference datum at
`N_h + 1` is the `n_a` of its last factor. -/
theorem na_eps_ua_top {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh) (hL7 : 7 ≤ L)
    {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N) (ms : ℕ)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) (hmN : ms ≤ Nh) :
    ε (plU (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a =
      nA (lastOF (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  obtain ⟨h₃, hl₃, -, hl₁, hl₂, hb₁₂⟩ := pl2_delta_inv R m hV hVL b μ₀ x y hmN hblk
  have h₁ := obsHist_isObs (R.withMsq m) (pl2Pts x y) _
    (obsInit_isObs .two (zV b) (pl2Pts x y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have h₂ := obsHist_isObs (R.withMsq m) (ptsX y) _ (obsInit_isObs .two (zV b) (ptsX y)) ms
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have hc : ∏ i ∈ Ico ms Nh, ch (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi =>
      pl_ch_ne (R.withMsq m) hN hspl hm0 hm hV hVL _ (by have := (mem_Ico.1 hi).2; omega)
  have hW := pl_W_rel (R.withMsq m) (pl2Pts x y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ (ptsX y)
    (pl2Pts x y).a (ptsX y).a (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) h₁ h₂ h₃ hl₁ hl₂ hl₃
    (pl_relSt_rr (R.withMsq m) ms _ _ _ _ hb₁₂) hmN le_rfl hc
  have hcN := pl_ch_ne (R.withMsq m) hN hspl hm0 hm hV hVL
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (le_refl Nh)
  have hrel := pl_rel_smul (ch (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ hW
  rw [pl_W_top (R.withMsq m) (pl2Pts x y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ h₁ hl₁ hmN,
    pl_W_top (R.withMsq m) (ptsX y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ h₂ hl₂ hmN,
    pl_W_top (R.withMsq m) (ptsX y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ h₃ hl₃ hmN, smul_smul,
    smul_smul, smul_smul, inv_mul_cancel₀ hcN, one_smul, one_smul, one_smul] at hrel
  rw [pl2_WTop_hist (R.withMsq m) (pl2Pts x y) _ ms Nh _ (by omega),
    pl2_WTop_hist (R.withMsq m) (ptsX y) _ ms Nh _ (by omega),
    plWTop_eq (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)] at hrel
  obtain ⟨s₁, a₁, -, -⟩ := pl2_WTop_facts (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0
    (pl2Pts x y)
  obtain ⟨-, a₂, -, -⟩ := pl2_WTop_facts (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0
    (ptsX y)
  have hA₃ := pl_nA_sub hrel
  rw [a₁, a₂, sub_zero] at hA₃
  have hs₃ := (pl_sE_eq hrel).2
  have hu := plU_bulk (R.withMsq m) (ptsX y) ms h₃ (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have hbn : bulk (-plU (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) = 0 := by rw [map_neg, hu, neg_zero]
  have hY : sE (lastOF (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) Nh
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ≠ 0 := by
    have e := hs₃
    rw [sE_mul, (pl_sX_oexp_obs hbn).1, one_mul] at e
    rw [e]; exact s₁
  rw [na_nA_oexp_mul hu hY] at hA₃
  linear_combination hA₃

/-- **`rpTopU` of the restarted difference datum at `N_h + 1`** (`h = 0`):
`rpTopU(δ_{N_h+1}) = −n_a(lastOF_{N_h+1}(δ_{N_h+1}))`. -/
theorem na_rpTopU_eq {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh) (hL7 : 7 ≤ L)
    {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N) (ms : ℕ)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) (hmN : ms ≤ Nh) :
    rpTopU (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) =
      -nA (lastOF (R.withMsq m) (ptsX y) (Nh + 1)
        (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  have h := na_eps_ua_top R hN m hρ1 hspl hm0 hm hV hVL hL7 hb hh0 x y ms hblk hmN
  have e : lastOF (R.withMsq m) (ptsX y) (Nh + 1)
      (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) =
      lastOF (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := by
    unfold lastOF zmOF finOF
    rw [obsHistFrom_self]
  rw [e, ← h]
  rfl

end Delta

end

end Spin2
