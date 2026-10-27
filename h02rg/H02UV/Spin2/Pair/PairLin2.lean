import PtCorr2.Pair.PairLin2
import Spin2.Pair.PairLin1
import Spin2.Multiscale.Conn

/-!
# Pair linearity, part 5: `P(x) − P(y)` as the restarted output of the difference datum (`h = 0`)

Case (2), the `h = 0` trajectory `t = traj (rgDataM R m) (L²) b μ₀` (`b = μ₀ + m²`), `N = N_h + 2`.

* `pl2_conn_eq` (translation, `avg_transl`): for a pair `Q` with `Q.b = Q.a + x`,
  `P(x) = P_{1/b}[0 ↔ x] = −⟨z̃_{Q.a}z̃_{Q.b}⟩` (`p = r = 0` at `h = 0`).
* **`pl2_W_facts`** (item 1): for every pair `Q`, the chain-invariant generating element
  `W_k = e^{−u_k}ω_{Γ_k}Z_k` of the pair observable history (`0 ≤ k ≤ N_h`) has
  `s_∅W_k ≠ 0`, `n_aW_k = n_bW_k = 0` (`⟨z̃_a⟩ = ⟨z̃_b⟩ = r = 0`) and `n_{ab}W_k = ⟨z̃_az̃_b⟩`;
  `pl2_WTop_facts`: the same for `W_top = e^{−u_{N_h+1}}·lastOF`.
* `pl2Pts x y = (y − x, y)` (the translated pair of `(0, x)`), `pl2O` (the pair observable history
  at `ms`), **`pl2Delta`** `= plDiffSt(rrStH(o₁), o₂)` with `β_B = m₂(V(B)_a)` (`pl2Beta`).
* **`pl2_delta_inv`** (item 3): `δ` is observable, `ObsLocInv (ptsX y) ms δ` (if `y − x` and `0`
  share the `ms`-block) and carries the reference `σ_b` part (`pl_diff_prj`).
* **`pl2_conn_diff`** (`ms ≤ j_y ≤ N_h`):
  `P(x) − P(y) = rpcOut_y(δ restarted from ms, at j_y) + ε(u^δ_{j_y,ab})`;
  **`pl2_conn_diff_top`** (`ms ≤ N_h`): the same with `rpTopOut` at `N_h + 1`.
* **`pl2_conn_diff_coal`**, **`pl2_conn_diff_top_coal`**: with the coalescence invariant
  `ObsCoalInv (ptsX y) ms δ` the `ab` constant vanishes (`rpb_coal_validL`) and the identities are
  exact (`j_y ≤ N_h`, resp. `N_h + 1 ≤ j_y`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Spin2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist PtCorr2

variable {L N : ℕ} [NeZero L]

/-! ### Pure assembly -/

section Pure

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- **The pure core.** `W₁, W₂, W₃` a triple, `W₁` with vanishing one-point parts and `s_∅ ≠ 0`,
`n_aW₂ = 0`, `W₃ = e^{−u₃}Y₃`: if `c_i = −n_{ab}W_i` (`i = 1, 2`), then
`c₁ − c₂ = plOut_{−ε(u₃,b)}(u₃, Y₃) + ε(u₃,ab)`. -/
theorem pl2_core {W₁ W₂ u₃ Y₃ : OE .two Λ} (hrel : PlRel W₁ W₂ (oexp (-u₃) * Y₃))
    (hu₃ : bulk u₃ = 0) (hs : sE W₁ ≠ 0) (hA₁ : nA W₁ = 0) (hA₂ : nA W₂ = 0) (hB₁ : nB W₁ = 0)
    {c₁ c₂ : ℂ} (h₁ : c₁ = -nAB W₁) (h₂ : c₂ = -nAB W₂) :
    c₁ - c₂ = plOut (-ε (u₃ : SA .two Λ).b) u₃ Y₃ + ε (u₃ : SA .two Λ).ab := by
  have hs₃ : sE (oexp (-u₃) * Y₃) ≠ 0 := by rw [(pl_sE_eq hrel).2]; exact hs
  have hA₃ : nA (oexp (-u₃) * Y₃) = 0 := by rw [← pl_nA_sub hrel, hA₁, hA₂, sub_zero]
  have hB₃ : nB (oexp (-u₃) * Y₃) = 0 := by rw [(pl_nB_eq hrel).2, hB₁]
  rw [pl2_plOut_W hu₃ hs₃ hA₃ hB₃, ← pl_nAB_sub hrel, h₁, h₂]
  ring

end Pure

/-! ### `P(x)` by translation -/

theorem pl2_zObsA (b : ℝ) (Q : ObsPts 2 L N) :
    PtCorr2.zObsA (zV b) Q = 1 - (b : ℂ) • (psibar Q.a * psi Q.a) := by
  simp [PtCorr2.zObsA, zV, sub_eq_add_neg, neg_smul]

theorem pl2_zObsB (b : ℝ) (Q : ObsPts 2 L N) :
    PtCorr2.zObsB (zV b) Q = 1 - (b : ℂ) • (psibar Q.b * psi Q.b) := by
  simp [PtCorr2.zObsB, zV, sub_eq_add_neg, neg_smul]

/-- **`P(x) = −⟨z̃_{Q.a}z̃_{Q.b}⟩` for any pair with `Q.b = Q.a + x`** (`h = 0`). -/
theorem pl2_conn_eq {b μ₀ m : ℝ} (hb : 0 < b) (hm0 : 0 < m) (hh0 : b = μ₀ + m) (hN1 : 1 ≤ N)
    (x : Lam 2 L N) (Q : ObsPts 2 L N) (hQ : Q.b = Q.a + x) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) =
      -PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) Q * PtCorr2.zObsB (zV b) Q) := by
  rw [Pconn_eq_avg0 hb hm0 hh0 x]
  obtain ⟨p, r, hp0, hpr, -, hr, hP⟩ := PtCorr2.twopt_eq_neg_zz (L := L) (N := N) hb hm0 hh0.le x
  have hr0 : (r : ℂ) = 0 := by
    rw [← hr, PtCorr2.onept_avg0_h0 hb hm0 hh0, mul_one_div_cancel
      (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]
  have hr0' : r = 0 := by exact_mod_cast hr0
  have hp : (p : ℂ) = 0 := by
    have : p = 0 := le_antisymm (hr0' ▸ hpr) hp0
    rw [this, Complex.ofReal_zero]
  rw [hP, hp, add_zero, pl2_zObsA, pl2_zObsB, hQ]
  congr 1
  have h := PtCorr.avg_transl hm0 hN1 (PtCorr2.V0c b μ₀) Q.a
    ((1 - (b : ℂ) • (psibar (0 : Lam 2 L N) * psi 0)) * (1 - (b : ℂ) • (psibar x * psi x)))
  simp only [map_mul, map_sub, map_one, map_smul, autAlg_psibar, autAlg_psi,
    Equiv.coe_addRight, zero_add] at h
  rw [add_comm Q.a x]
  exact h.symm

/-! ### The one-point facts of the generating element (item 1) -/

section Facts

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem pl2_avg_zA_zero {b μ₀ m : ℝ} (hb : 0 < b) (hm0 : 0 < m) (hh0 : b = μ₀ + m) (hN1 : 1 ≤ N)
    (p : Lam 2 L N) :
    PtCorr2.avg0 L N m b μ₀ (1 - (b : ℂ) • (psibar p * psi p)) = 0 := by
  rw [show PtCorr2.avg0 L N m b μ₀ (1 - (b : ℂ) • (psibar p * psi p)) =
      1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar p * psi p) from
    Ward.avg_one_sub_smul _ _ (PtCorr2.onept_Zb_ne hb hm0 hh0.le) _ _,
    PtCorr2.avg0_diag_transl hm0 hN1 p, PtCorr2.onept_avg0_h0 hb hm0 hh0,
    mul_one_div_cancel (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]

set_option maxHeartbeats 1000000 in
/-- **Item 1**: the generating element of the pair observable history of any pair `Q` at `h = 0`
(`k ≤ N_h`): `s_∅W_k ≠ 0`, `n_aW_k = n_bW_k = 0`, `n_{ab}W_k = ⟨z̃_az̃_b⟩`. -/
theorem pl2_W_facts {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (hL7 : 7 ≤ L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh0 : b = μ₀ + R.msq) (Q : ObsPts 2 L N) {k : ℕ} (hk : k ≤ Nh) :
    sE (plW R Q 0 (obsInit .two (zV b) Q) k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) ≠ 0 ∧
      nA (plW R Q 0 (obsInit .two (zV b) Q) k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) = 0 ∧
      nB (plW R Q 0 (obsInit .two (zV b) Q) k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) = 0 ∧
      nAB (plW R Q 0 (obsInit .two (zV b) Q) k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
        PtCorr2.avg0 L N R.msq b μ₀ (PtCorr2.zObsA (zV b) Q * PtCorr2.zObsB (zV b) Q) := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hZ, ha, hbb, hab⟩ := PtCorr2.zz_rg_ratio R Q hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0.le
    (zV b) (zV_abFree b)
  have h0 := PtCorr2.hist_omegaO_traj_loc R Q (obsInit .two (zV b) Q) hN hρ1 hspl hm0 hm hV hVL
    b μ₀ (obsInit_isObs .two (zV b) Q) (PtCorr2.obsLocInv_init .two (zV b) Q)
  have hW0 := (pl2_W_zero R Q (obsInit .two (zV b) Q) rfl _).trans h0
  have hch := pl_W_chain R Q 0 hN hρ1 hspl hm0 hm hV hVL b μ₀ (obsInit_isObs .two (zV b) Q)
    (PtCorr2.obsLocInv_init .two (zV b) Q) (Nat.zero_le k) hk
  rw [hW0] at hch
  have hc : ∏ i ∈ Ico 0 k, ch R i (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi =>
      pl_ch_ne R hN hspl hm0 hm hV hVL _ (by have := (mem_Ico.1 hi).2; omega)
  obtain ⟨hs, hA, hB, hAB⟩ := pl2_nX_smul hc
    (plW R Q 0 (obsInit .two (zV b) Q) k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
  rw [← hch] at hs hA hB hAB
  refine ⟨hs.1 hZ, ?_, ?_, ?_⟩
  · rw [← hA]
    show sA _ / sE _ = 0
    rw [← ha, pl2_zObsA]
    exact pl2_avg_zA_zero hb hm0 hh0 hN1 Q.a
  · rw [← hB]
    show sB _ / sE _ = 0
    rw [← hbb, pl2_zObsB]
    exact pl2_avg_zA_zero hb hm0 hh0 hN1 Q.b
  · rw [← hAB, hab]; rfl

set_option maxHeartbeats 1000000 in
/-- **Item 1 at the top**: the same for `W_top = e^{−u_{N_h+1}}·lastOF`. -/
theorem pl2_WTop_facts {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (hL7 : 7 ≤ L) {b μ₀ : ℝ} (hb : 0 < b)
    (hh0 : b = μ₀ + R.msq) (Q : ObsPts 2 L N) :
    sE (plWTop R Q 0 (obsInit .two (zV b) Q) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) ≠ 0 ∧
      nA (plWTop R Q 0 (obsInit .two (zV b) Q) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) = 0 ∧
      nB (plWTop R Q 0 (obsInit .two (zV b) Q) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) = 0 ∧
      nAB (plWTop R Q 0 (obsInit .two (zV b) Q) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
        PtCorr2.avg0 L N R.msq b μ₀ (PtCorr2.zObsA (zV b) Q * PtCorr2.zObsB (zV b) Q) := by
  obtain ⟨s, a, bb, ab⟩ := pl2_W_facts R hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0 Q (le_refl Nh)
  have ht := pl_W_top R Q 0 hN hρ1 hspl hm0 hm hV hVL b μ₀ (obsInit_isObs .two (zV b) Q)
    (PtCorr2.obsLocInv_init .two (zV b) Q) (Nat.zero_le Nh)
  obtain ⟨hs, hA, hB, hAB⟩ := pl2_nX_smul (pl_ch_ne R hN hspl hm0 hm hV hVL
    (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) (le_refl Nh))
    (plWTop R Q 0 (obsInit .two (zV b) Q) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
  rw [← ht] at hs hA hB hAB
  exact ⟨hs.1 s, hA ▸ a, hB ▸ bb, hAB ▸ ab⟩

end Facts

/-! ### The difference datum -/

section Delta

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The translated pair `(y − x, y)` of `(0, x)`. -/
def pl2Pts (x y : Lam 2 L N) : ObsPts 2 L N := ⟨y - x, y, ∅⟩

/-- The pair observable history of `Q` at scale `ms` along the `m²` trajectory. -/
def pl2O (m b μ₀ : ℝ) (Q : ObsPts 2 L N) (ms : ℕ) : ObsSt .two L N :=
  obsHist (R.withMsq m) Q (obsInit .two (zV b) Q) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- **The difference datum** at `ms`: the relocated history of `(y − x, y)` (Loc point `0`,
`β_B = m₂(V(B)_a)`) minus the reference history of `(0, y)`, with the reference `∅`/`σ_b` parts. -/
def pl2Delta (m b μ₀ : ℝ) (x y : Lam 2 L N) (ms : ℕ) : ObsSt .two L N :=
  plDiffSt (rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a
      (ptsX y).a (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) (pl2O R m b μ₀ (pl2Pts x y) ms))
    (pl2O R m b μ₀ (ptsX y) ms)

theorem pl2_valid {Nh : ℕ} (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (t : Hist.Seq (Xs (R.withMsq m))) {n : ℕ} (hn : n ≤ Nh) :
    ∀ i ≤ n, ValidCore (R.withMsq m) i ∧ RawInv (R.withMsq m) i (rawHist (R.withMsq m) i t) := by
  intro i hi
  refine ⟨?_, rawInv_histU (R.withMsq m) hV hVL t i (by omega)⟩
  rcases Nat.lt_or_ge i Nh with h | h
  · exact (hV i h).toValidCore
  · rw [show i = Nh by omega]; exact hVL.2

/-- **Item 3 and the setting of T5**: the difference datum is observable, local at `ms` around the
reference points `(0, y)`, and carries the reference `σ_b` part; the data form a state triple. -/
theorem pl2_delta_inv {Nh : ℕ} (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (b μ₀ : ℝ) (x y : Lam 2 L N) {ms : ℕ} (hmN : ms ≤ Nh)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) :
    (pl2Delta R m b μ₀ x y ms).IsObs ∧ ObsLocInv (ptsX y) ms (pl2Delta R m b μ₀ x y ms) ∧
      prjSt false (pl2Delta R m b μ₀ x y ms) = prjSt false (pl2O R m b μ₀ (ptsX y) ms) ∧
      ObsLocInv (pl2Pts x y) ms (pl2O R m b μ₀ (pl2Pts x y) ms) ∧
      ObsLocInv (ptsX y) ms (pl2O R m b μ₀ (ptsX y) ms) ∧
      prjSt false (pl2O R m b μ₀ (pl2Pts x y) ms) = prjSt false (pl2O R m b μ₀ (ptsX y) ms) := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hval := pl2_valid R m hV hVL t hmN
  have hl₁ : ObsLocInv (pl2Pts x y) ms (pl2O R m b μ₀ (pl2Pts x y) ms) :=
    obsLocInv_hist (R.withMsq m) (pl2Pts x y) _ (obsLocInv_init .two (zV b) (pl2Pts x y)) t ms
      fun i hi => hval i hi.le
  have hl₂ : ObsLocInv (ptsX y) ms (pl2O R m b μ₀ (ptsX y) ms) :=
    obsLocInv_hist (R.withMsq m) (ptsX y) _ (obsLocInv_init .two (zV b) (ptsX y)) t ms
      fun i hi => hval i hi.le
  have hr := pl2_rrSt_locInv_core (R.withMsq m) ms (rawHist (R.withMsq m) ms t) (t ms).1
    (t ms).2.1 (rawD (R.withMsq m) (rawHist (R.withMsq m) ms t).u (t ms).2.2)
    (rawK (R.withMsq m) (rawHist (R.withMsq m) ms t).u (t ms).2.2) (ptsX y).a
    (P' := ptsX y) hl₁ rfl hblk rfl (hval ms le_rfl).1 (hval ms le_rfl).2
    (rawD_mem (R.withMsq m) _ _) (rawK_mem (R.withMsq m) _ _)
  have hb : prjSt false (pl2O R m b μ₀ (pl2Pts x y) ms) =
      prjSt false (pl2O R m b μ₀ (ptsX y) ms) := by
    unfold pl2O
    rw [prj_obsHist (R.withMsq m) false (P := pl2Pts x y) (P' := ⟨y, y, ∅⟩) rfl,
      prj_obsHist (R.withMsq m) false (P := ptsX y) (P' := ⟨y, y, ∅⟩) rfl,
      pl2_prj_init (zV b) (P := pl2Pts x y) (P' := ptsX y) rfl]
  exact ⟨pl_diff_isObs _ (obsHist_isObs _ _ _ (obsInit_isObs .two (zV b) (ptsX y)) _ _),
    pl2_diff_locInv hr hl₂, pl_diff_prj _ _, hl₁, hl₂, hb⟩

set_option maxHeartbeats 1000000 in
/-- **The exact pair difference at the coalescence scale of `(0, y)`** (`h = 0`,
`ms ≤ j_y ≤ N_h`, `y − x` and `0` in one `ms`-block):
`P(x) − P(y) = rpcOut_y(δ restarted from ms, at j_y) + ε(u^δ_{j_y,ab})`. -/
theorem pl2_conn_diff {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh) (hL7 : 7 ≤ L)
    {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N) (ms : ℕ)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmj : ms ≤ Obs.coal L (0 : Lam 2 L N) y) (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
      rpcOut R m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) +
      ε (plU (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Obs.coal L (0 : Lam 2 L N) y)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab := by
  have hN1 : 1 ≤ N := by omega
  have e : (R.withMsq m).msq = m := rfl
  obtain ⟨h₃, hl₃, -, hl₁, hl₂, hb₁₂⟩ := pl2_delta_inv R m hV hVL b μ₀ x y (hmj.trans hj) hblk
  have h₁ := obsHist_isObs (R.withMsq m) (pl2Pts x y) _
    (obsInit_isObs .two (zV b) (pl2Pts x y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have h₂ := obsHist_isObs (R.withMsq m) (ptsX y) _ (obsInit_isObs .two (zV b) (ptsX y)) ms
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have hc : ∏ i ∈ Ico ms (Obs.coal L (0 : Lam 2 L N) y), ch (R.withMsq m) i (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi =>
      pl_ch_ne (R.withMsq m) hN hspl hm0 hm hV hVL _ (by have := (mem_Ico.1 hi).2; omega)
  have hrel := pl_W_rel (R.withMsq m) (pl2Pts x y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ (ptsX y)
    (pl2Pts x y).a (ptsX y).a (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) h₁ h₂ h₃ hl₁ hl₂ hl₃
    (pl_relSt_rr (R.withMsq m) ms _ _ _ _ hb₁₂) hmj hj hc
  rw [pl2_W_hist (R.withMsq m) (pl2Pts x y) _ ms _ hmj,
    pl2_W_hist (R.withMsq m) (ptsX y) _ ms _ hmj,
    plW_eq (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)] at hrel
  obtain ⟨s₁, a₁, b₁, ab₁⟩ := pl2_W_facts (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0
    (pl2Pts x y) hj
  obtain ⟨-, a₂, -, ab₂⟩ := pl2_W_facts (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0
    (ptsX y) hj
  rw [e] at ab₁ ab₂
  have H := pl2_core hrel (plU_bulk (R.withMsq m) (ptsX y) ms h₃ _ _) s₁ a₁ a₂ b₁
    (c₁ := ((Pconn L N (1 / b) x : ℝ) : ℂ)) (c₂ := ((Pconn L N (1 / b) y : ℝ) : ℂ))
    (by rw [ab₁]; exact pl2_conn_eq hb hm0 hh0 hN1 x (pl2Pts x y) (by show y = y - x + x; abel))
    (by rw [ab₂]; exact pl2_conn_eq hb hm0 hh0 hN1 y (ptsX y) (by show y = 0 + y; rw [zero_add]))
  have huB : uB R m b μ₀ y (Obs.coal L (0 : Lam 2 L N) y) =
      -ε (plU (R.withMsq m) (ptsX y) ms (pl2O R m b μ₀ (ptsX y) ms) (Obs.coal L (0 : Lam 2 L N) y)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).b := by
    unfold uB plU pl2O
    rw [rpb_histFrom_obsHist (R.withMsq m) (ptsX y) _ ms _ _ hmj]
  have hub3 := pl_u_b_eq (R.withMsq m) (P := ptsX y) (P' := ptsX y) rfl ms
    (pl_diff_prj (rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
      (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) (pl2O R m b μ₀ (pl2Pts x y) ms))
      (pl2O R m b μ₀ (ptsX y) ms)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs.coal L (0 : Lam 2 L N) y)
  rw [H, pl_rpcOut_eq, huB, ← hub3]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The exact pair difference at the top** (`h = 0`, `ms ≤ N_h`, `y − x` and `0` in one
`ms`-block): `P(x) − P(y) = rpTopOut_y(δ restarted from ms, at N_h + 1) + ε(u^δ_{N_h+1,ab})`. -/
theorem pl2_conn_diff_top {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh) (hL7 : 7 ≤ L)
    {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N) (ms : ℕ)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) (hmN : ms ≤ Nh) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
      rpTopOut R Nh m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) +
      ε (plU (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab := by
  have hN1 : 1 ≤ N := by omega
  have e : (R.withMsq m).msq = m := rfl
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
  have hcN := pl_ch_ne (R.withMsq m) hN hspl hm0 hm hV hVL (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (le_refl Nh)
  have hrel := pl_rel_smul (ch (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ hW
  rw [pl_W_top (R.withMsq m) (pl2Pts x y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ h₁ hl₁ hmN,
    pl_W_top (R.withMsq m) (ptsX y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ h₂ hl₂ hmN,
    pl_W_top (R.withMsq m) (ptsX y) ms hN hρ1 hspl hm0 hm hV hVL b μ₀ h₃ hl₃ hmN, smul_smul,
    smul_smul, smul_smul, inv_mul_cancel₀ hcN, one_smul, one_smul, one_smul] at hrel
  rw [pl2_WTop_hist (R.withMsq m) (pl2Pts x y) _ ms Nh _ (by omega),
    pl2_WTop_hist (R.withMsq m) (ptsX y) _ ms Nh _ (by omega),
    plWTop_eq (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)] at hrel
  obtain ⟨s₁, a₁, b₁, ab₁⟩ := pl2_WTop_facts (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0
    (pl2Pts x y)
  obtain ⟨-, a₂, -, ab₂⟩ := pl2_WTop_facts (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL hL7 hb hh0
    (ptsX y)
  rw [e] at ab₁ ab₂
  have H := pl2_core hrel (plU_bulk (R.withMsq m) (ptsX y) ms h₃ _ _) s₁ a₁ a₂ b₁
    (c₁ := ((Pconn L N (1 / b) x : ℝ) : ℂ)) (c₂ := ((Pconn L N (1 / b) y : ℝ) : ℂ))
    (by rw [ab₁]; exact pl2_conn_eq hb hm0 hh0 hN1 x (pl2Pts x y) (by show y = y - x + x; abel))
    (by rw [ab₂]; exact pl2_conn_eq hb hm0 hh0 hN1 y (ptsX y) (by show y = 0 + y; rw [zero_add]))
  have huB : uB R m b μ₀ y (Nh + 1) =
      -ε (plU (R.withMsq m) (ptsX y) ms (pl2O R m b μ₀ (ptsX y) ms) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).b := by
    unfold uB plU pl2O
    rw [rpb_histFrom_obsHist (R.withMsq m) (ptsX y) _ ms _ _ (by omega)]
  have hub3 := pl_u_b_eq (R.withMsq m) (P := ptsX y) (P' := ptsX y) rfl ms
    (pl_diff_prj (rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (pl2Pts x y).a (ptsX y).a
      (pl2Beta (pl2O R m b μ₀ (pl2Pts x y) ms)) (pl2O R m b μ₀ (pl2Pts x y) ms))
      (pl2O R m b μ₀ (ptsX y) ms)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
  rw [H, pl_rpTopOut_eq, huB, ← hub3]
  rfl

/-- **Item 2 (conditional on the coalescence invariant of `δ`)**: the `ab` constant of the
restarted history vanishes up to `min(j_y, N_h + 1)`. -/
theorem pl2_delta_uab {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (b μ₀ : ℝ)
    (x y : Lam 2 L N) {ms : ℕ} (hmN : ms ≤ Nh) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hcoal : ObsCoalInv (ptsX y) ms (pl2Delta R m b μ₀ x y ms)) {k : ℕ} (hmk : ms ≤ k)
    (hk : k ≤ min (Obs.coal L (0 : Lam 2 L N) y) (Nh + 1)) :
    ε (plU (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) k
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab = 0 := by
  obtain ⟨h₃, -⟩ := pl2_delta_inv R m hV hVL b μ₀ x y hmN hblk
  have := (rpb_coal_validL (R.withMsq m) (ptsX y) hN h₃ hcoal hL hV hVL
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k hmk hk).2
  unfold plU
  rw [this, map_zero]

set_option maxHeartbeats 1000000 in
/-- **Exact form below coalescence** (`ObsCoalInv (ptsX y) ms δ`):
`P(x) − P(y) = rpcOut_y(δ restarted from ms, at j_y)`. -/
theorem pl2_conn_diff_coal {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N)
    (ms : ℕ) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmj : ms ≤ Obs.coal L (0 : Lam 2 L N) y) (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
    (hcoal : ObsCoalInv (ptsX y) ms (pl2Delta R m b μ₀ x y ms)) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
      rpcOut R m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  rw [pl2_conn_diff R hN m hρ1 hspl hm0 hm hV hVL (by omega) hb hh0 x y ms hblk hmj hj,
    pl2_delta_uab R hN m hV hVL hL b μ₀ x y (hmj.trans hj) hblk hcoal hmj
      (le_min le_rfl (by omega)), add_zero]

set_option maxHeartbeats 1000000 in
/-- **Exact form at the top** (`N_h + 1 ≤ j_y`, `ObsCoalInv (ptsX y) ms δ`):
`P(x) − P(y) = rpTopOut_y(δ restarted from ms, at N_h + 1)`. -/
theorem pl2_conn_diff_top_coal {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {b μ₀ : ℝ} (hb : 0 < b) (hh0 : b = μ₀ + m) (x y : Lam 2 L N)
    (ms : ℕ) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) (hmN : ms ≤ Nh)
    (hjy : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    (hcoal : ObsCoalInv (ptsX y) ms (pl2Delta R m b μ₀ x y ms)) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ) =
      rpTopOut R Nh m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  rw [pl2_conn_diff_top R hN m hρ1 hspl hm0 hm hV hVL (by omega) hb hh0 x y ms hblk hmN,
    pl2_delta_uab R hN m hV hVL hL b μ₀ x y hmN hblk hcoal (by omega) (le_min hjy le_rfl),
    add_zero]

end Delta

end

end Spin2
