import Spin2.Cont.ContNb5
import Spin2.Cont.ContWire9
import Spin2.H0.MasterH0Multi
import Spin2.H0.H0OnePt
import Spin2.Case2.Case2Top
import Spin2.Pair.PairPR5
import Spin2.Pair.PairRed
import Spin2.Cont.ContDiffD2
import Spin2.Cont.ContTop4

set_option autoImplicit false

/-!
# B3, `r`-dependent form, item (c): the backward chain `nbGB` relative to `cddRel`

Along `D_ε` (master constants), for the restart data at `ms` (`0 < ms < N_h`) with an envelope
`M₀ ≤ R_l·|β^P_{ms}|` (for the pair-difference datum `R_l = cddRel`, `pl4_T6_inputs`):

* **`MasterFacts.eqc_zinv_le`**: `1/|Z_{n+1}| ≤ e^{K_Z}θ_n` (`n ≤ N_h`);
* **`MasterFacts.eqc_bt_le`**: `|β^P_k| ≤ (1 + 3K_p)bθ_k` (`1 ≤ k < N_h`);
* **`MasterFacts.eqc_env_le`**: `M_i ≤ K_e·R_l·b·θ_{ms+i}` (`ms + i ≤ N_h`; `cw4_prod_cmpD`,
  `cw2_ratioD`, and one factor `|1 − 𝔫| ≤ 9/8` at `N_h − 1`);
* **`MasterFacts.eqc_nbGB_le`**: `nbGB ≤ (N_h − j_y + 1)·eqcK·R_l·bθ_{N_h}²`, with an explicit
  constant `eqcK` of the master construction (`bθ_{N_h}² = ǧ_{N_h}ϑ_{N_h}`);
* **`MasterFacts.eqc_ctSig_rel`**: `σ = M_{N_h−ms} ≤ e^{c'}e^{c}R_l|β_{a,N_h}|`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- `K_e = (9/8)e^{c'}e^{c}(1 + 3K_p)`. -/
def eqcKe : ℝ :=
  9 / 8 * Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) *
    Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) * (1 + 3 * M.Kp)

/-- `G = ℓ²e^{K_Z}`. -/
def eqcG : ℝ := M.core.ℓ ^ 2 * Real.exp M.core.KZ

/-- `S₀ = (9/8)G(1 + 3K_p)`. -/
def eqcS0 : ℝ := 9 / 8 * M.eqcG * (1 + 3 * M.Kp)

def eqcKA : ℝ := (1 + 3 * M.core.cGB) * M.eqcKe * M.eqcG / 8

def eqcKW : ℝ :=
  15 / 14 * (M.eqcS0 / 1344 + 8 * (PtCorr2.csN 2 : ℝ) *
      (135 / 8 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * M.eqcG * M.eqcKe)) +
    (PtCorr2.cBn : ℝ) * Q1 2 * (9 / 4 * M.core.cWo * M.core.c * M.eqcG * M.eqcKe) +
    Q1 2 * M.eqcS0 / 1344

def eqcKT : ℝ :=
  2 * M.eqcKe * (M.eqcG / 16 + max (gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
    (16 * M.core.ℓ ^ 2 / 49)) 0 * Real.exp M.core.KZ)

/-- **The constant of the backward chain.** -/
def eqcK : ℝ := M.eqcKA + M.eqcKW + M.eqcKT

theorem eqcKe_nonneg : 0 ≤ M.eqcKe := by
  unfold eqcKe; have := M.Kp_nonneg; positivity

theorem eqcG_nonneg : 0 ≤ M.eqcG := by unfold eqcG; positivity

theorem eqcS0_nonneg : 0 ≤ M.eqcS0 := by
  unfold eqcS0; have := M.eqcG_nonneg; have := M.Kp_nonneg; positivity

theorem eqcKA_nonneg : 0 ≤ M.eqcKA := by
  unfold eqcKA
  have := M.eqcG_nonneg; have := M.eqcKe_nonneg
  have : 0 ≤ M.core.cGB := M.core.consts_nonneg.2.2.2.2.2.2.2.2.1
  positivity

theorem eqcKT_nonneg : 0 ≤ M.eqcKT := by
  unfold eqcKT
  have := M.eqcG_nonneg; have := M.eqcKe_nonneg
  have : 0 ≤ max (gbKb L M.core.ℓ (cmu ((L : ℝ) ^ 2) M.core.cm) (16 * M.core.ℓ ^ 2 / 49)) 0 :=
    le_max_right _ _
  positivity

/-- `1/|Z_{n+1}| ≤ e^{K_Z}θ_n` along `D_ε`. -/
theorem eqc_zinv_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {n : ℕ} (hn : n ≤ Nh) :
    (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (n + 1))⁻¹ ≤
      Real.exp M.core.KZ * thJ R m b μ₀ n := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hZ0, hZl⟩ :=
    (M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ₀ hD n hn
  have hg := (hD n hn).1
  have hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 ≤ 1 := (hD n hn).2.1.trans M.eps_le
  have hZp : 0 < ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ :=
    norm_pos_iff.2 hZ0
  have hinv := inv_normZ_leS hZp hg hb hZl
  have hKZ : 0 ≤ M.core.KZ := M.KZ_nonneg
  have he : Real.exp (M.core.KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) ≤
      Real.exp M.core.KZ :=
    Real.exp_le_exp.2 (by nlinarith)
  have hθ : 0 ≤ thJ R m b μ₀ n := Real.rpow_nonneg (div_pos hg hb).le _
  show ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖⁻¹ ≤ _
  exact hinv.trans (mul_le_mul_of_nonneg_right he hθ)

/-- `ǧ_k ≤ ǧ_n` for `k ≤ n ≤ N_h` along `D_ε`. -/
theorem eqc_g_mono {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {k : ℕ} :
    ∀ d : ℕ, k + d ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + d)).1
  | 0, _ => le_rfl
  | d + 1, h => (eqc_g_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD d (by omega)).trans
      (M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (k + d) (by omega))

/-- `θ_k ≤ θ_n` for `k ≤ n ≤ N_h`. -/
theorem eqc_thJ_mono {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {k n : ℕ} (hkn : k ≤ n) (hn : n ≤ Nh) :
    thJ R m b μ₀ k ≤ thJ R m b μ₀ n := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have h := M.eqc_g_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := k) (n - k) (by omega)
  rw [show k + (n - k) = n by omega] at h
  unfold thJ
  exact Real.rpow_le_rpow (div_pos (hD k (by omega)).1 hb).le
    (div_le_div_of_nonneg_right h hb.le) (by norm_num)

/-- `|β^P_k| ≤ (1 + 3K_p)bθ_k` for `1 ≤ k < N_h` (the reference vertex `zV0 b`). -/
theorem eqc_bt_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) (P : Obs2.ObsPts 2 L N) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < Nh) :
    ‖bt2 R P (zV0 b) m b μ₀ k‖ ≤ (1 + 3 * M.Kp) * b * thJ R m b μ₀ k := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  have hmn : m * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hz := zA_le_two (by linarith only [hL2]) hmn
  have hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := (hD k hk.le).2.1.trans M.eps_le
  have h := norm_bt2_le_hLam R hb M.Kp_nonneg hl hk (hD k hk.le).1.le (by linarith)
  rwa [cdd_bt2_zV0 R P m b μ₀ hk1] at h

set_option maxHeartbeats 4000000 in
/-- **The restart envelope relative to `θ`**: `M_i ≤ K_e·R_l·b·θ_{ms+i}` for `ms + i ≤ N_h`. -/
theorem eqc_env_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (o' : Obs2.ObsSt .two L N) (h0 : o'.IsObs)
    {ms : ℕ} (hms0 : 0 < ms) (hmsN : ms < Nh) {M₀ Rl : ℝ} (hRl : 0 ≤ Rl)
    (hrel : M₀ ≤ Rl * ‖bt2 R P (zV0 b) m b μ₀ ms‖) {i : ℕ} (hi : ms + i ≤ Nh) :
    ctEnv R m b μ₀ P ms o' M₀ i ≤ M.eqcKe * Rl * b * thJ R m b μ₀ (ms + i) := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set Cm := Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) with hCm
  set c := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε) with hc
  have hmu := zV0_mua_ne hb
  have hKp := M.Kp_nonneg
  set Pf := ∏ l ∈ range i, ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ms (ms + l)‖
    with hPf
  have hE : ctEnv R m b μ₀ P ms o' M₀ i = M₀ * Pf := rfl
  have hpc := M.cw4_prod_cmpD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV0 b) o' h0
    (k := ms) (j := i) hi
  have hPf0 : 0 ≤ Pf := prod_nonneg fun _ _ => norm_nonneg _
  have hec : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  have hθmono := fun k (hk : k ≤ ms + i) =>
    M.eqc_thJ_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hk hi
  -- the reduction to a product of reference factors of length `i'` and a final `9/8`
  have key : ∀ i' : ℕ, i' ≤ i → ms + i' < Nh →
      ∏ l ∈ range i, ‖1 - nn2 R P (zV0 b) m b μ₀ (ms + l)‖ ≤
        9 / 8 * ∏ l ∈ range i', ‖1 - nn2 R P (zV0 b) m b μ₀ (ms + l)‖ →
      ctEnv R m b μ₀ P ms o' M₀ i ≤ M.eqcKe * Rl * b * thJ R m b μ₀ (ms + i) := by
    intro i' hi' hi'N hprod
    have hra := M.cw2_ratioD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV0 b) hmu
      (k := ms) (j := i') (by omega)
    have hβ := M.eqc_bt_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P (k := ms + i') (by omega) hi'N
    set Pn := ∏ l ∈ range i', ‖1 - nn2 R P (zV0 b) m b μ₀ (ms + l)‖
    have hPn0 : 0 ≤ Pn := prod_nonneg fun _ _ => norm_nonneg _
    set βs := ‖bt2 R P (zV0 b) m b μ₀ ms‖
    have hβs0 : 0 ≤ βs := norm_nonneg _
    -- `βs·Pn ≤ e^c|β_{ms+i'}|`
    have h1 : βs * Pn ≤ Real.exp c * ‖bt2 R P (zV0 b) m b μ₀ (ms + i')‖ := by
      have := mul_le_mul_of_nonneg_left hra (Real.exp_pos c).le
      calc βs * Pn = Real.exp c * (Real.exp (-c) * βs * Pn) := by
            rw [← mul_assoc, ← mul_assoc, hec, one_mul]
        _ ≤ _ := this
    have hθ := hθmono (ms + i') (by omega)
    have hθ0 : 0 ≤ thJ R m b μ₀ (ms + i') :=
      Real.rpow_nonneg (div_pos (hD (ms + i') (by omega)).1 hb).le _
    have h2 : ‖bt2 R P (zV0 b) m b μ₀ (ms + i')‖ ≤
        (1 + 3 * M.Kp) * b * thJ R m b μ₀ (ms + i) :=
      hβ.trans (mul_le_mul_of_nonneg_left hθ (by positivity))
    rw [hE]
    have h3 : M₀ * Pf ≤ Rl * βs * (Cm * (9 / 8 * Pn)) :=
      mul_le_mul hrel (hpc.trans (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le)) hPf0
        (mul_nonneg hRl hβs0)
    have h4 : Rl * βs * (Cm * (9 / 8 * Pn)) = 9 / 8 * Cm * Rl * (βs * Pn) := by ring
    rw [h4] at h3
    have h5 : βs * Pn ≤ Real.exp c * ((1 + 3 * M.Kp) * b * thJ R m b μ₀ (ms + i)) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos c).le)
    have h6 := mul_le_mul_of_nonneg_left h5
      (show 0 ≤ 9 / 8 * Cm * Rl from
        mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hRl)
    refine h3.trans (h6.trans (le_of_eq ?_))
    unfold eqcKe; ring
  rcases Nat.lt_or_ge (ms + i) Nh with hlt | hge
  · refine key i le_rfl hlt ?_
    have : 0 ≤ ∏ l ∈ range i, ‖1 - nn2 R P (zV0 b) m b μ₀ (ms + l)‖ :=
      prod_nonneg fun _ _ => norm_nonneg _
    linarith
  · have hiN : ms + i = Nh := le_antisymm hi hge
    have hi1 : 1 ≤ i := by omega
    refine key (i - 1) (by omega) (by omega) ?_
    obtain ⟨-, -, hl⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV0 b)
    obtain ⟨q, -, -, hl⟩ := hl
    have hlast : ‖1 - nn2 R P (zV0 b) m b μ₀ (ms + (i - 1))‖ ≤ 9 / 8 := by
      have h1 := (hl (ms + (i - 1)) (by omega)).1
      exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    rw [show i = (i - 1) + 1 by omega, prod_range_succ, show i - 1 + 1 - 1 = i - 1 by omega]
    have : 0 ≤ ∏ l ∈ range (i - 1), ‖1 - nn2 R P (zV0 b) m b μ₀ (ms + l)‖ :=
      prod_nonneg fun _ _ => norm_nonneg _
    nlinarith

/-- The flow validity along `D_ε` (as in `nb_gam_back_top`). -/
theorem eqc_valid {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) :
    (∀ j < Nh, ValidAt (R.withMsq m) j) ∧ ValidAtL (R.withMsq m) Nh := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := M.flow
  exact (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm

theorem eqc_rho {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hRρ : R.ρ = M.core.ρ) (m : ℝ) : 0 ≤ (R.withMsq m).ρ ∧ (R.withMsq m).ρ ≤ 1 / 8 := by
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  exact ⟨by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le,
    by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'⟩

/-- `‖Γ_k‖ ≤ (G/16)θ_k` for `k ≤ N_h`. -/
theorem eqc_gamT_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {k : ℕ} (hk : k ≤ Nh) :
    ‖gamT R m b μ₀ k‖ ≤ M.eqcG / 16 * thJ R m b μ₀ k := by
  obtain ⟨hV, hVL⟩ := M.eqc_valid R hP hi0 hRℓ hRA hRρ hN2 hNh hm
  have h1 := norm_gamT_le_k R hP (b := b) (μ₀ := μ₀) hV hVL hk
  have h2 := M.eqc_zinv_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hk
  refine h1.trans ?_
  rw [hRℓ]
  have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ M.core.ℓ ^ 2 / 16 by positivity)
  refine this.trans (le_of_eq ?_)
  unfold eqcG; ring

/-- `s_k² ≤ (9/8)Gθ_k` for `k ≤ N_h`. -/
theorem eqc_histS_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {k : ℕ} (hk : k ≤ Nh) :
    histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 ≤
      9 / 8 * M.eqcG * thJ R m b μ₀ k := by
  obtain ⟨hρ0, hρ8⟩ := M.eqc_rho R hRρ m
  have h1 := histS_sq_le_z (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k hρ0 hρ8
  have h2 := M.eqc_zinv_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hk
  refine h1.trans ?_
  have eℓ : (R.withMsq m).ℓ ^ 2 = M.core.ℓ ^ 2 := by
    rw [show (R.withMsq m).ℓ = R.ℓ from rfl, hRℓ]
  rw [eℓ]
  have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 9 / 8 * M.core.ℓ ^ 2 by positivity)
  refine this.trans (le_of_eq ?_)
  unfold eqcG; ring

/-- `‖C_k(a, a)‖ ≤ s_k²/14` for `k ≤ N_h`. -/
theorem eqc_cov_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ} (a : Lam 2 L N) {k : ℕ} (hk : k ≤ Nh) :
    ‖Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k a a‖ ≤
      histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 / 14 := by
  obtain ⟨hV, hVL⟩ := M.eqc_valid R hP hi0 hRℓ hRA hRρ hN2 hNh hm
  obtain ⟨hρ0, hρ8⟩ := M.eqc_rho R hRρ m
  have hP' : (R.withMsq m).P = Pc := hP
  have e1 : Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k a a =
      gamT R m b μ₀ k := by
    have := histCovO_transl (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hP' k a 0 0
    rw [zero_add] at this
    rw [this]
    unfold Obs2.histCovO gamT GamInt
    rw [stCov_eq_dData (R.withMsq m) hP' _ le_rfl]
    simp [DressedFRD.kmat]
  rw [e1]
  have h1 := norm_gamT_le_k R hP (b := b) (μ₀ := μ₀) hV hVL hk
  have hZ0 := zH_pos (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k
  have hZ1 : 7 / 8 * zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k ≤
      zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (k + 1) := by
    rw [norm_Z_succ]
    have := (one_add_zeta_bds (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k).1
    nlinarith
  have hZ1p : 0 < zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (k + 1) := by
    linarith
  have e : histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 =
      R.ℓ ^ 2 * (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)⁻¹ := by
    unfold PtCorr2.histS; rw [mul_pow, Step2.fscale_sq]; simp only [zH]
    show _ * R.ℓ ^ 2 = _; ring
  have hi : (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (k + 1))⁻¹ ≤
      8 / 7 * (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)⁻¹ := by
    rw [inv_le_comm₀ hZ1p (by positivity), mul_inv, inv_div, inv_inv]
    linarith
  have h1' : ‖gamT R m b μ₀ k‖ ≤
      R.ℓ ^ 2 / 16 * (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (k + 1))⁻¹ := h1
  rw [e]
  have := mul_le_mul_of_nonneg_left hi (show 0 ≤ R.ℓ ^ 2 / 16 by positivity)
  nlinarith

/-- `2 ≤ c` of the master construction. -/
theorem eqc_c_ge {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) : 2 ≤ M.core.c := by
  obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  exact hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂

/-- The transient part of the envelope inequality: `8c_N(k + 120B_k(cε)w) ≤ S/1344` and
`c_B w ≤ S/1344`. -/
theorem eqc_trans_le {k w S : ℝ} (hk : 0 ≤ k) (hw : 0 ≤ w) (hc : 0 ≤ M.core.c)
    (hε : 0 ≤ M.core.ε)
    (hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤ S) :
    8 * (PtCorr2.csN 2 : ℝ) * (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) ≤ S / 1344 ∧
      (PtCorr2.cBn : ℝ) * w ≤ S / 1344 := by
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  have hcP : 0 ≤ M.core.cP := by
    show 0 ≤ (cbnC : ℝ) * M.core.Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := M.core.hCpf L; positivity
  have hC : (PtCorr2.cBn : ℝ) ≤ M.core.rdtC := by
    show (PtCorr2.cBn : ℝ) ≤ (cbnC : ℝ) * (1280 * Obs2.locK 2 ^ 2 * (8 / (7 * L)) + 1)
    have h1 : (0 : ℝ) ≤ 1280 * Obs2.locK 2 ^ 2 * (8 / (7 * L)) := by positivity
    have h2 : (PtCorr2.cBn : ℝ) = (cbnC : ℝ) := rfl
    rw [h2]
    have h3 : (0 : ℝ) ≤ cbnC := Nat.cast_nonneg _
    nlinarith
  have hΓ : M.core.rdtΓ = 8 * (PtCorr2.csN 2 : ℝ) * (120 * M.core.Bk * (M.core.c * M.core.ε)) +
      M.core.rdtC + 5 * M.core.cP * (M.core.c * M.core.ε) := rfl
  have hcs : (0 : ℝ) ≤ PtCorr2.csN 2 := Nat.cast_nonneg _
  have hcb : (0 : ℝ) ≤ PtCorr2.cBn := Nat.cast_nonneg _
  have hce : 0 ≤ M.core.c * M.core.ε := mul_nonneg hc hε
  have hC0 : 0 ≤ M.core.rdtC := hcb.trans hC
  have e1 : 0 ≤ 8 * (PtCorr2.csN 2 : ℝ) * (120 * M.core.Bk * (M.core.c * M.core.ε)) * w := by
    positivity
  have e2 : 0 ≤ M.core.rdtC * w := mul_nonneg hC0 hw
  have e3 : 0 ≤ 5 * M.core.cP * (M.core.c * M.core.ε) * w := by positivity
  have e4 : (PtCorr2.cBn : ℝ) * w ≤ M.core.rdtC * w := mul_le_mul_of_nonneg_right hC hw
  have e5 : 0 ≤ 8 * (PtCorr2.csN 2 : ℝ) * k := by positivity
  have hrw : M.core.rdtΓ * w = 8 * (PtCorr2.csN 2 : ℝ) * (120 * M.core.Bk * (M.core.c * M.core.ε)) * w +
      M.core.rdtC * w + 5 * M.core.cP * (M.core.c * M.core.ε) * w := by rw [hΓ]; ring
  constructor
  · have : 8 * (PtCorr2.csN 2 : ℝ) * (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) =
        8 * (PtCorr2.csN 2 : ℝ) * k +
          8 * (PtCorr2.csN 2 : ℝ) * (120 * M.core.Bk * (M.core.c * M.core.ε)) * w := by ring
    rw [this]; linarith
  · linarith

set_option maxHeartbeats 4000000 in
/-- **The `K`/`𝒲` part `G_{ms+i}` relative to `θ`**: `G_{ms+i} ≤ eqcKW·R_l·bθ_{N_h}²`. -/
theorem eqc_gw_le {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    {i : ℕ} (hi : ms + i ≤ Nh) :
    M.ctGw R m b μ₀ P ms o' M₀ k w i ≤ M.eqcKW * (Rl * (b * thJ R m b μ₀ Nh ^ 2)) := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hc2 := M.eqc_c_ge R hP hi0 hRℓ hRA hRρ hN2 hNh hm
  have hc0 : 0 ≤ M.core.c := by linarith
  have hε : 0 ≤ M.core.ε := (hD 0 (Nat.zero_le _)).1.le.trans (hD 0 (Nat.zero_le _)).2.1
  obtain ⟨-, -, -, -, -, hcWo, hBk, -, -, -⟩ := M.core.consts_nonneg
  obtain ⟨hρ0, hρ8⟩ := M.eqc_rho R hRρ m
  have hKp := M.Kp_nonneg
  have hG := M.eqcG_nonneg
  have hKe := M.eqcKe_nonneg
  set T := thJ R m b μ₀ Nh with hTd
  have hT0 : 0 ≤ T := Real.rpow_nonneg (div_pos (hD Nh le_rfl).1 hb).le _
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + i)).1 with hgd
  have hg0 : 0 < g := (hD (ms + i) hi).1
  have hg1 : g ≤ 1 := (hD (ms + i) hi).2.1.trans M.eps_le
  set s2 := histS (R.withMsq m) (ms + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 with hs2d
  have hs0 := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (ms + i)
  have hs2p : 0 < s2 := by positivity
  have hθi := M.eqc_thJ_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hi le_rfl
  have hs2 : s2 ≤ 9 / 8 * M.eqcG * T :=
    (M.eqc_histS_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hi).trans
      (mul_le_mul_of_nonneg_left hθi (by positivity))
  set E := ctEnv R m b μ₀ P ms o' M₀ i with hEd
  have hE0 : 0 ≤ E := mul_nonneg hM0 (prod_nonneg fun _ _ => norm_nonneg _)
  have hE : E ≤ M.eqcKe * Rl * b * T :=
    (M.eqc_env_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o' h0 hms0 hmsN hRl hrel hi).trans
      (mul_le_mul_of_nonneg_left hθi (by positivity))
  set Eb := M.eqcKe * Rl * b * T with hEbd
  have hEb0 : 0 ≤ Eb := hE0.trans hE
  set Sb := 9 / 8 * M.eqcG * T with hSbd
  have hsE : s2 * E ≤ Sb * Eb := mul_le_mul hs2 hE hE0 (by positivity)
  have hcg : M.core.c * g ≤ M.core.c := by nlinarith
  have hcg0 : 0 ≤ M.core.c * g := by positivity
  have hcg2 : (M.core.c * g) ^ 2 ≤ M.core.c ^ 2 := pow_le_pow_left₀ hcg0 hcg 2
  -- the `K` envelope
  set KKb := (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) +
    15 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * (Sb * Eb) with hKKbd
  have hkw0 : 0 ≤ k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w := by positivity
  have hKK : M.ctKK R m b μ₀ P ms o' M₀ k w i ≤ KKb := by
    show (8 / 15) ^ i * (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) +
      15 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s2 * E) ≤ KKb
    have a1 : (8 / 15 : ℝ) ^ i * (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) ≤
        k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w :=
      mul_le_of_le_one_left hkw0 (pow_le_one₀ (by norm_num) (by norm_num))
    have a2 : 15 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s2 * E) ≤
        15 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * (Sb * Eb) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcg2 (by positivity)) hsE (by positivity)
        (by positivity)
    linarith
  have hKKb0 : 0 ≤ KKb := by positivity
  -- the `𝒲` envelope
  set WWb := M.core.cWo * M.core.c * (2 * (Sb * Eb)) + w with hWWbd
  have hWW : M.ctWW R m b μ₀ P ms o' M₀ w i ≤ WWb := by
    show M.core.cWo * (M.core.c * g) * (2 * s2 * E) + (1 / 6) ^ i * w ≤ WWb
    have a1 : (1 / 6 : ℝ) ^ i * w ≤ w :=
      mul_le_of_le_one_left hw (pow_le_one₀ (by norm_num) (by norm_num))
    have a2 : M.core.cWo * (M.core.c * g) * (2 * s2 * E) ≤
        M.core.cWo * M.core.c * (2 * (Sb * Eb)) := by
      have : 2 * s2 * E = 2 * (s2 * E) := by ring
      rw [this]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcg (by linarith)) (by linarith)
        (by positivity) (by positivity)
    linarith
  -- the covariance ratio
  have hC := M.eqc_cov_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm (b := b) (μ₀ := μ₀) P.a hi
  have hcs : (0 : ℝ) ≤ PtCorr2.csN 2 := Nat.cast_nonneg _
  have hcb : (0 : ℝ) ≤ PtCorr2.cBn := Nat.cast_nonneg _
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  set A := (PtCorr2.csN 2 : ℝ) * (8 * KKb) with hAd
  have hA0 : 0 ≤ A := by positivity
  have hsinv : s2 * ((histS (R.withMsq m) (ms + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2)
      = 1 := by rw [hs2d, inv_pow, mul_inv_cancel₀ hs2p.ne']
  have hGw : M.ctGw R m b μ₀ P ms o' M₀ k w i ≤ 15 / 14 * A + (PtCorr2.cBn : ℝ) * (Q1 2 * WWb) := by
    show (PtCorr2.csN 2 : ℝ) * (8 * M.ctKK R m b μ₀ P ms o' M₀ k w i) +
      ‖Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (ms + i) P.a P.a‖ *
        ((PtCorr2.csN 2 : ℝ) * (8 * M.ctKK R m b μ₀ P ms o' M₀ k w i) *
          (histS (R.withMsq m) (ms + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
      (PtCorr2.cBn : ℝ) * (Q1 2 * M.ctWW R m b μ₀ P ms o' M₀ w i) ≤ _
    set u := (histS (R.withMsq m) (ms + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2
    have hu0 : 0 ≤ u := by positivity
    have b1 : (PtCorr2.csN 2 : ℝ) * (8 * M.ctKK R m b μ₀ P ms o' M₀ k w i) ≤ A :=
      mul_le_mul_of_nonneg_left (by linarith) hcs
    have b2 : ‖Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (ms + i)
        P.a P.a‖ * ((PtCorr2.csN 2 : ℝ) * (8 * M.ctKK R m b μ₀ P ms o' M₀ k w i) * u) ≤
        s2 / 14 * (A * u) :=
      mul_le_mul hC (mul_le_mul_of_nonneg_right b1 hu0) (by
        have : 0 ≤ M.ctKK R m b μ₀ P ms o' M₀ k w i := by
          unfold ctKK; have := hE0; positivity
        positivity) (by positivity)
    have b3 : s2 / 14 * (A * u) = A / 14 := by
      have : s2 / 14 * (A * u) = A / 14 * (s2 * u) := by ring
      rw [this, hsinv, mul_one]
    have b4 : (PtCorr2.cBn : ℝ) * (Q1 2 * M.ctWW R m b μ₀ P ms o' M₀ w i) ≤
        (PtCorr2.cBn : ℝ) * (Q1 2 * WWb) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWW (by linarith)) hcb
    linarith
  -- the transient terms against `S = s_{ms}²M₀`
  set S := histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀ with hSd
  obtain ⟨t1, t2⟩ := M.eqc_trans_le hk hw hc0 hε hM
  have hθs := M.eqc_thJ_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := ms) (n := Nh) (by omega)
    le_rfl
  have hθs0 : 0 ≤ thJ R m b μ₀ ms := Real.rpow_nonneg (div_pos (hD ms (by omega)).1 hb).le _
  have hSS : S ≤ M.eqcS0 * (Rl * (b * T ^ 2)) := by
    have h1 := M.eqc_histS_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (k := ms) (by omega)
    have h2 := M.eqc_bt_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P (k := ms) hms0 hmsN
    have h3 : M₀ ≤ Rl * ((1 + 3 * M.Kp) * b * T) :=
      hrel.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hθs
        (by positivity))) hRl)
    have h1' : histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 ≤
        9 / 8 * M.eqcG * T := h1.trans (mul_le_mul_of_nonneg_left hθs (by positivity))
    have := mul_le_mul h1' h3 hM0 (by positivity)
    refine this.trans (le_of_eq ?_)
    unfold eqcS0; ring
  have hX0 : 0 ≤ Rl * (b * T ^ 2) := by positivity
  -- assemble
  have hfin : 15 / 14 * A + (PtCorr2.cBn : ℝ) * (Q1 2 * WWb) ≤
      15 / 14 * (S / 1344 + 8 * (PtCorr2.csN 2 : ℝ) * (15 * M.core.cWo * M.core.Bk * M.core.c ^ 2 *
        (Sb * Eb))) + (PtCorr2.cBn : ℝ) * Q1 2 * (M.core.cWo * M.core.c * (2 * (Sb * Eb))) +
        Q1 2 * (S / 1344) := by
    have eA : A = 8 * (PtCorr2.csN 2 : ℝ) * (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) +
        8 * (PtCorr2.csN 2 : ℝ) * (15 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * (Sb * Eb)) := by
      rw [hAd, hKKbd]; ring
    have eW : (PtCorr2.cBn : ℝ) * (Q1 2 * WWb) = (PtCorr2.cBn : ℝ) * Q1 2 *
        (M.core.cWo * M.core.c * (2 * (Sb * Eb))) + Q1 2 * ((PtCorr2.cBn : ℝ) * w) := by
      rw [hWWbd]; ring
    rw [eA, eW]
    have := mul_le_mul_of_nonneg_left t2 (by linarith : (0 : ℝ) ≤ Q1 2)
    nlinarith
  refine hGw.trans (hfin.trans ?_)
  have eSE : Sb * Eb = 9 / 8 * M.eqcG * M.eqcKe * (Rl * (b * T ^ 2)) := by
    rw [hSbd, hEbd]; ring
  rw [eSE]
  have hdiff : 15 / 14 * (S / 1344 + 8 * (PtCorr2.csN 2 : ℝ) * (15 * M.core.cWo * M.core.Bk *
      M.core.c ^ 2 * (9 / 8 * M.eqcG * M.eqcKe * (Rl * (b * T ^ 2))))) +
      (PtCorr2.cBn : ℝ) * Q1 2 * (M.core.cWo * M.core.c * (2 * (9 / 8 * M.eqcG * M.eqcKe *
        (Rl * (b * T ^ 2))))) + Q1 2 * (S / 1344) - M.eqcKW * (Rl * (b * T ^ 2)) =
      (15 / 14 / 1344 + Q1 2 / 1344) * (S - M.eqcS0 * (Rl * (b * T ^ 2))) := by
    unfold eqcKW; ring
  have : (15 / 14 / 1344 + Q1 2 / 1344) * (S - M.eqcS0 * (Rl * (b * T ^ 2))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

end MasterFacts

end

end Spin2
