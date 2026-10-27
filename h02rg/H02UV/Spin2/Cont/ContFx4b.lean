import Spin2.Cont.ContFx4a
import Spin2.Cont.ContFx3b
import Spin2.Cont.ContEqS8

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`), Phase 2, layer 5b: all nearby pairs under `C_δ`-free thresholds

**`MasterFacts.fx_pairs (hcab) (hB)`**: `eqs_pairs` over `fx_eqc_all_pairs` and `fx_mid_pkg`
(the top case `eqs_top_pkg` is unchanged). The thresholds
* `fxGg r₀ = min(eqsThr(fxLg r₀), eqsThr(eqsLt r₀), eqsThr eqsLs)` for `ǧ_{N_h}`, `a_{ms}` and
  (new, for `hsmN`) `a_{N_h−1}`,
* `fxGm r₀ K_t C₁* = min(eqsThr(fxLm r₀ K_t C₁*), eqsThr(eqsLmt r₀))` for `m L^{2N}`
do not depend on `C_δ`. `C_δ` occurs only in `N ≤ J + C_δ`, in the waiting condition
`(3/4)^{J−ms}·eqsKWa(C_δ) ≤ ǧ_{ms}²` and in the conclusion constant
`2·max(eqcCmid(eqsKA r₀, fxKT(…, fxM0 C₁*, C_δ), C_δ), eqcCtop(eqsKAt r₀, eqsKEt r₀))`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- **The `ǧ` threshold** (`C_δ`-free). -/
def fxGg (r₀ : ℝ) : ℝ :=
  min (eqsThr (M.fxLg r₀)) (min (eqsThr (M.eqsLt r₀)) (eqsThr M.eqsLs))

/-- **The mass threshold** (`C_δ`-free). -/
def fxGm (r₀ Kt C₁w C₁t C₁v C₁m : ℝ) : ℝ :=
  min (eqsThr (M.fxLm r₀ Kt C₁w C₁t C₁v C₁m)) (eqsThr (M.eqsLmt r₀))

theorem fxGg_pos (r₀ : ℝ) : 0 < M.fxGg r₀ :=
  lt_min (eqsThr_pos _) (lt_min (eqsThr_pos _) (eqsThr_pos _))

theorem fxGm_pos (r₀ Kt C₁w C₁t C₁v C₁m : ℝ) : 0 < M.fxGm r₀ Kt C₁w C₁t C₁v C₁m :=
  lt_min (eqsThr_pos _) (eqsThr_pos _)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **All nearby pairs, scalar hypotheses discharged, `C_δ`-free thresholds.** -/
theorem fx_pairs (hcab : 0 < M.k2cab) (hBk : 0 < M.core.Bk) :
    ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ r₀ Kt : ℝ, 0 < r₀ ∧
    ∀ (Cδ : ℕ) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hG : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ M.fxGg r₀)
    (hX : m * (L : ℝ) ^ (2 * N) ≤ M.fxGm r₀ Kt C₁w C₁t C₁v C₁m)
    {ms r J : ℕ} (hk0 : 0 < ms) (hrk : r ≤ ms) (hr1 : 1 ≤ r) (hmsJ : ms < J) (hJN : J ≤ Nh)
    (hJδ : N ≤ J + Cδ) (hz : zA L m ms ≤ M.fxGg r₀)
    (hzN : zA L m (Nh - 1) ≤ M.fxGg r₀)
    (hW : (3 / 4) ^ (J - ms) * M.eqsKWa Cδ ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2)
    (x y : Lam 2 L N)
    (hxJ : ∀ z : Lam 2 L N, supNorm (z - x) ≤ L ^ (ms - r) → J ≤ Obs.coal L (0 : Lam 2 L N) z)
    (hxy : supNorm (y - x) ≤ L ^ (ms - r)),
    |Pconn L N (1 / b) x - Pconn L N (1 / b) y| ≤
      2 * (max (M.eqcCmid (M.eqsKA r₀)
          (M.fxKT r₀ C₁t Λ₁ Λ₂ (M.fxM0 C₁w C₁t C₁v C₁m) Cδ) Cδ)
          (M.eqcCtop (M.eqsKAt r₀) (M.eqsKEt r₀)) *
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0) (R.withMsq m).A r *
          varthJ R m b (b - m) Nh ^ 2) := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.fx_eqc_all_pairs hcab
  obtain ⟨r₀, hr₀, hr₀1, hJ⟩ := M.jet
  obtain ⟨Kt, -, hZTl⟩ := PtCorr2.lastOut_zeroT M.zeroT
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, r₀, Kt, hr₀, ?_⟩
  intro Cδ N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD hG hX ms r J hk0 hrk hr1 hmsJ hJN hJδ hz
    hzN hW x y hxJ hxy
  have hN2 : 2 ≤ N := by omega
  have hkN : ms < Nh := lt_of_lt_of_le hmsJ hJN
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, hCf0, -, -, hρ8, hspl, -⟩ := M.core.hC2
  have hc2 := M.eqc_c_ge R hP hi0 hRℓ hRA hRρ hN2 hNh hm
  have hε0 : 0 ≤ M.core.ε := (hD 0 (Nat.zero_le _)).1.le.trans (hD 0 (Nat.zero_le _)).2.1
  have hGp := (hD Nh le_rfl).1
  have hG1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 := (hD Nh le_rfl).2.1.trans M.eps_le
  have hgmp := (hD ms hkN.le).1
  have hgm1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ≤ 1 := (hD ms hkN.le).2.1.trans M.eps_le
  have hgmG := M.eqs_traj_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hkN.le le_rfl
  have hGg : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ eqsThr (M.fxLg r₀) := hG.trans (min_le_left _ _)
  have hGt : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ eqsThr (M.eqsLt r₀) := hG.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hGs : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ eqsThr M.eqsLs := hG.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzg : zA L m ms ≤ eqsThr (M.fxLg r₀) := hz.trans (min_le_left _ _)
  have hzt : zA L m ms ≤ eqsThr (M.eqsLt r₀) := hz.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hXm : m * (L : ℝ) ^ (2 * N) ≤ eqsThr (M.fxLm r₀ Kt C₁w C₁t C₁v C₁m) :=
    hX.trans (min_le_left _ _)
  have hXt : m * (L : ℝ) ^ (2 * N) ≤ eqsThr (M.eqsLmt r₀) := hX.trans (min_le_right _ _)
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.1.le (by positivity)
  have hthr : ∀ a ∈ M.fxLg r₀, ∀ g' : ℝ, 0 ≤ g' → g' ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 → a * g' ≤ 1 :=
    fun a ha g' h0 h => eqs_le_thr ha h0 (h.trans hGg)
  have hths : ∀ a ∈ M.eqsLs, a * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 := fun a ha => eqs_le_thr ha hGp.le hGs
  have hthm : ∀ a ∈ M.fxLm r₀ Kt C₁w C₁t C₁v C₁m, a * (m * (L : ℝ) ^ (2 * N)) ≤ 1 :=
    fun a ha => eqs_le_thr ha hX0 hXm
  have hG3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
    have : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 ≤ 1 := pow_le_one₀ hGp.le hG1
    calc (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 = (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 := by ring
      _ ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * 1 := mul_le_mul_of_nonneg_left this hGp.le
      _ = (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := mul_one _
  have hg3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 := by
    have : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 ≤ 1 := pow_le_one₀ hgmp.le hgm1
    calc (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3 = (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 := by ring
      _ ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * 1 := mul_le_mul_of_nonneg_left this hgmp.le
      _ = (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 := mul_one _
  -- the shared hypotheses
  have hρ0R : 0 ≤ R.ρ := by rw [hRρ]; exact hρpos.le
  have hK := hZTl N (R.withMsq m) hP hρ0R (le_of_eq hRρ) hm.1 hm.2 Nh hNh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))
  have f1 := hthm (2 * Kt) (by unfold fxLm; simp)
  have hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 := by
    have e : 2 * Kt * (m * (L : ℝ) ^ (2 * N)) = 2 * (Kt * m * (L : ℝ) ^ (2 * N)) := by ring
    linarith
  have f2 := hthm (8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) (by unfold fxLm; simp)
  have hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    rw [mul_assoc]; exact f2
  have f3 := hthr (2 * (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
      9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
      cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3)) (by unfold fxLg; simp) _ hGp.le le_rfl
  have hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
      9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
      cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2 := by
    rw [mul_assoc] at f3; linarith
  have f4 := hthr (2 * M.core.Cf / M.core.ρ) (by unfold fxLg; simp) _ hGp.le le_rfl
  have hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ := by
    have := eqs_le_of_div hρpos (show 2 * M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 / M.core.ρ * 1 ≤ 1 by
      rw [mul_one, mul_div_right_comm]; exact f4)
    rw [mul_one] at this; linarith [show 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) = 2 * M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 by ring]
  have f5 := hthr (16 * cM * M.core.ℓ ^ 2 * M.core.Cf) (by unfold fxLg; simp) _ hGp.le le_rfl
  have hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1 / 2 := by
    have e : 16 * cM * M.core.ℓ ^ 2 * M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 =
        2 * (8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) := by ring
    linarith
  have f6 := hthr (PtCorr2.cRho L * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL)
    (by unfold fxLg; simp) _ hGp.le le_rfl
  have hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1 := by
    rw [← mul_assoc]; exact f6
  have f7 := hthr (4 * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL / r₀ ^ 2)
    (by unfold fxLg; simp) _ hGp.le le_rfl
  have hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2 := by
    have := eqs_le_of_div (by positivity : (0 : ℝ) < r₀ ^ 2)
      (show 4 * cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 / r₀ ^ 2 * 1 ≤ 1 by
        rw [mul_one, mul_div_right_comm]; exact f7)
    rw [mul_one, mul_assoc] at this; exact this
  have f8 := hthr (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL / r₀)
    (by unfold fxLg; simp) _ hGp.le le_rfl
  have hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀ := by
    have := eqs_le_of_div hr₀ (show cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 / r₀ * 1 ≤ 1 by
        rw [mul_one, mul_div_right_comm]; exact f8)
    rwa [mul_one] at this
  have hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2 := by
    intro j hj
    have h := hthr (2 * max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0)
      (by unfold fxLg; simp) _ (hD j hj).1.le (M.eqs_traj_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hj le_rfl)
    rw [mul_assoc] at h; linarith
  have hspl' : SplitSmall R.P L R.ρ := by rw [hP, hRρ]; exact hspl
  have hKp := M.Kp_nonneg
  have hz0 := zA_nonneg L hm.1.le ms
  have fK1 := hthr (4 * M.Kp) (by unfold fxLg; simp) _ hgmp.le hgmG
  have fK2 := eqs_le_thr (l := M.fxLg r₀) (a := 4 * M.Kp) (by unfold fxLg; simp) hz0 hzg
  have hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) := by positivity
  have hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2 := by linarith
  -- `hsmN` at `N_h − 1` (the new `r`-free input of `fx_T6_mid`)
  have hzN0 := zA_nonneg L hm.1.le (Nh - 1)
  have hzNg : zA L m (Nh - 1) ≤ eqsThr (M.fxLg r₀) := hzN.trans (min_le_left _ _)
  have fN1 := hthr (4 * M.Kp) (by unfold fxLg; simp) _ (hD (Nh - 1) (by omega)).1.le
    (M.eqs_traj_mono R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (show Nh - 1 ≤ Nh by omega) le_rfl)
  have fN2 := eqs_le_thr (l := M.fxLg r₀) (a := 4 * M.Kp) (by unfold fxLg; simp) hzN0 hzNg
  have hsmN : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Nh - 1)).1 + zA L m (Nh - 1)) ≤
      1 / 2 := by linarith
  have hcx0 : 0 ≤ cx M.core.κ M.core.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id M.core.hC2
    unfold cx; exact (div_pos (by linarith) (by linarith)).le
  have fr := hthr (4 * M.core.A ^ 4 * cx M.core.κ M.core.cT) (by unfold fxLg; simp) _ hgmp.le hgmG
  have hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg3 hcx0)
      (by positivity : (0 : ℝ) ≤ M.core.A ^ 4)
    have e : 4 * M.core.A ^ 4 * cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 =
        4 * (M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1)) := by ring
    have : 0 ≤ M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) := by positivity
    linarith
  have fg := hthr (2688 * M.core.rdtC * M.core.cWo * M.core.c) (by unfold fxLg; simp) _ hgmp.le hgmG
  have hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * 2) ≤ 1 / 1344 := by
    have e : 2688 * M.core.rdtC * M.core.cWo * M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 =
        1344 * (M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * 2)) := by ring
    linarith
  have fv := hths (cM * M.core.ℓ ^ 2 * (4 * M.core.Cf) + 8 * M.core.ℓ ^ 4 * M.core.Cf)
    (by unfold eqsLs; simp)
  have hvb : cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) + 8 * M.core.ℓ ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1 := by
    have e : (cM * M.core.ℓ ^ 2 * (4 * M.core.Cf) + 8 * M.core.ℓ ^ 4 * M.core.Cf) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 =
        cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) + 8 * M.core.ℓ ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) := by ring
    linarith
  have fw := hths (2 * M.core.Cf) (by unfold eqsLs; simp)
  have hCf : 0 ≤ M.core.Cf := M.flow.2.2.2.2.2.2.2.2.2.2.1
  have hwb : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2) ≤ 1 := by
    have h2 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by rw [sq]; exact mul_le_of_le_one_right hGp.le hG1
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * M.core.Cf)
    have e : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2) = 2 * M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 := by ring
    linarith
  have fu := hths (5 / 4 * (M.core.A ^ 4 * (M.core.Cf + M.core.cKL))) (by unfold eqsLs; simp)
  have hcKL := M.cKL_nonneg
  have hu3 : M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 + M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 4 / 5 := by
    have := mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hG3 hCf)
      (M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (by positivity : (0 : ℝ) ≤ M.core.A ^ 4)
    have e : 5 / 4 * (M.core.A ^ 4 * (M.core.Cf + M.core.cKL)) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 =
        5 / 4 * (M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 + M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) := by ring
    linarith
  have hseed := M.core.topSeedD N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD hs1 hs2 hvb
    hwb hu3
  -- the waiting conditions
  have hcpos : 0 < M.core.c := by linarith
  have hΓ : 0 < M.core.rdtΓ := M.core.eqs_rdtΓ_pos hcpos.le hε0
  have hTw0 : 0 ≤ M.eqsTw := by unfold eqsTw; positivity
  have hTk0 : 0 ≤ M.eqsTk := by unfold eqsTk; positivity
  have hA0 : 0 < M.core.A := by linarith [M.core.hA2]
  have hK20 : 0 ≤ M.eqsK2 := by
    have := M.core.consts_nonneg.2.2.2.2.2.1
    unfold eqsK2 zabIota; positivity
  have hθ0 : 0 ≤ kθ0 L M.core.A M.core.C₀o M.core.ηo := by
    unfold kθ0
    exact mul_nonneg M.core.hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hTh0 := M.eqsTh_pos 0
  have hThC := M.eqsTh_pos Cδ
  have hKWt0 : 0 ≤ M.eqsKWt := by unfold eqsKWt; positivity
  have hKW0 : 0 ≤ M.eqsKW Cδ := by unfold eqsKW; positivity
  have hKWmid : (3 / 4) ^ (J - ms) * M.eqsKW Cδ ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (by unfold eqsKWa; linarith) (by positivity)) hW
  have hKWtop : (3 / 4) ^ (J - ms) * M.eqsKWt ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (by unfold eqsKWa; linarith) (by positivity)) hW
  -- the packages
  have hmidP : ∀ p q : Lam 2 L N, EqGood ms (L ^ (ms - r)) p q → J ≤ Obs.coal L (0 : Lam 2 L N) p →
      J ≤ Obs.coal L (0 : Lam 2 L N) q → Obs.coal L (0 : Lam 2 L N) q ≤ Nh →
      M.FxMidPkg C₁w C₁t C₁v C₁m Λ₁ Λ₂ R m b Nh r₀ p q ms r Cδ (M.eqsKA r₀)
        (M.fxKT r₀ C₁t Λ₁ Λ₂ (M.fxM0 C₁w C₁t C₁v C₁m) Cδ) :=
    fun p q hpq hp hq hqN => M.fx_mid_pkg (Kt := Kt) R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD p q hk0
      (by omega) hqN hrk hpq.2 hr₀ hC₁w hC₁t hC₁v hC₁m hcab hBk Cδ hq hJδ hGg hzg hXm hKWmid
  have htopP : ∀ p q : Lam 2 L N, EqGood ms (L ^ (ms - r)) p q → J ≤ Obs.coal L (0 : Lam 2 L N) p →
      Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) q → M.EqcTopPkg R m b Nh r₀ p q ms r (M.eqsKAt r₀)
        (M.eqsKEt r₀) :=
    fun p q hpq hp hq => M.eqs_top_pkg R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD p q hk0 hkN hrk hpq.2 hr₀
      hcab hBk hJN hGt hzt hXt hKWtop
  exact hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
    hsmall hsmN hspl' hm.1 hm.2 hseed hvb hwb hk0 hkN hrk hr1 hs0 hs hreg hg hmsJ hJδ hmidP htopP x y
    hxJ hxy

end MasterFacts

end

end Spin2
