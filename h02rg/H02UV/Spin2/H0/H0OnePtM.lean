import Spin2.H0.H0OnePt
import Spin2.H0.MasterH0Slack
import Spin2.Gam.LastKRem1
import Spin2.Gam.LastOneRem
import Spin2.H0.MasterH0Pair
import Spin2.Gam.GamTopFull
import Spin2.Gam.GamRemLast

/-!
# Route (a1), input (i) discharged: `Re r ≥ 0` at the upper window end from the one-point chain

`r = 1 − b⟨ψ̄_0ψ_0⟩` along a windowed trajectory (any sign of `h`):

* `r = γ_{a,N} + n_aΩ` exactly (`onePt_split_win`);
* `|γ_{a,N} − ϑ_{N_h}| ≤ (F' + c_L)ϑ_{N_h}ǧ_{N_h}` (`gamNa_near_of`: `MagAt`, `GamLastRel` with the sharp
  vertex bound `K_β = 4`);
* `n_aΩ = sA Ω/sE Ω` with `sE Ω = U e^{u^{obs,∅}_N − u_N}` (`sE_zZm`), `n = m²|Λ|U`,
  `Re n ≥ L⁴μ_{N_h} − S` (the mass flow of `h0MassAt`), `sA Ω = εF_a − c·c2F_a` (`LastOneRem`,
  `P₀ = 1`), `|β_{N−1}|/|Z_N| ≤ (32/7)e^{1/4}ϑ_{N_h}ǧ_{N_h}`: `|n_aΩ| ≤ 22ϑ_{N_h}ǧ_{N_h}/(L⁴μ_{N_h} − S)`;
* hence `Re r ≥ 0` as soon as `44ǧ ≤ L⁴μ_{N_h} − S` and `(F' + c_L)ǧ ≤ 1/2`
  (**`MasterFacts.onePt_re_win`**); with `Re χ > 0` (`h0MassC`) and the Ward identity this gives
  `r` real `≥ 0` (`onept_real_of_re`).

At the upper window end `L⁴μ_{N_h} = L⁴c₁`, `c₁ = (3/4)c_μǧ^c`, the slack is `≤ (5/4)(c_ν + 2)ǧ^c` and
`3L⁴c_μ − 5(c_ν + 2) ≥ 5L²` (`cNuLast_win_margin`), so `L⁴c₁ − S ≥ (5/4)L²ǧ^c ≥ 55ǧ^c` (`L ≥ 49`):
**`MasterFacts.h0EndsG`** is `H0EndsConclF` with input (i) replaced by
smallness conditions in `G = (5/4)ǧ^c` (`H0OnePtSmall`); **`thm_multiscale_h0G`**.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- The remainder constant of the two top steps, `max(c_ρ, 2c_BQ₁c_{WL}(9/8)ℓ² + C_fℓ⁴)`
(`TopConcl` for `ρ_{N_h}`, `gamRemNP_le` for `ρ_N`). -/
def h0crL {L : ℕ} [NeZero L] (M : MasterFacts L) : ℝ :=
  max M.core.cρ (2 * ((cBn : ℝ) * Q1 2 * M.core.cWL * (9 / 8 * M.core.ℓ ^ 2)) +
    M.core.Cf * M.core.ℓ ^ 4)

/-- **The smallness conditions of the one-point estimate**, for all `g ∈ [0, G]` (`g` stands for
`ǧ_{N_h}` and `ǧ_{N_h−1}` at the trajectory; `K_A = cKAL … r₀ … 3`,
`c_L = 8(ℓ²e^{K_Z}/14 + h0crL·e^{K_Z})`). -/
def H0OnePtSmall {L : ℕ} [NeZero L] (M : MasterFacts L) (N Nh : ℕ) (m r₀ G : ℝ) : Prop :=
  (∀ g : ℝ, 0 ≤ g → g ≤ G →
    (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) + 9 / 4 * ((cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * g ≤ 1 / 2 ∧
    2 * (M.core.Cf * g) ≤ M.core.ρ ∧
    8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * g) ≤ 1 / 2 ∧
    cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * g) ≤ 1 ∧
    4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * g) ≤ r₀ ^ 2 ∧
    cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * g ≤ r₀ ∧
    M.Kp * (g + zA L m (Nh - 1)) ≤ 1 ∧
    (L : ℝ) ^ 4 * (M.core.Cf * g ^ 2) ≤ 1 / 4 ∧
    M.core.KZ * g ≤ 1 / 4 ∧
    (max (spinMK L M.core.cg M.core.Ke M.core.KZ
        (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
      2 * 4 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 + h0crL M * Real.exp M.core.KZ)) * g ≤ 1 / 2) ∧
  8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 ∧
  h0KT L M.core.ρ * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2

/-- `e^{1/2} < 2`. -/
theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- **A point at coalescence scale one**: `x = (L, L)` (`L ≥ 3`, `N ≥ 2`): `x ≠ 0`, `j_x = 1`. -/
theorem exists_coal_one {L N : ℕ} [NeZero L] (hL : 3 ≤ L) (hN : 2 ≤ N) :
    ∃ x : Lam 2 L N, x ≠ 0 ∧ Obs.coal L (0 : Lam 2 L N) x = 1 := by
  have hLN : L < L ^ N := by
    calc L = L ^ 1 := (pow_one L).symm
      _ < L ^ N := Nat.pow_lt_pow_right (by omega) (by omega)
  have hLN2 : 2 * L ≤ L ^ N := by
    calc 2 * L ≤ L * L := Nat.mul_le_mul_right L (by omega)
      _ = L ^ 2 := (sq L).symm
      _ ≤ L ^ N := Nat.pow_le_pow_right (by omega) hN
  have hval : ((L : ℕ) : ZMod (L ^ N)).val = L := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hLN]
  let x : Lam 2 L N := fun _ => ((L : ℕ) : ZMod (L ^ N))
  refine ⟨x, fun h => ?_, ?_⟩
  · have h0 := congrArg (fun y : Lam 2 L N => ((y : Fin 2 → ZMod (L ^ N)) 0).val) h
    have : ((0 : Lam 2 L N) : Fin 2 → ZMod (L ^ N)) 0 = 0 := rfl
    rw [this, ZMod.val_zero] at h0
    have h1 : ((x : Fin 2 → ZMod (L ^ N)) 0).val = L := hval
    omega
  · have hz : ∀ i, zabs (((0 : Lam 2 L N) - x : Lam 2 L N) i) = L := by
      intro i
      have e : (((0 : Lam 2 L N) - x : Lam 2 L N) i) = -((L : ℕ) : ZMod (L ^ N)) := by
        show (0 : ZMod (L ^ N)) - ((L : ℕ) : ZMod (L ^ N)) = _
        ring
      rw [e, zabs_neg]
      unfold zabs
      rw [hval]
      exact min_eq_left (by omega)
    have hs : supNorm ((0 : Lam 2 L N) - x) = L := by
      unfold supNorm
      have : (fun i => zabs ((((0 : Lam 2 L N) - x : Lam 2 L N) : Fin 2 → ZMod (L ^ N)) i)) =
          fun _ => L := funext hz
      rw [this, Finset.sup_const Finset.univ_nonempty]
    unfold Obs.coal
    rw [hs, Nat.log_eq_iff (Or.inl one_ne_zero)]
    constructor
    · rw [pow_one]; omega
    · rw [show 1 + 1 = 2 by rfl, sq]
      have : 3 * L ≤ L * L := Nat.mul_le_mul_right L hL
      omega

/-- **The window margin**: `3L⁴c_μ − 5(c_ν + 2) ≥ 5L²` (`L ≥ 49`, master `c_m`, `c_με ≤ 1/16`). -/
theorem cNuLast_win_margin {L N : ℕ} [NeZero L] (R : RGPar 2 L N) {cm ε : ℝ} (hL : 49 ≤ L)
    (hcm : cm = 3 * (L : ℝ) ^ 2 * (16 * R.ℓ ^ 2 / 49) + 8 * R.ℓ ^ 2 / 49 + 1)
    (hu : cmu ((L : ℝ) ^ 2) cm * ε ≤ 1 / 16) :
    5 * (cNuLast R ((L : ℝ) ^ 2) cm ε + 2) + 5 * (L : ℝ) ^ 2 ≤
      3 * (L : ℝ) ^ 4 * cmu ((L : ℝ) ^ 2) cm := by
  set Λ : ℝ := (L : ℝ) ^ 2 with hΛ
  set q : ℝ := R.ℓ ^ 2 with hq
  set u : ℝ := cmu Λ cm * ε with hud
  have hL' : (49 : ℝ) ≤ L := by exact_mod_cast hL
  have hΛ0 : 2401 ≤ Λ := by rw [hΛ]; nlinarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hcm0 : 0 < cm := by rw [hcm]; positivity
  have hcmu0 : 0 < cmu Λ cm := by
    unfold cmu; have : 0 < Λ - 1 := by linarith
    positivity
  have hcmuE : cmu Λ cm * (Λ - 1) = 2 * cm := by
    unfold cmu; have : Λ - 1 ≠ 0 := by linarith
    field_simp
  have hL4 : (L : ℝ) ^ 4 = Λ ^ 2 := by rw [hΛ]; ring
  have hN : 5 * (cNuLast R Λ cm ε + 2) = 3200 / 1029 * (Λ ^ 2 * q * u) + 800 / 147 * (Λ ^ 2 * q) +
      (40 / 49 + 1280 / 343) * (Λ * q) + 15 / 7 * q + 10 := by
    unfold cNuLast cNuLs cZ; rw [hud, hq, hΛ]; ring
  have hR : 3 * (L : ℝ) ^ 4 * cmu Λ cm = 6 * Λ * cm + 3 * Λ * cmu Λ cm := by
    rw [hL4]; linear_combination (3 * Λ) * hcmuE
  have hcmΛ : 6 * Λ * cm = 288 / 49 * (Λ ^ 2 * q) + 48 / 49 * (Λ * q) + 6 * Λ := by
    rw [hcm]; ring
  have hP0 : 0 ≤ Λ ^ 2 * q := by positivity
  have h1 : Λ ^ 2 * q * u ≤ Λ ^ 2 * q * (1 / 16) := mul_le_mul_of_nonneg_left hu hP0
  have h2 : 2401 * (Λ * q) ≤ Λ ^ 2 * q := by
    have := mul_le_mul_of_nonneg_right hΛ0 (mul_nonneg (by linarith : (0 : ℝ) ≤ Λ) hq0)
    linarith [show Λ * (Λ * q) = Λ ^ 2 * q by ring]
  have h3 : q ≤ Λ * q := by nlinarith
  have h4 : 0 < 3 * Λ * cmu Λ cm := by positivity
  rw [hN, hR, hcmΛ]
  linarith

/-- **The slack on the window, quantitatively** (`θ = (3/4)c_μ`, `c₁ = θǧ^c`, `m²|Λ| ≤ ǧ^c`): every
`g ≤ ǧ^c + 2p_Wc₁` has `g ≤ (5/4)ǧ^c` and `h0Slack(g) ≤ (c_ν + 2)(5/4)ǧ^c`. -/
theorem h0Slack_le_win {Lr Cf ℓ cNL KT B ρ cμ gc ε mV pW : ℝ} (hCf : 0 ≤ Cf) (hcNL : 0 ≤ cNL)
    (hKT : 0 ≤ KT) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hcμ : 0 < cμ) (hgc : 0 < gc) (hgε : gc ≤ ε)
    (hmV : 0 ≤ mV) (hmg : mV ≤ gc) (hW : 3 / 4 * cμ * (1 + 2 * pW * cμ) < cμ)
    (hε : ε ≤ 4 / 5) (hX : 5 / 4 * h0Xc Lr Cf ℓ KT B ρ * ε ≤ 1) :
    ∀ g : ℝ, 0 ≤ g → g ≤ gc + pW * (3 / 4 * cμ * gc - -(3 / 4 * cμ * gc)) →
      g ≤ 5 / 4 * gc ∧ h0Slack Lr Cf ℓ cNL KT B ρ g mV ≤ (cNL + 2) * (5 / 4 * gc) := by
  intro g hg0 hg
  have hp : 3 / 2 * pW * cμ < 1 / 4 := by
    have h1 : 3 / 2 * pW * cμ * cμ < 1 / 4 * cμ := by nlinarith
    by_contra hc; rw [not_lt] at hc
    have := mul_le_mul_of_nonneg_right hc hcμ.le
    linarith
  have hgG : g ≤ 5 / 4 * gc := by
    have e : pW * (3 / 4 * cμ * gc - -(3 / 4 * cμ * gc)) = 3 / 2 * pW * cμ * gc := by ring
    have := mul_le_mul_of_nonneg_right hp.le hgc.le
    linarith
  refine ⟨hgG, ?_⟩
  have hX0 := h0Xc_nonneg (Lr := Lr) (ℓ := ℓ) hCf hKT hB hρ
  have hG1 : 5 / 4 * gc ≤ 1 := by linarith
  have hS1 := h0Slack_mono (Lr := Lr) (ℓ := ℓ) (cNL := cNL) (B := B) hCf hcNL hKT hB hρ hg0 hgG hmV
    (show mV ≤ 5 / 4 * gc by linarith)
  have hS2 := h0Slack_le_lin (Lr := Lr) (ℓ := ℓ) (cNL := cNL) (KT := KT) (B := B) (ρ := ρ) hCf hKT hB
    hρ (by linarith : (0 : ℝ) ≤ 5 / 4 * gc) hG1
  have hXG : h0Xc Lr Cf ℓ KT B ρ * (5 / 4 * gc) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hgε hX0
    linarith
  have hS3 : (cNL + 1 + h0Xc Lr Cf ℓ KT B ρ * (5 / 4 * gc)) * (5 / 4 * gc) ≤
      (cNL + 2) * (5 / 4 * gc) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 16000000 in
/-- **`Re r ≥ 0` along a windowed trajectory from the one-point chain** (any sign of `h`; one pair
point `x` with `1 ≤ j_x ≤ N_h` is used to read the chain). Inputs: the smallness `H0OnePtSmall` and the window margin `44G ≤ L⁴μ_{N_h} − S`. Outputs: `⟨Z_0⟩ ≠ 0`,
`Re(1 − b⟨ψ̄_0ψ_0⟩) ≥ 0` and `Re χ > 0`. -/
theorem MasterFacts.onePt_re_win {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ : ℝ, 0 < b →
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j)) →
    ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ G : ℝ, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 ≤ G → H0OnePtSmall M N Nh m r₀ G →
      44 * G ≤ (L : ℝ) ^ 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).2.1 -
        h0Slack L M.core.Cf M.core.ℓ (cNuLast (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.ε)
          (h0KT L M.core.ρ) (h0B L M.core.ρ) M.core.ρ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1
          (m * Fintype.card (Lam 2 L N)) →
      Obs.Zb (Suscept.Cov 2 L N m) (VE (V0c b μ) (univ : Finset (Lam 2 L N))) ≠ 0 ∧
      0 ≤ (1 - (b : ℂ) * avg0 L N m b μ (psibar 0 * psi 0)).re ∧
      0 < (∑ y : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi y)).re := by
  set D := M.core with hDd
  obtain ⟨r₀, hr₀, hr₀1, hJ⟩ := M.jet
  refine ⟨r₀, hr₀, hr₀1, ?_⟩
  obtain ⟨-, -, hρ, -, -, -, -, -, -, -, hCf, -, -, hρ8, hspl, H⟩ := D.hC2
  obtain ⟨hKTc0, hZTc⟩ := h0KT_spec D.hZT
  obtain ⟨hBc0, -⟩ := h0B_spec hspl
  set KTc := h0KT L D.ρ with hKTcd
  set Bc := h0B L D.ρ with hBcd
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hb hD x hx h1 hj G hgG hsm
    hmarg
  obtain ⟨hsmg, hmA, hmT⟩ := hsm
  obtain ⟨-, -, -, -, -, -, -, -, -, hval⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh
  obtain ⟨hV, hVL⟩ := hval m hm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by show 0 ≤ R.ρ; rw [hRρ]; exact hρ.le
  have hρ1 : (R.withMsq m).ρ < 1 := by show R.ρ < 1; rw [hRρ]; linarith
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by show R.ρ ≤ 1 / 8; rw [hRρ]; exact hρ8
  have hspl' : SplitSmall (R.withMsq m).P L (R.withMsq m).ρ := by
    show SplitSmall R.P L R.ρ; rw [hP, hRρ]; exact hspl
  have hm0 : 0 < m := hm.1
  have hL7 : 7 ≤ L := by have := D.hL49; omega
  have hℓR : (R.withMsq m).ℓ = D.ℓ := hRℓ
  have hρR : (R.withMsq m).ρ = D.ρ := hRρ
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ with ht
  set out := lastOut (R.withMsq m) Nh t with hout
  set g := (t Nh).1 with hg
  set c := (t Nh).2.1 with hc
  have hg0 : 0 ≤ g := ((hD Nh le_rfl).1).le
  -- the inputs
  obtain ⟨-, -, -, hk0, -, -, hnu, ha⟩ := (D.onePtWin R hP hi0 hRℓ hRA hRρ hN2 hNh hm hb hD).1
  have hnuS := D.hGN N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD
  have hw := hZTc N (R.withMsq m) hP hρ0 (le_of_eq hρR) hm0 hm.2 Nh hNh t
  obtain ⟨z, hz, hzZ⟩ := Zr_real_pos (R.withMsq m) hρ0 hρ1 ((L : ℝ) ^ 2) b μ (Nh + 2)
  have hZz : out.Z = (z : ℂ) := hzZ
  -- the volume
  set V : ℝ := (Fintype.card (Lam 2 L N) : ℝ) with hVd
  have hVc : (Fintype.card (Lam 2 L N) : ℂ) = (V : ℂ) := by simp [hVd]
  have hVL2 : V = ((L : ℝ) ^ 2) ^ (Nh + 1) * (L : ℝ) ^ 2 := by
    have h1 := card_lam_two_eq (L := L) hNh
    have h2 : ((V : ℝ) : ℂ) = ((((L : ℝ) ^ 2) ^ (Nh + 1) * (L : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hVc, h1]; push_cast; ring
    exact_mod_cast h2
  have hVN : (L : ℝ) ^ (2 * N) = V := by rw [hVL2, ← hNh]; ring
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hV0 : 0 < V := by rw [hVL2]; positivity
  -- names
  set A := aFin (Nh + 1) out with hA
  set tr := zmRaw (R.withMsq m) (Nh + 1) out.ζ with htr
  set k0 := k0Fin (Nh + 1) out with hk0d
  set νh := (L : ℂ) ^ (2 * (Nh + 1 + 1)) * out.κ.nu / out.Z with hνh
  set ah : ℂ := (V : ℂ) * A / (z : ℂ) with hah
  set w : ℂ := (m : ℂ) * ((z : ℂ) * tr) with hw'
  set mV := m * V with hmV
  have hmV0 : 0 < mV := mul_pos hm0 hV0
  set n : ℂ := ((m * V : ℝ) : ℂ) * (1 + k0) + ah * w with hn
  set Cf := D.Cf
  set ea := h0ea L Cf D.ℓ g
  set κ0 := h0k0 L Cf g
  set ahi := h0ahi L Cf D.ℓ g
  set cNL := cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε
  have hUeq : 1 + uFin (Nh + 1) out tr = 1 + (k0 + A * tr) := rfl
  -- the bounds in normalised form
  have hEz0 : 0 ≤ h0Ez L Cf g := by unfold h0Ez; have := Real.exp_pos ((L : ℝ) ^ 2 * Cf * g ^ 2); positivity
  have hea0 : 0 ≤ ea := by
    show 0 ≤ h0ea L Cf D.ℓ g; unfold h0ea; positivity
  have hκ00 : 0 ≤ κ0 := by show 0 ≤ h0k0 L Cf g; unfold h0k0; positivity
  have hahi0 : 0 ≤ ahi := by show 0 ≤ h0ahi L Cf D.ℓ g; unfold h0ahi; positivity
  have b_a : ‖ah - νh‖ ≤ ea := by
    have e : ah = (Fintype.card (Lam 2 L N) : ℂ) * A / out.Z := by rw [hVc, hZz]
    rw [e]
    have : ‖(Fintype.card (Lam 2 L N) : ℂ) * aFin (Nh + 1) out / out.Z - νh‖ ≤
        Cf * g * h0Ez L Cf g + (R.withMsq m).ℓ⁻¹ ^ 2 * (h0Ez L Cf g + Cf * g ^ 3) := ha
    rwa [hℓR] at this
  have b_s : ‖νh - (((L : ℝ) ^ 4 * c : ℝ) : ℂ)‖ ≤ cNL * g := by
    have e : (((L : ℝ) ^ 4 * c : ℝ) : ℂ) = (L : ℂ) ^ 4 * ((c : ℝ) : ℂ) := by push_cast; ring
    rw [e]; exact hnuS
  have b_n : ‖νh‖ ≤ Cf * g := hnu
  have b_k : ‖k0‖ ≤ κ0 := hk0
  have b_w : ‖w - 1‖ ≤ KTc * mV := by
    have e : w = ((R.withMsq m).msq : ℂ) * (out.Z * tr) := by rw [hZz]; rfl
    rw [e]
    have h := hw
    rw [hVN] at h
    have e2 : KTc * (R.withMsq m).msq * V = KTc * mV := by
      show KTc * m * V = KTc * (m * V); ring
    linarith only [h, e2.le]
  have b_ah : ‖ah‖ ≤ ahi := by
    have := norm_le_insert' ah νh
    show ‖ah‖ ≤ Cf * g + h0ea L Cf D.ℓ g
    linarith only [this, b_n, b_a]
  have b_η : ‖ah - (((L : ℝ) ^ 4 * c : ℝ) : ℂ)‖ ≤ cNL * g + ea := by
    have e : ah - (((L : ℝ) ^ 4 * c : ℝ) : ℂ) = (ah - νh) + (νh - (((L : ℝ) ^ 4 * c : ℝ) : ℂ)) := by ring
    rw [e]; exact (norm_add_le _ _).trans (by linarith only [b_a, b_s])
  have b_aw : ‖ah * (w - 1)‖ ≤ ahi * (KTc * mV) := by
    rw [norm_mul]; exact mul_le_mul b_ah b_w (norm_nonneg _) hahi0
  -- `Re n` and `|n|`
  have hnre : n.re = mV * (1 + k0.re) + ah.re + (ah * (w - 1)).re := by
    have e : n = ((m * V : ℝ) : ℂ) * (1 + k0) + ah + ah * (w - 1) := by rw [hn]; ring
    rw [e, hmV]; simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.one_re]
  have hk0re := abs_le.1 ((Complex.abs_re_le_norm k0).trans b_k)
  have haw := abs_le.1 ((Complex.abs_re_le_norm (ah * (w - 1))).trans b_aw)
  have har : |ah.re - (L : ℝ) ^ 4 * c| ≤ cNL * g + ea := by
    have := (Complex.abs_re_le_norm (ah - (((L : ℝ) ^ 4 * c : ℝ) : ℂ))).trans b_η
    rwa [Complex.sub_re, Complex.ofReal_re] at this
  have har' := abs_le.1 har
  have hnlo : mV * (1 - κ0) + (L : ℝ) ^ 4 * c - (cNL * g + ea) - ahi * (KTc * mV) ≤ n.re := by
    rw [hnre]
    have q1 := mul_le_mul_of_nonneg_left hk0re.1 hmV0.le
    linarith only [q1, haw.1, har'.1]
  have hnhi : n.re ≤ mV * (1 + κ0) + (L : ℝ) ^ 4 * c + (cNL * g + ea) + ahi * (KTc * mV) := by
    rw [hnre]
    have q2 := mul_le_mul_of_nonneg_left hk0re.2 hmV0.le
    linarith only [q2, haw.2, har'.2]
  have hnn : ‖n‖ ≤ h0nhi L Cf D.ℓ KTc g mV := by
    show ‖n‖ ≤ mV * (1 + κ0) + ahi * (1 + KTc * mV)
    have h1 : ‖((m * V : ℝ) : ℂ) * (1 + k0)‖ ≤ mV * (1 + κ0) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hmV0.le]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by rw [norm_one]; linarith only [b_k]))
        hmV0.le
    have h2 : ‖ah * w‖ ≤ ahi * (1 + KTc * mV) := by
      rw [norm_mul]
      refine mul_le_mul b_ah ?_ (norm_nonneg _) hahi0
      have := norm_le_insert' w 1
      rw [norm_one] at this; linarith only [this, b_w]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hnU : ((m * V : ℝ) : ℂ) * (1 + (k0 + A * tr)) = n := wn2_n_eq hz A tr k0
  have hQ0 : 0 ≤ h0Q L Cf D.ℓ KTc Bc D.ρ g mV := by
    unfold h0Q
    have : 0 ≤ h0nhi L Cf D.ℓ KTc g mV := by linarith only [hnn, norm_nonneg n]
    have hρD : 0 ≤ D.ρ := hρ.le
    positivity
  -- the lower bound of `Re n`
  set S := h0Slack L Cf D.ℓ cNL KTc Bc D.ρ g mV with hSd
  set nlo := (L : ℝ) ^ 4 * c - S with hnlod
  have hg0' : 0 < g := (hD Nh le_rfl).1
  have hG0 : 0 < G := hg0'.trans_le hgG
  have hnlo0 : 0 < nlo := by linarith only [hmarg, hG0]
  have hnre' : nlo ≤ n.re := by
    have hS : S = cNL * g + ea + ahi * (KTc * mV) + mV * (1 + κ0) +
        h0Q L Cf D.ℓ KTc Bc D.ρ g mV := rfl
    have : 0 ≤ mV * (1 + κ0) + mV * (1 - κ0) := by
      have e : mV * (1 + κ0) + mV * (1 - κ0) = 2 * mV := by ring
      rw [e]; exact mul_nonneg (by norm_num) hmV0.le
    rw [hnlod, hS]; linarith only [hnlo, this, hQ0]
  -- `U ≠ 0`, `Re χ > 0`, `⟨Z_0⟩ ≠ 0`
  have hMC := D.h0MassC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hb hD
  obtain ⟨hU, hχ⟩ := hMC.1 (by linarith only [hmarg, hG0, hnlod])
  obtain ⟨hZb, -, -⟩ := D.onePtWinU R hP hi0 hRℓ hRA hRρ hN2 hNh hm hb hD hU
  refine ⟨hZb, ?_, hχ⟩
  obtain ⟨-, hom, -⟩ := D.onePtWin R hP hi0 hRℓ hRA hRρ hN2 hNh hm hb hD
  obtain ⟨hch, hdet⟩ := chainFactors_ne (R.withMsq m) hNh hspl' hm.1 hm.2 hV hVL t
  have hZ : omegaC (Γh (R.withMsq m) 0 t) (Zh (R.withMsq m) 0 t : Alg 2 L N) ≠ 0 := by
    rw [hom]
    exact mul_ne_zero hch (mul_ne_zero (mul_ne_zero hdet (Complex.exp_ne_zero _)) hU)
  have hρ1R : R.ρ < 1 := hρ1
  have hsplR : SplitSmall R.P L R.ρ := hspl'
  -- the exact split
  obtain ⟨hs0, hsplit, hfac⟩ := onePt_split_win R hNh m hρ1R hsplR hm.1 hm.2 hV hVL hL7 hb x hZ
  have hsU := s_eq_of_fac hch hdet (hfac.symm.trans hom)
  have hsmx := hsmg g hg0'.le hgG
  obtain ⟨hsA, hs1, hs2, hs3, hs4, hs5, hsKp, hsEu, hsKZ, hsγ⟩ := hsmx
  have hGl : GlueOut (R.withMsq m) Nh Cf t := (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD).1
  have hδ : ‖zUB R Nh m b μ x - out.u‖ ≤ 1 / 4 :=
    (zUB_sub_u_le R hNh hCf x hGl hρ0 hρ1).trans hsEu
  ------------------------------------------------------------------ the `γ` part
  have hε1 := M.eps_le
  have hKZ := M.KZ_nonneg
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hpairP : ∀ P : Obs2.ObsPts 2 L N, HLam R Nh m b μ (lamHat2 R P (zV b) m b μ) M.Kp :=
    fun P => M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P
  have hrel : ∀ P : Obs2.ObsPts 2 L N, Case2Rel R P (zV b) Nh m b μ M.core.cRel := fun P =>
    M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD P (zV b) (zV_mua_ne hb)
  have hnn2 : ∀ P : Obs2.ObsPts 2 L N, ∀ k < Nh, ‖nn2 R P (zV b) m b μ k‖ ≤ 1 / 8 := by
    intro P k hk
    obtain ⟨-, -, q, -, -, hl'⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD P (zV b)
    exact (hl' k hk).1
  have htop : ∀ P : Obs2.ObsPts 2 L N, Case2TopStep R P (zV b) Nh m b μ := fun P =>
    (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD P).1
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have haz : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  have hNh1 : 1 ≤ Nh := h1.trans hj
  -- the sharp vertex bound at the two top scales
  have hk1 : Nh - 1 < Nh := by omega
  have hmo : (t (Nh - 1)).1 ≤ (t Nh).1 := by
    have := hmono (Nh - 1) hk1; rwa [show Nh - 1 + 1 = Nh by omega] at this
  have hgk := (hD (Nh - 1) (by omega)).1
  have hKpG : M.Kp * ((t (Nh - 1)).1 + zA L m (Nh - 1)) ≤ 1 :=
    (hsmg (t (Nh - 1)).1 hgk.le (hmo.trans hgG)).2.2.2.2.2.2.1
  have hβP : ∀ P : Obs2.ObsPts 2 L N, ‖bt2 R P (zV b) m b μ Nh‖ ≤ 4 * b * thJ R m b μ Nh ∧
      ‖bt2 R P (zV b) m b μ (Nh + 1)‖ ≤ 4 * b * thJ R m b μ Nh := by
    intro P
    have h := bt2_last_leG R P hNh hNh1 hb hKp (hpairP P) (hrel P) (hnn2 P _ hk1) hgk.le hmo
      (add_nonneg hgk.le (haz _ hk1).1) (G := (t (Nh - 1)).1 + zA L m (Nh - 1))
      (add_nonneg hgk.le (haz _ hk1).1) le_rfl (htop P)
    have hθ0 : 0 ≤ thJ R m b μ Nh := Real.rpow_nonneg (div_pos hg0' hb).le _
    have hle : 2 * (1 + M.Kp * ((t (Nh - 1)).1 + zA L m (Nh - 1))) * b * thJ R m b μ Nh ≤
        4 * b * thJ R m b μ Nh := by
      have h0 := mul_nonneg hb.le hθ0
      have h2 := mul_le_mul_of_nonneg_right hKpG h0
      have e : 2 * (1 + M.Kp * ((t (Nh - 1)).1 + zA L m (Nh - 1))) * b * thJ R m b μ Nh =
          2 * (b * thJ R m b μ Nh) +
            2 * (M.Kp * ((t (Nh - 1)).1 + zA L m (Nh - 1)) * (b * thJ R m b μ Nh)) := by ring
      have e2 : 4 * b * thJ R m b μ Nh = 4 * (b * thJ R m b μ Nh) := by ring
      rw [e, e2]; linarith only [h2, h0]
    exact ⟨h.1.trans hle, h.2.trans hle⟩
  have hβ4 : BetaLast R Nh m b μ 4 := fun x' _ _ _ => hβP (ptsX x')
  have hgg : ∀ k ≤ Nh, 0 < (t k).1 ∧ (t k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk).1, ((hD k hk).2.1).trans hε1⟩
  -- `GamLastRel` without remainder inputs (`TopConcl` for `ρ_{N_h}`, `gamRemNP_le` for `ρ_N`)
  have hT := M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD
  have hzi0 : 0 ≤ zInvT R Nh m b μ := inv_nonneg.2 (norm_nonneg _)
  have hcrr : 0 ≤ h0crL M := le_trans M.cρ_nonneg (le_max_left _ _)
  have hVNl := M.lastValid N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hr0X : ∀ x' : Lam 2 L N, x' ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x' →
      Obs.coal L (0 : Lam 2 L N) x' ≤ Nh →
      ‖gamRemX R m b μ x' Nh‖ ≤ h0crL M * ‖btX R m b μ x' Nh‖ * zInvT R Nh m b μ :=
    fun x' _ _ _ => (hT (ptsX x')).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) hzi0)
  have hGl0 : GlueOut (R.withMsq m) Nh Cf t :=
    (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD).1
  have hr1X : GamRemNZ R Nh m b μ (h0crL M) := fun x' _ _ _ => by
    rw [gamRemN_eq_P]
    have hW1 := M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD (ptsX x') (by omega)
    have hW : WbHc (R.withMsq m) (ptsX x') (Obs2.obsInit .two (zV b) (ptsX x')) t (Nh + 1)
        (D.cWL * histS (R.withMsq m) Nh t ^ 2 * ‖bt2 R (ptsX x') (zV b) m b μ Nh‖) := by
      intro B hB
      refine (hW1 B hB).trans (ENNReal.ofReal_le_ofReal ?_)
      have hX : 0 ≤ D.cWL * histS (R.withMsq m) Nh t ^ 2 * ‖bt2 R (ptsX x') (zV b) m b μ Nh‖ := by
        have := M.cWL_nonneg; positivity
      have := mul_le_mul_of_nonneg_left (hgg Nh le_rfl).2 hX
      calc D.cWL * (t Nh).1 * histS (R.withMsq m) Nh t ^ 2 * ‖bt2 R (ptsX x') (zV b) m b μ Nh‖
          = D.cWL * histS (R.withMsq m) Nh t ^ 2 * ‖bt2 R (ptsX x') (zV b) m b μ Nh‖ * (t Nh).1 := by
            ring
        _ ≤ _ := by linarith only [this]
    have h := gamRemNP_le R hNh hV hVL hVNl D.hLpl (ptsX x') hGl0 hCf (hgg Nh le_rfl).2
      M.cWL_nonneg hW (htop (ptsX x'))
    rw [hRℓ] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) hzi0)
  obtain ⟨hZ0s, hZs⟩ :=
    (M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ hD Nh le_rfl
  have hLast := gamLastRel_ofZ R hP hb hKZ hcrr hV hVL hVNl (hgg Nh le_rfl).1 (hgg Nh le_rfl).2
    hZ0s hZs hβ4 hr0X hr1X
  rw [hRℓ] at hLast
  have hMag := magAt_ofD R M.magD hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  obtain ⟨-, -, hWT, -⟩ := wk_inputsD M.wkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD
  have hB := gamBulkRel_of_A R (M.gamBulkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD)
  have hγ := gamNa_near_of R hP hMag hm.1.le hb hV hgg (fun k hk => (haz k hk).2) hKp
    M.cGB_nonneg M.cw_nonneg (fun x' _ => hpairP (ptsX x')) hB hWT hLast x hx h1 hj
  ------------------------------------------------------------------ the zero-mode part
  -- the zero-mode part
  have hβeq : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ x)‖ =
      ‖bt2 R (ptsX x) (zV b) m b μ (Nh + 1)‖ := by
    have e : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ x) =
        Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
          (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t (Nh + 1)) := by
      unfold Obs2.betaTot2
      refine sum_congr rfl fun b' _ => ?_
      rw [Obs2.histVO2_a]
      congr 1
      exact Obs2.emb_add_cmp true _ _
    rw [e]; rfl
  have hcWL := M.cWL_nonneg
  have hcKL := M.cKL_nonneg
  have hVN' := M.lastValid N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; have := D.hL49; omega
  have hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    show |m| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1
    rw [abs_of_pos hm.1]
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    exact h1
  have hJ' : PtCorr2.LastJetBd L (R.A / 2) r₀ := by rw [hRA]; exact hJ
  set KA := cKAL L D.ℓ r₀ Cf D.cWL D.cKL 3 with hKAd
  have hl1 : LastL1 R Nh m b μ 3 := fun x' _ _ _ =>
    M.lastL1D N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD (ptsX x')
      ((htop (ptsX x')).1.trans (by norm_num))
  have e2 : 8 * cM * R.ℓ ^ 2 = 8 * cM * D.ℓ ^ 2 := by rw [hRℓ]
  have eT : cTauL R.ℓ Cf D.cWL D.cKL = cTauL D.ℓ Cf D.cWL D.cKL := by rw [hRℓ]
  have hLK : LastKRem R Nh m b μ KA := by
    rw [hKAd, ← hRℓ]
    refine lastKRem_of R hNh hV hVL hVN' D.hLpl hL8 hmN hGl hr₀ hr₀1 hJ' hcWL hcKL hCf
      (hgg Nh le_rfl).1 (hgg Nh le_rfl).2 (by rw [hRρ]; exact hs1) (by rw [e2]; exact hs2)
      (by rw [eT]; exact hs3) (by rw [eT]; exact hs4) (by rw [eT]; exact hs5)
      (fun x' _ _ _ => M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD (ptsX x')
        (by omega))
      (fun x' _ _ _ => M.lastKD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD (ptsX x')
        (by omega))
      (fun x' _ _ _ => htop (ptsX x')) hl1
  have hLAp := lastOneRem_of R hNh hV hVL hVN' D.hLpl hL8 hGl hcWL (hgg Nh le_rfl).1.le
    (fun x' _ _ _ => M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ hD (ptsX x') (by omega))
    (fun x' _ _ _ => htop (ptsX x')) (by
      have e : R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128 = D.ℓ ^ 2 / 8 + D.ℓ ^ 4 / 128 := by rw [hRℓ]
      rw [e]; exact hsA) hLK
  obtain ⟨hLO1, hLO2⟩ := hLAp.1 x hx h1 hj
  have hP0 := hLAp.2 x hx h1 hj
  simp only [hP0, mul_one, norm_one] at hLO1 hLO2
  have hZn : ‖out.Z‖ = z := by rw [hZz, Complex.norm_real, Real.norm_of_nonneg hz.le]
  have hLO2' : ‖ε (zFin R Nh m b μ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KA * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ x)‖ / z := by
    rw [← hZn]; exact hLO2
  have hsA_eq := (sX_omegaCO_cstC (zCc R Nh m b μ) (zFin R Nh m b μ x)).2.1
  have hzCc : zCc R Nh m b μ = tr / (V : ℂ) := by unfold zCc; rw [hVc]; rfl
  have hnU' : ((m * V : ℝ) : ℂ) * (1 + uFin (Nh + 1) out tr) = n := by rw [hUeq]; exact hnU
  have hnA := nA_zm_le (sA := PtCorr2.sA (zZm R Nh m b μ x)) (s := PtCorr2.sE (zZm R Nh m b μ x))
    (Eu := 1 / 4) hz hm0 hV0 hsA_eq hzCc hLO1 hLO2' b_w hsU hδ hnU' hnlo0 hnre'
  -- `|β_{N−1}|/|Z_N| ≤ (32/7)e^{1/4}ϑǧ`
  have hθ0 : 0 ≤ thJ R m b μ Nh := Real.rpow_nonneg (div_pos hg0' hb).le _
  have hβz : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ x)‖ / z ≤
      32 / 7 * Real.exp (1 / 4) * (varthJ R m b μ Nh * g) := by
    rw [hβeq]
    have hb4 := (hβP (ptsX x)).2
    obtain ⟨hZ0', hZl⟩ :=
      (M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ hD Nh le_rfl
    have hZp : 0 < ‖(rawHist (R.withMsq m) (Nh + 1) t).Z‖ := norm_pos_iff.2 hZ0'
    have hinv := inv_normZ_leS hZp hg0' hb hZl
    have hZ' := norm_stZ'_ge (R.withMsq m) (j := Nh) (rawHist (R.withMsq m) (Nh + 1) t) hρ0 hρ8'
    have hzz : ‖stZ' (R.withMsq m) (rawHist (R.withMsq m) (Nh + 1) t)‖ = z := hZn
    rw [hzz] at hZ'
    have hE : Real.exp (D.KZ * g) ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 hsKZ
    have hiz : z⁻¹ ≤ 8 / 7 * (Real.exp (1 / 4) * thJ R m b μ Nh) := by
      have h7 : 7 / 8 * ‖(rawHist (R.withMsq m) (Nh + 1) t).Z‖ ≤ z := hZ'
      have hz1 : z⁻¹ ≤ (7 / 8 * ‖(rawHist (R.withMsq m) (Nh + 1) t).Z‖)⁻¹ :=
        inv_anti₀ (by positivity) h7
      rw [mul_inv, inv_div] at hz1
      have h2 : ‖(rawHist (R.withMsq m) (Nh + 1) t).Z‖⁻¹ ≤ Real.exp (1 / 4) * thJ R m b μ Nh :=
        hinv.trans (mul_le_mul_of_nonneg_right hE hθ0)
      calc z⁻¹ ≤ 8 / 7 * ‖(rawHist (R.withMsq m) (Nh + 1) t).Z‖⁻¹ := hz1
        _ ≤ 8 / 7 * (Real.exp (1 / 4) * thJ R m b μ Nh) := by linarith only [hz1, h2]
    have hsq : b * thJ R m b μ Nh ^ 2 = varthJ R m b μ Nh * g := b_thJ_sq hg0' hb
    rw [div_eq_mul_inv]
    calc ‖bt2 R (ptsX x) (zV b) m b μ (Nh + 1)‖ * z⁻¹
        ≤ (4 * b * thJ R m b μ Nh) * (8 / 7 * (Real.exp (1 / 4) * thJ R m b μ Nh)) :=
          mul_le_mul hb4 hiz (inv_nonneg.2 hz.le) (by positivity)
      _ = 32 / 7 * Real.exp (1 / 4) * (b * thJ R m b μ Nh ^ 2) := by ring
      _ = 32 / 7 * Real.exp (1 / 4) * (varthJ R m b μ Nh * g) := by rw [hsq]
  -- assembly
  have hv0 : 0 ≤ varthJ R m b μ Nh := Real.rpow_nonneg (div_pos hb hg0').le _
  have hQ : KA * (m * V) + 3 / 2 * (1 + KTc * (m * V)) ≤ 19 / 8 := by
    have h1' : KA * (m * V) ≤ 1 / 8 := by
      have := hmA; rw [hVN] at this
      have e : 8 * KA * m * V = 8 * (KA * (m * V)) := by ring
      linarith only [this, e]
    have h2' : KTc * (m * V) ≤ 1 / 2 := by
      have := hmT; rw [hVN] at this
      have e : KTc * m * V = KTc * (m * V) := by ring
      linarith only [this, e]
    linarith only [h1', h2']
  have hBz0 : 0 ≤ ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ x)‖ / z :=
    div_nonneg (norm_nonneg _) hz.le
  have hE2 : Real.exp (1 / 4) * Real.exp (1 / 4) < 2 := by
    rw [← Real.exp_add, show (1 : ℝ) / 4 + 1 / 4 = 1 / 2 by norm_num]; exact exp_half_lt_two
  have hw2 : ‖PtCorr2.nA (zZm R Nh m b μ x)‖ ≤ 1 / 2 * varthJ R m b μ Nh := by
    have e : PtCorr2.nA (zZm R Nh m b μ x) =
        PtCorr2.sA (zZm R Nh m b μ x) / PtCorr2.sE (zZm R Nh m b μ x) := rfl
    rw [e]
    refine hnA.trans ?_
    rw [div_le_iff₀ hnlo0]
    set Bz := ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ x)‖ / z
    have k1 : Real.exp (1 / 4) * Bz * (KA * (m * V) + 3 / 2 * (1 + KTc * (m * V))) ≤
        Real.exp (1 / 4) * Bz * (19 / 8) :=
      mul_le_mul_of_nonneg_left hQ (mul_nonneg (Real.exp_pos _).le hBz0)
    have k2 : Real.exp (1 / 4) * Bz * (19 / 8) ≤
        Real.exp (1 / 4) * (32 / 7 * Real.exp (1 / 4) * (varthJ R m b μ Nh * g)) * (19 / 8) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβz (Real.exp_pos _).le) (by norm_num)
    have k3 : Real.exp (1 / 4) * (32 / 7 * Real.exp (1 / 4) * (varthJ R m b μ Nh * g)) * (19 / 8) =
        76 / 7 * (Real.exp (1 / 4) * Real.exp (1 / 4)) * (varthJ R m b μ Nh * g) := by ring
    have hvg : 0 ≤ varthJ R m b μ Nh * g := mul_nonneg hv0 hg0
    have k4 : 76 / 7 * (Real.exp (1 / 4) * Real.exp (1 / 4)) * (varthJ R m b μ Nh * g) ≤
        76 / 7 * 2 * (varthJ R m b μ Nh * g) :=
      mul_le_mul_of_nonneg_right (by linarith only [hE2]) hvg
    have k5 : 76 / 7 * 2 * (varthJ R m b μ Nh * g) ≤ 1 / 2 * varthJ R m b μ Nh * nlo := by
      have : 44 * g ≤ nlo := by linarith only [hgG, hmarg]
      have h44 := mul_le_mul_of_nonneg_left this hv0
      have e1 : varthJ R m b μ Nh * (44 * g) = 44 * (varthJ R m b μ Nh * g) := by ring
      have e2 : 1 / 2 * varthJ R m b μ Nh * nlo = 1 / 2 * (varthJ R m b μ Nh * nlo) := by ring
      rw [e2]; linarith only [h44, e1, hvg]
    linarith only [k1, k2, k3, k4, k5]
  have hγ' : ‖gamNa R Nh m b μ x - ((varthJ R m b μ Nh : ℝ) : ℂ)‖ ≤
      ((max (spinMK L D.cg D.Ke D.KZ (M.Kp + (D.cGB + D.cw) * (1 + 3 * M.Kp)) D.KG 0) 0 +
        2 * 4 * (D.ℓ ^ 2 * Real.exp D.KZ / 14 + h0crL M * Real.exp D.KZ)) * g) *
          varthJ R m b μ Nh := by
    refine hγ.trans (le_of_eq ?_)
    ring
  exact re_nonneg_of_split hv0 hsplit hγ' hw2 (by linarith only [hsγ])


end

end Spin2
