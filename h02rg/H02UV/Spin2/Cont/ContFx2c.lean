import Spin2.Cont.ContFx2b
import Spin2.Cont.ContK2b

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`), Phase 2, layer 3a: per-scale sizes with the uniform `b`-ratio

* **`MasterFacts.fxMj M J ms Q j := (c_W + 1)((7/5)^{J−j} + Θ*) + (8/15)^{j−ms}Q`**: `k2Mj` with
  `Θ_b(j) = cw2Thb M N_h j` replaced by the constant `Θ* = fxTh`; `fxMj_pos`, `one_le_fxMj`,
  `fxMj_le_two` (`m_j ≤ 2m_{j+1}`).
* **`MasterFacts.fx_sizes`**: `k2_sizes` with `k2Mj ↦ fxMj` (`fx_pMS_ratioU` instead of
  `cw2_pMS_ratio`; new input `hsmN : K_p(ǧ_{N_h−1} + a_{N_h−1}) ≤ 1/2`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

theorem fxTh_pos : 0 < M.fxTh := by
  unfold fxTh; have := M.Kp_nonneg; positivity

/-- **The per-scale size with the uniform ratio** `m_j = (c_W + 1)((7/5)^{J−j} + Θ*) + (8/15)^{j−ms}Q`. -/
def fxMj (J ms : ℕ) (Q : ℝ) (j : ℕ) : ℝ :=
  (M.core.cWo + 1) * ((7 / 5) ^ (J - j) + M.fxTh) + (8 / 15) ^ (j - ms) * Q

theorem fxMj_pos (J ms : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) (j : ℕ) : 0 < M.fxMj J ms Q j := by
  unfold fxMj
  have := M.core.consts_nonneg.2.2.2.2.2.1
  have := M.fxTh_pos
  positivity

theorem one_le_fxMj (J ms : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) (j : ℕ) : 1 ≤ M.fxMj J ms Q j := by
  unfold fxMj
  have := M.core.consts_nonneg.2.2.2.2.2.1
  have := M.fxTh_pos
  have : 1 ≤ (7 / 5 : ℝ) ^ (J - j) := one_le_pow₀ (by norm_num)
  have : 0 ≤ (8 / 15 : ℝ) ^ (j - ms) * Q := by positivity
  nlinarith

/-- **`m_j ≤ 2m_{j+1}`** (`ms ≤ j`, `j < J`). -/
theorem fxMj_le_two (J ms : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) {j : ℕ} (hmj : ms ≤ j) (hjJ : j < J) :
    M.fxMj J ms Q j ≤ 2 * M.fxMj J ms Q (j + 1) := by
  unfold fxMj
  have e1 : J - j = (J - (j + 1)) + 1 := by omega
  have e3 : j + 1 - ms = (j - ms) + 1 := by omega
  rw [e1, e3, pow_succ, pow_succ]
  have := M.core.consts_nonneg.2.2.2.2.2.1
  have hΘ := M.fxTh_pos
  have h1 : 0 ≤ (7 / 5 : ℝ) ^ (J - (j + 1)) := by positivity
  have h3 : 0 ≤ (8 / 15 : ℝ) ^ (j - ms) * Q := by positivity
  nlinarith

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
/-- **`k2_sizes` with the uniform ratio** (`fxMj`). -/
theorem fx_sizes (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) {ms : ℕ} (hms0 : 0 < ms) (hms : ms ≤ Nh) (δ : Obs2.ObsSt .two L N)
    (hδ : δ.IsObs) (hδl : ObsLocInv (ptsX x) ms δ) (hδs : ObsSymInv ms δ)
    (hδf : ∀ q, Obs2.Loc2Form (ptsX x).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      mass2 (δ.V q : SA .two (Lam 2 L N)).a • pbp (ptsX x).a)
    (hδb : Obs2.prjSt false δ = Obs2.prjSt false (Obs2.obsHist (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖Obs2.betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX x) ms δ
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms)‖ +
      Obs2.shareDev2 (ptsX x).a ms (histVF2 (R.withMsq m) (ptsX x) ms δ
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms w)
    (hKR : KbHF (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) *
      2) ≤ 1 / 1344)
    (hMR : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)
    (hsmN : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 + zA L m (Nh - 1)) ≤ 1 / 2)
    {J : ℕ} (hmsJ : ms ≤ J) (hJ : J ≤ Nh) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQw : (7 / 5) ^ (J - ms) * (w / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 * Q)
    (hQk : (7 / 5) ^ (J - ms) * ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) ≤
      8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) ^ 2 * Q)
    {j : ℕ} (hmj : ms ≤ j) (hjJ : j ≤ J) :
    0 < k2Ma R m b μ₀ x ms δ M₀ J ∧
    0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh ∧
    ((∀ q, ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q :
        SA .two (Lam 2 L N)).ab = 0) →
      ∀ q ∈ blockIdx (L := L) (N := N) j,
        Obs2.oTo (wM (k2Ma R m b μ₀ x ms δ M₀ J)
            (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)) j
          (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q) ≤
          ENNReal.ofReal (M.fxMj J ms Q j)) ∧
    ((∀ q, ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q :
        SA .two (Lam 2 L N)).ab = 0) →
      ∀ q ∈ blockIdx (L := L) (N := N) j,
        Obs2.oTo (wM (k2Ma R m b μ₀ x ms δ M₀ J)
            (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)) j
          (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q) ≤
          ENNReal.ofReal (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 * M.fxMj J ms Q j)) ∧
    (∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      Obs2.oTo (wM1 (k2Ma R m b μ₀ x ms δ M₀ J)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤
      ENNReal.ofReal (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ 2 *
        M.fxMj J ms Q j)) := by
  have hN2 : 2 ≤ N := by omega
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hsN := histS_pos' (R.withMsq m) hρ0 hρ8 t Nh
  have hsJ := histS_pos' (R.withMsq m) hρ0 hρ8 t J
  have hsms := histS_pos' (R.withMsq m) hρ0 hρ8 t ms
  obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hc2 : 2 ≤ M.core.c := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hε0 : 0 ≤ M.core.ε := by have := H.hε; linarith
  have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  set i := j - ms with hid
  have hji : ms + i = j := by omega
  have hiN : i ≤ Nh - ms := by omega
  set g := (t j).1 with hgd
  have hg0 : 0 ≤ g := (hD j (by omega)).1.le
  have hgm : (t ms).1 ≤ g := by
    have := M.k2_g_mono N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ms := ms) i (by omega)
    rwa [hji] at this
  have hgms0 : 0 ≤ (t ms).1 := (hD ms hms).1.le
  set r := M.core.c * g with hrd
  have hr0 : 0 ≤ r := by positivity
  have hrms : M.core.c * (t ms).1 ≤ r := mul_le_mul_of_nonneg_left hgm (by linarith)
  -- the `a`-sector at `j`
  obtain ⟨hAV, hAW, hAK, henvi⟩ := M.core.art_aSizesD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b
    μ₀ hD (ptsX x) (zV0 b) ms δ hms0 hms hδ hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg hMR i hiN
  rw [hji] at hAV hAW hAK
  -- the envelope ratio
  have hrat := M.core.k2_envRatio N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV0 b)
    ms δ hδ hM0.le (i := i) (i' := J - ms) (by omega) (by omega)
  have eJ : ms + (J - ms) = J := by omega
  rw [hji, eJ] at hrat
  have eJi : J - ms - i = J - j := by omega
  rw [eJi] at hrat
  set Ma := k2Ma R m b μ₀ x ms δ M₀ J with hMad
  set Mai := 2 * histS (R.withMsq m) j t ^ 2 * k2Env R m b μ₀ x ms δ M₀ i with hMaid
  have hrat' : Mai ≤ (7 / 5) ^ (J - j) * Ma := hrat
  have henvJ : 0 < k2Env R m b μ₀ x ms δ M₀ (J - ms) :=
    (M.core.art_aSizesD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b
      μ₀ hD (ptsX x) (zV0 b) ms δ hms0 hms hδ hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg hMR
      (J - ms) (by omega)).2.2.2
  have hMa : 0 < Ma := by
    show 0 < 2 * histS (R.withMsq m) J t ^ 2 * k2Env R m b μ₀ x ms δ M₀ (J - ms); positivity
  have hMai0 : 0 ≤ Mai := by
    have : 0 < k2Env R m b μ₀ x ms δ M₀ i := henvi
    show 0 ≤ 2 * histS (R.withMsq m) j t ^ 2 * k2Env R m b μ₀ x ms δ M₀ i; positivity
  have hdiv : Mai / Ma ≤ (7 / 5) ^ (J - j) := by
    rw [div_le_iff₀ hMa]; exact hrat'
  -- the `b`-sector at `j`
  obtain ⟨hBV, hBW, hBK⟩ := M.cw3_bSizes N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μ₀ hD x δ
    hδb hms0 hmj (by omega)
  have hratb := M.fx_pMS_ratioU R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD x (j := j) (by omega)
    (by omega) hsmN
  replace hratb : 2 * histS (R.withMsq m) j t ^ 2 * ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ ≤
      M.fxTh * pM (R.withMsq m) (ptsS x) (zV0 b) t Nh := hratb
  set Mb := pM (R.withMsq m) (ptsS x) (zV0 b) t Nh with hMbd
  set Θ := M.fxTh with hΘd
  have hΘ0 : 0 < Θ := M.fxTh_pos
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; rw [htd] at this; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hβS := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS x)
    (zV0 b) rfl hmu (by omega) Nh le_rfl).1
  have hMb : 0 < Mb := by
    show 0 < 2 * histS (R.withMsq m) Nh t ^ 2 * _; exact mul_pos (mul_pos two_pos (pow_pos hsN 2)) hβS
  have hdivb : Θ * Mb / Mb = Θ := by field_simp
  set mj := M.fxMj J ms Q j with hmjd
  have hmjE : mj = (M.core.cWo + 1) * ((7 / 5) ^ (J - j) + Θ) + (8 / 15) ^ i * Q := rfl
  have hQi : 0 ≤ (8 / 15 : ℝ) ^ i * Q := by positivity
  have hp7 : 0 ≤ (7 / 5 : ℝ) ^ (J - j) := by positivity
  -- transients
  set τw := w / (histS (R.withMsq m) ms t ^ 2 * M₀) with hτwd
  set τk := (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
    (histS (R.withMsq m) ms t ^ 2 * M₀) with hτkd
  have hτw0 : 0 ≤ τw := by positivity
  have hτk0 : 0 ≤ τk := by
    have : 0 ≤ M.core.c * M.core.ε := by positivity
    positivity
  have eexp : J - ms = i + (J - j) := by omega
  have htw : (7 / 30 : ℝ) ^ i * (7 / 5) ^ (J - j) * τw ≤ (8 / 15) ^ i * (r * Q) := by
    have := k2_tr_le (p := 1 / 6) (by norm_num) (by norm_num) hτw0 hQ0 hrms i (J - j)
      (by rw [← eexp]; exact hQw)
    rwa [show (1 / 6 : ℝ) * (7 / 5) = 7 / 30 by norm_num] at this
  have htk : (56 / 75 : ℝ) ^ i * (7 / 5) ^ (J - j) * τk ≤
      (8 / 15) ^ i * (8 * M.core.Bk * r ^ 2 * Q) := by
    have hr2 : 8 * M.core.Bk * (M.core.c * (t ms).1) ^ 2 ≤ 8 * M.core.Bk * r ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrms 2) (by positivity)
    have := k2_tr_le (p := 8 / 15) (by norm_num) le_rfl hτk0 hQ0 hr2 i (J - j)
      (by rw [← eexp]; exact hQk)
    rw [show (8 / 15 : ℝ) * (7 / 5) = 56 / 75 by norm_num] at this
    linarith
  refine ⟨hMa, hMb, fun hab q hq => ?_, fun hab q hq => ?_, fun X hX => ?_⟩
  · -- `V`
    have hbv : Tj 2 (L : ℝ) j (histS (R.withMsq m) j t)
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j t).V q : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (Θ * Mb) := (hBV q hq).trans (ENNReal.ofReal_le_ofReal hratb)
    refine (oTo_wM_le_of_ab hMa hMb j _ _ (hab q) hMai0 (by positivity) (hAV q hq) hbv).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hdivb, hmjE]
    nlinarith
  · -- `𝒲`
    have hbw : Tj 2 (L : ℝ) j (histS (R.withMsq m) j t)
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j t).W q : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (M.core.cWo * r * (Θ * Mb)) :=
      (hBW q hq).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hratb (by positivity)))
    have hu0 : 0 ≤ (M.core.cWo * r + (7 / 30) ^ i * τw) * Mai := by positivity
    refine (oTo_wM_le_of_ab hMa hMb j _ _ (hab q) hu0 (by positivity) (hAW q hq) hbw).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have e1 : M.core.cWo * r * (Θ * Mb) / Mb = M.core.cWo * r * Θ := by field_simp
    rw [e1, mul_div_assoc]
    have h1 : (M.core.cWo * r + (7 / 30) ^ i * τw) * (Mai / Ma) ≤
        (M.core.cWo * r + (7 / 30) ^ i * τw) * (7 / 5) ^ (J - j) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    rw [hmjE]
    have hrp : 0 ≤ r * (7 / 5) ^ (J - j) := by positivity
    have hrΘ : 0 ≤ r * Θ := by positivity
    have eL : (M.core.cWo * r + (7 / 30) ^ i * τw) * (7 / 5) ^ (J - j) =
        M.core.cWo * r * (7 / 5) ^ (J - j) + (7 / 30) ^ i * (7 / 5) ^ (J - j) * τw := by ring
    have eR : r * ((M.core.cWo + 1) * ((7 / 5) ^ (J - j) + Θ) + (8 / 15) ^ i * Q) =
        M.core.cWo * r * (7 / 5) ^ (J - j) + M.core.cWo * r * Θ + r * (7 / 5) ^ (J - j) +
          r * Θ + (8 / 15) ^ i * (r * Q) := by ring
    rw [eR]
    linarith [h1, htw, hrp, hrΘ, eL]
  · -- `K`
    have hbk : ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
        Tj 2 (L : ℝ) j (histS (R.withMsq m) j t)
          ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j t).K X : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (8 * M.core.cWo * M.core.Bk * r ^ 2 * (Θ * Mb)) := by
      have h16 : 16 * M.core.cWo * M.core.Bk * r ^ 2 *
          (histS (R.withMsq m) j t ^ 2 * ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖) ≤
          8 * M.core.cWo * M.core.Bk * r ^ 2 * (Θ * Mb) := by
        have := mul_le_mul_of_nonneg_left hratb
          (by positivity : (0 : ℝ) ≤ 8 * M.core.cWo * M.core.Bk * r ^ 2)
        calc _ = 8 * M.core.cWo * M.core.Bk * r ^ 2 *
              (2 * histS (R.withMsq m) j t ^ 2 * ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖) := by ring
          _ ≤ _ := this
      exact (hBK X hX).trans (ENNReal.ofReal_le_ofReal h16)
    have hu0 : 0 ≤ ((56 / 75) ^ i * τk + 8 * M.core.cWo * M.core.Bk * r ^ 2) * Mai := by
      positivity
    refine (reg_oTo_wM1_le hMa hMb j _ _ _ hu0 (by positivity) (hAK X hX) hbk).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have e1 : 8 * M.core.cWo * M.core.Bk * r ^ 2 * (Θ * Mb) / Mb =
        8 * M.core.cWo * M.core.Bk * r ^ 2 * Θ := by field_simp
    rw [e1, mul_div_assoc]
    have h1 : ((56 / 75) ^ i * τk + 8 * M.core.cWo * M.core.Bk * r ^ 2) * (Mai / Ma) ≤
        ((56 / 75) ^ i * τk + 8 * M.core.cWo * M.core.Bk * r ^ 2) * (7 / 5) ^ (J - j) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    rw [hmjE]
    have hB8 : 0 ≤ 8 * M.core.Bk * r ^ 2 := by positivity
    have h2 : 8 * M.core.cWo * M.core.Bk * r ^ 2 * ((7 / 5) ^ (J - j) + Θ) ≤
        8 * M.core.Bk * r ^ 2 * ((M.core.cWo + 1) * ((7 / 5) ^ (J - j) + Θ)) := by
      have : 0 ≤ 8 * M.core.Bk * r ^ 2 * ((7 / 5) ^ (J - j) + Θ) := by positivity
      nlinarith
    have eL : ((56 / 75) ^ i * τk + 8 * M.core.cWo * M.core.Bk * r ^ 2) * (7 / 5) ^ (J - j) =
        (56 / 75) ^ i * (7 / 5) ^ (J - j) * τk +
          8 * M.core.cWo * M.core.Bk * r ^ 2 * (7 / 5) ^ (J - j) := by ring
    have eR : 8 * M.core.Bk * r ^ 2 * ((M.core.cWo + 1) * ((7 / 5) ^ (J - j) + Θ) + (8 / 15) ^ i * Q) =
        8 * M.core.Bk * r ^ 2 * ((M.core.cWo + 1) * ((7 / 5) ^ (J - j) + Θ)) +
          (8 / 15) ^ i * (8 * M.core.Bk * r ^ 2 * Q) := by ring
    have e2 : 8 * M.core.cWo * M.core.Bk * r ^ 2 * ((7 / 5) ^ (J - j) + Θ) =
        8 * M.core.cWo * M.core.Bk * r ^ 2 * (7 / 5) ^ (J - j) +
          8 * M.core.cWo * M.core.Bk * r ^ 2 * Θ := by ring
    rw [eR]
    linarith [h1, htk, h2, eL, e2]

end MasterFacts

end

end Spin2
