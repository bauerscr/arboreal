import Spin2.Cont.ContK2a
import Spin2.Cont.ContArt2

set_option autoImplicit false

/-!
# B3, T6, route (c): per-scale sizes of the restarted datum in **one fixed weight**

Fixed weight `w = wM(M_a, M_b)` with `M_a = 2s_J²M_{J−ms}` (the restart envelope at a later scale
`J`, `ms ≤ J ≤ N_h`; `J = j_y` resp. `J = N_h`) and `M_b = pM(ptsS x)_{N_h}`.

* `k2Env`, `k2Ma`: the envelope `M_i = M₀∏_{l<i}|1 − 𝔫F_{ms+l}|` and `M_a`.
* **`k2Mj M N_h J ms Q j := (c_W + 1)((7/5)^{J−j} + Θ_b(j)) + (8/15)^{j−ms}Q`**, the explicit
  per-scale size (`Θ_b(j) = cw2Thb = e^{2c_δ(4/β_L)ε}(81/56)^{N_h−j}`). The stationary part grows
  backwards by `≤ 7/5`, `81/56`; the transient part by `15/8`; so `m_j ≤ 2m_{j+1}` (`k2Mj_le_two`).
* `k2_tr_le` (pure): `(p·7/5)^i(7/5)^eτ ≤ (8/15)^i·rQ` from `(7/5)^{i+e}τ ≤ r₀Q`, `p ≤ 8/15`,
  `r₀ ≤ r`.
* `k2_g_mono`: `ǧ_{ms} ≤ ǧ_j` (`M.gmonoD`).
* **`MasterFacts.k2_sizes`**: for `ms ≤ j ≤ J`, with `Q ≥ 0`,
  `(7/5)^{J−ms}·w/(s_{ms}²M₀) ≤ r_{ms}Q`, `(7/5)^{J−ms}(k + 120B(cε)w)/(s_{ms}²M₀) ≤ 8Br_{ms}²Q`:
  `‖V_j(q)‖_w ≤ m_j` (if `V_{ab} = 0`), `‖𝒲_j(q)‖_w ≤ r_jm_j` (if `𝒲_{ab} = 0`),
  `A^{(|𝓑(X)|−4)_+}‖K_j(X)‖_{wOne w} ≤ 8Br_j²m_j` (`r_j = cǧ_j`, `m_j = k2Mj … j`).
  Proof: `art_aSizesD` at `i = j − ms`, `k2_envRatio` (`M_a(j) ≤ (7/5)^{J−j}M_a`), `cw3_bSizes`,
  `cw2_pMS_ratio`, `oTo_wM_le_of_ab`, `reg_oTo_wM1_le`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

/-- The restart envelope `M_i` of the datum `δ` at `ms` (points `ptsX x`). -/
def k2Env {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (x : Lam 2 L N) (ms : ℕ) (δ : Obs2.ObsSt .two L N) (M₀ : ℝ) (i : ℕ) : ℝ :=
  Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F (ptsX x) (Obs2.histCovO (R.withMsq m)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ms (ms + i)‖) i

/-- The fixed `a`-weight `M_a = 2s_J²M_{J−ms}`. -/
def k2Ma {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (x : Lam 2 L N) (ms : ℕ) (δ : Obs2.ObsSt .two L N) (M₀ : ℝ) (J : ℕ) : ℝ :=
  2 * histS (R.withMsq m) J (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
    k2Env R m b μ₀ x ms δ M₀ (J - ms)

/-- **The explicit per-scale size** `m_j = (c_W + 1)((7/5)^{J−j} + Θ_b(j)) + (8/15)^{j−ms}Q`. -/
def k2Mj (M : MasterFacts L) (Nh J ms : ℕ) (Q : ℝ) (j : ℕ) : ℝ :=
  (M.core.cWo + 1) * ((7 / 5) ^ (J - j) + cw2Thb M Nh j) + (8 / 15) ^ (j - ms) * Q

theorem cw2Thb_pos (M : MasterFacts L) (Nh j : ℕ) : 0 < cw2Thb M Nh j := by
  unfold cw2Thb; positivity

theorem k2Mj_pos (M : MasterFacts L) (Nh J ms : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) (j : ℕ) :
    0 < k2Mj M Nh J ms Q j := by
  unfold k2Mj
  have := M.core.consts_nonneg.2.2.2.2.2.1
  have := cw2Thb_pos M Nh j
  positivity

theorem one_le_k2Mj (M : MasterFacts L) (Nh J ms : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) (j : ℕ) :
    1 ≤ k2Mj M Nh J ms Q j := by
  unfold k2Mj
  have := M.core.consts_nonneg.2.2.2.2.2.1
  have := cw2Thb_pos M Nh j
  have : 1 ≤ (7 / 5 : ℝ) ^ (J - j) := one_le_pow₀ (by norm_num)
  have : 0 ≤ (8 / 15 : ℝ) ^ (j - ms) * Q := by positivity
  nlinarith

/-- **`m_j ≤ 2m_{j+1}`** (`ms ≤ j`, `j < J`, `j < N_h`). -/
theorem k2Mj_le_two (M : MasterFacts L) (Nh J ms : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) {j : ℕ}
    (hmj : ms ≤ j) (hjJ : j < J) (hjN : j < Nh) :
    k2Mj M Nh J ms Q j ≤ 2 * k2Mj M Nh J ms Q (j + 1) := by
  unfold k2Mj cw2Thb
  have e1 : J - j = (J - (j + 1)) + 1 := by omega
  have e2 : Nh - j = (Nh - (j + 1)) + 1 := by omega
  have e3 : j + 1 - ms = (j - ms) + 1 := by omega
  rw [e1, e2, e3, pow_succ, pow_succ, pow_succ]
  have := M.core.consts_nonneg.2.2.2.2.2.1
  set E := Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε))
  have hE : 0 < E := Real.exp_pos _
  have h1 : 0 ≤ (7 / 5 : ℝ) ^ (J - (j + 1)) := by positivity
  have h2 : 0 ≤ E * (81 / 56 : ℝ) ^ (Nh - (j + 1)) := by positivity
  have h3 : 0 ≤ (8 / 15 : ℝ) ^ (j - ms) * Q := by positivity
  nlinarith

/-- The transient bound (pure). -/
theorem k2_tr_le {p τ Q r₀ r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 8 / 15) (hτ : 0 ≤ τ) (hQ : 0 ≤ Q)
    (hr : r₀ ≤ r) (i e : ℕ) (h : (7 / 5) ^ (i + e) * τ ≤ r₀ * Q) :
    (p * (7 / 5)) ^ i * (7 / 5) ^ e * τ ≤ (8 / 15) ^ i * (r * Q) := by
  have e1 : (p * (7 / 5)) ^ i * (7 / 5) ^ e * τ = p ^ i * ((7 / 5) ^ (i + e) * τ) := by
    rw [mul_pow, pow_add]; ring
  rw [e1]
  have h1 : p ^ i ≤ (8 / 15) ^ i := pow_le_pow_left₀ hp0 hp i
  have h2 : (7 / 5) ^ (i + e) * τ ≤ r * Q := h.trans (mul_le_mul_of_nonneg_right hr hQ)
  have h3 : 0 ≤ (7 / 5 : ℝ) ^ (i + e) * τ := by positivity
  calc p ^ i * ((7 / 5) ^ (i + e) * τ) ≤ (8 / 15) ^ i * ((7 / 5) ^ (i + e) * τ) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ ≤ (8 / 15) ^ i * (r * Q) := mul_le_mul_of_nonneg_left h2 (by positivity)

namespace MasterFacts

variable (M : MasterFacts L)

theorem k2_g_mono (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc)
    (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ)
    (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) {ms : ℕ} :
    ∀ d, ms + d ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + d)).1
  | 0, _ => le_rfl
  | d + 1, h => (k2_g_mono N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD d (by omega)).trans
      (M.gmonoD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD (ms + d) (by omega))

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
/-- **Per-scale sizes of the restarted datum in the fixed weight `wM(M_a, M_b)`.** -/
theorem k2_sizes (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
          ENNReal.ofReal (k2Mj M Nh J ms Q j)) ∧
    ((∀ q, ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q :
        SA .two (Lam 2 L N)).ab = 0) →
      ∀ q ∈ blockIdx (L := L) (N := N) j,
        Obs2.oTo (wM (k2Ma R m b μ₀ x ms δ M₀ J)
            (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)) j
          (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q) ≤
          ENNReal.ofReal (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 * k2Mj M Nh J ms Q j)) ∧
    (∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      Obs2.oTo (wM1 (k2Ma R m b μ₀ x ms δ M₀ J)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)) j
        (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤
      ENNReal.ofReal (8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ 2 *
        k2Mj M Nh J ms Q j)) := by
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
  have hratb := M.cw2_pMS_ratio N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD x
    (j := j) (by omega)
  replace hratb : 2 * histS (R.withMsq m) j t ^ 2 * ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ ≤
      cw2Thb M Nh j * pM (R.withMsq m) (ptsS x) (zV0 b) t Nh := hratb
  set Mb := pM (R.withMsq m) (ptsS x) (zV0 b) t Nh with hMbd
  set Θ := cw2Thb M Nh j with hΘd
  have hΘ0 : 0 < Θ := cw2Thb_pos M Nh j
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; rw [htd] at this; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hβS := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS x)
    (zV0 b) rfl hmu (by omega) Nh le_rfl).1
  have hMb : 0 < Mb := by
    show 0 < 2 * histS (R.withMsq m) Nh t ^ 2 * _; exact mul_pos (mul_pos two_pos (pow_pos hsN 2)) hβS
  have hdivb : Θ * Mb / Mb = Θ := by field_simp
  set mj := k2Mj M Nh J ms Q j with hmjd
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
