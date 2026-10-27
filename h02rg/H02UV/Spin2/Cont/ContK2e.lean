import Spin2.Cont.ContK2d
import Spin2.Cont.ContTop8

set_option autoImplicit false

/-!
# B3, T6, route (c): `k₂` at `N_h + 1` and the top-coalescence bound with decayed transients

* **`MasterFacts.k2_top`** (`N_h + 1 ≤ j_y`, fixed weight `wM(k2Ma … N_h, pM(ptsS y)_{N_h})`,
  `m_j = k2Mj M N_h N_h ms Q j`): `ct_k2_top` with all per-scale inputs discharged by `k2_sizes`
  (`V_{ab} = 𝒲_{ab} = 0` for `j ≤ N_h` from `pl3_delta_inv`) and `hK20` from `Z_{ab} ≤ c_{ab}r_{ms}Q²`:
  `A^{(…)}w_{ab}T(K_{N_h+1}(X)_{ab}) ≤ (c_{ab}/5)r_{N_h}m_{N_h}²`.
* **`MasterFacts.k2_conn_diff_top`**: `ct_conn_diff_top'` with (i) the decayed transient conditions
  of `art_T5topD` (`(7/30)^{N_h−ms}`, `(56/75)^{N_h−ms}`) and (ii) the `ab` input at `N_h + 1`
  discharged: `k₂` only has to dominate `(c_{ab}/5)r_{N_h}m̄²` (`m̄ = k2mbar M N_h N_h`) under the
  waiting hypothesis `(8/15)^{N_h−ms}Q ≤ 1`. New inputs: `Q`, `hQw`, `hQk`, `Z_{ab}` (`hZ`, `hQz`).
  The initial `a`-constant stays inside `ctGamB` (as before).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
/-- **`k₂` at `N_h + 1` (top coalescence).** -/
theorem k2_top (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms : ℕ} (hms0 : 0 < ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hjy : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y) (hmsN : ms < Nh)
    (hδ : (pl2Delta R m b μ₀ x y ms).IsObs)
    (hδl : ObsLocInv (ptsX y) ms (pl2Delta R m b μ₀ x y ms))
    (hδs : ObsSymInv ms (pl2Delta R m b μ₀ x y ms))
    (hδf : ∀ q, Obs2.Loc2Form (ptsX y).a ((pl2Delta R m b μ₀ x y ms).V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, ((pl2Delta R m b μ₀ x y ms).V q : SA .two (Lam 2 L N)).a =
      mass2 ((pl2Delta R m b μ₀ x y ms).V q : SA .two (Lam 2 L N)).a • pbp (ptsX y).a)
    (hδb : Obs2.prjSt false (pl2Delta R m b μ₀ x y ms) = Obs2.prjSt false (Obs2.obsHist (R.withMsq m)
      (ptsX y) (Obs2.obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖Obs2.betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX y) ms
        (pl2Delta R m b μ₀ x y ms) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms)‖ +
      Obs2.shareDev2 (ptsX y).a ms (histVF2 (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms w)
    (hKR : KbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) *
      2) ≤ 1 / 1344)
    (hMR : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)
    {Q Zab : ℝ} (hQ0 : 0 ≤ Q)
    (hQw : (7 / 5) ^ (Nh - ms) *
        (w / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 * Q)
    (hQk : (7 / 5) ^ (Nh - ms) *
        ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) ≤
      8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) ^ 2 * Q)
    (hZ : ∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
      ((wM (k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ Nh)
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)).ab *
        Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((pl2Delta R m b μ₀ x y ms).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal Zab)
    (hQz : Zab ≤ M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) * Q ^ 2) :
    ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal ((R.withMsq m).A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM (k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ Nh)
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)).ab *
        Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X :
            SA .two (Lam 2 L N)).ab) ≤
      ENNReal.ofReal (M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) *
        k2Mj M Nh Nh ms Q Nh ^ 2)) := by
  have hN2 : 2 ≤ N := by omega
  have hms : ms ≤ Nh := hmsN.le
  have hmy : ms < Obs.coal L (0 : Lam 2 L N) y := by omega
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hRA' : R'.A = M.core.A := hRA
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by rw [hRA']; exact M.core.hSBx
  have htN := inDh_rg_of_D R' F1 hD Nh le_rfl
  have hmsq : R'.msq ∈ mRange L N := hm
  have hβε := M.core.hβε
  have X := c2ctx_master R' (by omega) M.core.hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε htN
  have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by have := M.core.hL49; omega)
    rw [abs_of_nonneg X.hm0]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) 2
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := M.core.hL49; norm_num; omega
  have hc2 : 2 ≤ M.core.c := hcR ▸ two_le_cR R' H.hcmu H.hC₂
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  -- the `kabCond` constants
  obtain ⟨hε₀u, hC₁u, hKBu, h1u, h2u, h3u, h4u⟩ :=
    Classical.choose_spec (Classical.choose_spec M.k2_cab_spec)
  have hcab : M.k2cab = 10 * kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) (Classical.choose
      (Classical.choose_spec M.k2_cab_spec)) (cx M.core.κ M.core.cT) (8 * M.core.Bk) := rfl
  set C₁ := Classical.choose (Classical.choose_spec M.k2_cab_spec) with hC₁d
  -- invariants of the restarted datum
  have hinv := fun (j : ℕ) (hmj : ms ≤ j) (hj : j ≤ Nh) =>
    pl3_delta_inv R hNh m hV hVL hL8 b μ₀ x y hms hblk hmx hmy (k := j) hmj (by omega) (by omega)
  -- sizes
  have hsz := fun (j : ℕ) (hmj : ms ≤ j) (hjJ : j ≤ Nh) =>
    M.k2_sizes N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μ₀ hD y hms0 hms _ hδ hδl hδs hδf hδp
      hδb hM0 hk hw hbR hWR hKR hg hMR (J := Nh) hms le_rfl hQ0 hQw hQk (j := j) hmj hjJ
  set Ma := k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ Nh with hMad
  set Mb := pM R' (ptsS y) (zV0 b) t Nh with hMbd
  set mm : ℕ → ℝ := fun j => k2Mj M Nh Nh ms Q j with hmmd
  have hm0 : ∀ j, 0 < mm j := fun j => k2Mj_pos M Nh Nh ms hQ0 j
  have hm1' : ∀ j, 1 ≤ mm j := fun j => one_le_k2Mj M Nh Nh ms hQ0 j
  have hcε : M.core.c * M.core.ε ≤ 1 := M.core.hcε
  have hr1 : ∀ j ≤ Nh, M.core.c * (t j).1 ≤ 1 := fun j hj => by
    have := (hD j hj).2.1
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ M.core.c)
    linarith
  have hgms : 0 ≤ (t ms).1 := (hD ms hms).1.le
  have hVo : ∀ j, ms ≤ j → j ≤ Nh → ∀ q ∈ blockIdx (L := L) (N := N) j,
      Obs2.oTo (wM Ma Mb) j (histS R' j t) ((obsHistFrom R' (ptsX y) ms
        (pl2Delta R m b μ₀ x y ms) j t).V q) ≤ ENNReal.ofReal (mm j) := fun j hmj hj =>
    (hsz j hmj hj).2.2.1 (hinv j hmj hj).Vab
  have hWo : ∀ j, ms ≤ j → j ≤ Nh → ∀ q ∈ blockIdx (L := L) (N := N) j,
      Obs2.oTo (wM Ma Mb) j (histS R' j t) ((obsHistFrom R' (ptsX y) ms
        (pl2Delta R m b μ₀ x y ms) j t).W q) ≤
        ENNReal.ofReal (cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t j).1 * mm j) :=
    fun j hmj hj => by rw [hcR]; exact (hsz j hmj hj).2.2.2.1 (hinv j hmj hj).Wab
  have hab := ct_k2_top R m (by rw [hRA']; exact hKBu) M.core.hC₀u hC₁u hSB' hNh hV hVL hm1 hmN hβ0
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H hL8 b μ₀ x y (wM Ma Mb) (wM_sub Ma Mb) ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    hms hblk hmx hjy hδ hδl hδs htN
    mm (fun j => 8 * M.core.Bk * (M.core.c * (t j).1) ^ 2 * mm j) (8 * M.core.Bk) M.k2cab
    (by positivity) hm0
    (fun j hmj hj => k2Mj_le_two M Nh Nh ms hQ0 hmj hj hj)
    (fun j => by have := hm0 j; positivity)
    (fun j hmj hj => by rw [hcR])
    (fun j hmj hj => by rw [hcR]; exact (hr1 j hj).trans (hm1' j))
    (by rw [hRA', hcab]) (by rw [hcR]; exact hcε) (by rw [hcR]; exact h1u)
    (by rw [hcR]; exact h2u)
    (by rw [hcR]; exact h3u)
    (by rw [hcR, hRA']; exact h4u)
    hVo hWo
    (fun j hmj hj X hX => by exact (hsz j hmj hj).2.2.2.2 X hX)
    (fun X hX => by
      refine (hZ X hX).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hcR]
      refine hQz.trans ?_
      have hQm : Q ≤ mm ms := by
        show Q ≤ k2Mj M Nh Nh ms Q ms
        unfold k2Mj
        have := M.core.consts_nonneg.2.2.2.2.2.1
        have := cw2Thb_pos M Nh ms
        rw [Nat.sub_self, pow_zero, one_mul]
        have : 0 ≤ (7 / 5 : ℝ) ^ (Nh - ms) := by positivity
        nlinarith
      have h0' : 0 ≤ M.k2cab * (M.core.c * (t ms).1) := mul_nonneg (M.k2cab_nonneg) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQm 2) h0')
  intro X hX
  have := hab X hX
  rw [hcR] at this
  exact this


set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The top-coalescence bound with decayed transients and `k₂` discharged** (route (c)). -/
theorem k2_conn_diff_top {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {cK0 Kt : ℝ} (hseed : TopSeedAt R Nh m b (b - m) cK0)
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
        9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2)
    (hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ)
    (hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
      ≤ 1 / 2)
    (hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀)
    (hvb : cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) +
      8 * M.core.ℓ ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hwb : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2) ≤ 1)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (y : Lam 2 L N) (hy : y ≠ 0) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    -- the pair-difference datum
    (hspl : SplitSmall R.P L R.ρ) (x : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hsc0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hsc : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1)
    (hgms : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * 2) ≤ 1 / 1344) :
    ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤ histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r) ∧
    ∀ {mm k₁ c₁ k2 Q Zab : ℝ}, 0 ≤ c₁ → 0 ≤ k2 →
      1 + cw2Thb M Nh Nh ≤ mm →
      M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + (7 / 30) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
          cw2Thb M Nh Nh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm →
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ mm →
      (56 / 75) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
          8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 +
          cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) ≤ k₁ →
      k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm →
      8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀ →
      -- route (c): sizes `m_j = k2Mj … Q j`, the datum's own `ab` activity, waiting
      0 ≤ Q →
      (7 / 5) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q →
      (7 / 5) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
        8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q →
      (∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
        ((wM (k2Ma R m b (b - m) y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) Nh)
            (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
          Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
            ((pl2Delta R m b (b - m) x y ms).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal Zab) →
      Zab ≤ M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * Q ^ 2 →
      (8 / 15) ^ (Nh - ms) * Q ≤ 1 →
      M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2) ≤ k2 →
      M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
        M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1 →
      2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
        (8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
          (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
            M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ)‖ ≤
        3 / 2 * (1 + M.fwKO) * M.ctGamB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) kk ww *
            varthJ R m b (b - m) Nh +
          9 / 4 * max (M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
            (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)) r₀) 0 *
            (cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
              (R.withMsq m).A r) * varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hid, h0, hl0, hs0', hVab, hVabN, hWabN, hf0, hp0, hδb, kk, ww, hkk, hww, hM0, hbR, hWR,
    hKR, hMR, hrel'⟩ := M.ct_T6_inputs_top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD hspl x y hk0
      hkN hmx hj hrk hblk hdist hsc0 hsc hreg
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro mm k₁ c₁ k2 Q Zab hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hQ0 hQw hQk hZ hQz hwait hk2e hsmT hmAB
  have hKab := M.k2_top N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD x y hk0 hblk hmx hj
    hkN h0 hl0 hs0' hf0 hp0 hδb hM0 hkk hww hbR hWR hKR hgms hMR hQ0 hQw hQk hZ hQz
  have hw1 := (k2_wait M Nh Nh ms hQ0 hkN le_rfl hwait).1
  have hcN : 0 ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    have := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
    have := (hD Nh le_rfl).1.le
    positivity
  have hK2 : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r)))
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X :
            Obs.SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2 := by
    intro X hX
    refine (hKab X hX).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hk2e))
    have hm0' := k2Mj_pos M Nh Nh ms hQ0 Nh
    have h5 : 0 ≤ M.k2cab / 5 := div_nonneg M.k2cab_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hm0'.le hw1 2) hcN) h5
  have hT := M.art_T5topD R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1
    hs2 hs3 hs4 hs5 hvb hwb hsmall y hy hj hk0 hkN.le _ h0 hl0 hs0' hVab hVabN hWabN hf0 hp0 hδb
    hM0 hkk hww hbR hWR hKR hgms hMR hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hK2 hsmT hmAB
  have hG := M.ct_gam_top R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX y)
    (obsInit .two (zV b) (ptsX y)) (obsInit_isObs .two (zV b) (ptsX y)) hk0 hkN.le _ h0 hl0 hs0'
    hf0 hp0 hM0 hkk hww hbR hWR hKR hgms hMR
  have hKO0 : 0 ≤ M.fwKO := by
    unfold fwKO
    have := M.topF'_nonneg; have := M.topCL_nonneg
    have : 0 ≤ max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 := le_max_right _ _
    positivity
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hv : 0 ≤ varthJ R m b (b - m) Nh := by
    unfold varthJ; exact Real.rpow_nonneg (div_nonneg hb.le (hD Nh le_rfl).1.le) _
  rw [hid]
  refine (hT.trans (add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hG (by positivity)) hv) le_rfl)).trans (add_le_add le_rfl ?_)
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hβs := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl (zV_mua_ne hb0) (by omega) ms (by omega)).1
  have hσ := M.ct_sig_cmp N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD y _ h0 hkN.le (by omega)
    hM0.le
  have hXY : ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms)
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) /
        ‖hBeta R m b (b - m) y Nh‖ ≤
      cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0) (R.withMsq m).A r := by
    refine hσ.trans (mul_le_mul_of_nonneg_left ?_ (cw4Cmp_pos M _).le)
    rw [div_le_iff₀ hβs]
    exact hrel'
  have hX0 : 0 ≤ ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms)
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) /
        ‖hBeta R m b (b - m) y Nh‖ := by
    refine div_nonneg ?_ (norm_nonneg _)
    unfold ctSig Obs2.rkEnv
    exact mul_nonneg hM0.le (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hv : 0 ≤ varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 :=
    mul_nonneg (sq_nonneg _) (hD Nh le_rfl).1.le
  set K := M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
    (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)) r₀
  have hKX := mul_le_mul (le_max_left K 0) hXY hX0 (le_max_right K 0)
  have := mul_le_mul_of_nonneg_right hKX hv
  have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 9 / 4)
  calc _ = 9 / 4 * (K * (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms)
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) /
        ‖hBeta R m b (b - m) y Nh‖) * (varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) := by ring
    _ ≤ _ := this
    _ = _ := by ring

end MasterFacts

end

end Spin2
