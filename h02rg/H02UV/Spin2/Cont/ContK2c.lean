import Spin2.Cont.ContK2b
import Spin2.Cont.ContTop7

set_option autoImplicit false

/-!
# B3, T6, route (c): `hK2`, `hW2` at `j_y` and `k₂` at `N_h + 1` for the pair-difference datum

Fixed weight `w = wM(k2Ma … J, pM(ptsS y)_{N_h})`, per-scale sizes `m_j = k2Mj … Q j`
(`Spin2/Cont/ContK2b`), `k₁_j = 8B r_j²m_j`, `c₁ = 8B` (the constant of the master `kabCond`).

* **`MasterFacts.k2_mid`** (`ms < j_y ≤ N_h`, `J = j_y`): `∃ c_{ab} ≥ 0` (from `kabCond`) such that,
  for the restart data at `ms` and `Q ≥ 0` with the transient conditions of `k2_sizes` and
  `Z_{ab} ≤ c_{ab}r_{ms}Q²` (`Z_{ab}` a bound of the datum's own `ab` activity at `ms`, input
  `hK20` of `rpab_hist`):
  - `A^{(…)}w_{ab}T(K_{j_y}(X)_{ab}) ≤ c_{ab}r_{j_y}m_{j_y}²` (`rpab_hist`, `hKs`, `V_{ab}`, `𝒲_{ab}`
    from `pl3_delta_inv`);
  - `w_{ab}T(𝒲_{j_y}(q)_{ab}) ≤ e^{L²C_w(r_{j_y−1} + m_{j_y−1}²)} − 1` (`k2_wfull_step` at
    `j_y − 1`, `oTo_split_ab`).
* **`MasterFacts.k2_top`** (`N_h + 1 ≤ j_y`, `J = N_h`): `k₂ = (c_{ab}/5)r_{N_h}m_{N_h}²` at
  `N_h + 1` (`ct_k2_top`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs Obs2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- The `ab` constant of the master `kabCond` (`c_{ab} = 10B₂`, `c₁ = 8B`). -/
theorem k2_cab_spec : ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    KObsBoundsU L M.core.A M.core.C₀u M.core.ηu ε₀ C₁ ∧
    2 * (M.core.c * M.core.ε) ≤ ε₀ ∧
    8 * (cx M.core.κ M.core.cT + 8 * M.core.Bk + 10 * kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) C₁
      (cx M.core.κ M.core.cT) (8 * M.core.Bk)) * (M.core.c * M.core.ε) ^ 3 ≤ 1 ∧
    8 * (cx M.core.κ M.core.cT + 8 * M.core.Bk + 10 * kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) C₁
      (cx M.core.κ M.core.cT) (8 * M.core.Bk)) * (M.core.c * M.core.ε) ^ 3 ≤ ε₀ ∧
    8 * kθ0 L M.core.A M.core.C₀u M.core.ηu + 16 * C₁ * (M.core.c * M.core.ε) +
      8 * C₁ * (8 * (cx M.core.κ M.core.cT + 8 * M.core.Bk + 10 * kB2 (kθ0 L M.core.A M.core.C₀u
        M.core.ηu) C₁ (cx M.core.κ M.core.cT) (8 * M.core.Bk)) * (M.core.c * M.core.ε) ^ 3) ≤
        1 / 10 := by
  obtain ⟨ε₀, C₁, h0, h1, h2, h3, h4, h5, h6, -⟩ := M.core.hkab
  exact ⟨ε₀, C₁, h0, h1, h2, h3, h4, h5, h6⟩

/-- The `ab` constant `c_{ab}`. -/
def k2cab : ℝ := 10 * kB2 (kθ0 L M.core.A M.core.C₀u M.core.ηu) (Classical.choose
  (Classical.choose_spec M.k2_cab_spec)) (cx M.core.κ M.core.cT) (8 * M.core.Bk)

theorem k2cab_nonneg : 0 ≤ M.k2cab := by
  obtain ⟨-, hC₁, -⟩ := Classical.choose_spec (Classical.choose_spec M.k2_cab_spec)
  unfold k2cab kB2
  have hA2 := M.core.hA2
  have hθ : 0 ≤ kθ0 L M.core.A M.core.C₀u M.core.ηu := by
    unfold kθ0
    exact mul_nonneg M.core.hC₀u (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hcx : 0 ≤ cx M.core.κ M.core.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id M.core.hC2
    unfold cx; exact div_nonneg (by linarith) (by linarith)
  have hB := M.core.consts_nonneg.2.2.2.2.2.2.1
  positivity

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
/-- **`hK2`, `hW2` at `j_y` (intermediate coalescence).** -/
theorem k2_mid (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms : ℕ} (hms0 : 0 < ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    (hjy : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
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
    (hQw : (7 / 5) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) *
        (w / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 * Q)
    (hQk : (7 / 5) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) *
        ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) ≤
      8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) ^ 2 * Q)
    (hZ : ∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
      ((wM (k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ (Obs.coal L (0 : Lam 2 L N) y))
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)).ab *
        Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((pl2Delta R m b μ₀ x y ms).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal Zab)
    (hQz : Zab ≤ M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) * Q ^ 2) :
    (∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) y) X →
      ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) y) X - 2 ^ 2)) *
        ((wM (k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ (Obs.coal L (0 : Lam 2 L N) y))
            (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)).ab *
          Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) y)
            (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
              (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X :
                SA .two (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
          (Obs.coal L (0 : Lam 2 L N) y)).1) *
          k2Mj M Nh (Obs.coal L (0 : Lam 2 L N) y) ms Q (Obs.coal L (0 : Lam 2 L N) y) ^ 2)) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) y),
      (wM (k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ (Obs.coal L (0 : Lam 2 L N) y))
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)).ab *
        Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) y)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
            (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q :
              SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) y - 1)).1 +
          k2Mj M Nh (Obs.coal L (0 : Lam 2 L N) y) ms Q (Obs.coal L (0 : Lam 2 L N) y - 1) ^ 2))) - 1)) := by
  set jy := Obs.coal L (0 : Lam 2 L N) y with hjyd
  have hN2 : 2 ≤ N := by omega
  have hms : ms ≤ Nh := by omega
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
  have hinv := fun (j : ℕ) (hmj : ms ≤ j) (hj : j < jy) =>
    pl3_delta_inv R hNh m hV hVL hL8 b μ₀ x y hms hblk hmx hmy (k := j) hmj hj (by omega)
  -- sizes
  have hsz := fun (j : ℕ) (hmj : ms ≤ j) (hjJ : j ≤ jy) =>
    M.k2_sizes N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μ₀ hD y hms0 hms _ hδ hδl hδs hδf hδp
      hδb hM0 hk hw hbR hWR hKR hg hMR (J := jy) hmy.le hjy hQ0 hQw hQk (j := j) hmj hjJ
  set Ma := k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ jy with hMad
  set Mb := pM R' (ptsS y) (zV0 b) t Nh with hMbd
  set mm : ℕ → ℝ := fun j => k2Mj M Nh jy ms Q j with hmmd
  have hm0 : ∀ j, 0 < mm j := fun j => k2Mj_pos M Nh jy ms hQ0 j
  have hm1' : ∀ j, 1 ≤ mm j := fun j => one_le_k2Mj M Nh jy ms hQ0 j
  have hcε : M.core.c * M.core.ε ≤ 1 := M.core.hcε
  have hr1 : ∀ j ≤ Nh, M.core.c * (t j).1 ≤ 1 := fun j hj => by
    have := (hD j hj).2.1
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ M.core.c)
    linarith
  have hgms : 0 ≤ (t ms).1 := (hD ms hms).1.le
  have hjy1 : ms ≤ jy - 1 := by omega
  have hVo : ∀ j, ms ≤ j → j < jy → ∀ q ∈ blockIdx (L := L) (N := N) j,
      Obs2.oTo (wM Ma Mb) j (histS R' j t) ((obsHistFrom R' (ptsX y) ms
        (pl2Delta R m b μ₀ x y ms) j t).V q) ≤ ENNReal.ofReal (mm j) := fun j hmj hj =>
    (hsz j hmj hj.le).2.2.1 (hinv j hmj hj).Vab
  have hWo : ∀ j, ms ≤ j → j < jy → ∀ q ∈ blockIdx (L := L) (N := N) j,
      Obs2.oTo (wM Ma Mb) j (histS R' j t) ((obsHistFrom R' (ptsX y) ms
        (pl2Delta R m b μ₀ x y ms) j t).W q) ≤
        ENNReal.ofReal (cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t j).1 * mm j) :=
    fun j hmj hj => by rw [hcR]; exact (hsz j hmj hj.le).2.2.2.1 (hinv j hmj hj).Wab
  refine ⟨?_, ?_⟩
  · have hab := rpab_hist R' (by rw [hRA']; exact hKBu) M.core.hC₀u hC₁u hSB' hV hVL hm1 hmN hβ0
      (by norm_num : (1 / 2 : ℝ) ≤ 1) H (ptsX y) (wM Ma Mb) (wM_sub Ma Mb) ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      _ hδ hδl hδs t jy hjy (inDh_rg_of_D R' F1 hD jy hjy)
      (fun j hmj hj X hX => (hinv j hmj hj).Kab X hX)
      mm (fun j => 8 * M.core.Bk * (M.core.c * (t j).1) ^ 2 * mm j) (8 * M.core.Bk) M.k2cab
      (by positivity) hm0
      (fun j hmj hj => k2Mj_le_two M Nh jy ms hQ0 hmj hj (by omega))
      (fun j => by have := hm0 j; positivity)
      (fun j hmj hj => by rw [hcR])
      (fun j hmj hj => by rw [hcR]; exact (hr1 j (by omega)).trans (hm1' j))
      (by rw [hRA', hcab]) (by rw [hcR]; exact hcε) (by rw [hcR]; exact h1u)
      (by rw [hcR]; exact h2u)
      (by rw [hcR]; exact h3u)
      (by rw [hcR, hRA']; exact h4u)
      hVo hWo
      (fun j hmj hj X hX => by exact (hsz j hmj hj.le).2.2.2.2 X hX)
      (fun X hX => by
        refine (hZ X hX).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hcR]
        refine hQz.trans ?_
        have hQm : Q ≤ mm ms := by
          show Q ≤ k2Mj M Nh jy ms Q ms
          unfold k2Mj
          have := M.core.consts_nonneg.2.2.2.2.2.1
          have := cw2Thb_pos M Nh ms
          rw [Nat.sub_self, pow_zero, one_mul]
          have : 0 ≤ (7 / 5 : ℝ) ^ (jy - ms) := by positivity
          nlinarith
        have h0' : 0 ≤ M.k2cab * (M.core.c * (t ms).1) := mul_nonneg (M.k2cab_nonneg) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQm 2) h0')
    intro X hX
    have := hab jy hmy.le le_rfl X hX
    rw [hcR] at this
    exact this
  · intro q hq
    have hstep := k2_wfull_step R' M.core.hWw hSB' hV hVL hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1)
      H (ptsX y) (wM Ma Mb) (wM_sub Ma Mb) _ hδ hδl hδs t (jy - 1) hjy1 (by omega)
      (inDh_rg_of_D R' F1 hD (jy - 1) (by omega)) (mm (jy - 1))
      (by rw [hcR]; exact (hr1 (jy - 1) (by omega)).trans (hm1' _))
      (by rw [hcR]; exact hr1 (jy - 1) (by omega))
      (hVo (jy - 1) hjy1 (by omega)) (hWo (jy - 1) hjy1 (by omega)) q
    have e : jy - 1 + 1 = jy := by omega
    rw [e, hcR, Obs2.oTo_split_ab] at hstep
    exact le_trans le_add_self hstep

end MasterFacts

end

end Spin2
