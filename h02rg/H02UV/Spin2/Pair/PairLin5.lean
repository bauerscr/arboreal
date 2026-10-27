import Spin2.Cont.ContWire9
import Spin2.Restart.RestartPairTopF1

set_option autoImplicit false

/-!
# B3, T6 (Task 3, chain part): the accumulated `a`-constant of the restarted history at `j_y ≤ N_h`

For a restart datum `δ` at `m_r` (observable, local, `U(1)`-invariant, `Loc2Form`, pure
`V(B)_a = β_Bψ̄_aψ_a`) with the restart data of `MasterCore.restartDT_lin` (those of
`MasterFacts.cw3_T5R`), along a `D_ε` trajectory and for `m_r ≤ j ≤ N_h` (here `j = j_y`):

* `pl5_epsTot_zero`: `∑_Bε(V^δ(B)_a) = 0` at `m_r` (pure form);
* `pl5_beta_le_shA2`: `|β^F_k| ≤ shA2F k`;
* **`MasterFacts.pl5_gamWKF`**: `|gamWKF_{m_r+i}| ≤ c_N8k_i + |C_{m_r+i}(0,0)|c_N8k_is_{m_r+i}^{−2}
  + c_{Bn}Q_1w_i` with the restart envelopes of `cw2_restartDT_lin`
  (`w_i = c_W cǧ_{m_r+i}·2s²E_i + 6^{−i}w`, `k_i = (8/15)^i(k + 120B(cε)w) + 15c_WB(cǧ)²s²E_i`,
  `E_i = rkEnv M₀ (|1 − 𝔫F|) i`; `rpg_gamWKF_le`);
* **`MasterFacts.pl5_gam_jy`**: `‖ε(u_a(cw2O R m b y m_r δ))‖ ≤ ‖ε(δ.u_a)‖ + pl5Gam …`,
  `pl5Gam = ∑_{i < j_y − m_r}(2E_i(1 + c_e(ǧ + zA))|Γ^{int}_{m_r+i+1}(0,0)| + gamWK-bound_i)`
  (`rpg_gam_le`, `rpg_C_le` with `M.gamBulkD`). The only term not controlled by the restart
  envelopes is the initial `‖ε(δ.u_a)‖`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

/-- `∑_Bε(V(B)_a) = 0` at the restart scale for a pure datum. -/
theorem pl5_epsTot_zero {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : ObsPts 2 L N) (m : ℕ) (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))
    (hp : ∀ q, (o'.V q : SA .two (Lam 2 L N)).a =
      LocObs.mass2 (o'.V q : SA .two (Lam 2 L N)).a • LocObs.pbp P.a) :
    epsTotF R P m o' t m = 0 := by
  unfold epsTotF
  refine sum_eq_zero fun q _ => ?_
  rw [histVF2_a, obsHistFrom_self, hp q, map_smul, Obs.LocObs.eps_pbp, smul_zero]

/-- `|β^F_k| ≤ shA2F k`. -/
theorem pl5_beta_le_shA2 {d N : ℕ} (V : ℕ → OFam .two d L N) (k : ℕ) :
    ‖betaTot2 (L := L) (N := N) k (V k)‖ ≤ shA2 V k :=
  norm_sum_le _ _

/-- The restart envelope `E_i = M₀∏_{l<i}|1 − 𝔫F_{m_r+l}|` at `y`. -/
def pl5Env {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b : ℝ) (y : Lam 2 L N)
    (mr : ℕ) (δ : ObsSt .two L N) (M₀ : ℝ) (i : ℕ) : ℝ :=
  rkEnv M₀ (fun l => ‖1 - frakN2F (ptsX y) (histCovO (R.withMsq m)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
    (histVF2 (R.withMsq m) (ptsX y) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) mr
      (mr + l)‖) i

/-- The `K`-envelope `k_i` of `cw2_restartDT_lin`. -/
def pl5KK (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b : ℝ) (y : Lam 2 L N) (mr : ℕ) (δ : ObsSt .two L N) (M₀ k w : ℝ) (i : ℕ) : ℝ :=
  (8 / 15) ^ i * (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) + 15 * M.core.cWo * M.core.Bk *
    (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (mr + i)).1) ^ 2 *
    (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
      pl5Env R m b y mr δ M₀ i)

/-- The `𝒲`-envelope `w_i` of `cw2_restartDT_lin`. -/
def pl5WW (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b : ℝ) (y : Lam 2 L N) (mr : ℕ) (δ : ObsSt .two L N) (M₀ w : ℝ) (i : ℕ) : ℝ :=
  M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (mr + i)).1) *
    (2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
      pl5Env R m b y mr δ M₀ i) + (1 / 6) ^ i * w

/-- The bound of `gamWKF_{m_r+i}` from the envelopes. -/
def pl5GW (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b : ℝ) (y : Lam 2 L N) (mr : ℕ) (δ : ObsSt .two L N) (M₀ k w : ℝ) (i : ℕ) : ℝ :=
  csN 2 * (8 * pl5KK M R m b y mr δ M₀ k w i) +
    ‖histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) (mr + i)
        (ptsX y).a (ptsX y).a‖ *
      (csN 2 * (8 * pl5KK M R m b y mr δ M₀ k w i) *
        (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))⁻¹ ^ 2) +
    (cBn : ℝ) * (Q1 2 * pl5WW M R m b y mr δ M₀ w i)

/-- The chain part of the `γ`-bound at `j_y`. -/
def pl5Gam (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b : ℝ) (y : Lam 2 L N) (mr : ℕ) (δ : ObsSt .two L N) (M₀ k w : ℝ) : ℝ :=
  ∑ i ∈ range (Obs.coal L (0 : Lam 2 L N) y - mr),
    (2 * pl5Env R m b y mr δ M₀ i * ((1 + M.core.cGB *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (mr + i)).1 + zA L m (mr + i))) *
          ‖gamT R m b (b - m) (mr + i)‖) + pl5GW M R m b y mr δ M₀ k w i)

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **`gamWKF` of the restarted history from the restart envelopes.** -/
theorem pl5_gamWKF (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (y : Lam 2 L N) {mr : ℕ} (hmr0 : 0 < mr) (hmrN : mr ≤ Nh)
    (δ : ObsSt .two L N) (h0 : δ.IsObs) (hl0 : ObsLocInv (ptsX y) mr δ)
    (hs0 : ObsSymInv mr δ)
    (hf0 : ∀ q, Obs2.Loc2Form (ptsX y).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      LocObs.mass2 (δ.V q : SA .two (Lam 2 L N)).a • LocObs.pbp (ptsX y).a)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖betaTot2 (L := L) (N := N) mr (histVF2 (R.withMsq m) (ptsX y) mr δ
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr)‖ +
      shareDev2 (ptsX y).a mr (histVF2 (R.withMsq m) (ptsX y) mr δ
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX y) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr w)
    (hKR : KbHF (R.withMsq m) (ptsX y) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) mr).1) * 2) ≤ 1 / 1344)
    (hMR : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)
    {i : ℕ} (hi : mr + i < Nh) :
    ‖betaTot2 (L := L) (N := N) (mr + i) (histVF2 (R.withMsq m) (ptsX y) mr δ
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) (mr + i))‖ ≤ 2 * pl5Env R m b y mr δ M₀ i ∧
    ‖gamWKF (R.withMsq m) (ptsX y) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) (mr + i)‖ ≤
      pl5GW M R m b y mr δ M₀ k w i := by
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) with htd
  have hL49 : 49 ≤ L := M.core.hL49
  have hF := M.flow
  have hval : ∀ j < Nh, ValidAt R' j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL R' Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := hF
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have ht := inDh_rg_of_D R' F1 hD
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by
    rw [show R'.A = M.core.A from hRA]; exact M.core.hSBx
  have X := c2ctx_master R' hNh hL49 hSB' H hm1 hval hvalL hρ0' hρ8' hm M.core.hβε (ht Nh le_rfl)
  have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    rw [abs_of_nonneg X.hm0]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by
      have : (1 : ℝ) ≤ 49 := by norm_num
      exact this.trans (by exact_mod_cast hL49)) (by omega)) 2
  have hβ2 := betaL_ge (by omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  obtain ⟨⟨hA, -, -⟩, hWi, hKi⟩ := M.core.cw2_restartDT_lin N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b
    (b - m) hD (ptsX y) (zV0 b) mr δ hmr0 hmrN h0 hl0 hs0 hf0 hp0 hM0 hk hw hbR hWR hKR hg hMR i
    (by omega)
  refine ⟨(pl5_beta_le_shA2 _ _).trans hA, ?_⟩
  have hE0 : 0 ≤ pl5Env R m b y mr δ M₀ i := by
    unfold pl5Env rkEnv; exact mul_nonneg hM0.le (prod_nonneg fun _ _ => norm_nonneg _)
  have hc2 : 0 ≤ M.core.c := by
    have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    have := two_le_cR R' H.hcmu H.hC₂; linarith
  have hg0 : 0 ≤ (t (mr + i)).1 := (hD (mr + i) (by omega)).1.le
  have hε0 : 0 ≤ M.core.ε := by have := H.hε; linarith
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
  have hkk0 : 0 ≤ pl5KK M R m b y mr δ M₀ k w i := by unfold pl5KK; positivity
  have hww0 : 0 ≤ pl5WW M R m b y mr δ M₀ w i := by unfold pl5WW; positivity
  exact rpg_gamWKF_le R' hSB' hval hvalL hm1 hmN hβ0 (by norm_num) H M.core.hLpl (ptsX y) δ hl0 t
    (mr + i) (by omega) (by omega) (by omega) (ht (mr + i) (by omega)) hww0 hkk0 hWi hKi

set_option maxHeartbeats 4000000 in
/-- **The accumulated `a`-constant of the restarted history at `j_y ≤ N_h`.** -/
theorem pl5_gam_jy (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (y : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh) {mr : ℕ} (hmr0 : 0 < mr)
    (hmrj : mr ≤ Obs.coal L (0 : Lam 2 L N) y)
    (δ : ObsSt .two L N) (h0 : δ.IsObs) (hl0 : ObsLocInv (ptsX y) mr δ)
    (hs0 : ObsSymInv mr δ)
    (hf0 : ∀ q, Obs2.Loc2Form (ptsX y).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      LocObs.mass2 (δ.V q : SA .two (Lam 2 L N)).a • LocObs.pbp (ptsX y).a)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖betaTot2 (L := L) (N := N) mr (histVF2 (R.withMsq m) (ptsX y) mr δ
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr)‖ +
      shareDev2 (ptsX y).a mr (histVF2 (R.withMsq m) (ptsX y) mr δ
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX y) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr w)
    (hKR : KbHF (R.withMsq m) (ptsX y) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) mr).1) * 2) ≤ 1 / 1344)
    (hMR : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀) :
    ‖ε (((cw2O R m b y mr δ).u : SA .two (Lam 2 L N)).a)‖ ≤
      ‖ε ((δ.u : SA .two (Lam 2 L N)).a)‖ + pl5Gam M R m b y mr δ M₀ k w := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) with htd
  set jy := Obs.coal L (0 : Lam 2 L N) y with hjyd
  have hF := M.flow
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hGB := M.gamBulkD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD
  have hgl := rpg_gam_le (R.withMsq m) (ptsX y) mr δ t h0 hf0
    (obsInit .two (zV0 b) (ptsX y)) (obsInit_isObs .two _ _) (jy - mr)
  rw [show mr + (jy - mr) = jy by omega] at hgl
  have hE : (if jy - mr = 0 then (0 : ℝ) else ‖epsTotF (R.withMsq m) (ptsX y) mr δ t mr‖) = 0 := by
    rw [pl5_epsTot_zero (R.withMsq m) (ptsX y) mr δ t hp0, norm_zero]; simp
  rw [hE, add_zero] at hgl
  have hg0 : gamF (R.withMsq m) (ptsX y) mr δ t mr = -ε ((δ.u : SA .two (Lam 2 L N)).a) := by
    unfold gamF; rw [obsHistFrom_self]
  rw [hg0, norm_neg] at hgl
  have hlhs : ‖ε (((cw2O R m b y mr δ).u : SA .two (Lam 2 L N)).a)‖ =
      ‖gamF (R.withMsq m) (ptsX y) mr δ t jy‖ := by
    rw [show gamF (R.withMsq m) (ptsX y) mr δ t jy =
      -ε (((cw2O R m b y mr δ).u : SA .two (Lam 2 L N)).a) from rfl, norm_neg]
  rw [hlhs]
  refine hgl.trans (add_le_add le_rfl ?_)
  unfold pl5Gam
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  obtain ⟨hB, hW⟩ := M.pl5_gamWKF N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b hD y hmr0 (by omega) δ
    h0 hl0 hs0 hf0 hp0 hM0 hk hw hbR hWR hKR hg hMR (i := i) (by omega)
  have hC := rpg_C_le R hP hval hGB (ptsX y) (obsInit .two (zV0 b) (ptsX y))
    (obsInit_isObs .two _ _) (k := mr + i) (by omega)
  refine add_le_add ?_ hW
  exact mul_le_mul hB hC (norm_nonneg _) ((norm_nonneg _).trans hB)

end MasterFacts

end

end Spin2
