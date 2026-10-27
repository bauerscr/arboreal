import Spin2.Cont.ContTop2
import Spin2.Restart.RestartPairTopF1

set_option autoImplicit false

/-!
# Top coalescence: `γ_δ` at `N_h + 1` from the restart envelopes

**`MasterFacts.ct_gam_top`**: for the data of `restartDT_lin` at `ms`, the accumulated `a`-constant
bound `rptfGam` of the restarted state at `N_h + 1` (`rptf_gam_sizes`) with
`B_k = 2M_{k−ms}` (`ct_restartTop`: `|β| + D ≤ 2M`) and `G_k` from `rpg_gamWKF_le` with the `𝒲`/`K`
envelopes of `cw2_restartDT_lin` (`ctWW`, `ctKK`):

`rptfGam ≤ ‖gamF ms‖ + ‖epsTotF ms‖ + ∑_{i<N_h−ms}(2M_i(1 + c_{GB}(ǧ + zA))‖gamT‖ + G_{ms+i})
  + 2M_{N_h−ms}(‖gamT N_h‖ + gbKb·ǧ_{N_h}/zH(N_h+1)) + G_{N_h}`.

The initial terms `‖gamF ms‖ = ‖ε(δ.u_a)‖`, `‖epsTotF ms‖ = ‖∑_Bε(δ.V(B)_a)‖` are the initial
`a`-constants of the datum (not bounded here).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

/-- The restart envelope `M_i`. -/
def ctEnv {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (M₀ : ℝ) (i : ℕ) : ℝ :=
  Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ms (ms + i)‖) i

/-- The initial terms of `γ_δ`: `‖gamF ms‖ = ‖ε(δ.u_a)‖`. -/
theorem ct_gamF_self {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (t : Hist.Seq (Xs R)) :
    ‖gamF R P ms o' t ms‖ = ‖ε ((o'.u : SA .two (Lam 2 L N)).a)‖ := by
  unfold gamF; rw [obsHistFrom_self, norm_neg]

/-- `∑_Bε(V(B)_a) = 0` at the restart scale for a pure datum (copy of `pl5_epsTot_zero`). -/
theorem ct_epsTot_zero {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (t : Hist.Seq (Xs R))
    (hp : ∀ q, (o'.V q : SA .two (Lam 2 L N)).a =
      Obs.LocObs.mass2 (o'.V q : SA .two (Lam 2 L N)).a • Obs.LocObs.pbp P.a) :
    epsTotF R P ms o' t ms = 0 := by
  unfold epsTotF
  refine sum_eq_zero fun q _ => ?_
  rw [histVF2_a, obsHistFrom_self, hp q, map_smul, Obs.LocObs.eps_pbp, smul_zero]

namespace MasterFacts

variable (M : MasterFacts L)

/-- The `𝒲` envelope at `ms + i` (`cw2_restartDT_lin`). -/
def ctWW {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (M₀ w : ℝ) (i : ℕ) : ℝ :=
  M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + i)).1) *
    (2 * histS (R.withMsq m) (ms + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ctEnv R m b μ₀ P ms o' M₀ i) +
    (1 / 6) ^ i * w

/-- The `K` envelope at `ms + i` (`cw2_restartDT_lin`). -/
def ctKK {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (M₀ k w : ℝ) (i : ℕ) : ℝ :=
  (8 / 15) ^ i * (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) + 15 * M.core.cWo * M.core.Bk *
    (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + i)).1) ^ 2 *
    (histS (R.withMsq m) (ms + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * ctEnv R m b μ₀ P ms o' M₀ i)

/-- The `K`/`𝒲` part `G_{ms+i}` of the `γ`-remainder (`rpg_gamWKF_le` with the envelopes). -/
def ctGw {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ)
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (M₀ k w : ℝ) (i : ℕ) : ℝ :=
  csN 2 * (8 * M.ctKK R m b μ₀ P ms o' M₀ k w i) +
    ‖Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (ms + i) P.a P.a‖ *
      (csN 2 * (8 * M.ctKK R m b μ₀ P ms o' M₀ k w i) *
        (histS (R.withMsq m) (ms + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
    (cBn : ℝ) * (Q1 2 * M.ctWW R m b μ₀ P ms o' M₀ w i)

set_option maxHeartbeats 4000000 in
/-- **`γ_δ` at `N_h + 1` from the restart envelopes.** -/
theorem ct_gam_top {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (o₀ : Obs2.ObsSt .two L N) (ho₀ : o₀.IsObs)
    {ms : ℕ} (hms0 : 0 < ms) (hms : ms ≤ Nh) (o' : Obs2.ObsSt .two L N) (h0 : o'.IsObs)
    (hl0 : ObsLocInv P ms o') (hs0 : ObsSymInv ms o')
    (hf0 : ∀ b, Obs2.Loc2Form P.a (o'.V b : Obs.SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : Obs.SA .two (Lam 2 L N)).a =
      Obs.LocObs.mass2 (o'.V b : Obs.SA .two (Lam 2 L N)).a • Obs.LocObs.pbp P.a)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hb : ‖Obs2.betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms)‖ +
        Obs2.shareDev2 P.a ms (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms) ≤ M₀)
    (hW : WbHF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms w)
    (hK : KbHF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) *
      2) ≤ 1 / 1344)
    (hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) :
    rptfGam (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) o₀ Nh ≤
      ‖gamF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms‖ +
        ‖epsTotF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms‖ +
        ∑ i ∈ range (Nh - ms), (2 * ctEnv R m b μ₀ P ms o' M₀ i * ((1 + M.core.cGB *
            ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + i)).1 + zA L m (ms + i))) *
              ‖gamT R m b μ₀ (ms + i)‖) + M.ctGw R m b μ₀ P ms o' M₀ k w i) +
        (2 * ctEnv R m b μ₀ P ms o' M₀ (Nh - ms) * (‖gamT R m b μ₀ Nh‖ +
          gbKb L (R.withMsq m).ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
          (cZ (R.withMsq m)) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
            zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) + M.ctGw R m b μ₀ P ms o' M₀ k w (Nh - ms)) := by
  have hF := M.flow
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL (R.withMsq m) Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hSB' : StepBounds L (R.withMsq m).A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x
      M.core.CDx M.core.Cqx M.core.Clx M.core.cSx := by
    rw [show (R.withMsq m).A = M.core.A from hRA]; exact M.core.hSBx
  have hβ2 := betaL_ge (by have := M.core.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hL49 : 49 ≤ L := M.core.hL49
  have hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    show |m| * _ ≤ 1
    rw [abs_of_pos hm.1]
    have h1 := PtCorr2.msq_mul_pow_le_one (L := L) (N := N) (by omega) (by omega) hm.2
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := M.core.hL49; omega : 1 ≤ L)
    have h2 : ((L : ℝ) ^ Nh) ^ 2 ≤ (L : ℝ) ^ (2 * (N - 1)) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
    exact (mul_le_mul_of_nonneg_left h2 hm.1.le).trans h1
  have ht := inDh_rg_of_D (R.withMsq m) F1 hD
  have hbD := (M.ct_restartTop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P ms o' hms0 hms h0
    hl0 hs0 hf0 hp0 hM0 hk hw hb hW hK hg hM).1
  have hWK := M.core.cw2_restartDT_lin N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b) ms
    o' hms0 hms h0 hl0 hs0 hf0 hp0 hM0 hk hw hb hW hK hg hM
  have hS := M.rptf_gam_sizes R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o₀ ho₀ hms o'
    (fun j => 2 * ctEnv R m b μ₀ P ms o' M₀ (j - ms)) (fun j => M.ctGw R m b μ₀ P ms o' M₀ k w (j - ms))
    (fun j hmj hjN => by
      have h := hbD (j - ms) (by omega)
      rw [show ms + (j - ms) = j by omega] at h
      have : 0 ≤ Obs2.shareDev2 P.a j (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j) :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      show _ ≤ 2 * ctEnv R m b μ₀ P ms o' M₀ (j - ms)
      unfold ctEnv
      linarith)
    (fun j hmj hjN => by
      obtain ⟨-, hWj, hKj⟩ := hWK (j - ms) (by omega)
      rw [show ms + (j - ms) = j by omega] at hWj hKj
      have e : ms + (j - ms) = j := by omega
      have hWw : 0 ≤ M.ctWW R m b μ₀ P ms o' M₀ w (j - ms) := by
        unfold ctWW ctEnv Obs2.rkEnv
        have := M.core.consts_nonneg.2.2.2.2.2.1
        have := (ht j hjN).1 j le_rfl
        have : 0 ≤ M.core.c := by
          have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
            rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
          have := two_le_cR (R.withMsq m) H.hcmu H.hC₂; linarith
        have : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + (j - ms))).1 :=
          ((ht j hjN).1 (ms + (j - ms)) (by omega)).1.le
        have : 0 ≤ ∏ i ∈ range (j - ms), ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ms (ms + i)‖ :=
          Finset.prod_nonneg fun _ _ => norm_nonneg _
        positivity
      have hKk : 0 ≤ M.ctKK R m b μ₀ P ms o' M₀ k w (j - ms) := by
        unfold ctKK ctEnv Obs2.rkEnv
        have := M.core.consts_nonneg.2.2.2.2.2.1
        have := M.core.consts_nonneg.2.2.2.2.2.2.1
        have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
          rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
        have : 2 ≤ M.core.c := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
        have : 0 ≤ M.core.ε := by have := H.hε; linarith
        have : 0 ≤ ∏ i ∈ range (j - ms), ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ms (ms + i)‖ :=
          Finset.prod_nonneg fun _ _ => norm_nonneg _
        have : 0 ≤ k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w := by positivity
        positivity
      have h := rpg_gamWKF_le (R.withMsq m) hSB' hval hvalL hm1 hmN hβ0 (by norm_num) H M.core.hLpl P
        o' hl0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j hmj hjN (by omega) (ht j hjN) hWw hKk
        (by unfold ctWW ctEnv; rw [e]; exact hWj) (by unfold ctKK ctEnv; rw [e]; exact hKj)
      refine h.trans (le_of_eq ?_)
      unfold ctGw
      rw [show ms + (j - ms) = j by omega])
  refine hS.trans (le_of_eq ?_)
  simp only [Nat.add_sub_cancel_left]
/-- The bound of `ct_gam_top` (`γ_δ` at `N_h + 1` from the restart envelopes). -/
def ctGamB {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ) (Nh : ℕ)
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (M₀ k w : ℝ) : ℝ :=
  ‖gamF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms‖ +
    ‖epsTotF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms‖ +
    ∑ i ∈ range (Nh - ms), (2 * ctEnv R m b μ₀ P ms o' M₀ i * ((1 + M.core.cGB *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (ms + i)).1 + zA L m (ms + i))) *
          ‖gamT R m b μ₀ (ms + i)‖) + M.ctGw R m b μ₀ P ms o' M₀ k w i) +
    (2 * ctEnv R m b μ₀ P ms o' M₀ (Nh - ms) * (‖gamT R m b μ₀ Nh‖ +
      gbKb L (R.withMsq m).ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
      (cZ (R.withMsq m)) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
        zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) + M.ctGw R m b μ₀ P ms o' M₀ k w (Nh - ms))

end MasterFacts

end

end Spin2
