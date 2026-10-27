import Spin2.Cont.ContTop5

set_option autoImplicit false

/-!
# The backward `γ` chain of the restarted history: from `N_h + 1` down to `j_y`

* **`nb_gam_back`** (exact chain, `m < j`): `|γ^F_j| ≤ |γ^F_{j+d}| + ∑_{i<d}(|β^F_{j+i}||c_{j+i}| +
  |gamWKF_{j+i}|)` (`rpg_gam_succ`; no `∑_Bε(V(B)_a)` term above the restart scale,
  `rpg_epsTot_succ`).
* **`MasterFacts.nb_gam_back_top`** (data of `restartDT_lin` at `ms`, `ms < j_y ≤ N_h`):
  `|γ^F_{j_y}| ≤ |γ^F_{N_h+1}| + nbGB`, with
  `nbGB = ∑_{i<N_h−j_y}(2M_{j_y+i−ms}(1 + c_{GB}(ǧ + zA))‖gamT‖ + G_{j_y+i−ms})
     + 2M_{N_h−ms}(‖gamT N_h‖ + gbKb·ǧ_{N_h}/zH(N_h+1)) + G_{N_h−ms}`
  (the same per-step bounds as `ct_gam_top`: `ct_restartTop`, `rpg_gamWKF_le`, `rpg_C_le`,
  `rptf_C_topD`). Combined with the `h = 0` identity at `N_h + 1` this bounds `ε(u^δ_{j_y,a})`
  without the initial `ε(δ.u_a)`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L : ℕ} [NeZero L]

section Back

variable {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : Obs2.ObsPts 2 L N)
  (m : ℕ) (o' : Obs2.ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))

/-- **The backward `γ` chain** (`m < j`). -/
theorem nb_gam_back (h0 : o'.IsObs)
    (hf0 : ∀ b, Obs2.Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (o₀ : Obs2.ObsSt .two L N) (ho₀ : o₀.IsObs) {j : ℕ} (hj : m < j) :
    ∀ d : ℕ, ‖gamF R P m o' t j‖ ≤ ‖gamF R P m o' t (j + d)‖ +
      ∑ i ∈ range d, (‖Obs2.betaTot2 (j + i) (histVF2 R P m o' t (j + i))‖ *
        ‖rpgC R P t o₀ (j + i)‖ + ‖gamWKF R P m o' t (j + i)‖)
  | 0 => by simp
  | d + 1 => by
    have ih := nb_gam_back h0 hf0 o₀ ho₀ hj d
    have hs := rpg_gam_succ R P m o' t h0 hf0 o₀ ho₀ (k := j + d) (by omega)
    have hE : epsTotF R P m o' t (j + d) = 0 := by
      rw [show j + d = (j + d - 1) + 1 by omega]
      exact rpg_epsTot_succ R P m o' t (by omega)
    rw [hE, sub_zero] at hs
    have e : gamF R P m o' t (j + d) = gamF R P m o' t (j + (d + 1)) +
        Obs2.betaTot2 (j + d) (histVF2 R P m o' t (j + d)) * rpgC R P t o₀ (j + d) -
        gamWKF R P m o' t (j + d) := by
      rw [show j + (d + 1) = j + d + 1 by omega, hs]; ring
    have h1 : ‖gamF R P m o' t (j + d)‖ ≤ ‖gamF R P m o' t (j + (d + 1))‖ +
        (‖Obs2.betaTot2 (j + d) (histVF2 R P m o' t (j + d))‖ * ‖rpgC R P t o₀ (j + d)‖ +
          ‖gamWKF R P m o' t (j + d)‖) := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have := norm_add_le (gamF R P m o' t (j + (d + 1)))
        (Obs2.betaTot2 (j + d) (histVF2 R P m o' t (j + d)) * rpgC R P t o₀ (j + d))
      rw [norm_mul] at this
      linarith
    rw [sum_range_succ]
    linarith

end Back

namespace MasterFacts

variable (M : MasterFacts L)

/-- The backward chain bound from `N_h + 1` down to `j_y` (per-step bounds of `ct_gam_top`). -/
def nbGB {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (m b μ₀ : ℝ) (Nh : ℕ)
    (P : Obs2.ObsPts 2 L N) (ms : ℕ) (o' : Obs2.ObsSt .two L N) (M₀ k w : ℝ) (jy : ℕ) : ℝ :=
  ∑ i ∈ range (Nh - jy), (2 * ctEnv R m b μ₀ P ms o' M₀ (jy + i - ms) * ((1 + M.core.cGB *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (jy + i)).1 + zA L m (jy + i))) *
        ‖gamT R m b μ₀ (jy + i)‖) + M.ctGw R m b μ₀ P ms o' M₀ k w (jy + i - ms)) +
    (2 * ctEnv R m b μ₀ P ms o' M₀ (Nh - ms) * (‖gamT R m b μ₀ Nh‖ +
      gbKb L (R.withMsq m).ℓ (cmu ((L : ℝ) ^ 2) M.core.cm)
      (cZ (R.withMsq m)) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 /
        zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) +
      M.ctGw R m b μ₀ P ms o' M₀ k w (Nh - ms))

set_option maxHeartbeats 4000000 in
/-- **The backward `γ` chain from `N_h + 1` down to `j_y`** (restart envelopes). -/
theorem nb_gam_back_top {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
      histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)
    {jy : ℕ} (hmj : ms < jy) (hjN : jy ≤ Nh) :
    ‖gamF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) jy‖ ≤
      ‖gamF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)‖ +
        M.nbGB R m b μ₀ Nh P ms o' M₀ k w jy := by
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
  have hB : ∀ j, ms ≤ j → j ≤ Nh → ‖Obs2.betaTot2 (L := L) (N := N) j
      (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j)‖ ≤
        2 * ctEnv R m b μ₀ P ms o' M₀ (j - ms) :=
    fun j hmj hjN => by
      have h := hbD (j - ms) (by omega)
      rw [show ms + (j - ms) = j by omega] at h
      have : 0 ≤ Obs2.shareDev2 P.a j (histVF2 (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j) :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      show _ ≤ 2 * ctEnv R m b μ₀ P ms o' M₀ (j - ms)
      unfold ctEnv
      linarith
  have hG : ∀ j, ms ≤ j → j ≤ Nh →
      ‖gamWKF (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j‖ ≤
        M.ctGw R m b μ₀ P ms o' M₀ k w (j - ms) :=
    fun j hmj hjN => by
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
      rw [show ms + (j - ms) = j by omega]
  have hGB := M.gamBulkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hCt := M.rptf_C_topD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P o₀ ho₀
  have hback := nb_gam_back (R.withMsq m) P ms o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) h0 hf0
    o₀ ho₀ hmj (Nh + 1 - jy)
  rw [show jy + (Nh + 1 - jy) = Nh + 1 by omega, show Nh + 1 - jy = (Nh - jy) + 1 by omega,
    sum_range_succ, show jy + (Nh - jy) = Nh by omega] at hback
  refine hback.trans ?_
  unfold nbGB
  refine add_le_add le_rfl (add_le_add (sum_le_sum fun i hi => ?_) ?_)
  · have hi' := mem_range.1 hi
    have hC := rpg_C_le R hP hval hGB P o₀ ho₀ (k := jy + i) (by omega)
    have hb := hB (jy + i) (by omega) (by omega)
    exact add_le_add (mul_le_mul hb hC (norm_nonneg _) ((norm_nonneg _).trans hb))
      (hG (jy + i) (by omega) (by omega))
  · exact add_le_add (mul_le_mul (hB Nh hms le_rfl) hCt (norm_nonneg _)
      ((norm_nonneg _).trans (hB Nh hms le_rfl))) (hG Nh hms le_rfl)

end MasterFacts

end

end Spin2
