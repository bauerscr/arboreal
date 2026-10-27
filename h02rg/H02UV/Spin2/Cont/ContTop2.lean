import Spin2.Cont.ContTop1
import Spin2.Cont.ContWire2
import Spin2.Master.MasterAllFactsD

set_option autoImplicit false

/-!
# Top coalescence: the top-step error of the restarted flow, linear form and along `D_ε`

* **`MasterCore.ct_restartDT_top_lin`**: `ct_restartDT_top` for the data of `restartDT_lin`
  (`w₀ = w`, `k₀ = k + 120B(cε)w`; copy of `cw2_restartDT_lin`).
* **`MasterFacts.ct_restartTop`**: the same with the reference vertex `zV b`, the input
  `|𝔫^{(2)}_{N_h}| ≤ 1/8` discharged by `TopConclD` (`M.topD`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **The top-step error, linear form**: the data of `MasterCore.restartDT_lin`, the
conclusions of `MasterCore.ct_restartDT_top` with `w₀ = w`, `k₀ = k + 120B(cε)w`. -/
theorem MasterCore.ct_restartDT_top_lin (D : MasterCore L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A)
    (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N)
    (b μ₀ : ℝ) (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (mr : ℕ) (o' : Obs2.ObsSt .two L N)
    (hmr0 : 0 < mr) (hmrN : mr ≤ Nh) (h0 : o'.IsObs) (hl0 : ObsLocInv P mr o')
    (hs0 : ObsSymInv mr o')
    (hf0 : ∀ b, Obs2.Loc2Form P.a (o'.V b : Obs.SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : Obs.SA .two (Lam 2 L N)).a =
      Obs.LocObs.mass2 (o'.V b : Obs.SA .two (Lam 2 L N)).a • Obs.LocObs.pbp P.a)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hb : ‖Obs2.betaTot2 (L := L) (N := N) mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr)‖ +
        Obs2.shareDev2 P.a mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr) ≤ M₀)
    (hW : WbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr w)
    (hK : KbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr k)
    (hg : D.rdtC * (D.cWo * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ mr).1) * 2) ≤ 1 / 1344)
    (hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + D.rdtΓ * w) ≤
      histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)
    (hn8N : ‖Obs2.frakN2 P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) Nh‖ ≤ 1 / 8) :
      (∀ j ≤ Nh - mr,
        ‖Obs2.betaTot2 (L := L) (N := N) (mr + j)
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + j))‖ +
          Obs2.shareDev2 P.a (mr + j) (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + j)) ≤
          2 * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) j) ∧
      Obs2.shareErrL1_2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (histWF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histKF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh ≤
        (D.cδ * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ^ 2 *
            ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh‖ +
          1 / 24 * (3 / 4) ^ (Nh - mr)) * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) (Nh - mr) ∧
      ‖Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh‖ ≤ 1 / 7 := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set s := histS (R.withMsq m) mr t with hsd
  obtain ⟨H, -, -⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
    rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
  have hc2 : 2 ≤ D.c := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hε0 : 0 ≤ D.ε := by have := H.hε; linarith
  have hcε : 0 ≤ D.c * D.ε := mul_nonneg (by linarith) hε0
  have hBk : 0 ≤ D.Bk := D.consts_nonneg.2.2.2.2.2.2.1
  have hcP : 0 ≤ D.cP := by
    show 0 ≤ (cbnC : ℝ) * D.Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := D.hCpf L; positivity
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id D.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρ8'
  have hs : 0 < s := histS_pos' (R.withMsq m) hρ0 hρ8 t mr
  have hX : 0 < s ^ 2 * M₀ := by positivity
  have hkw0 : 0 ≤ 120 * D.Bk * (D.c * D.ε) * w := by positivity
  have hct0 := rdt_ct_le (cN := (PtCorr2.csN 2 : ℝ)) (k := k) (w := w) (x := s ^ 2)
    (C := D.rdtC) (a := D.cWo) (g := D.c * (t mr).1) (Bce := 120 * D.Bk * (D.c * D.ε))
    (cPce := 5 * D.cP * (D.c * D.ε)) (by positivity) hX hM0 D.rdt_L
    (by
      have e : D.rdtΓ * w = (8 * (PtCorr2.csN 2 : ℝ) * (120 * D.Bk * (D.c * D.ε)) + D.rdtC +
          5 * D.cP * (D.c * D.ε)) * w := by unfold MasterCore.rdtΓ; ring
      rw [← e]; exact hM) hg
  have hct : 8 * (PtCorr2.csN 2 : ℝ) * (k + 120 * D.Bk * (D.c * D.ε) * w) / (s ^ 2 * M₀) +
        cbnC * (1280 * Obs2.locK 2 ^ 2 * (8 / (7 * L)) + 1) *
          (D.cWo * (D.c * (t mr).1) * (2 * s ^ 2 * M₀) + w) / (s ^ 2 * M₀) +
        4 / 3 * (2 / (L : ℝ)) + 5 * D.cP * (D.c * D.ε) * w / (s ^ 2 * M₀) ≤ 1 / 48 := hct0
  have hW' : WbHF (R.withMsq m) P mr o' t mr
      (D.cWo * (D.c * (t mr).1) * (2 * s ^ 2 * M₀) + w) := by
    intro b' hb'
    refine (hW b' hb').trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 1 ≤ D.cWo := D.consts_nonneg.2.2.2.2.2.1
    have hg0 : 0 ≤ (t mr).1 := by
      have := (inDh_rg_of_D (R.withMsq m) (D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).2.2 hD
        Nh le_rfl).1 mr hmrN
      exact this.1.le
    have : 0 ≤ D.cWo * (D.c * (t mr).1) * (2 * s ^ 2 * M₀) := by positivity
    linarith
  have key := D.ct_restartDT_top N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V mr o' hmr0 hmrN h0
    hl0 hs0 hf0 hp0 M₀ (k + 120 * D.Bk * (D.c * D.ε) * w) w hM0 (by linarith) hw (by linarith)
    hct hb hW'
    (fun X hX' => (hK X hX').trans (ENNReal.ofReal_le_ofReal (by linarith))) hn8N
  exact key


set_option maxHeartbeats 1000000 in
/-- **The top-step error of the restarted flow along `D_ε`** (reference vertex `zV b`):
for the data of `restartDT_lin`, `|β_{m_r+j}| + D_{m_r+j} ≤ 2M_j` (`j ≤ N_h − m_r`),
`E_{N_h} ≤ (c_δ(cǧ_{N_h})²a_{N_h} + (1/24)(3/4)^{N_h−m_r})M_{N_h−m_r}`, `|𝔫F_{N_h}| ≤ 1/7`. -/
theorem MasterFacts.ct_restartTop (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N)
    (b μ₀ : ℝ) (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (mr : ℕ) (o' : Obs2.ObsSt .two L N)
    (hmr0 : 0 < mr) (hmrN : mr ≤ Nh) (h0 : o'.IsObs) (hl0 : ObsLocInv P mr o')
    (hs0 : ObsSymInv mr o')
    (hf0 : ∀ b, Obs2.Loc2Form P.a (o'.V b : Obs.SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : Obs.SA .two (Lam 2 L N)).a =
      Obs.LocObs.mass2 (o'.V b : Obs.SA .two (Lam 2 L N)).a • Obs.LocObs.pbp P.a)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hb : ‖Obs2.betaTot2 (L := L) (N := N) mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr)‖ +
        Obs2.shareDev2 P.a mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr) ≤ M₀)
    (hW : WbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr w)
    (hK : KbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ mr).1) *
      2) ≤ 1 / 1344)
    (hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) :
      (∀ j ≤ Nh - mr,
        ‖Obs2.betaTot2 (L := L) (N := N) (mr + j)
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + j))‖ +
          Obs2.shareDev2 P.a (mr + j) (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + j)) ≤
          2 * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) j) ∧
      Obs2.shareErrL1_2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (histWF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (histKF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh ≤
        (M.core.cδ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ^ 2 *
            ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh‖ +
          1 / 24 * (3 / 4) ^ (Nh - mr)) * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) (Nh - mr) ∧
      ‖Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr Nh‖ ≤ 1 / 7 :=
  M.core.ct_restartDT_top_lin N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P (zV b) mr o' hmr0
    hmrN h0 hl0 hs0 hf0 hp0 hM0 hk hw hb hW hK hg hM
    (M.topD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P).1.1

end

end Spin2
