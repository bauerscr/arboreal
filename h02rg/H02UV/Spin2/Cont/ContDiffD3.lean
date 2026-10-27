import Spin2.Cont.ContDiffD2

/-!
# B3, T6: the restart data of the difference datum `pl2Delta` along `D_ε` (`h = 0`)

`cd3_restartM` re-derived for the `h = 0` trajectories `(b, b − m)` in `D_ε` (not admissible) and
for the actual pair-difference datum `δ = pl2Delta R m b μ₀ x y ms` (relocated history of
`(y − x, y)` minus the history of `(0, y)`, reference `σ_b` part):

* **`MasterFacts.cdd_restart_cd3`**: the inputs of `MasterCore.restartDT_lin`/`cw2_restartDT_lin` at
  `ms` for `cd3Delta (R.withMsq m) P P' (zV0 b) ms t` along `D_ε`: `|β_{ms}| + D_{ms} ≤ M₀`,
  `WbHF … ms w`, `KbHF … ms k`, `1344(8c_Nk + Γ_ww) ≤ s_{ms}²M₀`, with
  `M₀ = M.cddM M.Kp ǧ a |β^P| |β^{P'}| s ι A r` (= `cd3M` with `K_λ = M.Kp`, `ι = rpIota 0 0`).
  Inputs along `D_ε`: `cw2_relBaseD`, `cdd_relDevD`, `cdd_iotaD`, `cdd_regD`, the grid artefact
  `cdd_art_rel` with (H_λ) from `hLam_pairD`.
* **`MasterFacts.cdd_restart_data`**: the same data for `pl2Delta` (`σ_a` parts equal,
  `cdd_delta_a`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

/-- **The envelope of the difference datum** (`cd3M` with a general `K_λ`). -/
def MasterFacts.cddM (M : MasterFacts L) (Kl g z bb bb' s ι A : ℝ) (r : ℕ) : ℝ :=
  4 * (Kl * (g + z)) * bb' + 6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') +
    1344 * (8 * (PtCorr2.csN 2 : ℝ) * (16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb) +
        16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb') +
        2 * bb * (4 * s ^ 2 / (L : ℝ) ^ r) * ι * A) +
      M.core.rdtΓ * (M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb) +
        M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb'))) / s ^ 2 + g * bb'

set_option maxHeartbeats 4000000 in
/-- **The restart data of the `cd3` difference datum for `zV0 b` along `D_ε`.** -/
theorem MasterFacts.cdd_restart_cd3 (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P P' : ObsPts 2 L N) {k r : ℕ} (hk0 : 0 < k) (hkN : k < Nh) (hrk : r ≤ k)
    (hab : blk k P.a = blk k P'.a) (hPb : P.b = P'.b)
    (hdist : supNorm (P.a - P'.a) ≤ L ^ (k - r))
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 3) ≤ 1) :
    ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
      0 < M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 (zA L m k)
        ‖bt2 R P (zV0 b) m b μ₀ k‖ ‖bt2 R P' (zV0 b) m b μ₀ k‖
        (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
        (R.withMsq m).A r ∧
      ‖betaTot2 (L := L) (N := N) k (histVF2 (R.withMsq m) P' k
          (cd3Delta (R.withMsq m) P P' (zV0 b) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k)‖ +
        shareDev2 P'.a k (histVF2 (R.withMsq m) P' k
          (cd3Delta (R.withMsq m) P P' (zV0 b) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) ≤
        M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 (zA L m k)
          ‖bt2 R P (zV0 b) m b μ₀ k‖ ‖bt2 R P' (zV0 b) m b μ₀ k‖
          (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
          (R.withMsq m).A r ∧
      WbHF (R.withMsq m) P' k
        (cd3Delta (R.withMsq m) P P' (zV0 b) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k ww ∧
      KbHF (R.withMsq m) P' k
        (cd3Delta (R.withMsq m) P P' (zV0 b) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k kk ∧
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
        histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 (zA L m k)
            ‖bt2 R P (zV0 b) m b μ₀ k‖ ‖bt2 R P' (zV0 b) m b μ₀ k‖
            (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
            (R.withMsq m).A r := by
  set V := zV0 b with hV0
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hga : OCoup2.ga V = 0 := rfl
  have hmu : OCoup2.mua V ≠ 0 := zV0_mua_ne hb0
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  set s := histS R' k t with hsd
  set g := (t k).1 with hgd
  set bb := ‖bt2 R P V m b μ₀ k‖ with hbbd
  set bb' := ‖bt2 R P' V m b μ₀ k‖ with hbb'd
  set ι := rpIota 0 0 with hιd
  have hι : 0 ≤ ι := by have := one_le_rpIota (le_refl (0 : ℝ)) (le_refl (0 : ℝ)); linarith
  have hI := fun b' (hq : b' ∈ blockIdx (L := L) (N := N) k) =>
    M.cdd_iotaD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD hkN (cd3O R' P V k t)
      (obsHist_isObs R' P (obsInit .two V P) (obsInit_isObs .two V P) k t) P.a P'.a
      (cd3Beta R' P V k t) b' hq
  have hKb := M.cdd_regD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD hkN hreg
  have hNh0 : 0 < Nh := by omega
  -- bulk validity
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hval := hist_valid R' hV t (n := k + 1) (by omega)
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hsp : 0 < s := histS_pos' R' hρ0' hρ8' t k
  have hgp : 0 < g := (hD k (by omega)).1
  -- the one-point data
  obtain ⟨hbb0, hsh, hWP, hKP⟩ := M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V hga
    hmu hNh0 k hkN.le
  obtain ⟨hbb0', -, hWP', hKP'⟩ := M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P' V
    hga hmu hNh0 k hkN.le
  have hDP := M.core.cdd_relDevD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P V hga hmu hNh0 k
    hkN.le
  have hDP' := M.core.cdd_relDevD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P' V hga hmu hNh0 k
    hkN.le
  have hβδ : ‖betaTot2 k (cd3Delta R' P P' V k t).V‖ ≤ 4 * (M.Kp * (g + zA L m k)) * bb' := by
    have e := cd_delta_beta R P P' (zV0 b) m b μ₀ k
      (cd3Beta (R.withMsq m) P (zV0 b) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    have h := cdd_art_rel R P P' (zV b) (zV_mua_ne hb0)
      (M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN hNh hm hD P)
      (M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN hNh hm hD P') hkN hs0 hs
    rw [cdd_bt2_zV0 R P m b μ₀ hk0, cdd_bt2_zV0 R P' m b μ₀ hk0, ← e] at h
    exact h
  -- constants
  obtain ⟨-, -, -, -, -, hcWo, hBk, hcδ, -, -⟩ := M.core.consts_nonneg
  have hc2 : 0 ≤ M.core.c := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    have := hcR ▸ two_le_cR R' H.hcmu H.hC₂
    linarith
  have hβL : 0 ≤ betaL L := by
    have := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega); linarith
  have hA1 : 1 ≤ R'.A := by
    rw [show R'.A = M.core.A from hRA]; linarith [M.core.hA2]
  -- structure
  obtain ⟨h0, hl0, hsy0, hf0, hp0⟩ := cd3_struct R' P P' V hga k t hval hab hPb
  -- sizes
  have hcW0 : 0 ≤ M.core.cWo := by linarith
  have hcg : 0 ≤ M.core.c * g := mul_nonneg hc2 hgp.le
  have hx1 : 0 ≤ M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb) :=
    mul_nonneg (mul_nonneg hcW0 hcg) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (norm_nonneg _))
  have hx2 : 0 ≤ M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb') :=
    mul_nonneg (mul_nonneg hcW0 hcg) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (norm_nonneg _))
  have hW := cd3_W R' P P' V k t hx1 hx2 hWP hWP'
  obtain ⟨ww, hwwd⟩ : ∃ x, x = M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb) +
      M.core.cWo * (M.core.c * g) * (2 * s ^ 2 * bb') := ⟨_, rfl⟩
  rw [← hwwd] at hW
  have hww : 0 ≤ ww := by rw [hwwd]; exact add_nonneg hx1 hx2
  obtain ⟨k₁, hk₁d⟩ : ∃ x, x = 16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb) :=
    ⟨_, rfl⟩
  obtain ⟨k₂, hk₂d⟩ : ∃ x, x = 16 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 * (s ^ 2 * bb') :=
    ⟨_, rfl⟩
  have hk₁0 : 0 ≤ k₁ := by
    rw [hk₁d]; exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hBk) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have hk₂0 : 0 ≤ k₂ := by
    rw [hk₂d]; exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hBk) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have hKP1 : KbHc R' P (obsInit .two V P) t k k₁ := by rw [hk₁d]; exact hKP
  have hKP2 : KbHc R' P' (obsInit .two V P') t k k₂ := by rw [hk₂d]; exact hKP'
  have hLp : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨kk, hkkd⟩ : ∃ x, x = k₁ + k₂ + 2 * bb * (4 * s ^ 2 / (L : ℝ) ^ r) * ι * R'.A :=
    ⟨_, rfl⟩
  have hkk : 0 ≤ kk := by
    rw [hkkd]
    have : 0 ≤ 2 * bb * (4 * s ^ 2 / (L : ℝ) ^ r) * ι * R'.A :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
        (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) _)))
        hι) (by linarith)
    linarith
  have hβs : ∑ b' ∈ blockIdx (L := L) (N := N) k, ‖cd3Beta R' P V k t b'‖ ≤ 2 * bb := by
    refine le_trans (le_of_eq ?_) hsh
    exact sum_congr rfl fun b' _ => by rw [cd3_mass]; rfl
  have hOo := obsHist_isObs R' P (obsInit .two V P) (obsInit_isObs .two V P) k t
  have hK0 := r3_delta_KbHF R' P' k t P.a P'.a (cd3Beta R' P V k t)
    (o := cd3O R' P V k t) (o' := cd3O R' P' V k t) hOo hk₁0 hk₂0 hι hA1 hKP1 hKP2 hI hKb hβs hsp
  have hK : KbHF R' P' k (cd3Delta R' P P' V k t) t k kk := by
    intro X hX
    refine (hK0 X hX).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := cd2_reloc_le (s := s) hLp hrk hdist
    have hA0 : 0 ≤ R'.A := by linarith
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg
        (bt2 R P V m b μ₀ k)))) hι) hA0
    rw [hkkd]
    linarith only [h3]
  -- the envelope
  have hε0 : 0 ≤ M.core.ε := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    have := H.hε; linarith
  have hΓ := M.core.rdtΓ_nonneg hc2 hε0
  have hX : 0 ≤ 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) :=
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Nat.cast_nonneg _)) hkk) (mul_nonneg hΓ hww))
  have hb0 : 0 ≤ 4 * (M.Kp * (g + zA L m k)) * bb' +
      6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') := by
    refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (norm_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcδ (mul_nonneg (sq_nonneg _)
        (div_nonneg hgp.le (by linarith))))) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hgb : 0 < g * bb' := mul_pos hgp hbb0'
  have hMe : M.cddM M.Kp g (zA L m k) bb bb' s ι R'.A r =
      (4 * (M.Kp * (g + zA L m k)) * bb' +
        6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb')) +
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2 + g * bb' := by
    rw [hkkd, hwwd, hk₁d, hk₂d]; rfl
  have hXs : 0 ≤ 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2 :=
    div_nonneg hX (sq_nonneg _)
  have hM0 : 0 < M.cddM M.Kp g (zA L m k) bb bb' s ι R'.A r := by rw [hMe]; linarith
  have hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
      s ^ 2 * M.cddM M.Kp g (zA L m k) bb bb' s ι R'.A r := by
    rw [hMe]
    have e : s ^ 2 * (1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2) =
        1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) := by
      field_simp
    have h1 := mul_nonneg (sq_nonneg s) hb0
    have h2 := mul_nonneg (sq_nonneg s) hgb.le
    generalize 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) = X at e ⊢
    generalize 4 * (M.Kp * (g + zA L m k)) * bb' +
      6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') = B0 at h1 ⊢
    rw [mul_add, mul_add, e]
    linarith only [h1, h2]
  obtain ⟨hhb, hhd⟩ := cd3_hist_k R' P' k (cd3Delta R' P P' V k t) t
  have hdev := cd3_dev R' P P' V hga k t hab
  have hb : ‖betaTot2 (L := L) (N := N) k (histVF2 R' P' k (cd3Delta R' P P' V k t) t k)‖ +
      shareDev2 P'.a k (histVF2 R' P' k (cd3Delta R' P P' V k t) t k) ≤
      M.cddM M.Kp g (zA L m k) bb bb' s ι R'.A r := by
    rw [hhb, hhd, hMe]
    have h1 : ‖betaTot2 (L := L) (N := N) k (cd3Delta R' P P' V k t).V‖ ≤
        4 * (M.Kp * (g + zA L m k)) * bb' := hβδ
    refine le_trans (add_le_add h1 (hdev.trans (add_le_add hDP hDP'))) ?_
    rw [show 4 * (M.Kp * (g + zA L m k)) * bb' +
        (6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * bb +
          6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * bb') =
        4 * (M.Kp * (g + zA L m k)) * bb' +
          6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') by ring]
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_right hXs) hgb.le
  exact ⟨kk, ww, hkk, hww, hM0, hb, hW, hK, hM⟩


/-- **Transfer of the restart data** between two data with the same `σ_a` parts of `V, 𝒲, K`. -/
theorem cdd_transfer {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : ObsPts 2 L N) (k : ℕ) (t : Hist.Seq (Xs R)) {δ δ' : ObsSt .two L N}
    (hV : ∀ B, (δ.V B : SA .two (Lam 2 L N)).a = (δ'.V B : SA .two (Lam 2 L N)).a)
    (hW : ∀ B, (δ.W B : SA .two (Lam 2 L N)).a = (δ'.W B : SA .two (Lam 2 L N)).a)
    (hK : ∀ X, (δ.K X : SA .two (Lam 2 L N)).a = (δ'.K X : SA .two (Lam 2 L N)).a) :
    ‖betaTot2 (L := L) (N := N) k (histVF2 R P k δ t k)‖ + shareDev2 P.a k (histVF2 R P k δ t k) =
      ‖betaTot2 (L := L) (N := N) k (histVF2 R P k δ' t k)‖ +
        shareDev2 P.a k (histVF2 R P k δ' t k) ∧
    (∀ w, WbHF R P k δ' t k w → WbHF R P k δ t k w) ∧
    (∀ κ, KbHF R P k δ' t k κ → KbHF R P k δ t k κ) := by
  obtain ⟨b1, d1⟩ := cd3_hist_k R P k δ t
  obtain ⟨b2, d2⟩ := cd3_hist_k R P k δ' t
  have hb : betaTot2 (L := L) (N := N) k δ.V = betaTot2 (L := L) (N := N) k δ'.V := by
    unfold betaTot2; exact sum_congr rfl fun B _ => by rw [hV B]
  have hd : shareDev2 P.a k δ.V = shareDev2 P.a k δ'.V := by
    unfold shareDev2; rw [hb]; exact sum_congr rfl fun B _ => by rw [hV B]
  refine ⟨by rw [b1, d1, b2, d2, hb, hd], fun w h B hB => ?_, fun κ h X hX => ?_⟩
  · have := h B hB
    rw [obsHistFrom_self, rr_oTo_wA] at this ⊢
    rw [hW B]; exact this
  · have := h X hX
    rw [obsHistFrom_self, rr_oTo_wA] at this ⊢
    rw [hK X]; exact this

set_option maxHeartbeats 4000000 in
/-- **The restart data of the pair-difference datum `pl2Delta` along `D_ε`** (`h = 0` trajectory
`(b, b − m)`, `0 < ms < N_h`, `r ≤ ms`, `y − x` and `0` in one `ms`-block, `|y − x|_∞ ≤ L^{ms−r}`):
the inputs `0 < M₀`, `|β_{ms}| + D_{ms} ≤ M₀`, `WbHF … ms w`, `KbHF … ms k`,
`1344(8c_Nk + Γ_ww) ≤ s_{ms}²M₀` of `MasterCore.restartDT_lin`/`cw2_restartDT_lin`/`cw2_T5R`, with
`M₀ = M.cddM M.Kp ǧ_{ms} a_{ms} |β^{(y−x,y)}_{ms}| |β^{(0,y)}_{ms}| s_{ms} (2e^{3/2}) A r`. -/
theorem MasterFacts.cdd_restart_data (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh) (hrk : r ≤ ms)
    (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N)) (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 ^ 3) ≤ 1) :
    ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
      0 < M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 (zA L m ms)
        ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
        (R.withMsq m).A r ∧
      ‖betaTot2 (L := L) (N := N) ms (histVF2 (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms)‖ +
        shareDev2 (ptsX y).a ms (histVF2 (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms) ≤
        M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
          (R.withMsq m).A r ∧
      WbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms ww ∧
      KbHF (R.withMsq m) (ptsX y) ms (pl2Delta R m b μ₀ x y ms)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms kk ∧
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
        histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 (zA L m ms)
            ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖
            (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
            (R.withMsq m).A r := by
  obtain ⟨kk, ww, hkk, hww, hM0, hb, hW, hK, hM⟩ := M.cdd_restart_cd3 N R hP hi0 hRℓ hRA hRρ hN
    Nh hNh m hm b μ₀ hD (pl2Pts x y) (ptsX y) hk0 hkN hrk hblk rfl
    (by show supNorm (y - x - 0) ≤ _; rw [sub_zero]; exact hdist) hs0 hs hreg
  obtain ⟨ev, ew, ek⟩ := cdd_delta_a R m b μ₀ x y ms hk0
  obtain ⟨e1, e2, e3⟩ := cdd_transfer (R.withMsq m) (ptsX y) ms
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ev ew ek
  exact ⟨kk, ww, hkk, hww, hM0, by rw [e1]; exact hb, e2 ww hW, e3 kk hK, hM⟩


/-- The relative size of the envelope: `M₀ ≤ cddRel·|β^{P'}_k|`. -/
def MasterFacts.cddRel (M : MasterFacts L) (Kl g z ι A : ℝ) (r : ℕ) : ℝ :=
  4 * (Kl * (g + z)) + 24 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) +
    1344 * (8 * (PtCorr2.csN 2 : ℝ) * (64 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 +
      24 * (ι * A / (L : ℝ) ^ r)) + 8 * (M.core.rdtΓ * (M.core.cWo * (M.core.c * g)))) + g

/-- **The envelope relative to the reference coupling** (pure): if `|β| ≤ 3|β'|`, then
`cddM ≤ cddRel·|β'|`. -/
theorem MasterFacts.cddM_le_rel (M : MasterFacts L) {Kl g z bb bb' s ι A : ℝ} (r : ℕ)
    (hc : 0 ≤ M.core.c) (hΓ : 0 ≤ M.core.rdtΓ) (hg : 0 ≤ g) (hι : 0 ≤ ι) (hA : 0 ≤ A)
    (hs : 0 < s) (h3 : bb ≤ 3 * bb') :
    M.cddM Kl g z bb bb' s ι A r ≤ M.cddRel Kl g z ι A r * bb' := by
  obtain ⟨-, -, -, -, -, hcWo, hBk, hcδ, -, -⟩ := M.core.consts_nonneg
  have hβL : 0 ≤ betaL L := by
    have := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega); linarith
  have hL0 : (0 : ℝ) < (L : ℝ) ^ r := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) r
  set G := M.core.c * g with hG
  have hG0 : 0 ≤ G := mul_nonneg hc hg
  set a1 := 16 * M.core.cWo * M.core.Bk * G ^ 2 with ha1
  set a2 := ι * A / (L : ℝ) ^ r with ha2
  set a3 := M.core.rdtΓ * (M.core.cWo * G) with ha3
  set X := M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4))) with hX
  have h1 : 0 ≤ a1 := by rw [ha1]; have : 0 ≤ M.core.cWo := by linarith
                         positivity
  have h2 : 0 ≤ a2 := by rw [ha2]; positivity
  have h3' : 0 ≤ a3 := by rw [ha3]; have : 0 ≤ M.core.cWo := by linarith
                          positivity
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hN0 : (0 : ℝ) ≤ (PtCorr2.csN 2 : ℝ) := Nat.cast_nonneg _
  have e : M.cddM Kl g z bb bb' s ι A r = 4 * (Kl * (g + z)) * bb' + 6 * X * (bb + bb') +
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * (a1 * (bb + bb') + 8 * bb * a2) + 2 * a3 * (bb + bb')) +
      g * bb' := by
    unfold MasterFacts.cddM
    rw [ha1, ha2, ha3, hX]
    field_simp
    ring
  have e2 : M.cddRel Kl g z ι A r * bb' = 4 * (Kl * (g + z)) * bb' + 6 * X * (4 * bb') +
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * (a1 * (4 * bb') + 8 * (3 * bb') * a2) +
        2 * a3 * (4 * bb')) + g * bb' := by
    unfold MasterFacts.cddRel
    rw [ha1, ha2, ha3, hX]
    ring
  rw [e, e2]
  have hs4 : bb + bb' ≤ 4 * bb' := by linarith
  gcongr



set_option maxHeartbeats 1000000 in
/-- **The relative restart size of `pl2Delta`** along `D_ε`: `M₀ ≤ cddRel·|β^{(0,y)}_{ms}|` with
`cddRel = 4K_p(ǧ + a) + 24c_δc²ǧ/(β_L/4) + 1344(8c_N(64c_WB(cǧ)² + 24·2e^{3/2}A/L^r) + 8Γ_wc_Wcǧ) + ǧ`,
i.e. `M₀/|β^{(0,y)}_{ms}| ≲ ǧ_{ms} + a_{ms} + A·L^{−r}` (`|β^{(y−x,y)}| ≤ 3|β^{(0,y)}|`). -/
theorem MasterFacts.cdd_restart_rel (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms : ℕ} (r : ℕ) (hk0 : 0 < ms) (hkN : ms < Nh)
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 + zA L m ms) ≤ 1 / 2) :
    M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 (zA L m ms)
        ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
        (R.withMsq m).A r ≤
      M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 (zA L m ms) (rpIota 0 0)
        (R.withMsq m).A r * ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖ := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := id M.core.hC2
  obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hc2 : 0 ≤ M.core.c := by
    have := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂; linarith
  have hε0 : 0 ≤ M.core.ε := by have := H.hε; linarith
  have hΓ := M.core.rdtΓ_nonneg hc2 hε0
  have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8
  have hsp := histS_pos' (R.withMsq m) hρ0' hρ8' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ms
  have hgp : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 := (hD ms (by omega)).1
  have hι : 0 ≤ rpIota 0 0 := by have := one_le_rpIota (le_refl (0 : ℝ)) (le_refl (0 : ℝ)); linarith
  have hA : 0 ≤ (R.withMsq m).A := by
    rw [show (R.withMsq m).A = M.core.A from hRA]; linarith [M.core.hA2]
  have h := cdd_art_rel R (pl2Pts x y) (ptsX y) (zV b) (zV_mua_ne hb0)
    (M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN hNh hm hD (pl2Pts x y))
    (M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN hNh hm hD (ptsX y)) hkN hs0 hs
  rw [cdd_bt2_zV0 R (pl2Pts x y) m b μ₀ hk0, cdd_bt2_zV0 R (ptsX y) m b μ₀ hk0] at h
  have h3 : ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ ≤ 3 * ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖ := by
    have t1 := norm_le_norm_add_norm_sub' (bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms)
      (bt2 R (ptsX y) (zV0 b) m b μ₀ ms)
    have t2 := mul_le_mul_of_nonneg_right hs (norm_nonneg (bt2 R (ptsX y) (zV0 b) m b μ₀ ms))
    nlinarith [norm_nonneg (bt2 R (ptsX y) (zV0 b) m b μ₀ ms)]
  exact M.cddM_le_rel r hc2 hΓ hgp.le hι hA hsp h3

end

end Spin2
