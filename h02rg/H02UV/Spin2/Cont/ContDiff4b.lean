import Spin2.Cont.ContDiff4a

/-!
# B3, T6: `cd3_restartM` — the small restarted output of the difference datum, no named bulk inputs

`cd3_restart` (`Spin2/Cont/ContDiff3`) with the two bulk inputs discharged from `MasterFacts`:
`ι = rpIota 0 0 = 2e^{3/2}` (`MasterFacts.cd4_iota`) and the regulator from the scale condition
`A⁴c_xǧ_k³ ≤ 1` (`MasterFacts.cd4_reg`, `c_x = cx κ c_T`).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- **T6 without named bulk inputs**: `cd3_restart` with `ι = rpIota 0 0 = 2e^{3/2}` (`cd4_iota`) and the
regulator from the scale condition `A⁴c_xǧ_k³ ≤ 1` (`cd4_reg`). -/
theorem cd3_restartM (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P P' : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (hmu : OCoup2.mua V ≠ 0)
    {k r : ℕ} (hk0 : 0 < k) (hkN : k < Nh) (hrk : r ≤ k)
    (hab : blk k P.a = blk k P'.a) (hPb : P.b = P'.b)
    (hdist : supNorm (P.a - P'.a) ≤ L ^ (k - r))
    (hs0 : 0 ≤ M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hs : M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤ 1 / 2)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) * 2) ≤
      1 / 1344)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 3) ≤ 1) :
    ∀ j ≤ Nh - k,
      ‖betaTot2 (L := L) (N := N) (k + j) (histVF2 (R.withMsq m) P' k
          (cd3Delta (R.withMsq m) P P' V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (k + j))‖ ≤
        4 / 3 * M.cd3M (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 (zA L m k)
            ‖bt2 R P V m b μ₀ k‖ ‖bt2 R P' V m b μ₀ k‖
            (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0) (R.withMsq m).A r *
          ∏ i ∈ range j, ‖1 - frakN2F P' (histCovO (R.withMsq m)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P' k
              (cd3Delta (R.withMsq m) P P' V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) k (k + i)‖ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  set s := histS R' k t with hsd
  set g := (t k).1 with hgd
  set bb := ‖bt2 R P V m b μ₀ k‖ with hbbd
  set bb' := ‖bt2 R P' V m b μ₀ k‖ with hbb'd
  set ι := rpIota 0 0 with hιd
  have hι : 0 ≤ ι := by have := one_le_rpIota (le_refl (0 : ℝ)) (le_refl (0 : ℝ)); linarith
  have hI := fun b' (hq : b' ∈ blockIdx (L := L) (N := N) k) =>
    M.cd4_iota N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm hkN (cd3O R' P V k t)
      (obsHist_isObs R' P (obsInit .two V P) (obsInit_isObs .two V P) k t) P.a P'.a
      (cd3Beta R' P V k t) b' hq
  have hKb := M.cd4_reg N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm hkN hreg
  have hNh0 : 0 < Nh := by omega
  -- bulk validity
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hval := hist_valid R' hV t (n := k + 1) (by omega)
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hsp : 0 < s := histS_pos' R' hρ0' hρ8' t k
  have hgp : 0 < g := (hadm.1 k (by omega)).1
  -- the one-point data
  obtain ⟨hbb0, hsh, hWP, hKP⟩ := csm_K M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga
    hmu hNh0 hkN.le
  obtain ⟨hbb0', -, hWP', hKP'⟩ := csm_K M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V
    hga hmu hNh0 hkN.le
  have hDP := M.core.relDev N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hga hmu hNh0 k
    hkN.le
  have hDP' := M.core.relDev N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V hga hmu hNh0 k
    hkN.le
  have hβδ := cd_delta_beta_le M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P P' V hmu hkN
    hs0 hs (cd3Beta R' P V k t)
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
  have hb0 : 0 ≤ 4 * (M.csmK * (g + zA L m k)) * bb' +
      6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') := by
    refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (norm_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcδ (mul_nonneg (sq_nonneg _)
        (div_nonneg hgp.le (by linarith))))) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hgb : 0 < g * bb' := mul_pos hgp hbb0'
  have hMe : M.cd3M g (zA L m k) bb bb' s ι R'.A r =
      (4 * (M.csmK * (g + zA L m k)) * bb' +
        6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb')) +
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2 + g * bb' := by
    rw [hkkd, hwwd, hk₁d, hk₂d]; rfl
  have hXs : 0 ≤ 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2 :=
    div_nonneg hX (sq_nonneg _)
  have hM0 : 0 < M.cd3M g (zA L m k) bb bb' s ι R'.A r := by rw [hMe]; linarith
  have hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
      s ^ 2 * M.cd3M g (zA L m k) bb bb' s ι R'.A r := by
    rw [hMe]
    have e : s ^ 2 * (1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) / s ^ 2) =
        1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) := by
      field_simp
    have h1 := mul_nonneg (sq_nonneg s) hb0
    have h2 := mul_nonneg (sq_nonneg s) hgb.le
    generalize 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) = X at e ⊢
    generalize 4 * (M.csmK * (g + zA L m k)) * bb' +
      6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') = B0 at h1 ⊢
    rw [mul_add, mul_add, e]
    linarith only [h1, h2]
  obtain ⟨hhb, hhd⟩ := cd3_hist_k R' P' k (cd3Delta R' P P' V k t) t
  have hdev := cd3_dev R' P P' V hga k t hab
  have hb : ‖betaTot2 (L := L) (N := N) k (histVF2 R' P' k (cd3Delta R' P P' V k t) t k)‖ +
      shareDev2 P'.a k (histVF2 R' P' k (cd3Delta R' P P' V k t) t k) ≤
      M.cd3M g (zA L m k) bb bb' s ι R'.A r := by
    rw [hhb, hhd, hMe]
    have h1 : ‖betaTot2 (L := L) (N := N) k (cd3Delta R' P P' V k t).V‖ ≤
        4 * (M.csmK * (g + zA L m k)) * bb' := hβδ
    refine le_trans (add_le_add h1 (hdev.trans (add_le_add hDP hDP'))) ?_
    rw [show 4 * (M.csmK * (g + zA L m k)) * bb' +
        (6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * bb +
          6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * bb') =
        4 * (M.csmK * (g + zA L m k)) * bb' +
          6 * (M.core.cδ * (M.core.c ^ 2 * (g / (betaL L / 4)))) * (bb + bb') by ring]
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_right hXs) hgb.le
  exact M.core.restartDT_lin N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1 P' V k
    (cd3Delta R' P P' V k t) hk0 hkN.le h0 hl0 hsy0 hf0 hp0 hM0 hkk hww hb hW hK hg hM

end

end Spin2
