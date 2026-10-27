import Spin2.Pair.PairRed3
import Spin2.Case2.Case2RelPairL
import Spin2.Gam.GamLastBd
import PtCorr2.Pair.PairSectHist
import PtCorr2.Pair.PairDGeom

/-!
# PR1 discharged: the reduced pair states, and `PairAboveW1` under the master constants

**The reduced states (`oRed`).** For the pair observable `z̃_0z̃_x` at `j = j_x`, given a connected
`j`-polymer `D_x` covering the coalescence region (`PairDCov`: every `j`-block whose small-set
neighbourhood contains `0` or `x` lies in `D_x`), `oRed x = PtCorr2.redHist` is the reduced state of
`PtCorr2.Pair.PairSectHist`: `V' = 𝒲' = 0`, `u' = 0`, `K'(Y) = π_{ab}(zLoc Y)` on the connected
polymers `Y ⊇ D_x`.

* **`pairSectRed_of`**: `PairSectRed` holds for `oRed` (along every trajectory with `ValidAt`,
  `ValidAtL`).
* **`pairRedSeed_of`**: `PairRedSeed` holds for `oRed` (`V'_j = 0`: no `ab` constant, `r'_j = 0`).

**The flow-level statement (`thm_pairAbove_red`).** With the constants of `thm_case2_pairL` (one
`thm_flow_masterL` call), along every admissible trajectory, `GamTopBd K₄` (the body of
`thm_gamTopBd_case2`, `gamTopBd_of_pairL`) and `ValidLast` (`LastValidConcl`) are available, so
`pairAboveW1_of_red_parts` gives `PairAboveW1 (c_σe^{c_ε}c_s + c_d + K₂ + K₃K₄) (K₃M_b)` from the
named inputs `PairDCov`, `PairSrcRelR`, `PairVertSum`, `PairDefSumR`, `PairZeroRelR` for `oRed` and
the hypotheses of `thm_gamTopBd_case2`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The reduced pair states** at `j_x`, built from the covering polymers `D_x`. -/
def oRed (m b μ₀ : ℝ) (Dx : Lam 2 L N → Finset (Lam 2 L N)) (x : Lam 2 L N) :
    Obs2.ObsSt .two L N :=
  PtCorr2.redHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (Obs.coal L (0 : Lam 2 L N) x) (Dx x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- **The covering polymers** (geometric input): `D_x` is a connected `j_x`-polymer containing
every `j_x`-block whose small-set neighbourhood contains `0` or `x`. -/
def PairDCov (Nh : ℕ) (Dx : Lam 2 L N → Finset (Lam 2 L N)) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    PtCorr2.DCov (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (Dx x)

/-- **The standard covering polymers**: the `j_x`-blocks meeting the sup-ball of radius
`8L^{j_x} + |x|_∞` around `0` (`PtCorr2.ballPoly`). -/
def dxStd (x : Lam 2 L N) : Finset (Lam 2 L N) :=
  PtCorr2.ballPoly (Obs.coal L (0 : Lam 2 L N) x) (0 : Lam 2 L N)
    (2 ^ (2 + 1) * L ^ Obs.coal L (0 : Lam 2 L N) x + supNorm (x - 0))

/-- `PairDCov` holds for the standard covering polymers. -/
theorem pairDCov_std (Nh : ℕ) : PairDCov Nh (dxStd (L := L) (N := N)) := fun x _ _ _ =>
  ⟨PtCorr2.isConn_ballPoly _ _ _, fun c hc => PtCorr2.ballPoly_cover _ (0 : Lam 2 L N) x c hc⟩

/-- **PR1: `PairSectRed` for the reduced states.** -/
theorem pairSectRed_of {Nh : ℕ} (m : ℝ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (b μ₀ : ℝ) {Dx : Lam 2 L N → Finset (Lam 2 L N)}
    (hD : PairDCov Nh Dx) : PairSectRed R Nh m b μ₀ (oRed R m b μ₀ Dx) := by
  intro x hx h1 hj
  exact PtCorr2.pairSect_hist hV hVL (Obs2.obsInit_isObs .two (zV b) (ptsX x))
    (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) _ hj (hD x hx h1 hj)

/-- **The seed of the reduced history**: `V'_{j_x} = 0`, so `∑_B ε(V'(B)_{ab}) = 0`, `r'_{j_x} = 0`. -/
theorem pairRedSeed_of (Nh : ℕ) (m b μ₀ : ℝ) (Dx : Lam 2 L N → Finset (Lam 2 L N)) :
    PairRedSeed R Nh m b μ₀ (oRed R m b μ₀ Dx) := by
  intro x _ _ _
  have h0 : ∀ B, ((PtCorr2.hVR (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
      (oRed R m b μ₀ Dx x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x) B : Obs.OE .two (Lam 2 L N)) : Obs.SA .two (Lam 2 L N)).ab =
        0 := by
    intro B
    unfold PtCorr2.hVR
    rw [PtCorr2.obsHistFrom_self]
    show ((Obs2.embF _ B + (0 : Obs.OE .two (Lam 2 L N)) : Obs.OE .two (Lam 2 L N)) :
      Obs.SA .two (Lam 2 L N)).ab = 0
    rw [add_zero]; rfl
  refine ⟨?_, ?_⟩
  · exact Finset.sum_eq_zero fun B _ => by rw [h0 B]; simp
  · unfold hRR PtCorr2.rR Obs2.rAB2
    exact Finset.sum_eq_zero fun B _ => by
      rw [h0 B]; exact (Obs2.mass2L (d := 2) (L := L) (N := N)).map_zero

end Traj

set_option maxHeartbeats 4000000 in
/-- **`PairAboveW1` from the reduced pair history under one set of master constants** (those of
`thm_case2_pairL`, as in `thm_gamTopBd_case2`). Along every admissible trajectory, the hypotheses of
`thm_gamTopBd_case2` (giving `GamTopBd K₄`), the covering polymers `PairDCov` (PR1 is then
discharged: `pairSectRed_of`, `pairRedSeed_of`) and the PR5/PR6 inputs `PairSrcRelR c_σ c_ε`,
`PairVertSum c_s`, `PairDefSumR c_d`, `PairZeroRelR K₂ K₃` for the reduced states `oRed` give
`PairAboveW1 (c_σe^{c_ε}c_s + c_d + K₂ + K₃K₄) (K₃M_b)`; `ValidLast` comes from `LastValidConcl`. -/
theorem thm_pairAbove_red : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG ce cw Kp : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧ 0 ≤ KZ ∧
      SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      0 ≤ ce ∧ 0 ≤ cw ∧ 0 ≤ Kp ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl cr : ℝ), 0 ≤ Kl → 0 ≤ cr →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
        Case2TopStep R (ptsX x) (zV b) Nh m b μ₀ ∧ Case2TopStep R (ptsS x) (zV b) Nh m b μ₀) →
      GamLastRem R Nh m b μ₀ cr → GamLastRemS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ (cσ cε cs cd K2 K3 Mb : ℝ), 0 ≤ cσ → 0 ≤ K3 →
      (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
      PairSrcRelR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cσ cε →
      PairVertSum R Nh m b μ₀ lam cs →
      PairDefSumR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      PairZeroRelR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) K2 K3 →
      PairAboveW1 R Nh m b μ₀ lam
        (cσ * Real.exp cε * cs + cd + K2 + K3 * (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 +
            2 * (1 + cr) * (2 * (1 + 3 * Kp)) * (ℓ ^ 2 * Real.exp KZ / 14)))) (K3 * Mb) := by
  obtain ⟨L₀, hL₀⟩ := thm_case2_pairL
  refine ⟨max L₀ 49, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, B₁, B₂, B₃, cq, B', cδ, cw, ce, hF, hε1,
    hSp, hMC, hLoop, hcδ, hRelG, hcw, hWK, hce, hGB, hKZ, hGM, hLV⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL49 : 49 ≤ L := le_trans (le_max_right _ _) hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  set Kp := max (lamRelK (betaL L) cg (B₁ + B₂ + B₃) B' cq cδ (eRange (betaL L) Ke 1) 4) 0
    with hKpd
  have hKp : 0 ≤ Kp := le_max_right _ _
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, ce, cw, Kp, hF, hε1, hKZ, hSp, hMC, hce,
    hcw, hKp, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam Kl cr hKl hcr hl htop hr hrS
    hsmall cσ cε cs cd K2 K3 Mb hcσ hK3 hMb hSrc hS hDf hZ
  have hB := hGB N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk.le).1.le, ((hadm.1 k hk.le).2.1).trans hε1⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  -- (H_λ) for the pair vertices
  have hLC := lamConcl_of hL2 hε1 hSp
  have hpairP : ∀ P : Obs2.ObsPts 2 L N,
      HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp := by
    intro P
    obtain ⟨hB0, -, hloop⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    have h := hLam_case2 hLC hP hi0 hRℓ hRA hRρ (by omega) hm hadm hB0 hcδ (zV_mua_ne hb)
      (hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)) hloop
    exact hLam_mono hb hm.1.le (fun k hk => (hadm.1 k hk.le).1) h (le_max_left _ _)
  have hrel : ∀ P : Obs2.ObsPts 2 L N, Case2Rel R P (zV b) Nh m b μ₀ cδ := fun P =>
    hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)
  have hn : ∀ P : Obs2.ObsPts 2 L N, ∀ k < Nh, ‖nn2 R P (zV b) m b μ₀ k‖ ≤ 1 / 8 := by
    intro P k hk
    obtain ⟨-, -, q, -, -, hl'⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    exact (hl' k hk).1
  have hmono := hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, hWT, hWM⟩ := wk_inputs hWK N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβ := betaLast_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).1)
  have hβS := betaLastS_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).2)
  have hRS := gamRemTopS_of R hb hKp hce hcw hval hg ha (fun x _ => hpairP _) hB hWM
  have hcγ : 0 ≤ (ce + cw) * (1 + 3 * Kp) := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hKβ : 0 ≤ 2 * (1 + 3 * Kp) := by linarith
  have hGT := gamTopBd_both_flow hF hε1 hKZ hL8 hSp hMC hGM hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    b μ₀ hadm lam Kl Kp ce cw _ _ cr hKl hKp hce hcw hcγ hKβ hcr hl (fun x _ => hpairP _)
    (fun x _ => hpairP _) (gamBulkRel_of_A R hB) hWT hRS hβ hr hβS hrS hsmall
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hρ8, hspl, hrest⟩ := hF
  have hvalL := ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hg' : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1.le, ((hadm.1 k hk).2.1).trans hε1⟩
  exact pairAboveW1_of_red_parts R hP hNh m (by rw [hRρ]; linarith) (by rw [hP, hRρ]; exact hspl)
    hm.1 hm.2 hval hvalL (hLV N R hP hRℓ hRρ hN2 Nh hNh m hm) hL8 hb hh lam (oRed R m b μ₀ dxStd) hcσ
    hK3 hg' hMb (pairSectRed_of R m hval hvalL b μ₀ (pairDCov_std Nh)) (pairRedSeed_of R Nh m b μ₀ dxStd) hSrc hS
    hDf hZ hGT.1

end

end Spin2
