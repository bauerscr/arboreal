import Spin2.Cont.ContDiff3
import Spin2.Restart.RestartPairSeed
import PtCorr2.Restart.Restart3a

/-!
# B3, T6: the two bulk inputs of `cd3_restart` from `MasterFacts`

Along every admissible trajectory, at a scale `k < N_h`:

* **`MasterFacts.cd4_iota`**: for every observable state `o`, points `a, a'` and couplings `β`,
  the bulk part of the block factor of the restart input satisfies
  `‖(e^{-(V♭+Δ+o.V−rrD)(B)}(1 + fullW(B)))_∅‖_{T_k} ≤ ι₀ := rpIota 0 0 = 2e^{3/2}`
  (the observable parts have no bulk; `‖V♭ + Δ‖ ≤ 3/2`, `‖W^{lin} + D‖ ≤ 1` by
  `inV_fullW_bulk_le`).
* **`MasterFacts.cd4_reg`**: the regulator `A^{|𝓑(W)|}‖K♭_k(W)‖ ≤ 1` (`W` connected) under the
  scale condition `A⁴ c_x ǧ_k³ ≤ 1` (`c_x = cx κ c_T`, from `‖K_k‖ ≤ c_xǧ_k³` in `D_ε`; holds for
  `k` large since `ǧ_k → 0`).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **`ι` from `MasterFacts`**: `T_k(I'(B)_∅) ≤ 2e^{3/2}` for every observable `o`. -/
theorem MasterFacts.cd4_iota (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    {k : ℕ} (hkN : k < Nh) (o : ObsSt .two L N) (ho : o.IsObs) (a a' : Lam 2 L N)
    (β : (Fin 2 → ℕ) → ℂ) (b' : Fin 2 → ℕ) (hq : b' ∈ blockIdx (L := L) (N := N) k) :
    Tj 2 (L : ℝ) k (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      ((IbO (fun b'' => emb (stVf (R.withMsq m) k (rawHist (R.withMsq m) k
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.1 b'' +
        stDelta (R.withMsq m) k (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) b'') +
        (o.V b'' - rrD a a' β b''))
        (fullW (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (rawD (R.withMsq m) (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.2) o) b' :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (rpIota 0 0) := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have ht := inDh_rg_of_D R' F1 hadm.1 k hkN.le
  have hRA' : R'.A = M.core.A := hRA
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by rw [hRA']; exact M.core.hSBx
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hval := hist_valid R' hV t (n := k + 1) (by omega)
  have hVc : ValidCore R' k := (hval k (by omega)).1
  obtain ⟨hb1, hb2⟩ := inV_fullW_bulk_le R' hSB' hV hm1 (by linarith : (0 : ℝ) ≤ betaL L)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0' t k hkN.le ht hVc (hm1 k hkN)
    (by rw [hcR]; exact M.core.hcε)
  have hs : 0 < histS R' k t := histS_pos' R' hρ0' hρ8' t k
  refine le_trans (r3_IbO_e_le (c := .two) k hs _ _ b'
    (stVf R' k (rawHist R' k t) (t k).1 (t k).2.1 b' + stDelta R' k (rawHist R' k t) b')
    (((rawHist R' k t).Wl + rawD R' (rawHist R' k t).u (t k).2.2) b') ?_ ?_ ?_
    (by norm_num : (0 : ℝ) ≤ 3 / 2) zero_le_one (hb1 b' hq) (hb2 b' hq))
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  · rw [map_add, bulk_emb, map_sub, ho.V b']
    have : bulk (rrD a a' β b') = 0 := by
      apply Subtype.ext; rw [coe_bulk]; exact rrD_e a a' β b'
    rw [this, sub_zero, add_zero]; rfl
  · rw [← bulkF_apply, bulkF_fullW _ _ ho]; rfl
  · rw [AddMemClass.coe_add, map_add, stVf_eq_kap, eps_VfamL k _ b', eps_stDelta, add_zero]
  · unfold rpIota; ring_nf

set_option maxHeartbeats 1000000 in
/-- **The regulator from `MasterFacts`**: `A^{|𝓑(W)|}T_k(K♭_k(W)) ≤ 1` for connected `W`, under the
scale condition `A⁴c_xǧ_k³ ≤ 1`. -/
theorem MasterFacts.cd4_reg (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    {k : ℕ} (hkN : k < Nh)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 3) ≤ 1) :
    ∀ W, IsConn k W → ENNReal.ofReal ((R.withMsq m).A ^ nb k W) *
      Tj 2 (L : ℝ) k (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((rawK (R.withMsq m) (rawHist (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).2.2 W : Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1 := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set R' := R.withMsq m with hR'
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id M.core.hC2
  obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hval := hist_valid R' hV t (n := k + 1) (by omega)
  have HI := (hval k (by omega)).2
  have hρ1 : R'.ρ < 1 := by rw [show R'.ρ = M.core.ρ from hRρ]; linarith
  have hZ := HI.Z_ne_zero hρ1
  have hK := Knorm_rawK R' HI.hu hZ (t k).2.2
  have hx : ‖(t k).2.2‖ ≤ cx M.core.κ M.core.cT * (t k).1 ^ 3 := (hadm.1 k hkN.le).2.2.2
  have hA1 : 1 ≤ R'.A := by rw [show R'.A = M.core.A from hRA]; linarith [M.core.hA2]
  exact PtCorr2.r3_reg_of_Knorm hA1 _ (hK.le.trans (ENNReal.ofReal_le_ofReal ((norm_snd_le _).trans hx)))
    (by rw [show R'.A = M.core.A from hRA]; exact hreg)

end

end Spin2
