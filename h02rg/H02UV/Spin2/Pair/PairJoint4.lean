import Spin2.Pair.PairJoint3
import Spin2.Master.MasterAllFacts
import Spin2.Pair.PairDefAB4

/-!
# The joint route from `MasterFacts`

* **`oRed_V_ab_zero`**, **`oRed_W_ab_zero`**: the reduced pair states have `V' = 𝒲' = 0`
  (`PtCorr2.redSt`), the inputs `hV0`, `hW0` of `pairRRelR_of_jointSizes`;
* **`pairRRelR_of_jointSizes_MF`**: `PairJointSizes` for `oRed … dxStd` along an admissible
  trajectory gives `PairRRelR`, `PairRRelRX`, `PairErrRelRX` — every trajectory input of
  `pairRRelR_of_jointSizes` is taken from `MasterFacts` (`tad`: kernel `c_t = core.ce`, `c_tǧ ≤ 1`;
  `loop`: `‖𝔫‖ ≤ 1/8`, `‖𝔫‖ ≤ B'ǧ`; `relG`: `Case2Rel` with `c_δ = core.cRel`; `top`:
  `Case2TopStep`; `ginc`: `∑ǧ² ≤ 4/β`; `gmono`; `flow`: validity);
* **`pairDefSumR_of_sizes3_MF`**: `PairDefSizesR3 ⇒ PairDefSumR` for `oRed … dxStd`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The reduced pair states have no `V'`. -/
theorem oRed_V_ab_zero (m b μ₀ : ℝ) (Dx : Lam 2 L N → Finset (Lam 2 L N)) (x : Lam 2 L N) (B) :
    ((oRed R m b μ₀ Dx x).V B : Obs.SA .two (Lam 2 L N)).ab = 0 := by
  show ((0 : Obs2.OFam .two 2 L N) B : Obs.SA .two (Lam 2 L N)).ab = 0
  simp

/-- The reduced pair states have no `𝒲'`. -/
theorem oRed_W_ab_zero (m b μ₀ : ℝ) (Dx : Lam 2 L N → Finset (Lam 2 L N)) (x : Lam 2 L N) (B) :
    ((oRed R m b μ₀ Dx x).W B : Obs.SA .two (Lam 2 L N)).ab = 0 := by
  show ((0 : Obs2.OFam .two 2 L N) B : Obs.SA .two (Lam 2 L N)).ab = 0
  simp

end Traj

set_option maxHeartbeats 4000000 in
/-- **The joint route from `MasterFacts`**: along every admissible trajectory, `PairJointSizes`
for the reduced states `oRed … dxStd` gives `PairRRelR c_r` (the input of the pair theorems in place
of `pairRRelR_of_src2`/`PairSrcRelR2`), together with the region masses and errors. The constant
condition is `crErr2 c_e c_δ (4/β_L) c_t max(B',0) c_a ≤ c_r` with `c_δ = core.cRel`,
`c_t = core.ce`. -/
theorem pairRRelR_of_jointSizes_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) {ce ca cr : ℝ} (hce : 0 ≤ ce)
    (hcr : crErr2 ce M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) ca ≤ cr)
    (hJ : PairJointSizes R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca cr) :
    PairRRelR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr ∧
      PairRRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cr ∧
      PairErrRelRX R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) ce ca := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg' : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1.le, ((hadm.1 k hk).2.1).trans M.eps_le⟩
  have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
  have hG2 : ∑ k ∈ Finset.range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤
      4 / betaL L :=
    sum_gsq_le_of_inc hβL (M.ginc N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm)
      (hg' 0 (Nat.zero_le _)).1 (hg' Nh le_rfl).2
  have hmono := M.gmono N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hgm : ∀ i l, i ≤ l → l ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ l).1 := by
    intro i l hil hl
    have key : ∀ n, i + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (i + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (i + n) (by omega))
    have := key (l - i) (by omega)
    rwa [show i + (l - i) = l by omega] at this
  obtain ⟨hct, htad, hcg⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hF := M.flow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j :=
    ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL := ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hRd := pairSectRed_of R m hval hvalL b μ₀ (pairDCov_std Nh)
  have hloop := fun x : Lam 2 L N =>
    (M.loop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)).2.2
  refine pairRRelR_of_jointSizes R hNh hLp m hb lam (oRed R m b μ₀ dxStd) hce M.cRel_nonneg hct
    (le_max_right _ _) hL49 (fun k hk => (hg' k hk).1) hG2 hgm hcg hRd
    (fun x B => oRed_V_ab_zero R m b μ₀ dxStd x B) (fun x B => oRed_W_ab_zero R m b μ₀ dxStd x B)
    (fun x _ => M.relG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (zV b)
      (zV_mua_ne hb))
    (fun x _ k hk => by
      obtain ⟨q, -, -, hl⟩ := hloop x
      exact (hl k hk).1)
    (fun x _ k hk => by
      obtain ⟨q, -, -, hl⟩ := hloop x
      exact (hl k hk).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hg' k hk.le).1))
    (fun x _ _ _ => (M.top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1)
    (fun x _ i k hik hk => htad (ptsX x) (zV b) i k hik hk)
    (pairAnchR_oRed R Nh m b μ₀) hcr hJ

/-- **`PairDefSumR` for `oRed … dxStd` from `PairDefSizesR3`** (`L` from `MasterFacts`). -/
theorem pairDefSumR_of_sizes3_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} (hNh : Nh + 2 = N)
    (m b μ₀ : ℝ) (lam : ℕ → ℂ) {cd : ℝ}
    (hS : PairDefSizesR3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd) :
    PairDefSumR R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd :=
  pairDefSumR_of_sizes3 R hNh M.core.hLpl (by have := M.core.hL49; omega) m b μ₀ lam _
    (pairAnchR_oRed R Nh m b μ₀) hS

end

end Spin2
