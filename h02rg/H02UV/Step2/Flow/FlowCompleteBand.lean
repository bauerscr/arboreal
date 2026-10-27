import Step2.Flow.FlowCompleteBandHyp
import Step2.Flow.FlowComplete
import Step2.Last.FlowLastCont2b

/-!
# Expected result `thm:flow` with the sharp band at `j = N - 2` and the continuity of the last step

`thm_flow_complete_band`: the conclusions of `thm_flow_complete` (`Step2/Flow/FlowComplete.lean`) with
one set of constants, and in addition

* (sharp band at `j = N - 2`) along every admissible trajectory, `BandSharp`: with an error
  `e ≤ β/2` (and `e ≤ K_e (L^{-2(N-2)} + m² L^{2(N-1)})` for `N ≥ 3`),
  `|Re ǧ_{N-1} - ǧ_{N-2} - β ǧ_{N-2}²| ≤ e ǧ_{N-2}² + C_s ǧ_{N-2}³`
  (`F1_rg_sharpL`, `Step2/Last/FlowLastF1b.lean`); the mass term `m² L^{2(N-1)} ≤ 1` does not vanish
  at this step, it is `O(1)` (`L`-independent), and fits into the band for `L` large;
* (continuity of the last step) `LastContOn (lastB …) UfixM`: all outputs of the last map
  (`Z_N`, `κ_N` hence `ν_N` and `ǧ_N`, `u_N(Λ)`, `V_N(B)`, `𝒲_N(B)`, `K_N(Λ)`) along the admissible
  flow are continuous in `(m², b)` on `UfixM` (`lastB_contOn`, `Step2/Last/FlowLastCont2b.lean`).

At the last step `j = N - 1` there is no localisation: `ǧ_N = ǧ_{N-1}/(1 + n_{N-1})` exactly
(`lastG_eq`) and the second-order (`β ǧ²`) part of that step stays in the unlocalised
`𝒲_N = S`, so only `|ǧ_N - Re ǧ_{N-1}| ≤ C ǧ²` (`BandOut`) holds for the final coupling.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 20000000 in
/-- **Expected result `thm:flow` with the last two steps, the sharp band at `j = N - 2`, the
continuity of all outputs of the last step, and the shooting on `ǧ_N`.** The conclusions of
`thm_flow_complete`, and in addition: the sharp band `BandSharp` of the step `N - 2` along every
admissible trajectory, and `LastContOn`: `Z_N`, `κ_N` (in particular `ν_N`, `ǧ_N`), `u_N(Λ)`,
`V_N`, `𝒲_N`, `K_N(Λ)` along the admissible flow are continuous in `(m², b)` on `UfixM`.
One set of constants; for every `N ≥ 2`, `R`, `N_h = N - 2`: the conclusions of `thm_flow_final`
(`FixedConcl` for every mass, `MsqConcl`), the bounds `GlueOut` of `thm_flow_last` and the weak
band `BandOut` of the last two steps along every admissible trajectory, the joint continuity of
`(m², b) ↦ Re ǧ_N` on `UfixM`, and the shooting on `Re ǧ_N` (existence for `β_R ≥ 2/ε`, with
`|ǧ_{N-2}(b) - 1/β_R| ≤ 4 C_b/β_R²` for every solution). -/
theorem thm_flow_complete_band : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb Cs : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ Cf ∧ 0 ≤ Cb ∧ 0 ≤ Cs ∧ 2 * Cb * ε ≤ 1 / 4 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
      MsqConcl R κ cm cT Nh ε (mRange L N) ∧
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandSharp (R.withMsq m) Nh (betaL L) Ke Cs (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      LastContOn (lastB R κ cm cT Nh ε) (UfixM R κ cm cT Nh ε (mRange L N)) ∧
      ContinuousOn (fun q : ℝ × ℝ => gFinB R κ cm cT Nh ε q.1 q.2)
        (UfixM R κ cm cT Nh ε (mRange L N)) ∧
      (∀ m ∈ mRange L N, ∀ βR : ℝ, 2 / ε ≤ βR →
        ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
      (∀ m ∈ mRange L N, ∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, ∀ βR : ℝ,
        gFinB R κ cm cT Nh ε m b = 1 / βR →
        |Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b - 1 / βR| ≤ 4 * Cb * (1 / βR) ^ 2) := by
  obtain ⟨L₀, hL₀⟩ := flow_band_hyp0
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, Cs, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm,
    hcT, hKe, hCL, hCf, hCb, hCs, hCbε, hcgε, he, ha0, hs, hC, hρ8, hcov, h⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, Cs, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCf, hCb, hCs, hCbε, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  -- the bundles at every mass
  have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
      (eRange (betaL L) Ke 1) ∧ ValidAtL (R.withMsq m) Nh ∧
      (∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandSharp (R.withMsq m) Nh (betaL L) Ke Cs (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
    intro m hm
    obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, hglue⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le
    have hmass : m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
      have := msq_horizon (L := (L : ℝ)) (by linarith) hm.2 (Nh := Nh) (k := 0) (by omega)
      simpa using this
    exact ⟨⟨hV, H, HZ, HM, HD, e,
      { hc := hcg.le, he := he0
        hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 hmass heb hej
        F1s := F1s }⟩, (hglue hNh).1, (hglue hNh).2⟩
  obtain ⟨hFix, hMsq⟩ := flow_finalZ_of ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs, hC⟩ R hP hRρ
    (by omega) (by omega) le_rfl (fun m hm => (hyp m hm).1)
  have hcont := gFinB_contOn R (S := mRange L N) le_rfl (κ := κ) (cm := cm) (cT := cT) (ε := ε)
    (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
    (by rw [hP, hRρ]; exact hcov N (by omega)) (fun m hm => (hyp m hm).1.valid) hMsq
  have hlast := lastB_contOn R (S := mRange L N) le_rfl (κ := κ) (cm := cm) (cT := cT) (ε := ε)
    (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
    (by rw [hP, hRρ]; exact hcov N (by omega)) (fun m hm => (hyp m hm).1.valid)
    (fun m hm => (hyp m hm).2.1) hMsq
  obtain ⟨s1, s2⟩ := complete_shoot R hFix (fun m hm b μ₀ hb => ((hyp m hm).2.2 b μ₀ hb).2.1)
    hcont hε hCb hCbε
  exact ⟨hFix, hMsq, fun m hm => (hyp m hm).2.2, hlast, hcont, s1, s2⟩


end

end Step2
