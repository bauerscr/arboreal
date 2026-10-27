import Step2.Flow.FlowFinalZHyp
import Step2.FlowCont.FlowFixedRMsq
import Step2.Flow.FlowRange
import Flow2.FixedRParamG2

/-!
# Expected result `thm:flow`, consolidated, without the mass condition `m² L^{2(N_h+1)} ≤ ϑ`

`thm_flow_final`: for `L ≥ L₀` there is **one** set of constants `ℓ, A, ρ, κ, c_g, c_m, c_T, ε, K_e`
(independent of `N`, `m²`, `N_h`) such that for every `N`, `R` (`P = Pc`, `i₀ = 0`) and every
horizon `N_h + 2 ≤ N`:
* for every mass `0 < m² ≤ L^{-2(N-1)}` the flow of `rgData (R.withMsq m²)` satisfies
  `FixedConcl` ((i) log form with `E = eRange β K_e 1`; (ii) at fixed `β_R ≥ 1/ε`; (iii)
  continuity and differentiability in `b` on `Ufix`; the domain bounds);
* `MsqConcl … (mRange L N)`: joint continuity in `(m², b)` on the relatively open `UfixM`, and
  continuity of the shooting solution `b(m², 1/β_R)`, `β_R > 1/ε`.

The proof: `flow_finalZ_hyp0` (hypotheses with the separate `ζ`-channel), the signed cone from
`ZHyp` (`coneS_of_Z`), strict monotonicity from `MonoZHyp` (`strictMonoOn_adm_z`), and the generic
fixed-`β_R` theorems `fh_flow_final_g`, `fh_flow_final_param_g`.

The earlier version with the mass condition is `thm_flow_final_theta` (`Step2/FlowFinal.lean`).

**Modularity.** As in `Step2/FlowFinal.lean`: the bundles `FinConstZ`, `FinHypZ` are produced by
`flow_finalZ_hyp` (the horizon enters only there), and `flow_finalZ_of` derives the conclusions on
any set of masses on which they hold.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

variable (L) in
/-- The uniform part of the hypothesis bundle (separate `ζ`-channel). -/
structure FinConstZ (ρ κ cg cm cT ε CL aB : ℝ) : Prop where
  hρ0 : 0 < ρ
  hρ8 : ρ ≤ 1 / 8
  cov : ∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 ρ
  hε : 0 < ε
  hgβ : cg * ε ≤ betaL L / 4
  he : ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm
  ha0 : CL * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ CL
  hs : 4 * sZ CL (CL * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε)) (Qh κ * (CL * ε)) ≤
    ((L : ℝ) ^ 2 - 1) / 4
  mono : ∃ p q r s p₂ q₂ r₂ z₂ : ℝ,
    MonoZCoef ((L : ℝ) ^ 2) κ CL (CL * ε) CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂

/-- The hypothesis bundle for one `(N, R, N_h)` (separate `ζ`-channel). -/
structure FinHypZ {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ)
    (κ cg cm cT ε CL aB E : ℝ) : Prop where
  valid : ∀ j < Nh, ValidAt R j
  H : HHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh CL aB ε
  HZ : ZHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh (zetaH R) CL (CL * ε) CL
    (CL * ε) 4 ε
  HM : MonoZHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh (zetaH R) CL (CL * ε) CL
    4 ε (3 / 4)
  HD : HDiff (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh ε
  sharp : ∃ e : ℕ → ℝ, SharpHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh ε cg E e

/-- **The hypothesis bundles for every horizon `N_h + 2 ≤ N`** (no mass condition). -/
theorem flow_finalZ_hyp : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke CL aB : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ FinConstZ L ρ κ cg cm cT ε CL aB ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → FinHypZ R Nh κ cg cm cT ε CL aB (eRange (betaL L) Ke 1) := by
  obtain ⟨L₀, hL₀⟩ := flow_finalZ_hyp0
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCL, hcgε, he, ha0, hs, hC, hρ8, hcov, h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, hℓ, hA, hκ0, hκ1, hcg, hcm, hcT, hKe,
    ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs, hC⟩,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh => ?_⟩
  obtain ⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩ :=
    h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hmass : R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    have := msq_horizon (L := (L : ℝ)) (by linarith) hm (Nh := Nh) (k := 0) (by omega)
    simpa using this
  exact ⟨hV, H, HZ, HM, HD, e,
    { hc := hcg.le, he := he0
      hE := sum_e_le hL2 hm0.le hKe H.hβ.le he0 hmass heb hej
      F1s := F1s }⟩

/-- **The conclusions from the hypothesis bundles** (separate `ζ`-channel), for any set `S` of
masses on which the bundle holds. -/
theorem flow_finalZ_of {ρ κ cg cm cT ε CL aB E : ℝ} (hc : FinConstZ L ρ κ cg cm cT ε CL aB)
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc)
    (hRρ : R.ρ = ρ) (hN : 1 ≤ N) {Nh : ℕ} (hNh : Nh ≤ N) {S : Set ℝ} (hS : S ⊆ mRange L N)
    (hyp : ∀ m ∈ S, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB E) :
    (∀ m ∈ S, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε E) ∧
      MsqConcl R κ cm cT Nh ε S := by
  obtain ⟨hρ0, hρ8, hcov, hε, hgβ4, he, ha0, hs, ⟨p, q, r, s, p₂, q₂, r₂, z₂, hC⟩⟩ := hc
  have hβ : 0 ≤ betaL L := by
    unfold betaL
    have : 0 ≤ Real.log L :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    positivity
  have hgβ : cg * ε ≤ (1 - 1 / 2) * betaL L := by linarith only [hgβ4, hβ]
  have hgβ' : cg * ε ≤ (1 - 1 / 2) * betaL L / 2 := by linarith only [hgβ4]
  have hcone : ∀ m ∈ S, ConeS (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh ε :=
    fun m hm => coneS_of_Z (hyp m hm).H (hyp m hm).HZ ha0 hs
  have hmono : ∀ m ∈ S, StrictMonoOn (gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)
      {b | ∃ μ, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ} :=
    fun m hm => strictMonoOn_adm_z (hyp m hm).H (hyp m hm).HM hC
  refine ⟨fun m hm => ?_, ?_⟩
  · obtain ⟨-, H, -, -, HD, e, Sh⟩ := hyp m hm
    exact fh_flow_final_g H (hcone m hm) (hmono m hm) HD Sh he hgβ hgβ' hε
  · have HS : ∀ x : S,
        HHyp (rgDataM R x.1) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh CL aB ε :=
      fun x => (hyp x.1 x.2).H
    have hpc : ParamCont (fun m : S => rgDataM R m) Nh :=
      rgData_contM R hS (by rw [hRρ]; exact hρ0.le) (by rw [hRρ]; exact hρ8) hNh
        (by rw [hP, hRρ]; exact hcov N hN) (fun m hm => (hyp m hm).valid)
    exact msqConcl_of R hε (fh_flow_final_param_g HS (fun x => hcone x.1 x.2)
      (fun x => hmono x.1 x.2) he hgβ hε hpc)

/-- **Expected result `thm:flow`, consolidated, without the mass condition.** One set of
constants; for every `N`, `R`, every horizon `N_h + 2 ≤ N` and every mass `0 < m² ≤ L^{-2(N-1)}`:
the conclusions `FixedConcl` ((i) log form, (ii) at fixed `β_R`, (iii) continuity and
differentiability in `b` on `Ufix`, the domain bounds), and the `m²`-continuity conclusions
`MsqConcl` on the full mass range. -/
theorem thm_flow_final : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
      MsqConcl R κ cm cT Nh ε (mRange L N) := by
  obtain ⟨L₀, hL₀⟩ := flow_finalZ_hyp
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, hℓ, hA, hκ0, hκ1, hcg, hcm, hcT, hKe, hc,
    h⟩ := hL₀ L hL
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, hℓ, hA, hc.hρ0, hc.hε, hκ0, hκ1, hcg, hcm, hcT,
    hKe, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  exact flow_finalZ_of hc R hP hRρ hN (by omega) le_rfl
    (fun m hm => h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh)

end

end Step2
