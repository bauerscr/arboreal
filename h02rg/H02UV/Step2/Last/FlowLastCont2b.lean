import Step2.Last.FlowLastCont2a
import Step2.Last.FlowLastCont

/-!
# Continuity of all outputs of the last step along the admissible flow

* `lastOut_contM`: the final-scale object `lastOut` (`Z_N`, `κ_N`, in particular
  `ν_N = κ_N.nu`, `u_N(Λ)`, `V_N`, `𝒲_N`, `K_N(Λ)`) is jointly continuous in `(m², t)`, given
  `ValidAt` below `N_h` and `ValidAtL` at `N_h` for every mass (the membership of the inputs
  `D_{N-1}`, `K_{N-1}` in the coordinate spaces of scale `N - 1`, `RawInv.stepL`);
* `lastOut_truncH`: `lastOut` only depends on `t_0, …, t_{N_h}`;
* `contOn_UfixM_of_lastOut`, `LastContOn`, `lastB_contOn`: along the admissible flow, every
  output of the last step is continuous in `(m², b)` on the relatively open set `UfixM`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Set Filter Topology Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

variable {S : Set ℝ} (hS : S ⊆ mRange L N)

include hS

/-- **The final-scale object is jointly continuous in `(m², t)`.** -/
theorem lastOut_contM (Nh : ℕ) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hNh : Nh + 1 < N)
    (hcov : CovContM R.P L N 2 R.ρ)
    (hV : ∀ m ∈ S, ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ∀ m ∈ S, ValidAtL (R.withMsq m) Nh) :
    LastCont (fun q : S × Hist.Seq (Xs R) => lastOut (R.withMsq q.1) Nh q.2) := by
  obtain ⟨hst, hnu, hg, hD, hK⟩ := histOut_contM_top R hS Nh hρ hρ8 (by omega) hcov hV
  have hms : Continuous fun q : S × Hist.Seq (Xs R) => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hstep : ∀ q : S × Hist.Seq (Xs R),
      RawInv (R.withMsq q.1) (Nh + 1) (histOut (R.withMsq q.1) Nh q.2).st ∧
        (histOut (R.withMsq q.1) Nh q.2).D ∈ BSub (L := L) (N := N) (Nh + 1) ∧
        (histOut (R.withMsq q.1) Nh q.2).K ∈ ASub (L := L) (N := N) (Nh + 1) := fun q =>
    RawInv.stepL (hVL q.1 q.1.2) (rawInv_hist (R.withMsq q.1) hρ Nh (hV q.1 q.1.2) q.2)
      (q.2 Nh).1 (q.2 Nh).2.1 (rawD_mem _ _ _) (rawK_mem _ _ _)
  exact rawStepN_contM (R := R) (T := S × Hist.Seq (Xs R)) hρ hρ8 hNh hcov hms
    (fun q => (hS q.1.2).1) (fun q => (hS q.1.2).2) hst (fun q => (hstep q).1.ofWithMsq)
    (Complex.continuous_re.comp hg) (Complex.continuous_re.comp hnu) (fun q => (hstep q).2.1) hD
    (fun q => (hstep q).2.2) hK

omit hS

/-- `lastOut` depends only on `t_0, …, t_{N_h}`. -/
theorem lastOut_truncH (m : ℝ) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    lastOut (R.withMsq m) Nh (truncH R Nh t) = lastOut (R.withMsq m) Nh t := by
  have h := histOut_causal (R.withMsq m) Nh (truncH R Nh t) t
    (fun i hi => by simp only [truncH, if_pos hi])
  unfold lastOut
  rw [h]

/-- **The last step along the admissible flow** at mass `m²` and initial coupling `b`. -/
def lastB (κ cm cT : ℝ) (Nh : ℕ) (ε : ℝ) (q : ℝ × ℝ) : LastN.LastOut 2 L N :=
  lastOut (R.withMsq q.1) Nh
    (traj (rgDataM R q.1) ((L : ℝ) ^ 2) q.2 (muc (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2))

include hS

/-- **From continuity in `(m², t)` to continuity on `UfixM`** (via `MsqConcl.cont_traj` and
causality). -/
theorem contOn_UfixM_of_lastOut {Y : Type*} [TopologicalSpace Y] (φ : LastN.LastOut 2 L N → Y)
    {κ cm cT ε : ℝ} {Nh : ℕ} (hM : MsqConcl R κ cm cT Nh ε S)
    (hc : Continuous fun q : S × Hist.Seq (Xs R) => φ (lastOut (R.withMsq q.1) Nh q.2)) :
    ContinuousOn (fun q : ℝ × ℝ => φ (lastB R κ cm cT Nh ε q)) (UfixM R κ cm cT Nh ε S) := by
  rw [continuousOn_iff_continuous_restrict]
  set U := UfixM R κ cm cT Nh ε S
  have hφ1 : Continuous fun x : U => (⟨x.1.1, x.2.1⟩ : S) :=
    Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  have hφ2 : Continuous fun x : U => truncH R Nh (traj (rgDataM R x.1.1) ((L : ℝ) ^ 2) x.1.2
      (muc (rgDataM R x.1.1) ((L : ℝ) ^ 2) κ cm cT Nh ε x.1.2)) := by
    refine continuous_pi fun j => ?_
    by_cases hj : j ≤ Nh
    · simp only [truncH, if_pos hj]
      exact (hM.cont_traj j hj).restrict
    · simp only [truncH, if_neg hj]
      exact continuous_const
  have e : U.restrict (fun q : ℝ × ℝ => φ (lastB R κ cm cT Nh ε q)) =
      (fun q : S × Hist.Seq (Xs R) => φ (lastOut (R.withMsq q.1) Nh q.2)) ∘
        (fun x : U => ((⟨x.1.1, x.2.1⟩ : S), truncH R Nh (traj (rgDataM R x.1.1) ((L : ℝ) ^ 2)
          x.1.2 (muc (rgDataM R x.1.1) ((L : ℝ) ^ 2) κ cm cT Nh ε x.1.2)))) := by
    funext x
    simp only [Set.restrict_apply, Function.comp_apply]
    exact congrArg φ (lastOut_truncH R _ Nh _).symm
  rw [e]
  exact hc.comp (hφ1.prodMk hφ2)

omit hS

/-- **Continuity of the final-scale object on a set of parameters**: `Z_N`, `κ_N` (in particular
`ν_N`, `ǧ_N`), `u_N(Λ)` continuous, `V_N(B)`, `𝒲_N(B)`, `K_N(Λ)` coefficient-wise. -/
structure LastContOn (F : ℝ × ℝ → LastN.LastOut 2 L N) (U : Set (ℝ × ℝ)) : Prop where
  Z : ContinuousOn (fun q => (F q).Z) U
  κz : ContinuousOn (fun q => (F q).κ.z) U
  κy : ContinuousOn (fun q => (F q).κ.y) U
  κnu : ContinuousOn (fun q => (F q).κ.nu) U
  κg : ContinuousOn (fun q => (F q).κ.g) U
  u : ContinuousOn (fun q => (F q).u) U
  V : ∀ b n (z : Fin n → Sf (Lam 2 L N)),
    ContinuousOn (fun q => coeff (((F q).V b : EvR (Lam 2 L N)) : Alg 2 L N) z) U
  W : ∀ b n (z : Fin n → Sf (Lam 2 L N)),
    ContinuousOn (fun q => coeff (((F q).W b : EvR (Lam 2 L N)) : Alg 2 L N) z) U
  K : ∀ n (z : Fin n → Sf (Lam 2 L N)),
    ContinuousOn (fun q => coeff (((F q).K : EvR (Lam 2 L N)) : Alg 2 L N) z) U

include hS

/-- **Along the admissible flow, all outputs of the last step are continuous in `(m², b)` on
`UfixM`.** -/
theorem lastB_contOn {κ cm cT ε : ℝ} {Nh : ℕ} (hNh : Nh + 1 < N) (hρ : 0 ≤ R.ρ)
    (hρ8 : R.ρ ≤ 1 / 8) (hcov : CovContM R.P L N 2 R.ρ)
    (hV : ∀ m ∈ S, ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ∀ m ∈ S, ValidAtL (R.withMsq m) Nh) (hM : MsqConcl R κ cm cT Nh ε S) :
    LastContOn (lastB R κ cm cT Nh ε) (UfixM R κ cm cT Nh ε S) := by
  have H := lastOut_contM R hS Nh hρ hρ8 hNh hcov hV hVL
  exact ⟨contOn_UfixM_of_lastOut R hS (fun o => o.Z) hM H.Z,
    contOn_UfixM_of_lastOut R hS (fun o => o.κ.z) hM H.κz,
    contOn_UfixM_of_lastOut R hS (fun o => o.κ.y) hM H.κy,
    contOn_UfixM_of_lastOut R hS (fun o => o.κ.nu) hM H.κnu,
    contOn_UfixM_of_lastOut R hS (fun o => o.κ.g) hM H.κg,
    contOn_UfixM_of_lastOut R hS (fun o => o.u) hM H.u,
    fun b n z => contOn_UfixM_of_lastOut R hS
      (fun o => coeff ((o.V b : EvR (Lam 2 L N)) : Alg 2 L N) z) hM (H.V b n z),
    fun b n z => contOn_UfixM_of_lastOut R hS
      (fun o => coeff ((o.W b : EvR (Lam 2 L N)) : Alg 2 L N) z) hM (H.W b n z),
    fun n z => contOn_UfixM_of_lastOut R hS
      (fun o => coeff ((o.K : EvR (Lam 2 L N)) : Alg 2 L N) z) hM (H.K n z)⟩

end Hist

end

end Step2
