import Step2.Last.FlowLastBand2
import Step2.FlowCont.FlowFixedRMsq

/-!
# Continuity of the last two steps in the mass and the history

* `histOut_contM_top`: the outputs of the step `j = J` (state, `ν'`, `ǧ'`, `D'`, `K'`) are jointly
  continuous in `(m², t)` with `ValidAt` only below `J` (`J < N`; e.g. `J = N - 2`). This is
  `histOut_contM` at the top index: `rawStep_contM` needs no validity at the step itself.
* `lastG_contM`, `gFin_contM`: the final quartic coupling `ǧ_N = κ_N.g/Z_N²`
  (`= ǧ_{N-1}/(1 + n_{N-1})`, `lastG_eq`) and its real part are jointly continuous in `(m², t)`;
  `lastZ_contM`: so is `Z_N`.
* `gFin_contOn_UfixM`: along the admissible flow, `(m², b) ↦ ǧ_N` is continuous on the relatively
  open set `UfixM` (from the continuity of the trajectory, `MsqConcl.cont_traj`, and causality,
  `truncH`).
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

/-- **The outputs of the step `J` are jointly continuous in `(m², t)`**, with `ValidAt` only for
`j < J` (`J < N`). -/
theorem histOut_contM_top (J : ℕ) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hJ : J < N)
    (hcov : CovContM R.P L N 2 R.ρ)
    (hV : ∀ m ∈ S, ∀ j < J, ValidAt (R.withMsq m) j) :
    StCont (fun q : S × Hist.Seq (Xs R) => (histOut (R.withMsq q.1) J q.2).st) ∧
      Continuous (fun q : S × Hist.Seq (Xs R) => (histOut (R.withMsq q.1) J q.2).nu) ∧
      Continuous (fun q : S × Hist.Seq (Xs R) => (histOut (R.withMsq q.1) J q.2).g) ∧
      CF (fun q : S × Hist.Seq (Xs R) => (histOut (R.withMsq q.1) J q.2).D) ∧
      CA (fun q : S × Hist.Seq (Xs R) => (histOut (R.withMsq q.1) J q.2).K) := by
  have hms : Continuous fun q : S × Hist.Seq (Xs R) => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hI : ∀ q : S × Hist.Seq (Xs R), RawInv R J (rawHist (R.withMsq q.1) J q.2) :=
    fun q => (rawInv_hist (R.withMsq q.1) hρ J (fun i hi => hV q.1 q.1.2 i hi) q.2).ofWithMsq
  exact rawStep_contM (R := R) (T := S × Hist.Seq (Xs R)) hρ hρ8 hJ hcov hms
    (fun q => (hS q.1.2).1) (fun q => (hS q.1.2).2)
    (rawHist_contM R hS J hρ hρ8 hJ.le hcov hV J le_rfl) hI
    (continuous_fst.comp ((continuous_apply J).comp continuous_snd))
    (continuous_fst.comp (continuous_snd.comp ((continuous_apply J).comp continuous_snd)))
    (continuous_snd.comp (continuous_snd.comp ((continuous_apply J).comp continuous_snd)))

/-- `Z_{N_h+1} ≠ 0` and `Z_N ≠ 0` along histories. -/
theorem stZ'_histOut_ne (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) {Nh : ℕ} (m : ℝ)
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (t : Hist.Seq (Xs R)) :
    (histOut (R.withMsq m) Nh t).st.Z ≠ 0 ∧
      stZ' (R.withMsq m) (histOut (R.withMsq m) Nh t).st ≠ 0 := by
  have hρ1 : R.ρ < 1 := by linarith
  have HI := rawInv_hist (R.withMsq m) hρ Nh hV t
  have hZ : (rawHist (R.withMsq m) Nh t).Z ≠ 0 := HI.ofWithMsq.Z_ne_zero hρ1
  have h1 : (histOut (R.withMsq m) Nh t).st.Z ≠ 0 :=
    mul_ne_zero hZ (one_add_ne_zero ((absorb_le (R.withMsq m) hρ _ _).trans_lt hρ1))
  exact ⟨h1, mul_ne_zero h1 (one_add_ne_zero ((absorb_le (R.withMsq m) hρ _ _).trans_lt hρ1))⟩

/-- **The final quartic coupling `ǧ_N = κ_N.g/Z_N²` is jointly continuous in `(m², t)`.** -/
theorem lastG_contM (Nh : ℕ) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hNh : Nh < N)
    (hcov : CovContM R.P L N 2 R.ρ)
    (hV : ∀ m ∈ S, ∀ j < Nh, ValidAt (R.withMsq m) j) :
    Continuous (fun q : S × Hist.Seq (Xs R) => lastG (R.withMsq q.1) Nh q.2) ∧
      Continuous (fun q : S × Hist.Seq (Xs R) => (lastOut (R.withMsq q.1) Nh q.2).Z) := by
  obtain ⟨hst, hnu, hg, -, -⟩ := histOut_contM_top R hS Nh hρ hρ8 hNh hcov hV
  have hne := fun q : S × Hist.Seq (Xs R) => stZ'_histOut_ne R hS hρ hρ8 q.1 (hV q.1 q.1.2) q.2
  have hζ : Continuous fun q : S × Hist.Seq (Xs R) =>
      stZeta R (histOut (R.withMsq q.1) Nh q.2).st :=
    (continuous_clampDisk hρ).comp ((hst.z.add hst.y).div hst.Z fun q => (hne q).1)
  have hZ' : Continuous fun q : S × Hist.Seq (Xs R) =>
      stZ' R (histOut (R.withMsq q.1) Nh q.2).st :=
    hst.Z.mul (continuous_const.add hζ)
  have hμ : Continuous fun q : S × Hist.Seq (Xs R) => (histOut (R.withMsq q.1) Nh q.2).nu.re :=
    Complex.continuous_re.comp hnu
  have hgr : Continuous fun q : S × Hist.Seq (Xs R) => (histOut (R.withMsq q.1) Nh q.2).g.re :=
    Complex.continuous_re.comp hg
  have hNu : Continuous fun q : S × Hist.Seq (Xs R) =>
      stNu R (Nh + 1) (histOut (R.withMsq q.1) Nh q.2).st
        (histOut (R.withMsq q.1) Nh q.2).nu.re :=
    ((Complex.continuous_ofReal.comp hμ).mul hZ').div_const _
  have hGr : Continuous fun q : S × Hist.Seq (Xs R) =>
      stGr R (Nh + 1) (histOut (R.withMsq q.1) Nh q.2).st (histOut (R.withMsq q.1) Nh q.2).g.re
        (histOut (R.withMsq q.1) Nh q.2).nu.re :=
    (Complex.continuous_ofReal.comp hgr).div (continuous_const.add
      ((continuous_clampDisk (by norm_num)).comp ((continuous_const.mul hNu).mul hst.w1)))
      fun q => one_add_nCor_ne' _ _
  refine ⟨hGr.congr fun q => (lastG_eq (R.withMsq q.1) Nh q.2 (hne q).2).symm, hZ'⟩

/-- **`Re ǧ_N` is jointly continuous in `(m², t)`.** -/
theorem gFin_contM (Nh : ℕ) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hNh : Nh < N)
    (hcov : CovContM R.P L N 2 R.ρ)
    (hV : ∀ m ∈ S, ∀ j < Nh, ValidAt (R.withMsq m) j) :
    Continuous (fun q : S × Hist.Seq (Xs R) => gFin (R.withMsq q.1) Nh q.2) :=
  Complex.continuous_re.comp (lastG_contM R hS Nh hρ hρ8 hNh hcov hV).1

omit hS

/-- The truncation of a history after `N_h`. -/
def truncH (Nh : ℕ) (t : Hist.Seq (Xs R)) : Hist.Seq (Xs R) := fun j => if j ≤ Nh then t j else 0

/-- `ǧ_N` depends only on `t_0, …, t_{N_h}`. -/
theorem gFin_truncH (m : ℝ) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    gFin (R.withMsq m) Nh (truncH R Nh t) = gFin (R.withMsq m) Nh t := by
  have h := histOut_causal (R.withMsq m) Nh (truncH R Nh t) t
    (fun i hi => by simp only [truncH, if_pos hi])
  unfold gFin lastG lastOut
  rw [h]

include hS

/-- **Along the admissible flow, `(m², b) ↦ Re ǧ_N` is continuous on `UfixM`.** -/
theorem gFin_contOn_UfixM {κ cm cT ε : ℝ} {Nh : ℕ} (hNh : Nh < N) (hρ : 0 ≤ R.ρ)
    (hρ8 : R.ρ ≤ 1 / 8) (hcov : CovContM R.P L N 2 R.ρ)
    (hV : ∀ m ∈ S, ∀ j < Nh, ValidAt (R.withMsq m) j) (hM : MsqConcl R κ cm cT Nh ε S) :
    ContinuousOn (fun q : ℝ × ℝ => gFin (R.withMsq q.1) Nh
      (traj (rgDataM R q.1) ((L : ℝ) ^ 2) q.2 (muc (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2)))
      (UfixM R κ cm cT Nh ε S) := by
  rw [continuousOn_iff_continuous_restrict]
  set U := UfixM R κ cm cT Nh ε S
  have hc := gFin_contM R hS Nh hρ hρ8 hNh hcov hV
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
  have e : U.restrict (fun q : ℝ × ℝ => gFin (R.withMsq q.1) Nh
      (traj (rgDataM R q.1) ((L : ℝ) ^ 2) q.2 (muc (rgDataM R q.1) ((L : ℝ) ^ 2) κ cm cT Nh ε q.2))) =
      (fun q : S × Hist.Seq (Xs R) => gFin (R.withMsq q.1) Nh q.2) ∘
        (fun x : U => ((⟨x.1.1, x.2.1⟩ : S), truncH R Nh (traj (rgDataM R x.1.1) ((L : ℝ) ^ 2)
          x.1.2 (muc (rgDataM R x.1.1) ((L : ℝ) ^ 2) κ cm cT Nh ε x.1.2)))) := by
    funext x
    simp only [Set.restrict_apply, Function.comp_apply]
    exact (gFin_truncH R _ Nh _).symm
  rw [e]
  exact hc.comp (hφ1.prodMk hφ2)

end Hist

end

end Step2
