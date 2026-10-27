import Step2.FlowCont.FlowDiffStep

/-!
# Differentiability of the RG flow data along histories (`thm:flow`(iii))

The analogue of `Step2.rawHist_cont`, `Step2.rgData_cont` for differentiability: along a
two-parameter family of histories `u` whose coordinates `u_0, …, u_j` are differentiable at `p₀`,
the raw state `rawHist R j (u p)`, the outputs of step `j` and the maps `G_j`, `m_j`, `T_j` of
`rgData R` are differentiable at `p₀`, provided the clamps of the steps `0, …, j` are strictly
inactive at the history `u p₀` (`ClampsIn`, `ClampsOut`). In the language of `Flow2.Hist`:
`rgData_hdiffG`, `rgData_hdiffm`, `rgData_hdiffT` (`Flow2.Hist.HDiffAt`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Filter Topology Flow2

variable {d L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar d L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P}

/-- The input clamps of the steps `0, …, j` along the history `t` are strictly inactive. -/
def ClampsIn (j : ℕ) (t : Hist.Seq (Xs R)) : Prop :=
  ∀ i ≤ j, ClampIn R i (rawHist R i t) (t i).2.1

/-- The output clamps of step `j` along the history `t` are strictly inactive. -/
def ClampsOut (j : ℕ) (t : Hist.Seq (Xs R)) : Prop :=
  ClampOut R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2)

/-- **The raw state along differentiable histories is differentiable.** -/
theorem rawHist_diff (J : ℕ) (hV : ∀ j < J, ValidAt R j) (hc : ∀ j < J, CovDiff R j)
    {u : P → Hist.Seq (Xs R)} (hu : ∀ i < J, DifferentiableAt ℝ (fun p => u p i) p₀)
    (hcl : ∀ i < J, ClampIn R i (rawHist R i (u p₀)) (u p₀ i).2.1) :
    ∀ j ≤ J, StDiff (fun p => rawHist R j (u p)) p₀
  | 0, _ => by
    refine ⟨differentiableAt_const _, differentiableAt_const _, differentiableAt_const _,
      differentiableAt_const _, fun i => differentiableAt_const _, fun b n z => ?_,
      differentiableAt_const _⟩
    have e : ∀ t : Hist.Seq (Xs R), (rawHist R 0 t).Wl = 0 := fun t => rfl
    simp only [e]
    exact differentiableAt_const _
  | j + 1, hj => by
    have hρ : 0 ≤ R.ρ := (hV j (by omega)).2.2.2.1
    exact (rawStep_diff (hV j (by omega)) (hc j (by omega))
      (rawHist_diff J hV hc hu hcl j (by omega))
      (fun p => rawInv_hist R hρ j (fun i hi => hV i (by omega)) (u p))
      (hu j (by omega)).fst (hu j (by omega)).snd.fst (hu j (by omega)).snd.snd
      (hcl j (by omega))).1

variable {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hc : ∀ j < Nh, CovDiff R j)
include hV hc

/-- **The outputs of step `j` along differentiable histories are differentiable.** -/
theorem histOut_diff {j : ℕ} (hj : j < Nh) {u : P → Hist.Seq (Xs R)}
    (hu : ∀ i ≤ j, DifferentiableAt ℝ (fun p => u p i) p₀) (hcl : ClampsIn R j (u p₀)) :
    StDiff (fun p => (histOut R j (u p)).st) p₀ ∧ DF (fun p => (histOut R j (u p)).D) p₀ ∧
      DA (fun p => (histOut R j (u p)).K) p₀ ∧
      (ClampsOut R j (u p₀) → DifferentiableAt ℝ (fun p => (histOut R j (u p)).nu) p₀ ∧
        DifferentiableAt ℝ (fun p => (histOut R j (u p)).g) p₀) := by
  have hρ : 0 ≤ R.ρ := (hV j hj).2.2.2.1
  have hst := rawHist_diff R j (fun i hi => hV i (by omega)) (fun i hi => hc i (by omega))
    (fun i hi => hu i hi.le) (fun i hi => hcl i hi.le) j le_rfl
  exact rawStep_diff (hV j hj) (hc j hj) hst
    (fun p => rawInv_hist R hρ j (fun i hi => hV i (by omega)) (u p))
    (hu j le_rfl).fst (hu j le_rfl).snd.fst (hu j le_rfl).snd.snd (hcl j le_rfl)

/-- **`G_j` is differentiable** where the clamps are strictly inactive. -/
theorem rgData_hdiffG {j : ℕ} (hj : j < Nh) (t : Hist.Seq (Xs R)) (hcl : ClampsIn R j t)
    (hout : ClampsOut R j t) : Hist.HDiffAt j ((rgData R).G j) t := by
  intro u p₀ hu0 hud
  subst hu0
  have h := ((histOut_diff R hV hc hj hud hcl).2.2.2 hout).2
  exact Complex.reCLM.differentiableAt.comp p₀ h

/-- **`m_j` is differentiable** where the clamps are strictly inactive. -/
theorem rgData_hdiffm {j : ℕ} (hj : j < Nh) (t : Hist.Seq (Xs R)) (hcl : ClampsIn R j t)
    (hout : ClampsOut R j t) : Hist.HDiffAt j ((rgData R).m j) t := by
  intro u p₀ hu0 hud
  subst hu0
  have h := ((histOut_diff R hV hc hj hud hcl).2.2.2 hout).1
  exact (Complex.reCLM.differentiableAt.comp p₀ h).sub
    ((hud j le_rfl).snd.fst.const_mul _)

/-- **`T_j` is differentiable** where the input clamps are strictly inactive. -/
theorem rgData_hdiffT {j : ℕ} (hj : j < Nh) (t : Hist.Seq (Xs R)) (hcl : ClampsIn R j t) :
    Hist.HDiffAt j ((rgData R).T j) t := by
  intro u p₀ hu0 hud
  subst hu0
  obtain ⟨hst, hD, hK, -⟩ := histOut_diff R hV hc hj hud hcl
  have hval : ∀ i ≤ j, ValidAt R i := fun i hi => hV i (by omega)
  have hρ1 : R.ρ < 1 := by linarith [(hV j hj).2.2.2.2.1]
  have hu0 : ∀ t : Hist.Seq (Xs R), (histOut R j t).st.u ≠ 0 := fun t => by
    have HI := rawInv_hist R (hV j hj).2.2.2.1 (j + 1) (fun i hi => hV i (by omega)) t
    have hZ := HI.Z_ne_zero hρ1
    have hu := HI.hu
    rintro h0
    rw [rawHist_succ, h0, zero_pow two_ne_zero] at hu
    rw [rawHist_succ] at hZ
    exact hZ hu.symm
  have hs : DifferentiableAt ℝ (fun p => (histOut R j (u p)).st.u⁻¹) p₀ := hst.u.inv (hu0 _)
  show DifferentiableAt ℝ (fun p => Tmap R j (u p)) p₀
  unfold Tmap
  simp only [dif_pos hval]
  refine DifferentiableAt.prodMk ((BSp.diffAt_iff _).2 fun b n z => ?_)
    ((ASp.diffAt_iff _).2 fun X n z => ?_)
  · show DifferentiableAt ℝ (fun p => coeff ((sigE (histOut R j (u p)).st.u⁻¹
      ((histOut R j (u p)).D b) : EvR (Lam d L N)) : Alg d L N) z) p₀
    simp only [coe_sigE, coeff_sig]
    exact (hs.pow n).mul (hD b n z)
  · show DifferentiableAt ℝ (fun p => coeff ((sigE (histOut R j (u p)).st.u⁻¹
      ((histOut R j (u p)).K X) : EvR (Lam d L N)) : Alg d L N) z) p₀
    simp only [coe_sigE, coeff_sig]
    exact (hs.pow n).mul (hK X n z)

end Hist

end

end Step2
