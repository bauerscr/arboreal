import Step2.FlowCont.FlowMsqCov
import Step2.FlowCont.FlowCont
import Flow2.Param

/-!
# Joint continuity of the RG flow data in the mass and the history

For fixed parameters `R` (with `0 ≤ ρ ≤ 1/8`, `ρ` below the radius of `covContM_of_small`), the
flow data `rgData (R.withMsq m²)` are jointly continuous in `(m², t)` on
`(0, L^{-2(N-1)}] × Seq` (`rgData_contM`), given `ValidAt (R.withMsq m²) j` for all such `m²`
and `j < N_h`. The proof is that of `Step2.FlowCont.FlowCont` (`rawStep_cont`, `rawHist_cont`,
`histOut_cont`) with the mass as an additional variable; `m²` enters the step through the
covariance (`rawCov_contM`) and through the terms `a m²` of the vertex.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Set Filter Topology

variable {d L N : ℕ} [NeZero L]

/-- The mass range `(0, L^{-2(N-1)}]`. -/
def mRange (L N : ℕ) : Set ℝ := Ioc 0 ((L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))

/-- Joint continuity of `Γ^int_{j+1}` in `(m², ζ)` on `mRange × {|ζ_i| ≤ ρ}`, `j < N`. -/
def CovContM (P : PtFamily) (L N : ℕ) [NeZero L] (d : ℕ) (ρ : ℝ) : Prop :=
  ∀ j, j < N → ∀ x₀ : ℝ × (Fin (j + 1) → ℂ), 0 < x₀.1 →
    x₀.1 ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → (∀ i, ‖x₀.2 i‖ ≤ ρ) →
    ∀ m : Torus d (L ^ N), ContinuousAt (fun p : ℝ × (Fin (j + 1) → ℂ) =>
      (MsqJoint.DJ P L N p : DressedFRD.Data d (L ^ N)).Gint j m) x₀

theorem covContM_small (P : PtFamily) (hd : 2 ≤ d) (hL : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∀ (N : ℕ), 1 ≤ N → ∀ ρ : ℝ, ρ < ζbar → CovContM P L N d ρ := by
  obtain ⟨ζbar, hζ, h⟩ := covContM_of_small (L := L) P hd hL
  exact ⟨ζbar, hζ, fun N hN ρ hρ => h N hN ρ hρ⟩

instance RGPar.withMsq.factℓ (R : RGPar d L N) [h : Fact (0 < R.ℓ)] (m : ℝ) :
    Fact (0 < (R.withMsq m).ℓ) := h

instance RGPar.withMsq.factA (R : RGPar d L N) [h : Fact (0 < R.A)] (m : ℝ) :
    Fact (0 < (R.withMsq m).A) := h

theorem RawInv.ofWithMsq {R : RGPar d L N} {m : ℝ} {j : ℕ} {st : RawSt d L N}
    (h : RawInv (R.withMsq m) j st) : RawInv R j st :=
  ⟨h.hZprod, h.hζ, h.hζ0, h.hWl, h.hu⟩

section Step

variable (R : RGPar d L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {T : Type*} [TopologicalSpace T]

variable {R}

/-- **One raw step is jointly continuous in the mass, the state, `(g, μ)` and `x`.** -/
theorem rawStep_contM {j : ℕ} (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hj : j < N)
    (hcov : CovContM R.P L N d R.ρ) {ms : T → ℝ} (hms : Continuous ms) (hms0 : ∀ t, 0 < ms t)
    (hms1 : ∀ t, ms t ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    {f : T → RawSt d L N} (hf : StCont f) (hI : ∀ t, RawInv R j (f t)) {g μ : T → ℝ}
    (hg : Continuous g) (hμ : Continuous μ) {x : T → Xs R j} (hx : Continuous x) :
    StCont (fun t => (rawStep (R.withMsq (ms t)) j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).st) ∧
      Continuous (fun t => (rawStep (R.withMsq (ms t)) j (f t) (g t) (μ t)
        (rawD R (f t).u (x t)) (rawK R (f t).u (x t))).nu) ∧
      Continuous (fun t => (rawStep (R.withMsq (ms t)) j (f t) (g t) (μ t)
        (rawD R (f t).u (x t)) (rawK R (f t).u (x t))).g) ∧
      CF (fun t => (rawStep (R.withMsq (ms t)) j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).D) ∧
      CA (fun t => (rawStep (R.withMsq (ms t)) j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).K) := by
  have hρ1 : R.ρ < 1 := by linarith
  have hZ0 : ∀ t, (f t).Z ≠ 0 := fun t => (hI t).Z_ne_zero hρ1
  -- scalar pieces (independent of the mass)
  have hζ : Continuous fun t => cζ R (f t) :=
    (continuous_clampDisk hρ).comp ((hf.z.add hf.y).div hf.Z hZ0)
  have hζb : ∀ t, ‖cζ R (f t)‖ ≤ R.ρ := fun t => absorb_le R hρ _ _
  have hζ' : ∀ i, Continuous fun t => cζ' R j (f t) i := fun i => by
    by_cases hi : i = j
    · subst hi; simp only [cζ', Function.update_self]; exact hζ
    · simp only [cζ', Function.update_of_ne hi]; exact hf.ζ i
  have hC : ∀ x y, Continuous fun t => cC (R.withMsq (ms t)) j (f t) x y := fun x y =>
    rawCov_contM R.P hcov R rfl hj hms hms0 hms1 hζ' (fun t i => RawInv.zeta'_le hρ (hI t) i)
      (fun t i hi => by
        simp only [cζ', Function.update_of_ne (show i ≠ j by omega)]
        exact (hI t).hζ0 i hi.le) x y
  have hZ1 : Continuous fun t => cZ1 R (f t) := hf.Z.mul (continuous_const.add hζ)
  have hZ10 : ∀ t, cZ1 R (f t) ≠ 0 := fun t =>
    mul_ne_zero (hZ0 t) (one_add_ne_zero ((hζb t).trans_lt hρ1))
  have hA : Continuous fun t => cA R (f t) := hf.Z.mul hζ
  have hYc : Continuous fun t => cYc R (f t) :=
    hf.Z.mul ((continuous_clampDisk hρ).comp (hf.y.div hf.Z hZ0))
  have hNu : Continuous fun t => cNu R j (f t) (μ t) :=
    ((Complex.continuous_ofReal.comp hμ).mul hZ1).div_const _
  have hGr : Continuous fun t => cGr R j (f t) (g t) (μ t) :=
    ((Complex.continuous_ofReal.comp hg).div (continuous_const.add
      ((continuous_clampDisk (by norm_num)).comp ((continuous_const.mul hNu).mul hf.w1)))
      fun t => one_add_nCor_ne' _ _).mul (hZ1.pow 2)
  have hmsC : Continuous fun t => ((ms t : ℝ) : ℂ) := Complex.continuous_ofReal.comp hms
  have hvΔ : Continuous fun t => cvΔ (R.withMsq (ms t)) (f t) :=
    continuous_fin4 (hA.sub hYc) hYc (hA.mul hmsC) continuous_const
  have hvV : Continuous fun t => cvV (R.withMsq (ms t)) j (f t) (g t) (μ t) :=
    continuous_fin4 ((hf.z.add hYc).sub hA) (hf.y.sub hYc) (hNu.sub (hA.mul hmsC)) hGr
  -- the parameter map
  have hu := PE.continuous_mk (ℓ := R.ℓ) (A := R.A) (fun t => cC (R.withMsq (ms t)) j (f t)) hC
    hvV hvΔ hf.u (fun t => (hI t).hWl) hf.Wl (continuous_fst.comp hx) (continuous_snd.comp hx)
  have hκ : ∀ a, Continuous fun t => cκ (R.withMsq (ms t)) j (f t) (g t) (μ t)
      (rawD R (f t).u (x t)) (rawK R (f t).u (x t)) a := fun a => PE.cont_kappa hu R.i₀ a
  have hW1 : Continuous fun t => cW1 (R.withMsq (ms t)) j (f t) :=
    hf.w1.add (continuous_finsetSum _ fun y _ => hC y 0)
  have hZ2 : Continuous fun t => cZ2 (R.withMsq (ms t)) j (f t) (g t) (μ t)
      (rawD R (f t).u (x t)) (rawK R (f t).u (x t)) :=
    hZ1.mul (continuous_const.add ((continuous_clampDisk hρ).comp (((hκ 0).add (hκ 1)).div hZ1
      hZ10)))
  have hZ20 : ∀ t, cZ2 (R.withMsq (ms t)) j (f t) (g t) (μ t) (rawD R (f t).u (x t))
      (rawK R (f t).u (x t)) ≠ 0 :=
    fun t => mul_ne_zero (hZ10 t) (one_add_ne_zero ((absorb_le R hρ _ _).trans_lt hρ1))
  have hsq : Continuous fun t => csq (1 + cζ R (f t)) :=
    continuous_iff_continuousAt.2 fun t => ContinuousAt.comp (g := csq) (continuousAt_csq
      (one_add_mem_slitPlane ((hζb t).trans_lt hρ1))) (continuous_const.add hζ).continuousAt
  refine ⟨⟨?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [rs_z]; exact hκ 0
  · simp only [rs_y]; exact hκ 1
  · simp only [rs_Z]; exact hZ1
  · simp only [rs_w1]; exact hW1
  · simp only [rs_ζ]; exact hζ' i
  · simp only [rs_Wl]
    have h := PE.cont_Wl hu
    simp only [PE.C, PE.V, PE.Wl, BSp.toFam_mk'] at h
    exact h
  · simp only [rs_u]; exact hf.u.mul hsq
  · simp only [rs_nu]; exact ((hκ 2).mul continuous_const).div hZ2 hZ20
  · simp only [rs_g]
    exact ((hκ 3).div (hZ2.pow 2) fun t => pow_ne_zero 2 (hZ20 t)).mul (continuous_const.add
      ((continuous_clampDisk (by norm_num)).comp ((continuous_const.mul (hκ 2)).mul hW1)))
  · simp only [rs_D]
    have h := PE.cont_D hu
    simp only [PE.C, PE.V, PE.Wl, PE.D, BSp.toFam_mk'] at h
    exact h
  · simp only [rs_K]
    have h := PE.cont_K hu
    simp only [PE.C, PE.V, PE.Wl, PE.D, PE.K, BSp.toFam_mk'] at h
    exact h

end Step

/-! ### Along histories -/

section Hist

variable (R : RGPar d L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

variable {S : Set ℝ} (hS : S ⊆ mRange L N)

include hS

/-- **The raw state along histories is jointly continuous in `(m², t)`.** -/
theorem rawHist_contM (J : ℕ) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hJ : J ≤ N)
    (hcov : CovContM R.P L N d R.ρ)
    (hV : ∀ m ∈ S, ∀ j < J, ValidAt (R.withMsq m) j) :
    ∀ j ≤ J, StCont (fun q : S × Flow2.Hist.Seq (Xs R) => rawHist (R.withMsq q.1) j q.2)
  | 0, _ => by
    refine ⟨continuous_const, continuous_const, continuous_const, continuous_const,
      fun i => continuous_const, fun b n z => ?_, continuous_const⟩
    have e : ∀ q : S × Flow2.Hist.Seq (Xs R), (rawHist (R.withMsq q.1) 0 q.2).Wl = 0 :=
      fun q => rfl
    simp only [e]
    exact continuous_const
  | j + 1, hj => by
    have hms : Continuous fun q : S × Flow2.Hist.Seq (Xs R) => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hI : ∀ q : S × Flow2.Hist.Seq (Xs R), RawInv R j (rawHist (R.withMsq q.1) j q.2) :=
      fun q => (rawInv_hist (R.withMsq q.1) hρ j (fun i hi => hV q.1 q.1.2 i (by omega)) q.2).ofWithMsq
    exact (rawStep_contM (R := R) (T := S × Flow2.Hist.Seq (Xs R)) hρ hρ8 (by omega) hcov hms
      (fun q => (hS q.1.2).1) (fun q => (hS q.1.2).2)
      (rawHist_contM J hρ hρ8 hJ hcov hV j (by omega)) hI
      (continuous_fst.comp ((continuous_apply j).comp continuous_snd))
      (continuous_fst.comp (continuous_snd.comp ((continuous_apply j).comp continuous_snd)))
      (continuous_snd.comp (continuous_snd.comp ((continuous_apply j).comp continuous_snd)))).1

/-- **The outputs of step `j` are jointly continuous in `(m², t)`.** -/
theorem histOut_contM (J : ℕ) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hJ : J ≤ N)
    (hcov : CovContM R.P L N d R.ρ)
    (hV : ∀ m ∈ S, ∀ j < J, ValidAt (R.withMsq m) j) {j : ℕ} (hj : j < J) :
    StCont (fun q : S × Flow2.Hist.Seq (Xs R) => (histOut (R.withMsq q.1) j q.2).st) ∧
      Continuous (fun q : S × Flow2.Hist.Seq (Xs R) => (histOut (R.withMsq q.1) j q.2).nu) ∧
      Continuous (fun q : S × Flow2.Hist.Seq (Xs R) => (histOut (R.withMsq q.1) j q.2).g) ∧
      CF (fun q : S × Flow2.Hist.Seq (Xs R) => (histOut (R.withMsq q.1) j q.2).D) ∧
      CA (fun q : S × Flow2.Hist.Seq (Xs R) => (histOut (R.withMsq q.1) j q.2).K) := by
  have hms : Continuous fun q : S × Flow2.Hist.Seq (Xs R) => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hI : ∀ q : S × Flow2.Hist.Seq (Xs R), RawInv R j (rawHist (R.withMsq q.1) j q.2) :=
    fun q => (rawInv_hist (R.withMsq q.1) hρ j (fun i hi => hV q.1 q.1.2 i (by omega)) q.2).ofWithMsq
  exact rawStep_contM (R := R) (T := S × Flow2.Hist.Seq (Xs R)) hρ hρ8 (by omega) hcov hms
    (fun q => (hS q.1.2).1) (fun q => (hS q.1.2).2)
    (rawHist_contM R hS J hρ hρ8 hJ hcov hV j hj.le) hI
    (continuous_fst.comp ((continuous_apply j).comp continuous_snd))
    (continuous_fst.comp (continuous_snd.comp ((continuous_apply j).comp continuous_snd)))
    (continuous_snd.comp (continuous_snd.comp ((continuous_apply j).comp continuous_snd)))

/-- The flow data at mass `m²`, as data on the histories of `R`. -/
abbrev rgDataM (m : ℝ) : Flow2.Hist.HData (Xs R) := rgData (R.withMsq m)

/-- **The flow data are jointly continuous in `(m², t)`.** -/
theorem rgData_contM {Nh : ℕ} (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hNh : Nh ≤ N)
    (hcov : CovContM R.P L N d R.ρ)
    (hV : ∀ m ∈ S, ∀ j < Nh, ValidAt (R.withMsq m) j) :
    Flow2.Hist.ParamCont (fun m : S => rgDataM R m) Nh := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · exact Complex.continuous_re.comp (histOut_contM R hS Nh hρ hρ8 hNh hcov hV hj).2.2.1
  · exact (Complex.continuous_re.comp (histOut_contM R hS Nh hρ hρ8 hNh hcov hV hj).2.1).sub
      (continuous_const.mul (continuous_fst.comp (continuous_snd.comp
        ((continuous_apply j).comp continuous_snd))))
  · obtain ⟨hst, -, -, hD, hK⟩ := histOut_contM R hS Nh hρ hρ8 hNh hcov hV hj
    have hρ1 : R.ρ < 1 := by linarith
    have hu0 : ∀ q : S × Flow2.Hist.Seq (Xs R), (histOut (R.withMsq q.1) j q.2).st.u ≠ 0 :=
      fun q => by
        have HI := rawInv_hist (R.withMsq q.1) hρ (j + 1) (fun i hi => hV q.1 q.1.2 i (by omega))
          q.2
        have hZ := HI.ofWithMsq.Z_ne_zero hρ1
        have hu := HI.hu
        rintro h0
        rw [rawHist_succ, h0, zero_pow two_ne_zero] at hu
        rw [rawHist_succ] at hZ
        exact hZ hu.symm
    have hs : Continuous fun q : S × Flow2.Hist.Seq (Xs R) =>
        (histOut (R.withMsq q.1) j q.2).st.u⁻¹ := hst.u.inv₀ hu0
    have e : ∀ q : S × Flow2.Hist.Seq (Xs R), (rgDataM R q.1).T j q.2 =
        ((⟨sigF (histOut (R.withMsq q.1) j q.2).st.u⁻¹ (histOut (R.withMsq q.1) j q.2).D,
          sigF_mem ((rawInv_hist (R.withMsq q.1) hρ j
            (fun i hi => hV q.1 q.1.2 i (by omega)) q.2).step
            (hV q.1 q.1.2 j hj) (q.2 j).1 (q.2 j).2.1 (rawD_mem R _ _) (rawK_mem R _ _)).2.1 _⟩,
          ⟨sigK (histOut (R.withMsq q.1) j q.2).st.u⁻¹ (histOut (R.withMsq q.1) j q.2).K,
          sigK_mem ((rawInv_hist (R.withMsq q.1) hρ j
            (fun i hi => hV q.1 q.1.2 i (by omega)) q.2).step
            (hV q.1 q.1.2 j hj) (q.2 j).1 (q.2 j).2.1 (rawD_mem R _ _) (rawK_mem R _ _)).2.2 _⟩) :
          Xs R (j + 1)) := fun q => by
      show Tmap (R.withMsq q.1) j q.2 = _
      unfold Tmap
      rw [dif_pos (fun i hi => hV q.1 q.1.2 i (by omega))]
      rfl
    simp only [e]
    refine Continuous.prodMk ((BSp.continuous_iff _).2 fun b n z => ?_)
      ((ASp.continuous_iff _).2 fun X n z => ?_)
    · show Continuous fun q : S × Flow2.Hist.Seq (Xs R) =>
        coeff ((sigE (histOut (R.withMsq q.1) j q.2).st.u⁻¹
        ((histOut (R.withMsq q.1) j q.2).D b) : EvR (Lam d L N)) : Alg d L N) z
      simp only [coe_sigE, coeff_sig]
      exact (hs.pow n).mul (hD b n z)
    · show Continuous fun q : S × Flow2.Hist.Seq (Xs R) =>
        coeff ((sigE (histOut (R.withMsq q.1) j q.2).st.u⁻¹
        ((histOut (R.withMsq q.1) j q.2).K X) : EvR (Lam d L N)) : Alg d L N) z
      simp only [coe_sigE, coeff_sig]
      exact (hs.pow n).mul (hK X n z)

end Hist

end

end Step2
