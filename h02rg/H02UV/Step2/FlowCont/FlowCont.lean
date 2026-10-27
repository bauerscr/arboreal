import Step2.FlowCont.FlowCont3

/-!
# Continuity of the RG flow data (`h02uv-outline.tex`, Section `sec:reduction`)

The maps `G_j`, `m_j`, `T_j` of `rgData R` are continuous on histories, for `j < N_h`
(the `contG`, `contm`, `contT` fields of `Flow2.Hist.HHyp`), given

* `hV : ∀ j < N_h, ValidAt R j` (in particular `0 ≤ ρ ≤ 1/8`, so the clamps are continuous and
  `Z_j ≠ 0`, `1 + ζ_j ≠ 0`);
* `hc : ∀ j < N_h, CovCont R j`: `Γ^int_{j+1}(p)` is continuous in `(ζ_0, …, ζ_j)` on the closed
  polydisc of radius `ρ` (`Step2.FlowCont.FlowCont3`). It holds for `2 ≤ d`, `0 < m² ≤ L^{-2(N-1)}` and
  `ρ < ζ̄(P, d, L)` (`covCont_of_small`, `rgData_cont_small`).

The proof is by induction along the causal recursion `rawHist`: every quantity of the raw state
is continuous (`StCont`), Grassmann-valued quantities coefficient-wise (`CF`); the Grassmann part
of a step is `step_grass_cont` (`Step2.FlowCont.FlowCont2`); continuity into the normed spaces `BSp`,
`ASp` is coefficient-wise continuity (`BSp.continuous_iff`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### The pieces of one raw step -/

section Pieces

variable (R : RGPar d L N) (j : ℕ) (st : RawSt d L N) (g μ : ℝ) (D : Fam d L N) (K : Act d L N)

def cζ : ℂ := absorbZeta R st.Z (st.z + st.y)
def cA : ℂ := st.Z * cζ R st
def cYc : ℂ := st.Z * clampDisk R.ρ (st.y / st.Z)
def cζ' : ℕ → ℂ := Function.update st.ζ j (cζ R st)
def cC : Matrix (Lam d L N) (Lam d L N) ℂ := rawCov R j (cζ' R j st)
def cZ1 : ℂ := st.Z * (1 + cζ R st)
def cNu : ℂ := (μ : ℂ) * cZ1 R st / (L : ℂ) ^ (2 * j)
def cGr : ℂ := (g : ℂ) / (1 + nCor (cNu R j st μ) st.w1) * cZ1 R st ^ 2
def cvΔ : Fin 4 → ℂ := ![cA R st - cYc R st, cYc R st, cA R st * R.msq, 0]
def cvV : Fin 4 → ℂ :=
  ![st.z + cYc R st - cA R st, st.y - cYc R st, cNu R j st μ - cA R st * R.msq, cGr R j st g μ]
def cκ : Fin 4 → ℂ := cvec4 (blockSet (L := L) (N := N) (j + 1) 0) R.i₀
  (Vnext2 j (cC R j st) (VfamL j (cvV R j st g μ)) (st.Wl + D)
    (Kflat j (VfamL j (cvΔ R st)) K) 0)
def cW1 : ℂ := st.w1 + ∑ x, cC R j st x 0
def cZ2 : ℂ := cZ1 R st * (1 + absorbZeta R (cZ1 R st) (cκ R j st g μ D K 0 + cκ R j st g μ D K 1))

theorem rs_z : (rawStep R j st g μ D K).st.z = cκ R j st g μ D K 0 := rfl
theorem rs_y : (rawStep R j st g μ D K).st.y = cκ R j st g μ D K 1 := rfl
theorem rs_Z : (rawStep R j st g μ D K).st.Z = cZ1 R st := rfl
theorem rs_ζ : (rawStep R j st g μ D K).st.ζ = cζ' R j st := rfl
theorem rs_w1 : (rawStep R j st g μ D K).st.w1 = cW1 R j st := rfl
theorem rs_u : (rawStep R j st g μ D K).st.u = st.u * csq (1 + cζ R st) := rfl
theorem rs_Wl : (rawStep R j st g μ D K).st.Wl =
    WlinNext j (cC R j st) (VfamL j (cvV R j st g μ)) st.Wl := rfl
theorem rs_nu : (rawStep R j st g μ D K).nu =
    cκ R j st g μ D K 2 * (L : ℂ) ^ (2 * (j + 1)) / cZ2 R j st g μ D K := rfl
theorem rs_g : (rawStep R j st g μ D K).g = cκ R j st g μ D K 3 / cZ2 R j st g μ D K ^ 2 *
    (1 + nCor (cκ R j st g μ D K 2) (cW1 R j st)) := rfl
theorem rs_D : (rawStep R j st g μ D K).D =
    Dnext j (cC R j st) (VfamL j (cvV R j st g μ)) st.Wl D := rfl
theorem rs_K : (rawStep R j st g μ D K).K = Kconn (j + 1) (Kplus j (cC R j st)
    (VfamL j (cvV R j st g μ)) (st.Wl + D) (Kflat j (VfamL j (cvΔ R st)) K)) := rfl

end Pieces

theorem one_add_nCor_ne' (ν w1 : ℂ) : 1 + nCor ν w1 ≠ 0 :=
  one_add_ne_zero ((norm_clampDisk_le (by norm_num) _).trans_lt (by norm_num))

theorem continuous_fin4 {T : Type*} [TopologicalSpace T] {f0 f1 f2 f3 : T → ℂ}
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) :
    Continuous fun t => (![f0 t, f1 t, f2 t, f3 t] : Fin 4 → ℂ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-! ### Continuity of the raw state -/

section Hist

variable (R : RGPar d L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {T : Type*} [TopologicalSpace T]

/-- **Continuity of a family of raw states** (Grassmann parts coefficient-wise). -/
structure StCont (f : T → RawSt d L N) : Prop where
  z : Continuous fun t => (f t).z
  y : Continuous fun t => (f t).y
  Z : Continuous fun t => (f t).Z
  w1 : Continuous fun t => (f t).w1
  ζ : ∀ i, Continuous fun t => (f t).ζ i
  Wl : CF fun t => (f t).Wl
  u : Continuous fun t => (f t).u

variable {R}

/-- **One raw step is continuous** in the state, the coordinates `(g, μ)` and `x`. -/
theorem rawStep_cont {j : ℕ} (hV : ValidAt R j) (hc : CovCont R j) {f : T → RawSt d L N}
    (hf : StCont f) (hI : ∀ t, RawInv R j (f t)) {g μ : T → ℝ} (hg : Continuous g)
    (hμ : Continuous μ) {x : T → Xs R j} (hx : Continuous x) :
    StCont (fun t => (rawStep R j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).st) ∧
      Continuous (fun t => (rawStep R j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).nu) ∧
      Continuous (fun t => (rawStep R j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).g) ∧
      CF (fun t => (rawStep R j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).D) ∧
      CA (fun t => (rawStep R j (f t) (g t) (μ t) (rawD R (f t).u (x t))
        (rawK R (f t).u (x t))).K) := by
  obtain ⟨-, -, -, hρ, hρ8, -, -⟩ := hV
  have hρ1 : R.ρ < 1 := by linarith
  have hZ0 : ∀ t, (f t).Z ≠ 0 := fun t => (hI t).Z_ne_zero hρ1
  -- scalar pieces
  have hζ : Continuous fun t => cζ R (f t) :=
    (continuous_clampDisk hρ).comp ((hf.z.add hf.y).div hf.Z hZ0)
  have hζb : ∀ t, ‖cζ R (f t)‖ ≤ R.ρ := fun t => absorb_le R hρ _ _
  have hζ' : ∀ i, Continuous fun t => cζ' R j (f t) i := fun i => by
    by_cases hi : i = j
    · subst hi; simp only [cζ', Function.update_self]; exact hζ
    · simp only [cζ', Function.update_of_ne hi]; exact hf.ζ i
  have hC : ∀ x y, Continuous fun t => cC R j (f t) x y :=
    rawCov_cont hc hζ' (fun t i => RawInv.zeta'_le hρ (hI t) i)
      (fun t i hi => by
        simp only [cζ', Function.update_of_ne (show i ≠ j by omega)]
        exact (hI t).hζ0 i hi.le)
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
  have hvΔ : Continuous fun t => cvΔ R (f t) :=
    continuous_fin4 (hA.sub hYc) hYc (hA.mul continuous_const) continuous_const
  have hvV : Continuous fun t => cvV R j (f t) (g t) (μ t) :=
    continuous_fin4 ((hf.z.add hYc).sub hA) (hf.y.sub hYc) (hNu.sub (hA.mul continuous_const))
      hGr
  -- the parameter map
  have hu := PE.continuous_mk (ℓ := R.ℓ) (A := R.A) (fun t => cC R j (f t)) hC hvV hvΔ hf.u
    (fun t => (hI t).hWl) hf.Wl (continuous_fst.comp hx) (continuous_snd.comp hx)
  have hκ : ∀ a, Continuous fun t => cκ R j (f t) (g t) (μ t) (rawD R (f t).u (x t))
      (rawK R (f t).u (x t)) a := fun a => PE.cont_kappa hu R.i₀ a
  have hW1 : Continuous fun t => cW1 R j (f t) :=
    hf.w1.add (continuous_finsetSum _ fun y _ => hC y 0)
  have hZ2 : Continuous fun t => cZ2 R j (f t) (g t) (μ t) (rawD R (f t).u (x t))
      (rawK R (f t).u (x t)) :=
    hZ1.mul (continuous_const.add ((continuous_clampDisk hρ).comp (((hκ 0).add (hκ 1)).div hZ1
      hZ10)))
  have hZ20 : ∀ t, cZ2 R j (f t) (g t) (μ t) (rawD R (f t).u (x t)) (rawK R (f t).u (x t)) ≠ 0 :=
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

variable (R)

/-- **The raw state along histories is continuous.** -/
theorem rawHist_cont (J : ℕ) (hV : ∀ j < J, ValidAt R j) (hc : ∀ j < J, CovCont R j) :
    ∀ j ≤ J, StCont (rawHist R j : Flow2.Hist.Seq (Xs R) → RawSt d L N)
  | 0, _ => by
    refine ⟨continuous_const, continuous_const, continuous_const, continuous_const,
      fun i => continuous_const, fun b n z => ?_, continuous_const⟩
    have e : ∀ t : Flow2.Hist.Seq (Xs R), (rawHist R 0 t).Wl = 0 := fun t => rfl
    simp only [e]
    exact continuous_const
  | j + 1, hj => by
    have hρ : 0 ≤ R.ρ := (hV j (by omega)).2.2.2.1
    exact (rawStep_cont (hV j (by omega)) (hc j (by omega))
      (rawHist_cont J hV hc j (by omega))
      (fun t => rawInv_hist R hρ j (fun i hi => hV i (by omega)) t)
      (continuous_fst.comp (continuous_apply j))
      (continuous_fst.comp (continuous_snd.comp (continuous_apply j)))
      (continuous_snd.comp (continuous_snd.comp (continuous_apply j)))).1

/-- **The outputs of step `j` along histories are continuous.** -/
theorem histOut_cont (J : ℕ) (hV : ∀ j < J, ValidAt R j) (hc : ∀ j < J, CovCont R j) {j : ℕ}
    (hj : j < J) :
    StCont (fun t : Flow2.Hist.Seq (Xs R) => (histOut R j t).st) ∧
      Continuous (fun t : Flow2.Hist.Seq (Xs R) => (histOut R j t).nu) ∧
      Continuous (fun t : Flow2.Hist.Seq (Xs R) => (histOut R j t).g) ∧
      CF (fun t : Flow2.Hist.Seq (Xs R) => (histOut R j t).D) ∧
      CA (fun t : Flow2.Hist.Seq (Xs R) => (histOut R j t).K) := by
  have hρ : 0 ≤ R.ρ := (hV j hj).2.2.2.1
  exact rawStep_cont (hV j hj) (hc j hj) (rawHist_cont R J hV hc j hj.le)
    (fun t => rawInv_hist R hρ j (fun i hi => hV i (by omega)) t)
    (continuous_fst.comp (continuous_apply j))
    (continuous_fst.comp (continuous_snd.comp (continuous_apply j)))
    (continuous_snd.comp (continuous_snd.comp (continuous_apply j)))

/-! ### The flow data -/

variable {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hc : ∀ j < Nh, CovCont R j)
include hV hc

/-- **`G_j` is continuous** (`contG`). -/
theorem rgData_contG : ∀ j < Nh, Continuous ((rgData R).G j) := fun _ hj =>
  Complex.continuous_re.comp (histOut_cont R Nh hV hc hj).2.2.1

/-- **`m_j` is continuous** (`contm`). -/
theorem rgData_contm : ∀ j < Nh, Continuous ((rgData R).m j) := fun j hj =>
  (Complex.continuous_re.comp (histOut_cont R Nh hV hc hj).2.1).sub (continuous_const.mul
    (continuous_fst.comp (continuous_snd.comp (continuous_apply j))))

/-- **`T_j` is continuous** (`contT`). -/
theorem rgData_contT : ∀ j < Nh, Continuous ((rgData R).T j) := fun j hj => by
  obtain ⟨hst, -, -, hD, hK⟩ := histOut_cont R Nh hV hc hj
  have hval : ∀ i ≤ j, ValidAt R i := fun i hi => hV i (by omega)
  have hρ1 : R.ρ < 1 := by linarith [(hV j hj).2.2.2.2.1]
  have hu0 : ∀ t : Flow2.Hist.Seq (Xs R), (histOut R j t).st.u ≠ 0 := fun t => by
    have HI := rawInv_hist R (hV j hj).2.2.2.1 (j + 1) (fun i hi => hV i (by omega)) t
    have hZ := HI.Z_ne_zero hρ1
    have hu := HI.hu
    rintro h0
    rw [rawHist_succ, h0, zero_pow two_ne_zero] at hu
    rw [rawHist_succ] at hZ
    exact hZ hu.symm
  have hs : Continuous fun t : Flow2.Hist.Seq (Xs R) => (histOut R j t).st.u⁻¹ :=
    hst.u.inv₀ hu0
  show Continuous fun t => Tmap R j t
  unfold Tmap
  simp only [dif_pos hval]
  refine Continuous.prodMk ((BSp.continuous_iff _).2 fun b n z => ?_)
    ((ASp.continuous_iff _).2 fun X n z => ?_)
  · show Continuous fun t => coeff ((sigE (histOut R j t).st.u⁻¹
      ((histOut R j t).D b) : EvR (Lam d L N)) : Alg d L N) z
    simp only [coe_sigE, coeff_sig]
    exact (hs.pow n).mul (hD b n z)
  · show Continuous fun t => coeff ((sigE (histOut R j t).st.u⁻¹
      ((histOut R j t).K X) : EvR (Lam d L N)) : Alg d L N) z
    simp only [coe_sigE, coeff_sig]
    exact (hs.pow n).mul (hK X n z)

/-- **The flow data `rgData R` is continuous** (the fields `contG`, `contm`, `contT` of
`Flow2.Hist.HHyp`). -/
theorem rgData_cont :
    (∀ j < Nh, Continuous ((rgData R).G j)) ∧ (∀ j < Nh, Continuous ((rgData R).m j)) ∧
      (∀ j < Nh, Continuous ((rgData R).T j)) :=
  ⟨rgData_contG R hV hc, rgData_contm R hV hc, rgData_contT R hV hc⟩

end Hist

end

end Step2
