import Step2.FlowCont.FlowDiffBasic

/-!
# Differentiability of the RG flow data: one raw step (`thm:flow`(iii))

The analogue of `Step2.rawStep_cont` for real differentiability at a point `p₀` of a parameter
space `P`. The clamps of the step are only differentiable where they are inactive, so the step is
differentiable at `p₀` if the clamps are *strictly* inactive at `p₀`:
* `ClampIn`: `|(z + y)/Z| < ρ`, `|y/Z| < ρ` (the absorbed couplings) and `|4 ν_raw w^{(1)}| < 1/8`
  (the coordinate change `ǧ = g(1 + n)`) for the input of the step;
* `ClampOut`: `|(z' + y')/Z'| < ρ` and `|4 κ_ν w'^{(1)}| < 1/8` for the outputs `ν`, `ǧ`.
Then the clamps coincide with the identity near `p₀` (`diffAt_clampDisk`), and all other pieces are
holomorphic (`Step2.FlowCont.FlowCont2`) or rational.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Filter Topology

variable {d L N : ℕ} [NeZero L]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P}

theorem diffAt_ofReal {μ : P → ℝ} (hμ : DifferentiableAt ℝ μ p₀) :
    DifferentiableAt ℝ (fun p => (μ p : ℂ)) p₀ :=
  Complex.ofRealCLM.differentiableAt.comp p₀ hμ

theorem diffAt_div {c e : P → ℂ} (hc : DifferentiableAt ℝ c p₀) (he : DifferentiableAt ℝ e p₀)
    (h0 : e p₀ ≠ 0) : DifferentiableAt ℝ (fun p => c p / e p) p₀ := by
  simp_rw [div_eq_mul_inv]; exact hc.fun_mul (he.inv h0)

theorem diffAt_div_const {c : P → ℂ} (hc : DifferentiableAt ℝ c p₀) (e : ℂ) :
    DifferentiableAt ℝ (fun p => c p / e) p₀ := by
  simp_rw [div_eq_mul_inv]; exact hc.mul_const e⁻¹

theorem diffAt_fin4 {f0 f1 f2 f3 : P → ℂ} (h0 : DifferentiableAt ℝ f0 p₀)
    (h1 : DifferentiableAt ℝ f1 p₀) (h2 : DifferentiableAt ℝ f2 p₀)
    (h3 : DifferentiableAt ℝ f3 p₀) :
    DifferentiableAt ℝ (fun p => (![f0 p, f1 p, f2 p, f3 p] : Fin 4 → ℂ)) p₀ := by
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

section PEd

variable {j : ℕ} {ℓ A : ℝ} [Fact (0 < ℓ)] [Fact (0 < A)]

theorem PE.diffAt_mk (C : P → Matrix (Lam d L N) (Lam d L N) ℂ)
    (hC : ∀ x y, DifferentiableAt ℝ (fun p => C p x y) p₀) {v vΔ : P → Fin 4 → ℂ}
    (hv : DifferentiableAt ℝ v p₀) (hvΔ : DifferentiableAt ℝ vΔ p₀) {r : P → ℂ}
    (hr : DifferentiableAt ℝ r p₀) {Wl : P → Fam d L N}
    (hWl : ∀ p, Wl p ∈ BSub (L := L) (N := N) j) (hWlc : DF Wl p₀) {x1 : P → BSp d L N j ℓ}
    (hx1 : DifferentiableAt ℝ x1 p₀) {x2 : P → ASp d L N j ℓ A}
    (hx2 : DifferentiableAt ℝ x2 p₀) :
    DifferentiableAt ℝ (fun p => (((C p : Lam d L N → Lam d L N → ℂ), v p, vΔ p, r p,
      BSp.mk' (ℓ := ℓ) (Wl p) (hWl p), x1 p, x2 p) : PE d L N j ℓ A)) p₀ := by
  have hWc : DifferentiableAt ℝ (fun p => BSp.mk' (ℓ := ℓ) (Wl p) (hWl p)) p₀ :=
    (BSp.diffAt_iff _).2 (by simpa only [BSp.toFam_mk'] using hWlc)
  exact (differentiableAt_pi.2 fun x => differentiableAt_pi.2 fun y => hC x y).prodMk
    (hv.prodMk (hvΔ.prodMk (hr.prodMk (hWc.prodMk (hx1.prodMk hx2)))))

variable {u : P → PE d L N j ℓ A} (hu : DifferentiableAt ℝ u p₀)
include hu

theorem PE.diff_kappa (i₀ : Fin d) (a : Fin 4) : DifferentiableAt ℝ (fun p =>
    cvec4 (blockSet (L := L) (N := N) (j + 1) 0) i₀
      (Vnext2 j (PE.C (u p)) (PE.V (u p)) (PE.Wl (u p) + PE.D (u p)) (PE.K (u p)) 0) a) p₀ := by
  have h := diffAt_of_diffC (Hol.lin (Vnext2_holC j (PE.hC d L N j ℓ A) (PE.hV d L N j ℓ A)
    (PE.hW d L N j ℓ A) (PE.hK d L N j ℓ A) 0)
      ((LinearMap.proj a).comp (cvec4 (blockSet (L := L) (N := N) (j + 1) 0) i₀))) hu
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at h
  exact h

theorem PE.diff_Wl : DF (fun p => WlinNext j (PE.C (u p)) (PE.V (u p)) (PE.Wl (u p))) p₀ :=
  fun b n z => diffAt_of_hol (holE_WlinNext (PE.hC d L N j ℓ A) j (PE.hV d L N j ℓ A)
    (PE.hWl d L N j ℓ A) b) hu n z

theorem PE.diff_D :
    DF (fun p => Dnext j (PE.C (u p)) (PE.V (u p)) (PE.Wl (u p)) (PE.D (u p))) p₀ :=
  fun b n z => diffAt_of_hol (holE_Dnext (PE.hC d L N j ℓ A) j (PE.hV d L N j ℓ A)
    (PE.hWl d L N j ℓ A) (PE.hD d L N j ℓ A) b) hu n z

theorem PE.diff_K : DA (fun p => Kconn (j + 1) (Kplus j (PE.C (u p)) (PE.V (u p))
    (PE.Wl (u p) + PE.D (u p)) (PE.K (u p)))) p₀ :=
  fun X n z => diffAt_of_hol (holE_Kconn (j + 1) (Kplus_holC j (PE.hC d L N j ℓ A)
    (PE.hV d L N j ℓ A) (PE.hW d L N j ℓ A) (PE.hK d L N j ℓ A) (PE.hV0 d L N j ℓ A)) X) hu n z

end PEd

/-! ### Differentiability of raw states -/

section Hist

variable {R : RGPar d L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Differentiability of a family of raw states at `p₀`** (Grassmann parts coefficient-wise). -/
structure StDiff (f : P → RawSt d L N) (p₀ : P) : Prop where
  z : DifferentiableAt ℝ (fun p => (f p).z) p₀
  y : DifferentiableAt ℝ (fun p => (f p).y) p₀
  Z : DifferentiableAt ℝ (fun p => (f p).Z) p₀
  w1 : DifferentiableAt ℝ (fun p => (f p).w1) p₀
  ζ : ∀ i, DifferentiableAt ℝ (fun p => (f p).ζ i) p₀
  Wl : DF (fun p => (f p).Wl) p₀
  u : DifferentiableAt ℝ (fun p => (f p).u) p₀

variable (R) in
/-- **The input clamps of step `j` are strictly inactive.** -/
structure ClampIn (j : ℕ) (st : RawSt d L N) (μ : ℝ) : Prop where
  c1 : ‖(st.z + st.y) / st.Z‖ < R.ρ
  c2 : ‖st.y / st.Z‖ < R.ρ
  c3 : ‖4 * cNu R j st μ * st.w1‖ < 1 / 8

variable (R) in
/-- **The output clamps of step `j` are strictly inactive.** -/
structure ClampOut (j : ℕ) (st : RawSt d L N) (g μ : ℝ) (D : Fam d L N) (K : Act d L N) :
    Prop where
  c4 : ‖(cκ R j st g μ D K 0 + cκ R j st g μ D K 1) / cZ1 R st‖ < R.ρ
  c5 : ‖4 * cκ R j st g μ D K 2 * cW1 R j st‖ < 1 / 8

set_option maxHeartbeats 1000000 in
/-- **One raw step is differentiable** at `p₀` in the state, the coordinates `(g, μ)` and `x`, if
its clamps are strictly inactive at `p₀`. -/
theorem rawStep_diff {j : ℕ} (hV : ValidAt R j) (hc : CovDiff R j) {f : P → RawSt d L N}
    (hf : StDiff f p₀) (hI : ∀ p, RawInv R j (f p)) {g μ : P → ℝ}
    (hg : DifferentiableAt ℝ g p₀) (hμ : DifferentiableAt ℝ μ p₀) {x : P → Xs R j}
    (hx : DifferentiableAt ℝ x p₀) (hcl : ClampIn R j (f p₀) (μ p₀)) :
    StDiff (fun p => (rawStep R j (f p) (g p) (μ p) (rawD R (f p).u (x p))
        (rawK R (f p).u (x p))).st) p₀ ∧
      DF (fun p => (rawStep R j (f p) (g p) (μ p) (rawD R (f p).u (x p))
        (rawK R (f p).u (x p))).D) p₀ ∧
      DA (fun p => (rawStep R j (f p) (g p) (μ p) (rawD R (f p).u (x p))
        (rawK R (f p).u (x p))).K) p₀ ∧
      (ClampOut R j (f p₀) (g p₀) (μ p₀) (rawD R (f p₀).u (x p₀)) (rawK R (f p₀).u (x p₀)) →
        DifferentiableAt ℝ (fun p => (rawStep R j (f p) (g p) (μ p) (rawD R (f p).u (x p))
          (rawK R (f p).u (x p))).nu) p₀ ∧
        DifferentiableAt ℝ (fun p => (rawStep R j (f p) (g p) (μ p) (rawD R (f p).u (x p))
          (rawK R (f p).u (x p))).g) p₀) := by
  obtain ⟨-, -, -, hρ, hρ8, -, -⟩ := hV
  have hρ1 : R.ρ < 1 := by linarith
  have hZ0 : ∀ p, (f p).Z ≠ 0 := fun p => (hI p).Z_ne_zero hρ1
  -- scalar pieces
  have hζ : DifferentiableAt ℝ (fun p => cζ R (f p)) p₀ :=
    diffAt_clampDisk (diffAt_div (hf.z.add hf.y) hf.Z (hZ0 p₀)) hcl.c1
  have hζb : ∀ p, ‖cζ R (f p)‖ ≤ R.ρ := fun p => absorb_le R hρ _ _
  have hζ' : ∀ i, DifferentiableAt ℝ (fun p => cζ' R j (f p) i) p₀ := fun i => by
    by_cases hi : i = j
    · subst hi; simp only [cζ', Function.update_self]; exact hζ
    · simp only [cζ', Function.update_of_ne hi]; exact hf.ζ i
  have hC : ∀ x y, DifferentiableAt ℝ (fun p => cC R j (f p) x y) p₀ :=
    rawCov_diff hc (fun i _ => hζ' i) (fun i => RawInv.zeta'_le hρ (hI p₀) i)
      (fun p i hi => by
        simp only [cζ', Function.update_of_ne (show i ≠ j by omega)]
        exact (hI p).hζ0 i hi.le)
  have hZ1 : DifferentiableAt ℝ (fun p => cZ1 R (f p)) p₀ :=
    hf.Z.mul ((differentiableAt_const _).add hζ)
  have hZ10 : ∀ p, cZ1 R (f p) ≠ 0 := fun p =>
    mul_ne_zero (hZ0 p) (one_add_ne_zero ((hζb p).trans_lt hρ1))
  have hA : DifferentiableAt ℝ (fun p => cA R (f p)) p₀ := hf.Z.mul hζ
  have hYc : DifferentiableAt ℝ (fun p => cYc R (f p)) p₀ :=
    hf.Z.mul (diffAt_clampDisk (diffAt_div hf.y hf.Z (hZ0 p₀)) hcl.c2)
  have hNu : DifferentiableAt ℝ (fun p => cNu R j (f p) (μ p)) p₀ :=
    diffAt_div_const ((diffAt_ofReal hμ).mul hZ1) _
  have hnC : DifferentiableAt ℝ (fun p => nCor (cNu R j (f p) (μ p)) (f p).w1) p₀ :=
    diffAt_clampDisk (((differentiableAt_const _).mul hNu).mul hf.w1) hcl.c3
  have hGr : DifferentiableAt ℝ (fun p => cGr R j (f p) (g p) (μ p)) p₀ :=
    (diffAt_div (diffAt_ofReal hg) ((differentiableAt_const _).add hnC)
      (one_add_nCor_ne' _ _)).mul (hZ1.pow 2)
  have hvΔ : DifferentiableAt ℝ (fun p => cvΔ R (f p)) p₀ :=
    diffAt_fin4 (hA.sub hYc) hYc (hA.mul (differentiableAt_const _)) (differentiableAt_const _)
  have hvV : DifferentiableAt ℝ (fun p => cvV R j (f p) (g p) (μ p)) p₀ :=
    diffAt_fin4 ((hf.z.add hYc).sub hA) (hf.y.sub hYc)
      (hNu.sub (hA.mul (differentiableAt_const _))) hGr
  -- the parameter map
  have hu := PE.diffAt_mk (ℓ := R.ℓ) (A := R.A) (fun p => cC R j (f p)) hC hvV hvΔ hf.u
    (fun p => (hI p).hWl) hf.Wl hx.fst hx.snd
  have hκ : ∀ a, DifferentiableAt ℝ (fun p => cκ R j (f p) (g p) (μ p) (rawD R (f p).u (x p))
      (rawK R (f p).u (x p)) a) p₀ := fun a => PE.diff_kappa hu R.i₀ a
  have hW1 : DifferentiableAt ℝ (fun p => cW1 R j (f p)) p₀ :=
    hf.w1.add (DifferentiableAt.fun_sum fun y _ => hC y 0)
  have hsq : DifferentiableAt ℝ (fun p => csq (1 + cζ R (f p))) p₀ :=
    diffAt_csq ((differentiableAt_const _).add hζ)
      (one_add_mem_slitPlane ((hζb p₀).trans_lt hρ1))
  refine ⟨⟨?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_⟩, ?_, ?_, fun hout => ?_⟩
  · simp only [rs_z]; exact hκ 0
  · simp only [rs_y]; exact hκ 1
  · simp only [rs_Z]; exact hZ1
  · simp only [rs_w1]; exact hW1
  · simp only [rs_ζ]; exact hζ' i
  · simp only [rs_Wl]
    have h := PE.diff_Wl hu
    simp only [PE.C, PE.V, PE.Wl, BSp.toFam_mk'] at h
    exact h
  · simp only [rs_u]; exact hf.u.mul hsq
  · simp only [rs_D]
    have h := PE.diff_D hu
    simp only [PE.C, PE.V, PE.Wl, PE.D, BSp.toFam_mk'] at h
    exact h
  · simp only [rs_K]
    have h := PE.diff_K hu
    simp only [PE.C, PE.V, PE.Wl, PE.D, PE.K, BSp.toFam_mk'] at h
    exact h
  -- the outputs
  have hZ2 : DifferentiableAt ℝ (fun p => cZ2 R j (f p) (g p) (μ p) (rawD R (f p).u (x p))
      (rawK R (f p).u (x p))) p₀ :=
    hZ1.mul ((differentiableAt_const _).add
      (diffAt_clampDisk (diffAt_div ((hκ 0).add (hκ 1)) hZ1 (hZ10 p₀)) hout.c4))
  have hZ20 : ∀ p, cZ2 R j (f p) (g p) (μ p) (rawD R (f p).u (x p)) (rawK R (f p).u (x p)) ≠ 0 :=
    fun p => mul_ne_zero (hZ10 p) (one_add_ne_zero ((absorb_le R hρ _ _).trans_lt hρ1))
  refine ⟨?_, ?_⟩
  · simp only [rs_nu]
    exact diffAt_div ((hκ 2).mul (differentiableAt_const _)) hZ2 (hZ20 p₀)
  · simp only [rs_g]
    exact (diffAt_div (hκ 3) (hZ2.pow 2) (pow_ne_zero 2 (hZ20 p₀))).mul ((differentiableAt_const _).add
      (diffAt_clampDisk (((differentiableAt_const _).mul (hκ 2)).mul hW1) hout.c5))

end Hist

end

end Step2
