import Ward.MainFinite
import Ward.ObsLimitA
import Ward.ObsLimitTrunc
import Ward.ObsLimitQ1
import Ward.CorWard

/-!
# The double limits of `thm:h02` for fixed `β`

Let `(b̃, m̃²) = (bt β h, mt β h)` be the solutions of `cor:ward` (ii) (`SolAt`). For `h > 0`
(`m̃² > 0`) the finite-volume `ℍ^{0|2}` correlations at `(β, h)` are the `ψ`-model correlations
at `(m̃², b̃)` (`Ward.MainFinite`), whose `N → ∞` limits are those of `Ward.ObsLimit*`:

* `lim_z`: `⟨z_0⟩ → θh h := Re(1 - c² Γ(m̃², b̃))`;
* `lim_ξη`: `⟨ξ_0 η_x⟩ → τh h := Re(c² Q1(x)(m̃², b̃))`;
* `lim_cov`: `⟨z_0 z_x⟩ - ⟨z_0⟩⟨z_x⟩ → σh h := Re(c⁴ Q2(x)(m̃², b̃))`;
* `lim_dot`: `⟨u_0·u_x⟩ → -2 τh h - σh h - θh h ^ 2`.

The functions `θh, τh, σh` are defined by the same formulas at `h = 0` (`m̃² = 0`,
`b̃ = b*(β)`), and they are right-continuous at `h = 0` (`cont_θh`, `cont_τh`, `cont_σh`), by the
joint continuity of `Γ`, `Q1`, `Q2` and `c²` along `h ↦ (m̃², b̃)`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

variable (d L) in
/-- `θh(β, h) = Re(1 - c² Γ)` at `(m̃², b̃)(β, h)`. -/
def θh (V₀c : ℝ → ℂ → Vcoup) (lbar : ℝ) (bt mt : ℝ → ℝ → ℝ) (β h : ℝ) : ℝ :=
  (1 - (c2F V₀c (bt β h) (mt β h) : ℂ) * GamA d L V₀c lbar (mt β h) (bt β h)).re

variable (d L) in
/-- `τh(β, h, x) = Re(c² Q1(x))`. -/
def τh (V₀c : ℝ → ℂ → Vcoup) (lbar : ℝ) (bt mt : ℝ → ℝ → ℝ) (β : ℝ) (x : Zd d) (h : ℝ) : ℝ :=
  ((c2F V₀c (bt β h) (mt β h) : ℂ) * Qone d L V₀c lbar (mt β h) (bt β h) x).re

variable (d L) in
/-- `σh(β, h, x) = Re(c⁴ Q2(x))`. -/
def σh (V₀c : ℝ → ℂ → Vcoup) (lbar : ℝ) (bt mt : ℝ → ℝ → ℝ) (β : ℝ) (x : Zd d) (h : ℝ) : ℝ :=
  ((c2F V₀c (bt β h) (mt β h) : ℂ) ^ 2 * Qtwo d L V₀c lbar (mt β h) (bt β h) x).re

theorem tendsto_re_of {u : ℕ → ℝ} {z : ℂ} (h : Tendsto (fun N => (u N : ℂ)) atTop (𝓝 z)) :
    Tendsto u atTop (𝓝 z.re) := by
  have := (Complex.continuous_re.tendsto z).comp h
  simpa [Function.comp_def] using this

variable (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) (hd3 : 3 ≤ d)
  {bbar : ℝ} (hbpos : 0 < bbar) (hb2 : bbar ≤ lbar / 2) (h48 : 48 * C * bbar ≤ 1)
  {bt mt : ℝ → ℝ → ℝ} {β : ℝ} (hsol : SolAt V₀c bbar bt mt β)
include HW hLodd hd3 hbpos hb2 h48 hsol

theorem sol_facts {h : ℝ} (hh : 0 ≤ h) :
    0 < bt β h ∧ bt β h < lbar ∧ ‖((bt β h : ℝ) : ℂ)‖ ≤ lbar ∧ -1 < s0R V₀c (bt β h) (mt β h) ∧
      |s0R V₀c (bt β h) (mt β h)| ≤ 1 / 2 ∧ 0 ≤ mt β h := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hsol h hh
  have hl := HW.lbar_pos
  have hC := HW.C_nonneg
  have hbl : bt β h < lbar := by linarith
  have hs := abs_s0R_le HW.toFlowData h1.le hbl.le h3
  have hs2 : |s0R V₀c (bt β h) (mt β h)| ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h2 hC; nlinarith
  refine ⟨h1, hbl, ?_, by linarith [(abs_le.1 hs2).1], hs2, h3⟩
  rw [Complex.norm_real, Real.norm_of_nonneg h1.le]; exact hbl.le

/-! ### The limits `N → ∞` at `h > 0` -/

section Lim

variable {Cs Cs1 Cq Cb : ℝ} (hCs : 0 ≤ Cs) (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs)
  (hCs1 : 0 ≤ Cs1) (hS1 : StepBd1 d L A ℓ₀ V₀c lbar C κ Cs1) (hCq : 0 ≤ Cq) (hCb : 0 ≤ Cb)
  (hP : PairHyp2 d L A ℓ₀ V₀c lbar C κ Cq Cb)
include hCs hS

theorem lim_z {h : ℝ} (hh : 0 < h) :
    Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N))) atTop
      (𝓝 (θh d L V₀c lbar bt mt β h)) := by
  obtain ⟨hb, -, hbl, hs, -, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol hh.le
  obtain ⟨-, -, -, hm, hβ, hhF, -⟩ := hsol h hh.le
  have hm' := hm hh
  have H := ObsLimHyp.ofW HW hLodd
  refine tendsto_re_of ?_
  have e : ∀ N, ((H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N)) : ℝ) : ℂ) =
      1 - (c2F V₀c (bt β h) (mt β h) : ℂ) * avg (Suscept.Cov d L N (mt β h))
        (VE (V₀c (mt β h) (bt β h)) univ) (psibar (0 : Lam d L N) * psi 0) := fun N => by
    have := avgH_z (N := N) HW.conj HW.hb hb hs hm' (by rw [hhF]; exact hh.le) (0 : Lam d L N)
    rw [hβ, hhF] at this
    exact this
  simp only [e]
  exact tendsto_const_nhds.sub (tendsto_const_nhds.mul
    (avg_pbp_tendsto H hCs hS hd3 hm' hbl))

omit hCs hS in
include hCs1 hS1 in
theorem lim_ξη {h : ℝ} (hh : 0 < h) {x : Zd d} (hx0 : x ≠ 0) :
    Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h)
      (H02.ξ (0 : Lam d L N) * H02.η (toT L N x))) atTop (𝓝 (τh d L V₀c lbar bt mt β x h)) := by
  obtain ⟨hb, -, hbl, hs, -, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol hh.le
  obtain ⟨-, -, -, hm, hβ, hhF, -⟩ := hsol h hh.le
  have hm' := hm hh
  have H := ObsLimHyp.ofW HW hLodd
  refine tendsto_re_of ?_
  have e : ∀ N, ((H02.avg (nnW d L N β) (fun _ => h) (H02.ξ (0 : Lam d L N) * H02.η (toT L N x)) :
      ℝ) : ℂ) = (c2F V₀c (bt β h) (mt β h) : ℂ) * avg (Suscept.Cov d L N (mt β h))
        (VE (V₀c (mt β h) (bt β h)) univ) (psibar (0 : Lam d L N) * psi (prj x)) := fun N => by
    have := avgH_ξη (N := N) HW.conj HW.hb hb hs hm' (by rw [hhF]; exact hh.le) (0 : Lam d L N) (prj x)
    rw [hβ, hhF] at this
    exact this
  simp only [e]
  exact tendsto_const_nhds.mul
    (avg_two_tendsto H (by omega) hCs1 hS1 hd3 hm' hbl hx0)

include hCq hCb hP in
theorem lim_cov {h : ℝ} (hh : 0 < h) {x : Zd d} (hx0 : x ≠ 0) :
    Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h)
        (H02.z (0 : Lam d L N) * H02.z (toT L N x)) -
      H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N)) *
        H02.avg (nnW d L N β) (fun _ => h) (H02.z (toT L N x))) atTop
      (𝓝 (σh d L V₀c lbar bt mt β x h)) := by
  obtain ⟨hb, -, hbl, hs, -, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol hh.le
  obtain ⟨-, -, -, hm, hβ, hhF, -⟩ := hsol h hh.le
  have hm' := hm hh
  have H := ObsLimHyp.ofW HW hLodd
  refine tendsto_re_of ?_
  have e : ∀ N, ((H02.avg (nnW d L N β) (fun _ => h)
        (H02.z (0 : Lam d L N) * H02.z (toT L N x)) -
      H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N)) *
        H02.avg (nnW d L N β) (fun _ => h) (H02.z (toT L N x)) : ℝ) : ℂ) =
      (c2F V₀c (bt β h) (mt β h) : ℂ) ^ 2 *
        (avg (Suscept.Cov d L N (mt β h)) (VE (V₀c (mt β h) (bt β h)) univ)
          (psibar (0 : Lam d L N) * psi 0 * (psibar (prj x) * psi (prj x))) -
        avg (Suscept.Cov d L N (mt β h)) (VE (V₀c (mt β h) (bt β h)) univ)
            (psibar (0 : Lam d L N) * psi 0) *
          avg (Suscept.Cov d L N (mt β h)) (VE (V₀c (mt β h) (bt β h)) univ)
            (psibar (prj x : Lam d L N) * psi (prj x))) := fun N => by
    have := avgH_cov (N := N) HW.conj HW.hb hb hs hm' (by rw [hhF]; exact hh.le) (0 : Lam d L N) (prj x)
    rw [hβ, hhF] at this
    exact this
  simp only [e]
  exact tendsto_const_nhds.mul
    (trunc_tendsto H (by omega) hCs hS hCq hCb hP hd3 hm' hbl hx0)

include hCs1 hS1 hCq hCb hP in
theorem lim_dot {h : ℝ} (hh : 0 < h) {x : Zd d} (hx0 : x ≠ 0) :
    Tendsto (fun N => H02.avg (nnW d L N β) (fun _ => h)
        (H02.dot (0 : Lam d L N) (toT L N x))) atTop
      (𝓝 (-2 * τh d L V₀c lbar bt mt β x h - σh d L V₀c lbar bt mt β x h -
        θh d L V₀c lbar bt mt β h ^ 2)) := by
  obtain ⟨hb, -, hbl, hs, -, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol hh.le
  obtain ⟨-, -, -, hm, hβ, hhF, -⟩ := hsol h hh.le
  have hm' := hm hh
  have hZ := lim_z HW hLodd hd3 hbpos hb2 h48 hsol hCs hS hh
  have hT := lim_ξη HW hLodd hd3 hbpos hb2 h48 hsol hCs1 hS1 hh hx0
  have hC := lim_cov HW hLodd hd3 hbpos hb2 h48 hsol hCs hS hCq hCb hP hh hx0
  have hsum := ((hT.const_mul (-2)).sub (hC.add (hZ.pow 2)))
  have e : ∀ᶠ N : ℕ in atTop, -2 * H02.avg (nnW d L N β) (fun _ => h)
        (H02.ξ (0 : Lam d L N) * H02.η (toT L N x)) -
      ((H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N) * H02.z (toT L N x)) -
        H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N)) *
          H02.avg (nnW d L N β) (fun _ => h) (H02.z (toT L N x))) +
        H02.avg (nnW d L N β) (fun _ => h) (H02.z (0 : Lam d L N)) ^ 2) =
      H02.avg (nnW d L N β) (fun _ => h) (H02.dot (0 : Lam d L N) (toT L N x)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hd := avgH_dot (N := N) HW.conj HW.hb hb hs hm' (by rw [hhF]; exact hh.le) (0 : Lam d L N) (prj x)
    have htr := avgH_z_transl (d := d) (L := L) (N := N) HW.conj HW.hb hb hs hm'
      (by rw [hhF]; exact hh.le) hN (prj x)
    rw [hβ, hhF] at hd htr
    show _ = H02.avg (nnW d L N β) (fun _ => h) (H02.dot 0 (prj x))
    rw [hd, htr]; ring
  have := hsum.congr' e
  convert this using 2
  ring

end Lim

/-! ### Right-continuity at `h = 0` -/

section Cont

/-- `h ↦ (m̃², b̃)` tends to `(0, b*)` within `[0, ∞) × B(0, λ̄)`. -/
theorem path_tendsto {F : ℝ × ℂ → ℂ} (hF : ContinuousOn F (Set.Ici 0 ×ˢ ball 0 lbar)) :
    Tendsto (fun h => F (mt β h, ((bt β h : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (F (mt β 0, ((bt β 0 : ℝ) : ℂ)))) := by
  obtain ⟨-, -, -, -, -, -, hm0, hmt, hbt, -⟩ := hsol 0 le_rfl
  obtain ⟨hb0, hbl0, -, -, -, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol le_rfl
  have hmem : (mt β 0, ((bt β 0 : ℝ) : ℂ)) ∈ Set.Ici (0 : ℝ) ×ˢ ball (0 : ℂ) lbar := by
    refine ⟨by rw [hm0]; exact Set.self_mem_Ici, ?_⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hb0.le]; exact hbl0
  have hp : Tendsto (fun h => (mt β h, ((bt β h : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝[Set.Ici (0 : ℝ) ×ˢ ball (0 : ℂ) lbar] (mt β 0, ((bt β 0 : ℝ) : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := hmt.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      have h2 := ((Complex.continuous_ofReal.tendsto _).comp hbt).mono_left
        (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hm0]
      exact h1.prodMk_nhds h2
    · filter_upwards [self_mem_nhdsWithin] with h hh
      obtain ⟨hb, hbl, -, -, -, hm⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol
        (le_of_lt (Set.mem_Ioi.1 hh))
      refine ⟨hm, ?_⟩
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hb.le]; exact hbl
  exact (hF _ hmem).tendsto.comp hp

/-- `c² = c2F(b̃, m̃²)` is right-continuous at `h = 0`. -/
theorem c2F_tendsto :
    Tendsto (fun h => c2F V₀c (bt β h) (mt β h)) (𝓝[>] 0)
      (𝓝 (c2F V₀c (bt β 0) (mt β 0))) := by
  obtain ⟨-, -, -, -, -, -, hm0, hmt, hbt, -⟩ := hsol 0 le_rfl
  obtain ⟨hb0, hbl0, -, hs0, -, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol le_rfl
  obtain ⟨hsc, -⟩ := s0R_a0R_cont HW.toFlowData
  have hmem : (bt β 0, mt β 0) ∈ Set.Ico (0 : ℝ) lbar ×ˢ Set.Ici 0 :=
    ⟨⟨hb0.le, hbl0⟩, by rw [hm0]; exact Set.self_mem_Ici⟩
  have hc : ContinuousWithinAt (fun p : ℝ × ℝ => p.1 / (1 + s0R V₀c p.1 p.2))
      (Set.Ico 0 lbar ×ˢ Set.Ici 0) (bt β 0, mt β 0) :=
    continuousWithinAt_fst.div (continuousWithinAt_const.add (hsc _ hmem)) (by linarith)
  have hp : Tendsto (fun h => (bt β h, mt β h)) (𝓝[>] 0)
      (𝓝[Set.Ico (0 : ℝ) lbar ×ˢ Set.Ici 0] (bt β 0, mt β 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := hmt.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      have h2 := hbt.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hm0]
      exact h2.prodMk_nhds h1
    · filter_upwards [self_mem_nhdsWithin] with h hh
      obtain ⟨hb, hbl, -, -, -, hm⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol
        (le_of_lt (Set.mem_Ioi.1 hh))
      exact ⟨⟨hb.le, hbl⟩, hm⟩
  exact hc.tendsto.comp hp

variable {Cs Cs1 Cq Cb : ℝ} (hCs : 0 ≤ Cs) (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs)
  (hCs1 : 0 ≤ Cs1) (hS1 : StepBd1 d L A ℓ₀ V₀c lbar C κ Cs1) (hCq : 0 ≤ Cq) (hCb : 0 ≤ Cb)
  (hP : PairHyp2 d L A ℓ₀ V₀c lbar C κ Cq Cb)

include hCs hS in
theorem cont_θh : Tendsto (θh d L V₀c lbar bt mt β) (𝓝[>] 0)
    (𝓝 (θh d L V₀c lbar bt mt β 0)) := by
  have H := ObsLimHyp.ofW HW hLodd
  have hG := path_tendsto HW hLodd hd3 hbpos hb2 h48 hsol (GamA_joint H (by omega) hCs hS hd3)
  have hc := c2F_tendsto HW hLodd hd3 hbpos hb2 h48 hsol
  have h2 : Tendsto (fun h => (1 : ℂ) - (c2F V₀c (bt β h) (mt β h) : ℂ) *
      GamA d L V₀c lbar (mt β h) (bt β h)) (𝓝[>] 0)
      (𝓝 ((1 : ℂ) - (c2F V₀c (bt β 0) (mt β 0) : ℂ) * GamA d L V₀c lbar (mt β 0) (bt β 0))) :=
    tendsto_const_nhds.sub (((Complex.continuous_ofReal.tendsto _).comp hc).mul hG)
  exact (Complex.continuous_re.tendsto _).comp h2

include hCs1 hS1 in
theorem cont_τh {x : Zd d} (hx0 : x ≠ 0) : Tendsto (τh d L V₀c lbar bt mt β x) (𝓝[>] 0)
    (𝓝 (τh d L V₀c lbar bt mt β x 0)) := by
  have H := ObsLimHyp.ofW HW hLodd
  have hG := path_tendsto HW hLodd hd3 hbpos hb2 h48 hsol
    (Qone_joint H (by omega) hCs1 hS1 hd3 hx0)
  have hc := c2F_tendsto HW hLodd hd3 hbpos hb2 h48 hsol
  have := ((Complex.continuous_ofReal.tendsto _).comp hc).mul hG
  exact (Complex.continuous_re.tendsto _).comp this

include hCs hS hCq hCb hP in
theorem cont_σh {x : Zd d} (hx0 : x ≠ 0) : Tendsto (σh d L V₀c lbar bt mt β x) (𝓝[>] 0)
    (𝓝 (σh d L V₀c lbar bt mt β x 0)) := by
  have H := ObsLimHyp.ofW HW hLodd
  have hG := path_tendsto HW hLodd hd3 hbpos hb2 h48 hsol
    (Qtwo_joint H (by omega) hCs hS hCq hCb hP hd3 hx0)
  have hc := c2F_tendsto HW hLodd hd3 hbpos hb2 h48 hsol
  have := (((Complex.continuous_ofReal.tendsto _).comp hc).pow 2).mul hG
  exact (Complex.continuous_re.tendsto _).comp this

end Cont

end

end Ward
