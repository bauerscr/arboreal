import Step2.Flow.FlowWin1
import Step2.Last.FlowLastCont
import PtCorr2.Zero.WardNeg1

/-!
# Route (a1), tasks 3–4: the point `h = 0` in the window; shooting on the `h = 0` family

**Task 3.** At fixed `b`, the windowed family of initial data `μ ∈ [μ₋, μ₊]` around the admissible
`μ₀^c` (`Flow2.Hist.win_interval`, signed cone from `ZHyp` by `coneSG_of_Z`) is an interval, and
`h = (μ₀ + m²)/b - 1` is affine increasing in `μ₀`. So `μ₀ = b - m²` (`h = 0`) lies in the window
as soon as `h(μ₋) < 0 ≤ h(μ₊)`:
* the **upper end** from the one-point function (named input **`H0OnePtUp`**: `⟨Z_0⟩ ≠ 0`,
  `r = 1 - b⟨ψ̄_0ψ_0⟩ ≥ 0`, `χ = ∑_x⟨ψ̄_0ψ_x⟩ > 0` at `μ₊`; then the Ward identity
  `(μ₀ + m² - b)χ = r` gives `h ≥ 0`, `PtCorr2.h_nonneg_of_onept`);
* the **lower end** from positivity (`PtCorr2.h_neg_of_chi_out`: for `h ≥ 0`, `0 ≤ χ ≤ |Λ|/b`)
  once the susceptibility leaves `[0, |Λ|/b]` somewhere in the window (named input
  **`H0SusceptExit`**; RG: `χ ≈ |Λ|(1+k⁰)/(Z_N d)` with `d` crossing `0` in the window), or
  `⟨Z_0⟩` vanishes somewhere in the window (**`H0ZeroExit`**, `PtCorr2.h_neg_of_Zb_eq_zero`).

`h0_mem_window` (model level), **`h0_windowed`** (along `rgData R`: the trajectory from
`(b, b - m²)` is in `D_ε` up to `N_h` with `c₋ ≤ μ_{N_h} ≤ c₊` and `|ǧ_{N_h} - ǧ^c_{N_h}| ≤ p(c₊ - c₋)`).

**Task 4.** `gFinH0`: the final coupling `Re ǧ_N` along the `h = 0` family `b ↦ (b, b - m²)`;
**`gFinH0_cont`** (continuous in `b`, from `gFin_contM` and the continuity of the unclamped flow);
**`exists_b_h0`** (IVT: a `b` with `Re ǧ_N = 1/β_R` between two values bracketing `1/β_R`).
Uniqueness is *not* claimed: the `ǧ`-cone of `traj_cone_top_z` is not forward invariant without
a common final condition (its `μ`-part comes from `not_mu_cone`), see Log.
-/

namespace Spin2

open Set Filter Topology Finset

noncomputable section

open Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step PtCorr2

variable {L N : ℕ} [NeZero L]

/-- **Named input (RG one-point value at the upper window end).** At `(b, μ)`: `⟨Z_0⟩ ≠ 0`,
`r = 1 - b⟨ψ̄_0ψ_0⟩` real `≥ 0`, `χ = ∑_x ⟨ψ̄_0ψ_x⟩` real `> 0`. (RG: `r ≈ M_N(1 - qǧ_N/d)` with
`d > qǧ_N` at the upper end, `χ ≈ |Λ|(1+k⁰)/(Z_N d) > 0`.) -/
def H0OnePtUp (L N : ℕ) [NeZero L] (msq b μ : ℝ) : Prop :=
  Obs.Zb (Suscept.Cov 2 L N msq) (VE (V0c b μ) (Finset.univ : Finset (Lam 2 L N))) ≠ 0 ∧
  (∃ r : ℝ, 0 ≤ r ∧ 1 - (b : ℂ) * avg0 L N msq b μ (psibar 0 * psi 0) = r) ∧
  (∃ χ : ℝ, 0 < χ ∧ ∑ x : Lam 2 L N, avg0 L N msq b μ (psibar 0 * psi x) = χ)

/-- **Named input (RG susceptibility on the window).** Somewhere in `[μl, μu]` the susceptibility
`χ = ∑_x ⟨ψ̄_0ψ_x⟩` is not a real number in `[0, |Λ|/b]`. -/
def H0SusceptExit (L N : ℕ) [NeZero L] (msq b μl μu : ℝ) : Prop :=
  ∃ μ ∈ Icc μl μu, ¬ ∃ χ : ℝ, 0 ≤ χ ∧ χ ≤ (Fintype.card (Lam 2 L N) : ℝ) / b ∧
    ∑ x : Lam 2 L N, avg0 L N msq b μ (psibar 0 * psi x) = χ

/-- **`h = 0` lies in the window** (model level): the upper end has `h ≥ 0`, a point of the window
has `h < 0`. -/
theorem h0_mem_window {msq b μl μu : ℝ} (hb : 0 < b) (hm0 : 0 < msq)
    (hup : H0OnePtUp L N msq b μu) (hlo : ∃ μ ∈ Icc μl μu, μ + msq < b) :
    b - msq ∈ Ioc μl μu := by
  obtain ⟨hZ, ⟨r, hr0, hr⟩, ⟨χ, hχ0, hχ⟩⟩ := hup
  have h1 := h_nonneg_of_onept hb hm0 hZ hr0 hχ0 hr hχ
  obtain ⟨μ, hμ, hlt⟩ := hlo
  exact ⟨by linarith [hμ.1], by linarith⟩

theorem h0_mem_window' {msq b μl μu : ℝ} (hb : 0 < b) (hm0 : 0 < msq)
    (hup : H0OnePtUp L N msq b μu) (hex : H0SusceptExit L N msq b μl μu) :
    b - msq ∈ Ioc μl μu := by
  obtain ⟨μ, hμ, hout⟩ := hex
  exact h0_mem_window hb hm0 hup ⟨μ, hμ, h_neg_of_chi_out hb hm0 hout⟩

variable {E : Type*} [NormedAddCommGroup E]

/-- **The `h = 0` trajectory is windowed** (route (a1), task 3). Under the flow hypotheses
(`HHyp`, `ZHyp` with the smallness of `coneS_of_Z`, `ε ≤ eps0u`, `c_gε ≤ (1-δ)β`), around an
admissible `μ₀^c` there are window ends `μl ≤ μ₀^c ≤ μu` with targets `cl ≤ 0 ≤ cu`
(`p = K_h((1+L²)/2, κ, A)·a`, the `ǧ`-slope of the signed cone), and with the named inputs at the
ends the trajectory from `(b, b - m²)` is in `D_ε` up to `N_h`, `cl ≤ μ_{N_h} ≤ cu` and
`|ǧ_{N_h} - ǧ^c_{N_h}| ≤ p(cu - cl)`. -/
theorem h0_windowed (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    {β δ κ cg cm cT A' a' A a Aζ aζ bζ ε : ℝ} {Z : ℕ → Hist.Seq (Xs R) → E}
    (H : HHyp (rgData R) ((L : ℝ) ^ 2) β δ κ cg cm cT Nh A' a' ε)
    (HZ : ZHyp (rgData R) ((L : ℝ) ^ 2) β δ κ cg cm cT Nh Z A a Aζ aζ bζ ε)
    (ha0 : a ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ A)
    (hs : bζ * sZ Aζ aζ (Kh ((1 + (L : ℝ) ^ 2) / 2) κ A * a) (Qh κ * a) ≤ ((L : ℝ) ^ 2 - 1) / 4)
    (he : ε ≤ eps0u ((L : ℝ) ^ 2) β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β)
    (hm0 : 0 < R.msq) {b μc cl cu y : ℝ} (hb : 0 < b) (hy : y ≤ ε)
    (h0 : Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μc) (hl : cl ≤ 0) (hu : 0 ≤ cu)
    (hgy : (traj (rgData R) ((L : ℝ) ^ 2) b μc Nh).1 +
      Kh ((1 + (L : ℝ) ^ 2) / 2) κ A * a * (cu - cl) < y)
    (hcl : |cl| < cmu ((L : ℝ) ^ 2) cm * ((traj (rgData R) ((L : ℝ) ^ 2) b μc Nh).1 -
      Kh ((1 + (L : ℝ) ^ 2) / 2) κ A * a * (cu - cl)))
    (hcu : |cu| < cmu ((L : ℝ) ^ 2) cm * ((traj (rgData R) ((L : ℝ) ^ 2) b μc Nh).1 -
      Kh ((1 + (L : ℝ) ^ 2) / 2) κ A * a * (cu - cl))) :
    ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μl cl ∧
      AdmW (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μu cu ∧
      (H0OnePtUp L N R.msq b μu → H0SusceptExit L N R.msq b μl μu →
        b - R.msq ∈ Ioc μl μu ∧
        (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgData R) ((L : ℝ) ^ 2) b (b - R.msq) j)) ∧
        cl ≤ (traj (rgData R) ((L : ℝ) ^ 2) b (b - R.msq) Nh).2.1 ∧
        (traj (rgData R) ((L : ℝ) ^ 2) b (b - R.msq) Nh).2.1 ≤ cu ∧
        |(traj (rgData R) ((L : ℝ) ^ 2) b (b - R.msq) Nh).1 -
            (traj (rgData R) ((L : ℝ) ^ 2) b μc Nh).1| ≤
          Kh ((1 + (L : ℝ) ^ 2) / 2) κ A * a * (cu - cl)) := by
  have hΛ2 : 1 < (1 + (L : ℝ) ^ 2) / 2 := by linarith [H.hΛ]
  have hp : 0 ≤ Kh ((1 + (L : ℝ) ^ 2) / 2) κ A * a :=
    (coef_h hΛ2 H.hκ1 HZ.hA HZ.ha ha0).1
  have hC := coneSG_of_Z H HZ ha0 hs
  obtain ⟨μl, μu, h1, h2, h3, h4, h5⟩ :=
    win_interval H he hgβ hC hb hy h0 hl hu hp hgy hcl hcu
  refine ⟨μl, μu, h1, h2, h3, h4, fun hup hex => ?_⟩
  have hmem := h0_mem_window' hb hm0 hup hex
  obtain ⟨k1, k2, k3, k4⟩ := h5 (b - R.msq) ⟨hmem.1.le, hmem.2⟩
  exact ⟨hmem, k1, k2, k3, k4⟩

/-! ### Task 4: shooting on the `h = 0` family -/

/-- The final coupling `Re ǧ_N` along the `h = 0` family `(b, b - m²)`. -/
def gFinH0 (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (m b : ℝ) : ℝ :=
  gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))

/-- **`b ↦ Re ǧ_N` is continuous along the `h = 0` family.** -/
theorem gFinH0_cont (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {m : ℝ}
    (hm : m ∈ mRange L N) (hNh : Nh < N) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (hcov : CovContM R.P L N 2 R.ρ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    {β δ κ cg cm cT A a ε : ℝ}
    (H : HHyp (rgDataM R m) ((L : ℝ) ^ 2) β δ κ cg cm cT Nh A a ε) :
    Continuous (gFinH0 R Nh m) := by
  have hS : ({m} : Set ℝ) ⊆ mRange L N := Set.singleton_subset_iff.2 hm
  have hc := gFin_contM R hS Nh hρ hρ8 hNh hcov (fun m' hm' => by rw [hm']; exact hV)
  have hφ2 : Continuous fun b : ℝ => truncH R Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) := by
    refine continuous_pi fun j => ?_
    by_cases hj : j ≤ Nh
    · simp only [truncH, if_pos hj]
      exact (continuous_traj H hj).comp (continuous_id.prodMk (continuous_id.sub continuous_const))
    · simp only [truncH, if_neg hj]
      exact continuous_const
  have e : gFinH0 R Nh m = (fun q : ({m} : Set ℝ) × Hist.Seq (Xs R) => gFin (R.withMsq q.1) Nh q.2) ∘
      (fun b : ℝ => ((⟨m, rfl⟩ : ({m} : Set ℝ)),
        truncH R Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))) := by
    funext b
    simp only [Function.comp_apply, gFinH0]
    exact (gFin_truncH R _ Nh _).symm
  rw [e]
  exact hc.comp (continuous_const.prodMk hφ2)

/-- **Existence of the shooting parameter on the `h = 0` family** (IVT in `b`). If
`Re ǧ_N(b₁) ≤ y ≤ Re ǧ_N(b₂)` along `(b, b - m²)`, some `b ∈ [b₁, b₂]` has `Re ǧ_N = y`; combined
with `h0_windowed` at each `b ∈ [b₁, b₂]`, its trajectory is windowed. -/
theorem exists_b_h0 (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {m : ℝ}
    (hm : m ∈ mRange L N) (hNh : Nh < N) (hρ : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (hcov : CovContM R.P L N 2 R.ρ) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    {β δ κ cg cm cT A a ε : ℝ}
    (H : HHyp (rgDataM R m) ((L : ℝ) ^ 2) β δ κ cg cm cT Nh A a ε)
    {b₁ b₂ y : ℝ} (hb : b₁ ≤ b₂) (h1 : gFinH0 R Nh m b₁ ≤ y) (h2 : y ≤ gFinH0 R Nh m b₂) :
    ∃ b ∈ Icc b₁ b₂, gFinH0 R Nh m b = y :=
  intermediate_value_Icc hb (gFinH0_cont R hm hNh hρ hρ8 hcov hV H).continuousOn ⟨h1, h2⟩

end

end Spin2
