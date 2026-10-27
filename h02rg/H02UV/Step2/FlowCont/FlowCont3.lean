import Step2.FlowCont.FlowCont2
import DressedFRD.Holo
import DressedFRD.Instance

/-!
# Continuity of the RG flow data: the covariance

`rawCov R j ζ` is the kernel of `Γ^int_{j+1}(ζ)`, a rational function of `(ζ_0, …, ζ_j)`.
* `CovCont R j`: the hypothesis that `Γ^int_{j+1}(p)` is continuous in `(ζ_0, …, ζ_j)` at every
  point of the closed polydisc `|ζ_i| ≤ ρ` (for each momentum `p`). Since `Γ^int` is defined with
  divisions (by `Z_k`, `1 - ζ'_k ε_k`, `1 + ζ_j Z_j A Γ_j`) and Lean's division by zero is `0`, this
  can only hold where these denominators do not vanish, so some such hypothesis is needed.
* `covCont_of_small`: `CovCont` holds for `2 ≤ d`, `7 ≤ L`, `0 < m² ≤ L^{-2(N-1)}` and
  `ρ < ζ̄`, with `ζ̄ = ζ̄(P, d, L) > 0` from `thm:main` (`DressedFRD.thm_main_hol`).
* `rawCov_cont`: under `CovCont`, `t ↦ rawCov R j (ζ t)` is continuous entrywise along any
  continuous, admissible history `ζ` vanishing beyond `j`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- The data of the dressed decomposition with vanishing couplings. -/
def D0 (R : RGPar d L N) : DressedFRD.Data d (L ^ N) :=
  ⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, 0⟩

/-- **The continuity hypothesis on the dressed covariance**: for each momentum `p`,
`Γ^int_{j+1}(p)` is continuous in `(ζ_0, …, ζ_j)` at every point of the closed polydisc of
radius `ρ`. -/
def CovCont (R : RGPar d L N) (j : ℕ) : Prop :=
  ∀ z₀ : Fin (j + 1) → ℂ, (∀ i, ‖z₀ i‖ ≤ R.ρ) → ∀ m : Torus d (L ^ N),
    ContinuousAt (fun z : Fin (j + 1) → ℂ => ((D0 R).Dz z).Gint j m) z₀

/-- **`CovCont` for small `ρ`** (`thm:main`(ii): holomorphy on the polydisc `|ζ_i| < ζ̄`). -/
theorem covCont_of_small (P : PtFamily) (hd : 2 ≤ d) (hL : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∀ (N : ℕ) (R : RGPar d L N), R.P = P → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ < ζbar → ∀ j, j < N → CovCont R j := by
  obtain ⟨cS, hcS, hS⟩ := DressedFRD.frd_stdFull P (d := d) hd hL (q := 2) (M := d + 3)
    (by omega)
  obtain ⟨ζbar, hζ, -, K, hK⟩ := DressedFRD.thm_main_hol (d := d) hd le_rfl hL (M := d + 3)
    (by omega) hcS
  refine ⟨ζbar, hζ, fun N R hP hN hm hm' hρ j hj z₀ hz₀ m => ?_⟩
  subst hP
  have hS' := hS (L ^ N) N R.msq hN rfl hm
  have hdiff := ((hK (L ^ N) (D0 R) rfl rfl hS' hm').2 j hj m).1
  have hopen : IsOpen {z : Fin (j + 1) → ℂ | ∀ i, ‖z i‖ < ζbar} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  exact (hdiff.differentiableAt (hopen.mem_nhds fun i => (hz₀ i).trans_lt hρ)).continuousAt

/-- **The covariance is continuous along continuous admissible histories.** -/
theorem rawCov_cont {R : RGPar d L N} {j : ℕ} (hc : CovCont R j) {T : Type*}
    [TopologicalSpace T] {ζ : T → ℕ → ℂ} (hζ : ∀ i, Continuous fun t => ζ t i)
    (hb : ∀ t i, ‖ζ t i‖ ≤ R.ρ) (h0 : ∀ t i, j < i → ζ t i = 0) (x y : Lam d L N) :
    Continuous fun t => rawCov R j (ζ t) x y := by
  let zz : T → Fin (j + 1) → ℂ := fun t i => ζ t i
  have hzz : Continuous zz := continuous_pi fun i => hζ i
  have e : ∀ t, rawCov R j (ζ t) x y =
      DressedFRD.kern (((D0 R).Dz (zz t)).Gint j) (x - y) := by
    intro t
    have : ζ t = DressedFRD.Data.ext (zz t) := by
      funext i
      unfold DressedFRD.Data.ext
      split_ifs with hi
      · rfl
      · exact h0 t i (by omega)
    rw [rawCov, this]
    rfl
  simp only [e]
  have hG : ∀ m, Continuous fun t => ((D0 R).Dz (zz t)).Gint j m := fun m =>
    continuous_iff_continuousAt.2 fun t₀ =>
      (hc (zz t₀) (fun i => hb t₀ i) m).comp hzz.continuousAt
  unfold DressedFRD.kern
  exact continuous_const.mul (continuous_finsetSum _ fun m _ => (hG m).mul continuous_const)

end

end Step2
