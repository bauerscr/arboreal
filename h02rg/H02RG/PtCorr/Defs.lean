import Obs.FlowObs
import Suscept.PropSuscept

/-!
# Definitions for Section `sec:obs` (finite volume, `m² > 0`)

Along the observable flow `Obs.flowO` (which stores only the `V` part `Coup.toV` of the
observable coupling constants), the `u` parts produced by the steps are accumulated by hand:

* `nextAt … j = (u + V)^obs_{j+1}`, the full coupling constants produced by step `j`
  (`Obs.nextObs` with the covariance `Flow.covAt … j = C_{j+1}`);
* `qN = ∑_{j<N} (q_{a,j+1} + q_{b,j+1})`, `gaN = ∑_{j<N} γ_{a,j+1}`, `gbN = ∑_{j<N} γ_{b,j+1}`
  (`γ = 0` in Case (1)), the constants `q_N`, `γ_{a,N}`, `γ_{b,N}` of the text;
* `uObsN = ∑_{j<N} u^obs_{j+1}(Λ)`, an element with scalar components (`coe_uObsN`):
  `u^obs_N(Λ) = -σ_a γ_{a,N} - σ_b γ_{b,N} - σ_aσ_b q_N` (Case (2)),
  `-σ_a σ̄_b q_N` (Case (1));
* `VoN = V^obs_N` and `KNO = K_N(Λ)` (with observables);
* `ZtO = Z̃^obs_{N,N} = e^{u_N |Λ|} 𝔼_C θ e^{-V_0(Λ)}` with `C = (-Δ + m²)^{-1}` and
  `V_0 = V^∅_0 + V^obs_0` (split evaluation `Obs.VfullX`); its bulk part is
  `Suscept.ZtNN` (`bulk_ZtO`, in `PtCorr.ZNNObs`);
* `tau = t_N / |Λ|`, the constant covariance `t_N Q_N` (`Suscept.tQ_eq_cst`).

Restriction to constant fields (`RcO`) and the coefficients `c1p`, `c1m` of `ψ`, `ψ̄` are in
`PtCorr.Coef`.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Loc Step Obs

variable {d L : ℕ} [NeZero L]

section Defs

variable (d L) (c : Case) (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N)

/-- `(u + V)^obs_{j+1}`: the full observable coupling constants produced by step `j` of the
observable flow. -/
abbrev nextAt (j : ℕ) : Coup c :=
  nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
    (flowO d L c N msq V₀ Vo₀ a b j).2 a b

/-- `q_N = ∑_{j<N} (q_{a,j+1} + q_{b,j+1})`. -/
def qN : ℂ := ∑ j ∈ range N, (qaOf c (nextAt d L c N msq V₀ Vo₀ a b j) +
  qbOf c (nextAt d L c N msq V₀ Vo₀ a b j))

/-- `γ_{a,N} = ∑_{j<N} γ_{a,j+1}` (`0` in Case (1)). -/
def gaN : ℂ := ∑ j ∈ range N, gaOf c (nextAt d L c N msq V₀ Vo₀ a b j)

/-- `γ_{b,N} = ∑_{j<N} γ_{b,j+1}` (`0` in Case (1)). -/
def gbN : ℂ := ∑ j ∈ range N, gbOf c (nextAt d L c N msq V₀ Vo₀ a b j)

/-- `u^obs_N(Λ) = ∑_{j<N} u^obs_{j+1}(Λ)`. -/
def uObsN : OE c (Lam d L N) :=
  ∑ j ∈ range N, uObsX j (Flow.covAt d L N msq j) (flowO d L c N msq V₀ Vo₀ a b j).1
    (flowO d L c N msq V₀ Vo₀ a b j).2 a b univ

/-- `V^obs_N`. -/
abbrev VoN : Coup c := (flowO d L c N msq V₀ Vo₀ a b N).1

/-- `K_N(Λ)` (with observables). -/
abbrev KNO : OE c (Lam d L N) := (flowO d L c N msq V₀ Vo₀ a b N).2 univ

/-- `Z̃^obs_{N,N} = e^{u_N |Λ|} 𝔼_C θ e^{-V_0(Λ)}`, `C = (-Δ + m²)^{-1}`. -/
def ZtO : OE c (Lam d L N) :=
  Complex.exp (Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N)) •
    ECO (Suscept.Cov d L N msq) (thetaO (oexp (-VfullX V₀ Vo₀ a b univ)))

/-- `τ = t_N / |Λ|`. -/
abbrev tau : ℂ := ((Suscept.tNN d L N msq / Fintype.card (Lam d L N) : ℝ) : ℂ)

end Defs

/-! ### The components of `u^obs` -/

section UObs

variable {c : Case} {N : ℕ}

/-- `u^obs_{j+1}(Λ)` has scalar components `(0, -γ_a, -γ_b, -(q_a + q_b))`. -/
theorem coe_uObsX_univ (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vo : Coup c)
    (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N) :
    (uObsX j C Vo K a b univ : SA c (Lam d L N)) =
      ⟨0, algebraMap ℂ (Alg d L N) (-gaOf c (nextObs C j Vo K a b)),
        algebraMap ℂ (Alg d L N) (-gbOf c (nextObs C j Vo K a b)),
        algebraMap ℂ (Alg d L N) (-(qaOf c (nextObs C j Vo K a b) +
          qbOf c (nextObs C j Vo K a b)))⟩ := by
  rw [uObsX, splitO_univ, coe_evalO]
  cases c <;> ext <;>
    simp [evalS, Coup.toU, gaOf, gbOf, qaOf, qbOf, nr, nx]

variable (d L c N) in
/-- `u^obs_N(Λ) = (0, -γ_{a,N}, -γ_{b,N}, -q_N)`. -/
theorem coe_uObsN (msq : ℝ) (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N) :
    (uObsN d L c N msq V₀ Vo₀ a b : SA c (Lam d L N)) =
      ⟨0, algebraMap ℂ (Alg d L N) (-gaN d L c N msq V₀ Vo₀ a b),
        algebraMap ℂ (Alg d L N) (-gbN d L c N msq V₀ Vo₀ a b),
        algebraMap ℂ (Alg d L N) (-qN d L c N msq V₀ Vo₀ a b)⟩ := by
  rw [uObsN, AddSubmonoidClass.coe_finsetSum]
  simp only [coe_uObsX_univ]
  refine SA.ext ?_ ?_ ?_ ?_
  · rw [SA.sum_e]; simp
  · rw [SA.sum_a, gaN, ← Finset.sum_neg_distrib, map_sum]
  · rw [SA.sum_b, gbN, ← Finset.sum_neg_distrib, map_sum]
  · rw [SA.sum_ab, qN, ← Finset.sum_neg_distrib, map_sum]

theorem bulk_uObsN (msq : ℝ) (V₀ : Vcoup) (Vo₀ : Coup c) (a b : Lam d L N) :
    bulk (uObsN d L c N msq V₀ Vo₀ a b) = 0 :=
  Subtype.ext (by rw [coe_bulk, coe_uObsN]; rfl)

end UObs

end

end PtCorr
