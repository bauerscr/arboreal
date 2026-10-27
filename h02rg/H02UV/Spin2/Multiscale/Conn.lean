import PtCorr2.Zero.OnePt

/-!
# The connection probability `P_ε(x)` and its fermionic representation at `h = 0`

`h02uv-outline.tex`, Section 1.1: `ε = L^{-N}`, the discretised unit torus `𝕋_ε = εℤ²/ℤ²` is
identified with `Λ_N = (ℤ/L^Nℤ)² = Lam 2 L N` (lattice units), and

  `P_ε(x) = ℙ^{𝕋_ε}_{β_ε}[0 ↔ x_ε]`,

the arboreal-gas (`ℍ^{0|2}`) connection probability with nearest-neighbour weights `β`
(`Ward.nnW 2 L N β`). In lattice units the point `x_ε` is a vertex `x : Lam 2 L N`.

* `Pconn L N β x`: `P_β[0 ↔ x]` on `Λ_N` (`H02.arborealProb`).
* `Pconn_eq_avg`: `P_β[0 ↔ x] = ⟨ξ_0η_x⟩_{β,0}` (`H02.cor_spin_conn`, `prop:h02-forest`).
* `Pconn_eq_avg0`: at `h = 0`, i.e. `b = μ₀ + m²` (`β = 1/b`), `P_{1/b}[0 ↔ x] = b⟨ψ̄_0ψ_x⟩` for
  the fermionic initial model `V_0 = (0, 0, μ₀, b)` with covariance `(-Δ + m²)^{-1}`
  (`PtCorr2.avg0`; `Ward.bridge_avg_ξη`, `s₀ = 0`, `c² = b`). This is the object represented by
  the observable chain (`PtCorr2.thm_obs_chain_twopt`).
* `Pconn_mem`: `0 ≤ P ≤ 1`.
-/

namespace Spin2

noncomputable section

open Finset Grassmann Loc

variable {L N : ℕ} [NeZero L]

variable (L N) in
/-- **`P_β[0 ↔ x]`** on the torus `Λ_N = Lam 2 L N` (`P_ε(x)` at `β = β_ε`, `x = x_ε`). -/
def Pconn (β : ℝ) (x : Lam 2 L N) : ℝ :=
  H02.arborealProb (Ward.nnW 2 L N β) (Ward.nnW_symm β) (fun F => F.Reachable 0 x)

/-- `P_β[0 ↔ x] = ⟨ξ_0η_x⟩_{β,0}` (`e:P`). -/
theorem Pconn_eq_avg {β : ℝ} (hβ : 0 ≤ β) (x : Lam 2 L N) :
    Pconn L N β x = H02.avg (Ward.nnW 2 L N β) 0 (H02.ξ 0 * H02.η x) := by
  obtain ⟨h1, h2, h3, -⟩ := H02.cor_spin_conn (Ward.nnW_symm (d := 2) (L := L) (N := N) β)
    (Ward.nnW_nonneg hβ) 0 x
  rw [Pconn, h1, h2, h3]

theorem Pconn_mem {β : ℝ} (hβ : 0 ≤ β) (x : Lam 2 L N) : 0 ≤ Pconn L N β x ∧ Pconn L N β x ≤ 1 :=
  ⟨H02.arborealProb_nonneg _ (Ward.nnW_nonneg hβ) _, H02.arborealProb_le_one _ (Ward.nnW_nonneg hβ) _⟩

/-- **At `h = 0`** (`b = μ₀ + m²`): `P_{1/b}[0 ↔ x] = b⟨ψ̄_0ψ_x⟩` in the fermionic model
`V_0 = (0, 0, μ₀, b)` with covariance `(-Δ + m²)^{-1}`. -/
theorem Pconn_eq_avg0 {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b = μ₀ + msq)
    (x : Lam 2 L N) :
    ((Pconn L N (1 / b) x : ℝ) : ℂ) = (b : ℂ) * PtCorr2.avg0 L N msq b μ₀ (psibar 0 * psi x) := by
  have hV := PtCorr2.Vh_eq_V0 (μ₀ := μ₀) (msq := msq) hb
  have h0 : (μ₀ + msq) / b - 1 = 0 := by rw [← hh, div_self hb.ne', sub_self]
  rw [h0] at hV
  have hB := Ward.bridge_avg_ξη (d := 2) (L := L) (N := N) (β := 1 / b) (h := 0) (msq := msq)
    (s₀ := 0) (by positivity) (by norm_num) hm0 0 x
  rw [hV, PtCorr2.onept_b_eq b] at hB
  rw [Pconn_eq_avg (by positivity), ← hB]
  rfl

end

end Spin2
