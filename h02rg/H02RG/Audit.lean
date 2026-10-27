import H02RG.Main.Theorems
import Ward.CorWardMain
import Psi4.Main
import Psi4.Full
import H02.Main
import H02.Ghost

/-!
# Main statements of `h02rg.tex` (the `H^{0|2}` model / arboreal gas in `d ≥ 3`)

Audit of all main statements of `src/h02rg.tex`: the theorems of Sections 1–2 of `h02rg.tex` with their Lean names.
The main theorems of `h02rg-lean.tex` (`H02RG.thm_forest_macro`, `thm_h02`, `thm_forests0`,
`thm_forests`, `thm_all`) are in `H02RG/Main/Theorems.lean` (module `H02RG.Main.Theorems`).
Human-readable versions of the statements: `h02rg-lean.tex` (root), `summaries/h02rg-lean2.tex` (Ward results),
`summaries/h02theorem-lean.tex` (forest identity, `H02` library).

The only hypothesis of each top-level `Ward`/`Psi4` theorem is `3 ≤ d`; `L₀` depends on `d`, and
`L ≥ L₀` is odd. Run with `lake env lean H02RG/Audit.lean`. Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

/-! ## Section 1: results for the arboreal gas and the `H^{0|2}` model -/

-- thm:forest-macro (Thm 1.1). Finite torus, h = 0:
-- `P_β[0 ↔ x] = ζ(β) + c₀(β)/(β|x|^{d-2}) + O(β⁻¹|x|^{-(d-2+κ)}) + O(β⁻¹ L^{-κN})`,
-- `ζ(β) = 1 + O(1/β)`, `c₀(β) = c₀ + O(1/β)`, `c₀ > 0`.
#check H02RG.thm_forest_macro
#print axioms H02RG.thm_forest_macro

-- thm:forests0 (Thm 1.2). The percolation probability `θ_d(β)` exists and `θ_d(β)² = ζ_d(β) = 1 − O(1/β)`.
#check H02RG.thm_forests0
#print axioms H02RG.thm_forests0

-- thm:forests (Thm 1.3). Truncated connection probabilities `τ_β(x)`, `σ_β(x)` exist,
-- `τ_β ~ c₁(β)/(β|x|^{d-2})`, `σ_β ~ c₂(β)/(β²|x|^{2d-4})`; `c₂θ²/c₁² = 1`, `c₀ = 2c₁`.
#check H02RG.thm_forests
#print axioms H02RG.thm_forests

-- prop:h02-forest (Prop 1.4). Forest representation on any finite graph, `β, h ≥ 0`:
-- `P[0 ↔ g] = ⟨z₀⟩`, `P[0 ↔ x, 0 ↮ g] = ⟨ξ₀η_x⟩`, `P[0 ↔ x] + P[0 ↮ x, 0 ↔ g, x ↔ g] = −⟨u₀·u_x⟩`.
#check H02.prop_h02_forest
#print axioms H02.prop_h02_forest

-- Forest identity behind prop:h02-forest (h02.tex, thm:H02forest; see h02theorem-lean.tex):
-- `[1]_{β,h} = Σ_F Π_{e∈F} β_e Π_{T} (1 + Σ_{i∈T} h_i)`.
#check H02.thm_H02forest
#print axioms H02.thm_H02forest

-- thm:h02 (Thm 1.5). `H^{0|2}` model, `lim_{h↓0} lim_N`: `⟨z₀⟩ → θ_d(β)`,
-- `⟨ξ₀η_x⟩ ~ c₁(β)/(β|x|^{d-2})`, truncated `⟨z₀z_x⟩ ~ −c₂(β)/(β²|x|^{2d-4})`,
-- `⟨u₀·u_x⟩ = −θ² − 2c₁/(β|x|^{d-2}) + O(...)`.
#check H02RG.thm_h02
#print axioms H02RG.thm_h02

-- All of Section 1 with one shared set of constants (h02rg-lean.tex / h02rg-lean2.tex, thm:all):
-- `thm_forest_macro`, `thm_h02`, `thm_forests0`, `thm_forests` and `ζ = θ²`, `c₂θ²/c₁² = 1`,
-- `c₀ = 2c₁`, `c₀ = 2c_d`.
#check H02RG.thm_all
#print axioms H02RG.thm_all

/-! ## Section 2: renormalisation and Ward identities -/

-- thm:psi4 (Thm 2.1). Fermionic `ψ⁴` model, `b₀` small, `m² ≥ 0`, `L^{-N} ≤ m`: critical
-- `s₀^c, a₀^c = O(b₀)`, susceptibility `Σ_x ⟨ψ̄₀ψ_x⟩ = 1/m² + O(b₀L^{-(2+κ)N})/m⁴`, and the
-- one/two-point asymptotics with `λ = 1 + O(b₀)`, `γ = (−Δ+m²)⁻¹(0,0) + O(b₀)`.
#check Psi4.thm_psi4
#print axioms Psi4.thm_psi4

-- cor:ward (Cor 2.2). (i) `h(b₀,m²) = m² β(b₀,m²)(1 + O(b₀))`; (ii) for β large and `h ≥ 0`
-- there are `b̃₀(β,h) > 0`, `m̃²(β,h) ≥ 0` realising `(β,h)`, right-continuous as `h ↓ 0`.
#check Ward.cor_ward
#print axioms Ward.cor_ward

-- thm:psi4-full (Thm 2.3). As thm:psi4 without `L^{-N} ≤ m`, with the zero-mode
-- coefficients `ã_{N,N}^c`, `ũ_{N,N}^c`, `u_N^c`.
#check Psi4.thm_psi4_full
#print axioms Psi4.thm_psi4_full

-- cor:macro (Lemma 2.4). `E_{β,0}|T₀| = b₀/(1+s₀^c) · (1 + O(b₀L^{-κN}))/ã_{N,N}^c + O(b₀L^{2N})`.
#check Ward.cor_macro
#print axioms Ward.cor_macro

-- cor:anm0 (Lemma 2.5). The zero-mode identity `1 = b₀/(1+s₀^c) [γ + λ/(|Λ_N| ã_{N,N}^c) + ...]`.
#check Ward.cor_anm0
#print axioms Ward.cor_anm0

-- cor:conn4pt (Lemma 2.6). `P_{β,0}[0 ↔ x] = θ² + 2 b₀/(1+s₀^c) λθ (−Δ)⁻¹(0,x) + O(...)`.
#check Ward.cor_conn4pt
#print axioms Ward.cor_conn4pt

-- cor:aNlimit (Lemma 2.7). `λ θ_d(β) = 1`.
#check Ward.cor_aNlimit
#print axioms Ward.cor_aNlimit
