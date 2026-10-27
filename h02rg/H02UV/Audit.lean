import Spin2.Multiscale.BetaThm
import Spin2.Final.FinalTheorem
import Spin2.Final.FinalTop
import Spin2.Final.FinalAllX
import Spin2.Cont.ContTheta
import Spin2.Cont.ContShortX
import Spin2.Cont.ContLimit1
import Spin2.Cont.ContEqF5
import Spin2.Cont.ContFx5b
import Spin2.Macro.MacroB
import Spin2.Cont.ContWindowX
import Cont.TorusGreen
import Cont.LatScale
import H02UV.Main.Theorems
import Spin2.Final.ObsBeta3
import Spin2.Final.ObsSum3

/-!
# Main statements of `h02uv-outline.tex` (the arboreal gas in `d = 2`, ultraviolet limit)

Audit of the Lean-proved statements of the outline: the theorems of Section 1 (`sec:results`) of `h02uv-outline.tex` that
are proved in Lean, with their Lean names. The "Lean status" paragraphs of the outline explain
how each Lean statement relates to the paper statement (exact ranges, constants, brackets).
Throughout `d = 2`, `i₀ = 0`, `ε = L^{-N}`, `P_ε(x) = P_{β_ε}[0 ↔ x]`, `f_N = ϑ_ε^{-2} P_ε`.

Not proved in Lean: Conjecture `thm:limit` (full convergence), Conjecture `thm:short` (for the
true limit `G^ren`), Conjecture `thm:macro` (first-order term `2Z G_𝕋/β_R`), `cor:window` (b),(c)
(remarks), and the weak identity `−ΔG_𝕋 = δ − 1`.

The main theorems of `h02uv-lean.tex` (`H02UV.thm_arboreal_multiscale`,
`H02UV.thm_arboreal_limit_fixed`) are in `H02UV/Main/Theorems.lean` (module `H02UV.Main.Theorems`).

Run with `lake env lean H02UV/Audit.lean`. Expected axioms: `propext`, `Classical.choice`,
`Quot.sound`.
-/

/-! ## thm:beta (Thm 1.1): choice of `β_ε` -/

-- Unique `β_ε(β_R)` with the h = 0 flow perturbative and `Re ǧ_N = 1/β_R`; continuous and
-- increasing in `β_R`; `β_{j+1} = β_j − β₁ log L + O(β_j⁻¹)`, `β₁ = 3/(2π)`,
-- `β_ε = β₁ log(1/ε) + O(log log(1/ε))`.
#check Spin2.thm_beta
#print axioms Spin2.thm_beta

-- The master construction: flow, spin and β conclusions and the magnetisation (`MagConcl`)
-- with one set of constants.
#check Spin2.thm_flow_master_all
#print axioms Spin2.thm_flow_master_all

/-! ## thm:multiscale (Thm 1.2): multiscale formula at h = 0 -/

-- `|P_ε(x) − ϑ_k²| ≤ K ϑ_k²/β_k`, `k = min(j(|x|), N−2)`, `ϑ_j = (β_j/β_ε)^{1/3}`,
-- for `4m²L^{2N} ≤ 1/β_R ≤ g₀`. Base version: coalescence scale `j_x ≤ N − 2`.
#check Spin2.thm_multiscale_final_h0
#print axioms Spin2.thm_multiscale_final_h0

-- The same for every `x ≠ 0` (at `k = min(j_p, N − 2)`).
#check Spin2.thm_multiscale_final_h0_allx
#print axioms Spin2.thm_multiscale_final_h0_allx

-- For every `b` in the bracket `[bFin(1/(2β_R)), bFin(2/β_R)]` and every `x ≠ 0`.
#check Spin2.thm_multiscale_final_h0_allB
#print axioms Spin2.thm_multiscale_final_h0_allB

-- Base version plus the top coalescence scales `j_x ∈ {N−1, N}`.
#check Spin2.thm_multiscale_final_h0_top
#print axioms Spin2.thm_multiscale_final_h0_top

/-! ## Conjecture thm:limit (1.3), `ϑ_ε` part: `ϑ_ε² (log 1/ε)^{2/3} → z_*` -/

-- `|ϑ_ε²(log L^N)^{2/3} − z_*| ≤ z_* · 2K(1+β_R+log N)/(Nβ₁ log L)`, `z_* = (2πβ_R/3)^{2/3}`.
#check Spin2.thm_theta_eps
#print axioms Spin2.thm_theta_eps

-- The bound `f_N(x) ≤ C(δ)` for `|x|/L^N ≥ δ`, uniformly in `N` and `b` in the bracket.
#check Spin2.thm_bound_eps
#print axioms Spin2.thm_bound_eps

/-! ## prop:equi-r (Prop 1.4): equicontinuity on `{|x| ≥ r}`, limits there; short distances at fixed ε -/

-- (i) With `r`-dependent couplings `1/β_R ≤ g(r)`, `m²L^{2N} ≤ μ(r)`: `(f_N)` asymptotically
-- equicontinuous on `{|x| ≥ r}`; a subsequence converges uniformly there. One radius:
#check Spin2.thm_limit_equi_r
#print axioms Spin2.thm_limit_equi_r

-- The same on compact subsets of `{‖x‖ > r₀}` (smallness for every `r > r₀`).
#check Spin2.thm_limit_equi_rAnn
#print axioms Spin2.thm_limit_equi_rAnn

-- (ii) = finite-ε form of Conjecture thm:short (1.6), every `x ≠ 0`:
-- (A) `|f_N(x) − (β_k/β_R)^{2/3}| ≤ K(β_k/β_R)^{2/3}/β_k`, `|β_k − β₁λ| ≤ K_c(1+β_R+log(1+λ))`,
-- `λ = log(L^N/|x|)`; (B) the `(β₁λ/β_R)^{2/3}` form; (C) an upper bound.
#check Spin2.thm_short_epsX
#print axioms Spin2.thm_short_epsX

-- `|f_N(x) − (β₁λ/β_R)^{2/3}| ≤ K'(β₁λ/β_R)^{2/3} log λ/λ` for `|x|/L^N ≤ δ₀`, and the same
-- for every subsequential limit.
#check Spin2.thm_short_eps_logX
#print axioms Spin2.thm_short_eps_logX

/-! ## thm:limit-fixed (Thm 1.5): continuum limit at fixed `β_R` on `𝕋 \ {0}` -/

-- For `1/β_R ≤ g₀(L)` and admissible `(R_N, m_N², b_N)`: (a) `(f_N)` is asymptotically
-- equicontinuous on `{|x| ≥ r}` for every `r > 0`; (b) a subsequence converges uniformly on
-- compacts of `𝕋 \ {0}` to `G`, continuous, nonnegative, point-group invariant, bounded away
-- from 0, with `|G(x) − (β₁λ/β_R)^{2/3}| ≤ K'(β₁λ/β_R)^{2/3} log λ/λ`, `λ = log(1/|x|)`.
#check Spin2.thm_limit_fixed_betaR
#print axioms Spin2.thm_limit_fixed_betaR

/-! ## thm:macro0 (Thm 1.8): macroscopic form at order zero -/

-- (a) `β_{N−2}/β_R ∈ [1/4, 5]` and `|f_N(x) − Z_ε| ≤ C(δ,L)/β_R` for `|x|/L^N ≥ δ`,
-- `Z_ε = (β_{N−2}/β_R)^{2/3}`.
#check Spin2.thm_macro_eps0
#print axioms Spin2.thm_macro_eps0

-- (b) Limits `G` (of thm:limit-fixed) satisfy `|G(x) − G(y)| ≤ C(δ,L)/β_R` and
-- `G(x) ≥ 4^{-2/3} − C(δ,L)/β_R` for `‖x‖, ‖y‖ ≥ δ`.
#check Spin2.thm_macro_lim0
#print axioms Spin2.thm_macro_lim0

/-! ## Continuum Green function `G_𝕋` (library `Cont`; input for Conjecture thm:macro (1.7)) -/

-- `G_𝕋(x) = ∫₀^∞ (p_t(x) − 1) dt` on `𝕋 = UnitAddTorus (Fin 2)` is continuous on `𝕋 \ {0}`.
#check Cont.torusGreen_continuousOn
#print axioms Cont.torusGreen_continuousOn

-- Logarithmic singularity: `G_𝕋(x) + (1/2π) log |x|_𝕋 → c` as `x → 0`.
#check Cont.torusGreen_log_singularity
#print axioms Cont.torusGreen_log_singularity

-- Scaling limit of the zero-mode-free lattice Green function: `G_{Λ_N}(⌊L^N x⌉) → G_𝕋(x)`
-- uniformly on compact subsets of `𝕋 \ {0}`.
#check Cont.latGreen_latPtN_tendstoUniformlyOn
#print axioms Cont.latGreen_latPtN_tendstoUniformlyOn

/-! ## cor:window (Cor 1.9) (a): scaling window -/

-- `β_ε = A log(1/ε)` with `A > 3/(2π)` and `|x_N|/L^N → ℓ > 0`:
-- `P_ε(x_N) → (1 − 3/(2πA))^{2/3}`.
#check Spin2.thm_cor_window_aX
#print axioms Spin2.thm_cor_window_aX

/-! ## Theorems 1.1, 1.2, 1.5 for the arboreal gas, without the auxiliary mass `m²` (`h02uv-lean.tex`, `summaries/h02uv.tex`) -/

-- `avg0_mass_indep`, `avg0_eq_Pconn`: `H02UV/Spin2/Final/Arboreal.lean`; the two theorems:
-- `H02UV/Main/Theorems.lean`.

-- Mass-shift identity at h = 0: `⟨ψ̄_0ψ_x⟩` with covariance `(−Δ+m²)^{-1}` and `a₀ = b − m²`
-- does not depend on `m² > 0`; `b⟨ψ̄_0ψ_x⟩ = P_{1/b}[0 ↔ x]` (arboreal gas).
#check Spin2.avg0_mass_indep
#print axioms Spin2.avg0_mass_indep
#check Spin2.avg0_eq_Pconn
#print axioms Spin2.avg0_eq_Pconn

-- Thms 1.1 + 1.2: for N ≥ N₀, 1/β_R ≤ g₀ there are `β_ε` and `(β_j)` with `ArbScale`
-- (`|β_ε − β₁ log L^N| ≤ K_ε(1+β_R+log N)`, scale bounds on `β_j`, `|P_{β_ε}[0↔x] − ϑ_k²| ≤ Kϑ_k²/β_k`)
-- and `ArbShort` (`ϑ_ε^{-2}P_{β_ε}[0↔x] ≈ (β₁λ/β_R)^{2/3}`). `m²` is chosen internally.
#check H02UV.thm_arboreal_multiscale
#print axioms H02UV.thm_arboreal_multiscale

-- Thm 1.5: a sequence `β_N` (internal `m_N²`, bracket point) with the conclusions of 1.1/1.2 for
-- N ≥ N₀; `f_N = (β_R/β_N)^{-2/3}P_{β_N}[0 ↔ x_N]` equicontinuous, subsequential limit `G` on `𝕋 ∖ {0}`.
#check H02UV.thm_arboreal_limit_fixed
#print axioms H02UV.thm_arboreal_limit_fixed

/-! ## The observable renormalisation condition (`summaries/h02uv-outline.tex`, Theorems thm:obs, thm:limit-obs) -/

-- `t(β, N) = β · P_β[0 ↔ x₀,N]^{3/2}`, `x₀ = (1/2, 0)`; the normalised two-point function
-- `f_N(x) = P_{β_N}[0 ↔ x_N]/P_{β_N}[0 ↔ x₀,N]`.
#check @Spin2.obsBeta
#check @Spin2.obsF

-- Thm 2.2: for N ≥ N₀, t ≥ t₀ there is `β_N > 0` with `obsBeta L N β_N = t`, running couplings
-- `β̃_j` with `β̃_0 = β_N`, `|β_N − β₁ log L^N| ≤ K_ε(1+t+log N)`, `|β̃_{N−2} − t| ≤ K`, the
-- multiscale formula for every `x ≠ 0` (`ObsScale`), and the short-distance bounds of the
-- normalised two-point function in terms of `t` (`ArbShort L N t`).
#check Spin2.thm_arboreal_obs
#print axioms Spin2.thm_arboreal_obs

-- Thm 2.3: for t ≥ t₀ a sequence `β_N` with `obsBeta L N β_N = t` (N ≥ N₀) and the conclusions of
-- Thm 2.2; `f_N` equicontinuous; a subsequence converges uniformly on compacts of `𝕋 ∖ {0}` to
-- `G` continuous, nonnegative, point-group invariant, bounded away from 0, `G(x₀) = 1`,
-- `|G(x) − (β₁λ/t)^{2/3}| ≤ K'(β₁λ/t)^{2/3} log λ/λ`, `λ = log(1/|x|)`.
#check Spin2.thm_arboreal_limit_obs
#print axioms Spin2.thm_arboreal_limit_obs

/-! ## The summed observable renormalisation condition (`h02uv-outline.tex`, thm:obs-sum,
thm:limit-obs-sum) -/

-- `obsDens L N β = (∑_{x ∈ Λ_N} P_β[0 ↔ x])/L^{2N} = E_β|T_0|/|Λ_N|`,
-- `t_Σ(β, N) = β · obsDens L N β^{3/2}`; the normalised two-point function
-- `f^Σ_N(x) = P_{β_N}[0 ↔ x_N]/obsDens L N β_N`.
#check @Spin2.obsDens
#print axioms Spin2.obsDens
#check @Spin2.obsBetaSum
#print axioms Spin2.obsBetaSum
#check @Spin2.obsFS

-- thm:obs-sum: for N ≥ N₀, t ≥ t₀ there is `β_N > 0` with `obsBetaSum L N β_N = t` and the
-- conclusions `ObsScale`, `ArbShort L N t` of Thm 2.2.
#check Spin2.thm_arboreal_sum
#print axioms Spin2.thm_arboreal_sum

-- thm:limit-obs-sum: for t ≥ t₀ a sequence `β_N` with `obsBetaSum L N β_N = t` (N ≥ N₀), the
-- lattice average of `f^Σ_N` equal to 1, and the conclusions of thm:obs-sum; `f^Σ_N`
-- equicontinuous; a subsequence converges uniformly on compacts of `𝕋 ∖ {0}` to `G` continuous,
-- nonnegative, point-group invariant, bounded away from 0, with the short-distance law.
#check Spin2.thm_arboreal_limit_sum
#print axioms Spin2.thm_arboreal_limit_sum
