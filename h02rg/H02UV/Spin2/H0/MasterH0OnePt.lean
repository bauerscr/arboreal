import Spin2.Master.MasterAllCore
import Spin2.H0.H0Window
import PtCorr2.Zero.Flow

/-!
# Route (a1), tasks 2–3: the zero mode and the one-point function along windowed trajectories

Under the consolidated master construction (`MasterCore`, field `hGD : GlueD`), along every
trajectory in `D_ε` up to `N_h` (no final condition, any sign of `h`):

* **`MasterCore.onePtWin`**: `ZeroModeOut` (the zero-mode integration of `prop:ZNN` with the bounds
  in `ǧ_{N_h}`; from `GlueD` and `zeroModeOut_of_glue`), the factorisation
  `⟨Z_0⟩ = (∏_j c_j)·det·e^{-u}·U`, `U = 1 + ũ` (`hist_omega_traj`), and, when the three
  factors do not vanish, `⟨Z_0⟩ ≠ 0`, the dressed susceptibility
  `χ = 1/m² − X/m⁴`, `X = ãπ_N/U + ∑_{j<N} c_jπ_j/ρ_j`, and the Ward identity
  `(μ₀ + m² − b)χ = 1 − b⟨ψ̄_0ψ_0⟩` (`ward2_of_Zne`) — the windowed form of
  `thm_ward_flow_onept`, without `h ≥ 0`.
* Task 3, reduction of the named inputs to the zero-mode coefficient `X` (exact):
  **`h0OnePtUp_of_X`**: `H0OnePtUp` follows from the nonvanishing of the three factors,
  `r = 1 − b⟨ψ̄_0ψ_0⟩` real `≥ 0` (the RG one-point value) and `X` real `< m²`;
  **`h0SusceptExit_of_X`**: `H0SusceptExit` follows from the nonvanishing of the factors at one point
  of the window and `X` not a real number in `[m² − m⁴|Λ|/b, m²]` there.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The zero mode and the one-point function along a windowed trajectory** (any sign of `h`). -/
theorem MasterCore.onePtWin {L : ℕ} [NeZero L] (D : MasterCore L) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ)
    (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ} (hb : 0 < b)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) :
    let R' := R.withMsq m
    let t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
    let out := lastOut R' Nh t
    let U := 1 + uFin (Nh + 1) out (zmRaw R' (Nh + 1) out.ζ)
    let X := aFin (Nh + 1) out * πh R' (Nh + 2) t / U +
      ∑ j ∈ range (Nh + 2), ch₀ R' j t * πh R' j t / ρh R' j t
    ZeroModeOut R' Nh D.Cf t ∧
    omegaC (Γh R' 0 t) (Zh R' 0 t : Alg 2 L N) =
      (∏ j ∈ range (Nh + 1), ch R' j t) *
        (detStep R' (Nh + 1) (histOut R' Nh t).st * Complex.exp (-out.u) * U) ∧
    ((∏ j ∈ range (Nh + 1), ch R' j t) ≠ 0 → detStep R' (Nh + 1) (histOut R' Nh t).st ≠ 0 →
      U ≠ 0 →
      Obs.Zb (Suscept.Cov 2 L N m) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0 ∧
      ∑ x : Lam 2 L N, avg0 L N m b μ₀ (psibar 0 * psi x) =
        1 / (m : ℂ) - (1 / (m : ℂ)) ^ 2 * X ∧
      ((μ₀ + m - b : ℝ) : ℂ) * ∑ x : Lam 2 L N, avg0 L N m b μ₀ (psibar 0 * psi x) =
        1 - (b : ℂ) * avg0 L N m b μ₀ (psibar 0 * psi 0)) := by
  intro R' t out U X
  obtain ⟨-, -, hρ, -, -, -, -, -, -, -, hCf, -, -, hρ8, hspl, H⟩ := D.hC2
  obtain ⟨-, -, -, -, -, -, -, -, -, hval⟩ := H N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  obtain ⟨hV, hVL⟩ := hval m hm
  obtain ⟨hglue, -⟩ := D.hGD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD
  have hρ0 : 0 ≤ R'.ρ := by show 0 ≤ R.ρ; rw [hRρ]; exact hρ.le
  have hρ1 : R'.ρ < 1 := by show R.ρ < 1; rw [hRρ]; linarith
  have hspl' : SplitSmall R'.P L R'.ρ := by
    show SplitSmall R.P L R.ρ
    rw [hP, hRρ]; exact hspl
  have hZ := lastOut_Z_ne R' hρ0 hρ1 Nh t
  have hg := (hD Nh le_rfl).1
  obtain ⟨-, -, -, -, -, hBd, -⟩ := hglue.2
  have hVN := fun c hc => (hBd c hc).1
  have hom := hist_omega_traj R' hNh hρ1 hspl' hm.1 hm.2 hV hVL b μ₀ hVN
  refine ⟨zeroModeOut_of_glue R' hNh hCf t hg.le hglue hZ, hom, fun h1 h2 h3 => ?_⟩
  have hne := omegaZh_ne_of R' hNh hρ1 hspl' hm.1 hm.2 hV hVL b μ₀ hVN h1 h2 h3
  exact ward2_of_Zne R' hNh hρ1 hspl' hm.1 hm.2 hV hVL hb hVN hne

/-- **Task 3, upper end, reduced to the zero-mode coefficient.** If at `(b, μ)` the factors of
`⟨Z_0⟩` do not vanish, `r = 1 − b⟨ψ̄_0ψ_0⟩` is real `≥ 0` (RG one-point value) and the
zero-mode coefficient `X` is real with `X < m²`, then `H0OnePtUp` holds (`χ = (m² − X)/m⁴ > 0`). -/
theorem h0OnePtUp_of_X {L N : ℕ} [NeZero L] {m b μ : ℝ} (hm0 : 0 < m)
    (hZ : Obs.Zb (Suscept.Cov 2 L N m) (VE (V0c b μ) (univ : Finset (Lam 2 L N))) ≠ 0)
    {X : ℂ} (hχ : ∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x) =
      1 / (m : ℂ) - (1 / (m : ℂ)) ^ 2 * X)
    (hr : ∃ r : ℝ, 0 ≤ r ∧ 1 - (b : ℂ) * avg0 L N m b μ (psibar 0 * psi 0) = r)
    (hX : ∃ x : ℝ, x < m ∧ X = x) : H0OnePtUp L N m b μ := by
  obtain ⟨x, hx, rfl⟩ := hX
  refine ⟨hZ, hr, ⟨1 / m - (1 / m) ^ 2 * x, ?_, ?_⟩⟩
  · have e : 1 / m - (1 / m) ^ 2 * x = (m - x) / m ^ 2 := by field_simp
    rw [e]; exact div_pos (by linarith) (by positivity)
  · rw [hχ]; push_cast; ring

/-- **Task 3, lower end, reduced to the zero-mode coefficient.** If at some `μ ∈ [μl, μu]` the
factors of `⟨Z_0⟩` do not vanish and `X` is not a real number in `[m² − m⁴|Λ|/b, m²]`, then
`H0SusceptExit` holds (`χ = (m² − X)/m⁴ ∉ [0, |Λ|/b]`). -/
theorem h0SusceptExit_of_X {L N : ℕ} [NeZero L] {m b μl μu : ℝ} (hm0 : 0 < m)
    (h : ∃ μ ∈ Icc μl μu, ∃ X : ℂ, ∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x) =
      1 / (m : ℂ) - (1 / (m : ℂ)) ^ 2 * X ∧
      ¬ ∃ x : ℝ, m - m ^ 2 * ((Fintype.card (Lam 2 L N) : ℝ) / b) ≤ x ∧ x ≤ m ∧ X = x) :
    H0SusceptExit L N m b μl μu := by
  obtain ⟨μ, hμ, X, hχ, hX⟩ := h
  refine ⟨μ, hμ, fun ⟨χ, h0, h1, he⟩ => hX ⟨m - m ^ 2 * χ, ?_, ?_, ?_⟩⟩
  · have := mul_le_mul_of_nonneg_left h1 (sq_nonneg m); linarith
  · have := mul_nonneg (sq_nonneg m) h0; linarith
  · have hm' : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
    rw [hχ] at he
    have e : X = (m : ℂ) - (m : ℂ) ^ 2 * (1 / (m : ℂ) - (1 / (m : ℂ)) ^ 2 * X) := by
      field_simp; ring
    rw [e, he]; push_cast; ring

end

end Spin2
