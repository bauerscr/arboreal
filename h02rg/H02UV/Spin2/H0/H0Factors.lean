import Spin2.H0.MasterH0OnePt

/-!
# Route (a1), task 2 (part): the chain factors of `⟨Z_0⟩` do not vanish

`⟨Z_0⟩ = (∏_{j≤N_h} c_j)·det_{N_h+1}·e^{−u}·U` (`hist_omega_traj`), `c_j = det_j·e^{−u_{j+1}}`,
`det_j = det(1 + a_jAΓ_j)`. The Fourier symbol of `1 + a_jAΓ_j` is `1 + a_jA(p)Γ_j(p)`, which does
not vanish by the splitting hypothesis `SplitOK` (first component), valid at every step `j < N` of
every history (`splitOK_hist`, from `SplitSmall` and the mass window). Hence:

* **`detStep_ne_of_split`**: `RawInv ∧ SplitOK ⟹ det_j ≠ 0` (`split_kmat_gen`);
* **`chainFactors_ne`**: along every history, `∏_{j≤N_h} c_j ≠ 0` and `det_{N_h+1} ≠ 0`;
* **`MasterCore.onePtWinU`**: `onePtWin` with the factor hypotheses discharged — only `U ≠ 0` remains;
* **`h0OnePtUp_of_U`**, **`h0SusceptExit_of_U`**: the reduced inputs `h0OnePtUp_of_X`,
  `h0SusceptExit_of_X` with the factor conditions discharged: `H0OnePtUp` from `U ≠ 0`, `r ≥ 0`,
  `X` real `< m²` at `(b, μ₊)`; `H0SusceptExit` from `U ≠ 0` and `X ∉ [m² − m⁴|Λ|/b, m²]` at one
  point of the window.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- `det(1 + a_jAΓ_j) ≠ 0` from the splitting hypothesis (Fourier symbol `≠ 0`). -/
theorem detStep_ne_of_split {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] {j : ℕ} {st : RawSt 2 L N} (H : RawInv R j st) (hS : SplitOK R j st) :
    detStep R j st ≠ 0 := by
  have hden : ∀ m, 1 + stA R st * DressedFRD.Asym R.msq m * (stData R j st).Gam j m ≠ 0 := by
    intro m
    have := hS.1 m
    rwa [stData_ζZ H] at this
  have h := (split_kmat_gen ((stData R j st).Gam j)
    (fun m => (stData R j st).Gam j m /
      (1 + stA R st * DressedFRD.Asym R.msq m * (stData R j st).Gam j m)) 0 (stA R st) R.msq hden
    (fun m => by simp)).1
  exact h.ne_zero

/-- **The chain factors do not vanish** along every history (`N = N_h + 2`, `SplitSmall`, the mass
window, validity). -/
theorem chainFactors_ne {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {Nh : ℕ} (hN : Nh + 2 = N) (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) :
    (∏ j ∈ range (Nh + 1), ch R j t) ≠ 0 ∧ detStep R (Nh + 1) (histOut R Nh t).st ≠ 0 := by
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t) := rawInv_histU R hV hVL t
  have hS : ∀ j ≤ Nh + 1, SplitOK R j (rawHist R j t) := fun j hj =>
    splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega)
  refine ⟨prod_ne_zero_iff.2 fun j hj => ?_, ?_⟩
  · have hj' : j ≤ Nh + 1 := by have := mem_range.1 hj; omega
    exact mul_ne_zero (detStep_ne_of_split R (hRI j hj') (hS j hj')) (Complex.exp_ne_zero _)
  · exact detStep_ne_of_split R (hRI (Nh + 1) le_rfl) (hS (Nh + 1) le_rfl)

/-- **`onePtWin` with the chain factors discharged**: along every trajectory in `D_ε` (any sign of
`h`), if `U = 1 + ũ ≠ 0` then `⟨Z_0⟩ ≠ 0`, the dressed susceptibility formula and the Ward identity
hold. -/
theorem MasterCore.onePtWinU {L : ℕ} [NeZero L] (D : MasterCore L) {N : ℕ} (R : RGPar 2 L N)
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
    U ≠ 0 →
      Obs.Zb (Suscept.Cov 2 L N m) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0 ∧
      ∑ x : Lam 2 L N, avg0 L N m b μ₀ (psibar 0 * psi x) =
        1 / (m : ℂ) - (1 / (m : ℂ)) ^ 2 * X ∧
      ((μ₀ + m - b : ℝ) : ℂ) * ∑ x : Lam 2 L N, avg0 L N m b μ₀ (psibar 0 * psi x) =
        1 - (b : ℂ) * avg0 L N m b μ₀ (psibar 0 * psi 0) := by
  intro R' t out U X hU
  obtain ⟨-, -, hρ, -, -, -, -, -, -, -, -, -, -, hρ8, hspl, H⟩ := D.hC2
  obtain ⟨-, -, -, -, -, -, -, -, -, hval⟩ := H N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  obtain ⟨hV, hVL⟩ := hval m hm
  have hspl' : SplitSmall R'.P L R'.ρ := by
    show SplitSmall R.P L R.ρ
    rw [hP, hRρ]; exact hspl
  obtain ⟨h1, h2⟩ := chainFactors_ne R' hNh hspl' hm.1 hm.2 hV hVL t
  exact (D.onePtWin R hP hi0 hRℓ hRA hRρ hN hNh hm hb hD).2.2 h1 h2 hU

/-- **The upper window end reduced to `U ≠ 0`, `r ≥ 0` and the position of `X`.** -/
theorem h0OnePtUp_of_U {L : ℕ} [NeZero L] (D : MasterCore L) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ)
    (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ : ℝ} (hb : 0 < b)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j))
    (hU : 1 + uFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ))
      (zmRaw (R.withMsq m) (Nh + 1)
        (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)).ζ) ≠ 0)
    (hr : ∃ r : ℝ, 0 ≤ r ∧ 1 - (b : ℂ) * avg0 L N m b μ (psibar 0 * psi 0) = r)
    (hX : ∃ x : ℝ, x < m ∧
      aFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)) *
          πh (R.withMsq m) (Nh + 2) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) /
          (1 + uFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ))
            (zmRaw (R.withMsq m) (Nh + 1)
              (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)).ζ)) +
        ∑ j ∈ range (Nh + 2), ch₀ (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) *
          πh (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) /
          ρh (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) = x) :
    H0OnePtUp L N m b μ := by
  obtain ⟨hZ, hχ, -⟩ := D.onePtWinU R hP hi0 hRℓ hRA hRρ hN hNh hm hb hD hU
  exact h0OnePtUp_of_X hm.1 hZ hχ hr hX

/-- **The lower window end reduced to `U ≠ 0` and the position of `X` at one point.** -/
theorem h0SusceptExit_of_U {L : ℕ} [NeZero L] (D : MasterCore L) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ)
    (hRA : R.A = D.A) (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μl μu : ℝ} (hb : 0 < b)
    (h : ∃ μ ∈ Icc μl μu,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j)) ∧
      1 + uFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ))
        (zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)).ζ) ≠ 0 ∧
      ¬ ∃ x : ℝ, m - m ^ 2 * ((Fintype.card (Lam 2 L N) : ℝ) / b) ≤ x ∧ x ≤ m ∧
        aFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)) *
            πh (R.withMsq m) (Nh + 2) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) /
            (1 + uFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ))
              (zmRaw (R.withMsq m) (Nh + 1)
                (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)).ζ)) +
          ∑ j ∈ range (Nh + 2), ch₀ (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) *
            πh (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) /
            ρh (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ) = x) :
    H0SusceptExit L N m b μl μu := by
  obtain ⟨μ, hμ, hD, hU, hX⟩ := h
  obtain ⟨-, hχ, -⟩ := D.onePtWinU R hP hi0 hRℓ hRA hRρ hN hNh hm hb hD hU
  exact h0SusceptExit_of_X hm.1 ⟨μ, hμ, _, hχ, hX⟩

end

end Spin2
